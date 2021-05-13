// Copyright 2018. All rights reserved. Use of this source code is governed by
// an MIT-style license that can be found in the LICENSE file.

// Package cache implements the CLOCK-Pro caching algorithm.
//
// CLOCK-Pro is a patent-free alternative to the Adaptive Replacement Cache,
// https://en.wikipedia.org/wiki/Adaptive_replacement_cache.
// It is an approximation of LIRS ( https://en.wikipedia.org/wiki/LIRS_caching_algorithm ),
// much like the CLOCK page replacement algorithm is an approximation of LRU.
//
// This implementation is based on the python code from https://bitbucket.org/SamiLehtinen/pyclockpro .
//
// Slides describing the algorithm: http://fr.slideshare.net/huliang64/clockpro
//
// The original paper: http://static.usenix.org/event/usenix05/tech/general/full_papers/jiang/jiang_html/html.html
//
// It is MIT licensed, like the original.
package cache // import "github.com/cockroachdb/pebble/internal/cache"

import (
	"fmt"
	"os"
	"runtime"
	"runtime/debug"
	"strings"
	"sync"
	"sync/atomic"

	"github.com/cockroachdb/pebble/internal/base"
	"github.com/cockroachdb/pebble/internal/invariants"
)

type fileKey struct {
	// id is the namespace for fileNums.
	id      uint64
	fileNum base.FileNum
}

type key struct {
	fileKey
	offset uint64
}

// file returns the "file key" for the receiver. This is the key used for the
// shard.files map.
func (k key) file() key {
	k.offset = 0
	return k
}

func (k key) String() string {
	return fmt.Sprintf("%d/%d/%d", k.id, k.fileNum, k.offset)
}

// Handle provides a strong reference to a value in the cache. The reference
// does not pin the value in the cache, but it does prevent the underlying byte
// slice from being reused.
type Handle struct {
	value *Value
}

// Get returns the value stored in handle.
func (h Handle) Get() []byte {
	if h.value != nil {
		// NB: We don't increment shard.hits in this code path because we only want
		// to record a hit when the handle is retrieved from the cache.
		return h.value.buf
	}
	return nil
}

// Release releases the reference to the cache entry.
func (h Handle) Release() {
	if h.value != nil {
		h.value.release()
	}
}

type shard struct {
	hits   int64
	misses int64
	epoch  int64

	mu sync.RWMutex

	reservedSize int64
	maxSize      int64
	minColdSize  int64
	maxColdSize  int64
	coldTarget   int64
	blocks       robinHoodMap // fileNum+offset -> block
	files        robinHoodMap // fileNum -> list of blocks

	// The blocks and files maps store values in manually managed memory that is
	// invisible to the Go GC. This is fine for Value and entry objects that are
	// stored in manually managed memory, but when the "invariants" build tag is
	// set, all Value and entry objects are Go allocated and the entries map will
	// contain a reference to every entry.
	entries map[*entry]struct{}

	headHot         *entry
	headCold        *entry
	headNonResident *entry

	sizeHot  int64
	sizeCold int64
	sizeTest int64
}

func (c *shard) inTestPeriod(e *entry) bool {
	return c.sizeHot == 0 || e.epoch > c.headHot.epoch
}

func (c *shard) prune() {
	for c.sizeTest > 0 && !c.inTestPeriod(c.headNonResident) {
		c.runHandTest()
	}
}

func (c *shard) canPromote(candidate *entry) bool {
	if !c.inTestPeriod(candidate) {
		return false
	}
	c.adjustColdTarget(+candidate.size)
	for c.sizeHot > 0 && c.sizeHot >= c.targetSize()-c.coldTarget {
		if !c.runHandHot(candidate.epoch) {
			return false
		}
	}
	return c.inTestPeriod(candidate)
}

func (c *shard) adjustColdTarget(n int64) {
	c.coldTarget += n
	if c.coldTarget < c.minColdSize {
		c.coldTarget = c.minColdSize
	} else if c.coldTarget > c.maxColdSize {
		c.coldTarget = c.maxColdSize
	}
}

func (c *shard) updateProtectedColdSize() {
	protected := c.targetSize() / 100
	c.minColdSize = protected
	c.maxColdSize = c.targetSize() - protected
}

func (c *shard) Get(id uint64, fileNum base.FileNum, offset uint64) Handle {
	c.mu.RLock()
	var value *Value
	if e := c.blocks.Get(key{fileKey{id, fileNum}, offset}); e != nil {
		value = e.acquireValue()
		if value != nil {
			atomic.StoreInt32(&e.referenced, 1)
		}
	}
	c.mu.RUnlock()
	if value == nil {
		atomic.AddInt64(&c.misses, 1)
		return Handle{}
	}
	atomic.AddInt64(&c.hits, 1)
	return Handle{value: value}
}

func (c *shard) Set(id uint64, fileNum base.FileNum, offset uint64, value *Value) Handle {
	if n := value.refs(); n != 1 {
		panic(fmt.Sprintf("pebble: Value has already been added to the cache: refs=%d", n))
	}

	c.mu.Lock()
	defer c.mu.Unlock()

	k := key{fileKey{id, fileNum}, offset}
	e := c.blocks.Get(k)

	c.epoch++
	switch {
	case e == nil:
		// no cache entry? add it
		e = newEntry(c, k, int64(len(value.buf)))
		e.setValue(value)
		e.epoch = c.epoch
		if c.metaAdd(k, e) {
			value.ref.trace("add-cold")
			c.sizeCold += e.size
		} else {
			value.ref.trace("skip-cold")
			e.free()
			e = nil
		}

	case e.peekValue() != nil:
		// cache entry was a hot or cold page
		e.setValue(value)
		atomic.StoreInt32(&e.referenced, 1)
		delta := int64(len(value.buf)) - e.size
		e.size = int64(len(value.buf))
		if e.ptype == etHot {
			value.ref.trace("add-hot")
			c.sizeHot += delta
		} else {
			value.ref.trace("add-cold")
			c.sizeCold += delta
		}

	default:
		// cache entry was a test page
		c.sizeTest -= e.size
		c.metaDel(e)
		c.metaCheck(e)

		atomic.StoreInt32(&e.referenced, 0)
		e.setValue(value)
		e.epoch = c.epoch

		if c.canPromote(e) {
			e.ptype = etHot
			if c.metaAdd(k, e) {
				value.ref.trace("add-hot")
				c.sizeHot += e.size
			} else {
				value.ref.trace("skip-hot")
				e.free()
				e = nil
			}
		} else {
			e.ptype = etCold
			if c.metaAdd(k, e) {
				value.ref.trace("add-cold")
				c.sizeCold += e.size
			} else {
				value.ref.trace("skip-hot")
				e.free()
				e = nil
			}
		}
	}
	c.evict()

	// Values are initialized with a reference count of 1. That reference count
	// is being transferred to the returned Handle.
	return Handle{value: value}
}

// Delete deletes the cached value for the specified file and offset.
func (c *shard) Delete(id uint64, fileNum base.FileNum, offset uint64) {
	// The common case is there is nothing to delete, so do a quick check with
	// shared lock.
	k := key{fileKey{id, fileNum}, offset}
	c.mu.RLock()
	exists := c.blocks.Get(k) != nil
	c.mu.RUnlock()
	if !exists {
		return
	}

	c.mu.Lock()
	defer c.mu.Unlock()

	e := c.blocks.Get(k)
	if e == nil {
		return
	}
	c.metaEvict(e)
}

// EvictFile evicts all of the cache values for the specified file.
func (c *shard) EvictFile(id uint64, fileNum base.FileNum) {
	c.mu.Lock()
	defer c.mu.Unlock()

	fkey := key{fileKey{id, fileNum}, 0}
	blocks := c.files.Get(fkey)
	if blocks == nil {
		return
	}
	for b, n := blocks, (*entry)(nil); ; b = n {
		n = b.fileLink.next
		c.metaEvict(b)
		if b == n {
			break
		}
	}
}

func (c *shard) Free() {
	c.mu.Lock()
	defer c.mu.Unlock()

	// NB: we use metaDel rather than metaEvict in order to avoid the expensive
	// metaCheck call when the "invariants" build tag is specified.
	if c.headCold != nil {
		for c.headCold.prev() != c.headCold {
			c.metaEvict(c.headCold.prev())
		}
		c.metaEvict(c.headCold)
		c.headCold = nil
	}
	if c.headHot != nil {
		for c.headHot.prev() != c.headHot {
			c.metaEvict(c.headHot.prev())
		}
		c.metaEvict(c.headHot)
		c.headHot = nil
	}
	if c.headNonResident != nil {
		for c.headNonResident.prev() != c.headNonResident {
			c.metaEvict(c.headNonResident.prev())
		}
		c.metaEvict(c.headNonResident)
		c.headNonResident = nil
	}

	c.blocks.free()
	c.files.free()
}

func (c *shard) Reserve(n int) {
	c.mu.Lock()
	c.reservedSize += int64(n)
	c.updateProtectedColdSize()
	c.evict()
	c.mu.Unlock()
}

// Size returns the current space used by the cache.
func (c *shard) Size() int64 {
	c.mu.RLock()
	size := c.sizeHot + c.sizeCold
	c.mu.RUnlock()
	return size
}

func (c *shard) targetSize() int64 {
	target := c.maxSize - c.reservedSize
	// Always return a positive integer for targetSize. This is so that we don't
	// end up in an infinite loop in evict(), in cases where reservedSize is
	// greater than or equal to maxSize.
	if target < 1 {
		return 1
	}
	return target
}

// Add the entry to the cache, returning true if the entry was added and false
// if it would not fit in the cache.
func (c *shard) metaAdd(key key, e *entry) bool {
	if e.size > c.targetSize() {
		// The entry is larger than the target cache size.
		return false
	}

	c.blocks.Put(key, e)
	if entriesGoAllocated {
		// Go allocated entries need to be referenced from Go memory. The entries
		// map provides that reference.
		c.entries[e] = struct{}{}
	}

	if e.ptype == etCold {
		if c.headCold != nil {
			e.link(c.headCold)
		} else {
			c.headCold = e
		}
	} else if e.ptype == etHot {
		if c.headHot != nil {
			e.link(c.headHot)
		} else {
			c.headHot = e
		}
	} else {
		panic("invalid entry type")
	}

	fkey := key.file()
	if fileBlocks := c.files.Get(fkey); fileBlocks == nil {
		c.files.Put(fkey, e)
	} else {
		fileBlocks.linkFile(e)
	}
	return true
}

// Remove the entry from the cache. This removes the entry from the blocks map,
// the files map, and ensures that hand{Hot,Cold,Test} are not pointing at the
// entry.
func (c *shard) metaDel(e *entry) {
	if value := e.peekValue(); value != nil {
		value.ref.trace("metaDel")
	}
	e.setValue(nil)

	c.blocks.Delete(e.key)
	if entriesGoAllocated {
		// Go allocated entries need to be referenced from Go memory. The entries
		// map provides that reference.
		delete(c.entries, e)
	}

	if e == c.headCold {
		if e.next() != e {
			c.headCold = c.headCold.prev()
		} else {
			c.headCold = nil
		}
	} else if e == c.headHot {
		if e.next() != e {
			c.headHot = c.headHot.prev()
		} else {
			c.headHot = nil
		}
	} else if e == c.headNonResident {
		if e.next() != e {
			c.headNonResident = c.headNonResident.prev()
		} else {
			c.headNonResident = nil
		}
	}
	e.unlink()

	fkey := e.key.file()
	if next := e.unlinkFile(); e == next {
		c.files.Delete(fkey)
	} else {
		c.files.Put(fkey, next)
	}
}

// Check that the specified entry is not referenced by the cache.
func (c *shard) metaCheck(e *entry) {
	if invariants.Enabled {
		if _, ok := c.entries[e]; ok {
			fmt.Fprintf(os.Stderr, "%p: %s unexpectedly found in entries map\n%s",
				e, e.key, debug.Stack())
			os.Exit(1)
		}
		if c.blocks.findByValue(e) != nil {
			fmt.Fprintf(os.Stderr, "%p: %s unexpectedly found in blocks map\n%s\n%s",
				e, e.key, &c.blocks, debug.Stack())
			os.Exit(1)
		}
		if c.files.findByValue(e) != nil {
			fmt.Fprintf(os.Stderr, "%p: %s unexpectedly found in files map\n%s\n%s",
				e, e.key, &c.files, debug.Stack())
			os.Exit(1)
		}
		// NB: c.hand{Hot,Cold,Test} are pointers into a single linked list. We
		// only have to traverse one of them to check all of them.
		for t := c.headHot.next(); t != c.headHot; t = t.next() {
			if e == t {
				fmt.Fprintf(os.Stderr, "%p: %s unexpectedly found in blocks list\n%s",
					e, e.key, debug.Stack())
				os.Exit(1)
			}
		}
		for t := c.headCold.next(); t != c.headCold; t = t.next() {
			if e == t {
				fmt.Fprintf(os.Stderr, "%p: %s unexpectedly found in blocks list\n%s",
					e, e.key, debug.Stack())
				os.Exit(1)
			}
		}
		for t := c.headNonResident.next(); t != c.headNonResident; t = t.next() {
			if e == t {
				fmt.Fprintf(os.Stderr, "%p: %s unexpectedly found in blocks list\n%s",
					e, e.key, debug.Stack())
				os.Exit(1)
			}
		}
	}
}

func (c *shard) metaEvict(e *entry) {
	switch e.ptype {
	case etHot:
		c.sizeHot -= e.size
	case etCold:
		c.sizeCold -= e.size
	case etNR:
		c.sizeTest -= e.size
	}
	c.metaDel(e)
	c.metaCheck(e)
	e.free()
}

func (c *shard) evict() {
	for c.targetSize() < c.sizeHot+c.sizeCold {
		if c.sizeCold > 0 {
			c.runHandCold()
		} else {
			c.runHandHot(c.epoch)
		}
	}
	c.prune()
}

func (c *shard) runHandCold() {
	victim := c.headCold
	if atomic.LoadInt32(&victim.referenced) == 1 {
		atomic.StoreInt32(&victim.referenced, 0)
		if c.canPromote(victim) {
			if victim.next() != victim {
				c.headCold = c.headCold.prev()
				victim.unlink()
			} else {
				c.headCold = nil
			}
			victim.ptype = etHot
			if c.headHot != nil {
				victim.link(c.headHot)
			} else {
				c.headHot = victim
			}
			c.sizeCold -= victim.size
			c.sizeHot += victim.size
		} else {
			c.headCold = c.headCold.prev()
		}
		c.epoch++
		victim.epoch = c.epoch
	} else {
		if victim.next() != victim {
			c.headCold = c.headCold.prev()
			victim.unlink()
		} else {
			c.headCold = nil
		}
		if c.inTestPeriod(victim) {
			victim.ptype = etNR
			if c.headNonResident != nil {
				victim.link(c.headNonResident)
			} else {
				c.headNonResident = victim
			}
			c.sizeCold -= victim.size
			c.sizeTest += victim.size
		} else {
			c.metaEvict(victim)
		}
		for c.sizeTest > c.targetSize() {
			c.runHandTest()
		}
	}
}

func (c *shard) runHandHot(epoch int64) bool {
	for victim := c.headHot; victim.epoch <= epoch; victim = c.headHot {
		if atomic.LoadInt32(&victim.referenced) == 1 {
			atomic.StoreInt32(&victim.referenced, 0)
			c.epoch++
			victim.epoch = c.epoch
			c.headHot = c.headHot.prev()
		} else {
			if victim.next() != victim {
				c.headHot = c.headHot.prev()
				victim.unlink()
			} else {
				c.headHot = nil
			}
			victim.ptype = etCold
			if c.headCold != nil {
				victim.link(c.headCold)
			} else {
				c.headCold = victim
			}
			c.sizeHot -= victim.size
			c.sizeCold += victim.size
			return true
		}
	}
	return false
}

func (c *shard) runHandTest() {
	victim := c.headNonResident
	if victim.next() != victim {
		c.headNonResident = c.headNonResident.prev()
		victim.unlink()
	} else {
		c.headNonResident = nil
	}
	c.adjustColdTarget(-victim.size)
	c.metaEvict(victim)
}

func (c *shard) printClock() {
	if c.sizeCold > 0 {
		fmt.Println("** CLOCK-Pro list COLD HEAD (small recency) **")
		for e := c.headCold.prev(); e != c.headCold; e = e.prev() {
			fmt.Printf("%s:%s:%d:%d\n", e.key.String(), e.ptype.String(), e.referenced, e.epoch)
		}
		fmt.Println("** CLOCK-Pro list COLD TAIL (large recency) **")
	}
	if c.sizeHot > 0 {
		fmt.Println("** CLOCK-Pro list HOT HEAD (small recency) **")
		for e := c.headHot.prev(); e != c.headHot; e = e.prev() {
			fmt.Printf("%s:%s:%d:%d\n", e.key.String(), e.ptype.String(), e.referenced, e.epoch)
		}
		fmt.Println("** CLOCK-Pro list HOT TAIL (large recency) **")
	}
	if c.sizeCold > 0 {
		fmt.Println("** CLOCK-Pro list NR HEAD (small recency) **")
		for e := c.headNonResident.prev(); e != c.headNonResident; e = e.prev() {
			fmt.Printf("%s:%s:%d:%d\n", e.key.String(), e.ptype.String(), e.referenced, e.epoch)
		}
		fmt.Println("** CLOCK-Pro list NR TAIL (large recency) **")
	}
}

// Metrics holds metrics for the cache.
type Metrics struct {
	// The number of bytes inuse by the cache.
	Size int64
	// The count of objects (blocks or tables) in the cache.
	Count int64
	// The number of cache hits.
	Hits int64
	// The number of cache misses.
	Misses int64
}

// Cache implements Pebble's sharded block cache. The Clock-PRO algorithm is
// used for page replacement
// (http://static.usenix.org/event/usenix05/tech/general/full_papers/jiang/jiang_html/html.html). In
// order to provide better concurrency, 2 x NumCPUs shards are created, with
// each shard being given 1/n of the target cache size. The Clock-PRO algorithm
// is run independently on each shard.
//
// Blocks are keyed by an (id, fileNum, offset) triple. The ID is a namespace
// for file numbers and allows a single Cache to be shared between multiple
// Pebble instances. The fileNum and offset refer to an sstable file number and
// the offset of the block within the file. Because sstables are immutable and
// file numbers are never reused, (fileNum,offset) are unique for the lifetime
// of a Pebble instance.
//
// In addition to maintaining a map from (fileNum,offset) to data, each shard
// maintains a map of the cached blocks for a particular fileNum. This allows
// efficient eviction of all of the blocks for a file which is used when an
// sstable is deleted from disk.
//
// Memory Management
//
// In order to reduce pressure on the Go GC, manual memory management is
// performed for the data stored in the cache. Manual memory management is
// performed by calling into C.{malloc,free} to allocate memory. Cache.Values
// are reference counted and the memory backing a manual value is freed when
// the reference count drops to 0.
//
// Manual memory management brings the possibility of memory leaks. It is
// imperative that every Handle returned by Cache.{Get,Set} is eventually
// released. The "invariants" build tag enables a leak detection facility that
// places a GC finalizer on cache.Value. When the cache.Value finalizer is run,
// if the underlying buffer is still present a leak has occurred. The "tracing"
// build tag enables tracing of cache.Value reference count manipulation and
// eases finding where a leak has occurred. These two facilities are usually
// used in combination by specifying `-tags invariants,tracing`. Note that
// "tracing" produces a significant slowdown, while "invariants" does not.
type Cache struct {
	refs    int64
	maxSize int64
	idAlloc uint64
	shards  []shard

	// Traces recorded by Cache.trace. Used for debugging.
	tr struct {
		sync.Mutex
		msgs []string
	}
}

// New creates a new cache of the specified size. Memory for the cache is
// allocated on demand, not during initialization. The cache is created with a
// reference count of 1. Each DB it is associated with adds a reference, so the
// creator of the cache should usually release their reference after the DB is
// created.
//
//   c := cache.New(...)
//   defer c.Unref()
//   d, err := pebble.Open(pebble.Options{Cache: c})
func New(size int64) *Cache {
	return newShards(size, 2*runtime.GOMAXPROCS(0))
}

func newShards(size int64, shards int) *Cache {
	c := &Cache{
		refs:    1,
		maxSize: size,
		idAlloc: 1,
		shards:  make([]shard, shards),
	}
	c.trace("alloc", c.refs)
	for i := range c.shards {
		c.shards[i] = shard{
			maxSize: size / int64(len(c.shards)),
		}
		c.shards[i].updateProtectedColdSize()
		c.shards[i].coldTarget = c.shards[i].minColdSize
		if entriesGoAllocated {
			c.shards[i].entries = make(map[*entry]struct{})
		}
		c.shards[i].blocks.init(16)
		c.shards[i].files.init(16)
	}

	// Note: this is a no-op if invariants are disabled or race is enabled.
	invariants.SetFinalizer(c, func(obj interface{}) {
		c := obj.(*Cache)
		if v := atomic.LoadInt64(&c.refs); v != 0 {
			c.tr.Lock()
			fmt.Fprintf(os.Stderr, "pebble: cache (%p) has non-zero reference count: %d\n%s",
				c, v, strings.Join(c.tr.msgs, "\n"))
			c.tr.Unlock()
			os.Exit(1)
		}
	})
	return c
}

func (c *Cache) trace(msg string, refs int64) {
	if invariants.Enabled {
		s := fmt.Sprintf("%s: refs=%d\n%s", msg, refs, debug.Stack())
		c.tr.Lock()
		c.tr.msgs = append(c.tr.msgs, s)
		c.tr.Unlock()
	}
}

func (c *Cache) getShard(id uint64, fileNum base.FileNum, offset uint64) *shard {
	if id == 0 {
		panic("pebble: 0 cache ID is invalid")
	}

	// Inlined version of fnv.New64 + Write.
	const offset64 = 14695981039346656037
	const prime64 = 1099511628211

	h := uint64(offset64)
	for i := 0; i < 8; i++ {
		h *= prime64
		h ^= uint64(id & 0xff)
		id >>= 8
	}
	for i := 0; i < 8; i++ {
		h *= prime64
		h ^= uint64(fileNum & 0xff)
		fileNum >>= 8
	}
	for i := 0; i < 8; i++ {
		h *= prime64
		h ^= uint64(offset & 0xff)
		offset >>= 8
	}

	return &c.shards[h%uint64(len(c.shards))]
}

// Ref adds a reference to the cache. The cache only remains valid as long a
// reference is maintained to it.
func (c *Cache) Ref() {
	v := atomic.AddInt64(&c.refs, 1)
	if v <= 1 {
		panic(fmt.Sprintf("pebble: inconsistent reference count: %d", v))
	}
	c.trace("ref", v)
}

// Unref releases a reference on the cache.
func (c *Cache) Unref() {
	v := atomic.AddInt64(&c.refs, -1)
	c.trace("unref", v)
	switch {
	case v < 0:
		panic(fmt.Sprintf("pebble: inconsistent reference count: %d", v))
	case v == 0:
		for i := range c.shards {
			c.shards[i].Free()
		}
	}
}

// Get retrieves the cache value for the specified file and offset, returning
// nil if no value is present.
func (c *Cache) Get(id uint64, fileNum base.FileNum, offset uint64) Handle {
	return c.getShard(id, fileNum, offset).Get(id, fileNum, offset)
}

// Set sets the cache value for the specified file and offset, overwriting an
// existing value if present. A Handle is returned which provides faster
// retrieval of the cached value than Get (lock-free and avoidance of the map
// lookup). The value must have been allocated by Cache.Alloc.
func (c *Cache) Set(id uint64, fileNum base.FileNum, offset uint64, value *Value) Handle {
	return c.getShard(id, fileNum, offset).Set(id, fileNum, offset, value)
}

// Delete deletes the cached value for the specified file and offset.
func (c *Cache) Delete(id uint64, fileNum base.FileNum, offset uint64) {
	c.getShard(id, fileNum, offset).Delete(id, fileNum, offset)
}

// EvictFile evicts all of the cache values for the specified file.
func (c *Cache) EvictFile(id uint64, fileNum base.FileNum) {
	if id == 0 {
		panic("pebble: 0 cache ID is invalid")
	}
	for i := range c.shards {
		c.shards[i].EvictFile(id, fileNum)
	}
}

// MaxSize returns the max size of the cache.
func (c *Cache) MaxSize() int64 {
	return c.maxSize
}

// Size returns the current space used by the cache.
func (c *Cache) Size() int64 {
	var size int64
	for i := range c.shards {
		size += c.shards[i].Size()
	}
	return size
}

// Alloc allocates a byte slice of the specified size, possibly reusing
// previously allocated but unused memory. The memory backing the value is
// manually managed. The caller MUST either add the value to the cache (via
// Cache.Set), or release the value (via Cache.Free). Failure to do so will
// result in a memory leak.
func (c *Cache) Alloc(n int) *Value {
	return newValue(n)
}

// Free frees the specified value. The buffer associated with the value will
// possibly be reused, making it invalid to use the buffer after calling
// Free. Do not call Free on a value that has been added to the cache.
func (c *Cache) Free(v *Value) {
	if n := v.refs(); n > 1 {
		panic(fmt.Sprintf("pebble: Value has been added to the cache: refs=%d", n))
	}
	v.release()
}

// Reserve N bytes in the cache. This effectively shrinks the size of the cache
// by N bytes, without actually consuming any memory. The returned closure
// should be invoked to release the reservation.
func (c *Cache) Reserve(n int) func() {
	// Round-up the per-shard reservation. Most reservations should be large, so
	// this probably doesn't matter in practice.
	shardN := (n + len(c.shards) - 1) / len(c.shards)
	for i := range c.shards {
		c.shards[i].Reserve(shardN)
	}
	return func() {
		if shardN == -1 {
			panic("pebble: cache reservation already released")
		}
		for i := range c.shards {
			c.shards[i].Reserve(-shardN)
		}
		shardN = -1
	}
}

// Metrics returns the metrics for the cache.
func (c *Cache) Metrics() Metrics {
	var m Metrics
	for i := range c.shards {
		s := &c.shards[i]
		s.mu.RLock()
		m.Count += int64(s.blocks.Count())
		m.Size += s.sizeHot + s.sizeCold
		s.mu.RUnlock()
		m.Hits += atomic.LoadInt64(&s.hits)
		m.Misses += atomic.LoadInt64(&s.misses)
	}
	return m
}

// NewID returns a new ID to be used as a namespace for cached file
// blocks.
func (c *Cache) NewID() uint64 {
	return atomic.AddUint64(&c.idAlloc, 1)
}
