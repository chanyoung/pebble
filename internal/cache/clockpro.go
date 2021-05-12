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

	mu sync.RWMutex

	reservedSize int64
	maxSize      int64
	coldTarget   int64
	blocks       robinHoodMap // fileNum+offset -> block
	files        robinHoodMap // fileNum -> list of blocks

	// The blocks and files maps store values in manually managed memory that is
	// invisible to the Go GC. This is fine for Value and entry objects that are
	// stored in manually managed memory, but when the "invariants" build tag is
	// set, all Value and entry objects are Go allocated and the entries map will
	// contain a reference to every entry.
	entries map[*entry]struct{}

	handHot  *entry
	handCold *entry
	handTest *entry
	listHead *entry

	sizeHot        int64
	sizeResCold    int64
	sizeNonResCold int64
}

func (c *shard) printAll() {
	if c.Size() == 0 {
		return
	}
	s := c.print(c.listHead)
	for e := c.listHead.prev(); e != c.listHead; e = e.prev() {
		s += c.print(e)
	}
	fmt.Println(s)
}

func (c *shard) print(e *entry) string {
	s := fmt.Sprintf("%s:%s:%d", e.key.String(), e.ptype.String(), e.referenced)
	if e == c.handCold {
		s += " <- handCold"
	}
	if e == c.handHot {
		s += " <- handHot"
	}
	if e == c.handTest {
		s += " <- handTest"
	}
	if e == c.listHead {
		s += " <- listHead"
	}
	s += "\n"
	return s
}

func (c *shard) adjustColdTarget(n int64) {
	c.coldTarget += n
	if c.coldTarget < 0 {
		c.coldTarget = 0
	} else if c.coldTarget > c.targetSize() {
		c.coldTarget = c.targetSize()
	}
}

func (c *shard) canPromote(candidate *entry) bool {
	// To compare reuse distance, candidate must be in the clock. And only the node in its test
	// period can be considered to promote.
	if candidate.ptype == etOutOfClock || !candidate.ptype.isInTest() {
		return false
	}
	// This candidate cold page is accessed during its test period, so we increment coldTarget by 1.
	c.adjustColdTarget(+candidate.size)
	for c.sizeHot >= c.targetSize()-c.coldTarget && c.sizeHot > 0 {
		// handHot has passed the candidate and terminates its test period. Reject the promotion.
		if !candidate.ptype.isInTest() {
			return false
		}
		// Failed to demote a hot node. Reject the promotion.
		if !c.runHandHot(candidate) {
			return false
		}
	}
	return true
}

func (c *shard) terminateTestPeriod(e *entry) {
	if !e.ptype.isInTest() {
		return
	}
	// We terminate the test period of the cold page, and also remove it from the clock if it is a
	// non-resident page. Because the cold page has used up its test period without a re-access and
	// has no chance to turn into a hot page with its next access.
	if e.ptype == etColdResInTest {
		e.ptype = etColdRes
	} else {
		c.metaEvict(e)
	}
	// If a cold page is accessed during its test period, we increment coldTarget by 1. If a cold
	// page passes its test period without a re-access, we decrement coldTarget by 1. Note the
	// aforementioned cold pages include resident and non-resident cold pages.
	if atomic.LoadInt32(&e.referenced) == 1 {
		c.adjustColdTarget(+e.size)
	} else {
		c.adjustColdTarget(-e.size)
	}
}

func (c *shard) setEntryType(e *entry, ptype entryType) {
	if e.ptype == etHot {
		c.sizeHot -= e.size
	}
	if e.ptype.isResidentCold() {
		c.sizeResCold -= e.size
	}
	if e.ptype == etColdNonRes {
		c.sizeNonResCold -= e.size
	}
	e.ptype = ptype
	if e.ptype == etHot {
		c.sizeHot += e.size
	}
	if e.ptype.isResidentCold() {
		c.sizeResCold += e.size
	}
	if e.ptype == etColdNonRes {
		c.sizeNonResCold += e.size
	}
}

func (c *shard) removeFromClock(e *entry) {
	if e == c.listHead {
		c.listHead = c.listHead.prev()
	}
	if e == c.handCold {
		c.handCold = c.handCold.next()
	}
	if e == c.handHot {
		c.handHot = c.handHot.next()
	}
	if e == c.handTest {
		c.handTest = c.handTest.next()
	}
	if e == e.unlink() {
		c.listHead = nil
		c.handCold = nil
		c.handHot = nil
		c.handTest = nil
	}
	c.setEntryType(e, etOutOfClock)
	atomic.StoreInt32(&e.referenced, 0)
}

func (c *shard) moveToHead(e *entry, ptype entryType) {
	if e.ptype != etOutOfClock {
		c.removeFromClock(e)
	}
	if c.listHead != nil {
		c.listHead.link(e)
	}
	c.listHead = e
	c.setEntryType(e, ptype)
	if e.ptype.isResidentCold() && c.sizeResCold == e.size {
		c.handCold = e
	}
	// } else if e.ptype == etHot && c.sizeHot == e.size {
	// 	c.handHot = e
	// } else if e.ptype == etColdNonRes && c.sizeNonResCold == e.size {
	// 	c.handTest = e
	// }
}

// Make handHot points to the hot page with the largest recency.
func (c *shard) nextHandHot() {
	if c.sizeHot > 0 {
		if c.handHot == nil {
			c.handHot = c.listHead.next()
		}
		for c.handHot.ptype != etHot {
			if c.handHot == c.handTest {
				c.handTest = c.handTest.next()
			}
			// Terminate test period of encountered cold pages.
			c.handHot = c.handHot.next()
			c.terminateTestPeriod(c.handHot.prev())
		}
	} else {
		c.handHot = nil
	}
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

	switch {
	case e == nil:
		// no cache entry? add it
		e = newEntry(c, k, int64(len(value.buf)))
		e.setValue(value)
		if c.metaAdd(k, e, etColdResInTest) {
			value.ref.trace("add-cold")
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
		if delta > 0 {
			c.evict(delta)
		}
		e.size = int64(len(value.buf))
		if e.ptype == etHot {
			value.ref.trace("add-hot")
			c.sizeHot += delta
		} else {
			value.ref.trace("add-cold")
			c.sizeResCold += delta
		}

	default:
		// cache entry was a test page
		c.sizeNonResCold -= e.size
		c.metaDel(e)
		c.metaCheck(e)

		c.coldTarget += e.size
		if c.coldTarget > c.targetSize() {
			c.coldTarget = c.targetSize()
		}

		atomic.StoreInt32(&e.referenced, 0)
		e.setValue(value)
		if c.metaAdd(k, e, etHot) {
			value.ref.trace("add-hot")
		} else {
			value.ref.trace("skip-hot")
			e.free()
			e = nil
		}
	}

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
	for c.listHead != nil {
		e := c.listHead
		c.metaDel(c.listHead)
		e.free()
	}

	c.blocks.free()
	c.files.free()
}

func (c *shard) Reserve(n int) {
	c.mu.Lock()
	c.evict(int64(n))
	c.reservedSize += int64(n)
	c.mu.Unlock()
}

// Size returns the current space used by the cache.
func (c *shard) Size() int64 {
	c.mu.RLock()
	size := c.sizeHot + c.sizeResCold
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
func (c *shard) metaAdd(key key, e *entry, ptype entryType) bool {
	c.evict(e.size)
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

	c.moveToHead(e, ptype)

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

	c.removeFromClock(e)

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
		for t := c.listHead.next(); t != c.listHead; t = t.next() {
			if e == t {
				fmt.Fprintf(os.Stderr, "%p: %s unexpectedly found in blocks list\n%s",
					e, e.key, debug.Stack())
				os.Exit(1)
			}
		}
	}
}

func (c *shard) metaEvict(e *entry) {
	// switch e.ptype {
	// case etHot:
	// 	c.sizeHot -= e.size
	// case etColdResInTest:
	// 	c.sizeResCold -= e.size
	// case etColdRes:
	// 	c.sizeResCold -= e.size
	// case etColdNonRes:
	// 	c.sizeNonResCold -= e.size
	// }
	c.metaDel(e)
	c.metaCheck(e)
	e.free()
}

func (c *shard) evict(n int64) {
	if n > c.targetSize() {
		n = c.targetSize()
	}
	for c.targetSize() < c.sizeHot+c.sizeResCold+n {
		if c.sizeResCold > 0 {
			c.runHandCold()
		} else {
			c.runHandHot(nil)
		}
	}
}

func (c *shard) runHandCold() {
	// runHandCold is used to search for a resident cold page for replacement.
	for !c.handCold.ptype.isResidentCold() {
		c.handCold = c.handCold.next()
	}

	if atomic.LoadInt32(&c.handCold.referenced) == 1 {
		// If its bit is set and it is in its test period, we turn the cold page into a hot page,
		// and ask HAND for its actions, because an access during the test period indicates a
		// competitively small reuse distance. If its bit is set but it is not in its test period,
		// there are no status change as well as HAND actions. Its reference bit is reset, and we
		// move it to the list head.
		if c.handCold.ptype.isInTest() {
			if c.canPromote(c.handCold) {
				c.moveToHead(c.handCold, etHot)
			} else {
				c.moveToHead(c.handCold, etColdResInTest)
			}
		} else {
			c.moveToHead(c.handCold, etColdResInTest)
		}
	} else {
		// If the reference bit of the cold page currently pointed to by handCold is unset, we replace
		// the cold page for a free space. If the replaced cold page is in its test period, then it
		// will remain in the list as a non-resident cold page until it runs out of its test period.
		// If the replaced cold page is not in its test period, we move it out of the clock.
		if c.handCold.ptype.isInTest() {
			c.handCold.setValue(nil)
			c.setEntryType(c.handCold, etColdNonRes)
			c.handCold = c.handCold.next()
		} else {
			c.metaEvict(c.handCold)
		}
		// We keep track the number of non-resident cold pages. Once the number exceeds the limit, we
		// terminate the test period of the cold page pointed to by handTest.
		for c.sizeNonResCold > c.targetSize() {
			c.runHandTest()
		}
	}
}

// runHandHot demotes a hot node between the handHot and trigger node. If the demotion was
// successful it returns true, otherwise it returns false.
func (c *shard) runHandHot(trigger *entry) bool {
	// What triggers the movement of handHot is that a cold page (== argument "trigger") is found to
	// have been accessed in its test period and thus turns into a hot page, which "maybe"
	// accordingly turns the hot page with the largest recency into a cold page.
	c.nextHandHot()

	demoted := false
	for c.handHot != trigger {
		if c.handHot.ptype == etHot {
			// If the reference bit of the hot page pointed to by handHot is unset, we can simply change
			// its status and then move the hand forward. However, if the bit is set, which indicates
			// the page has been re-accessed, we spare this page, reset its reference bit and keep it as
			// a hot page. This is because the actual access time of the hot page could be earlier than
			// the cold page. Then we move the hand forward and do the same on the hot pages with their
			// bits set until the hand encounters a hot page with a reference bit of zero. Then the hot
			// page turns into a cold page.
			if atomic.LoadInt32(&c.handHot.referenced) == 1 {
				c.moveToHead(c.handHot, etHot)
			} else {
				c.moveToHead(c.handHot, etColdRes)
				demoted = true
				break
			}
		} else {
			// Whenever the hand encounters a cold page, it will terminate the page’s test period. The
			// hand will also remove the cold page from the clock if it is non-resident (the most
			// probable case). It actually does the work on the cold page on behalf of handTest.
			c.handHot = c.handHot.next()
			c.terminateTestPeriod(c.handHot.prev())
		}
	}
	// Finally the hand stops at a next hot page.
	c.nextHandHot()
	return demoted
}

func (c *shard) runHandTest() {
	if c.handTest == nil {
		c.handTest = c.handHot
		if c.handTest == nil {
			c.handTest = c.listHead.next()
		}
	}
	c.handTest = c.handTest.next()
	c.terminateTestPeriod(c.handTest.prev())
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
			maxSize:    size / int64(len(c.shards)),
			coldTarget: size / int64(len(c.shards)),
		}
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
		m.Size += s.sizeHot + s.sizeResCold
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
