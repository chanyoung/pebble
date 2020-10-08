// Copyright 2018. All rights reserved. Use of this source code is governed by
// an MIT-style license that can be found in the LICENSE file.

package cache

import (
	"bufio"
	"bytes"
	"fmt"
	"os"
	"runtime"
	"strconv"
	"strings"
	"sync"
	"testing"
	"time"

	"github.com/cockroachdb/pebble/internal/base"
	"github.com/stretchr/testify/require"
	"golang.org/x/exp/rand"
)

func TestCache(t *testing.T) {
	// Test data was generated from the python code
	f, err := os.Open("testdata/cache")
	require.NoError(t, err)

	cache := newShards(200, 1)
	defer cache.Unref()

	scanner := bufio.NewScanner(f)
	line := 1

	for scanner.Scan() {
		fields := bytes.Fields(scanner.Bytes())

		key, err := strconv.Atoi(string(fields[0]))
		require.NoError(t, err)

		wantHit := fields[1][0] == 'h'

		var hit bool
		h := cache.Get(1, base.FileNum(key), 0)
		if v := h.Get(); v == nil {
			value := cache.Alloc(1)
			value.Buf()[0] = fields[0][0]
			cache.Set(1, base.FileNum(key), 0, value).Release()
		} else {
			hit = true
			if !bytes.Equal(v, fields[0][:1]) {
				t.Errorf("%d: cache returned bad data: got %s , want %s\n", line, v, fields[0][:1])
			}
		}
		h.Release()
		if hit != wantHit {
			t.Errorf("%d: cache hit mismatch: got %v, want %v\n", line, hit, wantHit)
		}
		line++
	}
}

func testValue(cache *Cache, s string, repeat int) *Value {
	b := bytes.Repeat([]byte(s), repeat)
	v := cache.Alloc(len(b))
	copy(v.Buf(), b)
	return v
}

func TestCacheDelete(t *testing.T) {
	cache := newShards(100, 1)
	defer cache.Unref()

	cache.Set(1, 0, 0, testValue(cache, "a", 5)).Release()
	cache.Set(1, 1, 0, testValue(cache, "a", 5)).Release()
	cache.Set(1, 2, 0, testValue(cache, "a", 5)).Release()
	if expected, size := int64(15), cache.Size(); expected != size {
		t.Fatalf("expected cache size %d, but found %d", expected, size)
	}
	cache.Delete(1, 1, 0)
	if expected, size := int64(10), cache.Size(); expected != size {
		t.Fatalf("expected cache size %d, but found %d", expected, size)
	}
	if h := cache.Get(1, 0, 0); h.Get() == nil {
		t.Fatalf("expected to find block 0/0")
	} else {
		h.Release()
	}
	if h := cache.Get(1, 1, 0); h.Get() != nil {
		t.Fatalf("expected to not find block 1/0")
	} else {
		h.Release()
	}
	// Deleting a non-existing block does nothing.
	cache.Delete(1, 1, 0)
	if expected, size := int64(10), cache.Size(); expected != size {
		t.Fatalf("expected cache size %d, but found %d", expected, size)
	}
}

func TestEvictFile(t *testing.T) {
	cache := newShards(100, 1)
	defer cache.Unref()

	cache.Set(1, 0, 0, testValue(cache, "a", 5)).Release()
	cache.Set(1, 1, 0, testValue(cache, "a", 5)).Release()
	cache.Set(1, 2, 0, testValue(cache, "a", 5)).Release()
	cache.Set(1, 2, 1, testValue(cache, "a", 5)).Release()
	cache.Set(1, 2, 2, testValue(cache, "a", 5)).Release()
	if expected, size := int64(25), cache.Size(); expected != size {
		t.Fatalf("expected cache size %d, but found %d", expected, size)
	}
	cache.EvictFile(1, 0)
	if expected, size := int64(20), cache.Size(); expected != size {
		t.Fatalf("expected cache size %d, but found %d", expected, size)
	}
	cache.EvictFile(1, 1)
	if expected, size := int64(15), cache.Size(); expected != size {
		t.Fatalf("expected cache size %d, but found %d", expected, size)
	}
	cache.EvictFile(1, 2)
	if expected, size := int64(0), cache.Size(); expected != size {
		t.Fatalf("expected cache size %d, but found %d", expected, size)
	}
}

func TestEvictAll(t *testing.T) {
	// Verify that it is okay to evict all of the data from a cache. Previously
	// this would trigger a nil-pointer dereference.
	cache := newShards(100, 1)
	defer cache.Unref()

	cache.Set(1, 0, 0, testValue(cache, "a", 101)).Release()
	cache.Set(1, 1, 0, testValue(cache, "a", 101)).Release()
}

func TestMultipleDBs(t *testing.T) {
	cache := newShards(100, 1)
	defer cache.Unref()

	cache.Set(1, 0, 0, testValue(cache, "a", 5)).Release()
	cache.Set(2, 0, 0, testValue(cache, "b", 5)).Release()
	if expected, size := int64(10), cache.Size(); expected != size {
		t.Fatalf("expected cache size %d, but found %d", expected, size)
	}
	cache.EvictFile(1, 0)
	if expected, size := int64(5), cache.Size(); expected != size {
		t.Fatalf("expected cache size %d, but found %d", expected, size)
	}
	h := cache.Get(1, 0, 0)
	if v := h.Get(); v != nil {
		t.Fatalf("expected not present, but found %s", v)
	}
	h = cache.Get(2, 0, 0)
	if v := h.Get(); string(v) != "bbbbb" {
		t.Fatalf("expected bbbbb, but found %s", v)
	} else {
		h.Release()
	}
}

func TestZeroSize(t *testing.T) {
	cache := newShards(0, 1)
	defer cache.Unref()

	cache.Set(1, 0, 0, testValue(cache, "a", 5)).Release()
}

func TestReserve(t *testing.T) {
	cache := newShards(4, 2)
	defer cache.Unref()

	cache.Set(1, 0, 0, testValue(cache, "a", 1)).Release()
	cache.Set(2, 0, 0, testValue(cache, "a", 1)).Release()
	require.EqualValues(t, 2, cache.Size())
	r := cache.Reserve(1)
	require.EqualValues(t, 0, cache.Size())
	cache.Set(1, 0, 0, testValue(cache, "a", 1)).Release()
	cache.Set(2, 0, 0, testValue(cache, "a", 1)).Release()
	cache.Set(3, 0, 0, testValue(cache, "a", 1)).Release()
	cache.Set(4, 0, 0, testValue(cache, "a", 1)).Release()
	require.EqualValues(t, 2, cache.Size())
	r()
	require.EqualValues(t, 2, cache.Size())
	cache.Set(1, 0, 0, testValue(cache, "a", 1)).Release()
	cache.Set(2, 0, 0, testValue(cache, "a", 1)).Release()
	require.EqualValues(t, 4, cache.Size())
}

func TestReserveDoubleRelease(t *testing.T) {
	cache := newShards(100, 1)
	defer cache.Unref()

	r := cache.Reserve(10)
	r()

	result := func() (result string) {
		defer func() {
			if v := recover(); v != nil {
				result = fmt.Sprint(v)
			}
		}()
		r()
		return ""
	}()
	const expected = "pebble: cache reservation already released"
	if expected != result {
		t.Fatalf("expected %q, but found %q", expected, result)
	}
}

func TestCacheStressSetExisting(t *testing.T) {
	cache := newShards(1, 1)
	defer cache.Unref()

	var wg sync.WaitGroup
	for i := 0; i < 10; i++ {
		wg.Add(1)
		go func(i int) {
			defer wg.Done()
			for j := 0; j < 10000; j++ {
				cache.Set(1, 0, uint64(i), testValue(cache, "a", 1)).Release()
				runtime.Gosched()
			}
		}(i)
	}
	wg.Wait()
}

func BenchmarkCacheGet(b *testing.B) {
	const size = 100000

	cache := newShards(size, 1)
	defer cache.Unref()

	for i := 0; i < size; i++ {
		v := testValue(cache, "a", 1)
		cache.Set(1, 0, uint64(i), v).Release()
	}

	b.ResetTimer()
	b.RunParallel(func(pb *testing.PB) {
		rng := rand.New(rand.NewSource(uint64(time.Now().UnixNano())))

		for pb.Next() {
			h := cache.Get(1, 0, uint64(rng.Intn(size)))
			if h.Get() == nil {
				b.Fatal("failed to lookup value")
			}
			h.Release()
		}
	})
}

func TestCacheHitRatio(t *testing.T) {
	// Test data was generated from the python code
	f, err := os.Open("testdata/a64zipf")
	require.NoError(t, err)

	cache := newShards(536870912, 32)
	defer cache.Unref()

	scanner := bufio.NewScanner(f)

	allocMap := make(map[string]*Value)
	reserveMap := make(map[string]func())

	prevHit := int64(0)
	prevMiss := int64(0)
	i := int64(0)
	for scanner.Scan() {
		fields := bytes.Fields(scanner.Bytes())

		if strings.Compare("Get", string(fields[0])) == 0 {
			id, err := strconv.ParseUint(string(fields[1]), 10, 64)
			require.NoError(t, err)
			fileNumUint, err := strconv.ParseUint(string(fields[2]), 10, 64)
			require.NoError(t, err)
			fileNum := base.FileNum(fileNumUint)
			offset, err := strconv.ParseUint(string(fields[3]), 10, 64)
			require.NoError(t, err)
			h := cache.Get(id, fileNum, offset)
			h.Release()
			i++
		} else if strings.Compare("Set", string(fields[0])) == 0 {
			id, err := strconv.ParseUint(string(fields[1]), 10, 64)
			require.NoError(t, err)
			fileNumUint, err := strconv.ParseUint(string(fields[2]), 10, 64)
			require.NoError(t, err)
			fileNum := base.FileNum(fileNumUint)
			offset, err := strconv.ParseUint(string(fields[3]), 10, 64)
			require.NoError(t, err)
			valueID := string(fields[4])

			v, ok := allocMap[valueID]
			if !ok {
				t.Fatal("Try set with unallocated value")
			}
			h := cache.Set(id, fileNum, offset, v)
			h.Release()
		} else if strings.Compare("Delete", string(fields[0])) == 0 {
			id, err := strconv.ParseUint(string(fields[1]), 10, 64)
			require.NoError(t, err)
			fileNumUint, err := strconv.ParseUint(string(fields[2]), 10, 64)
			require.NoError(t, err)
			fileNum := base.FileNum(fileNumUint)
			offset, err := strconv.ParseUint(string(fields[3]), 10, 64)
			require.NoError(t, err)
			cache.Delete(id, fileNum, offset)
		} else if strings.Compare("EvictFile", string(fields[0])) == 0 {
			id, err := strconv.ParseUint(string(fields[1]), 10, 64)
			require.NoError(t, err)
			fileNumUint, err := strconv.ParseUint(string(fields[2]), 10, 64)
			require.NoError(t, err)
			fileNum := base.FileNum(fileNumUint)
			cache.EvictFile(id, fileNum)
		} else if strings.Compare("Alloc", string(fields[0])) == 0 {
			valueID := string(fields[1])
			n, err := strconv.Atoi(string(fields[2]))
			require.NoError(t, err)
			v := cache.Alloc(n)
			allocMap[valueID] = v
		} else if strings.Compare("Free", string(fields[0])) == 0 {
			valueID := string(fields[1])
			v, ok := allocMap[valueID]
			if !ok {
				t.Fatal("Try free with unallocated value")
			}
			delete(allocMap, valueID)
			cache.Free(v)
		} else if strings.Compare("Reserve", string(fields[0])) == 0 {
			reserveID := string(fields[1])
			n, err := strconv.Atoi(string(fields[2]))
			require.NoError(t, err)
			f := cache.Reserve(n)
			reserveMap[reserveID] = f
		} else if strings.Compare("Unreserve", string(fields[0])) == 0 {
			reserveID := string(fields[1])
			f, ok := reserveMap[reserveID]
			if !ok {
				t.Fatal("Try unreserve with invalid reserve id")
			}
			delete(reserveMap, reserveID)
			f()
		} else {
			t.Fatalf("Unknown: %s\n", string(fields[0]))
		}

		if i%1000 == 0 {
			m := cache.Metrics()
			hit := m.Hits - prevHit
			miss := m.Misses - prevMiss
			sum := hit + miss
			if sum != 0 {
				t.Logf("Hits: %d Misses: %d ratio: %f\n", hit, miss, float64(hit)/float64(sum))
				prevHit = m.Hits
				prevMiss = m.Misses
			}
		}
	}
	m := cache.Metrics()
	hit := m.Hits
	miss := m.Misses
	sum := hit + miss
	t.Logf("[Total] Hits: %d Misses: %d ratio: %f\n", hit, miss, float64(hit)/float64(sum))
}
