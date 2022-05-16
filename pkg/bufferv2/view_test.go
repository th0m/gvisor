// Copyright 2022 The gVisor Authors.
//
// Licensed under the Apache License, Version 2.0 (the "License");
// you may not use this file except in compliance with the License.
// You may obtain a copy of the License at
//
//     http://www.apache.org/licenses/LICENSE-2.0
//
// Unless required by applicable law or agreed to in writing, software
// distributed under the License is distributed on an "AS IS" BASIS,
// WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
// See the License for the specific language governing permissions and
// limitations under the License.

package buffer

import (
	"math/rand"
	"testing"

	"github.com/google/go-cmp/cmp"
)

func TestNewView(t *testing.T) {
	for sz := baseChunkSize; sz < maxChunkSize; sz <<= 1 {
		v := NewView(sz - 1)
		defer v.Release()

		if v.Capacity() != sz {
			t.Errorf("v.Capacity() = %d, want %d", v.Capacity(), sz)
		}
		if v.WriteSize() != sz {
			t.Errorf("v.WriteSize() = %d, want %d", v.WriteSize(), sz)
		}
		if v.ReadSize() != 0 {
			t.Errorf("v.ReadSize() = %d, want %d", v.ReadSize(), 0)
		}
	}

	// Allocating from heap should produce a chunk with the exact size requested
	// instead of a chunk where the size is contingent on the pool it came from.
	viewSize := maxChunkSize + 1
	v := NewView(viewSize)
	defer v.Release()
	if v.Capacity() != viewSize {
		t.Errorf("v.Capacity() = %d, want %d", v.Capacity(), viewSize)
	}
}

func TestClone(t *testing.T) {
	orig := NewView(100)
	clone := orig.Clone()
	if orig.chunk != clone.chunk {
		t.Errorf("orig.Clone().chunk = %p, want %p", clone.chunk, orig.chunk)
	}
	if orig.chunk.refCount.Load() != 2 {
		t.Errorf("got orig.chunk.chunkRefs.Load() = %d, want 2", orig.chunk.refCount.Load())
	}
	orig.Release()
	if clone.chunk.refCount.Load() != 1 {
		t.Errorf("got clone.chunk.chunkRefs.Load() = %d, want 1", clone.chunk.refCount.Load())
	}
	clone.Release()
}

func TestWrite(t *testing.T) {
	for _, tc := range []struct {
		name      string
		view      *View
		initData  []byte
		writeSize int
	}{
		{
			name:      "empty view",
			view:      NewView(100),
			writeSize: 50,
		},
		{
			name:      "full view",
			view:      NewView(100),
			initData:  make([]byte, 100),
			writeSize: 50,
		},
		{
			name:      "full write to partially full view",
			view:      NewView(100),
			initData:  make([]byte, 20),
			writeSize: 50,
		},
		{
			name:      "partial write to partially full view",
			view:      NewView(100),
			initData:  make([]byte, 80),
			writeSize: 50,
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			tc.view.Write(tc.initData)
			defer tc.view.Release()
			origWriteSize := tc.view.WriteSize()

			var orig []byte
			orig = append(orig, tc.view.ReadSlice()...)
			toWrite := make([]byte, tc.writeSize)
			rand.Read(toWrite)

			n := tc.view.Write(toWrite)

			if n > origWriteSize {
				t.Errorf("got tc.view.Write() = %d, want <=%d", n, origWriteSize)
			}
			if tc.writeSize > origWriteSize {
				toWrite = toWrite[:origWriteSize]
			}
			if tc.view.WriteSize() != tc.view.Capacity()-(len(toWrite)+len(orig)) {
				t.Errorf("got tc.view.WriteSize() = %d, want %d", tc.view.WriteSize(), tc.view.Capacity()-(len(toWrite)+len(orig)))
			}
			if !cmp.Equal(tc.view.ReadSlice(), append(orig, toWrite...)) {
				t.Errorf("got tc.view.ReadSlice() = %d, want %d", tc.view.ReadSlice(), toWrite)
			}
		})
	}
}

func TestWriteAt(t *testing.T) {
	for _, tc := range []struct {
		name       string
		view       *View
		initData   []byte
		writeSize  int
		writeIndex int
		readIndex  int
	}{
		{
			name:       "empty view",
			view:       NewView(100),
			writeSize:  50,
			writeIndex: 0,
		},
		{
			name:       "full write to partially full view",
			view:       NewView(100),
			initData:   make([]byte, 20),
			writeSize:  50,
			writeIndex: 10,
		},
		{
			name:       "partial write to partially full view",
			view:       NewView(100),
			initData:   make([]byte, 80),
			writeSize:  50,
			writeIndex: 80,
		},
		{
			name:       "write to trimmed view",
			view:       NewView(100),
			initData:   make([]byte, 25),
			writeSize:  50,
			writeIndex: 25,
			readIndex:  25,
		},
	} {
		t.Run(tc.name, func(t *testing.T) {
			tc.view.ReadMove(tc.readIndex)
			tc.view.WriteMove(tc.readIndex)
			tc.view.Write(tc.initData)
			defer tc.view.Release()

			toWrite := make([]byte, tc.writeSize)
			rand.Read(toWrite)

			want := make([]byte, tc.view.Capacity())
			copy(want, tc.view.ReadSlice())
			n := copy(want[tc.writeIndex:], toWrite)
			want = want[:tc.writeIndex+n]

			tc.view.WriteAt(tc.writeIndex, toWrite)

			if !cmp.Equal(want, tc.view.ReadSlice()) {
				t.Errorf("got v.ReadSlice() = %v, want %v", tc.view.ReadSlice(), want)
			}
		})
	}
}

func TestWriteToCloned(t *testing.T) {
	orig := NewView(100)
	toWrite := make([]byte, 20)
	rand.Read(toWrite)
	orig.Write(toWrite)

	clone := orig.Clone()
	clone.Write(toWrite)

	if !cmp.Equal(orig.ReadSlice(), toWrite) {
		t.Errorf("got orig.ReadSlice() = %v, want %v", orig.ReadSlice(), toWrite)
	}

	toWrite = append(toWrite, toWrite...)
	if !cmp.Equal(clone.ReadSlice(), toWrite) {
		t.Errorf("got clone.ReadSlice() = %v, want %v", clone.ReadSlice(), toWrite)
	}
}
