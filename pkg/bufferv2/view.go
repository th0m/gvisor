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
	"bytes"
	"fmt"
	"sync"
)

var viewPool = &sync.Pool{
	New: func() interface{} {
		return &View{}
	},
}

// View is a window into a shared chunk. Views are held by Buffers in
// viewLists to represent contiguous memory.
type View struct {
	viewEntry
	read  int
	write int
	chunk *chunk
}

// NewView creates a new view and points it to a newly allocated
// chunk that is at least as big as size.
func NewView(size int) *View {
	c := newChunk(size)
	v := viewPool.Get().(*View)
	v.read = 0
	v.write = 0
	v.chunk = c
	return v
}

// NewViewWithData creates a new view and initializes it with data.
func NewViewWithData(data []byte) *View {
	c := newChunk(len(data))
	v := viewPool.Get().(*View)
	v.read = 0
	v.write = 0
	v.chunk = c
	v.Write(data)
	return v
}

// Clone creates a shallow clone of v where the underlying chunk is shared.
func (v *View) Clone() *View {
	newV := viewPool.Get().(*View)
	*newV = *v
	v.chunk.IncRef()
	return newV
}

// Release releases the chunk held by v and returns v to the pool.
func (v *View) Release() {
	v.chunk.DecRef()
	v.chunk = nil
	viewPool.Put(v)
}

func (v *View) sharesChunk() bool {
	return v.chunk.refCount.Load() > 1
}

// BasePtr returns a pointer to the first byte in this view's chunk.
func (v *View) BasePtr() *byte {
	return &v.chunk.data[0]
}

// Full indicates the chunk is full.
//
// This indicates there is no capacity left to write.
func (v *View) Full() bool {
	return v.write == len(v.chunk.data)
}

// Capacity returns the total size of this view's chunk.
func (v *View) Capacity() int {
	return len(v.chunk.data)
}

// ReadSize returns the number of bytes available for reading.
func (v *View) ReadSize() int {
	return v.write - v.read
}

// ReadMove advances the read index by the given amount.
func (v *View) ReadMove(n int) {
	v.read += n
}

// ReadSlice returns the read slice for this chunk.
func (v *View) ReadSlice() []byte {
	return v.chunk.data[v.read:v.write]
}

// WriteSize returns the number of bytes available for writing.
func (v *View) WriteSize() int {
	return len(v.chunk.data) - v.write
}

// Write writes data to the view's chunk starting at the v.write index. If the
// view's chunk has a reference count greater than 1, the chunk is copied first
// and then written to.
func (v *View) Write(data []byte) int {
	done := v.WriteAt(v.write-v.read, data)
	return done
}

// WriteAt writes data to the views's chunk starting at start. If the
// view's chunk has a reference count greater than 1, the chunk is copied first
// and then written to.
func (v *View) WriteAt(start int, data []byte) int {
	if start < 0 || start > v.ReadSize() {
		panic(fmt.Sprintf("WriteAt(...): start index out of bounds: want 0 < start < %d, got start=%d", v.ReadSize(), start))
	}
	c := v.chunk
	if v.sharesChunk() {
		defer v.chunk.DecRef()
		c = v.chunk.Copy()
	}
	n := copy(c.data[v.read+start:], data)
	v.chunk = c
	v.write = v.read + start + n
	return n
}

// WriteMove advances the write index by the given amount.
func (v *View) WriteMove(n int) {
	v.write += n
}

// WriteSlice returns the write slice for the underlying chunk.
func (v *View) WriteSlice() []byte {
	c := v.chunk
	if v.sharesChunk() {
		defer v.chunk.DecRef()
		c = v.chunk.Copy()
	}
	v.chunk = c
	return v.chunk.data[v.write:]
}

// Reader returns a bytes.Reader for c.
func (v *View) Reader() bytes.Reader {
	var r bytes.Reader
	r.Reset(v.ReadSlice())
	return r
}
