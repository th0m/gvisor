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
	"fmt"

	"gvisor.dev/gvisor/pkg/sync"
)

const (
	// This is the size of the buffers in the first pool. Each subsquent pool
	// creates payloads 2^(pool index) times larger than the first pool's payloads.
	baseChunkSize = 1 << 6 // 64

	// The larget payload size that we pool. Payloads larget than this will
	// allocated from the heap and garbage collected as normal.
	maxChunkSize = 1 << 16 // 65536

	// The number of buffer pools we have for use.
	numPools = 10
)

// bufferPools is a collection of pools for payloads of different sizes. The
// size of the payloads doubles in each successive pool.
var chunkPools map[int]*sync.Pool

func init() {
	chunkPools = make(map[int]*sync.Pool, numPools)
	for i := 0; i < numPools; i++ {
		chunkSize := baseChunkSize * (1 << i)
		chunkPools[chunkSize] = makeChunkPool(chunkSize)
	}
}

func makeChunkPool(chunkSize int) *sync.Pool {
	return &sync.Pool{
		New: func() interface{} {
			c := &chunk{
				data: make([]byte, chunkSize),
			}
			return c
		},
	}
}

// Precondition: 0 <= size <= maxChunkSize
func getChunkPool(size int) *sync.Pool {
	poolChunkSize := baseChunkSize
	for sz := size / baseChunkSize; sz != 0; sz >>= 1 {
		poolChunkSize <<= 1
	}
	return chunkPools[poolChunkSize]
}

// Chunk represents a slice of pooled memory.
type chunk struct {
	chunkRefs
	data []byte
}

func newChunk(size int) *chunk {
	var c *chunk
	if size > maxChunkSize {
		c = &chunk{
			data: make([]byte, size),
		}
	} else {
		pool := getChunkPool(size)
		c = pool.Get().(*chunk)
	}
	c.InitRefs()
	return c
}

func (c *chunk) DecRef() {
	c.chunkRefs.DecRef(func() {
		if len(c.data) > maxChunkSize {
			c.data = nil
			return
		}
		pool, ok := chunkPools[len(c.data)]
		if !ok {
			panic(fmt.Sprintf("pool for chunk len %d does not exist", len(c.data)))
		}
		pool.Put(c)
	})
}

func (c *chunk) Copy() *chunk {
	cpy := newChunk(len(c.data))
	copy(cpy.data, c.data)
	return cpy
}
