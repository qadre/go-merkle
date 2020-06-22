go-merkle
=========

A fixed Merkle Tree implementation in Go

Example Use
===========

```go
package main

import (
    "crypto/sha256"
    "io/ioutil"
    "fmt"

    "github.com/qadre/go-merkle"
)

func splitData(data []byte, size int) [][]byte {
    /* Splits data into an array of slices of len(size) */
    count := len(data) / size
    blocks := make([][]byte, 0, count)
    for i := 0; i < count; i++ {
        block := data[i*size : (i+1)*size]
        blocks = append(blocks, block)
    }
    if len(data)%size != 0 {
        blocks = append(blocks, data[len(blocks)*size:])
    }
    return blocks
}

func main() {
    // Grab some data to make the tree out of, and partition
    data, err := ioutil.ReadFile("testdata") // assume testdata exists
    if err != nil {
        fmt.Println(err)
        return
    }
    blocks := splitData(data, 32)

    // Create & generate the tree
    tree := merkle.NewTree()
    // Create & generate the tree with sorted hashes
    // A tree with pair wise sorted hashes allows for a representation of proofs which are more space efficient
    //tree := merkle.NewTreeWithOpts(TreeOptions{EnableHashSorting: true})
    err = tree.Generate(blocks, sha256.New())
    if err != nil {
        fmt.Println(err)
        return
    }

    fmt.Printf("Height: %d\n", tree.Height())
    fmt.Printf("Root: %v\n", tree.Root())
    fmt.Printf("N Leaves: %v\n", len(tree.Leaves()))
    fmt.Printf("Height 2: %v\n", tree.GetNodesAtHeight(2))
}

```
