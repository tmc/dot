# dot

dot is a Go package that provides support for working with the DOT language, which is used for describing graphs in Graphviz.

## Features

- Create and manipulate graph structures
- Add nodes, edges, and subgraphs
- Set attributes for graphs, nodes, and edges
- Generate DOT language output
- Import and export graphs in DOT and JSON formats
- Graph analysis and algorithms (e.g., topological sort, shortest path)
- Graph visualization helpers (PNG and SVG output)

## Installation

To install the dot package, use the following command:

```
go install github.com/tmc/dot@latest
```

## Usage

Here's a simple example of how to use the dot package:

```go
package main

import (
    "fmt"
    "github.com/tmc/dot"
)

func main() {
    g := dot.NewGraph("Example")
    g.Set("label", "This is an example graph")

    n1 := dot.NewNode("Node1")
    n1.Set("shape", "box")
    n2 := dot.NewNode("Node2")
    n2.Set("color", "red")

    g.AddNode(n1)
    g.AddNode(n2)

    e := dot.NewEdge(n1, n2)
    e.Set("label", "connects to")
    g.AddEdge(e)

    fmt.Println(g.String())
}
```

This will output the DOT language representation of the graph.

## Documentation

For detailed documentation, please refer to the [GoDoc](https://pkg.go.dev/github.com/tmc/dot) page.

## Contributing

Contributions are welcome! Please feel free to submit a Pull Request.

## License

This project is licensed under the MIT License - see the [LICENSE](LICENSE) file for details.