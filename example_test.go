package dot_test

import (
	"fmt"
	"github.com/traviscline/dot"
)

func ExampleNewGraph() {
	g := dot.NewGraph("G")
	g.Set("label", "Example graph")
	fmt.Println(g)
	// Output:
	// digraph G {
	// label="Example graph";
	// }
}
