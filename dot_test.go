package dot

import (
	dot "."
	"fmt"
	"testing"
)

func TestCreateSimpleGraphWithNode(t *testing.T) {
	g := dot.NewGraph("Test")

	expected := "digraph Test {\n}\n"
	if fmt.Sprint(g) != expected {
		t.Errorf("'%s' != '%s'", fmt.Sprint(g), expected)
	}
	g.SetType(dot.GRAPH)

	expected = "graph Test {\n}\n"
	if fmt.Sprint(g) != expected {
		t.Errorf("'%s' != '%s'", fmt.Sprint(g), expected)
	}
	g.SetType(dot.DIGRAPH)

	node := dot.NewNode("legend")
	node.Set("shape", "box")
	g.AddNode(node)
	node.Set("label", "mine")

	expected = "digraph Test {\nlegend [label=\"mine\", shape=\"box\"];\n}\n"
	if fmt.Sprint(g) != expected {
		t.Errorf("'%s' != '%s'", fmt.Sprint(g), expected)
	}
}

func TestCreateSimpleNode(t *testing.T) {
	node := dot.NewNode("nodename")
	node.Set("shape", "box")
	node.Set("label", "mine")

	//@todo remove need for quotes on simple values
	//expected := "nodename [label=mine, shape=box];"
	expected := "nodename [label=\"mine\", shape=\"box\"];"
	if fmt.Sprint(node) != expected {
		t.Errorf("'%s' != '%s'", fmt.Sprint(node), expected)
	}
}

func TestGraphAttributeSetting(t *testing.T) {
	g := dot.NewGraph("Test")
	if g.Set("label", "foo") != nil {
		t.Error("Error setting value on g", g)
	}
	g.Set("Damping", "x")
	if g.Set("this_does_not_exist", "and_should_error") != dot.AttributeError {
		t.Error("Did not get godot.AttributeError when setting invalid attribute on g", g)
	}
}

func TestSubGraphs(t *testing.T) {
	g := dot.NewGraph("G")
	s := dot.NewSubgraph("SG")

	subgraphs := make([]*dot.SubGraph, 0)
	if subgraphs = g.GetSubgraphs(); len(subgraphs) != 0 {
		t.Error("Non-empty subgraphs returned:", subgraphs)
	}
	g.AddSubgraph(s)
	if g.GetSubgraphs()[0].Name() != s.Name() {
		t.Error(g.GetSubgraphs()[0].Name(), " != ", s.Name())
	}
}

func TestEdgeAddition(t *testing.T) {
	simple_graph := `digraph G {
label="this is a graph";
a -> b
}
`
	g := dot.NewGraph("G")
	g.Set("label", "this is a graph")
	a, b := dot.NewNode("a"), dot.NewNode("b")
	e := dot.NewEdge(a, b)
	g.AddEdge(e)

	if fmt.Sprint(g) != simple_graph {
		t.Errorf("'%s' != '%s'", g, simple_graph)
	}

}
