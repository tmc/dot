package dot_test

import (
	"fmt"
	"strings"
	"testing"

	"github.com/google/go-cmp/cmp"
	"github.com/tmc/dot"
)

func TestQuotingIfNecessary(t *testing.T) {
	cases := map[string]string{
		"foo":       "foo",
		"\"foo\"":   "\"foo\"",
		"foo bar":   "\"foo bar\"",
		"Allen, C.": "\"Allen, C.\"",
	}

	for input, expected := range cases {
		if dot.QuoteIfNecessary(input) != expected {
			t.Errorf("'%s' != '%s'", dot.QuoteIfNecessary(input), expected)
		}
	}
}

func TestGraphPrinting(t *testing.T) {
	g1 := dot.NewGraph("foo")
	expected1 := "digraph foo {\n}\n"
	g2 := dot.NewGraph("foo bar")
	expected2 := "digraph \"foo bar\" {\n}\n"

	if fmt.Sprint(g1) != expected1 {
		t.Errorf("'%s' != '%s'", fmt.Sprint(g1), expected1)
	}
	if fmt.Sprint(g2) != expected2 {
		t.Errorf("'%s' != '%s'", fmt.Sprint(g2), expected2)
	}
}

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
	node.Set("label", "value with spaces")

	node = dot.NewNode("html")
	node.Set("shape", "plain")
	node.Set("label", "<<B>bold</B>>")
	g.AddNode(node)

	expected = "digraph Test {\nlegend [label=\"value with spaces\", shape=box];\nhtml [label=<<B>bold</B>>, shape=plain];\n}\n"
	if fmt.Sprint(g) != expected {
		t.Errorf("'%s' != '%s'", fmt.Sprint(g), expected)
	}
}

func TestCreateSimpleNode(t *testing.T) {
	node := dot.NewNode("nodename")
	node.Set("shape", "box")
	node.Set("label", "mine")

	expected := "nodename [label=mine, shape=box];"
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
	if err := g.Set("this_does_not_exist", "and_should_error"); err == nil {
		t.Error("Did not get error when setting invalid attribute on g", g)
	} else if !strings.Contains(err.Error(), "invalid graph attribute") {
		t.Errorf("Expected error message containing 'invalid graph attribute', got %v", err)
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
	if g.GetSubgraphs()[0].Name != s.Name {
		t.Error(g.GetSubgraphs()[0].Name, " != ", s.Name)
	}

	expected := `digraph G {
subgraph SG {
}

}
`

	if fmt.Sprint(g) != expected {
		t.Errorf("'%s' != '%s'", g, expected)
	}
}

func TestEdgeAddition(t *testing.T) {
	simple_graph := `digraph G {
graph [
  label="this is a graph";
];
a -> b
}
`
	g := dot.NewGraph("G")
	g.Set("label", "this is a graph")
	a, b := dot.NewNode("a"), dot.NewNode("b")
	e := dot.NewEdge(a, b)
	if _, err := g.AddEdge(e); err != nil {
		t.Error("Error adding edge to graph", err)
	}

	if diff := cmp.Diff(fmt.Sprint(g), simple_graph); diff != "" {
		t.Errorf("unexpected graph (-got +want):\n%s", diff)
	}

}

func TestQuoting(t *testing.T) {
	g := dot.NewGraph("G")
	a, b := dot.NewNode("192.168.1.1"), dot.NewNode("192.168.1.2")
	e := dot.NewEdge(a, b)
	g.AddEdge(e)

	expected := `digraph G {
"192.168.1.1" -> "192.168.1.2"
}
`
	if fmt.Sprint(g) != expected {
		t.Errorf("'%s' != '%s'", g, expected)
	}

}
