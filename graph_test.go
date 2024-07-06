package dot

import (
	"testing"
)

func TestNewGraph(t *testing.T) {
	g := NewGraph("TestGraph")
	if g.Name != "TestGraph" {
		t.Errorf("Expected graph name to be 'TestGraph', got '%s'", g.Name)
	}
	if g.graphType != DIGRAPH {
		t.Errorf("Expected default graph type to be DIGRAPH, got %v", g.graphType)
	}
	if len(g.nodes) != 0 {
		t.Errorf("Expected new graph to have 0 nodes, got %d", len(g.nodes))
	}
	if len(g.edges) != 0 {
		t.Errorf("Expected new graph to have 0 edges, got %d", len(g.edges))
	}
}

func TestGraphSetType(t *testing.T) {
	g := NewGraph("TestGraph")
	g.SetType(GRAPH)
	if g.graphType != GRAPH {
		t.Errorf("Expected graph type to be GRAPH, got %v", g.graphType)
	}
}

func TestGraphAddNode(t *testing.T) {
	g := NewGraph("TestGraph")
	n := NewNode("TestNode")
	g.AddNode(n)
	if len(g.nodes) != 1 {
		t.Errorf("Expected graph to have 1 node, got %d", len(g.nodes))
	}
	if len(g.nodes["TestNode"]) == 0 || g.nodes["TestNode"][0] != n {
		t.Errorf("Expected to find node 'TestNode' in graph")
	}
}

func TestGraphAddEdge(t *testing.T) {
	g := NewGraph("TestGraph")
	n1 := NewNode("Node1")
	n2 := NewNode("Node2")
	e := NewEdge(n1, n2)
	g.AddEdge(e)
	if len(g.edges) != 1 {
		t.Errorf("Expected graph to have 1 edge, got %d", len(g.edges))
	}
	if len(g.edges[e.Name()]) == 0 || g.edges[e.Name()][0] != e {
		t.Errorf("Expected to find edge in graph")
	}
}

func TestGraphAddSubgraph(t *testing.T) {
	g := NewGraph("TestGraph")
	sg := NewSubgraph("TestSubgraph")
	g.AddSubgraph(sg)
	if len(g.subgraphs) != 1 {
		t.Errorf("Expected graph to have 1 subgraph, got %d", len(g.subgraphs))
	}
	if g.subgraphs["TestSubgraph"][0] != sg {
		t.Errorf("Expected to find subgraph 'TestSubgraph' in graph")
	}
}
