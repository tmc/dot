package dot

import (
	"encoding/json"
	"fmt"
	"os"
	"reflect"
	"strings"
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

func TestGraphShortestPath(t *testing.T) {
	g := NewGraph("G")
	a := NewNode("A")
	b := NewNode("B")
	c := NewNode("C")
	g.AddNode(a)
	g.AddNode(b)
	g.AddNode(c)
	g.AddEdge(NewEdge(a, b))
	g.AddEdge(NewEdge(b, c))

	t.Logf("Graph structure: %s", g)
	t.Logf("Nodes: %+v", g.nodes)
	t.Logf("Edges: %+v", g.edges)

	path, err := g.ShortestPath(a, c)
	if err != nil {
		t.Errorf("Unexpected error: %v", err)
	}

	if path == nil {
		t.Fatalf("Path is nil")
	}

	if len(path) != 3 || path[0] != a || path[1] != b || path[2] != c {
		t.Errorf("Incorrect shortest path: %v", path)
	}
}

func TestGraphDiff(t *testing.T) {
	g1 := NewGraph("G1")
	a1 := NewNode("A")
	b1 := NewNode("B")
	c1 := NewNode("C")
	g1.AddNode(a1)
	g1.AddNode(b1)
	g1.AddNode(c1)
	g1.AddEdge(NewEdge(a1, b1))
	g1.AddEdge(NewEdge(b1, c1))

	g2 := NewGraph("G2")
	a2 := NewNode("A")
	b2 := NewNode("B")
	d2 := NewNode("D")
	g2.AddNode(a2)
	g2.AddNode(b2)
	g2.AddNode(d2)
	g2.AddEdge(NewEdge(a2, b2))
	g2.AddEdge(NewEdge(b2, d2))

	diff, err := g1.Diff(g2)
	if err != nil {
		t.Fatalf("Unexpected error in Diff: %v", err)
	}

	t.Logf("Diff result: %s", diff)

	// Check nodes in diff
	if len(diff.nodes) != 2 || diff.nodes["C"] == nil || diff.nodes["D"] == nil {
		t.Errorf("Incorrect nodes in diff. Expected C and D, got: %v", diff.nodes)
	}

	// Check edges in diff
	if len(diff.edges) != 2 {
		t.Errorf("Incorrect number of edges in diff. Expected 2, got: %d", len(diff.edges))
	}

	// Check specific edges
	edgeBC := fmt.Sprintf("%s->%s", b1.Name(), c1.Name())
	edgeBD := fmt.Sprintf("%s->%s", b2.Name(), d2.Name())
	if diff.edges[edgeBC] == nil || diff.edges[edgeBD] == nil {
		t.Errorf("Expected edges B->C and B->D in diff, got: %v", diff.edges)
	}
}

func TestGraphClone(t *testing.T) {
	original := NewGraph("Original")
	a := NewNode("A")
	b := NewNode("B")
	c := NewNode("C")
	original.AddNode(a)
	original.AddNode(b)
	original.AddNode(c)
	original.AddEdge(NewEdge(a, b))
	original.AddEdge(NewEdge(b, c))
	original.Set("smoothing", "true")

	clone := original.Clone()

	t.Logf("Original: %s", original)
	t.Logf("Clone: %s", clone)

	// Check if the clone has the same name and type
	if clone.Name != original.Name || clone.graphType != original.graphType {
		t.Errorf("Clone has different name or type. Original: %s, %v. Clone: %s, %v",
			original.Name, original.graphType, clone.Name, clone.graphType)
	}

	// Check if the clone has the same number of nodes and edges
	if len(clone.nodes) != len(original.nodes) || len(clone.edges) != len(original.edges) {
		t.Errorf("Clone has different number of nodes or edges. Original: %d nodes, %d edges. Clone: %d nodes, %d edges",
			len(original.nodes), len(original.edges), len(clone.nodes), len(clone.edges))
	}

	// Check if the clone has the same attributes
	if clone.Get("graphAttr") != original.Get("graphAttr") {
		t.Errorf("Clone has different attribute value. Original: %s, Clone: %s",
			original.Get("graphAttr"), clone.Get("graphAttr"))
	}

	// Modify the clone and check if the original is unchanged
	d := NewNode("D")
	clone.AddNode(d)
	clone.AddEdge(NewEdge(c, d))

	if len(original.nodes) == len(clone.nodes) || len(original.edges) == len(clone.edges) {
		t.Errorf("Modifying clone affected original. Original: %d nodes, %d edges. Clone: %d nodes, %d edges",
			len(original.nodes), len(original.edges), len(clone.nodes), len(clone.edges))
	}
}

func TestGraphTopologicalSort(t *testing.T) {
	g := NewGraph("G")
	a := NewNode("A")
	b := NewNode("B")
	c := NewNode("C")
	d := NewNode("D")
	g.AddNode(a)
	g.AddNode(b)
	g.AddNode(c)
	g.AddNode(d)
	g.AddEdge(NewEdge(a, b))
	g.AddEdge(NewEdge(b, c))
	g.AddEdge(NewEdge(a, c))
	g.AddEdge(NewEdge(c, d))

	sorted, err := g.TopologicalSort()
	if err != nil {
		t.Errorf("Unexpected error: %v", err)
	}

	expectedOrder := []*Node{a, b, c, d}
	if !reflect.DeepEqual(sorted, expectedOrder) {
		t.Errorf("Expected order %v, got %v", expectedOrder, sorted)
	}

	// Test with cyclic graph
	g.AddEdge(NewEdge(d, a))
	_, err = g.TopologicalSort()
	if err == nil {
		t.Errorf("Expected error for cyclic graph, got nil")
	}
}

func TestGraphMerge(t *testing.T) {
	g1 := NewGraph("G1")
	g1.AddNode(NewNode("A"))
	g1.AddNode(NewNode("B"))
	g1.AddEdge(NewEdge(g1.nodes["A"][0], g1.nodes["B"][0]))
	// set a legal attribute:
	g1.Set("smoothing", "true")

	g2 := NewGraph("G2")
	g2.AddNode(NewNode("C"))
	g2.AddNode(NewNode("D"))
	g2.AddEdge(NewEdge(g2.nodes["C"][0], g2.nodes["D"][0]))
	g2.Set("rank", "same")

	err := g1.Merge(g2)
	if err != nil {
		t.Errorf("Unexpected error: %v", err)
	}

	expectedNodeCount := 4
	if len(g1.nodes) != expectedNodeCount {
		t.Errorf("Expected %d nodes after merge, got %d", expectedNodeCount, len(g1.nodes))
	}

	expectedEdgeCount := 2
	if len(g1.edges) != expectedEdgeCount {
		t.Errorf("Expected %d edges after merge, got %d", expectedEdgeCount, len(g1.edges))
	}

	if g1.Get("smoothing") != "true" || g1.Get("rank") != "same" {
		t.Errorf("Merged graph is missing attributes (expected: smoothing=true, rank=same)")
	}
}

func TestGraphValidate(t *testing.T) {
	t.Run("Valid graph", func(t *testing.T) {
		g := NewGraph("ValidGraph")
		a := NewNode("A")
		b := NewNode("B")
		g.AddNode(a)
		g.AddNode(b)
		g.AddEdge(NewEdge(a, b))
		g.Set("rankdir", "LR")

		err := g.Validate()
		if err != nil {
			t.Errorf("Expected no error for valid graph, got: %v", err)
		}
	})

	t.Run("Duplicate node names", func(t *testing.T) {
		g := NewGraph("DuplicateNodes")
		g.AddNode(NewNode("A"))
		_, err := g.AddNode(NewNode("A"))
		if err == nil {
			t.Error("Expected error for duplicate node names, got nil")
		}

	})

	t.Run("Edge with non-existent node", func(t *testing.T) {
		g := NewGraph("NonExistentNode")
		a := NewNode("A")
		b := NewNode("B")
		g.AddNode(a)
		g.AddEdge(NewEdge(a, b))

		err := g.Validate()
		if err == nil {
			t.Error("Expected error for edge with non-existent node, got nil")
		}
	})

	t.Run("Subgraph cycle", func(t *testing.T) {
		g := NewGraph("SubgraphCycle")
		sg1 := NewSubgraph("SG1")
		sg2 := NewSubgraph("SG2")
		g.AddSubgraph(sg1)
		g.AddSubgraph(sg2)
		sg1.AddSubgraph(sg2)
		sg2.AddSubgraph(sg1)

		err := g.Validate()
		if err == nil {
			t.Error("Expected error for subgraph cycle, got nil")
		}
	})
	t.Run("Cyclic subgraph structure", func(t *testing.T) {
		g := NewGraph("CyclicSubgraphs")
		sg1 := NewSubgraph("SG1")
		sg2 := NewSubgraph("SG2")
		g.AddSubgraph(sg1)
		sg1.AddSubgraph(sg2)
		sg2.AddSubgraph(sg1)

		err := g.Validate()
		if err == nil {
			t.Error("Expected error for cyclic subgraph structure, got nil")
		} else if !strings.Contains(err.Error(), "cyclic subgraph structure detected") {
			t.Errorf("Expected error message to contain 'cyclic subgraph structure detected', got: %v", err)
		}
	})
}
func TestGraphEquals(t *testing.T) {
	g1 := NewGraph("G")
	g1.AddNode(NewNode("A"))
	g1.AddNode(NewNode("B"))
	g1.AddEdge(NewEdge(g1.nodes["A"][0], g1.nodes["B"][0]))
	g1.Set("smoothing", "true")

	g2 := NewGraph("G")
	g2.AddNode(NewNode("A"))
	g2.AddNode(NewNode("B"))
	g2.AddEdge(NewEdge(g2.nodes["A"][0], g2.nodes["B"][0]))
	g2.Set("smoothing", "true")

	if !g1.Equals(g2) {
		t.Errorf("Graphs should be equal")
	}

	g2.Set("rankdir", "TB")
	if g1.Equals(g2) {
		t.Errorf("Graphs should not be equal after attribute change")
	}

	g2 = g1.Clone()
	g2.AddNode(NewNode("C"))
	if g1.Equals(g2) {
		t.Errorf("Graphs should not be equal after adding a node")
	}

	g2 = g1.Clone()
	g2.AddEdge(NewEdge(g2.nodes["A"][0], g2.nodes["A"][0]))
	if g1.Equals(g2) {
		t.Errorf("Graphs should not be equal after adding an edge")
	}

	g2 = g1.Clone()
	g2.AddSubgraph(NewSubgraph("SG"))
	if g1.Equals(g2) {
		t.Errorf("Graphs should not be equal after adding a subgraph")
	}
}

func TestGraphUnmarshalJSON(t *testing.T) {
	jsonData := []byte(`{
        "name": "TestGraph",
        "type": "digraph",
        "attributes": {"rankdir": "LR"},
        "nodes": {"A": [{}], "B": [{}]},
        "edges": {"A->B": [{}]},
        "subgraphs": {"SG": [{"name": "SubGraph"}]}
    }`)

	g := NewGraph("")
	err := g.UnmarshalJSON(jsonData)
	if err != nil {
		t.Errorf("Unexpected error: %v", err)
	}

	if g.Name != "TestGraph" || g.graphType != DIGRAPH {
		t.Errorf("Graph properties not correctly unmarshaled")
	}

	if len(g.nodes) != 2 || len(g.edges) != 1 || len(g.subgraphs) != 1 {
		t.Errorf("Graph structure not correctly unmarshaled")
	}

	if g.Get("rankdir") != "LR" {
		t.Errorf("Graph attributes not correctly unmarshaled")
	}
}

func TestGraphToPNG(t *testing.T) {
	g := NewGraph("TestPNG")
	g.AddNode(NewNode("A"))
	g.AddNode(NewNode("B"))
	g.AddEdge(NewEdge(g.nodes["A"][0], g.nodes["B"][0]))

	tempFile := "test_graph.png"
	err := g.ToPNG(tempFile)
	if err != nil {
		t.Errorf("Unexpected error: %v", err)
	}

	// Check if file exists
	if _, err := os.Stat(tempFile); os.IsNotExist(err) {
		t.Errorf("PNG file was not created")
	}

	// Clean up
	os.Remove(tempFile)
}

func TestGraphToSVG(t *testing.T) {
	g := NewGraph("TestSVG")
	g.AddNode(NewNode("A"))
	g.AddNode(NewNode("B"))
	g.AddEdge(NewEdge(g.nodes["A"][0], g.nodes["B"][0]))

	tempFile := "test_graph.svg"
	err := g.ToSVG(tempFile)
	if err != nil {
		t.Errorf("Unexpected error: %v", err)
	}

	// Check if file exists
	if _, err := os.Stat(tempFile); os.IsNotExist(err) {
		t.Errorf("SVG file was not created")
	}

	// Clean up
	os.Remove(tempFile)
}

func TestGraphBFS(t *testing.T) {
	g := NewGraph("BFS")
	g.AddNode(NewNode("A"))
	g.AddNode(NewNode("B"))
	g.AddNode(NewNode("C"))
	g.AddEdge(NewEdge(g.nodes["A"][0], g.nodes["B"][0]))
	g.AddEdge(NewEdge(g.nodes["B"][0], g.nodes["C"][0]))

	visited := make([]string, 0)
	g.BFS("A", func(n *Node) {
		visited = append(visited, n.Name())
	})

	expected := []string{"A", "B", "C"}
	if !reflect.DeepEqual(visited, expected) {
		t.Errorf("BFS traversal incorrect. Expected %v, got %v", expected, visited)
	}
}

func TestGraphMarshalJSON(t *testing.T) {
	g := NewGraph("TestGraph")
	g.AddNode(NewNode("A"))
	g.AddNode(NewNode("B"))
	g.AddEdge(NewEdge(g.nodes["A"][0], g.nodes["B"][0]))
	g.Set("rankdir", "LR")

	jsonData, err := g.MarshalJSON()
	if err != nil {
		t.Errorf("Unexpected error: %v", err)
	}

	// Unmarshal the JSON data into a map for easier checking
	var result map[string]interface{}
	err = json.Unmarshal(jsonData, &result)
	if err != nil {
		t.Errorf("Error unmarshaling JSON: %v", err)
	}

	if result["name"] != "TestGraph" {
		t.Errorf("Incorrect graph name in JSON")
	}

	if result["type"] != "digraph" {
		t.Errorf("Incorrect graph type in JSON")
	}

	attributes, ok := result["attributes"].(map[string]interface{})
	if !ok || attributes["rankdir"] != "LR" {
		t.Errorf("Incorrect attributes in JSON")
	}

	nodes, ok := result["nodes"].(map[string]interface{})
	if !ok || len(nodes) != 2 {
		t.Errorf("Incorrect nodes in JSON")
	}

	edges, ok := result["edges"].(map[string]interface{})
	if !ok || len(edges) != 1 {
		t.Errorf("Incorrect edges in JSON")
	}
}
