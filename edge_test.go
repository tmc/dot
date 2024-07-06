package dot

import (
	"testing"
)

func TestNewEdge(t *testing.T) {
	n1 := NewNode("Node1")
	n2 := NewNode("Node2")
	e := NewEdge(n1, n2)
	if e.Source() != n1 {
		t.Errorf("Expected edge source to be Node1")
	}
	if e.Destination() != n2 {
		t.Errorf("Expected edge destination to be Node2")
	}
	if len(e.attributes) != 0 {
		t.Errorf("Expected new edge to have 0 attributes, got %d", len(e.attributes))
	}
}

func TestEdgeSet(t *testing.T) {
	n1 := NewNode("Node1")
	n2 := NewNode("Node2")
	e := NewEdge(n1, n2)
	err := e.Set("color", "red")
	if err != nil {
		t.Errorf("Unexpected error setting valid attribute: %v", err)
	}
	if e.attributes["color"] != "red" {
		t.Errorf("Expected edge color to be 'red', got '%s'", e.attributes["color"])
	}

	err = e.Set("invalid_attr", "value")
	if err == nil {
		t.Error("Expected error for invalid attribute, got nil")
	} else if err.Error() != "invalid edge attribute: invalid_attr" {
		t.Errorf("Unexpected error message: %v", err)
	}
}

func TestEdgeString(t *testing.T) {
	n1 := NewNode("Node1")
	n2 := NewNode("Node2")
	e := NewEdge(n1, n2)
	e.Set("style", "dashed")
	expected := "Node1 -> Node2 [ style=dashed ]"
	if e.String() != expected {
		t.Errorf("Expected edge string to be '%s', got '%s'", expected, e.String())
	}
}
