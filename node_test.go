package dot

import (
	"testing"
)

func TestNewNode(t *testing.T) {
	n := NewNode("TestNode")
	if n.name != "TestNode" {
		t.Errorf("Expected node name to be 'TestNode', got '%s'", n.name)
	}
	if len(n.attributes) != 0 {
		t.Errorf("Expected new node to have 0 attributes, got %d", len(n.attributes))
	}
}

func TestNodeSet(t *testing.T) {
	n := NewNode("TestNode")
	err := n.Set("color", "red")
	if err != nil {
		t.Errorf("Unexpected error setting valid attribute: %v", err)
	}
	if n.attributes["color"] != "red" {
		t.Errorf("Expected node color to be 'red', got '%s'", n.attributes["color"])
	}

	err = n.Set("invalid_attr", "value")
	if err == nil {
		t.Error("Expected error for invalid attribute, got nil")
	} else if err.Error() != "invalid node attribute: invalid_attr" {
		t.Errorf("Unexpected error message: %v", err)
	}
}

func TestNodeString(t *testing.T) {
	n := NewNode("TestNode")
	n.Set("color", "blue")
	n.Set("shape", "box")
	expected := "TestNode [color=blue, shape=box];"
	if n.String() != expected {
		t.Errorf("Expected node string to be '%s', got '%s'", expected, n.String())
	}
}
