package dot

import (
	"fmt"
	"reflect"
	"strings"
)

// Node implementation

func (n *Node) Type() string {
	return "node"
}

func (n *Node) Name() string {
	return n.name
}

func (n *Node) Get(key string) string {
	return n.attributes[key]
}

func (n *Node) Set(key, value string) error {
	if !validNodeAttribute(key) {
		return fmt.Errorf("%w: %s", ErrInvalidNodeAttribute, key)
	}
	n.attributes[key] = value
	return nil
}

func (n *Node) Sequence() int {
	return n.sequence
}

func (n *Node) SetSequence(seq int) {
	n.sequence = seq
}

func (n *Node) String() string {
	name := QuoteIfNecessary(n.name)
	attrs := make([]string, 0, len(n.attributes))
	for _, key := range sortedKeys(n.attributes) {
		value := n.attributes[key]
		if key == "label" && len(value) > 4 && value[0] == '<' && value[len(value)-1] == '>' {
			attrs = append(attrs, fmt.Sprintf("%s=%s", key, value))
		} else {
			attrs = append(attrs, fmt.Sprintf("%s=%s", key, QuoteIfNecessary(value)))
		}
	}
	if len(attrs) > 0 {
		return fmt.Sprintf("%s [%s];", name, strings.Join(attrs, ", "))
	}
	return name + ";"
}

// Constants and variables

// Node comparison
func (n *Node) Equals(other *Node) bool {
	return n.name == other.name && reflect.DeepEqual(n.attributes, other.attributes)
}

type Node struct {
	name       string
	attributes map[string]string
	sequence   int
}

func NewNode(name string) *Node {
	return &Node{
		name:       name,
		attributes: make(map[string]string),
	}
}

func (n *Node) Clone() *Node {
	clone := NewNode(n.name)
	for k, v := range n.attributes {
		clone.attributes[k] = v
	}
	return clone
}
