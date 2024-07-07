package dot

import (
	"fmt"
	"reflect"
	"strings"
)

type Edge struct {
	src, dst   *Node
	attributes map[string]string
	sequence   int
}

func NewEdge(src, dst *Node) *Edge {
	return &Edge{
		src:        src,
		dst:        dst,
		attributes: make(map[string]string),
	}
}

func (e *Edge) Source() *Node {
	return e.src
}

func (e *Edge) Destination() *Node {
	return e.dst
}

func (e *Edge) Type() string {
	return "edge"
}

func (e *Edge) Name() string {
	return fmt.Sprintf("%s->%s", e.src.Name(), e.dst.Name())
}

func (e *Edge) Get(key string) string {
	return e.attributes[key]
}

func (e *Edge) Set(key, value string) error {
	if !validEdgeAttribute(key) {
		return fmt.Errorf("%w: %s", ErrInvalidEdgeAttribute, key)
	}
	e.attributes[key] = value
	return nil
}

func (e *Edge) Sequence() int {
	return e.sequence
}

func (e *Edge) SetSequence(seq int) {
	e.sequence = seq
}

func (e *Edge) String() string {
	src, dst := QuoteIfNecessary(e.src.Name()), QuoteIfNecessary(e.dst.Name())
	attrs := make([]string, 0, len(e.attributes))
	for _, key := range sortedKeys(e.attributes) {
		attrs = append(attrs, fmt.Sprintf("%s=%s", key, QuoteIfNecessary(e.attributes[key])))
	}
	if len(attrs) > 0 {
		return fmt.Sprintf("%s -> %s [ %s ]", src, dst, strings.Join(attrs, ", "))
	}
	return fmt.Sprintf("%s -> %s", src, dst)
}

func (e *Edge) Equals(other *Edge) bool {
	return e.src.Equals(other.src) && e.dst.Equals(other.dst) && reflect.DeepEqual(e.attributes, other.attributes)
}

func (e *Edge) Clone() *Edge {
	clone := NewEdge(e.src.Clone(), e.dst.Clone())
	for k, v := range e.attributes {
		clone.attributes[k] = v
	}
	return clone
}
