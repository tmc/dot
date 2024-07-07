package dot

type SubGraph struct {
	Graph
	sequence int
}

func NewSubgraph(name string) *SubGraph {
	sg := &SubGraph{
		Graph: *NewGraph(name),
	}
	sg.graphType = SUBGRAPH
	return sg
}

func (sg *SubGraph) Sequence() int {
	return sg.sequence
}

func (sg *SubGraph) SetSequence(seq int) {
	sg.sequence = seq
}

// SubGraph comparison
func (sg *SubGraph) Equals(other *SubGraph) bool {
	return sg.Graph.Equals(&other.Graph)
}
