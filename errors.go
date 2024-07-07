package dot

import "errors"

var (
	ErrNilNode               = errors.New("cannot add nil node")
	ErrEmptyNodeName         = errors.New("node name cannot be empty")
	ErrDuplicateNode         = errors.New("node with this name already exists")
	ErrNilEdge               = errors.New("cannot add nil edge")
	ErrInvalidEdge           = errors.New("edge must have both source and destination nodes")
	ErrNodeNotFound          = errors.New("node not found in the graph")
	ErrNilSubgraph           = errors.New("cannot add nil subgraph")
	ErrEmptySubgraphName     = errors.New("subgraph name cannot be empty")
	ErrDuplicateSubgraph     = errors.New("subgraph with this name already exists")
	ErrInvalidGraphType      = errors.New("invalid graph type")
	ErrUnsupportedOperation  = errors.New("operation not supported for this graph type")
	ErrCycleDetected         = errors.New("graph contains a cycle")
	ErrNoPath                = errors.New("no path exists between the given nodes")
	ErrDOTParsingFailed      = errors.New("failed to parse DOT input")
	ErrGraphvizNotFound      = errors.New("Graphviz tools not found in system PATH")
	ErrInvalidNodeAttribute  = errors.New("invalid node attribute")
	ErrInvalidEdgeAttribute  = errors.New("invalid edge attribute")
	ErrInvalidGraphAttribute = errors.New("invalid graph attribute")
)
