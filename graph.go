package dot

import (
	"container/heap"
	"encoding/json"
	"errors"
	"fmt"
	"io"
	"os/exec"
	"reflect"
	"regexp"
	"sort"
	"strings"
	"sync"
)

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

// GraphType represents the type of a graph.
type GraphType int

const (
	DIGRAPH GraphType = iota
	GRAPH
	SUBGRAPH
)

func (gt GraphType) String() string {
	switch gt {
	case DIGRAPH:
		return "digraph"
	case GRAPH:
		return "graph"
	case SUBGRAPH:
		return "subgraph"
	default:
		return "unknown"
	}
}

// Graph represents a graph in the DOT language.
type Graph struct {
	sync.RWMutex
	Name                 string
	graphType            GraphType
	attributes           map[string]string
	nodeAttributes       map[string]string
	edgeAttributes       map[string]string
	nodes                map[string][]*Node
	edges                map[string][]*Edge
	subgraphs            map[string][]*SubGraph
	sameRank             [][]string
	strict               bool
	supressDisconnected  bool
	simplify             bool
	currentChildSequence int
}

// NewGraph creates a new graph with the given name.
func NewGraph(name string) *Graph {
	return &Graph{
		Name:           name,
		graphType:      DIGRAPH,
		attributes:     make(map[string]string),
		nodeAttributes: make(map[string]string),
		edgeAttributes: make(map[string]string),
		nodes:          make(map[string][]*Node),
		edges:          make(map[string][]*Edge),
		subgraphs:      make(map[string][]*SubGraph),
		sameRank:       make([][]string, 0),
	}
}

// SetType sets the type of the graph.
func (g *Graph) SetType(t GraphType) error {
	g.Lock()
	defer g.Unlock()
	switch t {
	case DIGRAPH, GRAPH, SUBGRAPH:
		g.graphType = t
		return nil
	default:
		return ErrInvalidGraphType
	}
}

func (g *Graph) SetStrict(strict bool) *Graph {
	g.Lock()
	defer g.Unlock()
	g.strict = strict
	return g
}

func (g *Graph) Set(key, value string) error {
	g.Lock()
	defer g.Unlock()
	if !validGraphAttribute(key) {
		return ErrInvalidGraphAttribute
	}
	g.attributes[key] = value
	return nil
}

func (g *Graph) SetGlobalNodeAttr(key, value string) error {
	g.Lock()
	defer g.Unlock()
	if !validNodeAttribute(key) {
		return ErrInvalidNodeAttribute
	}
	g.nodeAttributes[key] = value
	return nil
}

func (g *Graph) SetGlobalEdgeAttr(key, value string) error {
	g.Lock()
	defer g.Unlock()
	if !validEdgeAttribute(key) {
		return ErrInvalidEdgeAttribute
	}
	g.edgeAttributes[key] = value
	return nil
}

func (g *Graph) AddNode(n *Node) (*Node, error) {
	g.Lock()
	defer g.Unlock()
	if n == nil {
		return nil, ErrNilNode
	}
	if n.Name() == "" {
		return nil, ErrEmptyNodeName
	}
	name := n.Name()
	if _, exists := g.nodes[name]; exists {
		return nil, fmt.Errorf("%w: %s", ErrDuplicateNode, name)
	}
	if g.nodes[name] == nil {
		g.nodes[name] = make([]*Node, 0)
	}
	n.SetSequence(g.getNextSequenceNumber())
	g.nodes[name] = append(g.nodes[name], n)
	return n, nil
}

func (g *Graph) AddEdge(e *Edge) (*Edge, error) {
	g.Lock()
	defer g.Unlock()
	if e == nil {
		return nil, ErrNilEdge
	}
	if e.Source() == nil || e.Destination() == nil {
		return nil, ErrInvalidEdge
	}
	name := e.Name()
	if g.edges[name] == nil {
		g.edges[name] = make([]*Edge, 0)
	}
	e.SetSequence(g.getNextSequenceNumber())
	g.edges[name] = append(g.edges[name], e)
	return e, nil
}

func (g *Graph) AddSubgraph(sg *SubGraph) (*SubGraph, error) {
	g.Lock()
	defer g.Unlock()
	if sg == nil {
		return nil, ErrNilSubgraph
	}
	if sg.Name == "" {
		return nil, ErrEmptySubgraphName
	}
	name := sg.Name
	if _, exists := g.subgraphs[name]; exists {
		return nil, fmt.Errorf("%w: %s", ErrDuplicateSubgraph, name)
	}
	if g.subgraphs[name] == nil {
		g.subgraphs[name] = make([]*SubGraph, 0)
	}
	sg.SetSequence(g.getNextSequenceNumber())
	g.subgraphs[name] = append(g.subgraphs[name], sg)
	return sg, nil
}

func (g *Graph) GetSubgraphs() []*SubGraph {
	g.RLock()
	defer g.RUnlock()
	result := make([]*SubGraph, 0)
	for _, sgs := range g.subgraphs {
		result = append(result, sgs...)
	}
	return result
}

func (g *Graph) SameRank(nodes []string) {
	g.Lock()
	defer g.Unlock()
	g.sameRank = append(g.sameRank, nodes)
}

func (g *Graph) getNextSequenceNumber() int {
	next := g.currentChildSequence
	g.currentChildSequence++
	return next
}

func (g *Graph) String() string {
	g.RLock()
	defer g.RUnlock()

	var parts []string
	if g.strict {
		parts = append(parts, "strict ")
	}
	if g.Name == "" {
		parts = append(parts, "{\n")
	} else {
		parts = append(parts, fmt.Sprintf("%s %s {\n", g.graphType, QuoteIfNecessary(g.Name)))
	}

	parts = append(parts, g.attributesToString("graph", g.attributes)...)
	parts = append(parts, g.attributesToString("node", g.nodeAttributes)...)
	parts = append(parts, g.attributesToString("edge", g.edgeAttributes)...)

	objectList := g.getSortedGraphObjects()

	for _, obj := range objectList {
		parts = append(parts, fmt.Sprintf("%s\n", obj))
	}

	for _, nodes := range g.sameRank {
		parts = append(parts, fmt.Sprintf("{ rank=same %s }", strings.Join(nodes, " ")))
	}

	parts = append(parts, "}\n")
	return strings.Join(parts, "")
}

func (g *Graph) attributesToString(prefix string, attrs map[string]string) []string {
	if len(attrs) == 0 {
		return nil
	}
	var parts []string
	parts = append(parts, prefix+" [\n")
	for _, key := range sortedKeys(attrs) {
		parts = append(parts, fmt.Sprintf("  %s=%s;\n", key, QuoteIfNecessary(attrs[key])))
	}
	parts = append(parts, "];\n")
	return parts
}

func (g *Graph) getSortedGraphObjects() []fmt.Stringer {
	objectList := make([]fmt.Stringer, 0)

	for _, nodes := range g.nodes {
		for _, node := range nodes {
			objectList = append(objectList, node)
		}
	}
	for _, edges := range g.edges {
		for _, edge := range edges {
			objectList = append(objectList, edge)
		}
	}
	for _, subgraphs := range g.subgraphs {
		for _, subgraph := range subgraphs {
			objectList = append(objectList, subgraph)
		}
	}
	sort.Slice(objectList, func(i, j int) bool {
		s1, ok1 := objectList[i].(Sequenceable)
		s2, ok2 := objectList[j].(Sequenceable)
		if ok1 && ok2 {
			return s1.Sequence() < s2.Sequence()
		}
		return reflect.TypeOf(objectList[i]).String() < reflect.TypeOf(objectList[j]).String()
	})

	return objectList
}

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

// Helper functions

func sortedKeys(m map[string]string) []string {
	keys := make([]string, 0, len(m))
	for k := range m {
		keys = append(keys, k)
	}
	sort.Strings(keys)
	return keys
}

func QuoteIfNecessary(s string) string {
	if needsQuotes(s) {
		s = strings.Replace(s, "\"", "\\\"", -1)
		s = strings.Replace(s, "\n", "\\n", -1)
		s = strings.Replace(s, "\r", "\\r", -1)
		return "\"" + s + "\""
	}
	return s
}

func needsQuotes(s string) bool {
	if indexInSlice(dotKeywords, s) != -1 {
		return false
	}
	if alreadyQuotedRegex.MatchString(s) {
		return false
	}
	if validIdentifierRegexWithPort.MatchString(s) || validIdentifierRegex.MatchString(s) {
		return false
	}
	return true
}

func indexInSlice(slice []string, toFind string) int {
	for i, v := range slice {
		if v == toFind {
			return i
		}
	}
	return -1
}

// Attribute validation

func validGraphAttribute(attributeName string) bool {
	return validAttribute(graphAttributes, attributeName)
}

func validNodeAttribute(attributeName string) bool {
	return validAttribute(nodeAttributes, attributeName)
}

func validEdgeAttribute(attributeName string) bool {
	return validAttribute(edgeAttributes, attributeName)
}

func validAttribute(validAttributes []string, attributeName string) bool {
	return indexInSlice(validAttributes, attributeName) != -1
}

// GraphObject interface

type GraphObject interface {
	fmt.Stringer
	Type() string
	Name() string
	Get(string) string
	Set(string, string) error
}

type Sequenceable interface {
	Sequence() int
	SetSequence(int)
}

// Node implementation

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

// Edge implementation

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

// Constants and variables

var (
	alreadyQuotedRegex           = regexp.MustCompile(`^".+"$`)
	validIdentifierRegexWithPort = regexp.MustCompile(`^[_a-zA-Z][a-zA-Z0-9_,:\"]*[a-zA-Z0-9_,\"]+$`)
	validIdentifierRegex         = regexp.MustCompile(`^[_a-zA-Z][a-zA-Z0-9_,]*$`)
)

var dotKeywords = []string{"graph", "digraph", "subgraph", "node", "edge", "strict"}

var graphAttributes = []string{
	"Damping", "K", "URL", "aspect", "bb", "bgcolor", "center", "charset",
	"clusterrank", "colorscheme", "comment", "compound", "concentrate",
	"defaultdist", "dim", "dimen", "diredgeconstraints", "dpi", "epsilon",
	"esep", "fontcolor", "fontname", "fontnames", "fontpath", "fontsize",
	"id", "label", "labeljust", "labelloc", "landscape", "layers", "layersep",
	"layout", "levels", "levelsgap", "lheight", "lp", "lwidth", "margin",
	"maxiter", "mclimit", "mindist", "mode", "model", "mosek", "nodesep",
	"nojustify", "normalize", "nslimit", "nslimit1", "ordering", "orientation",
	"outputorder", "overlap", "overlap_scaling", "pack", "packmode", "pad",
	"page", "pagedir", "quadtree", "quantum", "rankdir", "ranksep", "ratio",
	"remincross", "repulsiveforce", "resolution", "root", "rotate", "searchsize",
	"sep", "showboxes", "size", "smoothing", "sortv", "splines", "start",
	"stylesheet", "target", "truecolor", "viewport", "voro_margin", "rank",
}

var nodeAttributes = []string{
	"URL", "color", "colorscheme", "comment", "distortion", "fillcolor",
	"fixedsize", "fontcolor", "fontname", "fontsize", "group", "height",
	"id", "image", "imagescale", "label", "labelloc", "layer", "margin",
	"nojustify", "orientation", "penwidth", "peripheries", "pin", "pos",
	"rects", "regular", "root", "samplepoints", "shape", "shapefile",
	"showboxes", "sides", "skew", "sortv", "style", "target", "tooltip",
	"vertices", "width", "z",
	// The following are attributes for dot2tex
	"texlbl", "texmode",
}

var edgeAttributes = []string{
	"URL", "arrowhead", "arrowsize", "arrowtail", "color", "colorscheme",
	"comment", "constraint", "decorate", "dir", "edgeURL", "edgehref",
	"edgetarget", "edgetooltip", "fontcolor", "fontname", "fontsize",
	"headURL", "headclip", "headhref", "headlabel", "headport", "headtarget",
	"headtooltip", "href", "id", "label", "labelURL", "labelangle",
	"labeldistance", "labelfloat", "labelfontcolor", "labelfontname",
	"labelfontsize", "labelhref", "labeltarget", "labeltooltip", "layer",
	"len", "lhead", "lp", "ltail", "minlen", "nojustify", "penwidth",
	"pos", "samehead", "sametail", "showboxes", "style", "tailURL",
	"tailclip", "tailhref", "taillabel", "tailport", "tailtarget",
	"tailtooltip", "target", "tooltip", "weight",
	// for subgraphs
	"rank",
}

// Init function to sort attribute lists
func init() {
	sort.Strings(graphAttributes)
	sort.Strings(nodeAttributes)
	sort.Strings(edgeAttributes)
}

// Error type for invalid attributes
type AttributeError struct {
	AttributeName string
	ObjectType    string
}

func (e AttributeError) Error() string {
	return fmt.Sprintf("invalid %s attribute: %s", e.ObjectType, e.AttributeName)
}

// Helper function to create a new AttributeError
func newAttributeError(attributeName, objectType string) AttributeError {
	return AttributeError{
		AttributeName: attributeName,
		ObjectType:    objectType,
	}
}

// Implement method chaining for Graph

func (g *Graph) SetAttribute(key, value string) *Graph {
	g.Set(key, value)
	return g
}

func (g *Graph) SetGlobalNodeAttribute(key, value string) *Graph {
	g.SetGlobalNodeAttr(key, value)
	return g
}

func (g *Graph) SetGlobalEdgeAttribute(key, value string) *Graph {
	g.SetGlobalEdgeAttr(key, value)
	return g
}

// Implement method chaining for Node

func (n *Node) SetAttribute(key, value string) *Node {
	n.Set(key, value)
	return n
}

// Implement method chaining for Edge

func (e *Edge) SetAttribute(key, value string) *Edge {
	e.Set(key, value)
	return e
}

// Graph validation helpers

func (g *Graph) validateSubgraphCycles() error {
	visited := make(map[*SubGraph]bool)
	var dfs func(*SubGraph) error

	dfs = func(sg *SubGraph) error {
		if visited[sg] {
			return ErrCycleDetected
		}
		visited[sg] = true
		for _, child := range sg.GetSubgraphs() {
			if err := dfs(child); err != nil {
				return err
			}
		}
		visited[sg] = false
		return nil
	}

	for _, sg := range g.GetSubgraphs() {
		if err := dfs(sg); err != nil {
			return err
		}
	}
	return nil
}

func (g *Graph) validateUniqueNodeNames() error {
	nodeNames := make(map[string]bool)
	for name := range g.nodes {
		if nodeNames[name] {
			return fmt.Errorf("%w: %s", ErrDuplicateNode, name)
		}
		nodeNames[name] = true
	}
	return nil
}

// Serialization methods

func (g *Graph) MarshalJSON() ([]byte, error) {
	// Implement JSON marshaling
	// This is a basic implementation and might need to be expanded
	return json.Marshal(struct {
		Name       string                 `json:"name"`
		Type       string                 `json:"type"`
		Attributes map[string]string      `json:"attributes"`
		Nodes      map[string][]*Node     `json:"nodes"`
		Edges      map[string][]*Edge     `json:"edges"`
		Subgraphs  map[string][]*SubGraph `json:"subgraphs"`
	}{
		Name:       g.Name,
		Type:       g.graphType.String(),
		Attributes: g.attributes,
		Nodes:      g.nodes,
		Edges:      g.edges,
		Subgraphs:  g.subgraphs,
	})
}

func (g *Graph) UnmarshalJSON(data []byte) error {
	// Implement JSON unmarshaling
	// This is a basic implementation and might need to be expanded
	var temp struct {
		Name       string                 `json:"name"`
		Type       string                 `json:"type"`
		Attributes map[string]string      `json:"attributes"`
		Nodes      map[string][]*Node     `json:"nodes"`
		Edges      map[string][]*Edge     `json:"edges"`
		Subgraphs  map[string][]*SubGraph `json:"subgraphs"`
	}
	if err := json.Unmarshal(data, &temp); err != nil {
		return err
	}
	g.Name = temp.Name
	g.graphType = GraphTypeFromString(temp.Type)
	g.attributes = temp.Attributes
	g.nodes = temp.Nodes
	g.edges = temp.Edges
	g.subgraphs = temp.Subgraphs
	return nil
}

func GraphTypeFromString(s string) GraphType {
	switch s {
	case "digraph":
		return DIGRAPH
	case "graph":
		return GRAPH
	case "subgraph":
		return SUBGRAPH
	default:
		return DIGRAPH // Default to DIGRAPH
	}
}

// Graph traversal methods

func (g *Graph) DFS(startNode string, visitor func(*Node)) {
	visited := make(map[string]bool)
	var dfs func(string)
	dfs = func(nodeName string) {
		if visited[nodeName] {
			return
		}
		visited[nodeName] = true
		nodes := g.nodes[nodeName]
		for _, node := range nodes {
			visitor(node)
			for _, edge := range g.edges[nodeName] {
				dfs(edge.dst.Name())
			}
		}
	}
	dfs(startNode)
}

func (g *Graph) BFS(startNode string, visitor func(*Node)) {
	visited := make(map[string]bool)
	queue := []string{startNode}
	for len(queue) > 0 {
		nodeName := queue[0]
		queue = queue[1:]
		if visited[nodeName] {
			continue
		}
		visited[nodeName] = true
		nodes := g.nodes[nodeName]
		for _, node := range nodes {
			visitor(node)
			for _, edge := range g.edges[nodeName] {
				if !visited[edge.dst.Name()] {
					queue = append(queue, edge.dst.Name())
				}
			}
		}
	}
}

// Graph operations

func (g *Graph) Merge(other *Graph) error {
	g.Lock()
	defer g.Unlock()

	// Merge nodes
	for name, nodes := range other.nodes {
		if _, ok := g.nodes[name]; !ok {
			g.nodes[name] = make([]*Node, 0)
		}
		g.nodes[name] = append(g.nodes[name], nodes...)
	}

	// Merge edges
	for name, edges := range other.edges {
		if _, ok := g.edges[name]; !ok {
			g.edges[name] = make([]*Edge, 0)
		}
		g.edges[name] = append(g.edges[name], edges...)
	}

	// Merge subgraphs
	for name, subgraphs := range other.subgraphs {
		if _, ok := g.subgraphs[name]; !ok {
			g.subgraphs[name] = make([]*SubGraph, 0)
		}
		g.subgraphs[name] = append(g.subgraphs[name], subgraphs...)
	}

	// Merge attributes
	for k, v := range other.attributes {
		g.attributes[k] = v
	}

	return nil
}

func (g *Graph) Diff(other *Graph) (*Graph, error) {
	diff := NewGraph("Diff")
	diff.SetType(g.graphType)

	// Compare nodes
	for name, nodes := range g.nodes {
		if otherNodes, ok := other.nodes[name]; !ok {
			diff.nodes[name] = nodes
		} else {
			for _, node := range nodes {
				found := false
				for _, otherNode := range otherNodes {
					if node.Name() == otherNode.Name() {
						found = true
						break
					}
				}
				if !found {
					diff.AddNode(node)
				}
			}
		}
	}

	// Compare edges
	for name, edges := range g.edges {
		if otherEdges, ok := other.edges[name]; !ok {
			diff.edges[name] = edges
		} else {
			for _, edge := range edges {
				found := false
				for _, otherEdge := range otherEdges {
					if edge.Name() == otherEdge.Name() {
						found = true
						break
					}
				}
				if !found {
					diff.AddEdge(edge)
				}
			}
		}
	}

	// Compare subgraphs (recursive diff)
	for name, subgraphs := range g.subgraphs {
		if otherSubgraphs, ok := other.subgraphs[name]; !ok {
			diff.subgraphs[name] = subgraphs
		} else {
			for _, sg := range subgraphs {
				found := false
				for _, otherSg := range otherSubgraphs {
					if sg.Name == otherSg.Name {
						subDiff, err := sg.Diff(&otherSg.Graph)
						if err != nil {
							return nil, err
						}
						if len(subDiff.nodes) > 0 || len(subDiff.edges) > 0 || len(subDiff.subgraphs) > 0 {
							diff.AddSubgraph(NewSubgraph(sg.Name))
							diff.subgraphs[sg.Name][0].Merge(subDiff)
						}
						found = true
						break
					}
				}
				if !found {
					diff.AddSubgraph(sg)
				}
			}
		}
	}

	return diff, nil
}

// Graph optimization

func (g *Graph) Optimize() {
	g.Lock()
	defer g.Unlock()

	// Remove duplicate edges
	g.removeDuplicateEdges()

	// Merge nodes with identical attributes
	g.mergeIdenticalNodes()

	// Simplify subgraphs
	g.simplifySubgraphs()
}

func (g *Graph) removeDuplicateEdges() {
	for name, edges := range g.edges {
		uniqueEdges := make(map[string]*Edge)
		for _, edge := range edges {
			key := fmt.Sprintf("%s->%s", edge.src.Name(), edge.dst.Name())
			if existing, ok := uniqueEdges[key]; !ok || len(edge.attributes) > len(existing.attributes) {
				uniqueEdges[key] = edge
			}
		}
		g.edges[name] = make([]*Edge, 0, len(uniqueEdges))
		for _, edge := range uniqueEdges {
			g.edges[name] = append(g.edges[name], edge)
		}
	}
}

func (g *Graph) mergeIdenticalNodes() {
	nodeGroups := make(map[string][]*Node)
	for _, nodes := range g.nodes {
		for _, node := range nodes {
			key := node.attributesKey()
			nodeGroups[key] = append(nodeGroups[key], node)
		}
	}

	for _, group := range nodeGroups {
		if len(group) > 1 {
			primary := group[0]
			for i := 1; i < len(group); i++ {
				g.mergeNodes(primary, group[i])
			}
		}
	}
}

func (g *Graph) mergeNodes(primary, secondary *Node) {
	// Update all edges pointing to the secondary node to point to the primary node
	for _, edges := range g.edges {
		for _, edge := range edges {
			if edge.src == secondary {
				edge.src = primary
			}
			if edge.dst == secondary {
				edge.dst = primary
			}
		}
	}

	// Remove the secondary node
	delete(g.nodes, secondary.Name())
}

func (g *Graph) simplifySubgraphs() {
	for _, subgraphs := range g.subgraphs {
		for _, sg := range subgraphs {
			sg.Optimize()
			if len(sg.nodes) == 0 && len(sg.edges) == 0 && len(sg.subgraphs) == 0 {
				delete(g.subgraphs, sg.Name)
			}
		}
	}
}

// Helper method for node attributes comparison

func (n *Node) attributesKey() string {
	attrs := make([]string, 0, len(n.attributes))
	for k, v := range n.attributes {
		attrs = append(attrs, fmt.Sprintf("%s=%s", k, v))
	}
	sort.Strings(attrs)
	return strings.Join(attrs, ",")
}

// Graph export methods

func (g *Graph) ExportDOT(w io.Writer) error {
	_, err := w.Write([]byte(g.String()))
	return err
}

func (g *Graph) ExportJSON(w io.Writer) error {
	encoder := json.NewEncoder(w)
	encoder.SetIndent("", "  ")
	return encoder.Encode(g)
}

// Graph import methods

func ImportDOT(r io.Reader) (*Graph, error) {
	// TODO: Implement DOT parsing
	return nil, fmt.Errorf("DOT import not implemented")
}

func ImportJSON(r io.Reader) (*Graph, error) {
	var g Graph
	decoder := json.NewDecoder(r)
	err := decoder.Decode(&g)
	if err != nil {
		return nil, err
	}
	return &g, nil
}

// Graph analysis methods

func (g *Graph) GetNodeCount() int {
	count := 0
	for _, nodes := range g.nodes {
		count += len(nodes)
	}
	return count
}

func (g *Graph) GetEdgeCount() int {
	count := 0
	for _, edges := range g.edges {
		count += len(edges)
	}
	return count
}

func (g *Graph) GetSubgraphCount() int {
	count := 0
	for _, subgraphs := range g.subgraphs {
		count += len(subgraphs)
	}
	return count
}

func (g *Graph) GetDegree(nodeName string) int {
	inDegree := g.GetInDegree(nodeName)
	outDegree := g.GetOutDegree(nodeName)
	return inDegree + outDegree
}

func (g *Graph) GetInDegree(nodeName string) int {
	count := 0
	for _, edges := range g.edges {
		for _, edge := range edges {
			if edge.dst.Name() == nodeName {
				count++
			}
		}
	}
	return count
}

func (g *Graph) GetOutDegree(nodeName string) int {
	return len(g.edges[nodeName])
}

// Graph layout methods (placeholder for future implementation)

func (g *Graph) ApplyLayout(layout string) error {
	switch layout {
	case "dot":
		return g.applyDotLayout()
	case "neato":
		return g.applyNeatoLayout()
	case "fdp":
		return g.applyFDPLayout()
	case "sfdp":
		return g.applySFDPLayout()
	case "twopi":
		return g.applyTwopiLayout()
	case "circo":
		return g.applyCircoLayout()
	default:
		return fmt.Errorf("unsupported layout: %s", layout)
	}
}

func (g *Graph) applyDotLayout() error {
	// TODO: Implement dot layout algorithm
	return fmt.Errorf("dot layout not implemented")
}

func (g *Graph) applyNeatoLayout() error {
	// TODO: Implement neato layout algorithm
	return fmt.Errorf("neato layout not implemented")
}

func (g *Graph) applyFDPLayout() error {
	// TODO: Implement fdp layout algorithm
	return fmt.Errorf("fdp layout not implemented")
}

func (g *Graph) applySFDPLayout() error {
	// TODO: Implement sfdp layout algorithm
	return fmt.Errorf("sfdp layout not implemented")
}

func (g *Graph) applyTwopiLayout() error {
	// TODO: Implement twopi layout algorithm
	return fmt.Errorf("twopi layout not implemented")
}

func (g *Graph) applyCircoLayout() error {
	// TODO: Implement circo layout algorithm
	return fmt.Errorf("circo layout not implemented")
}

// Utility functions for graph manipulation

func (g *Graph) RemoveNode(nodeName string) {
	g.Lock()
	defer g.Unlock()

	delete(g.nodes, nodeName)

	// Remove all edges connected to this node
	for _, edges := range g.edges {
		for i := len(edges) - 1; i >= 0; i-- {
			if edges[i].src.Name() == nodeName || edges[i].dst.Name() == nodeName {
				edges = append(edges[:i], edges[i+1:]...)
			}
		}
	}
	delete(g.edges, nodeName)
}

func (g *Graph) RemoveEdge(src, dst string) {
	g.Lock()
	defer g.Unlock()

	if edges, ok := g.edges[src]; ok {
		for i, edge := range edges {
			if edge.dst.Name() == dst {
				g.edges[src] = append(edges[:i], edges[i+1:]...)
				break
			}
		}
	}
}

func (g *Graph) RemoveSubgraph(name string) {
	g.Lock()
	defer g.Unlock()

	delete(g.subgraphs, name)
}

// Graph cloning

func (g *Graph) Clone() *Graph {
	g.RLock()
	defer g.RUnlock()

	clone := NewGraph(g.Name)
	clone.graphType = g.graphType
	clone.strict = g.strict
	clone.supressDisconnected = g.supressDisconnected
	clone.simplify = g.simplify

	// Clone attributes
	for k, v := range g.attributes {
		clone.attributes[k] = v
	}

	// Clone nodes
	for name, nodes := range g.nodes {
		clone.nodes[name] = make([]*Node, len(nodes))
		for i, node := range nodes {
			cloneNode := NewNode(node.name)
			for k, v := range node.attributes {
				cloneNode.attributes[k] = v
			}
			clone.nodes[name][i] = cloneNode
		}
	}

	// Clone edges
	for name, edges := range g.edges {
		clone.edges[name] = make([]*Edge, len(edges))
		for i, edge := range edges {
			cloneEdge := NewEdge(
				clone.nodes[edge.src.Name()][0],
				clone.nodes[edge.dst.Name()][0],
			)
			for k, v := range edge.attributes {
				cloneEdge.attributes[k] = v
			}
			clone.edges[name][i] = cloneEdge
		}
	}

	// Clone subgraphs (recursive)
	for name, subgraphs := range g.subgraphs {
		clone.subgraphs[name] = make([]*SubGraph, len(subgraphs))
		for i, sg := range subgraphs {
			cloneSg := NewSubgraph(sg.Name)
			cloneSg.Graph = *sg.Clone()
			clone.subgraphs[name][i] = cloneSg
		}
	}

	// Clone same rank information
	clone.sameRank = make([][]string, len(g.sameRank))
	for i, rank := range g.sameRank {
		clone.sameRank[i] = make([]string, len(rank))
		copy(clone.sameRank[i], rank)
	}

	return clone
}

// Graph comparison

func (g *Graph) Equals(other *Graph) bool {
	if g.Name != other.Name || g.graphType != other.graphType || g.strict != other.strict {
		return false
	}

	if !reflect.DeepEqual(g.attributes, other.attributes) {
		return false
	}

	if len(g.nodes) != len(other.nodes) {
		return false
	}
	for name, nodes := range g.nodes {
		otherNodes, ok := other.nodes[name]
		if !ok || len(nodes) != len(otherNodes) {
			return false
		}
		for i, node := range nodes {
			if !node.Equals(otherNodes[i]) {
				return false
			}
		}
	}

	if len(g.edges) != len(other.edges) {
		return false
	}
	for name, edges := range g.edges {
		otherEdges, ok := other.edges[name]
		if !ok || len(edges) != len(otherEdges) {
			return false
		}
		for i, edge := range edges {
			if !edge.Equals(otherEdges[i]) {
				return false
			}
		}
	}

	if len(g.subgraphs) != len(other.subgraphs) {
		return false
	}
	for name, subgraphs := range g.subgraphs {
		otherSubgraphs, ok := other.subgraphs[name]
		if !ok || len(subgraphs) != len(otherSubgraphs) {
			return false
		}
		for i, sg := range subgraphs {
			if !sg.Equals(otherSubgraphs[i]) {
				return false
			}
		}
	}

	return reflect.DeepEqual(g.sameRank, other.sameRank)
}

// Node comparison
func (n *Node) Equals(other *Node) bool {
	return n.name == other.name && reflect.DeepEqual(n.attributes, other.attributes)
}

// Edge comparison
func (e *Edge) Equals(other *Edge) bool {
	return e.src.Equals(other.src) && e.dst.Equals(other.dst) && reflect.DeepEqual(e.attributes, other.attributes)
}

// SubGraph comparison
func (sg *SubGraph) Equals(other *SubGraph) bool {
	return sg.Graph.Equals(&other.Graph)
}

// Graph validation and error checking

func (g *Graph) Validate() error {
	if err := g.validateNodes(); err != nil {
		return err
	}
	if err := g.validateEdges(); err != nil {
		return err
	}
	if err := g.validateSubgraphs(); err != nil {
		return err
	}
	// Check for cycles in subgraphs
	if err := g.validateSubgraphCycles(); err != nil {
		return err
	}

	// Check for duplicate node names
	if err := g.validateUniqueNodeNames(); err != nil {
		return err
	}
	return g.validateAttributes()
}

func (g *Graph) validateNodes() error {
	for name, nodes := range g.nodes {
		if len(nodes) == 0 {
			return fmt.Errorf("empty node list for name: %s", name)
		}
		for _, node := range nodes {
			if node.name != name {
				return fmt.Errorf("node name mismatch: %s != %s", node.name, name)
			}
			if err := validateNodeAttributes(node.attributes); err != nil {
				return fmt.Errorf("invalid node attributes for %s: %v", name, err)
			}
		}
	}
	return nil
}

func (g *Graph) validateEdges() error {
	for _, edges := range g.edges {
		for _, edge := range edges {
			if _, ok := g.nodes[edge.src.Name()]; !ok {
				return fmt.Errorf("edge source node not found: %s", edge.src.Name())
			}
			if _, ok := g.nodes[edge.dst.Name()]; !ok {
				return fmt.Errorf("edge destination node not found: %s", edge.dst.Name())
			}
			if err := validateEdgeAttributes(edge.attributes); err != nil {
				return fmt.Errorf("invalid edge attributes for %s -> %s: %v", edge.src.Name(), edge.dst.Name(), err)
			}
		}
	}
	return nil
}

func (g *Graph) validateSubgraphs() error {
	for name, subgraphs := range g.subgraphs {
		for _, sg := range subgraphs {
			if sg.Name != name {
				return fmt.Errorf("subgraph name mismatch: %s != %s", sg.Name, name)
			}
			if err := sg.Validate(); err != nil {
				return fmt.Errorf("invalid subgraph %s: %v", name, err)
			}
		}
	}
	return nil
}

func (g *Graph) validateAttributes() error {
	return validateGraphAttributes(g.attributes)
}

func validateNodeAttributes(attrs map[string]string) error {
	for attr := range attrs {
		if !validNodeAttribute(attr) {
			return fmt.Errorf("invalid node attribute: %s", attr)
		}
	}
	return nil
}

func validateEdgeAttributes(attrs map[string]string) error {
	for attr := range attrs {
		if !validEdgeAttribute(attr) {
			return fmt.Errorf("invalid edge attribute: %s", attr)
		}
	}
	return nil
}

func validateGraphAttributes(attrs map[string]string) error {
	for attr := range attrs {
		if !validGraphAttribute(attr) {
			return fmt.Errorf("invalid graph attribute: %s", attr)
		}
	}
	return nil
}

// Graph statistics and metrics

func (g *Graph) GetDensity() float64 {
	nodeCount := g.GetNodeCount()
	edgeCount := g.GetEdgeCount()
	if nodeCount <= 1 {
		return 0
	}
	maxEdges := nodeCount * (nodeCount - 1)
	if g.graphType == GRAPH {
		maxEdges /= 2
	}
	return float64(edgeCount) / float64(maxEdges)
}

func (g *Graph) GetAverageDegree() float64 {
	nodeCount := g.GetNodeCount()
	if nodeCount == 0 {
		return 0
	}
	return float64(g.GetEdgeCount()*2) / float64(nodeCount)
}

func (g *Graph) GetDiameter() int {
	// Implement Floyd-Warshall algorithm to find the longest shortest path
	// This is a placeholder implementation and should be optimized for large graphs
	nodes := g.getAllNodes()
	n := len(nodes)
	dist := make([][]int, n)
	for i := range dist {
		dist[i] = make([]int, n)
		for j := range dist[i] {
			if i == j {
				dist[i][j] = 0
			} else {
				dist[i][j] = int(^uint(0) >> 1) // Initialize with a large value
			}
		}
	}

	// Initialize distances for direct edges
	for _, edges := range g.edges {
		for _, edge := range edges {
			i := indexOf(nodes, edge.src)
			j := indexOf(nodes, edge.dst)
			dist[i][j] = 1
			if g.graphType == GRAPH {
				dist[j][i] = 1
			}
		}
	}

	// Floyd-Warshall algorithm
	for k := 0; k < n; k++ {
		for i := 0; i < n; i++ {
			for j := 0; j < n; j++ {
				if dist[i][k]+dist[k][j] < dist[i][j] {
					dist[i][j] = dist[i][k] + dist[k][j]
				}
			}
		}
	}

	// Find the maximum finite distance
	diameter := 0
	for i := 0; i < n; i++ {
		for j := 0; j < n; j++ {
			if dist[i][j] < int(^uint(0)>>1) && dist[i][j] > diameter {
				diameter = dist[i][j]
			}
		}
	}

	return diameter
}

func (g *Graph) getAllNodes() []*Node {
	var nodes []*Node
	for _, nodeList := range g.nodes {
		nodes = append(nodes, nodeList...)
	}
	return nodes
}

func indexOf(nodes []*Node, node *Node) int {
	for i, n := range nodes {
		if n == node {
			return i
		}
	}
	return -1
}

// Graph algorithms

func (g *Graph) TopologicalSort() ([]*Node, error) {
	if g.graphType != DIGRAPH {
		return nil, fmt.Errorf("topological sort is only applicable to directed graphs")
	}

	var sorted []*Node
	visited := make(map[*Node]bool)
	temp := make(map[*Node]bool)

	var visit func(*Node) error
	visit = func(node *Node) error {
		if temp[node] {
			return fmt.Errorf("graph contains a cycle")
		}
		if !visited[node] {
			temp[node] = true
			for _, edges := range g.edges {
				for _, edge := range edges {
					if edge.src == node {
						if err := visit(edge.dst); err != nil {
							return err
						}
					}
				}
			}
			visited[node] = true
			temp[node] = false
			sorted = append([]*Node{node}, sorted...)
		}
		return nil
	}

	for _, nodes := range g.nodes {
		for _, node := range nodes {
			if !visited[node] {
				if err := visit(node); err != nil {
					return nil, err
				}
			}
		}
	}

	return sorted, nil
}

func (g *Graph) ShortestPath(start, end *Node) ([]*Node, error) {
	if g.graphType != DIGRAPH {
		return nil, fmt.Errorf("shortest path is only implemented for directed graphs")
	}

	dist := make(map[*Node]int)
	prev := make(map[*Node]*Node)
	queue := make(PriorityQueue, 0)

	for _, nodes := range g.nodes {
		for _, node := range nodes {
			dist[node] = int(^uint(0) >> 1) // Initialize with a large value
			prev[node] = nil
			queue.Push(&Item{node: node, priority: dist[node]})
		}
	}

	dist[start] = 0
	queue.Update(&Item{node: start, priority: 0})

	for queue.Len() > 0 {
		item := heap.Pop(&queue).(*Item)
		u := item.node

		if u == end {
			break
		}

		for _, edges := range g.edges {
			for _, edge := range edges {
				if edge.src == u {
					v := edge.dst
					alt := dist[u] + 1 // Assuming unit edge weights
					if alt < dist[v] {
						dist[v] = alt
						prev[v] = u
						queue.Update(&Item{node: v, priority: alt})
					}
				}
			}
		}
	}

	if prev[end] == nil {
		return nil, fmt.Errorf("no path exists between the given nodes")
	}

	path := []*Node{end}
	for u := prev[end]; u != nil; u = prev[u] {
		path = append([]*Node{u}, path...)
	}

	return path, nil
}

// Priority Queue implementation for Dijkstra's algorithm

type Item struct {
	node     *Node
	priority int
	index    int
}

type PriorityQueue []*Item

func (pq PriorityQueue) Len() int { return len(pq) }

func (pq PriorityQueue) Less(i, j int) bool {
	return pq[i].priority < pq[j].priority
}

func (pq PriorityQueue) Swap(i, j int) {
	pq[i], pq[j] = pq[j], pq[i]
	pq[i].index = i
	pq[j].index = j
}

func (pq *PriorityQueue) Push(x interface{}) {
	n := len(*pq)
	item := x.(*Item)
	item.index = n
	*pq = append(*pq, item)
}

func (pq *PriorityQueue) Pop() interface{} {
	old := *pq
	n := len(old)
	item := old[n-1]
	old[n-1] = nil  // avoid memory leak
	item.index = -1 // for safety
	*pq = old[0 : n-1]
	return item
}

func (pq *PriorityQueue) Update(item *Item) {
	heap.Fix(pq, item.index)
}

// Graph visualization helpers

func (g *Graph) ToPNG(filename string) error {
	cmd := exec.Command("dot", "-Tpng", "-o", filename)
	stdin, err := cmd.StdinPipe()
	if err != nil {
		return err
	}

	if err := cmd.Start(); err != nil {
		return err
	}

	if _, err := io.WriteString(stdin, g.String()); err != nil {
		return err
	}

	if err := stdin.Close(); err != nil {
		return err
	}

	return cmd.Wait()
}

func (g *Graph) ToSVG(filename string) error {
	cmd := exec.Command("dot", "-Tsvg", "-o", filename)
	stdin, err := cmd.StdinPipe()
	if err != nil {
		return err
	}

	if err := cmd.Start(); err != nil {
		return err
	}

	if _, err := io.WriteString(stdin, g.String()); err != nil {
		return err
	}

	if err := stdin.Close(); err != nil {
		return err
	}

	return cmd.Wait()
}

// Utility functions

func escapeString(s string) string {
	s = strings.Replace(s, "\\", "\\\\", -1)
	s = strings.Replace(s, "\"", "\\\"", -1)
	s = strings.Replace(s, "\n", "\\n", -1)
	s = strings.Replace(s, "\r", "\\r", -1)
	return s
}

func unescapeString(s string) string {
	s = strings.Replace(s, "\\\\", "\\", -1)
	s = strings.Replace(s, "\\\"", "\"", -1)
	s = strings.Replace(s, "\\n", "\n", -1)
	s = strings.Replace(s, "\\r", "\r", -1)
	return s
}
