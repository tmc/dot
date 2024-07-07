package dot

import (
	"encoding/json"
	"fmt"
	"io"
	"os/exec"
	"reflect"
	"regexp"
	"sort"
	"strings"
	"sync"
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

// Set an attribute on the graph.
func (g *Graph) Set(key, value string) error {
	g.Lock()
	defer g.Unlock()
	if !validGraphAttribute(key) {
		return ErrInvalidGraphAttribute
	}
	g.attributes[key] = value
	return nil
}

func (g *Graph) Get(key string) string {
	g.RLock()
	defer g.RUnlock()
	return g.attributes[key]
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
	queue := []*Node{g.nodes[startNode][0]}

	for len(queue) > 0 {
		node := queue[0]
		queue = queue[1:]

		if !visited[node.Name()] {
			visited[node.Name()] = true
			visitor(node)

			for _, edges := range g.edges {
				for _, edge := range edges {
					if edge.src == node && !visited[edge.dst.Name()] {
						queue = append(queue, edge.dst)
					}
				}
			}
		}
	}
}

// Graph operations

// Merge merges the contents of another graph into this graph.
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
		if _, ok := other.nodes[name]; !ok {
			for _, node := range nodes {
				diff.AddNode(node.Clone())
			}
		}
	}
	for name, nodes := range other.nodes {
		if _, ok := g.nodes[name]; !ok {
			for _, node := range nodes {
				diff.AddNode(node.Clone())
			}
		}
	}

	// Compare edges
	for name, edges := range g.edges {
		if _, ok := other.edges[name]; !ok {
			for _, edge := range edges {
				diff.AddEdge(edge.Clone())
			}
		}
	}
	for name, edges := range other.edges {
		if _, ok := g.edges[name]; !ok {
			for _, edge := range edges {
				diff.AddEdge(edge.Clone())
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
	if g.Name != other.Name || g.graphType != other.graphType {
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

	return true
}

// Graph validation and error checking

func (g *Graph) Validate() error {
	visited := make(map[*Graph]bool)
	return g.validateWithVisited(visited)
}

func (g *Graph) validateWithVisited(visited map[*Graph]bool) error {
	if visited[g] {
		return fmt.Errorf("cyclic subgraph structure detected")
	}
	visited[g] = true

	if err := g.validateNodes(); err != nil {
		return err
	}
	if err := g.validateEdges(); err != nil {
		return err
	}
	if err := g.validateSubgraphs(visited); err != nil {
		return err
	}
	if err := g.validateUniqueNodeNames(); err != nil {
		return err
	}
	return g.validateAttributes()
}

func (g *Graph) validateSubgraphs(visited map[*Graph]bool) error {
	for name, subgraphs := range g.subgraphs {
		for _, sg := range subgraphs {
			if sg.Name != name {
				return fmt.Errorf("subgraph name mismatch: %s != %s", sg.Name, name)
			}
			if err := sg.validateWithVisited(visited); err != nil {
				return fmt.Errorf("invalid subgraph %s: %v", name, err)
			}
		}
	}
	return nil
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
			for attr := range node.attributes {
				if !validNodeAttribute(attr) {
					return fmt.Errorf("invalid node attribute for %s: %s", name, attr)
				}
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
			for attr := range edge.attributes {
				if !validEdgeAttribute(attr) {
					return fmt.Errorf("invalid edge attribute for %s -> %s: %s", edge.src.Name(), edge.dst.Name(), attr)
				}
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
	visited := make(map[*Node]bool)

	for _, nodes := range g.nodes {
		for _, node := range nodes {
			dist[node] = int(^uint(0) >> 1) // Initialize with a large value
			prev[node] = nil
		}
	}

	dist[start] = 0
	queue := []*Node{start}

	for len(queue) > 0 {
		u := queue[0]
		queue = queue[1:]

		if u == end {
			break
		}

		if visited[u] {
			continue
		}
		visited[u] = true

		// Find outgoing edges from u
		for edgeName, edges := range g.edges {
			if strings.HasPrefix(edgeName, u.name+"->") {
				for _, edge := range edges {
					v := edge.dst
					alt := dist[u] + 1 // Assuming unit edge weights
					if alt < dist[v] {
						dist[v] = alt
						prev[v] = u
						queue = append(queue, v)
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
