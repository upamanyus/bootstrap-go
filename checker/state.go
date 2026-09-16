package checker

// Symbolic states and paths. These are internal to the analysis and are
// returned to callers for printing; they do not appear in the Rocq soundness
// statement.

// Cell is one owned heap cell: the location term (always a TVar in practice,
// since the fragment has no pointer arithmetic) and the value term stored in it.
type Cell struct {
	Loc *Term
	Val *Term
}

// State is a symbolic state.
type State struct {
	Heap []Cell  // symbolic heap: the points-to facts currently owned
	Cond []*Term // path condition: boolean terms known to hold, oldest first
	Vars []Sort  // sorts of logical variables 0..len(Vars)-1; allocation appends
}

// Path is one outcome of symbolic execution: the return value term and the
// final state.
type Path struct {
	Ret *Term
	St  *State
}

// clone returns a deep-enough copy of s: fresh slices so that appending to one
// copy never affects another. Terms are immutable and are shared.
func (s *State) clone() *State {
	h := make([]Cell, len(s.Heap))
	copy(h, s.Heap)
	c := make([]*Term, len(s.Cond))
	copy(c, s.Cond)
	v := make([]Sort, len(s.Vars))
	copy(v, s.Vars)
	return &State{Heap: h, Cond: c, Vars: v}
}
