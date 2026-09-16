package checker

// Entry points. Check is the function the Rocq soundness statement
// (new/checker/soundness.v) is about.

// Reason classifies why the checker rejected an input.
type Reason uint64

const (
	// Symbolic-execution failures (the program is not known to be safe).
	RUnboundVar  Reason = 1 // variable not in scope
	RBadType     Reason = 2 // unsupported Go type at a load/store/alloc/op
	RIllSorted   Reason = 3 // operand term has the wrong sort
	RNoPointsTo  Reason = 4 // load/store at a location not owned in the symbolic heap
	RBadConvert  Reason = 5 // Convert between different types
	RBadMonad    Reason = 6 // ;;; or exception_do applied to a non-monad value
	RUnsupported Reason = 7 // expression form not handled
	// Input validation.
	RPreHasOr     Reason = 8  // ∨ in a precondition
	RPreHasExists Reason = 9  // ∃ in a precondition
	RVarsTooShort Reason = 10 // fewer logical variables than parameters
	// Postcondition matching.
	RPostNoDisjunct    Reason = 11 // no disjunct matched the path
	RPostCellMissing   Reason = 12 // points-to atom: no heap cell at that location
	RPostValueMismatch Reason = 13 // points-to atom: value term differs
	RPostPureMissing   Reason = 14 // pure atom not in the path condition
	RPatUnbound        Reason = 15 // pattern variable never bound by a points-to
	RPatConflict       Reason = 16 // pattern variable bound to two different terms
)

// Failure describes a rejected input. Fields other than Reason are filled in
// when meaningful.
type Failure struct {
	Reason   Reason
	PathIdx  uint64 // index of the offending path
	Disjunct uint64 // index of the offending disjunct (postcondition failures)
	Name     string // variable name (RUnboundVar)
	Expr     *Expr  // offending expression
	Atom     *Assn  // offending assertion atom
	Want     *Term  // expected term (postcondition failures)
	Got      *Term  // actual term
}

// assnHasOr reports whether a contains a disjunction anywhere.
func assnHasOr(a *Assn) bool {
	if a == nil {
		return false
	}
	if a.Kind == AOr {
		return true
	}
	if assnHasOr(a.L) {
		return true
	}
	return assnHasOr(a.R)
}

// assnHasExists reports whether a contains an existential anywhere.
func assnHasExists(a *Assn) bool {
	if a == nil {
		return false
	}
	if a.Kind == AExists {
		return true
	}
	if assnHasExists(a.L) {
		return true
	}
	return assnHasExists(a.R)
}

// assnWellSorted sort-checks a precondition: every atom must be well-sorted,
// and no form other than emp, ∗ and the two atoms may appear.
func assnWellSorted(se *sortEnv, a *Assn) *Failure {
	if a == nil {
		return nil
	}
	if a.Kind == AEmp {
		return nil
	}
	if a.Kind == ASep {
		fl := assnWellSorted(se, a.L)
		if fl != nil {
			return fl
		}
		return assnWellSorted(se, a.R)
	}
	if a.Kind == APure || a.Kind == APointsTo {
		return atomWellSorted(se, a)
	}
	return &Failure{Reason: RUnsupported, Atom: a}
}

// assnHeap collects the points-to atoms of a precondition, left to right,
// into the initial symbolic heap.
func assnHeap(a *Assn) []Cell {
	var out []Cell
	if a == nil {
		return out
	}
	if a.Kind == ASep {
		out = append(out, assnHeap(a.L)...)
		out = append(out, assnHeap(a.R)...)
		return out
	}
	if a.Kind == APointsTo {
		return append(out, Cell{Loc: a.X, Val: a.Y})
	}
	return out
}

// assnPure collects the pure atoms of a precondition, left to right, into the
// initial path condition.
func assnPure(a *Assn) []*Term {
	var out []*Term
	if a == nil {
		return out
	}
	if a.Kind == ASep {
		out = append(out, assnPure(a.L)...)
		out = append(out, assnPure(a.R)...)
		return out
	}
	if a.Kind == APure {
		return append(out, a.X)
	}
	return out
}

// Analyze symbolically executes f under the precondition pre. vars gives the
// sorts of the logical variables; variables 0..len(f.Params)-1 are the
// parameters, the rest are ghost variables mentioned by pre. It returns one
// Path per feasible execution path (the strongest postcondition), or a
// Failure if some path could not be shown safe.
func Analyze(f *Func, vars []Sort, pre *Assn) ([]Path, *Failure) {
	if f == nil {
		return nil, &Failure{Reason: RUnsupported}
	}
	if len(f.Params) > len(vars) {
		return nil, &Failure{Reason: RVarsTooShort}
	}
	if assnHasOr(pre) {
		return nil, &Failure{Reason: RPreHasOr, Atom: pre}
	}
	if assnHasExists(pre) {
		return nil, &Failure{Reason: RPreHasExists, Atom: pre}
	}
	se := &sortEnv{vars: vars}
	fl := assnWellSorted(se, pre)
	if fl != nil {
		return nil, fl
	}
	// Parameter i is logical variable i. A repeated parameter name shadows
	// the earlier one, as in Go.
	var en *env = nil
	var i uint64 = 0
	for _, x := range f.Params {
		en = envBind(en, x, &Term{Kind: TVar, Num: i})
		i = i + 1
	}
	st := &State{Heap: assnHeap(pre), Cond: assnPure(pre), Vars: copySorts(vars)}
	return exec(f.Body, en, st)
}

// Verify checks that every path satisfies at least one disjunct of post.
// Heap cells that no disjunct mentions are permitted to leak. vars is
// accepted for symmetry with Analyze; the sorts that matter are the ones
// recorded in each path's state, which allocation may have extended.
func Verify(paths []Path, vars []Sort, post *Assn) *Failure {
	ds := parseDisjuncts(post)
	var pi uint64 = 0
	for _, p := range paths {
		pass := false
		for _, d := range ds {
			if checkDisjunct(p, d) == nil {
				pass = true
				break
			}
		}
		if !pass {
			return &Failure{Reason: RPostNoDisjunct, PathIdx: pi}
		}
		pi = pi + 1
	}
	return nil
}

// DisjunctFailure records why one disjunct of a postcondition failed for one
// path.
type DisjunctFailure struct {
	Path     uint64
	Disjunct uint64
	Fail     *Failure
}

// Explain returns, for the first path that satisfies no disjunct of post, the
// reason each disjunct failed. It returns nil when every path passes, so that
// a caller can print a diagnosis exactly when Verify rejects.
func Explain(paths []Path, vars []Sort, post *Assn) []DisjunctFailure {
	ds := parseDisjuncts(post)
	var pi uint64 = 0
	for _, p := range paths {
		var out []DisjunctFailure
		pass := false
		var di uint64 = 0
		for _, d := range ds {
			fl := checkDisjunct(p, d)
			if fl == nil {
				pass = true
			} else {
				out = append(out, DisjunctFailure{Path: pi, Disjunct: di, Fail: fl})
			}
			di = di + 1
		}
		if !pass {
			return out
		}
		pi = pi + 1
	}
	return nil
}

// Check reports whether f, run under pre, is safe and establishes post.
func Check(f *Func, vars []Sort, pre *Assn, post *Assn) bool {
	paths, fail := Analyze(f, vars, pre)
	if fail != nil {
		return false
	}
	return Verify(paths, vars, post) == nil
}
