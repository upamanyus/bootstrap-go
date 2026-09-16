package checker

// Postcondition matching.
//
// A postcondition is a disjunction of disjuncts, one per group of paths. Each
// disjunct is a list of ∃-bound pattern variables followed by a separating
// conjunction of atoms. A path satisfies a disjunct if
//
//   - every points-to atom of the disjunct can be matched against a distinct
//     cell of the path's symbolic heap, and
//   - every pure atom of the disjunct, once the pattern variables and `ret`
//     have been substituted, is syntactically justified by the path condition.
//
// Matching points-to atoms is what binds the pattern variables, so it runs to
// a fixpoint first (an atom whose location still mentions an unbound pattern
// variable is deferred); pure atoms are checked afterwards. Heap cells the
// postcondition does not mention are simply leaked, which is sound for a
// partial-correctness postcondition without a "no leaks" guarantee.

// disjunct is one parsed disjunct: the declared sorts of its pattern
// variables (indexed by the AExists Var, with patOk marking the indices that
// were actually bound) and the flat list of its atoms. fail is set when the
// disjunct is malformed, in which case it can never be satisfied.
type disjunct struct {
	pats  []Sort
	patOk []bool
	atoms []*Assn
	fail  *Failure
}

// growPats extends pats/patOk so that index n is addressable.
func (d *disjunct) growPats(n uint64) {
	for uint64(len(d.pats)) <= n {
		d.pats = append(d.pats, SortInt)
		d.patOk = append(d.patOk, false)
	}
}

// flatten collects the atoms of a separating conjunction. AOr and AExists are
// only allowed above it (as the top-level disjunction and the leading
// binders), not inside.
func (d *disjunct) flatten(a *Assn) *Failure {
	if a == nil {
		return &Failure{Reason: RUnsupported}
	}
	if a.Kind == AEmp {
		return nil
	}
	if a.Kind == ASep {
		fl := d.flatten(a.L)
		if fl != nil {
			return fl
		}
		return d.flatten(a.R)
	}
	if a.Kind == APure || a.Kind == APointsTo {
		d.atoms = append(d.atoms, a)
		return nil
	}
	return &Failure{Reason: RUnsupported, Atom: a}
}

// collectDisjuncts flattens the top-level ∨ chain of a postcondition, left to
// right. A postcondition with no ∨ is a single disjunct.
func collectDisjuncts(a *Assn) []*Assn {
	var out []*Assn
	if a != nil && a.Kind == AOr {
		out = append(out, collectDisjuncts(a.L)...)
		out = append(out, collectDisjuncts(a.R)...)
		return out
	}
	return append(out, a)
}

// parseDisjunct peels the leading ∃ binders off a disjunct and flattens the
// separating conjunction underneath.
func parseDisjunct(a *Assn) *disjunct {
	d := &disjunct{}
	body := a
	for body != nil && body.Kind == AExists {
		d.growPats(body.Var)
		if d.patOk[body.Var] {
			// The same pattern variable bound twice: the disjunct is
			// ambiguous, so reject it rather than pick a binder.
			d.fail = &Failure{Reason: RPatConflict, Atom: body}
			return d
		}
		d.pats[body.Var] = body.Sort
		d.patOk[body.Var] = true
		body = body.L
	}
	fl := d.flatten(body)
	if fl != nil {
		d.fail = fl
	}
	return d
}

// parseDisjuncts parses every disjunct of a postcondition.
func parseDisjuncts(post *Assn) []*disjunct {
	var out []*disjunct
	for _, a := range collectDisjuncts(post) {
		out = append(out, parseDisjunct(a))
	}
	return out
}

// instantiate replaces the pattern variables that subst has bound, and
// `ret`, by their values. Unbound pattern variables are left in place; the
// caller detects them with hasPat.
func instantiate(t *Term, subst []*Term, ret *Term) *Term {
	if t == nil {
		return nil
	}
	if t.Kind == TPat {
		if t.Num < uint64(len(subst)) && subst[t.Num] != nil {
			return subst[t.Num]
		}
		return t
	}
	if t.Kind == TResult {
		return ret
	}
	if t.A == nil && t.B == nil && t.C == nil {
		return t
	}
	return &Term{
		Kind: t.Kind,
		Num:  t.Num,
		A:    instantiate(t.A, subst, ret),
		B:    instantiate(t.B, subst, ret),
		C:    instantiate(t.C, subst, ret),
	}
}

// hasPat reports whether t still mentions a pattern variable.
func hasPat(t *Term) bool {
	if t == nil {
		return false
	}
	if t.Kind == TPat {
		return true
	}
	if hasPat(t.A) {
		return true
	}
	if hasPat(t.B) {
		return true
	}
	return hasPat(t.C)
}

// matchTerm matches the pattern term pat against the concrete term act,
// binding pattern variables into subst as it goes. A pattern variable matches
// any term of its declared sort, but only once: a second occurrence must meet
// a structurally equal term.
func matchTerm(pat *Term, act *Term, subst []*Term, d *disjunct, vars []Sort, ret *Term) *Failure {
	if pat == nil {
		if act == nil {
			return nil
		}
		return &Failure{Reason: RPostValueMismatch, Want: pat, Got: act}
	}
	if pat.Kind == TPat {
		if pat.Num >= uint64(len(subst)) || !d.patOk[pat.Num] {
			return &Failure{Reason: RPatUnbound, Want: pat}
		}
		if subst[pat.Num] == nil {
			s, ok := SortOf(vars, act)
			if !ok || s != d.pats[pat.Num] {
				return &Failure{Reason: RIllSorted, Want: pat, Got: act}
			}
			subst[pat.Num] = act
			return nil
		}
		if !termEq(subst[pat.Num], act) {
			return &Failure{Reason: RPatConflict, Want: subst[pat.Num], Got: act}
		}
		return nil
	}
	if pat.Kind == TResult {
		// `ret` stands for the path's return term; match that instead.
		// A return term never mentions TResult, so this does not loop.
		return matchTerm(ret, act, subst, d, vars, ret)
	}
	if act == nil {
		return &Failure{Reason: RPostValueMismatch, Want: pat, Got: act}
	}
	if pat.Kind != act.Kind || pat.Num != act.Num {
		return &Failure{Reason: RPostValueMismatch, Want: pat, Got: act}
	}
	fl := matchTerm(pat.A, act.A, subst, d, vars, ret)
	if fl != nil {
		return fl
	}
	fl = matchTerm(pat.B, act.B, subst, d, vars, ret)
	if fl != nil {
		return fl
	}
	return matchTerm(pat.C, act.C, subst, d, vars, ret)
}

// findCell finds an unused heap cell whose location is structurally equal
// to l, returning its index.
func findCell(h []Cell, used []bool, l *Term) (uint64, bool) {
	var i uint64 = 0
	for _, c := range h {
		if !used[i] && termEq(c.Loc, l) {
			return i, true
		}
		i = i + 1
	}
	return 0, false
}

// atomWellSorted sort-checks a single atom.
func atomWellSorted(se *sortEnv, a *Assn) *Failure {
	if a == nil {
		return &Failure{Reason: RUnsupported}
	}
	if a.Kind == APure {
		s, ok := sortOfEnv(se, a.X)
		if !ok || s != SortBool {
			return &Failure{Reason: RIllSorted, Atom: a, Got: a.X}
		}
		return nil
	}
	if a.Kind == APointsTo {
		s, ok := sortOfEnv(se, a.X)
		if !ok || s != SortLoc {
			return &Failure{Reason: RIllSorted, Atom: a, Got: a.X}
		}
		_, ok2 := sortOfEnv(se, a.Y)
		if !ok2 {
			return &Failure{Reason: RIllSorted, Atom: a, Got: a.Y}
		}
		return nil
	}
	return &Failure{Reason: RUnsupported, Atom: a}
}

// condHolds reports whether the path condition cond syntactically justifies
// the boolean term t. The checker does no arithmetic reasoning: t must either
// be one of the recorded facts, be a reflexive equation, or be `true`.
func condHolds(cond []*Term, t *Term) bool {
	for _, c := range cond {
		if termEq(c, t) {
			return true
		}
	}
	if t == nil {
		return false
	}
	if t.Kind == TEq && termEq(t.A, t.B) {
		return true
	}
	if t.Kind == TBool && t.Num == 1 {
		return true
	}
	return false
}

// firstUnresolved returns the first points-to atom that phase 1 could not
// resolve, for the RPatUnbound failure.
func firstUnresolved(d *disjunct, done []bool) *Assn {
	var i uint64 = 0
	for _, at := range d.atoms {
		if at.Kind == APointsTo && !done[i] {
			return at
		}
		i = i + 1
	}
	return nil
}

// checkDisjunct reports whether path p satisfies disjunct d, returning the
// reason it does not.
func checkDisjunct(p Path, d *disjunct) *Failure {
	if d.fail != nil {
		return d.fail
	}
	if p.St == nil {
		return &Failure{Reason: RUnsupported}
	}

	// Phase 0: the disjunct must be well-sorted under this path's variables,
	// its own pattern variables, and the sort of its return value.
	rs, rok := SortOf(p.St.Vars, p.Ret)
	se := &sortEnv{vars: p.St.Vars, pats: d.pats, patOk: d.patOk, ret: rs, retOk: rok}
	for _, at := range d.atoms {
		fl := atomWellSorted(se, at)
		if fl != nil {
			return fl
		}
	}

	subst := make([]*Term, len(d.pats))
	used := make([]bool, len(p.St.Heap))
	done := make([]bool, len(d.atoms))

	// Phase 1: match the points-to atoms against distinct heap cells,
	// binding pattern variables, until no further atom can be resolved.
	remaining := 0
	for _, at := range d.atoms {
		if at.Kind == APointsTo {
			remaining = remaining + 1
		}
	}
	for remaining > 0 {
		progress := false
		var i uint64 = 0
		for _, at := range d.atoms {
			if at.Kind == APointsTo && !done[i] {
				l := instantiate(at.X, subst, p.Ret)
				if !hasPat(l) {
					j, ok := findCell(p.St.Heap, used, l)
					if !ok {
						return &Failure{Reason: RPostCellMissing, Atom: at, Want: l}
					}
					fl := matchTerm(at.Y, p.St.Heap[j].Val, subst, d, p.St.Vars, p.Ret)
					if fl != nil {
						fl.Atom = at
						return fl
					}
					used[j] = true
					done[i] = true
					remaining = remaining - 1
					progress = true
				}
			}
			i = i + 1
		}
		if !progress {
			return &Failure{Reason: RPatUnbound, Atom: firstUnresolved(d, done)}
		}
	}

	// Phase 2: every pure atom must be justified by the path condition.
	for _, at := range d.atoms {
		if at.Kind == APure {
			t := instantiate(at.X, subst, p.Ret)
			if hasPat(t) {
				return &Failure{Reason: RPatUnbound, Atom: at, Want: t}
			}
			if !condHolds(p.St.Cond, t) {
				return &Failure{Reason: RPostPureMissing, Atom: at, Want: t}
			}
		}
	}
	return nil
}
