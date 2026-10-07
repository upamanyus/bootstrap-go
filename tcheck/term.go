package tcheck

// Operations on terms: equality, sorts, matching, instantiation and
// normalization by the table's facts.

func termEq(a *Term, b *Term) bool {
	if a.Kind != b.Kind || a.Num != b.Num || len(a.Args) != len(b.Args) {
		return false
	}
	for i := 0; i < len(a.Args); i++ {
		if !termEq(a.Args[i], b.Args[i]) {
			return false
		}
	}
	return true
}

// sortOf returns the sort of t, whose variables have the sorts vars, and
// whether t is well sorted.
func sortOf(syms []SymDecl, vars []Sort, t *Term) (Sort, bool) {
	if t == nil {
		return Sort{}, false
	}
	if t.Kind == TVar {
		if t.Num < uint64(len(vars)) && len(t.Args) == 0 {
			return vars[t.Num], true
		}
		return Sort{}, false
	}
	if t.Kind == TSym {
		if t.Num >= uint64(len(syms)) {
			return Sort{}, false
		}
		d := syms[t.Num]
		if len(d.Args) != len(t.Args) {
			return Sort{}, false
		}
		for i := 0; i < len(t.Args); i++ {
			s, ok := sortOf(syms, vars, t.Args[i])
			if !ok || !sortEq(s, d.Args[i]) {
				return Sort{}, false
			}
		}
		return d.Res, true
	}
	if t.Kind == TPair {
		if len(t.Args) != 2 {
			return Sort{}, false
		}
		if !hasSort(syms, vars, t.Args[0], Sort{Kind: SortVal}) || !hasSort(syms, vars, t.Args[1], Sort{Kind: SortVal}) {
			return Sort{}, false
		}
		return Sort{Kind: SortVal}, true
	}
	if t.Kind == TLit {
		if len(t.Args) == 0 || !hasSort(syms, vars, t.Args[0], Sort{Kind: SortType}) {
			return Sort{}, false
		}
		for i := 1; i < len(t.Args); i++ {
			if !hasSort(syms, vars, t.Args[i], Sort{Kind: SortVal}) {
				return Sort{}, false
			}
		}
		return Sort{Kind: SortVal}, true
	}
	if t.Kind == TUnit && len(t.Args) == 0 {
		return Sort{Kind: SortVal}, true
	}
	return Sort{}, false
}

func hasSort(syms []SymDecl, vars []Sort, t *Term, s Sort) bool {
	s2, ok := sortOf(syms, vars, t)
	return ok && sortEq(s, s2)
}

// matcher binds the variables of a pattern (a rule's, a fact's or the
// postcondition's), whose sorts are psorts, to terms over the logical
// variables of the state, whose sorts are vars.
type matcher struct {
	syms   []SymDecl
	vars   []Sort
	psorts []Sort
	bind   []*Term
}

func (m *matcher) save() []*Term {
	b := make([]*Term, len(m.bind))
	copy(b, m.bind)
	return b
}

func (m *matcher) term(pat *Term, t *Term) bool {
	if pat.Kind == TVar {
		n := pat.Num
		if m.bind[n] != nil {
			return termEq(m.bind[n], t)
		}
		if !hasSort(m.syms, m.vars, t, m.psorts[n]) {
			return false
		}
		m.bind[n] = t
		return true
	}
	if pat.Kind != t.Kind || pat.Num != t.Num || len(pat.Args) != len(t.Args) {
		return false
	}
	for i := 0; i < len(pat.Args); i++ {
		if !m.term(pat.Args[i], t.Args[i]) {
			return false
		}
	}
	return true
}

func (m *matcher) pat(p *Pat, s *Pat) bool {
	if p.Kind != s.Kind {
		return false
	}
	if p.Kind == PVal {
		return m.term(p.T, s.T)
	}
	return m.pat(p.A, s.A) && m.pat(p.B, s.B)
}

func (m *matcher) atomArgs(pats []*Term, ts []*Term) bool {
	if len(pats) != len(ts) {
		return false
	}
	for i := 0; i < len(pats); i++ {
		if !m.term(pats[i], ts[i]) {
			return false
		}
	}
	return true
}

func (m *matcher) allBound(n uint64) bool {
	for i := uint64(0); i < n; i++ {
		if m.bind[i] == nil {
			return false
		}
	}
	return true
}

// inst replaces the variables of pat by their bindings; every variable of
// pat must be bound.
func inst(pat *Term, bind []*Term) *Term {
	if pat.Kind == TVar {
		return bind[pat.Num]
	}
	if len(pat.Args) == 0 {
		return pat
	}
	args := make([]*Term, len(pat.Args))
	for i := 0; i < len(pat.Args); i++ {
		args[i] = inst(pat.Args[i], bind)
	}
	return &Term{Kind: pat.Kind, Num: pat.Num, Args: args}
}

// varsBound reports whether every variable of t is below n.
func varsBelow(t *Term, n uint64) bool {
	if t.Kind == TVar {
		return t.Num < n
	}
	for i := 0; i < len(t.Args); i++ {
		if !varsBelow(t.Args[i], n) {
			return false
		}
	}
	return true
}

// occurs reports whether variable v occurs in t.
func occurs(v uint64, t *Term) bool {
	if t.Kind == TVar {
		return t.Num == v
	}
	for i := 0; i < len(t.Args); i++ {
		if occurs(v, t.Args[i]) {
			return true
		}
	}
	return false
}
