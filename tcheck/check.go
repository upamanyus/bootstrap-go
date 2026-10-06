package tcheck

// Well-formedness of the input, and the entry points.

func wfAtom(inp *Input, vars []Sort, a *Atom) bool {
	if a == nil {
		return false
	}
	if a.Kind == APred {
		if a.Num >= uint64(len(inp.Preds)) {
			return false
		}
		d := inp.Preds[a.Num]
		if len(d.Args) != len(a.Args) {
			return false
		}
		for i := 0; i < len(a.Args); i++ {
			if !hasSort(inp.Syms, vars, a.Args[i], d.Args[i]) {
				return false
			}
		}
		return true
	}
	if a.Kind == AEq && len(a.Args) == 2 {
		s, ok := sortOf(inp.Syms, vars, a.Args[0])
		return ok && hasSort(inp.Syms, vars, a.Args[1], s)
	}
	return false
}

func wfAtoms(inp *Input, vars []Sort, as []*Atom) bool {
	for i := 0; i < len(as); i++ {
		if !wfAtom(inp, vars, as[i]) {
			return false
		}
	}
	return true
}

func wfPat(inp *Input, vars []Sort, p *Pat) bool {
	if p == nil {
		return false
	}
	if p.Kind == PVal {
		return hasSort(inp.Syms, vars, p.T, Sort{Kind: SortVal})
	}
	if p.Kind == PApp {
		return wfPat(inp, vars, p.A) && wfPat(inp, vars, p.B)
	}
	return false
}

func occursPat(v uint64, p *Pat) bool {
	if p.Kind == PVal {
		return occurs(v, p.T)
	}
	return occursPat(v, p.A) || occursPat(v, p.B)
}

func occursAtoms(v uint64, as []*Atom) bool {
	for i := 0; i < len(as); i++ {
		if as[i].Kind == APred {
			for j := 0; j < len(as[i].Args); j++ {
				if occurs(v, as[i].Args[j]) {
					return true
				}
			}
		}
	}
	return false
}

// wfRule: the left-hand side and precondition mention only the parameters,
// and every parameter occurs in the left-hand side or in a predicate atom
// of the precondition, so that matching binds it.
func wfRule(inp *Input, r *Rule) bool {
	if r == nil {
		return false
	}
	all := append(append([]Sort{}, r.Vars...), r.Ex...)
	if !wfPat(inp, r.Vars, r.Lhs) || !wfAtoms(inp, r.Vars, r.Pre) {
		return false
	}
	if !hasSort(inp.Syms, all, r.Ret, Sort{Kind: SortVal}) || !wfAtoms(inp, all, r.Post) {
		return false
	}
	for v := uint64(0); v < uint64(len(r.Vars)); v++ {
		if !occursPat(v, r.Lhs) && !occursAtoms(v, r.Pre) {
			return false
		}
	}
	return true
}

// wfFact: the left-hand side is a symbol application, both sides have the
// same sort, and the right-hand side mentions only variables of the left.
func wfFact(inp *Input, f *Fact) bool {
	if f == nil || f.Lhs == nil || f.Lhs.Kind != TSym {
		return false
	}
	s, ok := sortOf(inp.Syms, f.Vars, f.Lhs)
	if !ok || !hasSort(inp.Syms, f.Vars, f.Rhs, s) {
		return false
	}
	for v := uint64(0); v < uint64(len(f.Vars)); v++ {
		if occurs(v, f.Rhs) && !occurs(v, f.Lhs) {
			return false
		}
	}
	return true
}

// wfExpr: the values of the code are closed and well sorted, and the
// elements of a literal are values or variables.
func wfExpr(inp *Input, e *Expr) bool {
	if e == nil {
		return false
	}
	if e.Kind == EVal {
		return hasSort(inp.Syms, nil, e.T, Sort{Kind: SortVal})
	}
	if e.Kind == EVar {
		return true
	}
	if e.Kind == ELit {
		if !hasSort(inp.Syms, nil, e.T, Sort{Kind: SortType}) {
			return false
		}
		for i := 0; i < len(e.Elems); i++ {
			el := e.Elems[i]
			if el == nil || (el.Kind != EVal && el.Kind != EVar) || !wfExpr(inp, el) {
				return false
			}
		}
		return true
	}
	if e.Kind == EApp || e.Kind == EPair || e.Kind == ELet || e.Kind == ESeq || e.Kind == EXSeq {
		return wfExpr(inp, e.A) && wfExpr(inp, e.B)
	}
	if e.Kind == EDo || e.Kind == ERet || e.Kind == EXDo {
		return wfExpr(inp, e.A)
	}
	return false
}

func wfSpec(inp *Input) bool {
	sp := inp.Sp
	if len(inp.Fn.Params) == 0 || len(sp.Args) != len(inp.Fn.Params) {
		return false
	}
	for i := 0; i < len(sp.Args); i++ {
		if !hasSort(inp.Syms, sp.Vars, sp.Args[i], Sort{Kind: SortVal}) {
			return false
		}
	}
	all := append(append([]Sort{}, sp.Vars...), sp.Ex...)
	return wfAtoms(inp, sp.Vars, sp.Pre) && hasSort(inp.Syms, all, sp.Ret, Sort{Kind: SortVal}) &&
		wfAtoms(inp, all, sp.Post)
}

func wfInput(inp *Input) (bool, uint64) {
	for i := 0; i < len(inp.Rules); i++ {
		if !wfRule(inp, inp.Rules[i]) {
			return false, uint64(i)
		}
	}
	for i := 0; i < len(inp.Facts); i++ {
		if !wfFact(inp, inp.Facts[i]) {
			return false, uint64(len(inp.Rules) + i)
		}
	}
	if !wfExpr(inp, inp.Fn.Body) || !wfSpec(inp) {
		return false, uint64(len(inp.Rules) + len(inp.Facts))
	}
	return true, 0
}

// checkPost matches the postcondition against the final state and the
// returned value.
func (c *checker) checkPost(st *state, ret *Term) bool {
	sp := c.inp.Sp
	nv := uint64(len(sp.Vars))
	psorts := append(append([]Sort{}, sp.Vars...), sp.Ex...)
	m := &matcher{syms: c.inp.Syms, vars: st.vars, psorts: psorts, bind: make([]*Term, len(psorts))}
	for i := uint64(0); i < nv; i++ {
		m.bind[i] = &Term{Kind: TVar, Num: i}
	}
	if !m.term(sp.Ret, ret) {
		return false
	}
	if c.matchAtoms(st, m, sp.Post) == nil {
		return false
	}
	return m.allBound(uint64(len(psorts))) && c.pureAtomsHold(st, m, sp.Post)
}

// Run checks the input and returns nil if the triple is established, and
// which rules and facts it used (rules first, then facts).
func Run(inp *Input) (*Failure, []bool) {
	ok, item := wfInput(inp)
	if !ok {
		return &Failure{Code: FailInput, Item: item}, nil
	}
	c := &checker{inp: inp, fuel: 100000, used: make([]bool, len(inp.Rules)+len(inp.Facts))}
	sp := inp.Sp
	st := &state{vars: append([]Sort{}, sp.Vars...)}
	for i := 0; i < len(sp.Pre); i++ {
		c.addAtom(st, sp.Pre[i])
	}
	var env []binding
	for i := 0; i < len(inp.Fn.Params); i++ {
		env = append(env, binding{name: inp.Fn.Params[i], t: c.norm(st.vars, sp.Args[i])})
	}
	r := c.eval(st, env, inp.Fn.Body)
	if c.fail != nil {
		return c.fail, c.used
	}
	if r.kind != resVal {
		return &Failure{Code: FailMonad, Expr: inp.Fn.Body}, c.used
	}
	if !c.checkPost(st, r.t) {
		if c.fail != nil {
			return c.fail, c.used
		}
		return &Failure{Code: FailPost}, c.used
	}
	return nil, c.used
}

// Check is the function the Rocq statement is about: it parses the
// serialized input and returns true only if the triple is established.
func Check(b []byte) bool {
	inp := Parse(b)
	if inp == nil {
		return false
	}
	f, _ := Run(inp)
	return f == nil
}
