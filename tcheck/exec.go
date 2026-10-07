package tcheck

// Symbolic execution of the code, one path (the fragment has no if:).

// Failure codes.
const (
	FailParse     uint64 = 1 // the input does not parse
	FailInput     uint64 = 2 // the input is ill formed (ill sorted, unbindable rule variable, ...)
	FailUnbound   uint64 = 3 // a variable of the code is not bound
	FailNoRule    uint64 = 4 // no rule applies to Pat
	FailMonad     uint64 = 5 // an exception-monad value where a value is needed, or the converse
	FailLitElem   uint64 = 6 // an element of a literal is not a value or a variable
	FailPost      uint64 = 7 // the postcondition does not hold at the end
	FailFuel      uint64 = 8 // normalization by the facts did not terminate within the fuel
	FailUnsupport uint64 = 9 // a construct the checker does not handle
)

// Failure says why Check answered false.
type Failure struct {
	Code uint64
	Pat  *Pat  // FailNoRule: the expression no rule applies to
	Expr *Expr // FailUnbound, FailMonad, FailLitElem, FailUnsupport
	Item uint64
}

// state is the symbolic state: owned predicate atoms, pure facts known to
// hold, and the sorts of the logical variables.
type state struct {
	heap []*Atom
	pure []*Atom
	vars []Sort
}

type binding struct {
	name string
	t    *Term
}

// Result kinds: a value, or one of the two exception-monad values.
const (
	resVal  uint64 = 0
	resExec uint64 = 1 // ("execute", #())
	resRet  uint64 = 2 // ("return", t)
)

type result struct {
	kind uint64
	t    *Term
}

type checker struct {
	inp  *Input
	fuel uint64
	fail *Failure
	used []bool // which rules and facts were used: rules first, then facts
}

func (c *checker) setFail(f *Failure) {
	if c.fail == nil {
		c.fail = f
	}
}

// norm rewrites t with the facts, innermost first, to a normal form.
func (c *checker) norm(vars []Sort, t *Term) *Term {
	if c.fail != nil {
		return t
	}
	t2 := t
	if len(t.Args) != 0 {
		args := make([]*Term, len(t.Args))
		for i := 0; i < len(t.Args); i++ {
			args[i] = c.norm(vars, t.Args[i])
		}
		t2 = &Term{Kind: t.Kind, Num: t.Num, Args: args}
	}
	for i := 0; i < len(c.inp.Facts); i++ {
		f := c.inp.Facts[i]
		m := &matcher{syms: c.inp.Syms, vars: vars, psorts: f.Vars, bind: make([]*Term, len(f.Vars))}
		if m.term(f.Lhs, t2) {
			if c.fuel == 0 {
				c.setFail(&Failure{Code: FailFuel})
				return t2
			}
			c.fuel = c.fuel - 1
			c.used[len(c.inp.Rules)+i] = true
			return c.norm(vars, inst(f.Rhs, m.bind))
		}
	}
	return t2
}

func (c *checker) normArgs(vars []Sort, ts []*Term) []*Term {
	out := make([]*Term, len(ts))
	for i := 0; i < len(ts); i++ {
		out[i] = c.norm(vars, ts[i])
	}
	return out
}

// holds decides a pure fact: syntactically, after normalization, or because
// it is known.
func (c *checker) holds(st *state, a *Term, b *Term) bool {
	na := c.norm(st.vars, a)
	nb := c.norm(st.vars, b)
	if termEq(na, nb) {
		return true
	}
	for i := 0; i < len(st.pure); i++ {
		p := st.pure[i]
		if termEq(p.Args[0], na) && termEq(p.Args[1], nb) {
			return true
		}
		if termEq(p.Args[0], nb) && termEq(p.Args[1], na) {
			return true
		}
	}
	return false
}

// addAtom adds an instantiated atom to the state.
func (c *checker) addAtom(st *state, a *Atom) {
	n := &Atom{Kind: a.Kind, Num: a.Num, Args: c.normArgs(st.vars, a.Args)}
	if a.Kind == APred {
		st.heap = append(st.heap, n)
	} else {
		st.pure = append(st.pure, n)
	}
}

func instAtom(a *Atom, bind []*Term) *Atom {
	args := make([]*Term, len(a.Args))
	for i := 0; i < len(a.Args); i++ {
		args[i] = inst(a.Args[i], bind)
	}
	return &Atom{Kind: a.Kind, Num: a.Num, Args: args}
}

// matchAtoms matches the predicate atoms of pats against the heap, in
// order, each against the first heap atom it matches that has not been
// consumed; a persistent atom may be matched any number of times. It
// returns which heap atoms are consumed, or nil.
func (c *checker) matchAtoms(st *state, m *matcher, pats []*Atom) []bool {
	taken := make([]bool, len(st.heap))
	for i := 0; i < len(pats); i++ {
		a := pats[i]
		if a.Kind == APred {
			pers := c.inp.Preds[a.Num].Pers
			found := false
			for j := 0; j < len(st.heap) && !found; j++ {
				h := st.heap[j]
				if h.Num == a.Num && (pers || !taken[j]) {
					saved := m.save()
					if m.atomArgs(a.Args, h.Args) {
						found = true
						if !pers {
							taken[j] = true
						}
					} else {
						m.bind = saved
					}
				}
			}
			if !found {
				return nil
			}
		}
	}
	return taken
}

// pureAtomsHold checks the pure atoms of pats, all of whose variables are
// bound.
func (c *checker) pureAtomsHold(st *state, m *matcher, pats []*Atom) bool {
	for i := 0; i < len(pats); i++ {
		a := pats[i]
		if a.Kind == AEq {
			if !c.holds(st, inst(a.Args[0], m.bind), inst(a.Args[1], m.bind)) {
				return false
			}
		}
	}
	return true
}

func removeTaken(heap []*Atom, taken []bool) []*Atom {
	var out []*Atom
	for j := 0; j < len(heap); j++ {
		if !taken[j] {
			out = append(out, heap[j])
		}
	}
	return out
}

// applyRule applies rule r to s if it matches, and returns the result.
func (c *checker) applyRule(st *state, r *Rule, s *Pat) *Term {
	nv := uint64(len(r.Vars))
	psorts := append(append([]Sort{}, r.Vars...), r.Ex...)
	m := &matcher{syms: c.inp.Syms, vars: st.vars, psorts: psorts, bind: make([]*Term, len(psorts))}
	if !m.pat(r.Lhs, s) {
		return nil
	}
	taken := c.matchAtoms(st, m, r.Pre)
	if taken == nil || !m.allBound(nv) || !c.pureAtomsHold(st, m, r.Pre) {
		return nil
	}
	st.heap = removeTaken(st.heap, taken)
	for i := 0; i < len(r.Ex); i++ {
		m.bind[nv+uint64(i)] = &Term{Kind: TVar, Num: uint64(len(st.vars))}
		st.vars = append(st.vars, r.Ex[i])
	}
	for i := 0; i < len(r.Post); i++ {
		c.addAtom(st, instAtom(r.Post[i], m.bind))
	}
	return c.norm(st.vars, inst(r.Ret, m.bind))
}

// tryRules applies the first rule that applies to s, if any.
func (c *checker) tryRules(st *state, s *Pat) *Term {
	for i := 0; i < len(c.inp.Rules); i++ {
		t := c.applyRule(st, c.inp.Rules[i], s)
		if c.fail != nil {
			return nil
		}
		if t != nil {
			c.used[i] = true
			return t
		}
	}
	return nil
}

// replaceSpine replaces the node depth steps down the function spine of s
// (s.A, s.A.A, ...) by the value t.
func replaceSpine(s *Pat, depth uint64, t *Term) *Pat {
	if depth == 0 {
		return &Pat{Kind: PVal, T: t}
	}
	return &Pat{Kind: PApp, A: replaceSpine(s.A, depth-1, t), B: s.B}
}

// reduce evaluates s, an application of values (its function position is
// a value or, recursively, such an application). A rule may apply to s
// itself or to any application on its function spine (s.A, s.A.A, ...):
// those are in evaluation position, since every argument is a value. The
// outermost application a rule applies to is rewritten to the rule's
// result, and the search starts again from s, until a rule applies to s.
func (c *checker) reduce(st *state, s0 *Pat) *Term {
	s := s0
	for {
		var depth uint64 = 0
		p := s
		var t *Term = nil
		for p.Kind == PApp && t == nil {
			t = c.tryRules(st, p)
			if c.fail != nil {
				return nil
			}
			if t == nil {
				p = p.A
				depth = depth + 1
			}
		}
		if t == nil {
			c.setFail(&Failure{Code: FailNoRule, Pat: s})
			return nil
		}
		if depth == 0 {
			return t
		}
		s = replaceSpine(s, depth, t)
	}
}

// shallow evaluates the argument of an application, then the function
// position shallowly, in GooseLang's order (argument first).
func (c *checker) shallow(st *state, env []binding, e *Expr) *Pat {
	if e.Kind == EApp {
		arg := c.evalVal(st, env, e.B)
		if arg == nil {
			return nil
		}
		fn := c.shallow(st, env, e.A)
		if fn == nil {
			return nil
		}
		return &Pat{Kind: PApp, A: fn, B: &Pat{Kind: PVal, T: arg}}
	}
	t := c.evalVal(st, env, e)
	if t == nil {
		return nil
	}
	return &Pat{Kind: PVal, T: t}
}

func envLookup(env []binding, x string) *Term {
	for i := len(env); i > 0; i-- {
		if env[i-1].name == x {
			return env[i-1].t
		}
	}
	return nil
}

func (c *checker) evalVal(st *state, env []binding, e *Expr) *Term {
	r := c.eval(st, env, e)
	if r == nil {
		return nil
	}
	if r.kind != resVal {
		c.setFail(&Failure{Code: FailMonad, Expr: e})
		return nil
	}
	return r.t
}

func (c *checker) eval(st *state, env []binding, e *Expr) *result {
	if c.fail != nil {
		return nil
	}
	if e.Kind == EVal {
		return &result{kind: resVal, t: c.norm(st.vars, e.T)}
	}
	if e.Kind == EVar {
		t := envLookup(env, e.Name)
		if t == nil {
			c.setFail(&Failure{Code: FailUnbound, Expr: e})
			return nil
		}
		return &result{kind: resVal, t: t}
	}
	if e.Kind == EApp {
		s := c.shallow(st, env, e)
		if s == nil {
			return nil
		}
		t := c.reduce(st, s)
		if t == nil {
			return nil
		}
		return &result{kind: resVal, t: t}
	}
	if e.Kind == EPair {
		a := c.evalVal(st, env, e.A)
		if a == nil {
			return nil
		}
		b := c.evalVal(st, env, e.B)
		if b == nil {
			return nil
		}
		return &result{kind: resVal, t: c.norm(st.vars, &Term{Kind: TPair, Args: []*Term{a, b}})}
	}
	if e.Kind == ELet {
		v := c.evalVal(st, env, e.A)
		if v == nil {
			return nil
		}
		env2 := append(append([]binding{}, env...), binding{name: e.Name, t: v})
		return c.eval(st, env2, e.B)
	}
	if e.Kind == ESeq {
		if c.evalVal(st, env, e.A) == nil {
			return nil
		}
		return c.eval(st, env, e.B)
	}
	if e.Kind == ELit {
		args := []*Term{e.T}
		for i := 0; i < len(e.Elems); i++ {
			el := e.Elems[i]
			if el.Kind == EVal {
				args = append(args, el.T)
			} else if el.Kind == EVar {
				t := envLookup(env, el.Name)
				if t == nil {
					c.setFail(&Failure{Code: FailUnbound, Expr: el})
					return nil
				}
				args = append(args, t)
			} else {
				c.setFail(&Failure{Code: FailLitElem, Expr: el})
				return nil
			}
		}
		return &result{kind: resVal, t: c.norm(st.vars, &Term{Kind: TLit, Args: args})}
	}
	if e.Kind == EDo {
		if c.evalVal(st, env, e.A) == nil {
			return nil
		}
		return &result{kind: resExec}
	}
	if e.Kind == ERet {
		v := c.evalVal(st, env, e.A)
		if v == nil {
			return nil
		}
		return &result{kind: resRet, t: v}
	}
	if e.Kind == EXSeq {
		r := c.eval(st, env, e.A)
		if r == nil {
			return nil
		}
		if r.kind == resRet {
			return r
		}
		if r.kind != resExec {
			c.setFail(&Failure{Code: FailMonad, Expr: e.A})
			return nil
		}
		return c.eval(st, env, e.B)
	}
	if e.Kind == EXDo {
		r := c.eval(st, env, e.A)
		if r == nil {
			return nil
		}
		if r.kind == resExec {
			return &result{kind: resVal, t: &Term{Kind: TUnit}}
		}
		if r.kind == resRet {
			return &result{kind: resVal, t: r.t}
		}
		c.setFail(&Failure{Code: FailMonad, Expr: e.A})
		return nil
	}
	c.setFail(&Failure{Code: FailUnsupport, Expr: e})
	return nil
}
