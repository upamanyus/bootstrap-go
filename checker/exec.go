package checker

// Symbolic execution of the supported GooseLang fragment.
//
// exec turns an expression into the list of its feasible execution paths. A
// path is a return-value term plus a final symbolic state. Forking (at `if`
// on a non-literal condition) duplicates the state, and every state that is
// modified is cloned first, so that no two paths ever share a mutable slice.

// env is the (immutable) variable environment: a linked list from names to
// symbolic terms, with the most recent binding first. A linked list rather
// than a map, both because maps are unordered and because the model of a map
// in Perennial is much heavier than the model of a linked list.
type env struct {
	name string
	term *Term
	next *env
}

func envLookup(e *env, x string) (*Term, bool) {
	if e == nil {
		return nil, false
	}
	if e.name == x {
		return e.term, true
	}
	return envLookup(e.next, x)
}

func envBind(e *env, x string, t *Term) *env {
	return &env{name: x, term: t, next: e}
}

// onePath is the singleton path list: an expression that neither forks nor
// touches the heap.
func onePath(v *Term, st *State) []Path {
	var out []Path
	return append(out, Path{Ret: v, St: st})
}

// heapLookup finds the value stored at location term l. Locations are
// compared syntactically: two terms denote the same cell only if they are
// structurally equal.
func heapLookup(h []Cell, l *Term) (*Term, bool) {
	for _, c := range h {
		if termEq(c.Loc, l) {
			return c.Val, true
		}
	}
	return nil, false
}

// heapUpdate returns a fresh heap in which the (first) cell at location l
// holds v. It fails if no cell is at l: the checker only permits stores to
// locations it owns.
func heapUpdate(h []Cell, l *Term, v *Term) ([]Cell, bool) {
	var out []Cell
	found := false
	for _, c := range h {
		if !found && termEq(c.Loc, l) {
			out = append(out, Cell{Loc: c.Loc, Val: v})
			found = true
		} else {
			out = append(out, c)
		}
	}
	if !found {
		return nil, false
	}
	return out, true
}

// negate builds the negation of a boolean term, cancelling a double
// negation so that the path condition of an `else` branch after `if !b` is
// just `b`.
func negate(t *Term) *Term {
	if t.Kind == TNot {
		return t.A
	}
	return &Term{Kind: TNot, A: t}
}

// exec symbolically executes e in environment en and state st. It returns one
// Path per feasible execution path, in evaluation order (for `if`, the `then`
// paths precede the `else` paths), or a Failure if some path could not be
// shown safe.
func exec(e *Expr, en *env, st *State) ([]Path, *Failure) {
	if e == nil {
		return nil, &Failure{Reason: RUnsupported}
	}
	switch e.Kind {
	case EInt:
		return onePath(&Term{Kind: TInt, Num: e.Num}, st), nil
	case EBool:
		return onePath(&Term{Kind: TBool, Num: e.Num}, st), nil
	case EUnit:
		return onePath(&Term{Kind: TUnit}, st), nil
	case EVar:
		t, ok := envLookup(en, e.Name)
		if !ok {
			return nil, &Failure{Reason: RUnboundVar, Name: e.Name, Expr: e}
		}
		return onePath(t, st), nil
	case ELet:
		ps, fl := exec(e.A, en, st)
		if fl != nil {
			return nil, fl
		}
		var out []Path
		for _, p := range ps {
			// The name is always bound, even when it is empty: Goose emits
			// `let: Name := A in B`, which binds Name whatever it is, and
			// the checker has to agree with that denotation exactly. (A
			// real Go declaration never has an empty name anyway.)
			en2 := envBind(en, e.Name, p.Ret)
			ps2, fl2 := exec(e.B, en2, p.St)
			if fl2 != nil {
				return nil, fl2
			}
			out = append(out, ps2...)
		}
		return out, nil
	case ESeq:
		ps, fl := exec(e.A, en, st)
		if fl != nil {
			return nil, fl
		}
		var out []Path
		for _, p := range ps {
			ps2, fl2 := exec(e.B, en, p.St)
			if fl2 != nil {
				return nil, fl2
			}
			out = append(out, ps2...)
		}
		return out, nil
	case EIf:
		ps, fl := exec(e.A, en, st)
		if fl != nil {
			return nil, fl
		}
		var out []Path
		for _, p := range ps {
			ps2, fl2 := execIf(e, en, p.Ret, p.St)
			if fl2 != nil {
				return nil, fl2
			}
			out = append(out, ps2...)
		}
		return out, nil
	case ELoad:
		_, tok := TypeSort(e.Ty)
		if !tok {
			return nil, &Failure{Reason: RBadType, Expr: e}
		}
		ps, fl := exec(e.A, en, st)
		if fl != nil {
			return nil, fl
		}
		var out []Path
		for _, p := range ps {
			v, ok := heapLookup(p.St.Heap, p.Ret)
			if !ok {
				return nil, &Failure{Reason: RNoPointsTo, Expr: e, Got: p.Ret}
			}
			out = append(out, Path{Ret: v, St: p.St})
		}
		return out, nil
	case EStore:
		_, tok := TypeSort(e.Ty)
		if !tok {
			return nil, &Failure{Reason: RBadType, Expr: e}
		}
		ps, fl := exec(e.A, en, st)
		if fl != nil {
			return nil, fl
		}
		var out []Path
		for _, p := range ps {
			ps2, fl2 := exec(e.B, en, p.St)
			if fl2 != nil {
				return nil, fl2
			}
			for _, q := range ps2 {
				st2 := q.St.clone()
				h, ok := heapUpdate(st2.Heap, p.Ret, q.Ret)
				if !ok {
					return nil, &Failure{Reason: RNoPointsTo, Expr: e, Got: p.Ret}
				}
				st2.Heap = h
				out = append(out, Path{Ret: &Term{Kind: TUnit}, St: st2})
			}
		}
		return out, nil
	case EAlloc:
		_, tok := TypeSort(e.Ty)
		if !tok {
			return nil, &Failure{Reason: RBadType, Expr: e}
		}
		ps, fl := exec(e.A, en, st)
		if fl != nil {
			return nil, fl
		}
		var out []Path
		for _, p := range ps {
			st2 := p.St.clone()
			n := uint64(len(st2.Vars))
			st2.Vars = append(st2.Vars, SortLoc)
			l := &Term{Kind: TVar, Num: n}
			st2.Heap = append(st2.Heap, Cell{Loc: l, Val: p.Ret})
			out = append(out, Path{Ret: l, St: st2})
		}
		return out, nil
	case EZero:
		z, ok := typeZero(e.Ty)
		if !ok {
			return nil, &Failure{Reason: RBadType, Expr: e}
		}
		return onePath(z, st), nil
	case EBinOp:
		_, tok := TypeSort(e.Ty)
		if !tok {
			return nil, &Failure{Reason: RBadType, Expr: e}
		}
		ps, fl := exec(e.A, en, st)
		if fl != nil {
			return nil, fl
		}
		var out []Path
		for _, p := range ps {
			ps2, fl2 := exec(e.B, en, p.St)
			if fl2 != nil {
				return nil, fl2
			}
			for _, q := range ps2 {
				v, ok := applyBinOp(e.Op, e.Ty, q.St.Vars, p.Ret, q.Ret)
				if !ok {
					return nil, &Failure{Reason: RIllSorted, Expr: e, Want: p.Ret, Got: q.Ret}
				}
				out = append(out, Path{Ret: v, St: q.St})
			}
		}
		return out, nil
	case EUnOp:
		_, tok := TypeSort(e.Ty)
		if !tok {
			return nil, &Failure{Reason: RBadType, Expr: e}
		}
		ps, fl := exec(e.A, en, st)
		if fl != nil {
			return nil, fl
		}
		var out []Path
		for _, p := range ps {
			v, ok := applyUnOp(e.Op, e.Ty, p.St.Vars, p.Ret)
			if !ok {
				return nil, &Failure{Reason: RIllSorted, Expr: e, Got: p.Ret}
			}
			out = append(out, Path{Ret: v, St: p.St})
		}
		return out, nil
	case EConvert:
		_, tok := TypeSort(e.Ty)
		if !tok {
			return nil, &Failure{Reason: RBadType, Expr: e}
		}
		if !TypeEq(e.Ty, e.Ty2) {
			return nil, &Failure{Reason: RBadConvert, Expr: e}
		}
		return exec(e.A, en, st)
	case EDo:
		ps, fl := exec(e.A, en, st)
		if fl != nil {
			return nil, fl
		}
		var out []Path
		for _, p := range ps {
			out = append(out, Path{Ret: &Term{Kind: TExec}, St: p.St})
		}
		return out, nil
	case EReturn:
		ps, fl := exec(e.A, en, st)
		if fl != nil {
			return nil, fl
		}
		var out []Path
		for _, p := range ps {
			out = append(out, Path{Ret: &Term{Kind: TRet, A: p.Ret}, St: p.St})
		}
		return out, nil
	case EExcSeq:
		ps, fl := exec(e.A, en, st)
		if fl != nil {
			return nil, fl
		}
		var out []Path
		for _, p := range ps {
			if p.Ret == nil {
				return nil, &Failure{Reason: RBadMonad, Expr: e}
			}
			if p.Ret.Kind == TExec {
				ps2, fl2 := exec(e.B, en, p.St)
				if fl2 != nil {
					return nil, fl2
				}
				out = append(out, ps2...)
			} else if p.Ret.Kind == TRet {
				out = append(out, p)
			} else {
				return nil, &Failure{Reason: RBadMonad, Expr: e, Got: p.Ret}
			}
		}
		return out, nil
	case EExcDo:
		ps, fl := exec(e.A, en, st)
		if fl != nil {
			return nil, fl
		}
		var out []Path
		for _, p := range ps {
			if p.Ret == nil {
				return nil, &Failure{Reason: RBadMonad, Expr: e}
			}
			if p.Ret.Kind == TExec {
				out = append(out, Path{Ret: &Term{Kind: TUnit}, St: p.St})
			} else if p.Ret.Kind == TRet {
				out = append(out, Path{Ret: p.Ret.A, St: p.St})
			} else {
				return nil, &Failure{Reason: RBadMonad, Expr: e, Got: p.Ret}
			}
		}
		return out, nil
	}
	return nil, &Failure{Reason: RUnsupported, Expr: e}
}

// execIf runs one path of an `if`: c is the condition term reached on that
// path and st its state. A literal condition takes the corresponding branch
// without forking; otherwise the state forks, with c added to the path
// condition of the `then` state and its negation to that of the `else` state.
func execIf(e *Expr, en *env, c *Term, st *State) ([]Path, *Failure) {
	s, ok := SortOf(st.Vars, c)
	if !ok || s != SortBool {
		return nil, &Failure{Reason: RIllSorted, Expr: e, Got: c}
	}
	if c.Kind == TBool {
		if c.Num == 1 {
			return exec(e.B, en, st)
		}
		return exec(e.C, en, st)
	}
	st1 := st.clone()
	st1.Cond = append(st1.Cond, c)
	ps1, fl1 := exec(e.B, en, st1)
	if fl1 != nil {
		return nil, fl1
	}
	st2 := st.clone()
	st2.Cond = append(st2.Cond, negate(c))
	ps2, fl2 := exec(e.C, en, st2)
	if fl2 != nil {
		return nil, fl2
	}
	var out []Path
	out = append(out, ps1...)
	out = append(out, ps2...)
	return out, nil
}

// applyBinOp builds the term for a binary Go operator at type t, checking
// that both operands have the sort of t.
func applyBinOp(op Op, t *Type, vars []Sort, a *Term, b *Term) (*Term, bool) {
	ts, tok := TypeSort(t)
	if !tok {
		return nil, false
	}
	sa, oka := SortOf(vars, a)
	sb, okb := SortOf(vars, b)
	if !oka || !okb || sa != ts || sb != ts {
		return nil, false
	}
	if op == OpEq {
		if ts == SortUnit {
			return nil, false
		}
		return &Term{Kind: TEq, A: a, B: b}, true
	}
	if ts != SortInt {
		return nil, false
	}
	signed := typeSigned(t)
	if op == OpAdd {
		return &Term{Kind: TAdd, A: a, B: b}, true
	}
	if op == OpSub {
		return &Term{Kind: TSub, A: a, B: b}, true
	}
	if op == OpMul {
		return &Term{Kind: TMul, A: a, B: b}, true
	}
	if op == OpLt {
		if signed {
			return &Term{Kind: TLtS, A: a, B: b}, true
		}
		return &Term{Kind: TLtU, A: a, B: b}, true
	}
	if op == OpLe {
		if signed {
			return &Term{Kind: TLeS, A: a, B: b}, true
		}
		return &Term{Kind: TLeU, A: a, B: b}, true
	}
	if op == OpGt {
		if signed {
			return &Term{Kind: TLtS, A: b, B: a}, true
		}
		return &Term{Kind: TLtU, A: b, B: a}, true
	}
	if op == OpGe {
		if signed {
			return &Term{Kind: TLeS, A: b, B: a}, true
		}
		return &Term{Kind: TLeU, A: b, B: a}, true
	}
	return nil, false
}

// applyUnOp builds the term for a unary Go operator at type t.
func applyUnOp(op Op, t *Type, vars []Sort, a *Term) (*Term, bool) {
	ts, tok := TypeSort(t)
	if !tok {
		return nil, false
	}
	sa, oka := SortOf(vars, a)
	if !oka || sa != ts {
		return nil, false
	}
	// Unary minus only exists at the signed integer types: GooseLang has no
	// GoUnOp GoNeg for uint/uint64 (see new/golang/defn/predeclared.v), so
	// -x on an unsigned type is stuck and must not be accepted as safe.
	if op == OpNeg && ts == SortInt && typeSigned(t) {
		return &Term{Kind: TNeg, A: a}, true
	}
	if op == OpNot && ts == SortBool {
		return &Term{Kind: TNot, A: a}, true
	}
	return nil, false
}
