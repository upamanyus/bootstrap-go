package checker

// Types and sorts: the (very small) type system of the fragment, and the
// sort discipline on symbolic terms that stands in for it.

// TypeSort returns the sort of the values of a supported Go type. The bool
// result is false for an unsupported type; for a pointer type the sort is
// SortLoc but the element type must itself be supported.
func TypeSort(t *Type) (Sort, bool) {
	if t == nil {
		return SortInt, false
	}
	if t.Kind == TyInt || t.Kind == TyInt64 || t.Kind == TyUint64 {
		return SortInt, true
	}
	if t.Kind == TyBool {
		return SortBool, true
	}
	if t.Kind == TyPtr {
		_, ok := TypeSort(t.Elem)
		return SortLoc, ok
	}
	return SortInt, false
}

// typeSigned reports whether comparisons at this integer type are signed.
func typeSigned(t *Type) bool {
	return t.Kind == TyInt || t.Kind == TyInt64
}

// TypeEq decides structural equality of two types (nil-safe).
func TypeEq(a *Type, b *Type) bool {
	if a == nil {
		return b == nil
	}
	if b == nil {
		return false
	}
	if a.Kind != b.Kind {
		return false
	}
	return TypeEq(a.Elem, b.Elem)
}

// typeZero returns the term for the zero value of a supported type.
func typeZero(t *Type) (*Term, bool) {
	s, ok := TypeSort(t)
	if !ok {
		return nil, false
	}
	if s == SortInt {
		return &Term{Kind: TInt, Num: 0}, true
	}
	if s == SortBool {
		return &Term{Kind: TBool, Num: 0}, true
	}
	if s == SortLoc {
		return &Term{Kind: TNull}, true
	}
	return nil, false
}

// sortEnv assigns sorts to the free symbols a term may contain: logical
// variables (TVar, indexed into vars), postcondition pattern variables (TPat,
// indexed into pats, valid only where patOk is set) and `ret` (TResult, valid
// only when retOk). During symbolic execution only vars is populated; the
// other two are used when sort-checking a postcondition disjunct.
type sortEnv struct {
	vars  []Sort
	pats  []Sort
	patOk []bool
	ret   Sort
	retOk bool
}

// sortOfEnv computes the sort of t, failing if t is ill-sorted or mentions a
// symbol the environment does not describe. TExec and TRet have no sort: the
// exception-monad values are not first-order values of the fragment.
func sortOfEnv(e *sortEnv, t *Term) (Sort, bool) {
	if t == nil {
		return SortInt, false
	}
	if t.Kind == TVar {
		if t.Num >= uint64(len(e.vars)) {
			return SortInt, false
		}
		return e.vars[t.Num], true
	}
	if t.Kind == TPat {
		if t.Num >= uint64(len(e.pats)) {
			return SortInt, false
		}
		if !e.patOk[t.Num] {
			return SortInt, false
		}
		return e.pats[t.Num], true
	}
	if t.Kind == TResult {
		if !e.retOk {
			return SortInt, false
		}
		return e.ret, true
	}
	if t.Kind == TInt {
		return SortInt, true
	}
	if t.Kind == TBool {
		return SortBool, true
	}
	if t.Kind == TUnit {
		return SortUnit, true
	}
	if t.Kind == TNull {
		return SortLoc, true
	}
	if t.Kind == TAdd || t.Kind == TSub || t.Kind == TMul {
		sa, oka := sortOfEnv(e, t.A)
		sb, okb := sortOfEnv(e, t.B)
		if oka && okb && sa == SortInt && sb == SortInt {
			return SortInt, true
		}
		return SortInt, false
	}
	if t.Kind == TNeg {
		sa, oka := sortOfEnv(e, t.A)
		if oka && sa == SortInt {
			return SortInt, true
		}
		return SortInt, false
	}
	if t.Kind == TEq {
		sa, oka := sortOfEnv(e, t.A)
		sb, okb := sortOfEnv(e, t.B)
		if oka && okb && sa == sb {
			return SortBool, true
		}
		return SortInt, false
	}
	if t.Kind == TLtS || t.Kind == TLtU || t.Kind == TLeS || t.Kind == TLeU {
		sa, oka := sortOfEnv(e, t.A)
		sb, okb := sortOfEnv(e, t.B)
		if oka && okb && sa == SortInt && sb == SortInt {
			return SortBool, true
		}
		return SortInt, false
	}
	if t.Kind == TNot {
		sa, oka := sortOfEnv(e, t.A)
		if oka && sa == SortBool {
			return SortBool, true
		}
		return SortInt, false
	}
	if t.Kind == TIte {
		sc, okc := sortOfEnv(e, t.A)
		sa, oka := sortOfEnv(e, t.B)
		sb, okb := sortOfEnv(e, t.C)
		if okc && oka && okb && sc == SortBool && sa == sb {
			return sa, true
		}
		return SortInt, false
	}
	return SortInt, false
}

// SortOf computes the sort of a term over the logical variables vars. Terms
// containing pattern variables, `ret`, or exception-monad values have no sort.
func SortOf(vars []Sort, t *Term) (Sort, bool) {
	e := &sortEnv{vars: vars}
	return sortOfEnv(e, t)
}

// TermEq decides structural equality of two terms (nil-safe).
func TermEq(a *Term, b *Term) bool {
	return termEq(a, b)
}

// copySorts returns a fresh copy of ss, so that appending to the copy (as
// allocation does) cannot be observed through the original.
func copySorts(ss []Sort) []Sort {
	out := make([]Sort, len(ss))
	copy(out, ss)
	return out
}
