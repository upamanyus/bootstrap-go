package checker

import "testing"

// --- small constructors for building test inputs ----------------------------

func tyInt() *Type    { return &Type{Kind: TyInt} }
func tyUint64() *Type { return &Type{Kind: TyUint64} }
func tyBool() *Type   { return &Type{Kind: TyBool} }
func tyPtr(t *Type) *Type {
	return &Type{Kind: TyPtr, Elem: t}
}

func eInt(n uint64) *Expr { return &Expr{Kind: EInt, Num: n} }
func eBool(b bool) *Expr {
	if b {
		return &Expr{Kind: EBool, Num: 1}
	}
	return &Expr{Kind: EBool, Num: 0}
}
func eUnit() *Expr        { return &Expr{Kind: EUnit} }
func eVar(x string) *Expr { return &Expr{Kind: EVar, Name: x} }
func eLet(x string, a, b *Expr) *Expr {
	return &Expr{Kind: ELet, Name: x, A: a, B: b}
}
func eSeq(a, b *Expr) *Expr        { return &Expr{Kind: ESeq, A: a, B: b} }
func eIf(a, b, c *Expr) *Expr      { return &Expr{Kind: EIf, A: a, B: b, C: c} }
func eLoad(t *Type, a *Expr) *Expr { return &Expr{Kind: ELoad, Ty: t, A: a} }
func eStore(t *Type, a, b *Expr) *Expr {
	return &Expr{Kind: EStore, Ty: t, A: a, B: b}
}
func eAlloc(t *Type, a *Expr) *Expr { return &Expr{Kind: EAlloc, Ty: t, A: a} }
func eZero(t *Type) *Expr           { return &Expr{Kind: EZero, Ty: t} }
func eBin(op Op, t *Type, a, b *Expr) *Expr {
	return &Expr{Kind: EBinOp, Op: op, Ty: t, A: a, B: b}
}
func eUn(op Op, t *Type, a *Expr) *Expr {
	return &Expr{Kind: EUnOp, Op: op, Ty: t, A: a}
}
func eConv(from, to *Type, a *Expr) *Expr {
	return &Expr{Kind: EConvert, Ty: from, Ty2: to, A: a}
}
func eDo(a *Expr) *Expr        { return &Expr{Kind: EDo, A: a} }
func eRet(a *Expr) *Expr       { return &Expr{Kind: EReturn, A: a} }
func eExcSeq(a, b *Expr) *Expr { return &Expr{Kind: EExcSeq, A: a, B: b} }
func eExcDo(a *Expr) *Expr     { return &Expr{Kind: EExcDo, A: a} }

func tVar(n uint64) *Term { return &Term{Kind: TVar, Num: n} }
func tPat(n uint64) *Term { return &Term{Kind: TPat, Num: n} }
func tRes() *Term         { return &Term{Kind: TResult} }
func tInt(n uint64) *Term { return &Term{Kind: TInt, Num: n} }
func tBool(b bool) *Term {
	if b {
		return &Term{Kind: TBool, Num: 1}
	}
	return &Term{Kind: TBool, Num: 0}
}
func tUnit() *Term          { return &Term{Kind: TUnit} }
func tAdd(a, b *Term) *Term { return &Term{Kind: TAdd, A: a, B: b} }
func tEq(a, b *Term) *Term  { return &Term{Kind: TEq, A: a, B: b} }
func tLtS(a, b *Term) *Term { return &Term{Kind: TLtS, A: a, B: b} }
func tLtU(a, b *Term) *Term { return &Term{Kind: TLtU, A: a, B: b} }
func tNeg(a *Term) *Term    { return &Term{Kind: TNeg, A: a} }
func tNot(a *Term) *Term    { return &Term{Kind: TNot, A: a} }

func aEmp() *Assn           { return &Assn{Kind: AEmp} }
func aSep(l, r *Assn) *Assn { return &Assn{Kind: ASep, L: l, R: r} }
func aOr(l, r *Assn) *Assn  { return &Assn{Kind: AOr, L: l, R: r} }
func aPure(x *Term) *Assn   { return &Assn{Kind: APure, X: x} }
func aPt(x, y *Term) *Assn  { return &Assn{Kind: APointsTo, X: x, Y: y} }
func aEx(v uint64, s Sort, l *Assn) *Assn {
	return &Assn{Kind: AExists, Var: v, Sort: s, L: l}
}

func sorts(ss ...Sort) []Sort { return ss }

// sepAll builds a right-nested separating conjunction.
func sepAll(as ...*Assn) *Assn {
	if len(as) == 0 {
		return aEmp()
	}
	out := as[len(as)-1]
	for i := len(as) - 2; i >= 0; i-- {
		out = aSep(as[i], out)
	}
	return out
}

// --- assertions on results ---------------------------------------------------

func heapGet(h []Cell, l *Term) *Term {
	v, ok := heapLookup(h, l)
	if !ok {
		return nil
	}
	return v
}

func condIs(cond []*Term, want ...*Term) bool {
	if len(cond) != len(want) {
		return false
	}
	for i, c := range cond {
		if !TermEq(c, want[i]) {
			return false
		}
	}
	return true
}

func mustAnalyze(t *testing.T, f *Func, vars []Sort, pre *Assn) []Path {
	t.Helper()
	paths, fail := Analyze(f, vars, pre)
	if fail != nil {
		t.Fatalf("Analyze failed with reason %d", fail.Reason)
	}
	return paths
}

// --- the example programs, transcribed from Goose output --------------------

// func Double(x int, z *int) { y := x; if x == 0 { y = 37 }; *z = y + y }
func doubleFn() *Func {
	return &Func{Params: []string{"x", "z"}, Body: eExcDo(
		eLet("z", eAlloc(tyPtr(tyInt()), eVar("z")),
			eLet("x", eAlloc(tyInt(), eVar("x")),
				eLet("y", eAlloc(tyInt(), eZero(tyInt())),
					eLet("$r0", eLoad(tyInt(), eVar("x")),
						eExcSeq(eDo(eStore(tyInt(), eVar("y"), eVar("$r0"))),
							eExcSeq(
								eIf(eConv(tyBool(), tyBool(), eBin(OpEq, tyInt(), eLoad(tyInt(), eVar("x")), eInt(0))),
									eLet("$r0", eInt(37), eDo(eStore(tyInt(), eVar("y"), eVar("$r0")))),
									eDo(eUnit())),
								eLet("$r0", eBin(OpAdd, tyInt(), eLoad(tyInt(), eVar("y")), eLoad(tyInt(), eVar("y"))),
									eExcSeq(eDo(eStore(tyInt(), eLoad(tyPtr(tyInt()), eVar("z")), eVar("$r0"))),
										eRet(eUnit())))))))))),
	}
}

// func Max(a, b uint64) uint64 { if a < b { return b }; return a }
func maxFn() *Func {
	return &Func{Params: []string{"a", "b"}, Body: eExcDo(
		eLet("b", eAlloc(tyUint64(), eVar("b")),
			eLet("a", eAlloc(tyUint64(), eVar("a")),
				eExcSeq(
					eIf(eConv(tyBool(), tyBool(), eBin(OpLt, tyUint64(), eLoad(tyUint64(), eVar("a")), eLoad(tyUint64(), eVar("b")))),
						eRet(eLoad(tyUint64(), eVar("b"))),
						eDo(eUnit())),
					eRet(eLoad(tyUint64(), eVar("a"))))))),
	}
}

// func Swap(p, q *uint64) { tmp := *p; *p = *q; *q = tmp }
func swapFn() *Func {
	pu := tyPtr(tyUint64())
	return &Func{Params: []string{"p", "q"}, Body: eExcDo(
		eLet("q", eAlloc(pu, eVar("q")),
			eLet("p", eAlloc(pu, eVar("p")),
				eLet("tmp", eAlloc(tyUint64(), eZero(tyUint64())),
					eLet("$r0", eLoad(tyUint64(), eLoad(pu, eVar("p"))),
						eExcSeq(eDo(eStore(tyUint64(), eVar("tmp"), eVar("$r0"))),
							eLet("$r0", eLoad(tyUint64(), eLoad(pu, eVar("q"))),
								eExcSeq(eDo(eStore(tyUint64(), eLoad(pu, eVar("p")), eVar("$r0"))),
									eLet("$r0", eLoad(tyUint64(), eVar("tmp")),
										eExcSeq(eDo(eStore(tyUint64(), eLoad(pu, eVar("q")), eVar("$r0"))),
											eRet(eUnit()))))))))))),
	}
}

// func Abs(x int) int { if x < 0 { return -x }; return x }
func absFn() *Func {
	return &Func{Params: []string{"x"}, Body: eExcDo(
		eLet("x", eAlloc(tyInt(), eVar("x")),
			eExcSeq(
				eIf(eConv(tyBool(), tyBool(), eBin(OpLt, tyInt(), eLoad(tyInt(), eVar("x")), eInt(0))),
					eRet(eUn(OpNeg, tyInt(), eLoad(tyInt(), eVar("x")))),
					eDo(eUnit())),
				eRet(eLoad(tyInt(), eVar("x")))))),
	}
}

//	func CondStore(flag bool, p *uint64, v uint64) bool {
//		if !flag { return false }; *p = v; return true
//	}
func condStoreFn() *Func {
	pu := tyPtr(tyUint64())
	return &Func{Params: []string{"flag", "p", "v"}, Body: eExcDo(
		eLet("v", eAlloc(tyUint64(), eVar("v")),
			eLet("p", eAlloc(pu, eVar("p")),
				eLet("flag", eAlloc(tyBool(), eVar("flag")),
					eExcSeq(
						eIf(eUn(OpNot, tyBool(), eLoad(tyBool(), eVar("flag"))),
							eRet(eBool(false)),
							eDo(eUnit())),
						eLet("$r0", eLoad(tyUint64(), eVar("v")),
							eExcSeq(eDo(eStore(tyUint64(), eLoad(pu, eVar("p")), eVar("$r0"))),
								eRet(eBool(true))))))))),
	}
}

// --- symbolic execution ------------------------------------------------------

func TestDouble(t *testing.T) {
	// vars: 0 = x:int, 1 = z:*int, 2 = the old value of *z
	vars := sorts(SortInt, SortLoc, SortInt)
	pre := aPt(tVar(1), tVar(2))
	paths := mustAnalyze(t, doubleFn(), vars, pre)
	if len(paths) != 2 {
		t.Fatalf("expected 2 paths, got %d", len(paths))
	}

	// path 1: x == 0, so *z = 37 + 37
	p0 := paths[0]
	if !TermEq(heapGet(p0.St.Heap, tVar(1)), tAdd(tInt(37), tInt(37))) {
		t.Fatal("path 1: wrong value for *z")
	}
	if !condIs(p0.St.Cond, tEq(tVar(0), tInt(0))) {
		t.Fatal("path 1: wrong path condition")
	}

	// path 2: !(x == 0), so *z = x + x
	p1 := paths[1]
	if !TermEq(heapGet(p1.St.Heap, tVar(1)), tAdd(tVar(0), tVar(0))) {
		t.Fatal("path 2: wrong value for *z")
	}
	if !condIs(p1.St.Cond, tNot(tEq(tVar(0), tInt(0)))) {
		t.Fatal("path 2: wrong path condition")
	}

	if !TermEq(p0.Ret, tUnit()) || !TermEq(p1.Ret, tUnit()) {
		t.Fatal("expected unit return on both paths")
	}

	// Without ownership of *z the store is unsafe.
	_, fail := Analyze(doubleFn(), vars, aEmp())
	if fail == nil || fail.Reason != RNoPointsTo {
		t.Fatal("Double should not be safe without ownership of *z")
	}
}

func TestMax(t *testing.T) {
	vars := sorts(SortInt, SortInt)
	paths := mustAnalyze(t, maxFn(), vars, aEmp())
	if len(paths) != 2 {
		t.Fatalf("expected 2 paths, got %d", len(paths))
	}
	if !TermEq(paths[0].Ret, tVar(1)) || !TermEq(paths[1].Ret, tVar(0)) {
		t.Fatal("wrong return values")
	}
	// uint64 comparison must be unsigned
	if !condIs(paths[0].St.Cond, tLtU(tVar(0), tVar(1))) {
		t.Fatal("path 1: expected an unsigned <")
	}
	if !condIs(paths[1].St.Cond, tNot(tLtU(tVar(0), tVar(1)))) {
		t.Fatal("path 2: wrong path condition")
	}
}

func TestSwap(t *testing.T) {
	// vars: 0 = p, 1 = q, 2 = *p, 3 = *q
	vars := sorts(SortLoc, SortLoc, SortInt, SortInt)
	pre := aSep(aPt(tVar(0), tVar(2)), aPt(tVar(1), tVar(3)))
	paths := mustAnalyze(t, swapFn(), vars, pre)
	if len(paths) != 1 {
		t.Fatalf("expected 1 path, got %d", len(paths))
	}
	h := paths[0].St.Heap
	if !TermEq(heapGet(h, tVar(0)), tVar(3)) || !TermEq(heapGet(h, tVar(1)), tVar(2)) {
		t.Fatal("Swap did not swap")
	}
	// Only one pointer owned: the other store is unsafe.
	_, fail := Analyze(swapFn(), vars, aPt(tVar(0), tVar(2)))
	if fail == nil || fail.Reason != RNoPointsTo {
		t.Fatal("Swap should be unsafe with only *p owned")
	}
}

func TestAbs(t *testing.T) {
	vars := sorts(SortInt)
	paths := mustAnalyze(t, absFn(), vars, aEmp())
	if len(paths) != 2 {
		t.Fatalf("expected 2 paths, got %d", len(paths))
	}
	if !TermEq(paths[0].Ret, tNeg(tVar(0))) || !TermEq(paths[1].Ret, tVar(0)) {
		t.Fatal("wrong return values")
	}
	// int comparison must be signed
	if !condIs(paths[0].St.Cond, tLtS(tVar(0), tInt(0))) {
		t.Fatal("path 1: expected a signed <")
	}
}

func TestCondStore(t *testing.T) {
	// vars: 0 = flag, 1 = p, 2 = v, 3 = the old value of *p
	vars := sorts(SortBool, SortLoc, SortInt, SortInt)
	pre := aPt(tVar(1), tVar(3))
	paths := mustAnalyze(t, condStoreFn(), vars, pre)
	if len(paths) != 2 {
		t.Fatalf("expected 2 paths, got %d", len(paths))
	}
	// path 1: !flag, returns false, *p unchanged
	if !TermEq(paths[0].Ret, tBool(false)) {
		t.Fatal("path 1: expected false")
	}
	if !TermEq(heapGet(paths[0].St.Heap, tVar(1)), tVar(3)) {
		t.Fatal("path 1: *p should be unchanged")
	}
	if !condIs(paths[0].St.Cond, tNot(tVar(0))) {
		t.Fatal("path 1: wrong path condition")
	}
	// path 2: flag, with the double negation cancelled
	if !TermEq(paths[1].Ret, tBool(true)) {
		t.Fatal("path 2: expected true")
	}
	if !TermEq(heapGet(paths[1].St.Heap, tVar(1)), tVar(2)) {
		t.Fatal("path 2: *p should be v")
	}
	if !condIs(paths[1].St.Cond, tVar(0)) {
		t.Fatal("path 2: expected the double negation to cancel")
	}
}

func TestIllSorted(t *testing.T) {
	// `if` on an integer
	f := &Func{Params: []string{"x"}, Body: eIf(eVar("x"), eUnit(), eUnit())}
	_, fail := Analyze(f, sorts(SortInt), aEmp())
	if fail == nil || fail.Reason != RIllSorted {
		t.Fatal("if on an int should be rejected")
	}
	// int + bool
	f2 := &Func{Params: []string{"x"},
		Body: eBin(OpAdd, tyInt(), eVar("x"), eBool(true))}
	_, fail = Analyze(f2, sorts(SortInt), aEmp())
	if fail == nil || fail.Reason != RIllSorted {
		t.Fatal("int + bool should be rejected")
	}
	// == at unit
	f3 := &Func{Params: nil, Body: eBin(OpEq, tyInt(), eUnit(), eUnit())}
	_, fail = Analyze(f3, sorts(), aEmp())
	if fail == nil || fail.Reason != RIllSorted {
		t.Fatal("unit == unit should be rejected")
	}
	// !x on an int
	f4 := &Func{Params: []string{"x"}, Body: eUn(OpNot, tyBool(), eVar("x"))}
	_, fail = Analyze(f4, sorts(SortInt), aEmp())
	if fail == nil || fail.Reason != RIllSorted {
		t.Fatal("!int should be rejected")
	}
	// ill-sorted precondition
	_, fail = Analyze(&Func{Body: eUnit()}, sorts(SortInt), aPt(tVar(0), tInt(0)))
	if fail == nil || fail.Reason != RIllSorted {
		t.Fatal("a points-to at a non-location should be rejected")
	}
	_, fail = Analyze(&Func{Body: eUnit()}, sorts(SortInt), aPure(tVar(0)))
	if fail == nil || fail.Reason != RIllSorted {
		t.Fatal("a pure atom at a non-boolean should be rejected")
	}
}

func TestStoreThroughNil(t *testing.T) {
	f := &Func{Params: []string{"x"},
		Body: eStore(tyInt(), eZero(tyPtr(tyInt())), eVar("x"))}
	_, fail := Analyze(f, sorts(SortInt), aEmp())
	if fail == nil || fail.Reason != RNoPointsTo {
		t.Fatal("store through nil should be rejected")
	}
	f2 := &Func{Params: nil, Body: eLoad(tyInt(), eZero(tyPtr(tyInt())))}
	_, fail = Analyze(f2, sorts(), aEmp())
	if fail == nil || fail.Reason != RNoPointsTo {
		t.Fatal("load through nil should be rejected")
	}
}

func TestInputValidation(t *testing.T) {
	f := &Func{Params: []string{"x", "y"}, Body: eUnit()}
	_, fail := Analyze(f, sorts(SortInt), aEmp())
	if fail == nil || fail.Reason != RVarsTooShort {
		t.Fatal("expected RVarsTooShort")
	}
	g := &Func{Params: nil, Body: eUnit()}
	_, fail = Analyze(g, sorts(), aOr(aEmp(), aEmp()))
	if fail == nil || fail.Reason != RPreHasOr {
		t.Fatal("expected RPreHasOr")
	}
	_, fail = Analyze(g, sorts(), aEx(0, SortInt, aEmp()))
	if fail == nil || fail.Reason != RPreHasExists {
		t.Fatal("expected RPreHasExists")
	}
	h := &Func{Params: []string{"x"}, Body: eVar("y")}
	_, fail = Analyze(h, sorts(SortInt), aEmp())
	if fail == nil || fail.Reason != RUnboundVar || fail.Name != "y" {
		t.Fatal("expected RUnboundVar for y")
	}
	// a repeated parameter name: the later one wins
	dup := &Func{Params: []string{"x", "x"}, Body: eVar("x")}
	paths := mustAnalyze(t, dup, sorts(SortInt, SortInt), aEmp())
	if !TermEq(paths[0].Ret, tVar(1)) {
		t.Fatal("the later parameter should shadow the earlier one")
	}
}

func TestConvertAndMonad(t *testing.T) {
	// a non-identity conversion
	f := &Func{Params: []string{"x"}, Body: eConv(tyInt(), tyBool(), eVar("x"))}
	_, fail := Analyze(f, sorts(SortInt), aEmp())
	if fail == nil || fail.Reason != RBadConvert {
		t.Fatal("expected RBadConvert")
	}
	// an identity conversion is transparent
	g := &Func{Params: []string{"x"}, Body: eConv(tyInt(), tyInt(), eVar("x"))}
	paths := mustAnalyze(t, g, sorts(SortInt), aEmp())
	if !TermEq(paths[0].Ret, tVar(0)) {
		t.Fatal("an identity conversion should be transparent")
	}
	// exception_do on a plain value
	h := &Func{Params: nil, Body: eExcDo(eInt(3))}
	_, fail = Analyze(h, sorts(), aEmp())
	if fail == nil || fail.Reason != RBadMonad {
		t.Fatal("expected RBadMonad for exception_do")
	}
	// ;;; on a plain value
	k := &Func{Params: nil, Body: eExcSeq(eInt(3), eDo(eUnit()))}
	_, fail = Analyze(k, sorts(), aEmp())
	if fail == nil || fail.Reason != RBadMonad {
		t.Fatal("expected RBadMonad for ;;;")
	}
	// a literal condition does not fork
	lit := &Func{Params: nil, Body: eIf(eBool(true), eInt(1), eInt(2))}
	paths = mustAnalyze(t, lit, sorts(), aEmp())
	if len(paths) != 1 || !TermEq(paths[0].Ret, tInt(1)) || len(paths[0].St.Cond) != 0 {
		t.Fatal("a literal condition should not fork")
	}
	lit2 := &Func{Params: nil, Body: eIf(eBool(false), eInt(1), eInt(2))}
	paths = mustAnalyze(t, lit2, sorts(), aEmp())
	if len(paths) != 1 || !TermEq(paths[0].Ret, tInt(2)) {
		t.Fatal("a literal false condition should take the else branch")
	}
}

// TestForkNoAliasing is a regression test for state sharing between paths.
// Each of the four paths stores a different value through p and allocates a
// different value; if the forked states shared their heap, path-condition or
// variable slices, the paths would see one another's updates.
func TestForkNoAliasing(t *testing.T) {
	inner := func(a, b uint64) *Expr {
		return eIf(eVar("c"),
			eSeq(eStore(tyInt(), eVar("p"), eInt(a)), eAlloc(tyInt(), eInt(a*10))),
			eSeq(eStore(tyInt(), eVar("p"), eInt(b)), eAlloc(tyInt(), eInt(b*10))))
	}
	body := eIf(eVar("b"),
		eSeq(eStore(tyInt(), eVar("p"), eInt(1)), inner(2, 3)),
		eSeq(eStore(tyInt(), eVar("p"), eInt(4)), inner(5, 6)))
	f := &Func{Params: []string{"b", "c", "p"}, Body: body}
	// vars: 0 = b, 1 = c, 2 = p, 3 = the old value of *p
	vars := sorts(SortBool, SortBool, SortLoc, SortInt)
	paths := mustAnalyze(t, f, vars, aPt(tVar(2), tVar(3)))
	if len(paths) != 4 {
		t.Fatalf("expected 4 paths, got %d", len(paths))
	}
	stored := []uint64{2, 3, 5, 6}
	conds := [][]*Term{
		{tVar(0), tVar(1)},
		{tVar(0), tNot(tVar(1))},
		{tNot(tVar(0)), tVar(1)},
		{tNot(tVar(0)), tNot(tVar(1))},
	}
	for i, p := range paths {
		if len(p.St.Vars) != 5 {
			t.Fatalf("path %d: expected 5 logical variables, got %d", i, len(p.St.Vars))
		}
		if len(p.St.Heap) != 2 {
			t.Fatalf("path %d: expected 2 heap cells, got %d", i, len(p.St.Heap))
		}
		if !condIs(p.St.Cond, conds[i]...) {
			t.Fatalf("path %d: wrong path condition", i)
		}
		if !TermEq(heapGet(p.St.Heap, tVar(2)), tInt(stored[i])) {
			t.Fatalf("path %d: wrong value stored through p", i)
		}
		// each path allocated its own cell, which is logical variable 4
		if !TermEq(p.Ret, tVar(4)) {
			t.Fatalf("path %d: expected the allocated location", i)
		}
		if !TermEq(heapGet(p.St.Heap, tVar(4)), tInt(stored[i]*10)) {
			t.Fatalf("path %d: wrong value in the allocated cell", i)
		}
	}
}

// --- postcondition matching --------------------------------------------------

// explainReason returns the reason the given disjunct failed for the first
// failing path.
func explainReason(t *testing.T, paths []Path, vars []Sort, post *Assn, d int) Reason {
	t.Helper()
	fs := Explain(paths, vars, post)
	if len(fs) <= d {
		t.Fatalf("expected at least %d disjunct failures, got %d", d+1, len(fs))
	}
	return fs[d].Fail.Reason
}

func TestVerifyDouble(t *testing.T) {
	vars := sorts(SortInt, SortLoc, SortInt)
	pre := aPt(tVar(1), tVar(2))
	paths := mustAnalyze(t, doubleFn(), vars, pre)

	// One disjunct per path. Leftover cells (the local variable boxes) leak.
	post := aOr(
		aSep(aPt(tVar(1), tAdd(tInt(37), tInt(37))), aPure(tEq(tVar(0), tInt(0)))),
		aSep(aPt(tVar(1), tAdd(tVar(0), tVar(0))), aPure(tNot(tEq(tVar(0), tInt(0)))))) //nolint
	if fail := Verify(paths, vars, post); fail != nil {
		t.Fatalf("Verify rejected the true postcondition (reason %d)", fail.Reason)
	}
	if Explain(paths, vars, post) != nil {
		t.Fatal("Explain should return nil when Verify accepts")
	}
	if !Check(doubleFn(), vars, pre, post) {
		t.Fatal("Check rejected the true postcondition")
	}

	// A wrong value in the cell.
	bad := aPt(tVar(1), tInt(74))
	fail := Verify(paths, vars, bad)
	if fail == nil || fail.Reason != RPostNoDisjunct || fail.PathIdx != 0 {
		t.Fatal("expected RPostNoDisjunct on path 0")
	}
	if r := explainReason(t, paths, vars, bad, 0); r != RPostValueMismatch {
		t.Fatalf("expected RPostValueMismatch, got %d", r)
	}

	// A cell that is not owned at all.
	missing := aPt(tVar(9), tInt(0))
	if Verify(paths, vars, missing) == nil {
		t.Fatal("expected a failure for an unowned cell")
	}
	// (variable 9 does not exist, so this is ill-sorted before it is missing)
	if r := explainReason(t, paths, vars, missing, 0); r != RIllSorted {
		t.Fatalf("expected RIllSorted, got %d", r)
	}
	// A location of the right sort that the heap does not own: variable 3 is
	// a ghost location, so allocation starts at 4.
	ghostVars := sorts(SortInt, SortLoc, SortInt, SortLoc)
	ghostPaths := mustAnalyze(t, doubleFn(), ghostVars, pre)
	notOwned := aPt(tVar(3), tInt(0))
	if r := explainReason(t, ghostPaths, ghostVars, notOwned, 0); r != RPostCellMissing {
		t.Fatalf("expected RPostCellMissing, got %d", r)
	}

	// A pure atom that the path condition does not justify.
	unjust := aPure(tEq(tVar(0), tInt(5)))
	if Verify(paths, vars, unjust) == nil {
		t.Fatal("expected a failure for an unjustified pure atom")
	}
	if r := explainReason(t, paths, vars, unjust, 0); r != RPostPureMissing {
		t.Fatalf("expected RPostPureMissing, got %d", r)
	}

	// emp and `true` are satisfied by every path.
	if Verify(paths, vars, aEmp()) != nil {
		t.Fatal("emp should hold on every path")
	}
	if Verify(paths, vars, aPure(tBool(true))) != nil {
		t.Fatal("true should hold on every path")
	}
	if Verify(paths, vars, aPure(tBool(false))) == nil {
		t.Fatal("false should hold on no path")
	}

	// A disjunction only helps if some disjunct matches each path: giving
	// both paths the same (path-1) disjunct must fail on path 2.
	oneSided := aOr(
		aSep(aPt(tVar(1), tAdd(tInt(37), tInt(37))), aPure(tEq(tVar(0), tInt(0)))),
		aPure(tEq(tVar(0), tInt(1))))
	fail = Verify(paths, vars, oneSided)
	if fail == nil || fail.Reason != RPostNoDisjunct || fail.PathIdx != 1 {
		t.Fatal("expected RPostNoDisjunct on path 1")
	}
}

func TestVerifyPatternBinding(t *testing.T) {
	// A function that does nothing, so that the postcondition is matched
	// directly against the precondition's heap.
	nop := &Func{Params: []string{"p", "q"}, Body: eUnit()}
	// vars: 0 = p, 1 = q, 2, 3 = values
	vars := sorts(SortLoc, SortLoc, SortInt, SortInt)
	post := aEx(0, SortInt, aSep(aPt(tVar(0), tPat(0)), aPt(tVar(1), tPat(0))))

	// ∃ v, p ↦ v ∗ q ↦ v holds when both cells hold the same term.
	same := aSep(aPt(tVar(0), tVar(2)), aPt(tVar(1), tVar(2)))
	if !Check(nop, vars, same, post) {
		t.Fatal("∃ v, p ↦ v ∗ q ↦ v should hold when both cells agree")
	}
	// ...and not when they differ: the second occurrence conflicts.
	diff := aSep(aPt(tVar(0), tVar(2)), aPt(tVar(1), tVar(3)))
	if Check(nop, vars, diff, post) {
		t.Fatal("∃ v, p ↦ v ∗ q ↦ v should fail when the cells differ")
	}
	paths := mustAnalyze(t, nop, vars, diff)
	if r := explainReason(t, paths, vars, post, 0); r != RPatConflict {
		t.Fatalf("expected RPatConflict, got %d", r)
	}

	// The two points-to atoms must match distinct cells, so ∃ v, p ↦ v ∗
	// p ↦ v needs two cells at p and cannot be satisfied by one.
	twice := aEx(0, SortInt, aSep(aPt(tVar(0), tPat(0)), aPt(tVar(0), tPat(0))))
	if Check(nop, vars, same, twice) {
		t.Fatal("one cell should not satisfy two points-to atoms")
	}

	// A bound pattern variable is substituted into pure atoms too.
	withPure := aEx(0, SortInt,
		aSep(aPt(tVar(0), tPat(0)), aPure(tEq(tPat(0), tVar(2)))))
	if !Check(nop, vars, same, withPure) {
		t.Fatal("a bound pattern variable should be usable in a pure atom")
	}

	// A pattern variable of the wrong sort never binds.
	badSort := aEx(0, SortBool, aSep(aPt(tVar(0), tPat(0)), aEmp()))
	if Check(nop, vars, same, badSort) {
		t.Fatal("a pattern variable of the wrong sort should not bind")
	}

	// The same binder twice is ambiguous.
	dupBinder := aEx(0, SortInt, aEx(0, SortInt, aPt(tVar(0), tPat(0))))
	if r := explainReason(t, mustAnalyze(t, nop, vars, same), vars, dupBinder, 0); r != RPatConflict {
		t.Fatal("expected RPatConflict for a duplicate binder")
	}
}

// TestVerifyPatternFixpoint exercises the phase-1 fixpoint: the location of
// one points-to atom is itself a pattern variable, bound by another atom.
func TestVerifyPatternFixpoint(t *testing.T) {
	nop := &Func{Params: []string{"q"}, Body: eUnit()}
	// vars: 0 = q, 1 = p (= *q), 2 = *p
	vars := sorts(SortLoc, SortLoc, SortInt)
	pre := aSep(aPt(tVar(0), tVar(1)), aPt(tVar(1), tVar(2)))
	// ∃ (l : loc) (v : int), l ↦ v ∗ q ↦ l
	post := aEx(0, SortLoc, aEx(1, SortInt,
		aSep(aPt(tPat(0), tPat(1)), aPt(tVar(0), tPat(0)))))
	if !Check(nop, vars, pre, post) {
		t.Fatal("the deferred points-to atom should be resolved on the second round")
	}
	// Without the atom that binds l, nothing can resolve.
	stuck := aEx(0, SortLoc, aEx(1, SortInt, aPt(tPat(0), tPat(1))))
	if Check(nop, vars, pre, stuck) {
		t.Fatal("an unbindable location should not match")
	}
	if r := explainReason(t, mustAnalyze(t, nop, vars, pre), vars, stuck, 0); r != RPatUnbound {
		t.Fatalf("expected RPatUnbound, got %d", r)
	}
}

func TestVerifyPatUnbound(t *testing.T) {
	nop := &Func{Params: nil, Body: eUnit()}
	// ∃ v, ⌜v == 0⌝: no points-to atom can bind v.
	post := aEx(0, SortInt, aPure(tEq(tPat(0), tInt(0))))
	if Verify(mustAnalyze(t, nop, sorts(), aEmp()), sorts(), post) == nil {
		t.Fatal("an unbound pattern variable in a pure atom should be rejected")
	}
	if r := explainReason(t, mustAnalyze(t, nop, sorts(), aEmp()), sorts(), post, 0); r != RPatUnbound {
		t.Fatalf("expected RPatUnbound, got %d", r)
	}
}

func TestVerifyResult(t *testing.T) {
	// `ret` in a pure atom: Max returns b on one path and a on the other.
	vars := sorts(SortInt, SortInt)
	paths := mustAnalyze(t, maxFn(), vars, aEmp())
	post := aOr(aPure(tEq(tRes(), tVar(1))), aPure(tEq(tRes(), tVar(0))))
	if fail := Verify(paths, vars, post); fail != nil {
		t.Fatalf("⌜ret == b⌝ ∨ ⌜ret == a⌝ should hold for Max (reason %d)", fail.Reason)
	}
	// Neither path returns a constant.
	if Verify(paths, vars, aPure(tEq(tRes(), tInt(0)))) == nil {
		t.Fatal("⌜ret == 0⌝ should not hold for Max")
	}

	// `ret` alongside the heap: CondStore.
	csVars := sorts(SortBool, SortLoc, SortInt, SortInt)
	csPaths := mustAnalyze(t, condStoreFn(), csVars, aPt(tVar(1), tVar(3)))
	csPost := aOr(
		sepAll(aPt(tVar(1), tVar(3)), aPure(tNot(tVar(0))), aPure(tEq(tRes(), tBool(false)))),
		sepAll(aPt(tVar(1), tVar(2)), aPure(tVar(0)), aPure(tRes())))
	if fail := Verify(csPaths, csVars, csPost); fail != nil {
		t.Fatalf("CondStore's postcondition should hold (reason %d)", fail.Reason)
	}
	// Swapping the two disjuncts' heap parts breaks both paths.
	csBad := aOr(
		sepAll(aPt(tVar(1), tVar(2)), aPure(tNot(tVar(0)))),
		sepAll(aPt(tVar(1), tVar(3)), aPure(tVar(0))))
	if Verify(csPaths, csVars, csBad) == nil {
		t.Fatal("the swapped postcondition should be rejected")
	}

	// `ret` in the value of a points-to atom, matched structurally.
	retVal := aOr(
		aSep(aPt(tVar(1), tRes()), aPure(tNot(tVar(0)))),
		aSep(aPt(tVar(1), tRes()), aPure(tVar(0))))
	// path 1 leaves *p = old, but ret is false: ill-sorted (bool vs int).
	if Verify(csPaths, csVars, retVal) == nil {
		t.Fatal("p ↦ ret should not hold when ret is a boolean")
	}
}

func TestVerifyUnsupported(t *testing.T) {
	nop := &Func{Params: nil, Body: eUnit()}
	paths := mustAnalyze(t, nop, sorts(), aEmp())
	// ∨ below ∗ is not supported.
	post := aSep(aOr(aEmp(), aEmp()), aEmp())
	if Verify(paths, sorts(), post) == nil {
		t.Fatal("∨ below ∗ should be rejected")
	}
	if r := explainReason(t, paths, sorts(), post, 0); r != RUnsupported {
		t.Fatalf("expected RUnsupported, got %d", r)
	}
	// ∃ below ∗ is not supported either.
	post2 := aSep(aEx(0, SortInt, aEmp()), aEmp())
	if r := explainReason(t, paths, sorts(), post2, 0); r != RUnsupported {
		t.Fatalf("expected RUnsupported, got %d", r)
	}
	// a nil postcondition
	if Verify(paths, sorts(), nil) == nil {
		t.Fatal("a nil postcondition should be rejected")
	}
}

// --- the exported helpers the frontend uses ----------------------------------

func TestExportedHelpers(t *testing.T) {
	if s, ok := TypeSort(tyUint64()); !ok || s != SortInt {
		t.Fatal("uint64 should have sort int")
	}
	if s, ok := TypeSort(tyPtr(tyBool())); !ok || s != SortLoc {
		t.Fatal("*bool should have sort loc")
	}
	if _, ok := TypeSort(tyPtr(&Type{Kind: 99})); ok {
		t.Fatal("a pointer to an unsupported type should be unsupported")
	}
	if _, ok := TypeSort(nil); ok {
		t.Fatal("the nil type should be unsupported")
	}
	if !TypeEq(tyPtr(tyInt()), tyPtr(tyInt())) {
		t.Fatal("*int should equal *int")
	}
	if TypeEq(tyPtr(tyInt()), tyPtr(tyUint64())) {
		t.Fatal("*int should not equal *uint64")
	}
	vars := sorts(SortInt, SortBool, SortLoc)
	if s, ok := SortOf(vars, tAdd(tVar(0), tInt(1))); !ok || s != SortInt {
		t.Fatal("x + 1 should have sort int")
	}
	if _, ok := SortOf(vars, tAdd(tVar(1), tInt(1))); ok {
		t.Fatal("bool + 1 should be ill-sorted")
	}
	if s, ok := SortOf(vars, tEq(tVar(2), &Term{Kind: TNull})); !ok || s != SortBool {
		t.Fatal("p == nil should have sort bool")
	}
	if _, ok := SortOf(vars, tVar(3)); ok {
		t.Fatal("an out-of-range variable should have no sort")
	}
	if _, ok := SortOf(vars, tPat(0)); ok {
		t.Fatal("a pattern variable should have no sort outside a disjunct")
	}
	if _, ok := SortOf(vars, tRes()); ok {
		t.Fatal("ret should have no sort outside a disjunct")
	}
	if s, ok := SortOf(vars, &Term{Kind: TIte, A: tVar(1), B: tVar(0), C: tInt(2)}); !ok || s != SortInt {
		t.Fatal("an if-then-else at int should have sort int")
	}
	if !TermEq(tAdd(tVar(0), tInt(1)), tAdd(tVar(0), tInt(1))) {
		t.Fatal("equal terms should compare equal")
	}
	if TermEq(tAdd(tVar(0), tInt(1)), tAdd(tVar(0), tInt(2))) {
		t.Fatal("different terms should not compare equal")
	}
	if TermEq(nil, tInt(0)) || !TermEq(nil, nil) {
		t.Fatal("term equality should be nil-safe")
	}
}
