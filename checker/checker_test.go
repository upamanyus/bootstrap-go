package checker_test

import (
	"testing"

	"github.com/mit-pdos/perennial/checker"
	"github.com/mit-pdos/perennial/gocheck/spec"
	"github.com/mit-pdos/perennial/gocheck/translate"
)

// --- small constructors for building test inputs ----------------------------
//
// Programs have no surface syntax here (the frontend gets them from goose), so
// the example functions below are still built by hand.

func tyInt() *checker.Type    { return &checker.Type{Kind: checker.TyInt} }
func tyInt64() *checker.Type  { return &checker.Type{Kind: checker.TyInt64} }
func tyUint64() *checker.Type { return &checker.Type{Kind: checker.TyUint64} }
func tyBool() *checker.Type   { return &checker.Type{Kind: checker.TyBool} }
func tyPtr(t *checker.Type) *checker.Type {
	return &checker.Type{Kind: checker.TyPtr, Elem: t}
}

func eInt(n uint64) *checker.Expr { return &checker.Expr{Kind: checker.EInt, Num: n} }
func eBool(b bool) *checker.Expr {
	if b {
		return &checker.Expr{Kind: checker.EBool, Num: 1}
	}
	return &checker.Expr{Kind: checker.EBool, Num: 0}
}
func eUnit() *checker.Expr        { return &checker.Expr{Kind: checker.EUnit} }
func eVar(x string) *checker.Expr { return &checker.Expr{Kind: checker.EVar, Name: x} }
func eLet(x string, a, b *checker.Expr) *checker.Expr {
	return &checker.Expr{Kind: checker.ELet, Name: x, A: a, B: b}
}
func eSeq(a, b *checker.Expr) *checker.Expr {
	return &checker.Expr{Kind: checker.ESeq, A: a, B: b}
}
func eIf(a, b, c *checker.Expr) *checker.Expr {
	return &checker.Expr{Kind: checker.EIf, A: a, B: b, C: c}
}
func eLoad(t *checker.Type, a *checker.Expr) *checker.Expr {
	return &checker.Expr{Kind: checker.ELoad, Ty: t, A: a}
}
func eStore(t *checker.Type, a, b *checker.Expr) *checker.Expr {
	return &checker.Expr{Kind: checker.EStore, Ty: t, A: a, B: b}
}
func eAlloc(t *checker.Type, a *checker.Expr) *checker.Expr {
	return &checker.Expr{Kind: checker.EAlloc, Ty: t, A: a}
}
func eZero(t *checker.Type) *checker.Expr {
	return &checker.Expr{Kind: checker.EZero, Ty: t}
}
func eBin(op checker.Op, t *checker.Type, a, b *checker.Expr) *checker.Expr {
	return &checker.Expr{Kind: checker.EBinOp, Op: op, Ty: t, A: a, B: b}
}
func eUn(op checker.Op, t *checker.Type, a *checker.Expr) *checker.Expr {
	return &checker.Expr{Kind: checker.EUnOp, Op: op, Ty: t, A: a}
}
func eConv(from, to *checker.Type, a *checker.Expr) *checker.Expr {
	return &checker.Expr{Kind: checker.EConvert, Ty: from, Ty2: to, A: a}
}
func eDo(a *checker.Expr) *checker.Expr  { return &checker.Expr{Kind: checker.EDo, A: a} }
func eRet(a *checker.Expr) *checker.Expr { return &checker.Expr{Kind: checker.EReturn, A: a} }
func eExcSeq(a, b *checker.Expr) *checker.Expr {
	return &checker.Expr{Kind: checker.EExcSeq, A: a, B: b}
}
func eExcDo(a *checker.Expr) *checker.Expr { return &checker.Expr{Kind: checker.EExcDo, A: a} }

// The term and assertion constructors below exist only for the inputs that the
// surface language cannot express, because the frontend rejects them before
// the checker would: ill-sorted atoms, out-of-range variables, a repeated ∃
// binder, and ∨ or ∃ in positions where the checker must report them itself.
// Every well-formed assertion in this file comes from the parser instead.

func tVar(n uint64) *checker.Term { return &checker.Term{Kind: checker.TVar, Num: n} }
func tPat(n uint64) *checker.Term { return &checker.Term{Kind: checker.TPat, Num: n} }
func tRes() *checker.Term         { return &checker.Term{Kind: checker.TResult} }
func tInt(n uint64) *checker.Term { return &checker.Term{Kind: checker.TInt, Num: n} }
func tAdd(a, b *checker.Term) *checker.Term {
	return &checker.Term{Kind: checker.TAdd, A: a, B: b}
}
func tEq(a, b *checker.Term) *checker.Term {
	return &checker.Term{Kind: checker.TEq, A: a, B: b}
}

func aEmp() *checker.Assn { return &checker.Assn{Kind: checker.AEmp} }
func aSep(l, r *checker.Assn) *checker.Assn {
	return &checker.Assn{Kind: checker.ASep, L: l, R: r}
}
func aOr(l, r *checker.Assn) *checker.Assn {
	return &checker.Assn{Kind: checker.AOr, L: l, R: r}
}
func aPure(x *checker.Term) *checker.Assn {
	return &checker.Assn{Kind: checker.APure, X: x}
}
func aPt(x, y *checker.Term) *checker.Assn {
	return &checker.Assn{Kind: checker.APointsTo, X: x, Y: y}
}
func aEx(v uint64, s checker.Sort, l *checker.Assn) *checker.Assn {
	return &checker.Assn{Kind: checker.AExists, Var: v, Sort: s, L: l}
}

func sorts(ss ...checker.Sort) []checker.Sort { return ss }

// --- specifications, written in the surface syntax ---------------------------
//
// Pre- and postconditions go through exactly the path the gocheck CLI uses:
// spec.Parse turns the source text into a surface assertion, and the
// spec.Scope resolves its names against the function's signature and lowers it
// to a checker.Assn. The expected terms that results are compared against are
// parsed the same way, with spec.ParseTerm.

func params(names []string, tys []*checker.Type) []translate.ParamInfo {
	out := make([]translate.ParamInfo, len(names))
	for i := range names {
		out[i] = translate.ParamInfo{Name: names[i], Index: i, Ty: tys[i]}
	}
	return out
}

// The signatures of the example functions. They give the specifications their
// parameter names and Go types; the types decide the signedness of a
// comparison and the sort of the value a pointer points to.

func doubleSig() []translate.ParamInfo {
	return params([]string{"x", "z"}, []*checker.Type{tyInt(), tyPtr(tyInt())})
}

func maxSig() []translate.ParamInfo {
	return params([]string{"a", "b"}, []*checker.Type{tyUint64(), tyUint64()})
}

func swapSig() []translate.ParamInfo {
	return params([]string{"p", "q"},
		[]*checker.Type{tyPtr(tyUint64()), tyPtr(tyUint64())})
}

func absSig() []translate.ParamInfo {
	return params([]string{"x"}, []*checker.Type{tyInt()})
}

func condStoreSig() []translate.ParamInfo {
	return params([]string{"flag", "p", "v"},
		[]*checker.Type{tyBool(), tyPtr(tyUint64()), tyUint64()})
}

// scope is the lowering context of one specification: the names of a
// function's parameters plus the ghost variables its precondition introduced.
// Postconditions and expected terms are written against the same names.
type scope struct {
	t    *testing.T
	sc   *spec.Scope
	vars []checker.Sort // sorts of the logical variables, by index
	pre  *checker.Assn  // the lowered precondition
}

// newScope builds the scope of sig and lowers the precondition src in it.
func newScope(t *testing.T, sig []translate.ParamInfo, src string) *scope {
	t.Helper()
	sc, err := spec.NewScope(sig)
	if err != nil {
		t.Fatalf("building the scope: %v", err)
	}
	s, err := spec.Parse(src)
	if err != nil {
		t.Fatalf("parsing the precondition %q: %v", src, err)
	}
	pre, err := sc.LowerPre(s)
	if err != nil {
		t.Fatalf("lowering the precondition %q: %v", src, err)
	}
	return &scope{t: t, sc: sc, vars: sc.Vars(), pre: pre}
}

// post parses and lowers a postcondition.
func (s *scope) post(src string) *checker.Assn {
	s.t.Helper()
	surface, err := spec.Parse(src)
	if err != nil {
		s.t.Fatalf("parsing the postcondition %q: %v", src, err)
	}
	a, err := s.sc.LowerPost(surface)
	if err != nil {
		s.t.Fatalf("lowering the postcondition %q: %v", src, err)
	}
	return a
}

// term parses and lowers one term.
func (s *scope) term(src string) *checker.Term {
	s.t.Helper()
	surface, err := spec.ParseTerm(src)
	if err != nil {
		s.t.Fatalf("parsing the term %q: %v", src, err)
	}
	x, err := s.sc.LowerTerm(surface)
	if err != nil {
		s.t.Fatalf("lowering the term %q: %v", src, err)
	}
	return x
}

// terms lowers several terms, for comparing against a path condition.
func (s *scope) terms(srcs ...string) []*checker.Term {
	s.t.Helper()
	out := make([]*checker.Term, len(srcs))
	for i, src := range srcs {
		out[i] = s.term(src)
	}
	return out
}

// --- assertions on results ---------------------------------------------------

func heapGet(h []checker.Cell, l *checker.Term) *checker.Term {
	for _, c := range h {
		if checker.TermEq(c.Loc, l) {
			return c.Val
		}
	}
	return nil
}

func condIs(cond []*checker.Term, want ...*checker.Term) bool {
	if len(cond) != len(want) {
		return false
	}
	for i, c := range cond {
		if !checker.TermEq(c, want[i]) {
			return false
		}
	}
	return true
}

func mustAnalyze(t *testing.T, f *checker.Func, vars []checker.Sort, pre *checker.Assn) []checker.Path {
	t.Helper()
	paths, fail := checker.Analyze(f, vars, pre)
	if fail != nil {
		t.Fatalf("Analyze failed with reason %d", fail.Reason)
	}
	return paths
}

// --- the example programs, transcribed from Goose output --------------------

// func Double(x int, z *int) { y := x; if x == 0 { y = 37 }; *z = y + y }
func doubleFn() *checker.Func {
	return &checker.Func{Params: []string{"x", "z"}, Body: eExcDo(
		eLet("z", eAlloc(tyPtr(tyInt()), eVar("z")),
			eLet("x", eAlloc(tyInt(), eVar("x")),
				eLet("y", eAlloc(tyInt(), eZero(tyInt())),
					eLet("$r0", eLoad(tyInt(), eVar("x")),
						eExcSeq(eDo(eStore(tyInt(), eVar("y"), eVar("$r0"))),
							eExcSeq(
								eIf(eConv(tyBool(), tyBool(), eBin(checker.OpEq, tyInt(), eLoad(tyInt(), eVar("x")), eInt(0))),
									eLet("$r0", eInt(37), eDo(eStore(tyInt(), eVar("y"), eVar("$r0")))),
									eDo(eUnit())),
								eLet("$r0", eBin(checker.OpAdd, tyInt(), eLoad(tyInt(), eVar("y")), eLoad(tyInt(), eVar("y"))),
									eExcSeq(eDo(eStore(tyInt(), eLoad(tyPtr(tyInt()), eVar("z")), eVar("$r0"))),
										eRet(eUnit())))))))))),
	}
}

// func Max(a, b uint64) uint64 { if a < b { return b }; return a }
func maxFn() *checker.Func {
	return &checker.Func{Params: []string{"a", "b"}, Body: eExcDo(
		eLet("b", eAlloc(tyUint64(), eVar("b")),
			eLet("a", eAlloc(tyUint64(), eVar("a")),
				eExcSeq(
					eIf(eConv(tyBool(), tyBool(), eBin(checker.OpLt, tyUint64(), eLoad(tyUint64(), eVar("a")), eLoad(tyUint64(), eVar("b")))),
						eRet(eLoad(tyUint64(), eVar("b"))),
						eDo(eUnit())),
					eRet(eLoad(tyUint64(), eVar("a"))))))),
	}
}

// func Swap(p, q *uint64) { tmp := *p; *p = *q; *q = tmp }
func swapFn() *checker.Func {
	pu := tyPtr(tyUint64())
	return &checker.Func{Params: []string{"p", "q"}, Body: eExcDo(
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
func absFn() *checker.Func {
	return &checker.Func{Params: []string{"x"}, Body: eExcDo(
		eLet("x", eAlloc(tyInt(), eVar("x")),
			eExcSeq(
				eIf(eConv(tyBool(), tyBool(), eBin(checker.OpLt, tyInt(), eLoad(tyInt(), eVar("x")), eInt(0))),
					eRet(eUn(checker.OpNeg, tyInt(), eLoad(tyInt(), eVar("x")))),
					eDo(eUnit())),
				eRet(eLoad(tyInt(), eVar("x")))))),
	}
}

//	func CondStore(flag bool, p *uint64, v uint64) bool {
//		if !flag { return false }; *p = v; return true
//	}
func condStoreFn() *checker.Func {
	pu := tyPtr(tyUint64())
	return &checker.Func{Params: []string{"flag", "p", "v"}, Body: eExcDo(
		eLet("v", eAlloc(tyUint64(), eVar("v")),
			eLet("p", eAlloc(pu, eVar("p")),
				eLet("flag", eAlloc(tyBool(), eVar("flag")),
					eExcSeq(
						eIf(eUn(checker.OpNot, tyBool(), eLoad(tyBool(), eVar("flag"))),
							eRet(eBool(false)),
							eDo(eUnit())),
						eLet("$r0", eLoad(tyUint64(), eVar("v")),
							eExcSeq(eDo(eStore(tyUint64(), eLoad(pu, eVar("p")), eVar("$r0"))),
								eRet(eBool(true))))))))),
	}
}

// --- symbolic execution ------------------------------------------------------

func TestDouble(t *testing.T) {
	// vars: 0 = x:int, 1 = z:*int, 2 = z0, the old value of *z
	s := newScope(t, doubleSig(), "z ↦ z0")
	paths := mustAnalyze(t, doubleFn(), s.vars, s.pre)
	if len(paths) != 2 {
		t.Fatalf("expected 2 paths, got %d", len(paths))
	}

	// path 1: x == 0, so *z = 37 + 37
	p0 := paths[0]
	if !checker.TermEq(heapGet(p0.St.Heap, s.term("z")), s.term("37 + 37")) {
		t.Fatal("path 1: wrong value for *z")
	}
	if !condIs(p0.St.Cond, s.terms("x == 0")...) {
		t.Fatal("path 1: wrong path condition")
	}

	// path 2: !(x == 0), so *z = x + x
	p1 := paths[1]
	if !checker.TermEq(heapGet(p1.St.Heap, s.term("z")), s.term("x + x")) {
		t.Fatal("path 2: wrong value for *z")
	}
	if !condIs(p1.St.Cond, s.terms("x != 0")...) {
		t.Fatal("path 2: wrong path condition")
	}

	if !checker.TermEq(p0.Ret, s.term("()")) || !checker.TermEq(p1.Ret, s.term("()")) {
		t.Fatal("expected unit return on both paths")
	}

	// Without ownership of *z the store is unsafe.
	none := newScope(t, doubleSig(), "emp")
	_, fail := checker.Analyze(doubleFn(), none.vars, none.pre)
	if fail == nil || fail.Reason != checker.RNoPointsTo {
		t.Fatal("Double should not be safe without ownership of *z")
	}
}

func TestMax(t *testing.T) {
	s := newScope(t, maxSig(), "emp")
	paths := mustAnalyze(t, maxFn(), s.vars, s.pre)
	if len(paths) != 2 {
		t.Fatalf("expected 2 paths, got %d", len(paths))
	}
	if !checker.TermEq(paths[0].Ret, s.term("b")) || !checker.TermEq(paths[1].Ret, s.term("a")) {
		t.Fatal("wrong return values")
	}
	// uint64 comparison must be unsigned
	if !condIs(paths[0].St.Cond, s.terms("a <u b")...) {
		t.Fatal("path 1: expected an unsigned <")
	}
	if !condIs(paths[1].St.Cond, s.terms("a >=u b")...) {
		t.Fatal("path 2: wrong path condition")
	}
}

func TestSwap(t *testing.T) {
	// vars: 0 = p, 1 = q, 2 = a0 = *p, 3 = b0 = *q
	s := newScope(t, swapSig(), "p ↦ a0 ∗ q ↦ b0")
	paths := mustAnalyze(t, swapFn(), s.vars, s.pre)
	if len(paths) != 1 {
		t.Fatalf("expected 1 path, got %d", len(paths))
	}
	h := paths[0].St.Heap
	if !checker.TermEq(heapGet(h, s.term("p")), s.term("b0")) ||
		!checker.TermEq(heapGet(h, s.term("q")), s.term("a0")) {
		t.Fatal("Swap did not swap")
	}
	// Only one pointer owned: the other store is unsafe.
	half := newScope(t, swapSig(), "p ↦ a0")
	_, fail := checker.Analyze(swapFn(), half.vars, half.pre)
	if fail == nil || fail.Reason != checker.RNoPointsTo {
		t.Fatal("Swap should be unsafe with only *p owned")
	}
}

func TestAbs(t *testing.T) {
	s := newScope(t, absSig(), "emp")
	paths := mustAnalyze(t, absFn(), s.vars, s.pre)
	if len(paths) != 2 {
		t.Fatalf("expected 2 paths, got %d", len(paths))
	}
	if !checker.TermEq(paths[0].Ret, s.term("-x")) || !checker.TermEq(paths[1].Ret, s.term("x")) {
		t.Fatal("wrong return values")
	}
	// int comparison must be signed
	if !condIs(paths[0].St.Cond, s.terms("x <s 0")...) {
		t.Fatal("path 1: expected a signed <")
	}
}

func TestCondStore(t *testing.T) {
	// vars: 0 = flag, 1 = p, 2 = v, 3 = w0, the old value of *p
	s := newScope(t, condStoreSig(), "p ↦ w0")
	paths := mustAnalyze(t, condStoreFn(), s.vars, s.pre)
	if len(paths) != 2 {
		t.Fatalf("expected 2 paths, got %d", len(paths))
	}
	// path 1: !flag, returns false, *p unchanged
	if !checker.TermEq(paths[0].Ret, s.term("false")) {
		t.Fatal("path 1: expected false")
	}
	if !checker.TermEq(heapGet(paths[0].St.Heap, s.term("p")), s.term("w0")) {
		t.Fatal("path 1: *p should be unchanged")
	}
	if !condIs(paths[0].St.Cond, s.terms("!flag")...) {
		t.Fatal("path 1: wrong path condition")
	}
	// path 2: flag, with the double negation cancelled
	if !checker.TermEq(paths[1].Ret, s.term("true")) {
		t.Fatal("path 2: expected true")
	}
	if !checker.TermEq(heapGet(paths[1].St.Heap, s.term("p")), s.term("v")) {
		t.Fatal("path 2: *p should be v")
	}
	if !condIs(paths[1].St.Cond, s.terms("flag")...) {
		t.Fatal("path 2: expected the double negation to cancel")
	}
}

func TestIllSorted(t *testing.T) {
	xInt := newScope(t, absSig(), "emp")
	// `if` on an integer
	f := &checker.Func{Params: []string{"x"}, Body: eIf(eVar("x"), eUnit(), eUnit())}
	_, fail := checker.Analyze(f, xInt.vars, xInt.pre)
	if fail == nil || fail.Reason != checker.RIllSorted {
		t.Fatal("if on an int should be rejected")
	}
	// int + bool
	f2 := &checker.Func{Params: []string{"x"},
		Body: eBin(checker.OpAdd, tyInt(), eVar("x"), eBool(true))}
	_, fail = checker.Analyze(f2, xInt.vars, xInt.pre)
	if fail == nil || fail.Reason != checker.RIllSorted {
		t.Fatal("int + bool should be rejected")
	}
	// == at unit
	none := newScope(t, nil, "emp")
	f3 := &checker.Func{Params: nil, Body: eBin(checker.OpEq, tyInt(), eUnit(), eUnit())}
	_, fail = checker.Analyze(f3, none.vars, none.pre)
	if fail == nil || fail.Reason != checker.RIllSorted {
		t.Fatal("unit == unit should be rejected")
	}
	// !x on an int
	f4 := &checker.Func{Params: []string{"x"}, Body: eUn(checker.OpNot, tyBool(), eVar("x"))}
	_, fail = checker.Analyze(f4, xInt.vars, xInt.pre)
	if fail == nil || fail.Reason != checker.RIllSorted {
		t.Fatal("!int should be rejected")
	}
	// -x at an unsigned type. Go allows it, but GooseLang has no GoUnOp
	// GoNeg at uint/uint64, so the translated program is stuck there and the
	// checker must not call it safe.
	xU64 := newScope(t, params([]string{"x"}, []*checker.Type{tyUint64()}), "emp")
	f5 := &checker.Func{Params: []string{"x"}, Body: eUn(checker.OpNeg, tyUint64(), eVar("x"))}
	_, fail = checker.Analyze(f5, xU64.vars, xU64.pre)
	if fail == nil || fail.Reason != checker.RIllSorted {
		t.Fatal("unary minus at uint64 should be rejected")
	}
	// ... but it is still accepted at the signed types.
	f6 := &checker.Func{Params: []string{"x"}, Body: eUn(checker.OpNeg, tyInt(), eVar("x"))}
	if _, fail = checker.Analyze(f6, xInt.vars, xInt.pre); fail != nil {
		t.Fatalf("unary minus at int should be accepted, got reason %d", fail.Reason)
	}
	f7 := &checker.Func{Params: []string{"x"}, Body: eUn(checker.OpNeg, tyInt64(), eVar("x"))}
	x64 := newScope(t, params([]string{"x"}, []*checker.Type{tyInt64()}), "emp")
	if _, fail = checker.Analyze(f7, x64.vars, x64.pre); fail != nil {
		t.Fatalf("unary minus at int64 should be accepted, got reason %d", fail.Reason)
	}
	// An ill-sorted precondition. Sort inference in the surface language
	// rejects these, so the checker only sees them from a caller that built
	// the assertion itself.
	_, fail = checker.Analyze(&checker.Func{Body: eUnit()}, xInt.vars, aPt(tVar(0), tInt(0)))
	if fail == nil || fail.Reason != checker.RIllSorted {
		t.Fatal("a points-to at a non-location should be rejected")
	}
	_, fail = checker.Analyze(&checker.Func{Body: eUnit()}, xInt.vars, aPure(tVar(0)))
	if fail == nil || fail.Reason != checker.RIllSorted {
		t.Fatal("a pure atom at a non-boolean should be rejected")
	}
}

func TestStoreThroughNil(t *testing.T) {
	xInt := newScope(t, absSig(), "emp")
	f := &checker.Func{Params: []string{"x"},
		Body: eStore(tyInt(), eZero(tyPtr(tyInt())), eVar("x"))}
	_, fail := checker.Analyze(f, xInt.vars, xInt.pre)
	if fail == nil || fail.Reason != checker.RNoPointsTo {
		t.Fatal("store through nil should be rejected")
	}
	none := newScope(t, nil, "emp")
	f2 := &checker.Func{Params: nil, Body: eLoad(tyInt(), eZero(tyPtr(tyInt())))}
	_, fail = checker.Analyze(f2, none.vars, none.pre)
	if fail == nil || fail.Reason != checker.RNoPointsTo {
		t.Fatal("load through nil should be rejected")
	}
}

func TestInputValidation(t *testing.T) {
	xInt := newScope(t, absSig(), "emp")
	f := &checker.Func{Params: []string{"x", "y"}, Body: eUnit()}
	_, fail := checker.Analyze(f, xInt.vars, xInt.pre)
	if fail == nil || fail.Reason != checker.RVarsTooShort {
		t.Fatal("expected RVarsTooShort")
	}
	none := newScope(t, nil, "emp")
	g := &checker.Func{Params: nil, Body: eUnit()}
	// ∨ in a precondition, and a precondition ∃ that has not been lifted to
	// logical variables: the surface language rules both out, so the
	// checker's own rejection is exercised with hand-built assertions.
	_, fail = checker.Analyze(g, none.vars, aOr(aEmp(), aEmp()))
	if fail == nil || fail.Reason != checker.RPreHasOr {
		t.Fatal("expected RPreHasOr")
	}
	_, fail = checker.Analyze(g, none.vars, aEx(0, checker.SortInt, aEmp()))
	if fail == nil || fail.Reason != checker.RPreHasExists {
		t.Fatal("expected RPreHasExists")
	}
	h := &checker.Func{Params: []string{"x"}, Body: eVar("y")}
	_, fail = checker.Analyze(h, xInt.vars, xInt.pre)
	if fail == nil || fail.Reason != checker.RUnboundVar || fail.Name != "y" {
		t.Fatal("expected RUnboundVar for y")
	}
	// a repeated parameter name: the later one wins
	dupSig := params([]string{"x", "x"}, []*checker.Type{tyInt(), tyInt()})
	dupScope := newScope(t, dupSig, "emp")
	dup := &checker.Func{Params: []string{"x", "x"}, Body: eVar("x")}
	paths := mustAnalyze(t, dup, dupScope.vars, dupScope.pre)
	if !checker.TermEq(paths[0].Ret, dupScope.term("x")) {
		t.Fatal("the later parameter should shadow the earlier one")
	}
}

func TestConvertAndMonad(t *testing.T) {
	xInt := newScope(t, absSig(), "emp")
	none := newScope(t, nil, "emp")
	// a non-identity conversion
	f := &checker.Func{Params: []string{"x"}, Body: eConv(tyInt(), tyBool(), eVar("x"))}
	_, fail := checker.Analyze(f, xInt.vars, xInt.pre)
	if fail == nil || fail.Reason != checker.RBadConvert {
		t.Fatal("expected RBadConvert")
	}
	// an identity conversion is transparent
	g := &checker.Func{Params: []string{"x"}, Body: eConv(tyInt(), tyInt(), eVar("x"))}
	paths := mustAnalyze(t, g, xInt.vars, xInt.pre)
	if !checker.TermEq(paths[0].Ret, xInt.term("x")) {
		t.Fatal("an identity conversion should be transparent")
	}
	// exception_do on a plain value
	h := &checker.Func{Params: nil, Body: eExcDo(eInt(3))}
	_, fail = checker.Analyze(h, none.vars, none.pre)
	if fail == nil || fail.Reason != checker.RBadMonad {
		t.Fatal("expected RBadMonad for exception_do")
	}
	// ;;; on a plain value
	k := &checker.Func{Params: nil, Body: eExcSeq(eInt(3), eDo(eUnit()))}
	_, fail = checker.Analyze(k, none.vars, none.pre)
	if fail == nil || fail.Reason != checker.RBadMonad {
		t.Fatal("expected RBadMonad for ;;;")
	}
	// a literal condition does not fork
	lit := &checker.Func{Params: nil, Body: eIf(eBool(true), eInt(1), eInt(2))}
	paths = mustAnalyze(t, lit, none.vars, none.pre)
	if len(paths) != 1 || !checker.TermEq(paths[0].Ret, none.term("1")) || len(paths[0].St.Cond) != 0 {
		t.Fatal("a literal condition should not fork")
	}
	lit2 := &checker.Func{Params: nil, Body: eIf(eBool(false), eInt(1), eInt(2))}
	paths = mustAnalyze(t, lit2, none.vars, none.pre)
	if len(paths) != 1 || !checker.TermEq(paths[0].Ret, none.term("2")) {
		t.Fatal("a literal false condition should take the else branch")
	}
}

// TestForkNoAliasing is a regression test for state sharing between paths.
// Each of the four paths stores a different value through p and allocates a
// different value; if the forked states shared their heap, path-condition or
// variable slices, the paths would see one another's updates.
func TestForkNoAliasing(t *testing.T) {
	inner := func(a, b uint64) *checker.Expr {
		return eIf(eVar("c"),
			eSeq(eStore(tyInt(), eVar("p"), eInt(a)), eAlloc(tyInt(), eInt(a*10))),
			eSeq(eStore(tyInt(), eVar("p"), eInt(b)), eAlloc(tyInt(), eInt(b*10))))
	}
	body := eIf(eVar("b"),
		eSeq(eStore(tyInt(), eVar("p"), eInt(1)), inner(2, 3)),
		eSeq(eStore(tyInt(), eVar("p"), eInt(4)), inner(5, 6)))
	f := &checker.Func{Params: []string{"b", "c", "p"}, Body: body}
	// vars: 0 = b, 1 = c, 2 = p, 3 = v0, the old value of *p
	sig := params([]string{"b", "c", "p"},
		[]*checker.Type{tyBool(), tyBool(), tyPtr(tyInt())})
	s := newScope(t, sig, "p ↦ v0")
	paths := mustAnalyze(t, f, s.vars, s.pre)
	if len(paths) != 4 {
		t.Fatalf("expected 4 paths, got %d", len(paths))
	}
	stored := []string{"2", "3", "5", "6"}
	allocated := []string{"20", "30", "50", "60"}
	conds := [][]*checker.Term{
		s.terms("b", "c"),
		s.terms("b", "!c"),
		s.terms("!b", "c"),
		s.terms("!b", "!c"),
	}
	// The cell each path allocates is the next logical variable after the
	// ones the specification named, so it has no surface name.
	allocLoc := tVar(uint64(len(s.vars)))
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
		if !checker.TermEq(heapGet(p.St.Heap, s.term("p")), s.term(stored[i])) {
			t.Fatalf("path %d: wrong value stored through p", i)
		}
		// each path allocated its own cell, which is logical variable 4
		if !checker.TermEq(p.Ret, allocLoc) {
			t.Fatalf("path %d: expected the allocated location", i)
		}
		if !checker.TermEq(heapGet(p.St.Heap, allocLoc), s.term(allocated[i])) {
			t.Fatalf("path %d: wrong value in the allocated cell", i)
		}
	}
}

// --- postcondition matching --------------------------------------------------

// explainReason returns the reason the given disjunct failed for the first
// failing path.
func explainReason(t *testing.T, paths []checker.Path, vars []checker.Sort, post *checker.Assn, d int) checker.Reason {
	t.Helper()
	fs := checker.Explain(paths, vars, post)
	if len(fs) <= d {
		t.Fatalf("expected at least %d disjunct failures, got %d", d+1, len(fs))
	}
	return fs[d].Fail.Reason
}

func TestVerifyDouble(t *testing.T) {
	s := newScope(t, doubleSig(), "z ↦ z0")
	paths := mustAnalyze(t, doubleFn(), s.vars, s.pre)

	// One disjunct per path. Leftover cells (the local variable boxes) leak.
	post := s.post("(z ↦ 37 + 37 ∗ ⌜x == 0⌝) ∨ (z ↦ x + x ∗ ⌜x != 0⌝)")
	if fail := checker.Verify(paths, s.vars, post); fail != nil {
		t.Fatalf("Verify rejected the true postcondition (reason %d)", fail.Reason)
	}
	if checker.Explain(paths, s.vars, post) != nil {
		t.Fatal("Explain should return nil when Verify accepts")
	}
	if !checker.Check(doubleFn(), s.vars, s.pre, post) {
		t.Fatal("Check rejected the true postcondition")
	}

	// A wrong value in the cell.
	bad := s.post("z ↦ 74")
	fail := checker.Verify(paths, s.vars, bad)
	if fail == nil || fail.Reason != checker.RPostNoDisjunct || fail.PathIdx != 0 {
		t.Fatal("expected RPostNoDisjunct on path 0")
	}
	if r := explainReason(t, paths, s.vars, bad, 0); r != checker.RPostValueMismatch {
		t.Fatalf("expected RPostValueMismatch, got %d", r)
	}

	// A cell at a variable that does not exist. The surface language cannot
	// name one, so this assertion is built by hand.
	missing := aPt(tVar(9), tInt(0))
	if checker.Verify(paths, s.vars, missing) == nil {
		t.Fatal("expected a failure for an unowned cell")
	}
	// (variable 9 does not exist, so this is ill-sorted before it is missing)
	if r := explainReason(t, paths, s.vars, missing, 0); r != checker.RIllSorted {
		t.Fatalf("expected RIllSorted, got %d", r)
	}
	// A location of the right sort that the heap does not own: g is a ghost
	// location, so allocation starts after it.
	ghost := newScope(t, doubleSig(), "z ↦ z0 ∗ ⌜g != null⌝")
	ghostPaths := mustAnalyze(t, doubleFn(), ghost.vars, ghost.pre)
	notOwned := ghost.post("g ↦ 0")
	if r := explainReason(t, ghostPaths, ghost.vars, notOwned, 0); r != checker.RPostCellMissing {
		t.Fatalf("expected RPostCellMissing, got %d", r)
	}

	// A pure atom that the path condition does not justify.
	unjust := s.post("⌜x == 5⌝")
	if checker.Verify(paths, s.vars, unjust) == nil {
		t.Fatal("expected a failure for an unjustified pure atom")
	}
	if r := explainReason(t, paths, s.vars, unjust, 0); r != checker.RPostPureMissing {
		t.Fatalf("expected RPostPureMissing, got %d", r)
	}

	// emp and `true` are satisfied by every path.
	if checker.Verify(paths, s.vars, s.post("emp")) != nil {
		t.Fatal("emp should hold on every path")
	}
	if checker.Verify(paths, s.vars, s.post("⌜true⌝")) != nil {
		t.Fatal("true should hold on every path")
	}
	if checker.Verify(paths, s.vars, s.post("⌜false⌝")) == nil {
		t.Fatal("false should hold on no path")
	}

	// A disjunction only helps if some disjunct matches each path: giving
	// both paths the same (path-1) disjunct must fail on path 2.
	oneSided := s.post("(z ↦ 37 + 37 ∗ ⌜x == 0⌝) ∨ ⌜x == 1⌝")
	fail = checker.Verify(paths, s.vars, oneSided)
	if fail == nil || fail.Reason != checker.RPostNoDisjunct || fail.PathIdx != 1 {
		t.Fatal("expected RPostNoDisjunct on path 1")
	}
}

func TestVerifyPatternBinding(t *testing.T) {
	// A function that does nothing, so that the postcondition is matched
	// directly against the precondition's heap.
	nop := &checker.Func{Params: []string{"p", "q"}, Body: eUnit()}
	sig := params([]string{"p", "q"}, []*checker.Type{tyPtr(tyInt()), tyPtr(tyInt())})
	const postSrc = "∃ (v : int), p ↦ v ∗ q ↦ v"

	// ∃ v, p ↦ v ∗ q ↦ v holds when both cells hold the same term.
	same := newScope(t, sig, "p ↦ v0 ∗ q ↦ v0")
	if !checker.Check(nop, same.vars, same.pre, same.post(postSrc)) {
		t.Fatal("∃ v, p ↦ v ∗ q ↦ v should hold when both cells agree")
	}
	// ...and not when they differ: the second occurrence conflicts.
	diff := newScope(t, sig, "p ↦ v0 ∗ q ↦ w0")
	if checker.Check(nop, diff.vars, diff.pre, diff.post(postSrc)) {
		t.Fatal("∃ v, p ↦ v ∗ q ↦ v should fail when the cells differ")
	}
	paths := mustAnalyze(t, nop, diff.vars, diff.pre)
	if r := explainReason(t, paths, diff.vars, diff.post(postSrc), 0); r != checker.RPatConflict {
		t.Fatalf("expected RPatConflict, got %d", r)
	}

	// The two points-to atoms must match distinct cells, so ∃ v, p ↦ v ∗
	// p ↦ v needs two cells at p and cannot be satisfied by one.
	twice := same.post("∃ (v : int), p ↦ v ∗ p ↦ v")
	if checker.Check(nop, same.vars, same.pre, twice) {
		t.Fatal("one cell should not satisfy two points-to atoms")
	}

	// A bound pattern variable is substituted into pure atoms too.
	withPure := same.post("∃ (v : int), p ↦ v ∗ ⌜v == v0⌝")
	if !checker.Check(nop, same.vars, same.pre, withPure) {
		t.Fatal("a bound pattern variable should be usable in a pure atom")
	}

	// A pattern variable of the wrong sort never binds. Sort inference in the
	// surface language rejects this one, so it is built by hand.
	badSort := aEx(0, checker.SortBool, aSep(aPt(tVar(0), tPat(0)), aEmp()))
	if checker.Check(nop, same.vars, same.pre, badSort) {
		t.Fatal("a pattern variable of the wrong sort should not bind")
	}

	// The same binder twice is ambiguous. The parser numbers each binder
	// separately, so this too is built by hand.
	dupBinder := aEx(0, checker.SortInt, aEx(0, checker.SortInt, aPt(tVar(0), tPat(0))))
	if r := explainReason(t, mustAnalyze(t, nop, same.vars, same.pre), same.vars, dupBinder, 0); r != checker.RPatConflict {
		t.Fatal("expected RPatConflict for a duplicate binder")
	}
}

// TestVerifyPatternFixpoint exercises the phase-1 fixpoint: the location of
// one points-to atom is itself a pattern variable, bound by another atom.
func TestVerifyPatternFixpoint(t *testing.T) {
	nop := &checker.Func{Params: []string{"q"}, Body: eUnit()}
	// vars: 0 = q, 1 = p (= *q), 2 = v0 (= *p)
	sig := params([]string{"q"}, []*checker.Type{tyPtr(tyPtr(tyUint64()))})
	s := newScope(t, sig, "q ↦ p ∗ p ↦ v0")
	// ∃ (l : loc) (v : int), l ↦ v ∗ q ↦ l
	post := s.post("∃ (l : ptr) (v : int), l ↦ v ∗ q ↦ l")
	if !checker.Check(nop, s.vars, s.pre, post) {
		t.Fatal("the deferred points-to atom should be resolved on the second round")
	}
	// Without the atom that binds l, nothing can resolve.
	stuck := s.post("∃ (l : ptr) (v : int), l ↦ v")
	if checker.Check(nop, s.vars, s.pre, stuck) {
		t.Fatal("an unbindable location should not match")
	}
	if r := explainReason(t, mustAnalyze(t, nop, s.vars, s.pre), s.vars, stuck, 0); r != checker.RPatUnbound {
		t.Fatalf("expected RPatUnbound, got %d", r)
	}
}

func TestVerifyPatUnbound(t *testing.T) {
	nop := &checker.Func{Params: nil, Body: eUnit()}
	s := newScope(t, nil, "emp")
	// ∃ v, ⌜v == 0⌝: no points-to atom can bind v.
	post := s.post("∃ (v : int), ⌜v == 0⌝")
	if checker.Verify(mustAnalyze(t, nop, s.vars, s.pre), s.vars, post) == nil {
		t.Fatal("an unbound pattern variable in a pure atom should be rejected")
	}
	if r := explainReason(t, mustAnalyze(t, nop, s.vars, s.pre), s.vars, post, 0); r != checker.RPatUnbound {
		t.Fatalf("expected RPatUnbound, got %d", r)
	}
}

func TestVerifyResult(t *testing.T) {
	// `ret` in a pure atom: Max returns b on one path and a on the other.
	s := newScope(t, maxSig(), "emp")
	paths := mustAnalyze(t, maxFn(), s.vars, s.pre)
	post := s.post("⌜ret == b⌝ ∨ ⌜ret == a⌝")
	if fail := checker.Verify(paths, s.vars, post); fail != nil {
		t.Fatalf("⌜ret == b⌝ ∨ ⌜ret == a⌝ should hold for Max (reason %d)", fail.Reason)
	}
	// Neither path returns a constant.
	if checker.Verify(paths, s.vars, s.post("⌜ret == 0⌝")) == nil {
		t.Fatal("⌜ret == 0⌝ should not hold for Max")
	}

	// `ret` alongside the heap: CondStore.
	cs := newScope(t, condStoreSig(), "p ↦ w0")
	csPaths := mustAnalyze(t, condStoreFn(), cs.vars, cs.pre)
	csPost := cs.post("(p ↦ w0 ∗ ⌜!flag⌝ ∗ ⌜ret == false⌝) ∨ (p ↦ v ∗ ⌜flag⌝ ∗ ⌜ret⌝)")
	if fail := checker.Verify(csPaths, cs.vars, csPost); fail != nil {
		t.Fatalf("CondStore's postcondition should hold (reason %d)", fail.Reason)
	}
	// Swapping the two disjuncts' heap parts breaks both paths.
	csBad := cs.post("(p ↦ v ∗ ⌜!flag⌝) ∨ (p ↦ w0 ∗ ⌜flag⌝)")
	if checker.Verify(csPaths, cs.vars, csBad) == nil {
		t.Fatal("the swapped postcondition should be rejected")
	}

	// `ret` in the value of a points-to atom, matched structurally.
	retVal := cs.post("(p ↦ ret ∗ ⌜!flag⌝) ∨ (p ↦ ret ∗ ⌜flag⌝)")
	// path 1 leaves *p = old, but ret is false: ill-sorted (bool vs int).
	if checker.Verify(csPaths, cs.vars, retVal) == nil {
		t.Fatal("p ↦ ret should not hold when ret is a boolean")
	}
}

func TestVerifyUnsupported(t *testing.T) {
	nop := &checker.Func{Params: nil, Body: eUnit()}
	s := newScope(t, nil, "emp")
	paths := mustAnalyze(t, nop, s.vars, s.pre)
	// ∨ below ∗ is not supported. The surface language rejects it during
	// resolution, so the checker's own rejection is exercised by hand.
	post := aSep(aOr(aEmp(), aEmp()), aEmp())
	if checker.Verify(paths, s.vars, post) == nil {
		t.Fatal("∨ below ∗ should be rejected")
	}
	if r := explainReason(t, paths, s.vars, post, 0); r != checker.RUnsupported {
		t.Fatalf("expected RUnsupported, got %d", r)
	}
	// ∃ below ∗ is not supported either.
	post2 := aSep(aEx(0, checker.SortInt, aEmp()), aEmp())
	if r := explainReason(t, paths, s.vars, post2, 0); r != checker.RUnsupported {
		t.Fatalf("expected RUnsupported, got %d", r)
	}
	// a nil postcondition
	if checker.Verify(paths, s.vars, nil) == nil {
		t.Fatal("a nil postcondition should be rejected")
	}
}

// --- the exported helpers the frontend uses ----------------------------------

// TestExportedHelpers checks the checker's own term API on inputs the surface
// language cannot produce -- ill-sorted terms, an out-of-range variable, and a
// pattern variable or `ret` outside a disjunct -- so its terms are built here.
func TestExportedHelpers(t *testing.T) {
	if s, ok := checker.TypeSort(tyUint64()); !ok || s != checker.SortInt {
		t.Fatal("uint64 should have sort int")
	}
	if s, ok := checker.TypeSort(tyPtr(tyBool())); !ok || s != checker.SortLoc {
		t.Fatal("*bool should have sort loc")
	}
	if _, ok := checker.TypeSort(tyPtr(&checker.Type{Kind: 99})); ok {
		t.Fatal("a pointer to an unsupported type should be unsupported")
	}
	if _, ok := checker.TypeSort(nil); ok {
		t.Fatal("the nil type should be unsupported")
	}
	if !checker.TypeEq(tyPtr(tyInt()), tyPtr(tyInt())) {
		t.Fatal("*int should equal *int")
	}
	if checker.TypeEq(tyPtr(tyInt()), tyPtr(tyUint64())) {
		t.Fatal("*int should not equal *uint64")
	}
	vars := sorts(checker.SortInt, checker.SortBool, checker.SortLoc)
	if s, ok := checker.SortOf(vars, tAdd(tVar(0), tInt(1))); !ok || s != checker.SortInt {
		t.Fatal("x + 1 should have sort int")
	}
	if _, ok := checker.SortOf(vars, tAdd(tVar(1), tInt(1))); ok {
		t.Fatal("bool + 1 should be ill-sorted")
	}
	if s, ok := checker.SortOf(vars, tEq(tVar(2), &checker.Term{Kind: checker.TNull})); !ok || s != checker.SortBool {
		t.Fatal("p == nil should have sort bool")
	}
	if _, ok := checker.SortOf(vars, tVar(3)); ok {
		t.Fatal("an out-of-range variable should have no sort")
	}
	if _, ok := checker.SortOf(vars, tPat(0)); ok {
		t.Fatal("a pattern variable should have no sort outside a disjunct")
	}
	if _, ok := checker.SortOf(vars, tRes()); ok {
		t.Fatal("ret should have no sort outside a disjunct")
	}
	if s, ok := checker.SortOf(vars, &checker.Term{Kind: checker.TIte, A: tVar(1), B: tVar(0), C: tInt(2)}); !ok || s != checker.SortInt {
		t.Fatal("an if-then-else at int should have sort int")
	}
	if !checker.TermEq(tAdd(tVar(0), tInt(1)), tAdd(tVar(0), tInt(1))) {
		t.Fatal("equal terms should compare equal")
	}
	if checker.TermEq(tAdd(tVar(0), tInt(1)), tAdd(tVar(0), tInt(2))) {
		t.Fatal("different terms should not compare equal")
	}
	if checker.TermEq(nil, tInt(0)) || !checker.TermEq(nil, nil) {
		t.Fatal("term equality should be nil-safe")
	}
}
