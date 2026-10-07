package spec_test

import (
	"strings"
	"testing"

	"github.com/upamanyus/bootstrap-go/checker"
	"github.com/upamanyus/bootstrap-go/gocheck/render"
	"github.com/upamanyus/bootstrap-go/gocheck/spec"
	"github.com/upamanyus/bootstrap-go/gocheck/translate"
)

var (
	tInt  = &checker.Type{Kind: checker.TyInt}
	tU64  = &checker.Type{Kind: checker.TyUint64}
	tBool = &checker.Type{Kind: checker.TyBool}
)

func ptr(t *checker.Type) *checker.Type { return &checker.Type{Kind: checker.TyPtr, Elem: t} }

func params(names []string, tys []*checker.Type) []translate.ParamInfo {
	var out []translate.ParamInfo
	for i := range names {
		out = append(out, translate.ParamInfo{Name: names[i], Index: i, Ty: tys[i]})
	}
	return out
}

// doubleParams is the signature of examples.Double.
func doubleParams() []translate.ParamInfo {
	return params([]string{"x", "z"}, []*checker.Type{tInt, ptr(tInt)})
}

// maxParams is the signature of examples.Max.
func maxParams() []translate.ParamInfo {
	return params([]string{"a", "b"}, []*checker.Type{tU64, tU64})
}

// absParams is the signature of examples.Abs.
func absParams() []translate.ParamInfo {
	return params([]string{"x"}, []*checker.Type{tInt})
}

// condStoreParams is the signature of examples.CondStore.
func condStoreParams() []translate.ParamInfo {
	return params([]string{"flag", "p", "v"},
		[]*checker.Type{tBool, ptr(tU64), tU64})
}

func assnEq(a, b *checker.Assn) bool {
	if a == nil || b == nil {
		return a == b
	}
	if a.Kind != b.Kind || a.Var != b.Var || a.Sort != b.Sort {
		return false
	}
	return checker.TermEq(a.X, b.X) && checker.TermEq(a.Y, b.Y) &&
		assnEq(a.L, b.L) && assnEq(a.R, b.R)
}

// lowerPre parses and lowers a precondition in a fresh scope.
func lowerPre(t *testing.T, ps []translate.ParamInfo, src string) (*spec.Scope, *checker.Assn, error) {
	t.Helper()
	sc, err := spec.NewScope(ps)
	if err != nil {
		return nil, nil, err
	}
	s, err := spec.Parse(src)
	if err != nil {
		return nil, nil, err
	}
	a, err := sc.LowerPre(s)
	return sc, a, err
}

// lowerPost lowers pre and then post in a fresh scope.
func lowerPost(t *testing.T, ps []translate.ParamInfo, pre, post string) (*spec.Scope, *checker.Assn, error) {
	t.Helper()
	sc, _, err := lowerPre(t, ps, pre)
	if err != nil {
		return nil, nil, err
	}
	s, err := spec.Parse(post)
	if err != nil {
		return nil, nil, err
	}
	a, err := sc.LowerPost(s)
	return sc, a, err
}

// TestNoASCII checks that the ASCII spellings of Iris notation are rejected:
// assertions are written in Iris's Unicode notation only.
func TestNoASCII(t *testing.T) {
	for _, src := range []string{
		"z |-> z0",
		"[x == 0] ∗ z ↦ z0",
		"⌜x == 0⌝ * z ↦ z0",
		"exists v, z ↦ v",
		`⌜x == 0⌝ \/ z ↦ z0`,
	} {
		if _, err := spec.Parse(src); err == nil {
			t.Errorf("%q: parsed, want an error", src)
		}
	}
}

// TestRoundTrip checks that the renderer's output parses back to the same
// assertion.
func TestRoundTrip(t *testing.T) {
	srcs := []string{
		"⌜x == 0⌝ ∗ z ↦ 37 + 37",
		"⌜x != 0⌝ ∗ z ↦ x + x",
		"⌜¬(x == 0)⌝",
		"z ↦ if x == 0 then 37 else x",
	}
	for _, src := range srcs {
		sc, a, err := lowerPre(t, doubleParams(), src)
		if err != nil {
			t.Fatalf("%s: %v", src, err)
		}
		pr := &render.Printer{Names: sc.Names}
		printed := pr.Assn(a)
		_, b, err := lowerPre(t, doubleParams(), printed)
		if err != nil {
			t.Fatalf("%s: reparsing %q: %v", src, printed, err)
		}
		if !assnEq(a, b) {
			t.Errorf("%s: printed as %q, which lowers differently", src, printed)
		}
	}
}

func pure(x *checker.Term) *checker.Assn {
	return &checker.Assn{Kind: checker.APure, X: x}
}

func term(k checker.TermKind, a, b *checker.Term) *checker.Term {
	return &checker.Term{Kind: k, A: a, B: b}
}

func tvar(n uint64) *checker.Term  { return &checker.Term{Kind: checker.TVar, Num: n} }
func tint(n uint64) *checker.Term  { return &checker.Term{Kind: checker.TInt, Num: n} }
func tbool(n uint64) *checker.Term { return &checker.Term{Kind: checker.TBool, Num: n} }

// TestDesugar pins down the desugaring of the derived operators.
func TestDesugar(t *testing.T) {
	cases := []struct {
		src  string
		want *checker.Assn
	}{
		{"⌜x != 0⌝", pure(&checker.Term{Kind: checker.TNot,
			A: term(checker.TEq, tvar(0), tint(0))})},
		{"⌜x == -5⌝", pure(term(checker.TEq, tvar(0),
			&checker.Term{Kind: checker.TNeg, A: tint(5)}))},
		{"⌜x <s 1 && x >s 0⌝", pure(&checker.Term{Kind: checker.TIte,
			A: term(checker.TLtS, tvar(0), tint(1)),
			B: &checker.Term{Kind: checker.TNot,
				A: term(checker.TLeS, tvar(0), tint(0))},
			C: tbool(0)})},
		{"⌜x <s 1 || x >=s 2⌝", pure(&checker.Term{Kind: checker.TIte,
			A: term(checker.TLtS, tvar(0), tint(1)),
			B: tbool(1),
			C: &checker.Term{Kind: checker.TNot,
				A: term(checker.TLtS, tvar(0), tint(2))}})},
		{"⌜x <=s 3⌝", pure(term(checker.TLeS, tvar(0), tint(3)))},
		{"⌜!(x == 0)⌝", pure(&checker.Term{Kind: checker.TNot,
			A: term(checker.TEq, tvar(0), tint(0))})},
		{"z ↦ 1 + 2 ∗ 3", &checker.Assn{Kind: checker.APointsTo, X: tvar(1),
			Y: term(checker.TAdd, tint(1), term(checker.TMul, tint(2), tint(3)))}},
	}
	for _, c := range cases {
		_, got, err := lowerPre(t, doubleParams(), c.src)
		if err != nil {
			t.Errorf("%s: %v", c.src, err)
			continue
		}
		if !assnEq(got, c.want) {
			pr := &render.Printer{}
			t.Errorf("%s lowered to %s, want %s", c.src, pr.Assn(got), pr.Assn(c.want))
		}
	}
}

// TestSignedness checks that the signedness of a comparison follows the Go
// type of its operands.
func TestSignedness(t *testing.T) {
	_, a, err := lowerPre(t, maxParams(), "⌜a < b⌝")
	if err != nil {
		t.Fatal(err)
	}
	if a.X.Kind != checker.TLtU {
		t.Errorf("uint64 comparison lowered to kind %d, want TLtU", uint64(a.X.Kind))
	}
	_, a, err = lowerPre(t, absParams(), "⌜x <= 0⌝")
	if err != nil {
		t.Fatal(err)
	}
	if a.X.Kind != checker.TLeS {
		t.Errorf("int comparison lowered to kind %d, want TLeS", uint64(a.X.Kind))
	}
	// The Go type of a ghost reached through a points-to is known too.
	_, a, err = lowerPre(t, condStoreParams(), "p ↦ v0 ∗ ⌜v0 < v⌝")
	if err != nil {
		t.Fatal(err)
	}
	if a.R.X.Kind != checker.TLtU {
		t.Errorf("ghost comparison lowered to kind %d, want TLtU", uint64(a.R.X.Kind))
	}
}

// TestPreVars checks that a precondition's free names become logical
// variables with the next indices, and that their sorts are inferred.
func TestPreVars(t *testing.T) {
	sc, a, err := lowerPre(t, doubleParams(), "z ↦ z0 ∗ ⌜z0 == w⌝")
	if err != nil {
		t.Fatal(err)
	}
	want := []string{"x", "z", "z0", "w"}
	if strings.Join(sc.Names, ",") != strings.Join(want, ",") {
		t.Fatalf("names are %v, want %v", sc.Names, want)
	}
	vars := sc.Vars()
	wantSorts := []checker.Sort{checker.SortInt, checker.SortLoc, checker.SortInt, checker.SortInt}
	for i := range wantSorts {
		if vars[i] != wantSorts[i] {
			t.Errorf("var %d has sort %s, want %s", i,
				render.SortName(vars[i]), render.SortName(wantSorts[i]))
		}
	}
	if a.Kind != checker.ASep {
		t.Errorf("lowered to kind %d, want ASep", uint64(a.Kind))
	}
	// The lifted ∃ of a precondition leaves no AExists behind.
	_, b, err := lowerPre(t, doubleParams(), "∃ v, z ↦ v")
	if err != nil {
		t.Fatal(err)
	}
	if b.Kind != checker.APointsTo {
		t.Errorf("∃ in a precondition lowered to kind %d, want APointsTo", uint64(b.Kind))
	}
}

// TestPatIndices checks that pattern variables are numbered from 0 within
// each disjunct, in binder order.
func TestPatIndices(t *testing.T) {
	sc, a, err := lowerPost(t, params([]string{"p", "q"},
		[]*checker.Type{ptr(tU64), ptr(tU64)}), "emp", "∃ v w, p ↦ v ∗ q ↦ w")
	if err != nil {
		t.Fatal(err)
	}
	if a.Kind != checker.AExists || a.Var != 0 || a.L.Kind != checker.AExists || a.L.Var != 1 {
		pr := &render.Printer{Names: sc.Names}
		t.Fatalf("binders lowered as %s", pr.Assn(a))
	}
	body := a.L.L
	if body.L.Y.Kind != checker.TPat || body.L.Y.Num != 0 {
		t.Errorf("first value is %+v, want pattern variable 0", body.L.Y)
	}
	if body.R.Y.Kind != checker.TPat || body.R.Y.Num != 1 {
		t.Errorf("second value is %+v, want pattern variable 1", body.R.Y)
	}
	if names := sc.PatNames(0); strings.Join(names, ",") != "v,w" {
		t.Errorf("pattern names are %v, want [v w]", names)
	}

	// Each disjunct numbers its own pattern variables from 0.
	sc, a, err = lowerPost(t, params([]string{"p", "q"},
		[]*checker.Type{ptr(tU64), ptr(tU64)}), "emp",
		"(∃ v, p ↦ v) ∨ (∃ w, q ↦ w)")
	if err != nil {
		t.Fatal(err)
	}
	if a.Kind != checker.AOr {
		t.Fatalf("lowered to kind %d, want AOr", uint64(a.Kind))
	}
	if a.L.Var != 0 || a.R.Var != 0 {
		t.Errorf("disjunct binders are %d and %d, want 0 and 0", a.L.Var, a.R.Var)
	}
	if got := strings.Join(sc.PatNames(1), ","); got != "w" {
		t.Errorf("second disjunct's pattern names are %q, want \"w\"", got)
	}
}

// TestErrors checks the error cases.
func TestErrors(t *testing.T) {
	cases := []struct {
		name  string
		ps    []translate.ParamInfo
		post  bool
		pre   string
		src   string
		match string
	}{
		{name: "orInPre", ps: doubleParams(), src: "z ↦ z0 ∨ emp",
			match: "not allowed in a precondition"},
		{name: "retInPre", ps: maxParams(), src: "⌜ret == a⌝",
			match: "only allowed in a postcondition"},
		{name: "unknownInPost", ps: maxParams(), post: true, pre: "emp",
			src: "⌜ret == c⌝", match: "unknown name"},
		{name: "missingSignedness", ps: maxParams(), post: true, pre: "emp",
			src: "⌜ret < 5⌝", match: "cannot determine signedness of <"},
		{name: "sortMismatch", ps: doubleParams(), post: true, pre: "z ↦ z0",
			src: "⌜x && z0⌝", match: "sort mismatch"},
		{name: "unknownSort", ps: doubleParams(), src: "⌜n == m⌝",
			match: "cannot determine the sort"},
		{name: "existsInsidePost", ps: condStoreParams(), post: true, pre: "p ↦ v0",
			src: "p ↦ v0 ∗ ∃ w, ⌜w == v⌝", match: "∃ must come first"},
		{name: "orInsidePost", ps: maxParams(), post: true, pre: "emp",
			src: "⌜ret == a⌝ ∗ (⌜ret == b⌝ ∨ emp)", match: "only allowed at the top level"},
		{name: "bareTerm", ps: maxParams(), src: "a", match: "needs ↦"},
		{name: "badChar", ps: maxParams(), src: "a ↦ b #", match: "unexpected character"},
		{name: "unclosedPure", ps: maxParams(), src: "⌜a == b", match: `expected "⌝"`},
		{name: "trailing", ps: maxParams(), src: "emp emp", match: "unexpected"},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			var err error
			if c.post {
				_, _, err = lowerPost(t, c.ps, c.pre, c.src)
			} else {
				_, _, err = lowerPre(t, c.ps, c.src)
			}
			if err == nil {
				t.Fatalf("%s: expected an error", c.src)
			}
			if !strings.Contains(err.Error(), c.match) {
				t.Fatalf("%s: error %q does not contain %q", c.src, err, c.match)
			}
		})
	}
}

// TestSepVersusMul checks that ∗ is read as separating conjunction between
// points-to atoms and as multiplication inside a value.
func TestSepVersusMul(t *testing.T) {
	ps := params([]string{"p", "q"}, []*checker.Type{ptr(tU64), ptr(tU64)})
	_, a, err := lowerPre(t, ps, "p ↦ a ∗ q ↦ b")
	if err != nil {
		t.Fatal(err)
	}
	if a.Kind != checker.ASep || a.L.Kind != checker.APointsTo || a.R.Kind != checker.APointsTo {
		pr := &render.Printer{}
		t.Fatalf("p ↦ a ∗ q ↦ b lowered to %s", pr.Assn(a))
	}
	_, b, err := lowerPre(t, ps, "p ↦ a ∗ a")
	if err != nil {
		t.Fatal(err)
	}
	if b.Kind != checker.APointsTo || b.Y.Kind != checker.TMul {
		pr := &render.Printer{}
		t.Fatalf("p ↦ a ∗ a lowered to %s", pr.Assn(b))
	}
}

// lowerTerm parses and lowers a standalone term in the scope that pre built.
func lowerTerm(t *testing.T, ps []translate.ParamInfo, pre, src string) (*checker.Term, error) {
	t.Helper()
	sc, _, err := lowerPre(t, ps, pre)
	if err != nil {
		return nil, err
	}
	s, err := spec.ParseTerm(src)
	if err != nil {
		return nil, err
	}
	return sc.LowerTerm(s)
}

// TestParseTerm checks the standalone term entry point: a term of any sort,
// including `ret`, lowered against a scope that it may not extend.
func TestParseTerm(t *testing.T) {
	cases := []struct {
		name string
		ps   []translate.ParamInfo
		pre  string
		src  string
		want *checker.Term
	}{
		{name: "int", ps: doubleParams(), pre: "emp", src: "37 + 37",
			want: &checker.Term{Kind: checker.TAdd,
				A: &checker.Term{Kind: checker.TInt, Num: 37},
				B: &checker.Term{Kind: checker.TInt, Num: 37}}},
		{name: "loc", ps: doubleParams(), pre: "emp", src: "z",
			want: &checker.Term{Kind: checker.TVar, Num: 1}},
		{name: "ghost", ps: doubleParams(), pre: "z ↦ z0", src: "z0",
			want: &checker.Term{Kind: checker.TVar, Num: 2}},
		{name: "unit", ps: nil, pre: "emp", src: "()",
			want: &checker.Term{Kind: checker.TUnit}},
		{name: "unsigned", ps: maxParams(), pre: "emp", src: "a >=u b",
			want: &checker.Term{Kind: checker.TNot, A: &checker.Term{Kind: checker.TLtU,
				A: &checker.Term{Kind: checker.TVar, Num: 0},
				B: &checker.Term{Kind: checker.TVar, Num: 1}}}},
		{name: "ret", ps: absParams(), pre: "emp", src: "ret == -x",
			want: &checker.Term{Kind: checker.TEq,
				A: &checker.Term{Kind: checker.TResult},
				B: &checker.Term{Kind: checker.TNeg,
					A: &checker.Term{Kind: checker.TVar, Num: 0}}}},
	}
	for _, c := range cases {
		t.Run(c.name, func(t *testing.T) {
			got, err := lowerTerm(t, c.ps, c.pre, c.src)
			if err != nil {
				t.Fatalf("%s: %v", c.src, err)
			}
			if !checker.TermEq(got, c.want) {
				pr := &render.Printer{}
				t.Fatalf("%s lowered to %s", c.src, pr.Term(got))
			}
		})
	}
}

// TestParseTermErrors checks that a term may not introduce a logical variable
// and that trailing input is reported.
func TestParseTermErrors(t *testing.T) {
	cases := []struct{ src, match string }{
		{src: "nosuch", match: "unknown name"},
		{src: "x +", match: "expected a term"},
		{src: "x 1", match: "after the term"},
	}
	for _, c := range cases {
		t.Run(c.src, func(t *testing.T) {
			_, err := lowerTerm(t, absParams(), "emp", c.src)
			if err == nil {
				t.Fatalf("%s: expected an error", c.src)
			}
			if !strings.Contains(err.Error(), c.match) {
				t.Fatalf("%s: error %q does not contain %q", c.src, err, c.match)
			}
		})
	}
}
