package translate_test

import (
	"testing"

	"github.com/mit-pdos/perennial/checker"
	"github.com/mit-pdos/perennial/gocheck/translate"
)

func ptr(t *checker.Type) *checker.Type { return &checker.Type{Kind: checker.TyPtr, Elem: t} }

var (
	tInt  = &checker.Type{Kind: checker.TyInt}
	tU64  = &checker.Type{Kind: checker.TyUint64}
	tBool = &checker.Type{Kind: checker.TyBool}
)

func tyEq(a, b *checker.Type) bool {
	if a == nil || b == nil {
		return a == b
	}
	if a.Kind != b.Kind {
		return false
	}
	return tyEq(a.Elem, b.Elem)
}

func load(t *testing.T) *translate.Package {
	t.Helper()
	pkg, err := translate.LoadPackage("../../new/code", "../..", "./checker/examples")
	if err != nil {
		t.Fatalf("LoadPackage: %v", err)
	}
	return pkg
}

func TestExamples(t *testing.T) {
	pkg := load(t)
	type param struct {
		name string
		ty   *checker.Type
	}
	cases := []struct {
		fn     string
		params []param
	}{
		{"Double", []param{{"x", tInt}, {"z", ptr(tInt)}}},
		{"Max", []param{{"a", tU64}, {"b", tU64}}},
		{"Swap", []param{{"p", ptr(tU64)}, {"q", ptr(tU64)}}},
		{"Abs", []param{{"x", tInt}}},
		{"CondStore", []param{{"flag", tBool}, {"p", ptr(tU64)}, {"v", tU64}}},
	}
	for _, c := range cases {
		f, infos, err := pkg.Func(c.fn)
		if err != nil {
			t.Errorf("%s: %v", c.fn, err)
			continue
		}
		if f.Body == nil || f.Body.Kind != checker.EExcDo {
			t.Errorf("%s: body is not exception_do", c.fn)
		}
		if len(f.Params) != len(c.params) {
			t.Errorf("%s: %d params, want %d", c.fn, len(f.Params), len(c.params))
			continue
		}
		if len(infos) != len(c.params) {
			t.Errorf("%s: %d ParamInfos, want %d", c.fn, len(infos), len(c.params))
			continue
		}
		for i, want := range c.params {
			if f.Params[i] != want.name {
				t.Errorf("%s: param %d is %q, want %q", c.fn, i, f.Params[i], want.name)
			}
			got := infos[i]
			if got.Name != want.name || got.Index != i {
				t.Errorf("%s: ParamInfo %d = %+v, want name %q index %d",
					c.fn, i, got, want.name, i)
			}
			if !tyEq(got.Ty, want.ty) {
				t.Errorf("%s: param %q has type %+v, want %+v", c.fn, want.name, got.Ty, want.ty)
			}
		}
	}
}

func TestUnknownFunc(t *testing.T) {
	pkg := load(t)
	if _, _, err := pkg.Func("Nope"); err == nil {
		t.Fatal("expected an error for an unknown function")
	}
}

// TestDoubleShape pins down the shape of the translated body: the parameter
// allocation prologue is kept, and the store at the end is an EStore of an
// EBinOp.
func TestDoubleShape(t *testing.T) {
	pkg := load(t)
	f, _, err := pkg.Func("Double")
	if err != nil {
		t.Fatal(err)
	}
	e := f.Body.A // under exception_do
	if e.Kind != checker.ELet || e.Name != "z" {
		t.Fatalf("first binding is %v %q, want a let of z", e.Kind, e.Name)
	}
	if e.A.Kind != checker.EAlloc {
		t.Fatalf("z is bound to %v, want EAlloc", e.A.Kind)
	}
	var sawStore, sawIf bool
	var walk func(*checker.Expr)
	walk = func(x *checker.Expr) {
		if x == nil {
			return
		}
		switch x.Kind {
		case checker.EStore:
			sawStore = true
		case checker.EIf:
			sawIf = true
		}
		walk(x.A)
		walk(x.B)
		walk(x.C)
	}
	walk(f.Body)
	if !sawStore || !sawIf {
		t.Fatalf("Double: sawStore=%v sawIf=%v", sawStore, sawIf)
	}
}
