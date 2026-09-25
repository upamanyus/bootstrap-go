package rocqgoal_test

import (
	"os"
	"path/filepath"
	"strings"
	"testing"

	"github.com/mit-pdos/perennial/gocheck/rocqgoal"
)

// The inputs are exports of the goals in new/proof/rocqgoal/examples/,
// written by testdata/regen.sh.

func load(t *testing.T, name string) (string, *rocqgoal.Goal) {
	t.Helper()
	b, err := os.ReadFile(filepath.Join("testdata", name+".sexp"))
	if err != nil {
		t.Fatal(err)
	}
	src := strings.TrimSpace(string(b))
	g, err := rocqgoal.Parse(src)
	if err != nil {
		t.Fatalf("%s: %v", name, err)
	}
	return src, g
}

func has(t *rocqgoal.Term, f func(*rocqgoal.Term) bool) bool {
	return !rocqgoal.Walk(t, func(u *rocqgoal.Term) bool { return !f(u) })
}

func TestRoundTrip(t *testing.T) {
	files, err := filepath.Glob(filepath.Join("testdata", "*.sexp"))
	if err != nil || len(files) == 0 {
		t.Fatalf("no test inputs: %v", err)
	}
	for _, f := range files {
		name := strings.TrimSuffix(filepath.Base(f), ".sexp")
		src, g := load(t, name)
		if got := g.String(); got != src {
			t.Errorf("%s: printing the parse does not give the input back", name)
		}
	}
}

func TestSmallLet(t *testing.T) {
	_, g := load(t, "small_let")
	n := g.Hyp("n")
	if n == nil || n.Body == nil {
		t.Fatalf("n should be a let-bound hypothesis: %+v", n)
	}
	for name, sort := range map[string]string{"X": "Set", "Y": "SProp"} {
		if h := g.Hyp(name); h == nil || h.Type.Kind != rocqgoal.Sort || h.Type.Name != sort {
			t.Errorf("%s should be a %s", name, sort)
		}
	}
	if !has(g.Hyp("H1").Type, func(u *rocqgoal.Term) bool {
		return u.Kind == rocqgoal.Case && u.Name == "Corelib.Init.Datatypes.bool"
	}) {
		t.Errorf("H1 should match on a bool")
	}
	if !has(g.Hyp("H2").Type, func(u *rocqgoal.Term) bool {
		return u.Kind == rocqgoal.Fix && len(u.Binders) == 1 && u.Binders[0].Name == "f"
	}) {
		t.Errorf("H2 should contain fix f")
	}
	if c := g.Concl; c.Kind != rocqgoal.Prod || c.Binders[0].Type.Name != "Prop" || c.Args[0].Name != "Type" {
		t.Errorf("the conclusion should be Prop -> Type, got %s", c)
	}
}

func TestSmallPrim(t *testing.T) {
	_, g := load(t, "small_prim")
	if !has(g.Hyp("Hs").Type, func(u *rocqgoal.Term) bool {
		return u.Kind == rocqgoal.String && u.Name == "a\"b\\é"
	}) {
		t.Errorf("Hs should contain the string a\"b\\é: %s", g.Hyp("Hs").Type)
	}
	if !has(g.Hyp("Hi").Type, func(u *rocqgoal.Term) bool { return u.Kind == rocqgoal.Uint63 && u.Num == 42 }) {
		t.Errorf("Hi should contain 42")
	}
	if !has(g.Hyp("Hi").Type, func(u *rocqgoal.Term) bool { return u.Kind == rocqgoal.Lambda && u.Binders[0].Name == "x" }) {
		t.Errorf("Hi should contain fun x => _")
	}
	if !has(g.Hyp("Ha").Type, func(u *rocqgoal.Term) bool {
		return u.Kind == rocqgoal.Array && len(u.Args) == 4 && u.Args[1].Num == 0 && u.Args[2].Num == 1 && u.Args[3].Num == 2
	}) {
		t.Errorf("Ha should contain [| 1; 2 | 0 |]")
	}
}

func TestSmallProj(t *testing.T) {
	_, g := load(t, "small_proj")
	var names []string
	rocqgoal.Walk(g.Hyp("Hp").Type, func(u *rocqgoal.Term) bool {
		if u.Kind == rocqgoal.Proj {
			names = append(names, u.Name)
		}
		return true
	})
	want := "New.proof.rocqgoal.examples.small.px New.proof.rocqgoal.examples.small.py"
	if got := strings.Join(names, " "); got != want {
		t.Errorf("projections: got %q, want %q", got, want)
	}
}

func TestMedian3WpAuto(t *testing.T) {
	_, g := load(t, "median3_wp_auto")
	ipm, err := g.IPM()
	if err != nil {
		t.Fatal(err)
	}
	if len(ipm.Persistent) != 1 || ipm.Persistent[0].Name != "" {
		t.Fatalf("persistent context: want one anonymous hypothesis, got %+v", ipm.Persistent)
	}
	if head, _ := rocqgoal.Head(ipm.Persistent[0].Prop); head != "New.golang.theory.pkg.is_pkg_init" {
		t.Errorf("the persistent hypothesis should be is_pkg_init, got %s", head)
	}
	var labels, pts []string
	for _, h := range ipm.Spatial {
		labels = append(labels, h.Label())
		if p, ok := rocqgoal.AsPointsTo(h.Prop); ok {
			pts = append(pts, rocqgoal.Short(p.Loc, 0)+" ↦ "+rocqgoal.Short(p.Val, 0)+" : "+rocqgoal.Short(p.Type, 0))
		}
	}
	if got := strings.Join(labels, " "); got != "HΦ x y z" {
		t.Errorf("spatial context: got %q, want %q", got, "HΦ x y z")
	}
	want := "x_ptr ↦ a : w64, y_ptr ↦ b : w64, z_ptr ↦ c : w64"
	if got := strings.Join(pts, ", "); got != want {
		t.Errorf("points-to facts: got %q, want %q", got, want)
	}
	if _, ok := rocqgoal.AsWP(ipm.Goal); !ok {
		t.Errorf("the goal should be a WP, got %s", rocqgoal.Short(ipm.Goal, 80))
	}
}

func TestMedian3Path(t *testing.T) {
	_, g := load(t, "median3_path")
	ipm, err := g.IPM()
	if err != nil {
		t.Fatal(err)
	}
	if _, ok := rocqgoal.AsWP(ipm.Goal); ok {
		t.Errorf("a path goal is past the WP")
	}
	// the path condition is in the Rocq context
	var conds int
	for _, h := range g.Hyps {
		if head, _ := rocqgoal.Head(h.Type); head == "Stdlib.ZArith.BinInt.Z.lt" || head == "Stdlib.ZArith.BinInt.Z.le" {
			conds++
		}
	}
	if conds == 0 {
		t.Errorf("no path condition in the Rocq context")
	}
}

func TestParseErrors(t *testing.T) {
	for _, src := range []string{
		"",
		"(Goal (Concl Prop)",
		"(Goal (Concl Prop)))",
		"(Goal (Hyp x Prop))",
		"(Goal (Concl (Q 1)))",
		"(Goal (Concl (R x)))",
		`(Goal (Concl (Str "abc)))`,
		"(Goal (Concl (Fix 0 (f Prop))))",
		"(Goal (Concl Prop) (Hyp x Prop))",
	} {
		if _, err := rocqgoal.Parse(src); err == nil {
			t.Errorf("Parse(%q) should fail", src)
		}
	}
}

func TestShort(t *testing.T) {
	tm, err := rocqgoal.ParseTerm("(Pi (x (I Corelib.Init.Datatypes.nat)) (A (I Corelib.Init.Logic.eq) (I Corelib.Init.Datatypes.nat) (R 1) (V y)))")
	if err != nil {
		t.Fatal(err)
	}
	if got, want := rocqgoal.Short(tm, 0), "∀ x, (eq nat #1 y)"; got != want {
		t.Errorf("Short: got %q, want %q", got, want)
	}
}
