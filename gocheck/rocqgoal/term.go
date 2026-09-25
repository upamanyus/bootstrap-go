// Package rocqgoal reads the Rocq goals exported by
// new/proof/rocqgoal/export.v and recognizes Iris proof mode structure in
// them.
//
// The exporter knows nothing about Iris or GooseLang: it prints kernel terms,
// naming every constant, inductive and constructor by its full kernel path.
// All the recognizing happens here, by name, and none of it is trusted: a
// later import step only has to check, in Rocq, that the syntax built from a
// goal denotes it.
package rocqgoal

// Kind identifies the kernel term constructor of a Term.
type Kind int

const (
	Rel       Kind = iota + 1 // de Bruijn index Num, from 1
	Var                       // context variable Name
	Sort                      // Name is "Prop", "SProp", "Set" or "Type"
	Prod                      // ∀ Binders[0], Args[0]
	Lambda                    // λ Binders[0], Args[0]
	LetIn                     // let Binders[0] := Args[0] in Args[1]
	App                       // Args[0] applied to Args[1:]
	Const                     // constant Name
	Ind                       // inductive type Name
	Construct                 // constructor Name
	Case                      // match on inductive Name: Args[0] the return clause, Args[1] the scrutinee, Args[2:] the branches
	Fix                       // Binders the functions, Args their bodies, Num the one this term is
	CoFix                     // as Fix
	Proj                      // primitive projection Name of Args[0]
	Uint63                    // primitive integer Num
	Float                     // primitive float (the exporter drops its value)
	String                    // primitive string Name (the bytes, unescaped)
	Array                     // primitive array: Args[0] its type, Args[1] its default element, Args[2:] its elements
	Evar                      // existential variable
)

var kindNames = map[Kind]string{
	Rel: "Rel", Var: "Var", Sort: "Sort", Prod: "Prod", Lambda: "Lambda",
	LetIn: "LetIn", App: "App", Const: "Const", Ind: "Ind",
	Construct: "Construct", Case: "Case", Fix: "Fix", CoFix: "CoFix",
	Proj: "Proj", Uint63: "Uint63", Float: "Float", String: "String",
	Array: "Array", Evar: "Evar",
}

func (k Kind) String() string {
	if s, ok := kindNames[k]; ok {
		return s
	}
	return "Kind(?)"
}

// Binder is a bound name and its type. Name is "" for an anonymous binder.
type Binder struct {
	Name string
	Type *Term
}

// Term is a kernel term. Which fields are meaningful depends on Kind; see
// the Kind constants.
type Term struct {
	Kind    Kind
	Name    string
	Num     int64
	Binders []Binder
	Args    []*Term
}

// Hyp is a hypothesis of the Rocq context: Name : Type, or Name := Body :
// Type when it is let-bound (Body is nil otherwise).
type Hyp struct {
	Name string
	Body *Term
	Type *Term
}

// Goal is an exported proof state: the Rocq context, oldest hypothesis first,
// and the conclusion.
type Goal struct {
	Hyps  []Hyp
	Concl *Term
}

// Hyp returns the hypothesis called name, or nil.
func (g *Goal) Hyp(name string) *Hyp {
	for i := range g.Hyps {
		if g.Hyps[i].Name == name {
			return &g.Hyps[i]
		}
	}
	return nil
}

// Head returns the name of the constant, inductive or constructor t is, or
// that t applies, together with the arguments it is applied to. It returns
// "" if the head of t is anything else.
func Head(t *Term) (string, []*Term) {
	var args []*Term
	if t.Kind == App {
		t, args = t.Args[0], t.Args[1:]
	}
	switch t.Kind {
	case Const, Ind, Construct:
		return t.Name, args
	}
	return "", args
}

// Walk calls f on t and then on every subterm of t, binder types included,
// until f returns false.
func Walk(t *Term, f func(*Term) bool) bool {
	if !f(t) {
		return false
	}
	for _, b := range t.Binders {
		if !Walk(b.Type, f) {
			return false
		}
	}
	for _, a := range t.Args {
		if !Walk(a, f) {
			return false
		}
	}
	return true
}
