package tcheck

// The checker's input. Every type here has a Rocq mirror in
// new/tcheck/syntax.v, and the serialized form parsed by parse.go is the one
// [ser_input] there produces. Kind codes are part of that interface: do not
// renumber them.

// SortKind classifies sorts.
type SortKind uint64

const (
	SortVal  SortKind = 0 // a GooseLang value (val)
	SortType SortKind = 1 // a Go type (go.type)
	SortUser SortKind = 2 // user sort Num: a Gallina type the table's denotation names
)

// Sort is the sort of a term.
type Sort struct {
	Kind SortKind
	Num  uint64
}

func sortEq(a Sort, b Sort) bool {
	return a.Kind == b.Kind && a.Num == b.Num
}

// TermKind identifies the form of a Term.
type TermKind uint64

const (
	TVar  TermKind = 0 // Num = logical variable index
	TSym  TermKind = 1 // Num = symbol index, Args = its arguments
	TPair TermKind = 2 // Args = [a, b]: the value (a, b)
	TLit  TermKind = 3 // Args = [ty, e1, .., en]: LiteralValueV of elements e1..en at type ty
	TUnit TermKind = 4 // the value #()
)

// Term is a symbolic value. Terms are never mutated after construction.
type Term struct {
	Kind TermKind
	Num  uint64
	Args []*Term
}

// SymDecl declares symbol i: a Gallina function from Args to Res. Constants
// of the code (GoInstruction values, Go types, literals) are nullary symbols.
type SymDecl struct {
	Args []Sort
	Res  Sort
}

// PredDecl declares predicate i, an iProp over arguments of sorts Args.
// A persistent predicate is never consumed when a rule or the
// postcondition uses it; the table's link proves it [Persistent].
type PredDecl struct {
	Pers bool
	Args []Sort
}

// AtomKind identifies an assertion atom.
type AtomKind uint64

const (
	APred AtomKind = 0 // Num = predicate index, Args = its arguments
	AEq   AtomKind = 1 // Args = [a, b]: the pure fact a = b
)

// Atom is one conjunct of an assertion; an assertion is a list of atoms
// joined by ∗.
type Atom struct {
	Kind AtomKind
	Num  uint64
	Args []*Term
}

// PatKind identifies a node of an expression pattern.
type PatKind uint64

const (
	PVal PatKind = 0 // T: a value
	PApp PatKind = 1 // A applied to B
)

// Pat is an expression whose leaves are values: the left-hand side of a
// rule, and the shape the evaluator hands to the rules.
type Pat struct {
	Kind PatKind
	T    *Term
	A    *Pat
	B    *Pat
}

// Rule is a Hoare triple the checker may use:
//
//	∀ vars, {{{ Pre }}} Lhs {{{ ∃ ex, RET Ret; Post }}}
//
// Variables 0..len(Vars)-1 are the rule's parameters, bound by matching Lhs
// and then Pre against the symbolic state; variables len(Vars).. are the
// existentials of the postcondition, and become fresh logical variables.
type Rule struct {
	Vars []Sort
	Lhs  *Pat
	Pre  []*Atom
	Ex   []Sort
	Ret  *Term
	Post []*Atom
}

// Fact is an equation ∀ vars, Lhs = Rhs, used left to right to normalize
// terms.
type Fact struct {
	Vars []Sort
	Lhs  *Term
	Rhs  *Term
}

// ExprKind identifies a node of the code.
type ExprKind uint64

const (
	EVal  ExprKind = 0  // T: a value (a closed term)
	EVar  ExprKind = 1  // Name
	EApp  ExprKind = 2  // A applied to B
	EPair ExprKind = 3  // (A, B)
	ELet  ExprKind = 4  // let: Name := A in B
	ESeq  ExprKind = 5  // A ;; B
	ELit  ExprKind = 6  // LiteralValue of Elems at type T (each element a value or a variable)
	EDo   ExprKind = 7  // do: A
	ERet  ExprKind = 8  // return: A
	EXSeq ExprKind = 9  // A ;;; B
	EXDo  ExprKind = 10 // exception_do A
)

// Expr is the code of a function, as Goose emits it.
type Expr struct {
	Kind  ExprKind
	Name  string
	T     *Term
	A     *Expr
	B     *Expr
	Elems []*Expr
}

// Func is [λ: Params, Body].
type Func struct {
	Params []string
	Body   *Expr
}

// Spec is the triple to establish for the function:
//
//	∀ vars, {{{ Pre }}} f Args {{{ ∃ ex, RET Ret; Post }}}
type Spec struct {
	Vars []Sort
	Args []*Term
	Pre  []*Atom
	Ex   []Sort
	Ret  *Term
	Post []*Atom
}

// Input is everything Check reads.
type Input struct {
	Syms  []SymDecl
	Preds []PredDecl
	Rules []*Rule
	Facts []*Fact
	Fn    *Func
	Sp    *Spec
}
