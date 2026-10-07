// Package render prints checker terms, assertions, states and failures in the
// same notation that the spec parser accepts.
package render

import (
	"fmt"
	"strings"

	"github.com/upamanyus/bootstrap-go/checker"
)

// Printer renders checker data structures. Names gives the source name of
// each logical variable; variables with a higher index were allocated during
// symbolic execution and print as ?lN. Pats gives the names of the pattern
// variables of the assertion being printed, if known.
type Printer struct {
	Names []string
	Pats  []string
	ASCII bool
}

// WithPats returns a copy of p that knows the given pattern-variable names.
func (p *Printer) WithPats(names []string) *Printer {
	q := *p
	q.Pats = names
	return &q
}

func (p *Printer) sym(unicode, ascii string) string {
	if p.ASCII {
		return ascii
	}
	return unicode
}

// Sep is the separating conjunction symbol.
func (p *Printer) Sep() string { return p.sym("∗", "*") }

// PointsTo is the points-to arrow.
func (p *Printer) PointsTo() string { return p.sym("↦", "|->") }

// Or is the disjunction symbol.
func (p *Printer) Or() string { return p.sym("∨", `\/`) }

// Emp is the empty assertion.
func (p *Printer) Emp() string { return "emp" }

// Pure wraps a term as a pure assertion.
func (p *Printer) Pure(s string) string {
	if p.ASCII {
		return "[" + s + "]"
	}
	return "⌜" + s + "⌝"
}

func (p *Printer) not() string { return p.sym("¬", "!") }

func (p *Printer) exists() string { return p.sym("∃", "exists") }

// Var renders logical variable i.
func (p *Printer) Var(i uint64) string {
	if i < uint64(len(p.Names)) && p.Names[i] != "" {
		return p.Names[i]
	}
	return fmt.Sprintf("?l%d", i)
}

// Pat renders pattern variable i.
func (p *Printer) Pat(i uint64) string {
	if i < uint64(len(p.Pats)) && p.Pats[i] != "" {
		return p.Pats[i]
	}
	return fmt.Sprintf("?p%d", i)
}

// term precedence levels
const (
	precIte  = 0
	precCmp  = 1
	precSum  = 2
	precMul  = 3
	precUn   = 4
	precAtom = 5
)

func paren(s string, have, want int) string {
	if have < want {
		return "(" + s + ")"
	}
	return s
}

// Term renders a term.
func (p *Printer) Term(t *checker.Term) string { return p.term(t, precIte) }

func (p *Printer) term(t *checker.Term, want int) string {
	if t == nil {
		return "<nil>"
	}
	bin := func(op string, prec int) string {
		s := fmt.Sprintf("%s %s %s", p.term(t.A, prec), op, p.term(t.B, prec+1))
		return paren(s, prec, want)
	}
	switch t.Kind {
	case checker.TVar:
		return p.Var(t.Num)
	case checker.TPat:
		return p.Pat(t.Num)
	case checker.TResult:
		return "ret"
	case checker.TInt:
		return fmt.Sprintf("%d", t.Num)
	case checker.TBool:
		if t.Num != 0 {
			return "true"
		}
		return "false"
	case checker.TUnit:
		return "()"
	case checker.TNull:
		return "null"
	case checker.TAdd:
		return bin("+", precSum)
	case checker.TSub:
		return bin("-", precSum)
	case checker.TMul:
		return bin(p.Sep(), precMul)
	case checker.TEq:
		return bin("==", precCmp)
	case checker.TLtS:
		return bin("<s", precCmp)
	case checker.TLtU:
		return bin("<u", precCmp)
	case checker.TLeS:
		return bin("<=s", precCmp)
	case checker.TLeU:
		return bin("<=u", precCmp)
	case checker.TNeg:
		return paren("-"+p.term(t.A, precUn), precUn, want)
	case checker.TNot:
		return p.not() + "(" + p.term(t.A, precIte) + ")"
	case checker.TIte:
		s := fmt.Sprintf("if %s then %s else %s",
			p.term(t.A, precIte), p.term(t.B, precIte), p.term(t.C, precIte))
		return paren(s, precIte, want)
	case checker.TExec:
		return "execute"
	case checker.TRet:
		return paren("return "+p.term(t.A, precUn), precUn, want)
	}
	return fmt.Sprintf("<term kind %d>", uint64(t.Kind))
}

// Assn renders an assertion.
func (p *Printer) Assn(a *checker.Assn) string { return p.assn(a, 0) }

func (p *Printer) assn(a *checker.Assn, want int) string {
	if a == nil {
		return "<nil>"
	}
	switch a.Kind {
	case checker.AEmp:
		return p.Emp()
	case checker.ASep:
		s := fmt.Sprintf("%s %s %s", p.assn(a.L, 2), p.Sep(), p.assn(a.R, 1))
		return paren(s, 1, want)
	case checker.AOr:
		var parts []string
		for _, d := range flattenOr(a) {
			parts = append(parts, p.assn(d, 2))
		}
		return paren(strings.Join(parts, " "+p.Or()+" "), 0, want)
	case checker.AExists:
		s := fmt.Sprintf("%s (%s : %s), %s", p.exists(), p.Pat(a.Var),
			SortName(a.Sort), p.assn(a.L, 0))
		return paren(s, 0, want)
	case checker.APure:
		return p.Pure(p.Term(a.X))
	case checker.APointsTo:
		return fmt.Sprintf("%s %s %s", p.term(a.X, precUn), p.PointsTo(), p.term(a.Y, precCmp))
	}
	return fmt.Sprintf("<assn kind %d>", uint64(a.Kind))
}

// flattenOr flattens the top-level disjunction of an assertion, left to right.
func flattenOr(a *checker.Assn) []*checker.Assn {
	if a != nil && a.Kind == checker.AOr {
		return append(flattenOr(a.L), flattenOr(a.R)...)
	}
	return []*checker.Assn{a}
}

// SortName is the surface name of a sort.
func SortName(s checker.Sort) string {
	switch s {
	case checker.SortInt:
		return "int"
	case checker.SortBool:
		return "bool"
	case checker.SortLoc:
		return "ptr"
	case checker.SortUnit:
		return "unit"
	}
	return fmt.Sprintf("sort#%d", uint64(s))
}

// PathAtoms returns the atoms of a path's strongest postcondition: the path
// condition oldest first, then the heap cells, then the return value.
func (p *Printer) PathAtoms(pa checker.Path) []string {
	var atoms []string
	if pa.St != nil {
		for _, c := range pa.St.Cond {
			atoms = append(atoms, p.Pure(p.Term(c)))
		}
		for _, c := range pa.St.Heap {
			atoms = append(atoms, fmt.Sprintf("%s %s %s",
				p.term(c.Loc, precUn), p.PointsTo(), p.term(c.Val, precCmp)))
		}
	}
	if r := retTerm(pa.Ret); r != nil {
		atoms = append(atoms, p.Pure("ret == "+p.Term(r)))
	}
	if len(atoms) == 0 {
		atoms = append(atoms, p.Emp())
	}
	return atoms
}

// retTerm strips the exception-monad wrapper from a path's return term and
// drops an uninformative unit result.
func retTerm(t *checker.Term) *checker.Term {
	if t == nil {
		return nil
	}
	if t.Kind == checker.TExec {
		return nil
	}
	if t.Kind == checker.TRet {
		return retTerm(t.A)
	}
	if t.Kind == checker.TUnit {
		return nil
	}
	return t
}

// Path renders a path's strongest postcondition as one atom per line, joined
// by the separating conjunction. Each line is prefixed with indent.
func (p *Printer) Path(pa checker.Path, indent string) string {
	atoms := p.PathAtoms(pa)
	var b strings.Builder
	for i, a := range atoms {
		b.WriteString(indent)
		b.WriteString(a)
		if i != len(atoms)-1 {
			b.WriteString(" " + p.Sep())
			b.WriteString("\n")
		}
	}
	return b.String()
}

// Heap renders the symbolic heap of a state on one line.
func (p *Printer) Heap(st *checker.State) string {
	if st == nil || len(st.Heap) == 0 {
		return p.Emp()
	}
	var parts []string
	for _, c := range st.Heap {
		parts = append(parts, fmt.Sprintf("%s %s %s",
			p.term(c.Loc, precUn), p.PointsTo(), p.term(c.Val, precCmp)))
	}
	return strings.Join(parts, " "+p.Sep()+" ")
}

// Cond renders the path condition of a state on one line.
func (p *Printer) Cond(st *checker.State) string {
	if st == nil || len(st.Cond) == 0 {
		return "true"
	}
	var parts []string
	for _, c := range st.Cond {
		parts = append(parts, p.Pure(p.Term(c)))
	}
	return strings.Join(parts, " "+p.Sep()+" ")
}

// GoType renders a supported Go type.
func GoType(t *checker.Type) string {
	if t == nil {
		return "?"
	}
	switch t.Kind {
	case checker.TyInt:
		return "int"
	case checker.TyInt64:
		return "int64"
	case checker.TyUint64:
		return "uint64"
	case checker.TyBool:
		return "bool"
	case checker.TyPtr:
		return "*" + GoType(t.Elem)
	}
	return fmt.Sprintf("<type kind %d>", uint64(t.Kind))
}
