package render

import (
	"fmt"
	"strconv"

	"github.com/upamanyus/bootstrap-go/checker"
)

// Reason returns a one-line explanation of why the checker rejected an input.
func (p *Printer) Reason(f *checker.Failure) string {
	if f == nil {
		return "no failure"
	}
	switch f.Reason {
	case checker.RUnboundVar:
		return fmt.Sprintf("variable %s is not in scope", strconv.Quote(f.Name))
	case checker.RBadType:
		return "unsupported Go type at a load, store, allocation or operator"
	case checker.RIllSorted:
		return "a term has the wrong sort"
	case checker.RNoPointsTo:
		if f.Expr != nil && f.Expr.Kind == checker.EStore {
			return "store to a location not owned in the symbolic heap"
		}
		if f.Expr != nil && f.Expr.Kind == checker.ELoad {
			return "load from a location not owned in the symbolic heap"
		}
		return "access to a location not owned in the symbolic heap"
	case checker.RBadConvert:
		return "conversion between two different types"
	case checker.RBadMonad:
		return "an exception-monad operation was applied to a plain value"
	case checker.RUnsupported:
		return "expression form not handled by the checker"
	case checker.RPreHasOr:
		return "the precondition contains " + p.Or()
	case checker.RPreHasExists:
		return "the precondition contains " + p.exists()
	case checker.RVarsTooShort:
		return "fewer logical variables than the function has parameters"
	case checker.RPostNoDisjunct:
		return "no disjunct of the postcondition matched this path"
	case checker.RPostCellMissing:
		return "the postcondition claims a heap cell the path does not own"
	case checker.RPostValueMismatch:
		return "the heap cell holds a different value than the postcondition claims"
	case checker.RPostPureMissing:
		return "the pure fact is not among this path's conditions"
	case checker.RPatUnbound:
		return "a pattern variable is never bound by a points-to atom"
	case checker.RPatConflict:
		return "a pattern variable would have to denote two different terms"
	}
	return fmt.Sprintf("failure reason %d", uint64(f.Reason))
}

// FailureLines returns the reason plus one line per piece of evidence.
func (p *Printer) FailureLines(f *checker.Failure) []string {
	if f == nil {
		return nil
	}
	lines := []string{p.Reason(f)}
	if f.Expr != nil {
		lines = append(lines, "expression: "+p.Expr(f.Expr))
	}
	if f.Atom != nil {
		lines = append(lines, "assertion:  "+p.Assn(f.Atom))
	}
	if f.Want != nil {
		lines = append(lines, "expected:   "+p.Term(f.Want))
	}
	if f.Got != nil {
		lines = append(lines, "found:      "+p.Term(f.Got))
	}
	return lines
}
