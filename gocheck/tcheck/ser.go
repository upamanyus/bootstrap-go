package main

import (
	"fmt"
	"strings"

	"github.com/upamanyus/bootstrap-go/tcheck"
)

// ser writes an input in the format tcheck.Parse reads; it must agree with
// [ser_input] (new/tcheck/syntax.v) byte for byte, which every generated
// observation file checks by computation.

func serSort(s tcheck.Sort) string {
	switch s.Kind {
	case tcheck.SortVal:
		return "v"
	case tcheck.SortType:
		return "y"
	}
	return fmt.Sprintf("(u %d)", s.Num)
}

func serList[A any](f func(A) string, l []A) string {
	if len(l) == 0 {
		return "()"
	}
	var parts []string
	for _, x := range l {
		parts = append(parts, f(x))
	}
	return "(" + strings.Join(parts, " ") + ")"
}

func serTail[A any](f func(A) string, l []A) string {
	var b strings.Builder
	for _, x := range l {
		b.WriteString(" ")
		b.WriteString(f(x))
	}
	return b.String()
}

func serTerm(t *tcheck.Term) string {
	switch t.Kind {
	case tcheck.TVar:
		return fmt.Sprintf("(var %d)", t.Num)
	case tcheck.TSym:
		return fmt.Sprintf("(sym %d", t.Num) + serTail(serTerm, t.Args) + ")"
	case tcheck.TPair:
		return "(pair " + serTerm(t.Args[0]) + " " + serTerm(t.Args[1]) + ")"
	case tcheck.TLit:
		return "(lit " + serTerm(t.Args[0]) + serTail(serTerm, t.Args[1:]) + ")"
	}
	return "unit"
}

func serPat(p *tcheck.Pat) string {
	if p.Kind == tcheck.PVal {
		return "(pval " + serTerm(p.T) + ")"
	}
	return "(papp " + serPat(p.A) + " " + serPat(p.B) + ")"
}

func serAtom(a *tcheck.Atom) string {
	if a.Kind == tcheck.APred {
		return fmt.Sprintf("(pred %d", a.Num) + serTail(serTerm, a.Args) + ")"
	}
	return "(eq " + serTerm(a.Args[0]) + " " + serTerm(a.Args[1]) + ")"
}

func serStr(x string) string { return "\"" + x + "\"" }

func serExpr(e *tcheck.Expr) string {
	switch e.Kind {
	case tcheck.EVal:
		return "(val " + serTerm(e.T) + ")"
	case tcheck.EVar:
		return "(cvar " + serStr(e.Name) + ")"
	case tcheck.EApp:
		return "(app " + serExpr(e.A) + " " + serExpr(e.B) + ")"
	case tcheck.EPair:
		return "(cpair " + serExpr(e.A) + " " + serExpr(e.B) + ")"
	case tcheck.ELet:
		return "(let " + serStr(e.Name) + " " + serExpr(e.A) + " " + serExpr(e.B) + ")"
	case tcheck.ESeq:
		return "(seq " + serExpr(e.A) + " " + serExpr(e.B) + ")"
	case tcheck.ELit:
		return "(clit " + serTerm(e.T) + serTail(serExpr, e.Elems) + ")"
	case tcheck.EDo:
		return "(do " + serExpr(e.A) + ")"
	case tcheck.ERet:
		return "(ret " + serExpr(e.A) + ")"
	case tcheck.EXSeq:
		return "(xseq " + serExpr(e.A) + " " + serExpr(e.B) + ")"
	case tcheck.EXDo:
		return "(xdo " + serExpr(e.A) + ")"
	}
	panic("serExpr")
}

func serInput(i *tcheck.Input) string {
	sym := func(d tcheck.SymDecl) string {
		return "(sym " + serList(serSort, d.Args) + " " + serSort(d.Res) + ")"
	}
	pred := func(d tcheck.PredDecl) string {
		b := "0"
		if d.Pers {
			b = "1"
		}
		return "(pred " + b + " " + serList(serSort, d.Args) + ")"
	}
	rule := func(r *tcheck.Rule) string {
		return "(rule " + serList(serSort, r.Vars) + " " + serPat(r.Lhs) + " " + serList(serAtom, r.Pre) +
			" " + serList(serSort, r.Ex) + " " + serTerm(r.Ret) + " " + serList(serAtom, r.Post) + ")"
	}
	fact := func(f *tcheck.Fact) string {
		return "(fact " + serList(serSort, f.Vars) + " " + serTerm(f.Lhs) + " " + serTerm(f.Rhs) + ")"
	}
	sp := i.Sp
	return "(input (syms" + serTail(sym, i.Syms) + ") (preds" + serTail(pred, i.Preds) +
		") (rules" + serTail(rule, i.Rules) + ") (facts" + serTail(fact, i.Facts) + ") " +
		"(func " + serList(serStr, i.Fn.Params) + " " + serExpr(i.Fn.Body) + ") " +
		"(spec " + serList(serSort, sp.Vars) + " " + serList(serTerm, sp.Args) + " " +
		serList(serAtom, sp.Pre) + " " + serList(serSort, sp.Ex) + " " + serTerm(sp.Ret) + " " +
		serList(serAtom, sp.Post) + "))"
}
