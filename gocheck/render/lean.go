package render

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/upamanyus/bootstrap-go/checker"
)

// Lean renders the checker's input as Lean terms over the mirror of the
// input syntax in Checkers/Checker/Defs.lean (cfunc, cexpr, ctype, cassn,
// term, sort). The terms are exactly the trees gocheck hands to
// checker.Check, so a Lean statement about them is a statement about this run
// of the checker.

// LeanFile renders the definitions `<name>_func`, `<name>_vars`,
// `<name>_pre` and `<name>_post`.
func LeanFile(name string, f *checker.Func, vars []checker.Sort, pre, post *checker.Assn) string {
	var b strings.Builder
	fmt.Fprintf(&b, "def %s_func : cfunc :=\n  %s\n\n", name, LeanFunc(f))
	fmt.Fprintf(&b, "def %s_vars : List sort := %s\n\n", name, LeanSorts(vars))
	fmt.Fprintf(&b, "def %s_pre : cassn :=\n  %s\n\n", name, LeanAssn(pre))
	fmt.Fprintf(&b, "def %s_post : cassn :=\n  %s\n", name, LeanAssn(post))
	return b.String()
}

func leanString(s string) string {
	return "go!" + strconv.Quote(s)
}

func leanW64(n uint64) string {
	return fmt.Sprintf("(W64 %d)", n)
}

func leanBool(n uint64) string {
	if n != 0 {
		return "true"
	}
	return "false"
}

// LeanFunc renders a checker.Func as a cfunc.
func LeanFunc(f *checker.Func) string {
	var ps []string
	for _, p := range f.Params {
		ps = append(ps, leanString(p))
	}
	return fmt.Sprintf("mkFunc [%s]\n    %s", strings.Join(ps, ", "), LeanExpr(f.Body))
}

// LeanSorts renders a sort table.
func LeanSorts(vars []checker.Sort) string {
	var ss []string
	for _, s := range vars {
		ss = append(ss, leanSort(s))
	}
	return "[" + strings.Join(ss, ", ") + "]"
}

func leanSort(s checker.Sort) string {
	switch s {
	case checker.SortInt:
		return "SInt"
	case checker.SortBool:
		return "SBool"
	case checker.SortLoc:
		return "SLoc"
	case checker.SortUnit:
		return "SUnit"
	}
	panic(fmt.Sprintf("lean: unknown sort %d", s))
}

func leanType(t *checker.Type) string {
	switch t.Kind {
	case checker.TyInt:
		return "CTyInt"
	case checker.TyInt64:
		return "CTyInt64"
	case checker.TyUint64:
		return "CTyUint64"
	case checker.TyBool:
		return "CTyBool"
	case checker.TyPtr:
		return "(CTyPtr " + leanType(t.Elem) + ")"
	}
	panic(fmt.Sprintf("lean: unknown type kind %d", t.Kind))
}

func leanOp(op checker.Op) string {
	switch op {
	case checker.OpAdd:
		return "COAdd"
	case checker.OpSub:
		return "COSub"
	case checker.OpMul:
		return "COMul"
	case checker.OpEq:
		return "COEq"
	case checker.OpLt:
		return "COLt"
	case checker.OpLe:
		return "COLe"
	case checker.OpGt:
		return "COGt"
	case checker.OpGe:
		return "COGe"
	case checker.OpNeg:
		return "CONeg"
	case checker.OpNot:
		return "CONot"
	}
	panic(fmt.Sprintf("lean: unknown operator %d", op))
}

// LeanExpr renders a checker.Expr as a cexpr.
func LeanExpr(e *checker.Expr) string {
	switch e.Kind {
	case checker.EInt:
		return "(CEInt " + leanW64(e.Num) + ")"
	case checker.EBool:
		return "(CEBool " + leanBool(e.Num) + ")"
	case checker.EUnit:
		return "CEUnit"
	case checker.EVar:
		return "(CEVar " + leanString(e.Name) + ")"
	case checker.ELet:
		return fmt.Sprintf("(CELet %s %s %s)", leanString(e.Name), LeanExpr(e.A), LeanExpr(e.B))
	case checker.ESeq:
		return fmt.Sprintf("(CESeq %s %s)", LeanExpr(e.A), LeanExpr(e.B))
	case checker.EIf:
		return fmt.Sprintf("(CEIf %s %s %s)", LeanExpr(e.A), LeanExpr(e.B), LeanExpr(e.C))
	case checker.ELoad:
		return fmt.Sprintf("(CELoad %s %s)", leanType(e.Ty), LeanExpr(e.A))
	case checker.EStore:
		return fmt.Sprintf("(CEStore %s %s %s)", leanType(e.Ty), LeanExpr(e.A), LeanExpr(e.B))
	case checker.EAlloc:
		return fmt.Sprintf("(CEAlloc %s %s)", leanType(e.Ty), LeanExpr(e.A))
	case checker.EZero:
		return fmt.Sprintf("(CEZero %s)", leanType(e.Ty))
	case checker.EBinOp:
		return fmt.Sprintf("(CEBinOp %s %s %s %s)", leanOp(e.Op), leanType(e.Ty), LeanExpr(e.A), LeanExpr(e.B))
	case checker.EUnOp:
		return fmt.Sprintf("(CEUnOp %s %s %s)", leanOp(e.Op), leanType(e.Ty), LeanExpr(e.A))
	case checker.EConvert:
		return fmt.Sprintf("(CEConvert %s %s %s)", leanType(e.Ty), leanType(e.Ty2), LeanExpr(e.A))
	case checker.EDo:
		return "(CEDo " + LeanExpr(e.A) + ")"
	case checker.EReturn:
		return "(CEReturn " + LeanExpr(e.A) + ")"
	case checker.EExcSeq:
		return fmt.Sprintf("(CEExcSeq %s %s)", LeanExpr(e.A), LeanExpr(e.B))
	case checker.EExcDo:
		return "(CEExcDo " + LeanExpr(e.A) + ")"
	}
	panic(fmt.Sprintf("lean: unknown expression kind %d", e.Kind))
}

// LeanTerm renders a checker.Term as a term.
func LeanTerm(t *checker.Term) string {
	bin := func(c string) string { return fmt.Sprintf("(%s %s %s)", c, LeanTerm(t.A), LeanTerm(t.B)) }
	switch t.Kind {
	case checker.TVar:
		return fmt.Sprintf("(TVar %d)", t.Num)
	case checker.TPat:
		return fmt.Sprintf("(TPat %d)", t.Num)
	case checker.TResult:
		return "TResult"
	case checker.TInt:
		return "(TInt " + leanW64(t.Num) + ")"
	case checker.TBool:
		return "(TBool " + leanBool(t.Num) + ")"
	case checker.TUnit:
		return "TUnit"
	case checker.TNull:
		return "TNull"
	case checker.TAdd:
		return bin("TPlus")
	case checker.TSub:
		return bin("TMinus")
	case checker.TMul:
		return bin("TMul")
	case checker.TNeg:
		return "(TNeg " + LeanTerm(t.A) + ")"
	case checker.TEq:
		return bin("TEq")
	case checker.TLtS:
		return bin("TLt true")
	case checker.TLtU:
		return bin("TLt false")
	case checker.TLeS:
		return bin("TLe true")
	case checker.TLeU:
		return bin("TLe false")
	case checker.TNot:
		return "(TNot " + LeanTerm(t.A) + ")"
	case checker.TIte:
		return fmt.Sprintf("(TIte %s %s %s)", LeanTerm(t.A), LeanTerm(t.B), LeanTerm(t.C))
	case checker.TExec:
		return "TExec"
	case checker.TRet:
		return "(TRet " + LeanTerm(t.A) + ")"
	}
	panic(fmt.Sprintf("lean: unknown term kind %d", t.Kind))
}

// LeanAssn renders a checker.Assn as a cassn.
func LeanAssn(a *checker.Assn) string {
	switch a.Kind {
	case checker.AEmp:
		return "CAEmp"
	case checker.ASep:
		return fmt.Sprintf("(CASep %s %s)", LeanAssn(a.L), LeanAssn(a.R))
	case checker.AOr:
		return fmt.Sprintf("(CAOr %s\n    %s)", LeanAssn(a.L), LeanAssn(a.R))
	case checker.AExists:
		return fmt.Sprintf("(CAExists %d %s %s)", a.Var, leanSort(a.Sort), LeanAssn(a.L))
	case checker.APure:
		return "(CAPure " + LeanTerm(a.X) + ")"
	case checker.APointsTo:
		return fmt.Sprintf("(CAPointsTo %s %s)", LeanTerm(a.X), LeanTerm(a.Y))
	}
	panic(fmt.Sprintf("lean: unknown assertion kind %d", a.Kind))
}
