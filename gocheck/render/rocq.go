package render

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/mit-pdos/perennial/checker"
)

// Rocq renders the checker's input as Gallina terms over the mirror of the
// input syntax in new/checker/defs.v (cfunc, cexpr, ctype, cassn, term,
// sort). The terms are exactly the trees gocheck hands to checker.Check, so a
// Rocq statement about them is a statement about this run of the checker.

// RocqFile renders the definitions [<name>_func], [<name>_vars],
// [<name>_pre] and [<name>_post].
func RocqFile(name string, f *checker.Func, vars []checker.Sort, pre, post *checker.Assn) string {
	var b strings.Builder
	fmt.Fprintf(&b, "Definition %s_func : cfunc :=\n  %s.\n\n", name, RocqFunc(f))
	fmt.Fprintf(&b, "Definition %s_vars : list sort := %s.\n\n", name, RocqSorts(vars))
	fmt.Fprintf(&b, "Definition %s_pre : cassn :=\n  %s.\n\n", name, RocqAssn(pre))
	fmt.Fprintf(&b, "Definition %s_post : cassn :=\n  %s.\n", name, RocqAssn(post))
	return b.String()
}

func rocqString(s string) string {
	return strconv.Quote(s) + "%go"
}

func rocqW64(n uint64) string {
	return fmt.Sprintf("(W64 %d)", n)
}

func rocqBool(n uint64) string {
	if n != 0 {
		return "true"
	}
	return "false"
}

// RocqFunc renders a checker.Func as a cfunc.
func RocqFunc(f *checker.Func) string {
	var ps []string
	for _, p := range f.Params {
		ps = append(ps, rocqString(p))
	}
	return fmt.Sprintf("mkFunc [%s]\n    %s", strings.Join(ps, "; "), RocqExpr(f.Body))
}

// RocqSorts renders a sort table.
func RocqSorts(vars []checker.Sort) string {
	var ss []string
	for _, s := range vars {
		ss = append(ss, rocqSort(s))
	}
	return "[" + strings.Join(ss, "; ") + "]"
}

func rocqSort(s checker.Sort) string {
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
	panic(fmt.Sprintf("rocq: unknown sort %d", s))
}

func rocqType(t *checker.Type) string {
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
		return "(CTyPtr " + rocqType(t.Elem) + ")"
	}
	panic(fmt.Sprintf("rocq: unknown type kind %d", t.Kind))
}

func rocqOp(op checker.Op) string {
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
	panic(fmt.Sprintf("rocq: unknown operator %d", op))
}

// RocqExpr renders a checker.Expr as a cexpr.
func RocqExpr(e *checker.Expr) string {
	switch e.Kind {
	case checker.EInt:
		return "(CEInt " + rocqW64(e.Num) + ")"
	case checker.EBool:
		return "(CEBool " + rocqBool(e.Num) + ")"
	case checker.EUnit:
		return "CEUnit"
	case checker.EVar:
		return "(CEVar " + rocqString(e.Name) + ")"
	case checker.ELet:
		return fmt.Sprintf("(CELet %s %s %s)", rocqString(e.Name), RocqExpr(e.A), RocqExpr(e.B))
	case checker.ESeq:
		return fmt.Sprintf("(CESeq %s %s)", RocqExpr(e.A), RocqExpr(e.B))
	case checker.EIf:
		return fmt.Sprintf("(CEIf %s %s %s)", RocqExpr(e.A), RocqExpr(e.B), RocqExpr(e.C))
	case checker.ELoad:
		return fmt.Sprintf("(CELoad %s %s)", rocqType(e.Ty), RocqExpr(e.A))
	case checker.EStore:
		return fmt.Sprintf("(CEStore %s %s %s)", rocqType(e.Ty), RocqExpr(e.A), RocqExpr(e.B))
	case checker.EAlloc:
		return fmt.Sprintf("(CEAlloc %s %s)", rocqType(e.Ty), RocqExpr(e.A))
	case checker.EZero:
		return fmt.Sprintf("(CEZero %s)", rocqType(e.Ty))
	case checker.EBinOp:
		return fmt.Sprintf("(CEBinOp %s %s %s %s)", rocqOp(e.Op), rocqType(e.Ty), RocqExpr(e.A), RocqExpr(e.B))
	case checker.EUnOp:
		return fmt.Sprintf("(CEUnOp %s %s %s)", rocqOp(e.Op), rocqType(e.Ty), RocqExpr(e.A))
	case checker.EConvert:
		return fmt.Sprintf("(CEConvert %s %s %s)", rocqType(e.Ty), rocqType(e.Ty2), RocqExpr(e.A))
	case checker.EDo:
		return "(CEDo " + RocqExpr(e.A) + ")"
	case checker.EReturn:
		return "(CEReturn " + RocqExpr(e.A) + ")"
	case checker.EExcSeq:
		return fmt.Sprintf("(CEExcSeq %s %s)", RocqExpr(e.A), RocqExpr(e.B))
	case checker.EExcDo:
		return "(CEExcDo " + RocqExpr(e.A) + ")"
	}
	panic(fmt.Sprintf("rocq: unknown expression kind %d", e.Kind))
}

// RocqTerm renders a checker.Term as a term.
func RocqTerm(t *checker.Term) string {
	bin := func(c string) string { return fmt.Sprintf("(%s %s %s)", c, RocqTerm(t.A), RocqTerm(t.B)) }
	switch t.Kind {
	case checker.TVar:
		return fmt.Sprintf("(TVar %d)", t.Num)
	case checker.TPat:
		return fmt.Sprintf("(TPat %d)", t.Num)
	case checker.TResult:
		return "TResult"
	case checker.TInt:
		return "(TInt " + rocqW64(t.Num) + ")"
	case checker.TBool:
		return "(TBool " + rocqBool(t.Num) + ")"
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
		return "(TNeg " + RocqTerm(t.A) + ")"
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
		return "(TNot " + RocqTerm(t.A) + ")"
	case checker.TIte:
		return fmt.Sprintf("(TIte %s %s %s)", RocqTerm(t.A), RocqTerm(t.B), RocqTerm(t.C))
	case checker.TExec:
		return "TExec"
	case checker.TRet:
		return "(TRet " + RocqTerm(t.A) + ")"
	}
	panic(fmt.Sprintf("rocq: unknown term kind %d", t.Kind))
}

// RocqAssn renders a checker.Assn as a cassn.
func RocqAssn(a *checker.Assn) string {
	switch a.Kind {
	case checker.AEmp:
		return "CAEmp"
	case checker.ASep:
		return fmt.Sprintf("(CASep %s %s)", RocqAssn(a.L), RocqAssn(a.R))
	case checker.AOr:
		return fmt.Sprintf("(CAOr %s\n    %s)", RocqAssn(a.L), RocqAssn(a.R))
	case checker.AExists:
		return fmt.Sprintf("(CAExists %d %s %s)", a.Var, rocqSort(a.Sort), RocqAssn(a.L))
	case checker.APure:
		return "(CAPure " + RocqTerm(a.X) + ")"
	case checker.APointsTo:
		return fmt.Sprintf("(CAPointsTo %s %s)", RocqTerm(a.X), RocqTerm(a.Y))
	}
	panic(fmt.Sprintf("rocq: unknown assertion kind %d", a.Kind))
}
