package render

import (
	"fmt"
	"strconv"
	"strings"

	"github.com/upamanyus/bootstrap-go/checker"
)

func (p *Printer) tyAnn(t *checker.Type) string {
	if p.ASCII {
		return "[" + GoType(t) + "]"
	}
	return "⟨" + GoType(t) + "⟩"
}

var binOpText = map[checker.Op]string{
	checker.OpAdd: "+",
	checker.OpSub: "-",
	checker.OpMul: "*",
	checker.OpEq:  "=",
	checker.OpLt:  "<",
	checker.OpLe:  "<=",
	checker.OpGt:  ">",
	checker.OpGe:  ">=",
}

// Expr renders a GooseLang expression on one line, in a notation close to the
// one goose emits.
func (p *Printer) Expr(e *checker.Expr) string {
	if e == nil {
		return "<nil>"
	}
	switch e.Kind {
	case checker.EInt:
		return fmt.Sprintf("#(W64 %d)", e.Num)
	case checker.EBool:
		if e.Num != 0 {
			return "#true"
		}
		return "#false"
	case checker.EUnit:
		return "#()"
	case checker.EVar:
		return strconv.Quote(e.Name)
	case checker.ELet:
		return fmt.Sprintf("let: %s := %s in %s", strconv.Quote(e.Name), p.Expr(e.A), p.Expr(e.B))
	case checker.ESeq:
		return fmt.Sprintf("%s ;; %s", p.Expr(e.A), p.Expr(e.B))
	case checker.EExcSeq:
		return fmt.Sprintf("%s ;;; %s", p.Expr(e.A), p.Expr(e.B))
	case checker.EIf:
		return fmt.Sprintf("if: %s then %s else %s", p.Expr(e.A), p.Expr(e.B), p.Expr(e.C))
	case checker.ELoad:
		return fmt.Sprintf("![%s] %s", GoType(e.Ty), p.atomExpr(e.A))
	case checker.EStore:
		return fmt.Sprintf("%s <-[%s] %s", p.atomExpr(e.A), GoType(e.Ty), p.atomExpr(e.B))
	case checker.EAlloc:
		return fmt.Sprintf("GoAlloc %s %s", GoType(e.Ty), p.atomExpr(e.A))
	case checker.EZero:
		return fmt.Sprintf("GoZeroVal %s #()", GoType(e.Ty))
	case checker.EBinOp:
		op, ok := binOpText[e.Op]
		if !ok {
			op = fmt.Sprintf("op#%d", uint64(e.Op))
		}
		return fmt.Sprintf("%s %s%s %s", p.atomExpr(e.A), op, p.tyAnn(e.Ty), p.atomExpr(e.B))
	case checker.EUnOp:
		op := "-"
		if e.Op == checker.OpNot {
			op = "!"
		}
		return fmt.Sprintf("%s%s %s", p.tyAnn(e.Ty), op, p.atomExpr(e.A))
	case checker.EConvert:
		return fmt.Sprintf("Convert %s %s %s", GoType(e.Ty), GoType(e.Ty2), p.atomExpr(e.A))
	case checker.EDo:
		return fmt.Sprintf("do: %s", p.atomExpr(e.A))
	case checker.EReturn:
		return fmt.Sprintf("return: %s", p.atomExpr(e.A))
	case checker.EExcDo:
		return fmt.Sprintf("exception_do %s", p.atomExpr(e.A))
	}
	return fmt.Sprintf("<expr kind %d>", uint64(e.Kind))
}

// atomExpr renders e, parenthesized unless it is already atomic.
func (p *Printer) atomExpr(e *checker.Expr) string {
	if e == nil {
		return "<nil>"
	}
	switch e.Kind {
	case checker.EInt, checker.EBool, checker.EUnit, checker.EVar:
		return p.Expr(e)
	}
	return "(" + p.Expr(e) + ")"
}

// ExprBlock renders e over several lines, one binding per line.
func (p *Printer) ExprBlock(e *checker.Expr, indent int) string {
	pad := strings.Repeat(" ", indent)
	if e == nil {
		return pad + "<nil>"
	}
	switch e.Kind {
	case checker.ELet:
		return fmt.Sprintf("%slet: %s := %s in\n%s", pad, strconv.Quote(e.Name),
			p.Expr(e.A), p.ExprBlock(e.B, indent))
	case checker.ESeq:
		return fmt.Sprintf("%s%s ;;\n%s", pad, p.Expr(e.A), p.ExprBlock(e.B, indent))
	case checker.EExcSeq:
		return fmt.Sprintf("%s%s ;;;\n%s", pad, p.ExprBlockInline(e.A, indent),
			p.ExprBlock(e.B, indent))
	case checker.EExcDo:
		return fmt.Sprintf("%sexception_do (\n%s\n%s)", pad, p.ExprBlock(e.A, indent+2), pad)
	case checker.EIf:
		return fmt.Sprintf("%sif: %s\n%sthen\n%s\n%selse\n%s", pad, p.Expr(e.A),
			pad, p.ExprBlock(e.B, indent+2), pad, p.ExprBlock(e.C, indent+2))
	}
	return pad + p.Expr(e)
}

// ExprBlockInline is ExprBlock with the first line's padding already emitted
// by the caller.
func (p *Printer) ExprBlockInline(e *checker.Expr, indent int) string {
	s := p.ExprBlock(e, indent)
	return strings.TrimLeft(s, " ")
}
