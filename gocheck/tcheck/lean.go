package main

import (
	"fmt"
	"path/filepath"
	"strings"

	"github.com/upamanyus/bootstrap-go/tcheck"
)

// Writing Lean: the generated table file and observation files.

func leanSort(s tcheck.Sort) string {
	switch s.Kind {
	case tcheck.SortVal:
		return "SVal"
	case tcheck.SortType:
		return "SType"
	}
	return fmt.Sprintf("(SU %d)", s.Num)
}

func leanList[A any](f func(A) string, l []A) string {
	var parts []string
	for _, x := range l {
		parts = append(parts, f(x))
	}
	return "[" + strings.Join(parts, ", ") + "]"
}

func leanTerm(t *tcheck.Term) string {
	switch t.Kind {
	case tcheck.TVar:
		return fmt.Sprintf("(TVar %d)", t.Num)
	case tcheck.TSym:
		return fmt.Sprintf("(TSym %d %s)", t.Num, leanList(leanTerm, t.Args))
	case tcheck.TPair:
		return "(TPair " + leanTerm(t.Args[0]) + " " + leanTerm(t.Args[1]) + ")"
	case tcheck.TLit:
		return "(TLit " + leanTerm(t.Args[0]) + " " + leanList(leanTerm, t.Args[1:]) + ")"
	}
	return "TUnit"
}

func leanPat(p *tcheck.Pat) string {
	if p.Kind == tcheck.PVal {
		return "(PVal " + leanTerm(p.T) + ")"
	}
	return "(PApp " + leanPat(p.A) + " " + leanPat(p.B) + ")"
}

func leanAtom(a *tcheck.Atom) string {
	if a.Kind == tcheck.APred {
		return fmt.Sprintf("(APred %d %s)", a.Num, leanList(leanTerm, a.Args))
	}
	return "(AEq " + leanTerm(a.Args[0]) + " " + leanTerm(a.Args[1]) + ")"
}

func leanExpr(e *tcheck.Expr) string {
	switch e.Kind {
	case tcheck.EVal:
		return "(CVal " + leanTerm(e.T) + ")"
	case tcheck.EVar:
		return "(CVar " + leanQuote(e.Name) + ")"
	case tcheck.EApp:
		return "(CApp " + leanExpr(e.A) + " " + leanExpr(e.B) + ")"
	case tcheck.EPair:
		return "(CPair " + leanExpr(e.A) + " " + leanExpr(e.B) + ")"
	case tcheck.ELet:
		return "(CLet " + leanQuote(e.Name) + "\n  " + leanExpr(e.A) + "\n  " + leanExpr(e.B) + ")"
	case tcheck.ESeq:
		return "(CSeq " + leanExpr(e.A) + "\n  " + leanExpr(e.B) + ")"
	case tcheck.ELit:
		return "(CLit " + leanTerm(e.T) + " " + leanList(leanExpr, e.Elems) + ")"
	case tcheck.EDo:
		return "(CDo " + leanExpr(e.A) + ")"
	case tcheck.ERet:
		return "(CRet " + leanExpr(e.A) + ")"
	case tcheck.EXSeq:
		return "(CXSeq " + leanExpr(e.A) + "\n  " + leanExpr(e.B) + ")"
	case tcheck.EXDo:
		return "(CXDo " + leanExpr(e.A) + ")"
	}
	panic("leanExpr")
}

func leanRule(r *tcheck.Rule) string {
	return "mkRule " + leanList(leanSort, r.Vars) + "\n    " + leanPat(r.Lhs) + "\n    " +
		leanList(leanAtom, r.Pre) + " " + leanList(leanSort, r.Ex) + " " + leanTerm(r.Ret) + "\n    " +
		leanList(leanAtom, r.Post)
}

func leanSpec(sp *tcheck.Spec) string {
	return fmt.Sprintf("mkSpec %s\n    %s\n    %s\n    %s %s\n    %s",
		leanList(leanSort, sp.Vars), leanList(leanTerm, sp.Args), leanList(leanAtom, sp.Pre),
		leanList(leanSort, sp.Ex), leanTerm(sp.Ret), leanList(leanAtom, sp.Post))
}

func leanFact(f *tcheck.Fact) string {
	return "mkFact " + leanList(leanSort, f.Vars) + "\n    " + leanTerm(f.Lhs) + "\n    " + leanTerm(f.Rhs)
}

// modulePath turns Checkers/TCheck/Raft/TableRaft.lean into
// Checkers.TCheck.Raft.TableRaft.
func modulePath(path string) string {
	p := filepath.ToSlash(strings.TrimSuffix(path, ".lean"))
	p = strings.TrimPrefix(p, "./")
	return strings.ReplaceAll(p, "/", ".")
}

// The section variables of a spec in the etcd proofs: the ambient a
// denotation lives in (Checkers/TCheck/Denote.lean).
const ambientVars = "variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]\n" +
	"variable [go_gctx : GoGlobalContext]\n" +
	"variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]\n" +
	"variable [sem : go.Semantics]\n"

func (t *table) leanSortName(name string) string {
	switch name {
	case "val":
		return "val"
	case "type":
		return "go.GoType"
	}
	for _, s := range t.sorts {
		if s.name == name {
			return "(" + s.lean + ")"
		}
	}
	return "?"
}

func (t *table) arrowType(args []string, res string) string {
	var parts []string
	for _, a := range args {
		parts = append(parts, t.leanSortName(a))
	}
	parts = append(parts, res)
	return strings.Join(parts, " → ")
}

func header(b *strings.Builder, lines ...string) {
	b.WriteString("/-\n")
	for _, l := range lines {
		b.WriteString(l + "\n")
	}
	b.WriteString("-/\n")
}

func (t *table) leanPreamble(b *strings.Builder) {
	b.WriteString("\nnoncomputable section\n\nnamespace Perennial\nnamespace TCheck\n\n")
	if t.opens != "" {
		fmt.Fprintf(b, "open %s\n\n", t.opens)
	}
}

func leanPostamble(b *strings.Builder) {
	b.WriteString("\nend TCheck\nend Perennial\n")
}

// tableDefs is every definition of the table file, for `rule_start`.
func (t *table) tableDefs() []string {
	T := t.name
	names := []string{T + "_den", T + "_sym", T + "_sort", T + "_pred", T + "_syms", T + "_preds"}
	for _, rd := range t.rules {
		names = append(names, T+"_rule_"+rd.name)
	}
	for _, fd := range t.facts {
		names = append(names, T+"_fact_"+fd.name)
	}
	for _, fd := range t.funcs {
		names = append(names, T+"_spec_"+fd.name, T+"_rule_"+fd.name)
	}
	return names
}

// genTable writes the table file: the syntax of every symbol, predicate,
// rule and fact, and the denotation.
func (t *table) genTable(src string, cmd string) (string, error) {
	syms, err := t.symDecls()
	if err != nil {
		return "", err
	}
	preds, err := t.predDecls()
	if err != nil {
		return "", err
	}
	T := t.name
	var b strings.Builder
	header(&b, "Generated by gocheck/tcheck from "+src+" -- DO NOT EDIT.", "",
		"     "+cmd, "",
		"The syntax of the table (what the Go checker reads) and its denotation",
		"(what each symbol and predicate means, in Lean).  The rules and facts",
		"are proved valid by hand, in the link file next to this one.")
	for _, r := range t.imports {
		fmt.Fprintf(&b, "import %s\n", r)
	}
	b.WriteString("import Checkers.TCheck.Link\n")
	t.leanPreamble(&b)
	b.WriteString("/-! Sorts:")
	for i, s := range t.sorts {
		fmt.Fprintf(&b, " `SU %d` = %s (`%s`)%s", i, s.name, s.lean, map[bool]string{true: ".", false: ";"}[i == len(t.sorts)-1])
	}
	b.WriteString(" -/\n\n")
	fmt.Fprintf(&b, "def %s_syms : List symdecl := [\n", T)
	for i, d := range syms {
		sep := ","
		if i == len(syms)-1 {
			sep = ""
		}
		fmt.Fprintf(&b, "  /- %d %s -/ mkSym %s %s%s\n", i, t.syms[i].name, leanList(leanSort, d.Args), leanSort(d.Res), sep)
	}
	b.WriteString("]\n\n")
	fmt.Fprintf(&b, "def %s_preds : List preddecl := [\n", T)
	for i, d := range preds {
		sep := ","
		if i == len(preds)-1 {
			sep = ""
		}
		fmt.Fprintf(&b, "  /- %d %s -/ mkPred %v %s%s\n", i, t.preds[i].name, d.Pers, leanList(leanSort, d.Args), sep)
	}
	b.WriteString("]\n\n")
	for _, rd := range t.rules {
		r, err := t.rule(rd)
		if err != nil {
			return "", fmt.Errorf("rule %s: %v", rd.name, err)
		}
		fmt.Fprintf(&b, "def %s_rule_%s : trule :=\n  %s\n\n", T, rd.name, leanRule(r))
	}
	for _, fd := range t.facts {
		f, err := t.fact(fd)
		if err != nil {
			return "", fmt.Errorf("fact %s: %v", fd.name, err)
		}
		fmt.Fprintf(&b, "def %s_fact_%s : tfact :=\n  %s\n\n", T, fd.name, leanFact(f))
	}
	for _, fd := range t.funcs {
		sp, err := t.spec(fd)
		if err != nil {
			return "", fmt.Errorf("func %s: %v", fd.name, err)
		}
		r, err := t.funcRule(fd)
		if err != nil {
			return "", fmt.Errorf("func %s: %v", fd.name, err)
		}
		fmt.Fprintf(&b, "/-- `%s`: its specification, and the rule callers use. -/\n", fd.impl)
		fmt.Fprintf(&b, "def %s_spec_%s : tspec :=\n  %s\n", T, fd.name, leanSpec(sp))
		fmt.Fprintf(&b, "def %s_rule_%s : trule :=\n  spec_rule %s %s_spec_%s\n\n", T, fd.name,
			leanTerm(patHeadTerm(r.Lhs)), T, fd.name)
	}
	b.WriteString("section den\n" + ambientVars)
	fmt.Fprintf(&b, "variable [package_sem : %s]\n\n", t.assumptions)
	fmt.Fprintf(&b, "def %s_sort : Nat → Type\n", T)
	for i, s := range t.sorts {
		fmt.Fprintf(&b, "  | %d => %s\n", i, s.lean)
	}
	b.WriteString("  | _ => Unit\n\n")
	fmt.Fprintf(&b, "def %s_sym : (n : Nat) → sym_ty %s_sort (lookup_sym %s_syms n)\n", T, T, T)
	for i, s := range t.syms {
		fmt.Fprintf(&b, "  | %d => ((%s) : %s) -- %s\n", i, s.lean, t.arrowType(s.args, t.leanSortName(s.res)), s.name)
	}
	fmt.Fprintf(&b, "  | _ + %d => (#() : val)\n\n", len(t.syms))
	fmt.Fprintf(&b, "def %s_pred : (n : Nat) → pred_ty %s_sort GF (lookup_pred %s_preds n)\n", T, T, T)
	for i, p := range t.preds {
		fmt.Fprintf(&b, "  | %d => ((%s) : %s) -- %s\n", i, p.lean, t.arrowType(p.args, "IProp GF"), p.name)
	}
	fmt.Fprintf(&b, "  | _ + %d => (iprop(True) : IProp GF)\n\n", len(t.preds))
	fmt.Fprintf(&b, "def %s_den : DenAt GF %s_syms %s_preds :=\n  mkDenAt %s_sort (%s_sym (hG := hG)) (%s_pred (hG := hG))\n", T, T, T, T, T, T)
	b.WriteString("end den\n\n")
	fmt.Fprintf(&b, "/-- `tc_simp`, unfolding this table's definitions too. -/\nmacro \"%s_tc_simp\" : tactic =>\n  `(tactic| tc_simp [%s])\n\n",
		T, strings.Join(t.tableDefs(), ", "))
	fmt.Fprintf(&b, "/-- `rule_start`, unfolding this table's definitions too. -/\nmacro \"%s_rule_start\" : tactic =>\n  `(tactic| rule_start [%s])\n",
		T, strings.Join(t.tableDefs(), ", "))
	leanPostamble(&b)
	return b.String(), nil
}

// genObservation writes the observation file of one run.
func genObservation(t *table, tableFile string, f *funcDecl, inp *tcheck.Input, ruleNames, factNames []string,
	bytes string, cmd string, implName string, head *tcheck.Term) string {
	T := t.name
	F := f.name
	var b strings.Builder
	header(&b, "Generated by gocheck/tcheck -- DO NOT EDIT.", "",
		"     "+cmd, "",
		"tcheck.Check answered true on the bytes in `"+F+"_check_run`, the input",
		"`"+F+"_input`: the function `"+f.impl+"`, its specification, and the rules and",
		"facts of the table that the run used.  The axiom is an observation, of",
		"the form Checkers/TCheck/Observe.lean describes; gocheck/tcheck/observe.sh",
		"reruns the checker on these bytes and regenerates this file.")
	fmt.Fprintf(&b, "import %s\n", modulePath(tableFile))
	t.leanPreamble(&b)
	fmt.Fprintf(&b, "def %s_func : cfunc :=\n  mkFunc %s\n  %s\n\n", F, leanList(leanQuote, inp.Fn.Params), leanExpr(inp.Fn.Body))
	var rs, fs []string
	for _, n := range ruleNames {
		rs = append(rs, T+"_rule_"+n)
	}
	for _, n := range factNames {
		fs = append(fs, T+"_fact_"+n)
	}
	fmt.Fprintf(&b, "def %s_rules : List trule := [%s]\n", F, strings.Join(rs, ", "))
	fmt.Fprintf(&b, "def %s_facts : List tfact := [%s]\n\n", F, strings.Join(fs, ", "))
	fmt.Fprintf(&b, "def %s_input : tinput :=\n  mkInput %s_syms %s_preds %s_rules %s_facts %s_func %s_spec_%s\n\n", F, T, T, F, F, F, T, F)
	b.WriteString("/-- OBSERVE-EXECUTION: tcheck.Check returned true on exactly these bytes. -/\n")
	fmt.Fprintf(&b, "axiom %s_check_run : observed_run\n  go!%s\n\n", F, leanQuote(bytes))
	b.WriteString("set_option maxRecDepth 100000 in\n")
	b.WriteString("/-- The bytes are `ser_input` of the input, by kernel evaluation (`decide +kernel`; the\n" +
		"list comparison recurses once per byte, hence `maxRecDepth`). -/\n")
	fmt.Fprintf(&b, "theorem %s_holds : input_holds %s_input :=\n", F, F)
	fmt.Fprintf(&b, "  observed_input_holds _ _ (by decide +kernel) %s_check_run\n\n", F)
	b.WriteString("section den\n" + ambientVars)
	fmt.Fprintf(&b, "variable [package_sem : %s]\n\n", t.assumptions)
	b.WriteString("/-- The checked function is Goose's. -/\n")
	fmt.Fprintf(&b, "theorem %s_func_val :\n    func_val (%s_den (hG := hG)) %s_func = %s := by\n  rfl\n\n", F, T, F, implName)
	fmt.Fprintf(&b, "/-- The call `%s_rule_%s` is about unfolds to the checked function. -/\n", T, F)
	fmt.Fprintf(&b, "theorem %s_call_ok :\n    call_ok (%s_den (hG := hG)) %s_func %s_spec_%s %s :=\n", F, T, F, T, F, leanTerm(head))
	fmt.Fprintf(&b, "  call_ok_of _ _ _ _ _ %s_func_val (by call_ok_by)\n", F)
	b.WriteString("end den\n")
	leanPostamble(&b)
	return b.String()
}

// patHeadTerm is the value at the head of an application pattern.
func patHeadTerm(p *tcheck.Pat) *tcheck.Term {
	for p.Kind == tcheck.PApp {
		p = p.A
	}
	return p.T
}
