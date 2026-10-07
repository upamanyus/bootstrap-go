// Command tcheck runs the table-driven checker (tcheck/) on a function and
// writes the Rocq files that turn the run into a proof.
//
//	tcheck -table T.tbl -gen-table OUT.v
//	    write the table's syntax and denotation (the link proving its rules
//	    is written by hand, next to it)
//	tcheck -table T.tbl -table-file OUT.v -func NAME [-observe OBS.v]
//	    run the checker on function NAME of the table; with -observe, write
//	    the observation file of the run (the input restricted to the rules
//	    and facts it used, and the axiom that Check returned true on it)
//	tcheck -verify OBS.v
//	    rerun tcheck.Check on the bytes recorded in an observation file
//
// Exit codes: 0 established (or verified), 1 the checker answered false,
// 2 usage or input error.
package main

import (
	"flag"
	"fmt"
	"os"
	"regexp"
	"strings"

	"github.com/upamanyus/bootstrap-go/tcheck"
)

func die(code int, format string, args ...any) {
	fmt.Fprintf(os.Stderr, "tcheck: "+format+"\n", args...)
	os.Exit(code)
}

var axiomRe = regexp.MustCompile(`(?s)Axiom (\S+) : observed_run\s+"((?:[^"]|"")*)"%go\.`)

func verify(path string) {
	b, err := os.ReadFile(path)
	if err != nil {
		die(2, "%v", err)
	}
	ms := axiomRe.FindAllStringSubmatch(string(b), -1)
	if len(ms) != 1 {
		die(2, "%s: expected exactly one observation axiom, found %d", path, len(ms))
	}
	bytes := strings.ReplaceAll(ms[0][2], "\"\"", "\"")
	if !tcheck.Check([]byte(bytes)) {
		inp := tcheck.Parse([]byte(bytes))
		if inp == nil {
			die(1, "%s: %s: the recorded bytes do not parse", path, ms[0][1])
		}
		f, _ := tcheck.Run(inp)
		die(1, "%s: %s: tcheck.Check answered false (failure code %d)", path, ms[0][1], f.Code)
	}
	fmt.Printf("%s: %s: tcheck.Check: true (%d bytes)\n", path, ms[0][1], len(bytes))
}

func main() {
	tablePath := flag.String("table", "", "table file")
	genTable := flag.String("gen-table", "", "write the table's Rocq file here")
	tableFile := flag.String("table-file", "", "the table's Rocq file (for the observation file's Require)")
	fn := flag.String("func", "", "function to check")
	observe := flag.String("observe", "", "write the observation file here")
	verifyPath := flag.String("verify", "", "rerun the checker on an observation file's bytes")
	flag.Parse()
	if *verifyPath != "" {
		verify(*verifyPath)
		return
	}
	if *tablePath == "" {
		flag.Usage()
		os.Exit(2)
	}
	t, err := loadTable(*tablePath)
	if err != nil {
		die(2, "%v", err)
	}
	cmd := "go run ./gocheck/tcheck " + strings.Join(os.Args[1:], " ")
	if *genTable != "" {
		s, err := t.genTable(*tablePath, cmd)
		if err != nil {
			die(2, "%v", err)
		}
		if err := os.WriteFile(*genTable, []byte(s), 0o644); err != nil {
			die(2, "%v", err)
		}
		fmt.Printf("wrote %s\n", *genTable)
	}
	if *fn == "" {
		return
	}
	if *observe != "" && *tableFile == "" {
		die(2, "-observe needs -table-file")
	}
	fd, err := t.funcDecl(*fn)
	if err != nil {
		die(2, "%v", err)
	}
	syms, err := t.symDecls()
	if err != nil {
		die(2, "%v", err)
	}
	preds, err := t.predDecls()
	if err != nil {
		die(2, "%v", err)
	}
	inp := &tcheck.Input{Syms: syms, Preds: preds}
	if inp.Fn, err = reifyFunc(t, fd.impl); err != nil {
		die(2, "%v", err)
	}
	allNames, rules, err := []string(nil), []*tcheck.Rule(nil), error(nil)
	if rules, allNames, err = t.allRules(fd.name); err != nil {
		die(2, "%v", err)
	}
	inp.Rules = rules
	for _, fdl := range t.facts {
		f, err := t.fact(fdl)
		if err != nil {
			die(2, "fact %s: %v", fdl.name, err)
		}
		inp.Facts = append(inp.Facts, f)
	}
	if inp.Sp, err = t.spec(*fd); err != nil {
		die(2, "func %s: %v", fd.name, err)
	}
	f, used := tcheck.Run(inp)
	if f != nil {
		fmt.Println(t.renderFailure(inp, allNames, f))
		os.Exit(1)
	}
	// The input of the observation: only the rules and facts the run used.
	small := &tcheck.Input{Syms: inp.Syms, Preds: inp.Preds, Fn: inp.Fn, Sp: inp.Sp}
	var ruleNames, factNames []string
	for i, r := range inp.Rules {
		if used[i] {
			small.Rules = append(small.Rules, r)
			ruleNames = append(ruleNames, allNames[i])
		}
	}
	for i, fa := range inp.Facts {
		if used[len(inp.Rules)+i] {
			small.Facts = append(small.Facts, fa)
			factNames = append(factNames, t.facts[i].name)
		}
	}
	bytes := serInput(small)
	if !tcheck.Check([]byte(bytes)) {
		die(2, "internal error: the restricted input does not check")
	}
	fmt.Printf("checker.Check: true -- %s (%d bytes)\n  rules: %s\n  facts: %s\n", fd.name, len(bytes),
		strings.Join(ruleNames, " "), strings.Join(factNames, " "))
	if *observe != "" {
		fr, err := t.funcRule(*fd)
		if err != nil {
			die(2, "%v", err)
		}
		cf, err := loadCode(t.codeFile, t.module)
		if err != nil {
			die(2, "%v", err)
		}
		s := genObservation(t, *tableFile, fd, small, ruleNames, factNames, bytes, cmd,
			cf.qualify(fd.impl), patHeadTerm(fr.Lhs))
		if err := os.WriteFile(*observe, []byte(s), 0o644); err != nil {
			die(2, "%v", err)
		}
		fmt.Printf("wrote %s\n", *observe)
	}
}

// Rendering failures with the table's names.

func (t *table) renderTerm(t0 *tcheck.Term) string {
	switch t0.Kind {
	case tcheck.TVar:
		return fmt.Sprintf("?%d", t0.Num)
	case tcheck.TUnit:
		return "unit"
	case tcheck.TPair:
		return "(pair " + t.renderTerm(t0.Args[0]) + " " + t.renderTerm(t0.Args[1]) + ")"
	case tcheck.TLit:
		var parts []string
		for _, a := range t0.Args {
			parts = append(parts, t.renderTerm(a))
		}
		return "(lit " + strings.Join(parts, " ") + ")"
	}
	name := fmt.Sprintf("sym%d", t0.Num)
	if int(t0.Num) < len(t.syms) {
		name = t.syms[t0.Num].name
	}
	if len(t0.Args) == 0 {
		return name
	}
	var parts []string
	for _, a := range t0.Args {
		parts = append(parts, t.renderTerm(a))
	}
	return "(" + name + " " + strings.Join(parts, " ") + ")"
}

func (t *table) renderPat(p *tcheck.Pat) string {
	if p.Kind == tcheck.PVal {
		return t.renderTerm(p.T)
	}
	return "(app " + t.renderPat(p.A) + " " + t.renderPat(p.B) + ")"
}

func (t *table) renderFailure(inp *tcheck.Input, ruleNames []string, f *tcheck.Failure) string {
	names := map[uint64]string{
		tcheck.FailParse: "the input does not parse", tcheck.FailInput: "the input is ill formed",
		tcheck.FailUnbound: "unbound variable", tcheck.FailNoRule: "no rule applies",
		tcheck.FailMonad: "exception-monad value misplaced", tcheck.FailLitElem: "literal element not a value",
		tcheck.FailPost: "the postcondition does not hold", tcheck.FailFuel: "facts do not terminate",
		tcheck.FailUnsupport: "unsupported construct",
	}
	s := "checker.Check: false -- " + names[f.Code]
	switch f.Code {
	case tcheck.FailNoRule:
		s += " to\n  " + t.renderPat(f.Pat)
	case tcheck.FailInput:
		nr := uint64(len(ruleNames))
		switch {
		case f.Item < nr:
			s += " (rule " + ruleNames[f.Item] + ")"
		case f.Item < nr+uint64(len(t.facts)):
			s += " (fact " + t.facts[f.Item-nr].name + ")"
		default:
			s += " (the function or its specification)"
		}
	case tcheck.FailUnbound:
		s += " " + f.Expr.Name
	}
	return s
}
