// Command gocheck symbolically executes a Go function with the CSL checker in
// github.com/upamanyus/bootstrap-go/checker and, optionally, verifies it against
// a postcondition.
//
// Usage:
//
//	gocheck [-pkg P] [-pre A] [-post A] [-moddir D] [-configdir D] [-ast] [-v]
//	        [-lean FILE [-lean-name N]] Func
//
// With -lean (which needs -post), gocheck also calls checker.Check on the
// input and writes that input, as Lean terms over Checkers/Checker/Defs.lean, to FILE
// (see render.LeanFile).
package main

import (
	"flag"
	"fmt"
	"os"
	"strings"

	"github.com/upamanyus/bootstrap-go/checker"
	"github.com/upamanyus/bootstrap-go/gocheck/render"
	"github.com/upamanyus/bootstrap-go/gocheck/spec"
	"github.com/upamanyus/bootstrap-go/gocheck/translate"
)

const (
	exitOK     = 0 // verified, or the strongest postcondition was printed
	exitReject = 1 // the checker rejected the program or the postcondition
	exitUsage  = 2 // usage, parse, translation or unsupported-input error
)

func main() {
	code, err := run()
	if err != nil {
		fmt.Fprintf(os.Stderr, "gocheck: %v\n", err)
	}
	os.Exit(code)
}

func run() (int, error) {
	fs := flag.NewFlagSet("gocheck", flag.ContinueOnError)
	usage := func() {
		fmt.Fprintf(os.Stderr, "usage: gocheck [-pkg P] [-pre A] [-post A] [-moddir D] "+
			"[-configdir D] [-ast] [-v] [-lean FILE [-lean-name N]] Func\n")
		fs.PrintDefaults()
	}
	fs.Usage = usage
	pkg := fs.String("pkg", ".", "Go package pattern holding the function")
	pre := fs.String("pre", "emp", "precondition")
	post := fs.String("post", "", "postcondition to verify (default: print the strongest one)")
	modDir := fs.String("moddir", ".", "directory containing go.mod")
	configDir := fs.String("configdir", "new/code", "goose output root (its -out directory)")
	showAST := fs.Bool("ast", false, "print the translated GooseLang body")
	verbose := fs.Bool("v", false, "print extra detail")
	leanFile := fs.String("lean", "", "write the checker input as Lean definitions to this file (needs -post)")
	leanName := fs.String("lean-name", "", "prefix of the Lean definitions (default: the function name, lowercased)")
	if err := fs.Parse(os.Args[1:]); err != nil {
		return exitUsage, nil
	}
	if fs.NArg() != 1 {
		usage()
		return exitUsage, fmt.Errorf("expected exactly one function name, got %d", fs.NArg())
	}
	fname := fs.Arg(0)
	out := os.Stdout
	pr := &render.Printer{}

	// 1. Translate.
	p, err := translate.LoadPackage(*configDir, *modDir, *pkg)
	if err != nil {
		return exitUsage, err
	}
	f, params, err := p.Func(fname)
	if err != nil {
		return exitUsage, err
	}

	// 2. Scope and precondition.
	sc, err := spec.NewScope(params)
	if err != nil {
		return exitUsage, err
	}
	preSurface, err := spec.Parse(*pre)
	if err != nil {
		return exitUsage, fmt.Errorf("-pre: %v", err)
	}
	preAssn, err := sc.LowerPre(preSurface)
	if err != nil {
		return exitUsage, fmt.Errorf("-pre: %v", err)
	}
	pr.Names = sc.Names
	vars := sc.Vars()

	// 3. Report the signature, the logical variables and the precondition.
	fmt.Fprintf(out, "func %s(%s)\n", fname, signature(params))
	fmt.Fprintf(out, "vars:\n")
	for i, name := range sc.Names {
		s, _ := sc.Sort(i)
		line := fmt.Sprintf("  [%d] %s : %s", i, name, render.SortName(s))
		if ty := sc.GoType(i); ty != nil {
			line += strings.Repeat(" ", max(1, 24-len(line))) + "// Go type " + render.GoType(ty)
		}
		fmt.Fprintln(out, line)
	}
	fmt.Fprintf(out, "pre:\n  %s\n", pr.Assn(preAssn))
	if *showAST {
		fmt.Fprintf(out, "body:\n%s\n", pr.ExprBlock(f.Body, 2))
	}

	// 4. Symbolic execution.
	paths, fail := checker.Analyze(f, vars, preAssn)
	if fail != nil {
		lines := pr.FailureLines(fail)
		fmt.Fprintf(out, "path %d unsafe: %s\n", fail.PathIdx, lines[0])
		for _, l := range lines[1:] {
			fmt.Fprintf(out, "  %s\n", l)
		}
		fmt.Fprintf(out, "  heap at entry: %s\n", heapOf(preAssn, pr))
		fmt.Fprintf(out, "UNSAFE\n")
		return exitReject, nil
	}

	fmt.Fprintf(out, "paths: %d\n", len(paths))
	for i, pa := range paths {
		fmt.Fprintf(out, "path %d:\n%s\n", i, pr.Path(pa, "  "))
		if *verbose {
			nvars := 0
			if pa.St != nil {
				nvars = len(pa.St.Vars)
			}
			fmt.Fprintf(out, "  (ret term: %s; %d logical variables)\n",
				pr.Term(pa.Ret), nvars)
		}
	}

	// 5. Postcondition.
	if *post == "" {
		return exitOK, nil
	}
	postSurface, err := spec.Parse(*post)
	if err != nil {
		return exitUsage, fmt.Errorf("-post: %v", err)
	}
	postAssn, err := sc.LowerPost(postSurface)
	if err != nil {
		return exitUsage, fmt.Errorf("-post: %v", err)
	}
	fmt.Fprintf(out, "post:\n  %s\n", pr.WithPats(sc.PatNames(0)).Assn(postAssn))

	if *leanFile != "" {
		name := *leanName
		if name == "" {
			name = strings.ToLower(fname)
		}
		src := render.LeanFile(name, f, vars, preAssn, postAssn)
		if err := os.WriteFile(*leanFile, []byte(src), 0o644); err != nil {
			return exitUsage, err
		}
		fmt.Fprintf(out, "checker.Check: %v (input written to %s)\n",
			checker.Check(f, vars, preAssn, postAssn), *leanFile)
	}

	okCount := 0
	for i := range paths {
		one := paths[i : i+1]
		if checker.Verify(one, vars, postAssn) == nil {
			okCount++
			fmt.Fprintf(out, "path %d: OK\n", i)
			continue
		}
		fmt.Fprintf(out, "path %d: FAIL\n", i)
		for _, df := range checker.Explain(one, vars, postAssn) {
			dp := pr.WithPats(sc.PatNames(int(df.Disjunct)))
			lines := dp.FailureLines(df.Fail)
			fmt.Fprintf(out, "  disjunct %d: %s\n", df.Disjunct, lines[0])
			for _, l := range lines[1:] {
				fmt.Fprintf(out, "    %s\n", l)
			}
		}
	}
	if okCount == len(paths) {
		fmt.Fprintf(out, "OK %d/%d paths verified\n", okCount, len(paths))
		return exitOK, nil
	}
	fmt.Fprintf(out, "FAIL %d/%d paths verified\n", okCount, len(paths))
	return exitReject, nil
}

func signature(params []translate.ParamInfo) string {
	var parts []string
	for _, p := range params {
		parts = append(parts, p.Name+" "+render.GoType(p.Ty))
	}
	return strings.Join(parts, ", ")
}

// heapOf renders the points-to atoms of a precondition.
func heapOf(a *checker.Assn, pr *render.Printer) string {
	cells := collectPointsTo(a)
	if len(cells) == 0 {
		return pr.Emp()
	}
	var parts []string
	for _, c := range cells {
		parts = append(parts, pr.Assn(c))
	}
	return strings.Join(parts, " "+pr.Sep()+" ")
}

func collectPointsTo(a *checker.Assn) []*checker.Assn {
	if a == nil {
		return nil
	}
	switch a.Kind {
	case checker.APointsTo:
		return []*checker.Assn{a}
	case checker.ASep, checker.AOr:
		return append(collectPointsTo(a.L), collectPointsTo(a.R)...)
	case checker.AExists:
		return collectPointsTo(a.L)
	}
	return nil
}
