package main

import (
	"fmt"
	"os"
	"strings"

	"github.com/mit-pdos/perennial/tcheck"
)

// A table file:
//
//	(table NAME
//	  (require "Rocq.Library")*            ; what the generated files Require Export
//	  (code "path/to/code.v" MODULE)       ; the Goose output the functions come from
//	  (assumptions `raft.Assumptions`)     ; the package assumptions the denotation needs
//	  (sort NAME `Gallina type`)*          ; user sorts u0, u1, ...
//	  (sym NAME (SORT*) SORT `Gallina function`)*
//	  (const NAME `value`)*                ; a nullary symbol of sort val; also a code constant
//	  (tconst NAME `go type`)*             ; a nullary symbol of sort type; also a code constant
//	  (pred NAME [persistent] (SORT*) `Gallina function to iProp`)*
//	  (rule NAME (vars (X SORT)*) (lhs PAT) (pre ATOM*) (ex (X SORT)*) (ret TERM) (post ATOM*))*
//	  (fact NAME (vars (X SORT)*) (lhs TERM) (rhs TERM))*
//	  (func NAME `impl` (vars ..) (head TERM) (args TERM*) (pre ..) (ex ..) (ret TERM) (post ..))*)
//
// A func is checked against its specification; callers (other funcs)
// use it as the rule [spec_rule head spec]: the call of head on the args
// after the first (the receiver, which head contains).
//
// SORT is val, type, or a declared sort. A TERM is a variable, unit, a
// nullary symbol, (SYM TERM*), (pair TERM TERM) or (lit TERM TERM*). A PAT is
// (app PAT PAT) or a TERM. An ATOM is (PRED TERM*) or (= TERM TERM).

type sortDecl struct {
	name, rocq string
}

type symDecl struct {
	name  string
	args  []string
	res   string
	rocq  string
	const_ bool // a code constant: matched against the leaves of the code
}

type predDecl struct {
	name string
	pers bool
	args []string
	rocq string
}

type varDecl struct {
	name, sort string
}

type tripleDecl struct {
	vars []varDecl
	lhs  *node   // rules
	args []*node // funcs
	head *node   // funcs: the value called (the method value of the receiver)
	pre  []*node
	ex   []varDecl
	ret  *node
	post []*node
}

type ruleDecl struct {
	name string
	tripleDecl
}

type factDecl struct {
	name     string
	vars     []varDecl
	lhs, rhs *node
}

type funcDecl struct {
	name string
	impl string
	tripleDecl
}

type table struct {
	name        string
	requires    []string
	codeFile    string
	module      string
	assumptions string
	sorts       []sortDecl
	syms        []symDecl
	preds       []predDecl
	rules       []ruleDecl
	facts       []factDecl
	funcs       []funcDecl
}

func errAt(n *node, format string, args ...any) error {
	return fmt.Errorf("line %d: %s", n.line, fmt.Sprintf(format, args...))
}

func loadTable(path string) (*table, error) {
	src, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	ns, err := parseSexps(string(src))
	if err != nil {
		return nil, fmt.Errorf("%s: %v", path, err)
	}
	if len(ns) != 1 || ns[0].head() != "table" || len(ns[0].list) < 2 {
		return nil, fmt.Errorf("%s: expected one (table NAME ...)", path)
	}
	t := &table{name: ns[0].list[1].text}
	for _, d := range ns[0].list[2:] {
		if err := t.decl(d); err != nil {
			return nil, fmt.Errorf("%s: %v", path, err)
		}
	}
	return t, nil
}

func rocqOf(n *node) (string, error) {
	if n.kind != nRocq {
		return "", errAt(n, "expected a Rocq term in backquotes, got %v", n)
	}
	return strings.TrimSpace(n.text), nil
}

func sortList(n *node) ([]string, error) {
	if n.kind != nList {
		return nil, errAt(n, "expected a list of sorts")
	}
	var ss []string
	for _, c := range n.list {
		if c.kind != nAtom {
			return nil, errAt(c, "expected a sort")
		}
		ss = append(ss, c.text)
	}
	return ss, nil
}

func varList(ns []*node) ([]varDecl, error) {
	var vs []varDecl
	for _, c := range ns {
		if c.kind != nList || len(c.list) != 2 || c.list[0].kind != nAtom || c.list[1].kind != nAtom {
			return nil, errAt(c, "expected (NAME SORT)")
		}
		vs = append(vs, varDecl{c.list[0].text, c.list[1].text})
	}
	return vs, nil
}

func (t *table) triple(d *node, fields []*node, isRule bool) (tripleDecl, error) {
	var tr tripleDecl
	seen := map[string]bool{}
	for _, f := range fields {
		h := f.head()
		if h == "" || seen[h] {
			return tr, errAt(f, "expected a field (vars|lhs|args|pre|ex|ret|post), once each")
		}
		seen[h] = true
		rest := f.list[1:]
		var err error
		switch h {
		case "vars":
			tr.vars, err = varList(rest)
		case "ex":
			tr.ex, err = varList(rest)
		case "lhs":
			if !isRule || len(rest) != 1 {
				return tr, errAt(f, "(lhs PAT) belongs to a rule")
			}
			tr.lhs = rest[0]
		case "args":
			if isRule {
				return tr, errAt(f, "(args ..) belongs to a func")
			}
			tr.args = rest
		case "head":
			if isRule || len(rest) != 1 {
				return tr, errAt(f, "(head TERM) belongs to a func")
			}
			tr.head = rest[0]
		case "pre":
			tr.pre = rest
		case "post":
			tr.post = rest
		case "ret":
			if len(rest) != 1 {
				return tr, errAt(f, "(ret TERM)")
			}
			tr.ret = rest[0]
		default:
			return tr, errAt(f, "unknown field %s", h)
		}
		if err != nil {
			return tr, err
		}
	}
	if tr.ret == nil || (isRule && tr.lhs == nil) || (!isRule && (tr.head == nil || len(tr.args) < 2)) {
		return tr, errAt(d, "missing (ret ..), (lhs ..) or (head ..), or a func with fewer than two args")
	}
	return tr, nil
}

func (t *table) decl(d *node) error {
	h := d.head()
	l := d.list
	switch h {
	case "require":
		if len(l) != 2 || l[1].kind != nString {
			return errAt(d, "(require \"Library\")")
		}
		t.requires = append(t.requires, l[1].text)
	case "code":
		if len(l) != 3 || l[1].kind != nString || l[2].kind != nAtom {
			return errAt(d, "(code \"file.v\" MODULE)")
		}
		t.codeFile, t.module = l[1].text, l[2].text
	case "assumptions":
		if len(l) != 2 {
			return errAt(d, "(assumptions `Class`)")
		}
		r, err := rocqOf(l[1])
		if err != nil {
			return err
		}
		t.assumptions = r
	case "sort":
		if len(l) != 3 || l[1].kind != nAtom {
			return errAt(d, "(sort NAME `type`)")
		}
		r, err := rocqOf(l[2])
		if err != nil {
			return err
		}
		t.sorts = append(t.sorts, sortDecl{l[1].text, r})
	case "sym":
		if len(l) != 5 || l[1].kind != nAtom || l[3].kind != nAtom {
			return errAt(d, "(sym NAME (SORT*) SORT `function`)")
		}
		args, err := sortList(l[2])
		if err != nil {
			return err
		}
		r, err := rocqOf(l[4])
		if err != nil {
			return err
		}
		t.syms = append(t.syms, symDecl{name: l[1].text, args: args, res: l[3].text, rocq: r})
	case "const", "tconst":
		if len(l) != 3 || l[1].kind != nAtom {
			return errAt(d, "(%s NAME `term`)", h)
		}
		r, err := rocqOf(l[2])
		if err != nil {
			return err
		}
		res := "val"
		if h == "tconst" {
			res = "type"
		}
		t.syms = append(t.syms, symDecl{name: l[1].text, res: res, rocq: r, const_: true})
	case "pred":
		if len(l) < 4 || l[1].kind != nAtom {
			return errAt(d, "(pred NAME [persistent] (SORT*) `function`)")
		}
		p := predDecl{name: l[1].text}
		i := 2
		if l[2].isAtom("persistent") {
			p.pers = true
			i = 3
		}
		if len(l) != i+2 {
			return errAt(d, "(pred NAME [persistent] (SORT*) `function`)")
		}
		args, err := sortList(l[i])
		if err != nil {
			return err
		}
		r, err := rocqOf(l[i+1])
		if err != nil {
			return err
		}
		p.args, p.rocq = args, r
		t.preds = append(t.preds, p)
	case "rule":
		if len(l) < 2 || l[1].kind != nAtom {
			return errAt(d, "(rule NAME ...)")
		}
		tr, err := t.triple(d, l[2:], true)
		if err != nil {
			return err
		}
		t.rules = append(t.rules, ruleDecl{l[1].text, tr})
	case "fact":
		if len(l) != 5 || l[1].kind != nAtom || l[2].head() != "vars" || l[3].head() != "lhs" ||
			l[4].head() != "rhs" || len(l[3].list) != 2 || len(l[4].list) != 2 {
			return errAt(d, "(fact NAME (vars ..) (lhs TERM) (rhs TERM))")
		}
		vs, err := varList(l[2].list[1:])
		if err != nil {
			return err
		}
		t.facts = append(t.facts, factDecl{l[1].text, vs, l[3].list[1], l[4].list[1]})
	case "func":
		if len(l) < 3 || l[1].kind != nAtom {
			return errAt(d, "(func NAME `impl` ...)")
		}
		impl, err := rocqOf(l[2])
		if err != nil {
			return err
		}
		tr, err := t.triple(d, l[3:], false)
		if err != nil {
			return err
		}
		t.funcs = append(t.funcs, funcDecl{l[1].text, impl, tr})
	default:
		return errAt(d, "unknown declaration %v", d)
	}
	return nil
}

// Resolution of names to the checker's indices.

func (t *table) sortOf(n *node, name string) (tcheck.Sort, error) {
	switch name {
	case "val":
		return tcheck.Sort{Kind: tcheck.SortVal}, nil
	case "type":
		return tcheck.Sort{Kind: tcheck.SortType}, nil
	}
	for i, s := range t.sorts {
		if s.name == name {
			return tcheck.Sort{Kind: tcheck.SortUser, Num: uint64(i)}, nil
		}
	}
	return tcheck.Sort{}, errAt(n, "unknown sort %s", name)
}

func (t *table) symIndex(name string) int {
	for i, s := range t.syms {
		if s.name == name {
			return i
		}
	}
	return -1
}

func (t *table) predIndex(name string) int {
	for i, p := range t.preds {
		if p.name == name {
			return i
		}
	}
	return -1
}

// scope maps variable names to indices and sorts.
type scope struct {
	names []string
	sorts []tcheck.Sort
}

func (s *scope) index(x string) int {
	for i := len(s.names) - 1; i >= 0; i-- {
		if s.names[i] == x {
			return i
		}
	}
	return -1
}

func (t *table) addVars(n *node, sc *scope, vs []varDecl) error {
	for _, v := range vs {
		s, err := t.sortOf(n, v.sort)
		if err != nil {
			return err
		}
		if t.symIndex(v.name) >= 0 || v.name == "unit" {
			return errAt(n, "variable %s shadows a symbol", v.name)
		}
		sc.names = append(sc.names, v.name)
		sc.sorts = append(sc.sorts, s)
	}
	return nil
}

func (t *table) term(sc *scope, n *node) (*tcheck.Term, error) {
	if n.kind == nAtom {
		if n.text == "unit" {
			return &tcheck.Term{Kind: tcheck.TUnit}, nil
		}
		if i := sc.index(n.text); i >= 0 {
			return &tcheck.Term{Kind: tcheck.TVar, Num: uint64(i)}, nil
		}
		if i := t.symIndex(n.text); i >= 0 {
			return &tcheck.Term{Kind: tcheck.TSym, Num: uint64(i)}, nil
		}
		return nil, errAt(n, "unknown variable or symbol %s", n.text)
	}
	if n.kind != nList || len(n.list) == 0 || n.list[0].kind != nAtom {
		return nil, errAt(n, "expected a term, got %v", n)
	}
	var args []*tcheck.Term
	for _, c := range n.list[1:] {
		a, err := t.term(sc, c)
		if err != nil {
			return nil, err
		}
		args = append(args, a)
	}
	h := n.list[0].text
	switch h {
	case "pair":
		if len(args) != 2 {
			return nil, errAt(n, "(pair a b)")
		}
		return &tcheck.Term{Kind: tcheck.TPair, Args: args}, nil
	case "lit":
		if len(args) < 1 {
			return nil, errAt(n, "(lit TYPE elem*)")
		}
		return &tcheck.Term{Kind: tcheck.TLit, Args: args}, nil
	}
	i := t.symIndex(h)
	if i < 0 {
		return nil, errAt(n, "unknown symbol %s", h)
	}
	return &tcheck.Term{Kind: tcheck.TSym, Num: uint64(i), Args: args}, nil
}

func (t *table) pat(sc *scope, n *node) (*tcheck.Pat, error) {
	if n.head() == "app" {
		if len(n.list) != 3 {
			return nil, errAt(n, "(app PAT PAT)")
		}
		a, err := t.pat(sc, n.list[1])
		if err != nil {
			return nil, err
		}
		b, err := t.pat(sc, n.list[2])
		if err != nil {
			return nil, err
		}
		return &tcheck.Pat{Kind: tcheck.PApp, A: a, B: b}, nil
	}
	tm, err := t.term(sc, n)
	if err != nil {
		return nil, err
	}
	return &tcheck.Pat{Kind: tcheck.PVal, T: tm}, nil
}

func (t *table) atoms(sc *scope, ns []*node) ([]*tcheck.Atom, error) {
	var as []*tcheck.Atom
	for _, n := range ns {
		if n.kind != nList || len(n.list) == 0 || n.list[0].kind != nAtom {
			return nil, errAt(n, "expected an atom (PRED ..) or (= a b)")
		}
		var args []*tcheck.Term
		for _, c := range n.list[1:] {
			a, err := t.term(sc, c)
			if err != nil {
				return nil, err
			}
			args = append(args, a)
		}
		h := n.list[0].text
		if h == "=" {
			if len(args) != 2 {
				return nil, errAt(n, "(= a b)")
			}
			as = append(as, &tcheck.Atom{Kind: tcheck.AEq, Args: args})
			continue
		}
		i := t.predIndex(h)
		if i < 0 {
			return nil, errAt(n, "unknown predicate %s", h)
		}
		as = append(as, &tcheck.Atom{Kind: tcheck.APred, Num: uint64(i), Args: args})
	}
	return as, nil
}

func (t *table) symDecls() ([]tcheck.SymDecl, error) {
	var out []tcheck.SymDecl
	for _, s := range t.syms {
		d := tcheck.SymDecl{}
		for _, a := range s.args {
			so, err := t.sortOf(&node{}, a)
			if err != nil {
				return nil, fmt.Errorf("symbol %s: %v", s.name, err)
			}
			d.Args = append(d.Args, so)
		}
		r, err := t.sortOf(&node{}, s.res)
		if err != nil {
			return nil, fmt.Errorf("symbol %s: %v", s.name, err)
		}
		d.Res = r
		out = append(out, d)
	}
	return out, nil
}

func (t *table) predDecls() ([]tcheck.PredDecl, error) {
	var out []tcheck.PredDecl
	for _, p := range t.preds {
		d := tcheck.PredDecl{Pers: p.pers}
		for _, a := range p.args {
			so, err := t.sortOf(&node{}, a)
			if err != nil {
				return nil, fmt.Errorf("predicate %s: %v", p.name, err)
			}
			d.Args = append(d.Args, so)
		}
		out = append(out, d)
	}
	return out, nil
}

func (t *table) rule(r ruleDecl) (*tcheck.Rule, error) {
	sc := &scope{}
	n := r.lhs
	if err := t.addVars(n, sc, r.vars); err != nil {
		return nil, err
	}
	out := &tcheck.Rule{Vars: sc.sorts}
	var err error
	if out.Lhs, err = t.pat(sc, r.lhs); err != nil {
		return nil, err
	}
	if out.Pre, err = t.atoms(sc, r.pre); err != nil {
		return nil, err
	}
	all := &scope{names: append([]string{}, sc.names...), sorts: append([]tcheck.Sort{}, sc.sorts...)}
	if err := t.addVars(n, all, r.ex); err != nil {
		return nil, err
	}
	out.Ex = all.sorts[len(sc.sorts):]
	if out.Ret, err = t.term(all, r.ret); err != nil {
		return nil, err
	}
	if out.Post, err = t.atoms(all, r.post); err != nil {
		return nil, err
	}
	out.Vars = append([]tcheck.Sort{}, sc.sorts...)
	return out, nil
}

func (t *table) fact(f factDecl) (*tcheck.Fact, error) {
	sc := &scope{}
	if err := t.addVars(f.lhs, sc, f.vars); err != nil {
		return nil, err
	}
	l, err := t.term(sc, f.lhs)
	if err != nil {
		return nil, err
	}
	r, err := t.term(sc, f.rhs)
	if err != nil {
		return nil, err
	}
	return &tcheck.Fact{Vars: sc.sorts, Lhs: l, Rhs: r}, nil
}

func (t *table) spec(f funcDecl) (*tcheck.Spec, error) {
	sc := &scope{}
	n := f.ret
	if err := t.addVars(n, sc, f.vars); err != nil {
		return nil, err
	}
	out := &tcheck.Spec{}
	for _, a := range f.args {
		tm, err := t.term(sc, a)
		if err != nil {
			return nil, err
		}
		out.Args = append(out.Args, tm)
	}
	var err error
	if out.Pre, err = t.atoms(sc, f.pre); err != nil {
		return nil, err
	}
	all := &scope{names: append([]string{}, sc.names...), sorts: append([]tcheck.Sort{}, sc.sorts...)}
	if err := t.addVars(n, all, f.ex); err != nil {
		return nil, err
	}
	out.Vars = append([]tcheck.Sort{}, sc.sorts...)
	out.Ex = all.sorts[len(sc.sorts):]
	if out.Ret, err = t.term(all, f.ret); err != nil {
		return nil, err
	}
	if out.Post, err = t.atoms(all, f.post); err != nil {
		return nil, err
	}
	return out, nil
}

func (t *table) funcDecl(name string) (*funcDecl, error) {
	for i := range t.funcs {
		if t.funcs[i].name == name {
			return &t.funcs[i], nil
		}
	}
	return nil, fmt.Errorf("no (func %s ...) in the table", name)
}

// funcRule is the rule callers use for f: [spec_rule head spec]
// (new/tcheck/syntax.v), built the same way.
func (t *table) funcRule(f funcDecl) (*tcheck.Rule, error) {
	sp, err := t.spec(f)
	if err != nil {
		return nil, err
	}
	sc := &scope{}
	if err := t.addVars(f.ret, sc, f.vars); err != nil {
		return nil, err
	}
	h, err := t.term(sc, f.head)
	if err != nil {
		return nil, err
	}
	lhs := &tcheck.Pat{Kind: tcheck.PVal, T: h}
	for _, a := range sp.Args[1:] {
		lhs = &tcheck.Pat{Kind: tcheck.PApp, A: lhs, B: &tcheck.Pat{Kind: tcheck.PVal, T: a}}
	}
	return &tcheck.Rule{Vars: sp.Vars, Lhs: lhs, Pre: sp.Pre, Ex: sp.Ex, Ret: sp.Ret, Post: sp.Post}, nil
}

// allRules: the table's rules, then the rules of its funcs other than skip.
func (t *table) allRules(skip string) ([]*tcheck.Rule, []string, error) {
	var rs []*tcheck.Rule
	var names []string
	for _, rd := range t.rules {
		r, err := t.rule(rd)
		if err != nil {
			return nil, nil, fmt.Errorf("rule %s: %v", rd.name, err)
		}
		rs = append(rs, r)
		names = append(names, rd.name)
	}
	for _, fd := range t.funcs {
		if fd.name == skip {
			continue
		}
		r, err := t.funcRule(fd)
		if err != nil {
			return nil, nil, fmt.Errorf("func %s: %v", fd.name, err)
		}
		rs = append(rs, r)
		names = append(names, fd.name)
	}
	return rs, names, nil
}
