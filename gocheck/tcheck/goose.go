package main

import (
	"fmt"
	"os"
	"regexp"
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/upamanyus/bootstrap-go/tcheck"
)

// Reading a function out of Goose's Rocq output (new/code/...), as the
// checker's code. The parser knows the notations Goose prints (λ:, let:,
// do:, return:, ;;;, ;;, <-[t], ![t], #) and treats everything else as
// Rocq application; the leaves (values and Go types) are printed back as
// Rocq text and looked up among the table's code constants. Nothing here is
// trusted: the generated observation file checks by reflexivity that the
// code's denotation is the Goose definition.

type gkind int

const (
	gIdent gkind = iota
	gStr         // a string literal; goStr: with %go
	gNum
	gApp // kids[0] applied to kids[1:]
	gList
	gHash // #kids[0]
	gUnit // #()
	gLam  // params, kids[0]
	gLet  // text, kids[0], kids[1]
	gDo
	gRet
	gXSeq
	gSeq
	gLoad  // kids[0] type, kids[1]
	gStore // kids[0] type, kids[1], kids[2]
	gPair
)

type gnode struct {
	kind   gkind
	text   string
	goStr  bool
	kids   []*gnode
	params []string
}

type gtok struct {
	kind string // "(", ")", "[", "]", ",", ";", ";;", ";;;", ":=", "λ:", "let:", "do:", "return:", "<-[", "![", "#", "<>", "str", "gostr", "id", "num"
	text string
}

func gooseTokens(src string) ([]gtok, error) {
	var ts []gtok
	i := 0
	for i < len(src) {
		r, w := utf8.DecodeRuneInString(src[i:])
		switch {
		case unicode.IsSpace(r):
			i += w
		case strings.HasPrefix(src[i:], ";;;"):
			ts = append(ts, gtok{kind: ";;;"})
			i += 3
		case strings.HasPrefix(src[i:], ";;"):
			ts = append(ts, gtok{kind: ";;"})
			i += 2
		case strings.HasPrefix(src[i:], ":="):
			ts = append(ts, gtok{kind: ":="})
			i += 2
		case strings.HasPrefix(src[i:], "λ:"):
			ts = append(ts, gtok{kind: "λ:"})
			i += len("λ:")
		case strings.HasPrefix(src[i:], "<-["):
			ts = append(ts, gtok{kind: "<-["})
			i += 3
		case strings.HasPrefix(src[i:], "!["):
			ts = append(ts, gtok{kind: "!["})
			i += 2
		case strings.HasPrefix(src[i:], "<>"):
			ts = append(ts, gtok{kind: "<>"})
			i += 2
		case strings.ContainsRune("()[],;#", r):
			ts = append(ts, gtok{kind: string(r)})
			i += w
		case r == '"':
			j := i + 1
			for j < len(src) && src[j] != '"' {
				j++
			}
			if j >= len(src) {
				return nil, fmt.Errorf("unterminated string")
			}
			s := src[i+1 : j]
			j++
			k := "str"
			if strings.HasPrefix(src[j:], "%go") {
				k = "gostr"
				j += 3
			}
			ts = append(ts, gtok{kind: k, text: s})
			i = j
		case unicode.IsDigit(r):
			j := i
			for j < len(src) && src[j] >= '0' && src[j] <= '9' {
				j++
			}
			ts = append(ts, gtok{kind: "num", text: src[i:j]})
			i = j
		case unicode.IsLetter(r) || r == '_' || r == '@':
			j := i
			for j < len(src) {
				r2, w2 := utf8.DecodeRuneInString(src[j:])
				if unicode.IsLetter(r2) || unicode.IsDigit(r2) || r2 == '_' || r2 == '.' || r2 == '\'' ||
					unicode.Is(unicode.Lm, r2) || (r2 == '@' && j == i) {
					j += w2
				} else {
					break
				}
			}
			id := src[i:j]
			switch id {
			case "let", "do", "return", "if":
				if j < len(src) && src[j] == ':' {
					ts = append(ts, gtok{kind: id + ":"})
					i = j + 1
					continue
				}
			}
			ts = append(ts, gtok{kind: "id", text: id})
			i = j
		default:
			return nil, fmt.Errorf("unexpected character %q in %q", r, excerpt(src, i))
		}
	}
	return ts, nil
}

func excerpt(s string, i int) string {
	j := i + 40
	if j > len(s) {
		j = len(s)
	}
	return s[i:j]
}

type gparser struct {
	ts []gtok
	i  int
}

func (p *gparser) peek() gtok {
	if p.i < len(p.ts) {
		return p.ts[p.i]
	}
	return gtok{kind: "eof"}
}

func (p *gparser) next() gtok {
	t := p.peek()
	p.i++
	return t
}

func (p *gparser) expect(k string) error {
	t := p.next()
	if t.kind != k {
		return fmt.Errorf("expected %s, got %s %q (token %d)", k, t.kind, t.text, p.i-1)
	}
	return nil
}

func (p *gparser) startsAtom() bool {
	t := p.peek()
	switch t.kind {
	case "(", "[", "str", "gostr", "num", "#", "![":
		return true
	case "id":
		return t.text != "in" && t.text != "then" && t.text != "else"
	}
	return false
}

// expr parses at the given Rocq level: 200 takes everything, 85 stops
// before ;;;, 79 before <-[ .. ].
func (p *gparser) expr(lvl int) (*gnode, error) {
	var left *gnode
	switch p.peek().kind {
	case "λ:":
		p.next()
		n := &gnode{kind: gLam}
		for p.peek().kind != "," {
			t := p.next()
			if t.kind == "str" {
				n.params = append(n.params, t.text)
			} else if t.kind == "<>" {
				n.params = append(n.params, "")
			} else {
				return nil, fmt.Errorf("λ: expects parameter names, got %q", t.text)
			}
		}
		p.next()
		body, err := p.expr(200)
		if err != nil {
			return nil, err
		}
		n.kids = []*gnode{body}
		return n, nil
	case "let:":
		p.next()
		x := p.next()
		if x.kind != "str" {
			return nil, fmt.Errorf("let: expects a name")
		}
		if err := p.expect(":="); err != nil {
			return nil, err
		}
		a, err := p.expr(200)
		if err != nil {
			return nil, err
		}
		if t := p.next(); t.kind != "id" || t.text != "in" {
			return nil, fmt.Errorf("let: expects in")
		}
		b, err := p.expr(200)
		if err != nil {
			return nil, err
		}
		return &gnode{kind: gLet, text: x.text, kids: []*gnode{a, b}}, nil
	case "do:", "return:":
		k := gDo
		if p.next().kind == "return:" {
			k = gRet
		}
		a, err := p.expr(85)
		if err != nil {
			return nil, err
		}
		left = &gnode{kind: k, kids: []*gnode{a}}
	case "if:":
		return nil, fmt.Errorf("if: is not supported yet")
	default:
		var err error
		left, err = p.app()
		if err != nil {
			return nil, err
		}
	}
	for {
		switch p.peek().kind {
		case "<-[":
			if lvl < 80 {
				return left, nil
			}
			p.next()
			ty, err := p.expr(200)
			if err != nil {
				return nil, err
			}
			if err := p.expect("]"); err != nil {
				return nil, err
			}
			rhs, err := p.expr(79)
			if err != nil {
				return nil, err
			}
			left = &gnode{kind: gStore, kids: []*gnode{ty, left, rhs}}
		case ";;;":
			if lvl < 90 {
				return left, nil
			}
			p.next()
			rhs, err := p.expr(200)
			if err != nil {
				return nil, err
			}
			left = &gnode{kind: gXSeq, kids: []*gnode{left, rhs}}
		case ";;":
			if lvl < 100 {
				return left, nil
			}
			p.next()
			rhs, err := p.expr(200)
			if err != nil {
				return nil, err
			}
			left = &gnode{kind: gSeq, kids: []*gnode{left, rhs}}
		default:
			return left, nil
		}
	}
}

func (p *gparser) app() (*gnode, error) {
	h, err := p.atom()
	if err != nil {
		return nil, err
	}
	if !p.startsAtom() {
		return h, nil
	}
	n := &gnode{kind: gApp, kids: []*gnode{h}}
	for p.startsAtom() {
		a, err := p.atom()
		if err != nil {
			return nil, err
		}
		n.kids = append(n.kids, a)
	}
	return n, nil
}

func (p *gparser) atom() (*gnode, error) {
	t := p.next()
	switch t.kind {
	case "(":
		e, err := p.expr(200)
		if err != nil {
			return nil, err
		}
		if p.peek().kind == "," {
			p.next()
			e2, err := p.expr(200)
			if err != nil {
				return nil, err
			}
			e = &gnode{kind: gPair, kids: []*gnode{e, e2}}
		}
		return e, p.expect(")")
	case "[":
		n := &gnode{kind: gList}
		if p.peek().kind == "]" {
			p.next()
			return n, nil
		}
		for {
			e, err := p.expr(200)
			if err != nil {
				return nil, err
			}
			n.kids = append(n.kids, e)
			if p.peek().kind == ";" {
				p.next()
				continue
			}
			return n, p.expect("]")
		}
	case "str":
		return &gnode{kind: gStr, text: t.text}, nil
	case "gostr":
		return &gnode{kind: gStr, text: t.text, goStr: true}, nil
	case "num":
		return &gnode{kind: gNum, text: t.text}, nil
	case "id":
		return &gnode{kind: gIdent, text: t.text}, nil
	case "#":
		if p.peek().kind == "(" && p.i+1 < len(p.ts) && p.ts[p.i+1].kind == ")" {
			p.i += 2
			return &gnode{kind: gUnit}, nil
		}
		a, err := p.atom()
		if err != nil {
			return nil, err
		}
		return &gnode{kind: gHash, kids: []*gnode{a}}, nil
	case "![":
		ty, err := p.expr(200)
		if err != nil {
			return nil, err
		}
		if err := p.expect("]"); err != nil {
			return nil, err
		}
		a, err := p.atom()
		if err != nil {
			return nil, err
		}
		return &gnode{kind: gLoad, kids: []*gnode{ty, a}}, nil
	}
	return nil, fmt.Errorf("unexpected token %s %q", t.kind, t.text)
}

// The code file: the definition of a function, and the names its module
// defines (which the leaves print qualified).

type codeFile struct {
	module string
	defs   map[string]bool
	src    string
}

var defRe = regexp.MustCompile(`(?m)^Definition (\S+)`)

func loadCode(path, module string) (*codeFile, error) {
	b, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	src := string(b)
	start := strings.Index(src, "\nModule "+module+".\n")
	if start < 0 {
		return nil, fmt.Errorf("%s: no Module %s", path, module)
	}
	end := strings.LastIndex(src, "\nEnd "+module+".")
	if end < 0 {
		end = len(src)
	}
	cf := &codeFile{module: module, defs: map[string]bool{}, src: src}
	for _, m := range defRe.FindAllStringSubmatch(src[start:end], -1) {
		cf.defs[m[1]] = true
	}
	return cf, nil
}

// definition returns the body of [Definition name ... : val := BODY.].
func (cf *codeFile) definition(name string) (string, error) {
	hdr := "\nDefinition " + name + " "
	i := strings.Index(cf.src, hdr)
	if i < 0 {
		return "", fmt.Errorf("no Definition %s in the code file", name)
	}
	j := strings.Index(cf.src[i:], ":=")
	if j < 0 {
		return "", fmt.Errorf("Definition %s has no body", name)
	}
	body := cf.src[i+j+2:]
	// The body ends at the first "." that ends a line outside a string.
	inStr := false
	for k := 0; k < len(body); k++ {
		c := body[k]
		if c == '"' {
			inStr = !inStr
		}
		if c == '.' && !inStr && (k+1 == len(body) || body[k+1] == '\n') {
			return body[:k], nil
		}
	}
	return "", fmt.Errorf("Definition %s does not end", name)
}

// Printing leaves back as Rocq.

func (cf *codeFile) qualify(id string) string {
	if cf.defs[id] {
		return cf.module + "." + id
	}
	return id
}

func (cf *codeFile) print(g *gnode) string {
	switch g.kind {
	case gIdent:
		return cf.qualify(g.text)
	case gNum:
		return g.text
	case gStr:
		if g.goStr {
			return "\"" + g.text + "\"%go"
		}
		return "\"" + g.text + "\""
	case gUnit:
		return "#()"
	case gHash:
		a := g.kids[0]
		if a.kind == gIdent || a.kind == gStr || a.kind == gNum {
			return "#" + cf.print(a)
		}
		return "#(" + cf.print(a) + ")"
	case gList:
		var parts []string
		for _, k := range g.kids {
			parts = append(parts, cf.print(k))
		}
		return "[" + strings.Join(parts, "; ") + "]"
	case gApp:
		parts := []string{cf.printArg(g.kids[0])}
		for _, k := range g.kids[1:] {
			parts = append(parts, cf.printArg(k))
		}
		return strings.Join(parts, " ")
	case gPair:
		return "(" + cf.print(g.kids[0]) + ", " + cf.print(g.kids[1]) + ")"
	}
	return fmt.Sprintf("<unprintable %d>", g.kind)
}

func (cf *codeFile) printArg(g *gnode) string {
	if g.kind == gApp {
		return "(" + cf.print(g) + ")"
	}
	return cf.print(g)
}

// normRocq canonicalizes Rocq text for comparison: whitespace runs become
// one space, and there is none just inside brackets.
func normRocq(s string) string {
	s = strings.Join(strings.Fields(s), " ")
	for _, r := range []struct{ a, b string }{{"( ", "("}, {" )", ")"}, {"[ ", "["}, {" ]", "]"}} {
		s = strings.ReplaceAll(s, r.a, r.b)
	}
	return s
}

// instruction heads: the number of static arguments of each GoInstruction
// constructor Goose applies directly.
var instrArity = map[string]int{
	"GoAlloc": 1, "GoLoad": 1, "GoStore": 1, "GoZeroVal": 1, "Convert": 2,
	"FuncResolve": 2, "MethodResolve": 2, "StructFieldRef": 2, "StructFieldGet": 2,
	"StructFieldSet": 2, "CompositeLiteral": 1, "IndexRef": 1, "Index": 1,
	"TypeAssert": 1, "TypeAssert2": 1, "GlobalVarAddr": 1,
}

type reifier struct {
	t       *table
	cf      *codeFile
	missing map[string]bool
}

func (r *reifier) leaf(text string, sort tcheck.SortKind) *tcheck.Term {
	if text == "#()" {
		return &tcheck.Term{Kind: tcheck.TUnit}
	}
	want := normRocq(text)
	for i, s := range r.t.syms {
		res := tcheck.SortVal
		if s.res == "type" {
			res = tcheck.SortType
		}
		if s.const_ && res == sort && normRocq(s.rocq) == want {
			return &tcheck.Term{Kind: tcheck.TSym, Num: uint64(i)}
		}
	}
	r.missing[fmt.Sprintf("(%s NAME `%s`)", map[tcheck.SortKind]string{tcheck.SortVal: "const", tcheck.SortType: "tconst"}[sort], want)] = true
	return &tcheck.Term{Kind: tcheck.TUnit}
}

func (r *reifier) val(text string) *tcheck.Expr {
	return &tcheck.Expr{Kind: tcheck.EVal, T: r.leaf(text, tcheck.SortVal)}
}

func app(f *tcheck.Expr, a *tcheck.Expr) *tcheck.Expr {
	return &tcheck.Expr{Kind: tcheck.EApp, A: f, B: a}
}

func (r *reifier) expr(g *gnode) (*tcheck.Expr, error) {
	switch g.kind {
	case gStr:
		if !g.goStr {
			return &tcheck.Expr{Kind: tcheck.EVar, Name: g.text}, nil
		}
	case gHash, gUnit, gIdent, gNum:
		return r.val(r.cf.print(g)), nil
	case gLet, gXSeq, gSeq:
		a, err := r.expr(g.kids[0])
		if err != nil {
			return nil, err
		}
		b, err := r.expr(g.kids[1])
		if err != nil {
			return nil, err
		}
		k := map[gkind]tcheck.ExprKind{gLet: tcheck.ELet, gXSeq: tcheck.EXSeq, gSeq: tcheck.ESeq}[g.kind]
		return &tcheck.Expr{Kind: k, Name: g.text, A: a, B: b}, nil
	case gDo, gRet:
		a, err := r.expr(g.kids[0])
		if err != nil {
			return nil, err
		}
		k := tcheck.EDo
		if g.kind == gRet {
			k = tcheck.ERet
		}
		return &tcheck.Expr{Kind: k, A: a}, nil
	case gLoad:
		a, err := r.expr(g.kids[1])
		if err != nil {
			return nil, err
		}
		return app(r.val("GoInstruction (GoLoad "+r.cf.printArg(g.kids[0])+")"), a), nil
	case gStore:
		a, err := r.expr(g.kids[1])
		if err != nil {
			return nil, err
		}
		b, err := r.expr(g.kids[2])
		if err != nil {
			return nil, err
		}
		return app(r.val("GoInstruction (GoStore "+r.cf.printArg(g.kids[0])+")"),
			&tcheck.Expr{Kind: tcheck.EPair, A: a, B: b}), nil
	case gPair:
		a, err := r.expr(g.kids[0])
		if err != nil {
			return nil, err
		}
		b, err := r.expr(g.kids[1])
		if err != nil {
			return nil, err
		}
		return &tcheck.Expr{Kind: tcheck.EPair, A: a, B: b}, nil
	case gApp:
		h := g.kids[0]
		args := g.kids[1:]
		var f *tcheck.Expr
		if h.kind == gIdent && h.text == "exception_do" && len(args) == 1 {
			a, err := r.expr(args[0])
			if err != nil {
				return nil, err
			}
			return &tcheck.Expr{Kind: tcheck.EXDo, A: a}, nil
		}
		if h.kind == gIdent && h.text == "LiteralValue" && len(args) == 1 {
			return r.literal(args[0])
		}
		if h.kind == gIdent {
			if k, ok := instrArity[h.text]; ok {
				if len(args) < k {
					return nil, fmt.Errorf("%s needs %d static arguments", h.text, k)
				}
				st := &gnode{kind: gApp, kids: append([]*gnode{h}, args[:k]...)}
				f = r.val("GoInstruction (" + r.cf.print(st) + ")")
				args = args[k:]
			}
		}
		if f == nil {
			var err error
			if f, err = r.expr(h); err != nil {
				return nil, err
			}
		}
		for _, a := range args {
			ea, err := r.expr(a)
			if err != nil {
				return nil, err
			}
			f = app(f, ea)
		}
		return f, nil
	}
	return nil, fmt.Errorf("unsupported code: %s", r.cf.print(g))
}

// literal: LiteralValue [KeyedElement None (ElementExpression T e); ..].
func (r *reifier) literal(l *gnode) (*tcheck.Expr, error) {
	if l.kind != gList {
		return nil, fmt.Errorf("LiteralValue of a non-list")
	}
	out := &tcheck.Expr{Kind: tcheck.ELit}
	var ty string
	for _, k := range l.kids {
		if k.kind != gApp || len(k.kids) != 3 || !isIdent(k.kids[0], "KeyedElement") ||
			!isIdent(k.kids[1], "None") {
			return nil, fmt.Errorf("unsupported literal element %s", r.cf.print(k))
		}
		ee := k.kids[2]
		if ee.kind != gApp || len(ee.kids) != 3 || !isIdent(ee.kids[0], "ElementExpression") {
			return nil, fmt.Errorf("unsupported literal element %s", r.cf.print(k))
		}
		t := r.cf.print(ee.kids[1])
		if ty != "" && t != ty {
			return nil, fmt.Errorf("literal elements of different types")
		}
		ty = t
		e, err := r.expr(ee.kids[2])
		if err != nil {
			return nil, err
		}
		out.Elems = append(out.Elems, e)
	}
	if ty == "" {
		return nil, fmt.Errorf("empty literals are not supported")
	}
	out.T = r.leaf(ty, tcheck.SortType)
	return out, nil
}

func isIdent(g *gnode, s string) bool { return g.kind == gIdent && g.text == s }

// reifyFunc reads [Definition impl ... := λ: x1 .. xn, body.].
func reifyFunc(t *table, impl string) (*tcheck.Func, error) {
	cf, err := loadCode(t.codeFile, t.module)
	if err != nil {
		return nil, err
	}
	body, err := cf.definition(impl)
	if err != nil {
		return nil, err
	}
	ts, err := gooseTokens(body)
	if err != nil {
		return nil, fmt.Errorf("%s: %v", impl, err)
	}
	p := &gparser{ts: ts}
	g, err := p.expr(200)
	if err != nil {
		return nil, fmt.Errorf("%s: %v", impl, err)
	}
	if p.peek().kind != "eof" {
		return nil, fmt.Errorf("%s: trailing tokens at %d", impl, p.i)
	}
	if g.kind != gLam {
		return nil, fmt.Errorf("%s is not λ: ..", impl)
	}
	for _, x := range g.params {
		if x == "" {
			return nil, fmt.Errorf("%s: anonymous parameters are not supported yet", impl)
		}
	}
	r := &reifier{t: t, cf: cf, missing: map[string]bool{}}
	e, err := r.expr(g.kids[0])
	if err != nil {
		return nil, fmt.Errorf("%s: %v", impl, err)
	}
	if len(r.missing) > 0 {
		var ms []string
		for m := range r.missing {
			ms = append(ms, "  "+m)
		}
		return nil, fmt.Errorf("%s: the code uses constants the table does not declare; add:\n%s",
			impl, strings.Join(ms, "\n"))
	}
	return &tcheck.Func{Params: g.params, Body: e}, nil
}
