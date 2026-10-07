package main

import (
	"fmt"
	"os"
	"regexp"
	"strconv"
	"strings"
	"unicode"
	"unicode/utf8"

	"github.com/upamanyus/bootstrap-go/tcheck"
)

// Reading a function out of Goose's Lean output (e.g.
// .lake/packages/perennial/Perennial/Code/go_etcd_io/raft/v3.lean), as the
// checker's code. Goose prints a function as a plain term of GooseLang's
// constructors,
//
//	noncomputable def raft.becomeFollower.impl [FfiSyntax] [GoGlobalContext] : val :=
//	  (LamV "r"
//	  (Lam "term" ... (App (Val exceptionDo) (Let "r" (App (Val (GoInstruction ..)) (Var "r")) ..))))
//
// so the parser is one for Lean applications (identifiers, string and go!
// literals, numbers, #, parentheses and lists); the reifier recognizes the
// constructors and the exception monad's constants, and every leaf `Val v`
// is printed back as Lean text and looked up among the table's code
// constants. Nothing here is trusted: the generated observation file checks
// by `rfl` that the code's denotation is the Goose definition.

type gkind int

const (
	gIdent gkind = iota
	gStr         // a Lean string literal (text: its contents, unescaped)
	gGoStr       // go!"..." (text: its contents, unescaped)
	gNum
	gApp  // kids[0] applied to kids[1:]
	gList // [kids, ..]
	gHash // #kids[0]
	gUnit // ()
)

type gnode struct {
	kind gkind
	text string
	kids []*gnode
}

type gtok struct {
	kind string // "(", ")", "[", "]", ",", "#", "str", "gostr", "id", "num"
	text string
}

// leanString reads a Lean string literal starting at src[i] == '"'; it
// returns the unescaped contents and the index after the closing quote.
func leanString(src string, i int) (string, int, error) {
	var b strings.Builder
	j := i + 1
	for j < len(src) {
		c := src[j]
		switch c {
		case '"':
			return b.String(), j + 1, nil
		case '\\':
			if j+1 >= len(src) {
				return "", 0, fmt.Errorf("unterminated escape")
			}
			e := src[j+1]
			switch e {
			case '\\', '"', '\'':
				b.WriteByte(e)
				j += 2
			case 'n':
				b.WriteByte('\n')
				j += 2
			case 't':
				b.WriteByte('\t')
				j += 2
			case 'r':
				b.WriteByte('\r')
				j += 2
			case 'x':
				if j+4 > len(src) {
					return "", 0, fmt.Errorf("bad \\x escape")
				}
				n, err := strconv.ParseUint(src[j+2:j+4], 16, 8)
				if err != nil {
					return "", 0, fmt.Errorf("bad \\x escape")
				}
				b.WriteRune(rune(n))
				j += 4
			case 'u':
				k := strings.IndexByte(src[j:], '}')
				if j+2 >= len(src) || src[j+2] != '{' || k < 0 {
					return "", 0, fmt.Errorf("bad \\u escape")
				}
				n, err := strconv.ParseUint(src[j+3:j+k], 16, 32)
				if err != nil {
					return "", 0, fmt.Errorf("bad \\u escape")
				}
				b.WriteRune(rune(n))
				j += k + 1
			default:
				return "", 0, fmt.Errorf("unsupported escape \\%c", e)
			}
		default:
			b.WriteByte(c)
			j++
		}
	}
	return "", 0, fmt.Errorf("unterminated string")
}

// leanQuote writes s as a Lean string literal.
func leanQuote(s string) string {
	var b strings.Builder
	b.WriteByte('"')
	for _, r := range s {
		switch r {
		case '"':
			b.WriteString("\\\"")
		case '\\':
			b.WriteString("\\\\")
		case '\n':
			b.WriteString("\\n")
		case '\t':
			b.WriteString("\\t")
		case '\r':
			b.WriteString("\\r")
		default:
			b.WriteRune(r)
		}
	}
	b.WriteByte('"')
	return b.String()
}

func isIdentStart(r rune) bool { return unicode.IsLetter(r) || r == '_' || r == '«' }

func isIdentRest(r rune) bool {
	return unicode.IsLetter(r) || unicode.IsDigit(r) || r == '_' || r == '.' || r == '\'' || r == '!' ||
		r == '?' || r == '«' || r == '»' || unicode.Is(unicode.Lm, r) || (r >= '₀' && r <= '₉')
}

func gooseTokens(src string) ([]gtok, error) {
	var ts []gtok
	i := 0
	for i < len(src) {
		r, w := utf8.DecodeRuneInString(src[i:])
		switch {
		case unicode.IsSpace(r):
			i += w
		case strings.ContainsRune("()[],#", r):
			ts = append(ts, gtok{kind: string(r)})
			i += w
		case strings.HasPrefix(src[i:], "go!\""):
			s, j, err := leanString(src, i+3)
			if err != nil {
				return nil, err
			}
			ts = append(ts, gtok{kind: "gostr", text: s})
			i = j
		case r == '"':
			s, j, err := leanString(src, i)
			if err != nil {
				return nil, err
			}
			ts = append(ts, gtok{kind: "str", text: s})
			i = j
		case unicode.IsDigit(r):
			j := i
			for j < len(src) && src[j] >= '0' && src[j] <= '9' {
				j++
			}
			ts = append(ts, gtok{kind: "num", text: src[i:j]})
			i = j
		case isIdentStart(r):
			j := i + w
			for j < len(src) {
				r2, w2 := utf8.DecodeRuneInString(src[j:])
				if !isIdentRest(r2) || (r2 == '!' && strings.HasPrefix(src[j:], "!\"")) {
					break
				}
				j += w2
			}
			ts = append(ts, gtok{kind: "id", text: src[i:j]})
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
	switch p.peek().kind {
	case "(", "[", "str", "gostr", "num", "#", "id":
		return true
	}
	return false
}

// expr: an application of atoms.
func (p *gparser) expr() (*gnode, error) {
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
		if p.peek().kind == ")" {
			p.next()
			return &gnode{kind: gUnit}, nil
		}
		e, err := p.expr()
		if err != nil {
			return nil, err
		}
		return e, p.expect(")")
	case "[":
		n := &gnode{kind: gList}
		if p.peek().kind == "]" {
			p.next()
			return n, nil
		}
		for {
			e, err := p.expr()
			if err != nil {
				return nil, err
			}
			n.kids = append(n.kids, e)
			if p.peek().kind == "," {
				p.next()
				continue
			}
			return n, p.expect("]")
		}
	case "str":
		return &gnode{kind: gStr, text: t.text}, nil
	case "gostr":
		return &gnode{kind: gGoStr, text: t.text}, nil
	case "num":
		return &gnode{kind: gNum, text: t.text}, nil
	case "id":
		return &gnode{kind: gIdent, text: t.text}, nil
	case "#":
		a, err := p.atom()
		if err != nil {
			return nil, err
		}
		return &gnode{kind: gHash, kids: []*gnode{a}}, nil
	}
	return nil, fmt.Errorf("unexpected token %s %q", t.kind, t.text)
}

// The code file: the body of a definition in a namespace.

type codeFile struct {
	namespace string
	src       string
}

func loadCode(path, namespace string) (*codeFile, error) {
	b, err := os.ReadFile(path)
	if err != nil {
		return nil, err
	}
	src := string(b)
	start := strings.Index(src, "\nnamespace "+namespace+"\n")
	if start < 0 {
		return nil, fmt.Errorf("%s: no namespace %s", path, namespace)
	}
	end := strings.Index(src[start:], "\nend "+namespace+"\n")
	if end < 0 {
		end = len(src)
	} else {
		end += start
	}
	return &codeFile{namespace: namespace, src: src[start:end]}, nil
}

// definition returns the body of `def name … : val :=`, the indented
// lines that follow it.
func (cf *codeFile) definition(name string) (string, error) {
	re := regexp.MustCompile(`(?m)^(?:noncomputable )?def ` + regexp.QuoteMeta(name) + ` [^\n]*:=\n`)
	loc := re.FindStringIndex(cf.src)
	if loc == nil {
		return "", fmt.Errorf("no def %s in namespace %s of the code file", name, cf.namespace)
	}
	var body []string
	for _, l := range strings.Split(cf.src[loc[1]:], "\n") {
		if !strings.HasPrefix(l, "  ") {
			break
		}
		body = append(body, l)
	}
	if len(body) == 0 {
		return "", fmt.Errorf("def %s has no body", name)
	}
	return strings.Join(body, "\n"), nil
}

// qualify names a definition of the code file's namespace.
func (cf *codeFile) qualify(id string) string { return cf.namespace + "." + id }

// Printing leaves back as Lean.

func printLean(g *gnode) string {
	switch g.kind {
	case gIdent, gNum:
		return g.text
	case gStr:
		return leanQuote(g.text)
	case gGoStr:
		return "go!" + leanQuote(g.text)
	case gUnit:
		return "()"
	case gHash:
		a := g.kids[0]
		if a.kind == gIdent || a.kind == gNum || a.kind == gUnit {
			return "#" + printLean(a)
		}
		return "#(" + printLean(a) + ")"
	case gList:
		var parts []string
		for _, k := range g.kids {
			parts = append(parts, printLean(k))
		}
		return "[" + strings.Join(parts, ", ") + "]"
	case gApp:
		var parts []string
		for _, k := range g.kids {
			parts = append(parts, printArg(k))
		}
		return strings.Join(parts, " ")
	}
	return fmt.Sprintf("<unprintable %d>", g.kind)
}

func printArg(g *gnode) string {
	if g.kind == gApp {
		return "(" + printLean(g) + ")"
	}
	return printLean(g)
}

// normLean canonicalizes Lean text for comparison: whitespace runs become
// one space, and there is none just inside brackets or before a comma.
func normLean(s string) string {
	s = strings.Join(strings.Fields(s), " ")
	for _, r := range []struct{ a, b string }{{"( ", "("}, {" )", ")"}, {"[ ", "["}, {" ]", "]"}, {" ,", ","}} {
		s = strings.ReplaceAll(s, r.a, r.b)
	}
	return s
}

type reifier struct {
	t       *table
	missing map[string]bool
}

func (r *reifier) leaf(text string, sort tcheck.SortKind) *tcheck.Term {
	if text == "#()" {
		return &tcheck.Term{Kind: tcheck.TUnit}
	}
	want := normLean(text)
	for i, s := range r.t.syms {
		res := tcheck.SortVal
		if s.res == "type" {
			res = tcheck.SortType
		}
		if s.const_ && res == sort && normLean(s.lean) == want {
			return &tcheck.Term{Kind: tcheck.TSym, Num: uint64(i)}
		}
	}
	r.missing[fmt.Sprintf("(%s NAME `%s`)", map[tcheck.SortKind]string{tcheck.SortVal: "const", tcheck.SortType: "tconst"}[sort], want)] = true
	return &tcheck.Term{Kind: tcheck.TUnit}
}

func isIdent(g *gnode, s string) bool { return g.kind == gIdent && g.text == s }

// isCon: g is the constructor c applied to n arguments.
func isCon(g *gnode, c string, n int) bool {
	return g.kind == gApp && len(g.kids) == n+1 && isIdent(g.kids[0], c)
}

// valOf: g is `Val c` for the constant c.
func valOf(g *gnode, c string) bool { return isCon(g, "Val", 1) && isIdent(g.kids[1], c) }

func (r *reifier) expr(g *gnode) (*tcheck.Expr, error) {
	two := func(k tcheck.ExprKind, name string, a, b *gnode) (*tcheck.Expr, error) {
		ea, err := r.expr(a)
		if err != nil {
			return nil, err
		}
		eb, err := r.expr(b)
		if err != nil {
			return nil, err
		}
		return &tcheck.Expr{Kind: k, Name: name, A: ea, B: eb}, nil
	}
	switch {
	case isCon(g, "Val", 1):
		return &tcheck.Expr{Kind: tcheck.EVal, T: r.leaf(printLean(g.kids[1]), tcheck.SortVal)}, nil
	case isCon(g, "Var", 1) && g.kids[1].kind == gStr:
		return &tcheck.Expr{Kind: tcheck.EVar, Name: g.kids[1].text}, nil
	case isCon(g, "App", 2):
		f, a := g.kids[1], g.kids[2]
		for _, m := range []struct {
			c string
			k tcheck.ExprKind
		}{{"exceptionDo", tcheck.EXDo}, {"doExecute", tcheck.EDo}, {"doReturn", tcheck.ERet}} {
			if valOf(f, m.c) {
				ea, err := r.expr(a)
				if err != nil {
					return nil, err
				}
				return &tcheck.Expr{Kind: m.k, A: ea}, nil
			}
		}
		// a ;;; b is exceptionSeq (λ: <>, b) a.
		if isCon(f, "App", 2) && valOf(f.kids[1], "exceptionSeq") && isCon(f.kids[2], "Lam", 2) &&
			isIdent(f.kids[2].kids[1], "BAnon") {
			return two(tcheck.EXSeq, "", a, f.kids[2].kids[2])
		}
		return two(tcheck.EApp, "", f, a)
	case isCon(g, "Pair", 2):
		return two(tcheck.EPair, "", g.kids[1], g.kids[2])
	case isCon(g, "Let", 3) && g.kids[1].kind == gStr:
		return two(tcheck.ELet, g.kids[1].text, g.kids[2], g.kids[3])
	case isCon(g, "Let", 3) && isIdent(g.kids[1], "BAnon"), isCon(g, "Seq", 2):
		n := len(g.kids)
		return two(tcheck.ESeq, "", g.kids[n-2], g.kids[n-1])
	case isCon(g, "LiteralValue", 1):
		return r.literal(g.kids[1])
	}
	return nil, fmt.Errorf("unsupported code: %s", excerpt(printLean(g), 0))
}

// literal: LiteralValue [(KeyedElement none (ElementExpression T e)), ..].
func (r *reifier) literal(l *gnode) (*tcheck.Expr, error) {
	if l.kind != gList {
		return nil, fmt.Errorf("LiteralValue of a non-list")
	}
	out := &tcheck.Expr{Kind: tcheck.ELit}
	var ty string
	for _, k := range l.kids {
		if !isCon(k, "KeyedElement", 2) || !isIdent(k.kids[1], "none") ||
			!isCon(k.kids[2], "ElementExpression", 2) {
			return nil, fmt.Errorf("unsupported literal element %s", printLean(k))
		}
		ee := k.kids[2]
		t := printLean(ee.kids[1])
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

// reifyFunc reads `def impl … : val := (LamV x1 (Lam x2 .. body))`.
func reifyFunc(t *table, impl string) (*tcheck.Func, error) {
	cf, err := loadCode(t.codeFile, t.namespace)
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
	g, err := p.expr()
	if err != nil {
		return nil, fmt.Errorf("%s: %v", impl, err)
	}
	if p.peek().kind != "eof" {
		return nil, fmt.Errorf("%s: trailing tokens at %d", impl, p.i)
	}
	if !isCon(g, "LamV", 2) {
		return nil, fmt.Errorf("%s is not LamV ..", impl)
	}
	var params []string
	for first := true; first || isCon(g, "Lam", 2); first = false {
		x := g.kids[1]
		if x.kind != gStr {
			return nil, fmt.Errorf("%s: anonymous parameters are not supported yet", impl)
		}
		params = append(params, x.text)
		g = g.kids[2]
	}
	r := &reifier{t: t, missing: map[string]bool{}}
	e, err := r.expr(g)
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
	return &tcheck.Func{Params: params, Body: e}, nil
}
