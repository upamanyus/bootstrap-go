package tcheck

// Parsing the serialized input. The format is one S-expression with single
// spaces between items and no other whitespace; [ser_input] in
// new/tcheck/syntax.v writes exactly this format, and Parse accepts nothing
// else.
//
//	input ::= (input (syms sym*) (preds pred*) (rules rule*) (facts fact*) func spec)
//	sym   ::= (sym (srt*) srt)
//	pred  ::= (pred b (srt*))                     b is 0 or 1 (persistent)
//	rule  ::= (rule (srt*) pat (atom*) (srt*) term (atom*))
//	fact  ::= (fact (srt*) term term)
//	func  ::= (func (str*) expr)
//	spec  ::= (spec (srt*) (term*) (atom*) (srt*) term (atom*))
//	srt   ::= v | y | (u n)
//	term  ::= (var n) | (sym n term*) | (pair term term) | (lit term term*) | unit
//	pat   ::= (pval term) | (papp pat pat)
//	atom  ::= (pred n term*) | (eq term term)
//	expr  ::= (val term) | (cvar str) | (app expr expr) | (cpair expr expr)
//	        | (let str expr expr) | (seq expr expr) | (clit term expr*)
//	        | (do expr) | (ret expr) | (xseq expr expr) | (xdo expr)
//	str   ::= a double quote, bytes other than a double quote or a backslash,
//	          a double quote
//	n     ::= decimal digits, at most 18 of them

type parser struct {
	b   []byte
	i   uint64
	bad bool
}

func (p *parser) fail() {
	p.bad = true
}

func (p *parser) peek() byte {
	if p.i < uint64(len(p.b)) {
		return p.b[p.i]
	}
	return 0
}

func (p *parser) expect(c byte) {
	if p.bad {
		return
	}
	if p.peek() != c {
		p.fail()
		return
	}
	p.i = p.i + 1
}

// word reads a nonempty run of lowercase letters.
func (p *parser) word() string {
	start := p.i
	for p.i < uint64(len(p.b)) && p.b[p.i] >= 'a' && p.b[p.i] <= 'z' {
		p.i = p.i + 1
	}
	if p.i == start {
		p.fail()
		return ""
	}
	return string(p.b[start:p.i])
}

// open reads "(" and a word.
func (p *parser) open() string {
	p.expect('(')
	if p.bad {
		return ""
	}
	return p.word()
}

func (p *parser) num() uint64 {
	var n uint64 = 0
	var k uint64 = 0
	for p.i < uint64(len(p.b)) && p.b[p.i] >= '0' && p.b[p.i] <= '9' {
		n = n*10 + uint64(p.b[p.i]-'0')
		p.i = p.i + 1
		k = k + 1
	}
	if k == 0 || k > 18 {
		p.fail()
	}
	return n
}

func (p *parser) str() string {
	p.expect('"')
	if p.bad {
		return ""
	}
	start := p.i
	for p.i < uint64(len(p.b)) && p.b[p.i] != '"' {
		if p.b[p.i] == '\\' {
			p.fail()
			return ""
		}
		p.i = p.i + 1
	}
	s := string(p.b[start:p.i])
	p.expect('"')
	return s
}

// more reports whether another item follows in the current list (a space),
// and consumes the space.
func (p *parser) more() bool {
	if p.bad {
		return false
	}
	if p.peek() == ' ' {
		p.i = p.i + 1
		return true
	}
	return false
}

// items: "(" item (" " item)* ")" or "()"; first reports whether there is
// a first item, after which the caller uses more.
func (p *parser) listOpen() bool {
	p.expect('(')
	if p.bad {
		return false
	}
	return p.peek() != ')'
}

func (p *parser) sort() Sort {
	c := p.peek()
	if c == 'v' {
		p.i = p.i + 1
		return Sort{Kind: SortVal}
	}
	if c == 'y' {
		p.i = p.i + 1
		return Sort{Kind: SortType}
	}
	if p.open() != "u" {
		p.fail()
		return Sort{}
	}
	p.expect(' ')
	n := p.num()
	p.expect(')')
	return Sort{Kind: SortUser, Num: n}
}

func (p *parser) sorts() []Sort {
	var ss []Sort
	if p.listOpen() {
		ss = append(ss, p.sort())
		for p.more() {
			ss = append(ss, p.sort())
		}
	}
	p.expect(')')
	return ss
}

// termArgs reads " term"* up to the closing parenthesis, and consumes it.
func (p *parser) termArgs() []*Term {
	var ts []*Term
	for p.more() {
		ts = append(ts, p.term())
	}
	p.expect(')')
	return ts
}

func (p *parser) term() *Term {
	if p.bad {
		return nil
	}
	if p.peek() == 'u' {
		if p.word() != "unit" {
			p.fail()
			return nil
		}
		return &Term{Kind: TUnit}
	}
	w := p.open()
	if w == "var" {
		p.expect(' ')
		n := p.num()
		p.expect(')')
		return &Term{Kind: TVar, Num: n}
	}
	if w == "sym" {
		p.expect(' ')
		n := p.num()
		return &Term{Kind: TSym, Num: n, Args: p.termArgs()}
	}
	if w == "pair" {
		p.expect(' ')
		a := p.term()
		p.expect(' ')
		b := p.term()
		p.expect(')')
		return &Term{Kind: TPair, Args: []*Term{a, b}}
	}
	if w == "lit" {
		p.expect(' ')
		ty := p.term()
		args := []*Term{ty}
		args = append(args, p.termArgs()...)
		return &Term{Kind: TLit, Args: args}
	}
	p.fail()
	return nil
}

func (p *parser) terms() []*Term {
	var ts []*Term
	if p.listOpen() {
		ts = append(ts, p.term())
		for p.more() {
			ts = append(ts, p.term())
		}
	}
	p.expect(')')
	return ts
}

func (p *parser) pat() *Pat {
	if p.bad {
		return nil
	}
	w := p.open()
	if w == "pval" {
		p.expect(' ')
		t := p.term()
		p.expect(')')
		return &Pat{Kind: PVal, T: t}
	}
	if w == "papp" {
		p.expect(' ')
		a := p.pat()
		p.expect(' ')
		b := p.pat()
		p.expect(')')
		return &Pat{Kind: PApp, A: a, B: b}
	}
	p.fail()
	return nil
}

func (p *parser) atom() *Atom {
	if p.bad {
		return nil
	}
	w := p.open()
	if w == "pred" {
		p.expect(' ')
		n := p.num()
		return &Atom{Kind: APred, Num: n, Args: p.termArgs()}
	}
	if w == "eq" {
		p.expect(' ')
		a := p.term()
		p.expect(' ')
		b := p.term()
		p.expect(')')
		return &Atom{Kind: AEq, Args: []*Term{a, b}}
	}
	p.fail()
	return nil
}

func (p *parser) atoms() []*Atom {
	var as []*Atom
	if p.listOpen() {
		as = append(as, p.atom())
		for p.more() {
			as = append(as, p.atom())
		}
	}
	p.expect(')')
	return as
}

func (p *parser) expr2(k ExprKind) *Expr {
	p.expect(' ')
	a := p.expr()
	p.expect(' ')
	b := p.expr()
	p.expect(')')
	return &Expr{Kind: k, A: a, B: b}
}

func (p *parser) expr1(k ExprKind) *Expr {
	p.expect(' ')
	a := p.expr()
	p.expect(')')
	return &Expr{Kind: k, A: a}
}

func (p *parser) expr() *Expr {
	if p.bad {
		return nil
	}
	w := p.open()
	if w == "val" {
		p.expect(' ')
		t := p.term()
		p.expect(')')
		return &Expr{Kind: EVal, T: t}
	}
	if w == "cvar" {
		p.expect(' ')
		x := p.str()
		p.expect(')')
		return &Expr{Kind: EVar, Name: x}
	}
	if w == "app" {
		return p.expr2(EApp)
	}
	if w == "cpair" {
		return p.expr2(EPair)
	}
	if w == "let" {
		p.expect(' ')
		x := p.str()
		e := p.expr2(ELet)
		e.Name = x
		return e
	}
	if w == "seq" {
		return p.expr2(ESeq)
	}
	if w == "clit" {
		p.expect(' ')
		ty := p.term()
		var es []*Expr
		for p.more() {
			es = append(es, p.expr())
		}
		p.expect(')')
		return &Expr{Kind: ELit, T: ty, Elems: es}
	}
	if w == "do" {
		return p.expr1(EDo)
	}
	if w == "ret" {
		return p.expr1(ERet)
	}
	if w == "xseq" {
		return p.expr2(EXSeq)
	}
	if w == "xdo" {
		return p.expr1(EXDo)
	}
	p.fail()
	return nil
}

func (p *parser) word1(w string) {
	if p.open() != w {
		p.fail()
	}
}

func (p *parser) symDecl() SymDecl {
	p.word1("sym")
	p.expect(' ')
	args := p.sorts()
	p.expect(' ')
	res := p.sort()
	p.expect(')')
	return SymDecl{Args: args, Res: res}
}

func (p *parser) predDecl() PredDecl {
	p.word1("pred")
	p.expect(' ')
	n := p.num()
	if n > 1 {
		p.fail()
	}
	p.expect(' ')
	args := p.sorts()
	p.expect(')')
	return PredDecl{Pers: n == 1, Args: args}
}

func (p *parser) rule() *Rule {
	p.word1("rule")
	p.expect(' ')
	vars := p.sorts()
	p.expect(' ')
	lhs := p.pat()
	p.expect(' ')
	pre := p.atoms()
	p.expect(' ')
	ex := p.sorts()
	p.expect(' ')
	ret := p.term()
	p.expect(' ')
	post := p.atoms()
	p.expect(')')
	return &Rule{Vars: vars, Lhs: lhs, Pre: pre, Ex: ex, Ret: ret, Post: post}
}

func (p *parser) fact() *Fact {
	p.word1("fact")
	p.expect(' ')
	vars := p.sorts()
	p.expect(' ')
	lhs := p.term()
	p.expect(' ')
	rhs := p.term()
	p.expect(')')
	return &Fact{Vars: vars, Lhs: lhs, Rhs: rhs}
}

func (p *parser) fn() *Func {
	p.word1("func")
	p.expect(' ')
	var xs []string
	if p.listOpen() {
		xs = append(xs, p.str())
		for p.more() {
			xs = append(xs, p.str())
		}
	}
	p.expect(')')
	p.expect(' ')
	body := p.expr()
	p.expect(')')
	return &Func{Params: xs, Body: body}
}

func (p *parser) spec() *Spec {
	p.word1("spec")
	p.expect(' ')
	vars := p.sorts()
	p.expect(' ')
	args := p.terms()
	p.expect(' ')
	pre := p.atoms()
	p.expect(' ')
	ex := p.sorts()
	p.expect(' ')
	ret := p.term()
	p.expect(' ')
	post := p.atoms()
	p.expect(')')
	return &Spec{Vars: vars, Args: args, Pre: pre, Ex: ex, Ret: ret, Post: post}
}

// Parse reads a serialized input. It returns nil unless the whole of b is
// one well-formed input.
func Parse(b []byte) *Input {
	p := &parser{b: b}
	p.word1("input")
	p.expect(' ')
	inp := &Input{}
	p.word1("syms")
	for p.more() {
		inp.Syms = append(inp.Syms, p.symDecl())
	}
	p.expect(')')
	p.expect(' ')
	p.word1("preds")
	for p.more() {
		inp.Preds = append(inp.Preds, p.predDecl())
	}
	p.expect(')')
	p.expect(' ')
	p.word1("rules")
	for p.more() {
		inp.Rules = append(inp.Rules, p.rule())
	}
	p.expect(')')
	p.expect(' ')
	p.word1("facts")
	for p.more() {
		inp.Facts = append(inp.Facts, p.fact())
	}
	p.expect(')')
	p.expect(' ')
	inp.Fn = p.fn()
	p.expect(' ')
	inp.Sp = p.spec()
	p.expect(')')
	if p.bad || p.i != uint64(len(b)) {
		return nil
	}
	return inp
}
