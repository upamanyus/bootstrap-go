package spec

import "fmt"

// AssnKind identifies the form of a surface assertion.
type AssnKind int

const (
	AEmp AssnKind = iota + 1
	ASep
	AOr
	AExists
	APure
	APointsTo
)

// Binder is one ∃-bound name, with an optional sort annotation.
type Binder struct {
	Name string
	Sort string // "", "int", "bool", "ptr", "loc" or "unit"
	Pos  int
}

// Assn is a surface assertion.
type Assn struct {
	Kind    AssnKind
	L, R    *Assn    // ASep, AOr
	Body    *Assn    // AExists
	Binders []Binder // AExists
	X, Y    *Term    // APure: X; APointsTo: X ↦ Y
	Pos     int
}

// TermKind identifies the form of a surface term.
type TermKind int

const (
	TNum TermKind = iota + 1
	TBoolLit
	TUnitLit
	TNullLit
	TRet
	TName
	TIf
	TAdd
	TSub
	TMul
	TNeg
	TNot
	TAnd
	TOr
	TEq
	TNe
	TLt
	TLe
	TGt
	TGe
)

// Sign records an explicit signedness annotation on a comparison.
type Sign int

const (
	SignAuto Sign = iota
	SignSigned
	SignUnsigned
)

// Term is a surface term.
type Term struct {
	Kind    TermKind
	Name    string // TName
	Num     uint64 // TNum
	Bool    bool   // TBoolLit
	Sign    Sign   // TLt, TLe, TGt, TGe
	A, B, C *Term
	Pos     int
}

// Surface is a parsed assertion together with its source text.
type Surface struct {
	Src string
	A   *Assn
}

var sortNames = map[string]bool{
	"int": true, "bool": true, "ptr": true, "loc": true, "unit": true,
}

var relOps = map[string]struct {
	kind TermKind
	sign Sign
}{
	"==":  {TEq, SignAuto},
	"!=":  {TNe, SignAuto},
	"<":   {TLt, SignAuto},
	"<=":  {TLe, SignAuto},
	">":   {TGt, SignAuto},
	">=":  {TGe, SignAuto},
	"<u":  {TLt, SignUnsigned},
	"<s":  {TLt, SignSigned},
	"<=u": {TLe, SignUnsigned},
	"<=s": {TLe, SignSigned},
	">u":  {TGt, SignUnsigned},
	">s":  {TGt, SignSigned},
	">=u": {TGe, SignUnsigned},
	">=s": {TGe, SignSigned},
}

// Parse parses an assertion.
func Parse(src string) (*Surface, error) {
	toks, err := lex(src)
	if err != nil {
		return nil, err
	}
	p := &parser{toks: toks}
	a, err := p.assn()
	if err != nil {
		return nil, err
	}
	if p.cur().kind != tEOF {
		return nil, p.errf(p.cur(), "unexpected %s after the assertion", p.cur())
	}
	return &Surface{Src: src, A: a}, nil
}

type parser struct {
	toks []token
	i    int
}

func (p *parser) cur() token  { return p.toks[p.i] }
func (p *parser) next() token { t := p.toks[p.i]; p.i++; return t }

func (p *parser) atSym(s string) bool {
	t := p.cur()
	return t.kind == tSym && t.text == s
}

func (p *parser) atIdent(s string) bool {
	t := p.cur()
	return t.kind == tIdent && t.text == s
}

func (p *parser) eatSym(s string) bool {
	if p.atSym(s) {
		p.i++
		return true
	}
	return false
}

func (p *parser) eatIdent(s string) bool {
	if p.atIdent(s) {
		p.i++
		return true
	}
	return false
}

func (p *parser) expectSym(s string) error {
	if p.eatSym(s) {
		return nil
	}
	return p.errf(p.cur(), "expected %q, found %s", s, p.cur())
}

func (p *parser) errf(t token, format string, args ...any) error {
	return fmt.Errorf("at offset %d: %s", t.pos, fmt.Sprintf(format, args...))
}

// assn = sepList { "∨" sepList }
func (p *parser) assn() (*Assn, error) {
	l, err := p.sepList()
	if err != nil {
		return nil, err
	}
	if t := p.cur(); t.kind == tSym && t.text == "∨" {
		p.i++
		r, err := p.assn()
		if err != nil {
			return nil, err
		}
		return &Assn{Kind: AOr, L: l, R: r, Pos: t.pos}, nil
	}
	return l, nil
}

// sepList = unit { "∗" unit }
func (p *parser) sepList() (*Assn, error) {
	l, err := p.unit()
	if err != nil {
		return nil, err
	}
	if t := p.cur(); t.kind == tSym && t.text == "∗" {
		p.i++
		r, err := p.sepList()
		if err != nil {
			return nil, err
		}
		return &Assn{Kind: ASep, L: l, R: r, Pos: t.pos}, nil
	}
	return l, nil
}

func (p *parser) unit() (*Assn, error) {
	t := p.cur()
	switch {
	case p.atIdent("emp"):
		p.i++
		return &Assn{Kind: AEmp, Pos: t.pos}, nil
	case p.atSym("⌜"):
		p.i++
		x, err := p.term()
		if err != nil {
			return nil, err
		}
		if err := p.expectSym("⌝"); err != nil {
			return nil, err
		}
		return &Assn{Kind: APure, X: x, Pos: t.pos}, nil
	case p.atSym("∃"):
		p.i++
		return p.exists(t.pos)
	case p.atSym("("):
		// Either a parenthesized assertion or a parenthesized term on the
		// left of ↦; try the assertion first and backtrack if what follows
		// turns out to be a points-to.
		save := p.i
		p.i++
		a, err := p.assn()
		if err == nil && p.eatSym(")") && !p.atSym("↦") {
			return a, nil
		}
		p.i = save
	}
	return p.pointsTo()
}

// exists parses the binders and body of an ∃ (which extends maximally right).
func (p *parser) exists(pos int) (*Assn, error) {
	var binders []Binder
	for {
		t := p.cur()
		if t.kind == tIdent {
			p.i++
			binders = append(binders, Binder{Name: t.text, Pos: t.pos})
			continue
		}
		if p.atSym("(") {
			save := p.i
			p.i++
			name := p.cur()
			if name.kind != tIdent {
				p.i = save
				break
			}
			p.i++
			if !p.eatSym(":") {
				p.i = save
				break
			}
			s := p.cur()
			if s.kind != tIdent || !sortNames[s.text] {
				return nil, p.errf(s, "expected a sort (int, bool, ptr, loc, unit), found %s", s)
			}
			p.i++
			if err := p.expectSym(")"); err != nil {
				return nil, err
			}
			binders = append(binders, Binder{Name: name.text, Sort: s.text, Pos: name.pos})
			continue
		}
		break
	}
	if len(binders) == 0 {
		return nil, p.errf(p.cur(), "expected a binder after ∃, found %s", p.cur())
	}
	if err := p.expectSym(","); err != nil {
		return nil, err
	}
	body, err := p.assn()
	if err != nil {
		return nil, err
	}
	return &Assn{Kind: AExists, Binders: binders, Body: body, Pos: pos}, nil
}

// pointsTo = term "↦" term
func (p *parser) pointsTo() (*Assn, error) {
	start := p.cur()
	l, err := p.term()
	if err != nil {
		return nil, err
	}
	t := p.cur()
	if !p.eatSym("↦") {
		return nil, p.errf(start, "expected an assertion; a bare term needs ↦ "+
			"(or ⌜...⌝ for a pure fact), found %s", t)
	}
	r, err := p.term()
	if err != nil {
		return nil, err
	}
	return &Assn{Kind: APointsTo, X: l, Y: r, Pos: t.pos}, nil
}

// term = orT
func (p *parser) term() (*Term, error) { return p.orT() }

func (p *parser) orT() (*Term, error) {
	l, err := p.andT()
	if err != nil {
		return nil, err
	}
	for {
		t := p.cur()
		if !p.eatSym("||") {
			return l, nil
		}
		r, err := p.andT()
		if err != nil {
			return nil, err
		}
		l = &Term{Kind: TOr, A: l, B: r, Pos: t.pos}
	}
}

func (p *parser) andT() (*Term, error) {
	l, err := p.cmpT()
	if err != nil {
		return nil, err
	}
	for {
		t := p.cur()
		if !p.eatSym("&&") {
			return l, nil
		}
		r, err := p.cmpT()
		if err != nil {
			return nil, err
		}
		l = &Term{Kind: TAnd, A: l, B: r, Pos: t.pos}
	}
}

func (p *parser) cmpT() (*Term, error) {
	l, err := p.sumT()
	if err != nil {
		return nil, err
	}
	t := p.cur()
	if t.kind != tSym {
		return l, nil
	}
	rel, ok := relOps[t.text]
	if !ok {
		return l, nil
	}
	p.i++
	r, err := p.sumT()
	if err != nil {
		return nil, err
	}
	return &Term{Kind: rel.kind, Sign: rel.sign, A: l, B: r, Pos: t.pos}, nil
}

func (p *parser) sumT() (*Term, error) {
	l, err := p.mulT()
	if err != nil {
		return nil, err
	}
	for {
		t := p.cur()
		var kind TermKind
		switch {
		case p.atSym("+"):
			kind = TAdd
		case p.atSym("-"):
			kind = TSub
		default:
			return l, nil
		}
		p.i++
		r, err := p.mulT()
		if err != nil {
			return nil, err
		}
		l = &Term{Kind: kind, A: l, B: r, Pos: t.pos}
	}
}

// mulT parses a product. The ∗ token is overloaded: it is multiplication
// inside a term but separating conjunction between assertions, so a ∗ is only
// taken as multiplication when an operand follows it and that operand is not
// itself the location of a points-to. This is what makes
// `p ↦ a ∗ q ↦ b` a separating conjunction while `p ↦ a ∗ b` stores a
// product.
func (p *parser) mulT() (*Term, error) {
	l, err := p.unT()
	if err != nil {
		return nil, err
	}
	for {
		t := p.cur()
		save := p.i
		if !p.eatSym("∗") {
			return l, nil
		}
		r, err := p.unT()
		if err != nil || p.atSym("↦") {
			p.i = save
			return l, nil
		}
		l = &Term{Kind: TMul, A: l, B: r, Pos: t.pos}
	}
}

func (p *parser) unT() (*Term, error) {
	t := p.cur()
	if p.eatSym("-") {
		a, err := p.unT()
		if err != nil {
			return nil, err
		}
		return &Term{Kind: TNeg, A: a, Pos: t.pos}, nil
	}
	if p.eatSym("!") {
		a, err := p.unT()
		if err != nil {
			return nil, err
		}
		return &Term{Kind: TNot, A: a, Pos: t.pos}, nil
	}
	return p.atomT()
}

func (p *parser) atomT() (*Term, error) {
	t := p.cur()
	switch t.kind {
	case tNum:
		p.i++
		return &Term{Kind: TNum, Num: t.num, Pos: t.pos}, nil
	case tIdent:
		switch t.text {
		case "true":
			p.i++
			return &Term{Kind: TBoolLit, Bool: true, Pos: t.pos}, nil
		case "false":
			p.i++
			return &Term{Kind: TBoolLit, Bool: false, Pos: t.pos}, nil
		case "null", "nil":
			p.i++
			return &Term{Kind: TNullLit, Pos: t.pos}, nil
		case "ret":
			p.i++
			return &Term{Kind: TRet, Pos: t.pos}, nil
		case "if":
			p.i++
			return p.ifT(t.pos)
		case "emp":
			return nil, p.errf(t, "emp is an assertion, not a term")
		}
		p.i++
		return &Term{Kind: TName, Name: t.text, Pos: t.pos}, nil
	case tSym:
		if t.text == "(" {
			p.i++
			if p.eatSym(")") {
				return &Term{Kind: TUnitLit, Pos: t.pos}, nil
			}
			a, err := p.term()
			if err != nil {
				return nil, err
			}
			if err := p.expectSym(")"); err != nil {
				return nil, err
			}
			return a, nil
		}
	}
	return nil, p.errf(t, "expected a term, found %s", t)
}

func (p *parser) ifT(pos int) (*Term, error) {
	cond, err := p.term()
	if err != nil {
		return nil, err
	}
	if !p.eatIdent("then") {
		return nil, p.errf(p.cur(), "expected `then`, found %s", p.cur())
	}
	then, err := p.term()
	if err != nil {
		return nil, err
	}
	if !p.eatIdent("else") {
		return nil, p.errf(p.cur(), "expected `else`, found %s", p.cur())
	}
	els, err := p.term()
	if err != nil {
		return nil, err
	}
	return &Term{Kind: TIf, A: cond, B: then, C: els, Pos: pos}, nil
}
