package rocqgoal

import (
	"fmt"
	"strconv"
)

// The format is the one documented in new/proof/rocqgoal/export.v. Parsing
// is in two steps: a generic S-expression reader, then a conversion that
// knows the layout of each node. The second step is where a binder and a
// term are told apart, which the first cannot do: a binder named A looks
// like an application.

// sexp is a node of a generic S-expression.
type sexp struct {
	off    int     // byte offset in the input, for errors
	atom   string  // an atom, or the unescaped contents of a string literal
	quoted bool    // atom came from a string literal
	list   []*sexp // a list, when atom == "" and !quoted
	isList bool
}

type reader struct {
	src string
	i   int
}

func (r *reader) errf(off int, format string, args ...any) error {
	return fmt.Errorf("rocqgoal: offset %d: %s", off, fmt.Sprintf(format, args...))
}

func (r *reader) skipSpace() {
	for r.i < len(r.src) && (r.src[r.i] == ' ' || r.src[r.i] == '\n' || r.src[r.i] == '\t' || r.src[r.i] == '\r') {
		r.i++
	}
}

func (r *reader) read() (*sexp, error) {
	r.skipSpace()
	if r.i >= len(r.src) {
		return nil, r.errf(r.i, "unexpected end of input")
	}
	start := r.i
	switch r.src[r.i] {
	case '(':
		r.i++
		n := &sexp{off: start, isList: true}
		for {
			r.skipSpace()
			if r.i >= len(r.src) {
				return nil, r.errf(start, "unclosed parenthesis")
			}
			if r.src[r.i] == ')' {
				r.i++
				return n, nil
			}
			k, err := r.read()
			if err != nil {
				return nil, err
			}
			n.list = append(n.list, k)
		}
	case ')':
		return nil, r.errf(start, "unexpected )")
	case '"':
		r.i++
		for r.i < len(r.src) && r.src[r.i] != '"' {
			if r.src[r.i] == '\\' {
				r.i++
			}
			r.i++
		}
		if r.i >= len(r.src) {
			return nil, r.errf(start, "unterminated string")
		}
		r.i++
		s, err := strconv.Unquote(r.src[start:r.i])
		if err != nil {
			return nil, r.errf(start, "bad string literal: %v", err)
		}
		return &sexp{off: start, atom: s, quoted: true}, nil
	}
	for r.i < len(r.src) {
		c := r.src[r.i]
		if c == ' ' || c == '\n' || c == '\t' || c == '\r' || c == '(' || c == ')' || c == '"' {
			break
		}
		r.i++
	}
	return &sexp{off: start, atom: r.src[start:r.i]}, nil
}

func readAll(src string) (*sexp, error) {
	r := &reader{src: src}
	n, err := r.read()
	if err != nil {
		return nil, err
	}
	r.skipSpace()
	if r.i != len(src) {
		return nil, r.errf(r.i, "trailing input")
	}
	return n, nil
}

// Parse reads an exported goal: (Goal hyp* (Concl t)).
func Parse(src string) (*Goal, error) {
	n, err := readAll(src)
	if err != nil {
		return nil, err
	}
	if !n.isList || len(n.list) < 2 || n.list[0].atom != "Goal" {
		return nil, errAt(n, "expected (Goal ...)")
	}
	g := &Goal{}
	for i, h := range n.list[1:] {
		tag := ""
		if h.isList && len(h.list) > 0 {
			tag = h.list[0].atom
		}
		last := i == len(n.list)-2
		switch {
		case tag == "Hyp" && len(h.list) == 3 && !last:
			ty, err := term(h.list[2])
			if err != nil {
				return nil, err
			}
			g.Hyps = append(g.Hyps, Hyp{Name: h.list[1].atom, Type: ty})
		case tag == "Def" && len(h.list) == 4 && !last:
			body, err := term(h.list[2])
			if err != nil {
				return nil, err
			}
			ty, err := term(h.list[3])
			if err != nil {
				return nil, err
			}
			g.Hyps = append(g.Hyps, Hyp{Name: h.list[1].atom, Body: body, Type: ty})
		case tag == "Concl" && len(h.list) == 2 && last:
			g.Concl, err = term(h.list[1])
			if err != nil {
				return nil, err
			}
		default:
			return nil, errAt(h, "expected (Hyp id t) or (Def id t t), and (Concl t) last")
		}
	}
	return g, nil
}

// ParseTerm reads one exported term.
func ParseTerm(src string) (*Term, error) {
	n, err := readAll(src)
	if err != nil {
		return nil, err
	}
	return term(n)
}

func errAt(n *sexp, format string, args ...any) error {
	return fmt.Errorf("rocqgoal: offset %d: %s", n.off, fmt.Sprintf(format, args...))
}

var sorts = map[string]bool{"Prop": true, "SProp": true, "Set": true, "Type": true}

func term(n *sexp) (*Term, error) {
	if !n.isList {
		switch {
		case n.quoted:
			return nil, errAt(n, "unexpected string literal")
		case sorts[n.atom]:
			return &Term{Kind: Sort, Name: n.atom}, nil
		case n.atom == "Float":
			return &Term{Kind: Float}, nil
		case n.atom == "?":
			return &Term{Kind: Evar}, nil
		}
		return nil, errAt(n, "unexpected atom %q", n.atom)
	}
	if len(n.list) == 0 || n.list[0].isList || n.list[0].quoted {
		return nil, errAt(n, "expected a tag")
	}
	tag, xs := n.list[0].atom, n.list[1:]
	arity := func(ok bool) error {
		if !ok {
			return errAt(n, "wrong number of fields in (%s ...)", tag)
		}
		return nil
	}
	switch tag {
	case "R", "U":
		if err := arity(len(xs) == 1); err != nil {
			return nil, err
		}
		v, err := num(xs[0])
		if err != nil {
			return nil, err
		}
		if tag == "R" {
			return &Term{Kind: Rel, Num: v}, nil
		}
		return &Term{Kind: Uint63, Num: v}, nil
	case "V", "C", "I", "K":
		if err := arity(len(xs) == 1); err != nil {
			return nil, err
		}
		name, err := ident(xs[0])
		if err != nil {
			return nil, err
		}
		k := map[string]Kind{"V": Var, "C": Const, "I": Ind, "K": Construct}[tag]
		return &Term{Kind: k, Name: name}, nil
	case "Str":
		if err := arity(len(xs) == 1 && xs[0].quoted); err != nil {
			return nil, err
		}
		return &Term{Kind: String, Name: xs[0].atom}, nil
	case "Pi", "Lam":
		if err := arity(len(xs) == 2); err != nil {
			return nil, err
		}
		b, err := binder(xs[0])
		if err != nil {
			return nil, err
		}
		body, err := term(xs[1])
		if err != nil {
			return nil, err
		}
		k := Prod
		if tag == "Lam" {
			k = Lambda
		}
		return &Term{Kind: k, Binders: []Binder{b}, Args: []*Term{body}}, nil
	case "Let":
		if err := arity(len(xs) == 3); err != nil {
			return nil, err
		}
		b, err := binder(xs[0])
		if err != nil {
			return nil, err
		}
		args, err := terms(xs[1:])
		if err != nil {
			return nil, err
		}
		return &Term{Kind: LetIn, Binders: []Binder{b}, Args: args}, nil
	case "A", "Arr":
		// A: the function and at least one argument; Arr: the type and the
		// default element, then any number of elements
		if err := arity(len(xs) >= 2); err != nil {
			return nil, err
		}
		args, err := terms(xs)
		if err != nil {
			return nil, err
		}
		if tag == "A" {
			return &Term{Kind: App, Args: args}, nil
		}
		return &Term{Kind: Array, Args: args}, nil
	case "M":
		if err := arity(len(xs) >= 3); err != nil {
			return nil, err
		}
		name, err := ident(xs[0])
		if err != nil {
			return nil, err
		}
		args, err := terms(xs[1:])
		if err != nil {
			return nil, err
		}
		return &Term{Kind: Case, Name: name, Args: args}, nil
	case "Fix", "CoFix":
		// n, then m binders, then m bodies
		if err := arity(len(xs) >= 3 && len(xs)%2 == 1); err != nil {
			return nil, err
		}
		v, err := num(xs[0])
		if err != nil {
			return nil, err
		}
		m := (len(xs) - 1) / 2
		t := &Term{Kind: Fix, Num: v}
		if tag == "CoFix" {
			t.Kind = CoFix
		}
		for _, x := range xs[1 : 1+m] {
			b, err := binder(x)
			if err != nil {
				return nil, err
			}
			t.Binders = append(t.Binders, b)
		}
		if t.Args, err = terms(xs[1+m:]); err != nil {
			return nil, err
		}
		return t, nil
	case "Proj":
		if err := arity(len(xs) == 2); err != nil {
			return nil, err
		}
		name, err := ident(xs[0])
		if err != nil {
			return nil, err
		}
		arg, err := term(xs[1])
		if err != nil {
			return nil, err
		}
		return &Term{Kind: Proj, Name: name, Args: []*Term{arg}}, nil
	}
	return nil, errAt(n, "unknown tag %q", tag)
}

func terms(xs []*sexp) ([]*Term, error) {
	out := make([]*Term, len(xs))
	for i, x := range xs {
		t, err := term(x)
		if err != nil {
			return nil, err
		}
		out[i] = t
	}
	return out, nil
}

func binder(n *sexp) (Binder, error) {
	if !n.isList || len(n.list) != 2 {
		return Binder{}, errAt(n, "expected a binder (id t)")
	}
	name, err := ident(n.list[0])
	if err != nil {
		return Binder{}, err
	}
	if name == "_" {
		name = ""
	}
	ty, err := term(n.list[1])
	if err != nil {
		return Binder{}, err
	}
	return Binder{Name: name, Type: ty}, nil
}

func ident(n *sexp) (string, error) {
	if n.isList || n.quoted || n.atom == "" {
		return "", errAt(n, "expected a name")
	}
	return n.atom, nil
}

func num(n *sexp) (int64, error) {
	if n.isList || n.quoted {
		return 0, errAt(n, "expected a number")
	}
	v, err := strconv.ParseInt(n.atom, 10, 64)
	if err != nil {
		return 0, errAt(n, "bad number %q", n.atom)
	}
	return v, nil
}
