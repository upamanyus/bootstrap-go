package rocqgoal

import (
	"strconv"
	"strings"
)

// String prints t in the export format: Parse and String are inverse, byte
// for byte, on what the exporter prints.
func (t *Term) String() string {
	var b strings.Builder
	t.write(&b)
	return b.String()
}

// String prints g in the export format.
func (g *Goal) String() string {
	var b strings.Builder
	b.WriteString("(Goal")
	for _, h := range g.Hyps {
		if h.Body != nil {
			b.WriteString(" (Def " + h.Name + " ")
			h.Body.write(&b)
		} else {
			b.WriteString(" (Hyp " + h.Name)
		}
		b.WriteString(" ")
		h.Type.write(&b)
		b.WriteString(")")
	}
	b.WriteString(" (Concl ")
	g.Concl.write(&b)
	b.WriteString("))")
	return b.String()
}

func writeBinder(b *strings.Builder, x Binder) {
	name := x.Name
	if name == "" {
		name = "_"
	}
	b.WriteString("(" + name + " ")
	x.Type.write(b)
	b.WriteString(")")
}

func (t *Term) write(b *strings.Builder) {
	args := func(ts []*Term) {
		for _, a := range ts {
			b.WriteString(" ")
			a.write(b)
		}
	}
	switch t.Kind {
	case Rel:
		b.WriteString("(R " + strconv.FormatInt(t.Num, 10) + ")")
	case Var:
		b.WriteString("(V " + t.Name + ")")
	case Sort:
		b.WriteString(t.Name)
	case Prod, Lambda:
		tag := "(Pi "
		if t.Kind == Lambda {
			tag = "(Lam "
		}
		b.WriteString(tag)
		writeBinder(b, t.Binders[0])
		args(t.Args)
		b.WriteString(")")
	case LetIn:
		b.WriteString("(Let ")
		writeBinder(b, t.Binders[0])
		args(t.Args)
		b.WriteString(")")
	case App:
		b.WriteString("(A")
		args(t.Args)
		b.WriteString(")")
	case Const:
		b.WriteString("(C " + t.Name + ")")
	case Ind:
		b.WriteString("(I " + t.Name + ")")
	case Construct:
		b.WriteString("(K " + t.Name + ")")
	case Case:
		b.WriteString("(M " + t.Name)
		args(t.Args)
		b.WriteString(")")
	case Fix, CoFix:
		tag := "(Fix "
		if t.Kind == CoFix {
			tag = "(CoFix "
		}
		b.WriteString(tag + strconv.FormatInt(t.Num, 10))
		for _, x := range t.Binders {
			b.WriteString(" ")
			writeBinder(b, x)
		}
		args(t.Args)
		b.WriteString(")")
	case Proj:
		b.WriteString("(Proj " + t.Name)
		args(t.Args)
		b.WriteString(")")
	case Uint63:
		b.WriteString("(U " + strconv.FormatInt(t.Num, 10) + ")")
	case Float:
		b.WriteString("Float")
	case String:
		b.WriteString("(Str " + quote(t.Name) + ")")
	case Array:
		b.WriteString("(Arr")
		args(t.Args)
		b.WriteString(")")
	case Evar:
		b.WriteString("?")
	}
}

// quote escapes s as the exporter does: a double quote, a backslash and a
// byte outside 32-126 are escaped, the rest is verbatim.
func quote(s string) string {
	const hex = "0123456789abcdef"
	var b strings.Builder
	b.WriteByte('"')
	for i := 0; i < len(s); i++ {
		c := s[i]
		switch {
		case c == '"':
			b.WriteString(`\"`)
		case c == '\\':
			b.WriteString(`\\`)
		case c < 32 || c > 126:
			b.WriteString(`\x`)
			b.WriteByte(hex[c>>4])
			b.WriteByte(hex[c&15])
		default:
			b.WriteByte(c)
		}
	}
	b.WriteByte('"')
	return b.String()
}

// Short prints t for a person: names without their module path, variables
// bare, applications as (f x y) and binders as ∀/λ, cut off after max bytes
// (no limit if max <= 0). Bound variables print as their de Bruijn index.
func Short(t *Term, max int) string {
	var b strings.Builder
	t.short(&b)
	s := b.String()
	if max > 0 && len(s) > max {
		s = s[:max] + "…"
	}
	return s
}

func baseName(name string) string {
	if i := strings.LastIndexByte(name, '.'); i >= 0 {
		return name[i+1:]
	}
	return name
}

func (t *Term) short(b *strings.Builder) {
	switch t.Kind {
	case Rel:
		b.WriteString("#" + strconv.FormatInt(t.Num, 10))
	case Var, Sort:
		b.WriteString(t.Name)
	case Const, Ind, Construct:
		b.WriteString(baseName(t.Name))
	case Prod, Lambda:
		if t.Kind == Prod {
			b.WriteString("∀ ")
		} else {
			b.WriteString("λ ")
		}
		name := t.Binders[0].Name
		if name == "" {
			name = "_"
		}
		b.WriteString(name + ", ")
		t.Args[0].short(b)
	case App:
		b.WriteString("(")
		for i, a := range t.Args {
			if i > 0 {
				b.WriteString(" ")
			}
			a.short(b)
		}
		b.WriteString(")")
	case Uint63:
		b.WriteString(strconv.FormatInt(t.Num, 10))
	case String:
		b.WriteString(strconv.Quote(t.Name))
	case Proj:
		t.Args[0].short(b)
		b.WriteString(".(" + baseName(t.Name) + ")")
	default:
		b.WriteString("<" + t.Kind.String() + ">")
	}
}
