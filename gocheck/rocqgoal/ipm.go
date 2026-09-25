package rocqgoal

import "fmt"

// Kernel names recognized here. Arguments are taken from the end of an
// application, so implicit arguments in front (the PROP, Σ, ...) can change
// without breaking the recognizers.
const (
	NameEnvsEntails   = "iris.proofmode.environments.envs_entails"
	NameEnvs          = "iris.proofmode.environments.Envs"
	NameEnil          = "iris.proofmode.environments.Enil"
	NameEsnoc         = "iris.proofmode.environments.Esnoc"
	NameINamed        = "iris.proofmode.base.ident.INamed"
	NameIAnon         = "iris.proofmode.base.ident.IAnon"
	NameWP            = "iris.bi.weakestpre.wp"
	NameTypedPointsto = "New.golang.theory.postlifting.typed_pointsto"

	nameString      = "Stdlib.Strings.String.String"
	nameEmptyString = "Stdlib.Strings.String.EmptyString"
	nameAscii       = "Stdlib.Strings.Ascii.Ascii"
	nameTrue        = "Corelib.Init.Datatypes.true"
	nameFalse       = "Corelib.Init.Datatypes.false"
	nameXH          = "Corelib.Numbers.BinNums.xH"
	nameXO          = "Corelib.Numbers.BinNums.xO"
	nameXI          = "Corelib.Numbers.BinNums.xI"
)

// IHyp is a hypothesis of an Iris proof mode context.
type IHyp struct {
	Name string // "" for an anonymous hypothesis
	Anon int64  // the number of an anonymous hypothesis
	Prop *Term
}

// Label is how the proof mode would print the hypothesis's name.
func (h IHyp) Label() string {
	if h.Name != "" {
		return h.Name
	}
	return fmt.Sprintf("_%d", h.Anon)
}

// IPM is an Iris proof mode goal, envs_entails (Envs Γp Γs _) Goal: the
// persistent and the spatial context, oldest hypothesis first, and what is
// left to prove.
type IPM struct {
	Persistent []IHyp
	Spatial    []IHyp
	Goal       *Term
}

// IPM recognizes g's conclusion as an Iris proof mode goal.
func (g *Goal) IPM() (*IPM, error) {
	head, args := Head(g.Concl)
	if head != NameEnvsEntails || len(args) < 2 {
		return nil, fmt.Errorf("rocqgoal: the conclusion is not an Iris proof mode goal (head %q)", head)
	}
	delta, goal := args[len(args)-2], args[len(args)-1]
	head, dargs := Head(delta)
	if head != NameEnvs || len(dargs) < 3 {
		return nil, fmt.Errorf("rocqgoal: expected Envs, got head %q", head)
	}
	pers, err := env(dargs[len(dargs)-3])
	if err != nil {
		return nil, err
	}
	spat, err := env(dargs[len(dargs)-2])
	if err != nil {
		return nil, err
	}
	return &IPM{Persistent: pers, Spatial: spat, Goal: goal}, nil
}

// env reads a proof mode context, a snoc list of (ident, prop) pairs.
func env(t *Term) ([]IHyp, error) {
	var out []IHyp
	var rec func(t *Term) error
	rec = func(t *Term) error {
		head, args := Head(t)
		switch {
		case head == NameEnil:
			return nil
		case head == NameEsnoc && len(args) >= 3:
			if err := rec(args[len(args)-3]); err != nil {
				return err
			}
			h := IHyp{Prop: args[len(args)-1]}
			ihead, iargs := Head(args[len(args)-2])
			switch {
			case ihead == NameINamed && len(iargs) == 1:
				s, ok := AsString(iargs[0])
				if !ok {
					return fmt.Errorf("rocqgoal: a hypothesis name is not a string literal")
				}
				h.Name = s
			case ihead == NameIAnon && len(iargs) == 1:
				n, ok := AsPositive(iargs[0])
				if !ok {
					return fmt.Errorf("rocqgoal: an anonymous hypothesis number is not a literal")
				}
				h.Anon = n
			default:
				return fmt.Errorf("rocqgoal: unexpected hypothesis identifier (head %q)", ihead)
			}
			out = append(out, h)
			return nil
		}
		return fmt.Errorf("rocqgoal: expected Enil or Esnoc, got head %q", head)
	}
	if err := rec(t); err != nil {
		return nil, err
	}
	return out, nil
}

// AsString decodes a closed Stdlib string (String and Ascii constructors
// all the way down).
func AsString(t *Term) (string, bool) {
	var b []byte
	for {
		head, args := Head(t)
		switch {
		case head == nameEmptyString && len(args) == 0:
			return string(b), true
		case head == nameString && len(args) == 2:
			ahead, bits := Head(args[0])
			if ahead != nameAscii || len(bits) != 8 {
				return "", false
			}
			var c byte
			for k := 7; k >= 0; k-- { // Ascii takes the least significant bit first
				bh, _ := Head(bits[k])
				switch bh {
				case nameTrue:
					c = c<<1 | 1
				case nameFalse:
					c <<= 1
				default:
					return "", false
				}
			}
			b = append(b, c)
			t = args[1]
		default:
			return "", false
		}
	}
}

// AsPositive decodes a closed binary positive (xI, xO, xH).
func AsPositive(t *Term) (int64, bool) {
	head, args := Head(t)
	switch {
	case head == nameXH && len(args) == 0:
		return 1, true
	case (head == nameXO || head == nameXI) && len(args) == 1:
		n, ok := AsPositive(args[0])
		if !ok || n > 1<<61 {
			return 0, false
		}
		if head == nameXI {
			return 2*n + 1, true
		}
		return 2 * n, true
	}
	return 0, false
}

// PointsTo is a typed points-to fact, l ↦{dq} v at Go type V (a Rocq type:
// w64, loc, a struct's record type, ...).
type PointsTo struct {
	Loc, Val, Dfrac, Type *Term
}

// AsPointsTo recognizes typed_pointsto l v dq.
func AsPointsTo(t *Term) (PointsTo, bool) {
	head, args := Head(t)
	if head != NameTypedPointsto || len(args) < 5 {
		return PointsTo{}, false
	}
	n := len(args)
	return PointsTo{Loc: args[n-3], Val: args[n-2], Dfrac: args[n-1], Type: args[n-5]}, true
}

// WP is a weakest precondition, WP e @ s; E {{ Post }}.
type WP struct {
	Stuck, Mask, Expr, Post *Term
}

// AsWP recognizes wp s E e Φ.
func AsWP(t *Term) (WP, bool) {
	head, args := Head(t)
	if head != NameWP || len(args) < 4 {
		return WP{}, false
	}
	n := len(args)
	return WP{Stuck: args[n-4], Mask: args[n-3], Expr: args[n-2], Post: args[n-1]}, true
}
