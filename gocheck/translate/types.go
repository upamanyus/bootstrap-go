package translate

import (
	"fmt"

	"github.com/upamanyus/bootstrap-go/checker"
	"github.com/mit-pdos/perennial/goose/glang"
)

// Type converts a GooseLang type expression into a checker.Type.
func Type(e glang.Expr) (*checker.Type, error) {
	e = unwrap(e)
	switch n := e.(type) {
	case glang.GallinaIdent:
		return namedType(string(n), e)
	case glang.VerbatimExpr:
		return namedType(string(n), e)
	case glang.CallExpr:
		name, ok := identName(n.MethodName)
		if !ok {
			return nil, unsupported(e, "type constructor")
		}
		if name == "go.PointerType" {
			if len(n.Args) != 1 {
				return nil, unsupported(e, "go.PointerType with %d arguments", len(n.Args))
			}
			elem, err := Type(n.Args[0])
			if err != nil {
				return nil, err
			}
			return &checker.Type{Kind: checker.TyPtr, Elem: elem}, nil
		}
		return nil, unsupported(e, "type %s", name)
	}
	return nil, unsupported(e, "type")
}

func namedType(name string, e glang.Expr) (*checker.Type, error) {
	switch name {
	case "go.int":
		return &checker.Type{Kind: checker.TyInt}, nil
	case "go.int64":
		return &checker.Type{Kind: checker.TyInt64}, nil
	case "go.uint64":
		return &checker.Type{Kind: checker.TyUint64}, nil
	case "go.bool", "go.untyped_bool":
		return &checker.Type{Kind: checker.TyBool}, nil
	}
	return nil, unsupported(e, "type %s", name)
}

// identName returns the text of an identifier-like glang expression.
func identName(e glang.Expr) (string, bool) {
	switch n := unwrap(e).(type) {
	case glang.GallinaIdent:
		return string(n), true
	case glang.VerbatimExpr:
		return string(n), true
	}
	return "", false
}

// unwrap strips the syntactic wrappers that carry no meaning for us.
func unwrap(e glang.Expr) glang.Expr {
	for {
		switch n := e.(type) {
		case glang.ParenExpr:
			e = n.Inner
		case glang.ValueScoped:
			e = n.Value
		default:
			return e
		}
	}
}

func unsupported(e glang.Expr, format string, args ...any) error {
	what := fmt.Sprintf(format, args...)
	text := "<nil>"
	if e != nil {
		text = e.Coq(false)
	}
	return fmt.Errorf("unsupported %s (%T): %s", what, e, text)
}
