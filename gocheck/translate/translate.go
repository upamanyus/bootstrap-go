// Package translate converts the GooseLang output of goose into the
// checker's input language.
package translate

import (
	"fmt"
	"math/big"
	"sort"
	"strings"

	"github.com/upamanyus/bootstrap-go/checker"
	"github.com/mit-pdos/perennial/goose"
	"github.com/mit-pdos/perennial/goose/glang"
)

// ParamInfo records what we learned about one Go parameter of a function: its
// name, its position in the parameter list, and its Go type (recovered from
// the GoAlloc prologue that goose emits).
type ParamInfo struct {
	Name  string
	Index int
	Ty    *checker.Type
}

// Package is a goose-translated Go package.
type Package struct {
	Path  string
	decls map[string]glang.FuncDecl
	order []string
}

// LoadPackage runs goose on a single package pattern and collects its function
// declarations. configDir is the goose output root (where the per-package
// configuration lives) and modDir is the directory containing go.mod.
func LoadPackage(configDir string, modDir string, pattern string) (*Package, error) {
	files, errs, patternErr := goose.TranslatePackages(configDir, modDir, pattern)
	if patternErr != nil {
		return nil, fmt.Errorf("goose: %w", patternErr)
	}
	if len(files) != 1 {
		return nil, fmt.Errorf("pattern %q matched %d packages, want exactly 1", pattern, len(files))
	}
	if errs[0] != nil {
		return nil, fmt.Errorf("goose: %w", errs[0])
	}
	p := &Package{Path: files[0].PkgPath, decls: make(map[string]glang.FuncDecl)}
	for _, d := range files[0].Decls {
		fd, ok := d.(glang.FuncDecl)
		if !ok {
			continue
		}
		name, ok := strings.CutSuffix(fd.Name, glang.FuncImpl(""))
		if !ok {
			continue
		}
		if _, dup := p.decls[name]; dup {
			continue
		}
		p.decls[name] = fd
		p.order = append(p.order, name)
	}
	return p, nil
}

// Names lists the translated function names, sorted.
func (p *Package) Names() []string {
	names := make([]string, len(p.order))
	copy(names, p.order)
	sort.Strings(names)
	return names
}

// Func converts the named Go function to a checker.Func.
func (p *Package) Func(name string) (*checker.Func, []ParamInfo, error) {
	fd, ok := p.decls[name]
	if !ok {
		return nil, nil, fmt.Errorf("package %s has no translated function %s (have: %s)",
			p.Path, name, strings.Join(p.Names(), ", "))
	}
	return FuncDecl(fd)
}

// FuncDecl converts one goose function declaration.
func FuncDecl(fd glang.FuncDecl) (*checker.Func, []ParamInfo, error) {
	if fd.RecvArg != nil {
		return nil, nil, fmt.Errorf("methods are not supported (receiver %q)", fd.RecvArg.Name)
	}
	if len(fd.TypeArgs) != 0 {
		return nil, nil, fmt.Errorf("generic functions are not supported")
	}
	body, err := expr(fd.Body)
	if err != nil {
		return nil, nil, err
	}
	var params []string
	for _, a := range fd.Args {
		params = append(params, a.Name)
	}
	f := &checker.Func{Params: params, Body: body}
	infos, err := paramInfo(params, body)
	if err != nil {
		return nil, nil, err
	}
	return f, infos, nil
}

// paramInfo recovers the Go type of each parameter from the allocation
// prologue `let: "p" := GoAlloc Ty "p" in ...` that goose emits (in reverse
// parameter order) at the top of the function body.
func paramInfo(params []string, body *checker.Expr) ([]ParamInfo, error) {
	want := make(map[string]int, len(params))
	for i, p := range params {
		want[p] = i
	}
	found := make(map[string]*checker.Type, len(params))
	e := body
	if e != nil && e.Kind == checker.EExcDo {
		e = e.A
	}
	for e != nil && e.Kind == checker.ELet {
		if a := e.A; a != nil && a.Kind == checker.EAlloc &&
			a.A != nil && a.A.Kind == checker.EVar && a.A.Name == e.Name {
			if _, ok := want[e.Name]; ok {
				if _, dup := found[e.Name]; !dup {
					found[e.Name] = a.Ty
				}
			}
		}
		e = e.B
	}
	var infos []ParamInfo
	for i, p := range params {
		ty, ok := found[p]
		if !ok {
			return nil, fmt.Errorf("cannot determine the Go type of parameter %q: "+
				"no `let: %q := GoAlloc _ %q` in the function prologue", p, p, p)
		}
		infos = append(infos, ParamInfo{Name: p, Index: i, Ty: ty})
	}
	return infos, nil
}

var binOps = map[glang.OpId]checker.Op{
	glang.OpPlus:        checker.OpAdd,
	glang.OpMinus:       checker.OpSub,
	glang.OpMul:         checker.OpMul,
	glang.OpEquals:      checker.OpEq,
	glang.OpLessThan:    checker.OpLt,
	glang.OpLessEq:      checker.OpLe,
	glang.OpGreaterThan: checker.OpGt,
	glang.OpGreaterEq:   checker.OpGe,
}

var opNames = map[glang.OpId]string{
	glang.OpNotEquals: "!=",
	glang.OpQuot:      "/",
	glang.OpRem:       "%",
	glang.OpShl:       "<<",
	glang.OpShr:       ">>",
	glang.OpAnd:       "&",
	glang.OpAndNot:    "&^",
	glang.OpOr:        "|",
	glang.OpXor:       "^",
	glang.OpLAnd:      "&&",
	glang.OpLOr:       "||",
	glang.OpNot:       "!",
}

func opName(id glang.OpId) string {
	if s, ok := opNames[id]; ok {
		return s
	}
	return fmt.Sprintf("op#%d", int(id))
}

// expr converts a GooseLang expression.
func expr(e glang.Expr) (*checker.Expr, error) {
	e = unwrap(e)
	switch n := e.(type) {
	case glang.CallExpr:
		return callExpr(n)
	case glang.LetExpr:
		return letExpr(n)
	case glang.SeqExpr:
		if n.Cont == nil {
			return expr(n.Expr)
		}
		a, err := expr(n.Expr)
		if err != nil {
			return nil, err
		}
		b, err := expr(n.Cont)
		if err != nil {
			return nil, err
		}
		return &checker.Expr{Kind: checker.EExcSeq, A: a, B: b}, nil
	case glang.DoExpr:
		a, err := expr(n.Expr)
		if err != nil {
			return nil, err
		}
		return &checker.Expr{Kind: checker.EDo, A: a}, nil
	case glang.ReturnExpr:
		return returnExpr(n)
	case glang.IfExpr:
		a, err := expr(n.Cond)
		if err != nil {
			return nil, err
		}
		b, err := expr(n.Then)
		if err != nil {
			return nil, err
		}
		c, err := expr(n.Else)
		if err != nil {
			return nil, err
		}
		return &checker.Expr{Kind: checker.EIf, A: a, B: b, C: c}, nil
	case glang.DerefExpr:
		ty, err := Type(n.Ty)
		if err != nil {
			return nil, err
		}
		a, err := expr(n.X)
		if err != nil {
			return nil, err
		}
		return &checker.Expr{Kind: checker.ELoad, Ty: ty, A: a}, nil
	case glang.StoreStmt:
		ty, err := Type(n.Ty)
		if err != nil {
			return nil, err
		}
		a, err := expr(n.Dst)
		if err != nil {
			return nil, err
		}
		b, err := expr(n.X)
		if err != nil {
			return nil, err
		}
		return &checker.Expr{Kind: checker.EStore, Ty: ty, A: a, B: b}, nil
	case glang.BinaryExpr:
		op, ok := binOps[n.Op.OpId]
		if !ok {
			return nil, unsupported(e, "binary operator %s", opName(n.Op.OpId))
		}
		ty, err := Type(n.Op.Type)
		if err != nil {
			return nil, err
		}
		a, err := expr(n.X)
		if err != nil {
			return nil, err
		}
		b, err := expr(n.Y)
		if err != nil {
			return nil, err
		}
		return &checker.Expr{Kind: checker.EBinOp, Op: op, Ty: ty, A: a, B: b}, nil
	case glang.UnaryExpr:
		var op checker.Op
		switch n.Op.OpId {
		case glang.OpMinus:
			op = checker.OpNeg
		case glang.OpNot:
			op = checker.OpNot
		default:
			return nil, unsupported(e, "unary operator %s", opName(n.Op.OpId))
		}
		ty, err := Type(n.Op.Type)
		if err != nil {
			return nil, err
		}
		a, err := expr(n.X)
		if err != nil {
			return nil, err
		}
		return &checker.Expr{Kind: checker.EUnOp, Op: op, Ty: ty, A: a}, nil
	case glang.NotExpr:
		a, err := expr(n.X)
		if err != nil {
			return nil, err
		}
		return &checker.Expr{Kind: checker.EUnOp, Op: checker.OpNot,
			Ty: &checker.Type{Kind: checker.TyBool}, A: a}, nil
	case glang.IdentExpr:
		return &checker.Expr{Kind: checker.EVar, Name: string(n)}, nil
	case glang.ToVal:
		return toVal(n)
	case glang.Int64Val:
		num, err := intLit(n.Value)
		if err != nil {
			return nil, err
		}
		return &checker.Expr{Kind: checker.EInt, Num: num}, nil
	case glang.GooseBoolLiteral:
		num := uint64(0)
		if bool(n) {
			num = 1
		}
		return &checker.Expr{Kind: checker.EBool, Num: num}, nil
	case glang.UnitLiteral:
		return &checker.Expr{Kind: checker.EUnit}, nil
	}
	return nil, unsupported(e, "expression")
}

func toVal(n glang.ToVal) (*checker.Expr, error) {
	switch v := unwrap(n.Value).(type) {
	case glang.CallExpr:
		if name, ok := identName(v.MethodName); ok && name == "W64" && len(v.Args) == 1 {
			num, err := intLit(v.Args[0])
			if err != nil {
				return nil, err
			}
			return &checker.Expr{Kind: checker.EInt, Num: num}, nil
		}
	case glang.ZLiteral:
		return &checker.Expr{Kind: checker.EInt, Num: zToU64(v.Value)}, nil
	case glang.GooseBoolLiteral:
		num := uint64(0)
		if bool(v) {
			num = 1
		}
		return &checker.Expr{Kind: checker.EBool, Num: num}, nil
	case glang.UnitLiteral:
		return &checker.Expr{Kind: checker.EUnit}, nil
	}
	return nil, unsupported(n, "literal")
}

func intLit(e glang.Expr) (uint64, error) {
	z, ok := unwrap(e).(glang.ZLiteral)
	if !ok {
		return 0, unsupported(e, "integer literal")
	}
	return zToU64(z.Value), nil
}

// zToU64 reduces an arbitrary integer literal to its 64-bit two's complement
// representation, the way W64 does.
func zToU64(z *big.Int) uint64 {
	if z == nil {
		return 0
	}
	mask := new(big.Int).Lsh(big.NewInt(1), 64)
	mask.Sub(mask, big.NewInt(1))
	return new(big.Int).And(z, mask).Uint64()
}

func callExpr(n glang.CallExpr) (*checker.Expr, error) {
	name, ok := identName(n.MethodName)
	if !ok {
		return nil, unsupported(n, "function call")
	}
	switch name {
	case "exception_do":
		if len(n.Args) != 1 {
			return nil, unsupported(n, "exception_do with %d arguments", len(n.Args))
		}
		a, err := expr(n.Args[0])
		if err != nil {
			return nil, err
		}
		return &checker.Expr{Kind: checker.EExcDo, A: a}, nil
	case "GoAlloc":
		if len(n.Args) != 2 {
			return nil, unsupported(n, "GoAlloc with %d arguments", len(n.Args))
		}
		ty, err := Type(n.Args[0])
		if err != nil {
			return nil, err
		}
		a, err := expr(n.Args[1])
		if err != nil {
			return nil, err
		}
		return &checker.Expr{Kind: checker.EAlloc, Ty: ty, A: a}, nil
	case "GoZeroVal":
		if len(n.Args) != 2 {
			return nil, unsupported(n, "GoZeroVal with %d arguments", len(n.Args))
		}
		ty, err := Type(n.Args[0])
		if err != nil {
			return nil, err
		}
		if _, ok := unwrap(n.Args[1]).(glang.UnitLiteral); !ok {
			return nil, unsupported(n, "GoZeroVal second argument")
		}
		return &checker.Expr{Kind: checker.EZero, Ty: ty}, nil
	case "Convert":
		if len(n.Args) != 3 {
			return nil, unsupported(n, "Convert with %d arguments", len(n.Args))
		}
		from, err := Type(n.Args[0])
		if err != nil {
			return nil, err
		}
		to, err := Type(n.Args[1])
		if err != nil {
			return nil, err
		}
		a, err := expr(n.Args[2])
		if err != nil {
			return nil, err
		}
		return &checker.Expr{Kind: checker.EConvert, Ty: from, Ty2: to, A: a}, nil
	}
	return nil, unsupported(n, "call to %s", name)
}

func letExpr(n glang.LetExpr) (*checker.Expr, error) {
	if n.Cont == nil {
		return expr(n.ValExpr)
	}
	if len(n.Names) > 1 {
		return nil, unsupported(n, "let with %d bound names", len(n.Names))
	}
	a, err := expr(n.ValExpr)
	if err != nil {
		return nil, err
	}
	b, err := expr(n.Cont)
	if err != nil {
		return nil, err
	}
	if len(n.Names) == 0 {
		return &checker.Expr{Kind: checker.ESeq, A: a, B: b}, nil
	}
	return &checker.Expr{Kind: checker.ELet, Name: n.Names[0], A: a, B: b}, nil
}

func returnExpr(n glang.ReturnExpr) (*checker.Expr, error) {
	v := unwrap(n.Value)
	switch t := v.(type) {
	case glang.TupleExpr:
		if len(t) != 1 {
			return nil, unsupported(n, "return of %d values", len(t))
		}
		a, err := expr(t[0])
		if err != nil {
			return nil, err
		}
		return &checker.Expr{Kind: checker.EReturn, A: a}, nil
	case glang.UnitLiteral:
		return &checker.Expr{Kind: checker.EReturn,
			A: &checker.Expr{Kind: checker.EUnit}}, nil
	}
	a, err := expr(v)
	if err != nil {
		return nil, err
	}
	return &checker.Expr{Kind: checker.EReturn, A: a}, nil
}
