package spec

import (
	"fmt"

	"github.com/mit-pdos/perennial/checker"
	"github.com/mit-pdos/perennial/gocheck/translate"
)

// SortName is the surface name of a sort.
func SortName(s checker.Sort) string {
	switch s {
	case checker.SortInt:
		return "int"
	case checker.SortBool:
		return "bool"
	case checker.SortLoc:
		return "ptr"
	case checker.SortUnit:
		return "unit"
	}
	return fmt.Sprintf("sort#%d", uint64(s))
}

func sortByName(name string) (checker.Sort, bool) {
	switch name {
	case "int":
		return checker.SortInt, true
	case "bool":
		return checker.SortBool, true
	case "ptr", "loc":
		return checker.SortLoc, true
	case "unit":
		return checker.SortUnit, true
	}
	return 0, false
}

// sortVar is a (possibly still unknown) sort, with union-find so that
// equalities between two unknown sorts can be recorded.
type sortVar struct {
	parent *sortVar
	known  bool
	s      checker.Sort
	desc   string
}

func conc(s checker.Sort) *sortVar { return &sortVar{known: true, s: s} }

func (v *sortVar) find() *sortVar {
	root := v
	for root.parent != nil {
		root = root.parent
	}
	for v.parent != nil {
		v.parent, v = root, v.parent
	}
	return root
}

func (v *sortVar) describe() string {
	r := v.find()
	if r.desc != "" {
		return r.desc
	}
	if r.known {
		return SortName(r.s)
	}
	return "this term"
}

func unify(a, b *sortVar) error {
	x, y := a.find(), b.find()
	if x == y {
		return nil
	}
	switch {
	case x.known && y.known:
		if x.s != y.s {
			ad, bd := x.desc, y.desc
			switch {
			case ad != "" && bd != "":
				return fmt.Errorf("sort mismatch: %s has sort %s but %s has sort %s",
					ad, SortName(x.s), bd, SortName(y.s))
			case ad != "":
				return fmt.Errorf("sort mismatch: %s has sort %s, but sort %s is "+
					"required here", ad, SortName(x.s), SortName(y.s))
			case bd != "":
				return fmt.Errorf("sort mismatch: %s has sort %s, but sort %s is "+
					"required here", bd, SortName(y.s), SortName(x.s))
			}
			return fmt.Errorf("sort mismatch: expected %s, found %s",
				SortName(y.s), SortName(x.s))
		}
		y.parent = x
	case x.known:
		y.parent = x
	default:
		x.parent = y
	}
	return nil
}

// entry is a resolved name: a logical variable (TVar) or a postcondition
// pattern variable (TPat).
type entry struct {
	name string
	idx  uint64
	pat  bool
	sv   *sortVar
	ty   *checker.Type // Go type, when known (used for signedness)
}

// Scope maps names to logical-variable indices. It starts out holding the
// function's parameters and grows with the ghost variables mentioned by the
// precondition.
type Scope struct {
	Names []string       // index -> name
	sorts []checker.Sort // index -> sort
	base  map[string]*entry

	// patNames records, per postcondition disjunct, the names of the pattern
	// variables in index order. It is filled in by LowerPost.
	patNames [][]string
}

// NewScope builds a scope holding the parameters of a function.
func NewScope(params []translate.ParamInfo) (*Scope, error) {
	sc := &Scope{base: make(map[string]*entry)}
	for i, p := range params {
		if p.Index != i {
			return nil, fmt.Errorf("parameter %q has index %d, want %d", p.Name, p.Index, i)
		}
		s, ok := checker.TypeSort(p.Ty)
		if !ok {
			return nil, fmt.Errorf("parameter %q has an unsupported type", p.Name)
		}
		sc.Names = append(sc.Names, p.Name)
		sc.sorts = append(sc.sorts, s)
		sv := conc(s)
		sv.desc = fmt.Sprintf("%q", p.Name)
		sc.base[p.Name] = &entry{name: p.Name, idx: uint64(i), sv: sv, ty: p.Ty}
	}
	return sc, nil
}

// Vars returns the sorts of the logical variables, indexed by variable index.
func (sc *Scope) Vars() []checker.Sort {
	out := make([]checker.Sort, len(sc.sorts))
	copy(out, sc.sorts)
	return out
}

// GoType returns the Go type of logical variable i, or nil if none was
// inferred. The type is held on the variable's entry, where the resolver
// records and reads it; this is only a lookup by index, for diagnostics.
func (sc *Scope) GoType(i int) *checker.Type {
	if i < 0 || i >= len(sc.Names) {
		return nil
	}
	e, ok := sc.base[sc.Names[i]]
	if !ok {
		return nil
	}
	return e.ty
}

// Sort returns the sort of logical variable i.
func (sc *Scope) Sort(i int) (checker.Sort, bool) {
	if i < 0 || i >= len(sc.sorts) {
		return 0, false
	}
	return sc.sorts[i], true
}

// PatNames returns the pattern-variable names of postcondition disjunct d.
func (sc *Scope) PatNames(d int) []string {
	if d < 0 || d >= len(sc.patNames) {
		return nil
	}
	return sc.patNames[d]
}

// resolver carries the state of one lowering.
type resolver struct {
	sc      *Scope
	post    bool
	scopes  []map[string]*entry // innermost last; scopes[0] aliases sc.base
	names   map[*Term]*entry    // resolved TName occurrences
	binders map[*Assn][]*entry  // resolved ∃ binders
	newVars []*entry            // logical variables created by a precondition
	pats    []*entry            // pattern variables of the current disjunct
	allPats [][]*entry          // pattern variables per disjunct
	retSort *sortVar
}

func (sc *Scope) newResolver(post bool) *resolver {
	return &resolver{
		sc:      sc,
		post:    post,
		scopes:  []map[string]*entry{sc.base},
		names:   make(map[*Term]*entry),
		binders: make(map[*Assn][]*entry),
		retSort: &sortVar{desc: "ret"},
	}
}

func (r *resolver) lookup(name string) *entry {
	for i := len(r.scopes) - 1; i >= 0; i-- {
		if e, ok := r.scopes[i][name]; ok {
			return e
		}
	}
	return nil
}

func errAt(pos int, format string, args ...any) error {
	return fmt.Errorf("at offset %d: %s", pos, fmt.Sprintf(format, args...))
}

// LowerPre lowers a precondition, extending the scope with one logical
// variable per free (or ∃-bound) name that is not a parameter.
func (sc *Scope) LowerPre(s *Surface) (*checker.Assn, error) {
	r := sc.newResolver(false)
	if err := r.inferAssn(s.A); err != nil {
		return nil, err
	}
	if err := r.finishSorts(); err != nil {
		return nil, err
	}
	a, err := r.lowerAssn(s.A)
	if err != nil {
		return nil, err
	}
	// Commit the new logical variables to the scope.
	for _, e := range r.newVars {
		sc.Names = append(sc.Names, e.name)
		sc.sorts = append(sc.sorts, e.sv.find().s)
		sc.base[e.name] = e
	}
	return a, nil
}

// LowerPost lowers a postcondition. Free names must already be in scope;
// ∃-bound names become pattern variables numbered from 0 within each
// disjunct.
func (sc *Scope) LowerPost(s *Surface) (*checker.Assn, error) {
	r := sc.newResolver(true)
	if err := r.inferTop(s.A); err != nil {
		return nil, err
	}
	if err := r.finishSorts(); err != nil {
		return nil, err
	}
	a, err := r.lowerTop(s.A)
	if err != nil {
		return nil, err
	}
	sc.patNames = nil
	for _, ps := range r.allPats {
		var names []string
		for _, e := range ps {
			names = append(names, e.name)
		}
		sc.patNames = append(sc.patNames, names)
	}
	return a, nil
}

// LowerTerm lowers a term written against sc. Like a postcondition, it may
// mention `ret` and may not introduce new logical variables: every name must
// already be a parameter or a precondition variable.
func (sc *Scope) LowerTerm(s *SurfaceTerm) (*checker.Term, error) {
	r := sc.newResolver(true)
	if _, err := r.inferTerm(s.T, nil); err != nil {
		return nil, err
	}
	if err := r.finishSorts(); err != nil {
		return nil, err
	}
	return r.lowerTerm(s.T)
}

// finishSorts checks that every variable's sort was determined.
func (r *resolver) finishSorts() error {
	var all []*entry
	all = append(all, r.newVars...)
	for _, ps := range r.allPats {
		all = append(all, ps...)
	}
	for _, e := range all {
		if !e.sv.find().known {
			what := "logical variable"
			hint := fmt.Sprintf("mention it in a points-to or annotate it: ∃ (%s:int), ...", e.name)
			if e.pat {
				what = "pattern variable"
			}
			return fmt.Errorf("cannot determine the sort of %s %q; %s", what, e.name, hint)
		}
	}
	return nil
}

// ---------------------------------------------------------------- inference

// inferTop walks a postcondition: ∨ at the top level, then one disjunct.
func (r *resolver) inferTop(a *Assn) error {
	if a.Kind == AOr {
		if err := r.inferTop(a.L); err != nil {
			return err
		}
		return r.inferTop(a.R)
	}
	r.pats = nil
	depth := len(r.scopes)
	if err := r.inferDisjunct(a); err != nil {
		return err
	}
	r.scopes = r.scopes[:depth]
	r.allPats = append(r.allPats, r.pats)
	r.pats = nil
	return nil
}

// inferDisjunct peels the ∃ binders at the head of a disjunct.
func (r *resolver) inferDisjunct(a *Assn) error {
	for a.Kind == AExists {
		scope := make(map[string]*entry)
		for _, b := range a.Binders {
			e := &entry{name: b.Name, idx: uint64(len(r.pats)), pat: true,
				sv: &sortVar{desc: fmt.Sprintf("%q", b.Name)}}
			if b.Sort != "" {
				s, ok := sortByName(b.Sort)
				if !ok {
					return errAt(b.Pos, "unknown sort %q", b.Sort)
				}
				e.sv = conc(s)
				e.sv.desc = fmt.Sprintf("%q", b.Name)
			}
			r.pats = append(r.pats, e)
			r.binders[a] = append(r.binders[a], e)
			scope[b.Name] = e
		}
		r.scopes = append(r.scopes, scope)
		a = a.Body
	}
	return r.inferAssn(a)
}

func (r *resolver) inferAssn(a *Assn) error {
	switch a.Kind {
	case AEmp:
		return nil
	case ASep:
		if err := r.inferAssn(a.L); err != nil {
			return err
		}
		return r.inferAssn(a.R)
	case AOr:
		if !r.post {
			return errAt(a.Pos, "∨ is not allowed in a precondition")
		}
		return errAt(a.Pos, "∨ is only allowed at the top level of a postcondition")
	case AExists:
		if r.post {
			return errAt(a.Pos, "∃ must come first in a postcondition disjunct")
		}
		// In a precondition an ∃ is lifted: its binders become ordinary
		// logical variables.
		scope := make(map[string]*entry)
		for _, b := range a.Binders {
			e, err := r.newLogicalVar(b.Name, b.Sort, b.Pos)
			if err != nil {
				return err
			}
			r.binders[a] = append(r.binders[a], e)
			scope[b.Name] = e
		}
		r.scopes = append(r.scopes, scope)
		if err := r.inferAssn(a.Body); err != nil {
			return err
		}
		r.scopes = r.scopes[:len(r.scopes)-1]
		return nil
	case APure:
		_, err := r.inferTerm(a.X, conc(checker.SortBool))
		return err
	case APointsTo:
		if _, err := r.inferTerm(a.X, conc(checker.SortLoc)); err != nil {
			return err
		}
		// If the location's Go type is known, it fixes the sort (and the Go
		// type) of the stored value.
		var want *sortVar
		var elem *checker.Type
		if ty := r.goTypeOf(a.X); ty != nil && ty.Kind == checker.TyPtr {
			elem = ty.Elem
			s, ok := checker.TypeSort(elem)
			if !ok {
				return errAt(a.Pos, "points-to at an unsupported pointer type")
			}
			want = conc(s)
		}
		sv, err := r.inferTerm(a.Y, want)
		if err != nil {
			return err
		}
		_ = sv
		if elem != nil {
			r.setGoType(a.Y, elem)
		}
		return nil
	}
	return errAt(a.Pos, "unhandled assertion form")
}

// newLogicalVar allocates a fresh logical variable (precondition only).
func (r *resolver) newLogicalVar(name string, sortAnn string, pos int) (*entry, error) {
	e := &entry{
		name: name,
		idx:  uint64(len(r.sc.Names) + len(r.newVars)),
		sv:   &sortVar{desc: fmt.Sprintf("%q", name)},
	}
	if sortAnn != "" {
		s, ok := sortByName(sortAnn)
		if !ok {
			return nil, errAt(pos, "unknown sort %q", sortAnn)
		}
		e.sv = conc(s)
		e.sv.desc = fmt.Sprintf("%q", name)
	}
	r.newVars = append(r.newVars, e)
	return e, nil
}

func (r *resolver) inferTerm(t *Term, want *sortVar) (*sortVar, error) {
	got, err := r.inferTermRaw(t)
	if err != nil {
		return nil, err
	}
	if want != nil {
		if err := unify(got, want); err != nil {
			return nil, errAt(t.Pos, "%s", err)
		}
	}
	return got, nil
}

func (r *resolver) inferTermRaw(t *Term) (*sortVar, error) {
	sInt := func() (*sortVar, error) {
		if _, err := r.inferTerm(t.A, conc(checker.SortInt)); err != nil {
			return nil, err
		}
		if t.B != nil {
			if _, err := r.inferTerm(t.B, conc(checker.SortInt)); err != nil {
				return nil, err
			}
		}
		return conc(checker.SortInt), nil
	}
	sBoolArgs := func() (*sortVar, error) {
		if _, err := r.inferTerm(t.A, conc(checker.SortBool)); err != nil {
			return nil, err
		}
		if t.B != nil {
			if _, err := r.inferTerm(t.B, conc(checker.SortBool)); err != nil {
				return nil, err
			}
		}
		return conc(checker.SortBool), nil
	}
	switch t.Kind {
	case TNum:
		return conc(checker.SortInt), nil
	case TBoolLit:
		return conc(checker.SortBool), nil
	case TUnitLit:
		return conc(checker.SortUnit), nil
	case TNullLit:
		return conc(checker.SortLoc), nil
	case TRet:
		if !r.post {
			return nil, errAt(t.Pos, "ret is only allowed in a postcondition")
		}
		return r.retSort, nil
	case TName:
		e := r.lookup(t.Name)
		if e == nil {
			if r.post {
				return nil, errAt(t.Pos, "unknown name %q in a postcondition: it is not a "+
					"parameter or a precondition variable (bind it with `∃ %s,` if it is "+
					"existentially quantified)", t.Name, t.Name)
			}
			var err error
			e, err = r.newLogicalVar(t.Name, "", t.Pos)
			if err != nil {
				return nil, err
			}
			r.scopes[0][t.Name] = e
		}
		r.names[t] = e
		return e.sv, nil
	case TAdd, TSub, TMul, TNeg:
		return sInt()
	case TNot, TAnd, TOr:
		return sBoolArgs()
	case TLt, TLe, TGt, TGe:
		if _, err := sInt(); err != nil {
			return nil, err
		}
		return conc(checker.SortBool), nil
	case TEq, TNe:
		sa, err := r.inferTerm(t.A, nil)
		if err != nil {
			return nil, err
		}
		sb, err := r.inferTerm(t.B, nil)
		if err != nil {
			return nil, err
		}
		if err := unify(sa, sb); err != nil {
			return nil, errAt(t.Pos, "%s", err)
		}
		// Propagate a known Go type across the equality, so that a later
		// comparison can pick up its signedness.
		if ty := r.goTypeOf(t.A); ty != nil {
			r.setGoType(t.B, ty)
		} else if ty := r.goTypeOf(t.B); ty != nil {
			r.setGoType(t.A, ty)
		}
		return conc(checker.SortBool), nil
	case TIf:
		if _, err := r.inferTerm(t.A, conc(checker.SortBool)); err != nil {
			return nil, err
		}
		sb, err := r.inferTerm(t.B, nil)
		if err != nil {
			return nil, err
		}
		sc, err := r.inferTerm(t.C, nil)
		if err != nil {
			return nil, err
		}
		if err := unify(sb, sc); err != nil {
			return nil, errAt(t.Pos, "the branches of `if` disagree: %s", err)
		}
		return sb, nil
	}
	return nil, errAt(t.Pos, "unhandled term form")
}

// goTypeOf reports the Go type of a term, looking through unary minus and the
// branches of an `if`.
func (r *resolver) goTypeOf(t *Term) *checker.Type {
	if t == nil {
		return nil
	}
	switch t.Kind {
	case TName:
		if e, ok := r.names[t]; ok {
			return e.ty
		}
	case TNeg:
		return r.goTypeOf(t.A)
	case TIf:
		if ty := r.goTypeOf(t.B); ty != nil {
			return ty
		}
		return r.goTypeOf(t.C)
	}
	return nil
}

// setGoType records a Go type for a name that did not have one yet.
func (r *resolver) setGoType(t *Term, ty *checker.Type) {
	if t == nil || ty == nil {
		return
	}
	if t.Kind == TName {
		if e, ok := r.names[t]; ok && e.ty == nil {
			e.ty = ty
		}
	}
}

// ----------------------------------------------------------------- lowering

func (r *resolver) lowerTop(a *Assn) (*checker.Assn, error) {
	if a.Kind == AOr {
		l, err := r.lowerTop(a.L)
		if err != nil {
			return nil, err
		}
		rr, err := r.lowerTop(a.R)
		if err != nil {
			return nil, err
		}
		return &checker.Assn{Kind: checker.AOr, L: l, R: rr}, nil
	}
	return r.lowerAssn(a)
}

func (r *resolver) lowerAssn(a *Assn) (*checker.Assn, error) {
	switch a.Kind {
	case AEmp:
		return &checker.Assn{Kind: checker.AEmp}, nil
	case ASep:
		l, err := r.lowerAssn(a.L)
		if err != nil {
			return nil, err
		}
		rr, err := r.lowerAssn(a.R)
		if err != nil {
			return nil, err
		}
		return &checker.Assn{Kind: checker.ASep, L: l, R: rr}, nil
	case AExists:
		body, err := r.lowerAssn(a.Body)
		if err != nil {
			return nil, err
		}
		if !r.post {
			// Lifted: the binders are ordinary logical variables now.
			return body, nil
		}
		es := r.binders[a]
		for i := len(es) - 1; i >= 0; i-- {
			body = &checker.Assn{Kind: checker.AExists, Var: es[i].idx,
				Sort: es[i].sv.find().s, L: body}
		}
		return body, nil
	case APure:
		x, err := r.lowerTerm(a.X)
		if err != nil {
			return nil, err
		}
		return &checker.Assn{Kind: checker.APure, X: x}, nil
	case APointsTo:
		x, err := r.lowerTerm(a.X)
		if err != nil {
			return nil, err
		}
		y, err := r.lowerTerm(a.Y)
		if err != nil {
			return nil, err
		}
		return &checker.Assn{Kind: checker.APointsTo, X: x, Y: y}, nil
	}
	return nil, errAt(a.Pos, "unhandled assertion form")
}

func (r *resolver) lowerTerm(t *Term) (*checker.Term, error) {
	bin := func(k checker.TermKind) (*checker.Term, error) {
		a, err := r.lowerTerm(t.A)
		if err != nil {
			return nil, err
		}
		b, err := r.lowerTerm(t.B)
		if err != nil {
			return nil, err
		}
		return &checker.Term{Kind: k, A: a, B: b}, nil
	}
	switch t.Kind {
	case TNum:
		return &checker.Term{Kind: checker.TInt, Num: t.Num}, nil
	case TBoolLit:
		n := uint64(0)
		if t.Bool {
			n = 1
		}
		return &checker.Term{Kind: checker.TBool, Num: n}, nil
	case TUnitLit:
		return &checker.Term{Kind: checker.TUnit}, nil
	case TNullLit:
		return &checker.Term{Kind: checker.TNull}, nil
	case TRet:
		return &checker.Term{Kind: checker.TResult}, nil
	case TName:
		e := r.names[t]
		if e == nil {
			return nil, errAt(t.Pos, "unresolved name %q", t.Name)
		}
		if e.pat {
			return &checker.Term{Kind: checker.TPat, Num: e.idx}, nil
		}
		return &checker.Term{Kind: checker.TVar, Num: e.idx}, nil
	case TAdd:
		return bin(checker.TAdd)
	case TSub:
		return bin(checker.TSub)
	case TMul:
		return bin(checker.TMul)
	case TEq:
		return bin(checker.TEq)
	case TNeg:
		a, err := r.lowerTerm(t.A)
		if err != nil {
			return nil, err
		}
		return &checker.Term{Kind: checker.TNeg, A: a}, nil
	case TNot:
		a, err := r.lowerTerm(t.A)
		if err != nil {
			return nil, err
		}
		return &checker.Term{Kind: checker.TNot, A: a}, nil
	case TNe:
		eq, err := bin(checker.TEq)
		if err != nil {
			return nil, err
		}
		return &checker.Term{Kind: checker.TNot, A: eq}, nil
	case TAnd:
		a, err := r.lowerTerm(t.A)
		if err != nil {
			return nil, err
		}
		b, err := r.lowerTerm(t.B)
		if err != nil {
			return nil, err
		}
		return &checker.Term{Kind: checker.TIte, A: a, B: b,
			C: &checker.Term{Kind: checker.TBool, Num: 0}}, nil
	case TOr:
		a, err := r.lowerTerm(t.A)
		if err != nil {
			return nil, err
		}
		b, err := r.lowerTerm(t.B)
		if err != nil {
			return nil, err
		}
		return &checker.Term{Kind: checker.TIte, A: a,
			B: &checker.Term{Kind: checker.TBool, Num: 1}, C: b}, nil
	case TIf:
		a, err := r.lowerTerm(t.A)
		if err != nil {
			return nil, err
		}
		b, err := r.lowerTerm(t.B)
		if err != nil {
			return nil, err
		}
		c, err := r.lowerTerm(t.C)
		if err != nil {
			return nil, err
		}
		return &checker.Term{Kind: checker.TIte, A: a, B: b, C: c}, nil
	case TLt, TLe, TGt, TGe:
		signed, err := r.signOf(t)
		if err != nil {
			return nil, err
		}
		switch t.Kind {
		case TLt:
			if signed {
				return bin(checker.TLtS)
			}
			return bin(checker.TLtU)
		case TLe:
			if signed {
				return bin(checker.TLeS)
			}
			return bin(checker.TLeU)
		case TGt:
			// a > b  is  ¬(a <= b)
			var le *checker.Term
			if signed {
				le, err = bin(checker.TLeS)
			} else {
				le, err = bin(checker.TLeU)
			}
			if err != nil {
				return nil, err
			}
			return &checker.Term{Kind: checker.TNot, A: le}, nil
		default:
			// a >= b  is  ¬(a < b)
			var lt *checker.Term
			if signed {
				lt, err = bin(checker.TLtS)
			} else {
				lt, err = bin(checker.TLtU)
			}
			if err != nil {
				return nil, err
			}
			return &checker.Term{Kind: checker.TNot, A: lt}, nil
		}
	}
	return nil, errAt(t.Pos, "unhandled term form")
}

var relText = map[TermKind]string{TLt: "<", TLe: "<=", TGt: ">", TGe: ">="}

// signOf decides whether a comparison is signed.
func (r *resolver) signOf(t *Term) (bool, error) {
	switch t.Sign {
	case SignSigned:
		return true, nil
	case SignUnsigned:
		return false, nil
	}
	for _, side := range []*Term{t.A, t.B} {
		ty := r.goTypeOf(side)
		if ty == nil {
			continue
		}
		switch ty.Kind {
		case checker.TyInt, checker.TyInt64:
			return true, nil
		case checker.TyUint64:
			return false, nil
		}
	}
	op := relText[t.Kind]
	return false, errAt(t.Pos, "cannot determine signedness of %s; write %su or %ss", op, op, op)
}
