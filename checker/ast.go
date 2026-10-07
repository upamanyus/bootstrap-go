package checker

// This file defines the input language of the checker: the fragment of
// GooseLang (Perennial's Go semantics) that it can symbolically execute.
//
// The kind codes below are part of the trusted interface with the Rocq
// soundness statement in new/checker/soundness.v, which spells them out
// numerically. Do not renumber them.

// TypeKind identifies a supported Go type.
type TypeKind uint64

const (
	TyInt    TypeKind = 1 // go.int
	TyInt64  TypeKind = 2 // go.int64
	TyUint64 TypeKind = 3 // go.uint64
	TyBool   TypeKind = 4 // go.bool (also go.untyped_bool, which is the same type)
	TyPtr    TypeKind = 5 // go.PointerType Elem
)

// Type is a supported Go type. Elem is set only for TyPtr.
type Type struct {
	Kind TypeKind
	Elem *Type
}

// Op is a Go operator (GooseLang go_operator / go_unary_operator).
type Op uint64

const (
	OpAdd Op = 1  // +
	OpSub Op = 2  // -
	OpMul Op = 3  // *
	OpEq  Op = 4  // ==
	OpLt  Op = 5  // <
	OpLe  Op = 6  // <=
	OpGt  Op = 7  // >
	OpGe  Op = 8  // >=
	OpNeg Op = 9  // unary -
	OpNot Op = 10 // unary !
)

// ExprKind identifies the form of an Expr. The comment on each kind lists the
// fields that are meaningful for it; all other fields are zero.
type ExprKind uint64

const (
	EInt     ExprKind = 1  // Num                          #(W64 Num)
	EBool    ExprKind = 2  // Num (0 or 1)                 #false / #true
	EUnit    ExprKind = 3  //                              #()
	EVar     ExprKind = 4  // Name                         "Name"
	ELet     ExprKind = 5  // Name, A, B                   let: Name := A in B
	ESeq     ExprKind = 6  // A, B                         A ;; B
	EIf      ExprKind = 7  // A, B, C                      if: A then B else C
	ELoad    ExprKind = 8  // Ty, A                        ![Ty] A
	EStore   ExprKind = 9  // Ty, A, B                     A <-[Ty] B
	EAlloc   ExprKind = 10 // Ty, A                        GoAlloc Ty A
	EZero    ExprKind = 11 // Ty                           GoZeroVal Ty #()
	EBinOp   ExprKind = 12 // Op, Ty, A, B                 GoOp Op Ty (A, B)
	EUnOp    ExprKind = 13 // Op, Ty, A                    GoUnOp Op Ty A
	EConvert ExprKind = 14 // Ty (from), Ty2 (to), A       Convert Ty Ty2 A
	EDo      ExprKind = 15 // A                            do: A
	EReturn  ExprKind = 16 // A                            return: A
	EExcSeq  ExprKind = 17 // A, B                         A ;;; B
	EExcDo   ExprKind = 18 // A                            exception_do A
)

// Expr is a GooseLang expression in the supported fragment. Expressions are
// immutable once constructed and may be shared.
type Expr struct {
	Kind ExprKind
	Name string // EVar, ELet
	Num  uint64 // EInt, EBool
	Op   Op     // EBinOp, EUnOp
	Ty   *Type  // ELoad, EStore, EAlloc, EZero, EBinOp, EUnOp, EConvert (from)
	Ty2  *Type  // EConvert (to)
	A    *Expr
	B    *Expr
	C    *Expr
}

// Func is a curried GooseLang function value `λ: p0 .. pn, Body` as Goose
// emits for a Go function declaration. A Go function without parameters is
// translated to `λ: <>, Body`, represented here with an empty Params.
type Func struct {
	Params []string
	Body   *Expr
}
