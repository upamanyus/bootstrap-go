package checker

// Symbolic terms: first-order symbolic values manipulated by the checker.
//
// Kind codes are part of the trusted interface with new/checker/soundness.v;
// do not renumber.

// Sort classifies the values a term can denote.
type Sort uint64

const (
	SortInt  Sort = 0 // 64-bit machine integer (int, int64, uint64)
	SortBool Sort = 1
	SortLoc  Sort = 2 // pointer
	SortUnit Sort = 3
)

// TermKind identifies the form of a Term. The comment lists the meaningful
// fields.
type TermKind uint64

const (
	TVar    TermKind = 1 // Num = logical variable index (parameter, ghost, or allocated)
	TPat    TermKind = 2 // Num = postcondition pattern variable (∃-bound) index
	TResult TermKind = 3 // `ret`: the return value of the path (postconditions only)
	TInt    TermKind = 4 // Num
	TBool   TermKind = 5 // Num (0 or 1)
	TUnit   TermKind = 6
	TNull   TermKind = 7
	TAdd    TermKind = 8  // A, B    (wrapping 64-bit)
	TSub    TermKind = 9  // A, B
	TMul    TermKind = 10 // A, B
	TNeg    TermKind = 11 // A
	TEq     TermKind = 12 // A, B    (equality at any sort)
	TLtS    TermKind = 13 // A, B    signed <
	TLtU    TermKind = 14 // A, B    unsigned <
	TLeS    TermKind = 15 // A, B    signed <=
	TLeU    TermKind = 16 // A, B    unsigned <=
	TNot    TermKind = 17 // A
	TIte    TermKind = 18 // A (condition), B, C
	TExec   TermKind = 19 // exception-monad value ("execute", ())
	TRet    TermKind = 20 // exception-monad value ("return", A)
)

// Term is a symbolic value. Terms are immutable once constructed and may be
// shared between states and paths.
type Term struct {
	Kind TermKind
	Num  uint64
	A    *Term
	B    *Term
	C    *Term
}

// termEq decides structural equality of two terms (nil-safe).
func termEq(a *Term, b *Term) bool {
	if a == nil {
		return b == nil
	}
	if b == nil {
		return false
	}
	if a.Kind != b.Kind || a.Num != b.Num {
		return false
	}
	return termEq(a.A, b.A) && termEq(a.B, b.B) && termEq(a.C, b.C)
}
