package checker

// Assertions: the separation-logic formulas used for pre- and postconditions.
//
// Kind codes are part of the trusted interface with new/checker/soundness.v;
// do not renumber.

// AssnKind identifies the form of an Assn.
type AssnKind uint64

const (
	AEmp      AssnKind = 1 //                 emp
	ASep      AssnKind = 2 // L, R            L ∗ R
	AOr       AssnKind = 3 // L, R            L ∨ R        (postconditions only, top level)
	AExists   AssnKind = 4 // Var, Sort, L    ∃ (pat Var : Sort), L   (postconditions only)
	APure     AssnKind = 5 // X               ⌜X⌝  (X is a boolean term)
	APointsTo AssnKind = 6 // X, Y            X ↦ Y
)

// Assn is an assertion. In a precondition only AEmp, ASep, APure and
// APointsTo may appear. In a postcondition, AOr may appear at the top level
// (a disjunction over paths) and each disjunct may start with AExists binders
// whose pattern variables (TPat) are instantiated by matching points-to
// atoms against the symbolic heap.
type Assn struct {
	Kind AssnKind
	L    *Assn
	R    *Assn
	X    *Term
	Y    *Term
	Var  uint64 // AExists: pattern variable index
	Sort Sort   // AExists: sort of that pattern variable
}
