// Package checker is a separation-logic symbolic-execution proof checker for
// a fragment of GooseLang, the Go semantics used by Perennial.
//
// # What it does
//
// Given a GooseLang function value (Func), the sorts of the logical variables
// it is specified over, a precondition and a postcondition, Check reports
// whether the function is safe under the precondition and establishes the
// postcondition. Analyze does the symbolic execution alone and returns the
// strongest postcondition as a list of Paths; Verify matches those paths
// against a user-written postcondition, and Explain says why a match failed.
//
// # Fragment
//
// The supported expressions are exactly the ExprKind constants in ast.go:
// integer, boolean and unit literals, variables, let, sequencing, if, load,
// store, allocation, zero values, the Go binary and unary operators, identity
// conversions, and the four constructs of Goose's exception monad (do,
// return, ;;; and exception_do). The supported types are int, int64, uint64,
// bool and pointers to those (TypeKind in ast.go). There is no recursion, no
// loops, no function calls, no structs, slices, maps or channels.
//
// Symbolic values are first-order Terms over machine integers, booleans,
// locations and unit, classified by Sort. The checker does no arithmetic or
// SMT reasoning at all: a path condition is a list of boolean terms, and a
// pure postcondition atom is discharged only if it is syntactically one of
// them (or a reflexive equation, or `true`). Likewise a store or load only
// succeeds at a location that is structurally equal to one the symbolic heap
// already owns; there is no pointer-arithmetic or aliasing reasoning.
//
// Analyze explores every branch eagerly, so the number of paths is
// exponential in the number of `if`s. That is acceptable for the small
// functions this checker is aimed at.
//
// # Trust boundary
//
// This Go package is unverified: nothing here is proved, and a bug in it
// could make Check return true for an unsafe function. What makes the answer
// meaningful is the Rocq side. new/checker/soundness.v states what a `true`
// answer means: if Check returns true for a function value, a precondition
// and a postcondition, then the corresponding Perennial specification of that
// GooseLang function holds. Only that statement, the GooseLang semantics, and
// the Observe-Execution axiom that lets a proof assume the result of running
// this program, are trusted. So a wrong answer from this package cannot let
// an unsound Perennial proof through: the Rocq statement is what has to be
// discharged, and this package is only the oracle that computes it.
//
// # Style constraints
//
// The package is written so that Goose can translate it, and therefore:
//
//   - it has no imports at all, so failures are the structured Failure values
//     in check.go rather than error strings;
//   - it uses no maps, no generics, no closures and no goto, and the variable
//     environment is a linked list (env in exec.go) rather than a map, since
//     Go's map iteration order is unspecified and the model of a map in
//     Perennial is far heavier than that of a linked list;
//   - kind constants are written out numerically rather than with iota.
//
// # Immutability invariant
//
// Term, Expr, Assn and Type values are never mutated after construction. They
// are shared freely between paths, states and assertions, and structural
// equality (termEq, TypeEq) rather than pointer identity is what the checker
// compares. Only State (and the scratch values inside Verify) is mutable, and
// a State is always copied with clone before it is modified, so that forking
// at an `if` or appending to a heap on one path can never be observed on
// another.
//
// # Do not renumber kinds
//
// The numeric values of TypeKind, Op, ExprKind, Sort, TermKind and AssnKind
// are part of the trusted interface with the Rocq soundness statement, which
// spells them out numerically. Renumbering one of them silently changes what
// new/checker/soundness.v means and would invalidate proofs that depend on
// it. Add new kinds with new numbers; never reuse or shift an existing one.
package checker
