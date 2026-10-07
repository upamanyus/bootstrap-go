# checker: a CSL symbolic-execution checker for GooseLang

`checker` is a Go program that symbolically executes a (small fragment of a) Go
program, as translated to GooseLang by Goose, under a concurrent-separation-logic
precondition, and checks that every execution path is safe and establishes a
given postcondition. It exists to explore the "Observe-Execution" idea: rather
than checking a Perennial proof in Lean (slow), run a Go checker on real
hardware and trust its answer via the axiom

    Executed Go program p and saw it return v
    ----------------------------------------- (OBSERVE-EXECUTION)
          (p, initg, initσ) ⤳* v

## Status and trust boundary

- The checker is verified: `Checkers/Checker/Soundness.lean` states what a
  `true` answer means (`check_sound`) in terms of the Goose translation of
  `checker.Check` (`Generated/Code/github_com/upamanyus/bootstrap_go/checker.lean`),
  and it is proved (`Checkers/Checker/CheckSound.lean`; `notes/checker-port.md`
  describes the port, and `git show main:new/checker/NOTES.md` the proof).
- `Checkers/Checker/Adequacy.lean` closes the program logic: a finite real run
  of `checker.Check` from a heap holding the input that returns `true` gives
  `triple_holds`, the triple for every FFI, ghost state and Go semantics.
  (It takes `[GooseGpreS ffi GF]` as a premise, as Perennial Lean's own
  adequacy theorems do: Perennial Lean cannot build that instance for an
  arbitrary FFI.)
- `#print axioms` of `check_sound` and `check_adequate`: `propext`,
  `Classical.choice`, `Quot.sound`.
- The frontend `gocheck/` (Go source → checker input, spec parsing) is unverified
  marshalling. Its output is checked in Lean, though (see "From a run to a Lean
  proof").
- Trusted: the GooseLang semantics, the Goose translation, and the
  observation that the checker returned `true`.

## Layout

```
checker/            core, translated by Goose; NO imports (see below)
  ast.go            input language: Type, Op, Expr, Func  (kind codes are fixed)
  term.go           symbolic terms and sorts
  assn.go           assertions (emp, ∗, ∨, ∃, ⌜⌝, ↦)
  state.go          symbolic state, paths
  exec.go           symbolic execution
  match.go          postcondition matching
  check.go          Analyze / Verify / Check / Explain
  examples/         target Go programs for the demo
gocheck/            frontend + CLI (not translated): translate/, spec/, render/, demo.sh
Checkers/Checker/Defs.lean        the vocabulary of the statement (cfunc, cassn, triple_holds, ...)
Checkers/Checker/Soundness.lean   the soundness statement, check_sound
Checkers/Checker/**               its proof (Fn/: one file per Go function of checker/)
Checkers/Checker/Examples/        hand-written Lean proofs of the same six
                                  specifications, one file per function
  Observed/                       wp_Median3 from one observed run
Generated/Code/github_com/upamanyus/bootstrap_go/checker{,/examples}.lean   Goose output
```

## Fragment

Loop-free Go functions over `int`, `int64`, `uint64`, `bool` and pointers to
them, i.e. exactly what Goose emits for such functions: literals, variables,
`let:`/`;;`, `if:`, `GoAlloc`/`GoLoad`/`GoStore`/`GoZeroVal`, `GoOp` (`+ - * == <
<= > >=`), `GoUnOp` (`-`, `!`), identity `Convert`, and the exception monad
(`do:`, `return:`, `;;;`, `exception_do`). No loops, calls, structs, slices,
maps, channels, or concurrency.

## What the checker does

`Analyze(f, vars, pre)` binds parameter `i` to logical variable `i`, seeds a
symbolic state from the precondition (points-to atoms become owned heap cells,
pure atoms become the path condition) and executes the body:

- loads and stores require an owned cell with a *syntactically* equal location
  term (locations are always logical variables; there is no pointer arithmetic);
- `GoAlloc` creates a fresh location variable and cell; `GoZeroVal` yields the
  type's zero;
- arithmetic and comparisons require operands of the right sort and build terms
  (`<` is signed for `int`/`int64`, unsigned for `uint64`);
- `if:` on a symbolic condition `c` forks: one path adds `c` to the path
  condition, the other adds `¬c` (a double negation is cancelled);
- the exception monad is tracked exactly (`do:` yields `execute`, `return: e`
  yields `return e`, `;;;` short-circuits on `return`).

The result is one path per feasible branch: `(return term, heap, path condition)`
— the strongest postcondition. `Verify(paths, vars, post)` checks each path
against the postcondition.

### Postconditions and the matching policy

There is deliberately **no normalizer and no pure prover**: matching is
syntactic.

- The post may be a disjunction `P1 ∨ P2 ∨ …`; each path must satisfy some
  disjunct.
- Each disjunct may start with `∃ x y, …`; these are *pattern variables*, bound
  by matching `l ↦ x` against the heap. A pattern variable that occurs only in a
  location position cannot be bound and is rejected.
- `l ↦ t` matches a still-unconsumed heap cell with location `l` whose value is
  syntactically `t` (after substituting bound pattern variables and `ret`).
- `⌜φ⌝` holds iff `φ` occurs syntactically in the path condition, or is `t == t`
  with identical sides, or is literally `true`.
- Leftover heap cells are dropped (the logic is affine).

Pure obligations that need arithmetic are thus *your* job: write the
postcondition per path, exactly as the strongest postcondition prints it (run
`gocheck` without `-post` to see it). The printed paths also show the cells
Goose allocates for parameters and locals (`?l3 ↦ z`, ...); those cannot be
named in a post (their locations are fresh variables) and are simply dropped.
The return value prints as `⌜ret == t⌝` so that the output stays in the input
notation.

### Variable conventions

- In a **precondition**, every free name that is not a parameter is a new
  logical (universally quantified) variable; its sort is inferred from use
  (`z ↦ z0` with `z : *int` makes `z0 : int`). `∃` in a pre is accepted and
  means the same thing.
- In a **postcondition**, free names must be parameters or those logical
  variables; `∃`-bound names are pattern variables; `ret` is the return value.
- Comparisons need a signedness: `<u`/`<s` etc. force it, otherwise it is taken
  from the Go type of an operand name. Surface `a > b` and `a >= b` are
  desugared to `¬(a <= b)` and `¬(a < b)` so that negated branch conditions
  match; the checker itself represents Go's `>`/`>=` as swapped `<`/`<=`.

## Running the demo

```
bash gocheck/demo.sh
```

It runs the six examples with their specs, four failing cases (a missing
points-to, two wrong posts, an ill-sorted spec) and a few variants, asserting the
exit code of each.

The last section of the demo establishes each of the six specifications the
other way too, with the hand-written Lean proof in `Checkers/Checker/Examples/`,
and prints the wall-clock time of each: `lake env lean` on that one file
against prebuilt dependencies -- the incremental cost of re-checking that one
proof -- against one whole run of the checker. Most of a check is spent
loading the proof's imports, which says nothing about the proof, so the table
also times a file with the same imports and nothing else and reports the
difference. A typical run (`lake build Checkers.Checker.Examples.ExamplesInit`
first):

```
function      lean  imports   proof  gocheck proof/go
Double        2.88     1.97    0.91     0.04      23x
Max           2.53     2.02    0.51     0.05      10x
Swap          2.61     2.12    0.49     0.04      12x
Abs           2.48     2.00    0.48     0.04      12x
CondStore     2.63     2.03    0.60     0.04      15x
Median3       6.09     1.94    4.15     0.04     104x
```

Or by hand, e.g.

```
go run ./gocheck -pkg ./checker/examples \
   -pre 'z |-> z0' \
   -post '(⌜x == 0⌝ ∗ z ↦ 37 + 37) ∨ (⌜x != 0⌝ ∗ z ↦ x + x)' Double
```

Exit codes: 0 verified (or strongest postcondition printed when `-post` is
omitted), 1 the checker answered false (unsafe path or post not established),
2 usage/parse/translation error.

## From a run to a Lean proof

`gocheck -lean FILE` (with `-post`) also calls `checker.Check` on the input and
writes that input to FILE as Lean terms over `Checkers/Checker/Defs.lean`
(`cfunc`, `cassn`, `sort`). `gocheck/observe.sh` does this for Median3,
producing `Checkers/Checker/Examples/Observed/Median3Input.lean`, and fails
unless the checker answers `true`.

`Checkers/Checker/Examples/Observed/Median3.lean` then proves `wp_Median3`
from one axiom, `median3_check_run`: some GooseLang run of `checker.Check` on
exactly that input returns `#true` (OBSERVE-EXECUTION). `check_adequate` turns
the run into `triple_holds`. The function in the input is checked to be
Goose's `Median3` by `rfl`, so the frontend's translation is not trusted. The
postcondition is read off by computation (`Checkers/Checker/PostSimp.lean`:
one rewrite and `simp only`), with no case analysis or arithmetic per program.

The resulting specification returns a `val`: `RET v` with `⌜v = #b⌝`, not
`RET #r` with `⌜r = b⌝`. The two forms are equivalent, but only the first is
the checker's postcondition up to simplification. In the second, the last two
(contradictory) disjuncts would have to be refuted by arithmetic before an
`r` can be produced, and each of the others would need a case of its own to
pick one.

With the dependencies built, the two proofs of `wp_Median3` cost
(`lake env lean`, wall clock; about 2 s of each is loading imports):

```
Examples/Median3.lean            5.8-6.2 s   hand-written
Examples/Observed/Median3.lean   3.8-4.0 s   from the checker's run
gocheck                          0.04 s      built binary
```

(`main`'s Rocq version also had a third proof, by reflection with `wp_symex`;
that executor is not ported.)

## Constraints on the core package (Goose translatability)

The core is translated by Goose so that the Lean statement can talk about the
real program. Therefore `checker/` has **no imports** (an import would become a
package dependency in the translation), no maps, no generics, no `range` over
integers or strings, no labels. Failures are structured `Failure` values;
printing lives in `gocheck/render`. Terms, expressions, assertions and types are
never mutated after construction; states are cloned before forking. The numeric
kind codes in `ast.go`, `term.go`, `assn.go` are written out in
`Checkers/Checker/Defs.lean`: do not renumber them.


## Regenerating the Goose output

```
bash etc/goose.sh            # goose and proofgen of the pinned Perennial dependency
lake build Generated
```

`etc/goose.sh` lists the packages (`./checker ./checker/examples ./tcheck`).
Never pass `./checker/...`: that would try to translate the frontend.

## Future work

- loops (`for:`) with invariants supplied as hints; function calls; structs.
- a pure prover (or VC emission) instead of syntactic matching.
- a kernel-level `exec` term replacing the hand-instantiated axiom.
