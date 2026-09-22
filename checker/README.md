# checker: a CSL symbolic-execution checker for GooseLang

`checker` is a Go program that symbolically executes a (small fragment of a) Go
program, as translated to GooseLang by Goose, under a concurrent-separation-logic
precondition, and checks that every execution path is safe and establishes a
given postcondition. It exists to explore the "Observe-Execution" idea: rather
than checking a Perennial proof in Rocq (slow), run a Go checker on real
hardware and trust its answer via the axiom

    Executed Go program p and saw it return v
    ----------------------------------------- (OBSERVE-EXECUTION)
          (p, initg, initσ) ⤳* v

## Status and trust boundary

- The checker is **not verified** (yet). `new/checker/soundness.v` *states* what a
  `true` answer means (`Axiom check_sound`) in terms of the Goose translation of
  `checker.Check` (`new/code/github_com/mit_pdos/perennial/checker.v`); there is
  no proof and no Gallina reference implementation.
- The frontend `gocheck/` (Go source → checker input, spec parsing) is unverified
  marshalling, in the same role a kernel-level `exec` term would play.
- Trusted: the GooseLang semantics, `check_sound`, and the frontend.

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
  examples/long/    longer targets (Median3), not translated or proved in Rocq
gocheck/            frontend + CLI (not translated): translate/, spec/, render/, demo.sh
new/checker/soundness.v   the soundness statement (definitions + Axiom)
new/proof/github_com/mit_pdos/perennial/checker/examples/   hand-written Rocq
                          proofs of the same five specifications, one file
                          per function
new/code/github_com/mit_pdos/perennial/checker.v      Goose output for checker/
new/code/github_com/mit_pdos/perennial/checker/examples.v  Goose output for the examples
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

It runs the five examples with their specs, three failing cases (a missing
points-to, a wrong post, an ill-sorted spec) and a few variants, asserting the
exit code of each.

The last section of the demo establishes each of the five specifications the
other way too, with the hand-written Rocq proof of it in
`new/proof/github_com/mit_pdos/perennial/checker/examples/`, and prints the
wall-clock time of each. It rebuilds one `.vok` file per function -- the
incremental cost of re-checking that one proof against prebuilt dependencies --
and compares it against one whole run of the checker.

Most of a `-vok` run is spent loading the proof's imports, which says nothing
about the proof, so the table splits the Rocq time in two: `rocq compile -time`
attributes wall-clock time to each vernacular command, and an import is one
command, so the time spent on the imports and the time spent checking the proof
can be summed separately.

This part needs `rocq` in `PATH` and the dependencies built once, with

```
make -j$(nproc) TIMED=false \
  new/proof/github_com/mit_pdos/perennial/checker/examples/examples_init.vos
```

and says so and skips itself if either is missing.

Or by hand, e.g.

```
go run ./gocheck -pkg ./checker/examples \
   -pre 'z |-> z0' \
   -post '(⌜x == 0⌝ ∗ z ↦ 37 + 37) ∨ (⌜x != 0⌝ ∗ z ↦ x + x)' Double
```

Exit codes: 0 verified (or strongest postcondition printed when `-post` is
omitted), 1 the checker answered false (unsafe path or post not established),
2 usage/parse/translation error.

## Constraints on the core package (Goose translatability)

The core is translated by Goose so that the Rocq statement can talk about the
real program. Therefore `checker/` has **no imports** (an import would become a
package dependency in the translation), no maps, no generics, no `range` over
integers or strings, no labels. Failures are structured `Failure` values;
printing lives in `gocheck/render`. Terms, expressions, assertions and types are
never mutated after construction; states are cloned before forking. The numeric
kind codes in `ast.go`, `term.go`, `assn.go` are written out in
`new/checker/soundness.v`: do not renumber them.

## Regenerating the Goose output

```
go install ./goose/cmd/goose ./goose/cmd/proofgen
~/go/bin/goose    -out new/code/          -dir . ./checker ./checker/examples
~/go/bin/proofgen -out new/generatedproof -configdir new/code -dir . ./checker ./checker/examples
make -j$(nproc) TIMED=false new/code/github_com/mit_pdos/perennial/checker.vos \
     new/generatedproof/github_com/mit_pdos/perennial/checker.vos new/checker/soundness.vos
```

Never pass `./checker/...`: that would try to translate the frontend.

## Future work

- loops (`for:`) with invariants supplied as hints; function calls; structs.
- a pure prover (or VC emission) instead of syntactic matching.
- the soundness proof of `check_sound`, in Perennial, once the tool has proven
  useful.
- a kernel-level `exec` term replacing the hand-instantiated axiom.
