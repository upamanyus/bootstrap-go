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

- The checker is verified: `new/checker/soundness.v` states what a `true`
  answer means (`check_sound`) in terms of the Goose translation of
  `checker.Check` (`new/code/github_com/mit_pdos/perennial/checker.v`), and
  it is proved (`new/checker/NOTES.md` describes the proof).
- `new/checker/adequacy.v` closes the program logic: a crash-free run of
  `checker.Check` from a heap holding the input that returns `true` gives
  `triple_holds`, the triple for every FFI, ghost state and Go semantics.
- The frontend `gocheck/` (Go source → checker input, spec parsing) is unverified
  marshalling, in the same role a kernel-level `exec` term would play. Its
  output can be checked in Rocq, though (see "From a run to a Rocq proof").
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
  rocqgoal/         reads Rocq goals exported by new/proof/rocqgoal/ (see its README)
new/checker/soundness.v   the soundness statement (definitions + Axiom)
new/proof/github_com/mit_pdos/perennial/checker/examples/   hand-written Rocq
                          proofs of the same six specifications, one file
                          per function
  reflect/                the same six lemmas again, proved with wp_symex
new/proof/symex/          wp_symex: symbolic execution by reflection (see below)
new/proof/rocqgoal/       export.v: a generic goal exporter, Rocq proof state -> S-expression
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

It runs the six examples with their specs, four failing cases (a missing
points-to, two wrong posts, an ill-sorted spec) and a few variants, asserting the
exit code of each.

The last section of the demo establishes each of the six specifications the
other way too, in Rocq, with two proofs of each: the hand-written one in
`new/proof/github_com/mit_pdos/perennial/checker/examples/`, and one by
reflection in its `reflect/` subdirectory (see "Proof by reflection" below). It
prints the wall-clock time of each: it rebuilds one `.vok` file per proof -- the
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
  new/proof/github_com/mit_pdos/perennial/checker/examples/examples_init.vo \
  new/proof/symex/tactic.vo
```

(or the same targets as `.vos`), and says so and skips itself if either is
missing. A typical run:

```
                hand-written     by reflection
function        -vok   proof      -vok   proof  gocheck hand/refl  refl/go
Double          5.16    2.38      3.43    0.76     0.05        3x      15x
Max             4.10    1.21      3.05    0.51     0.05        2x      10x
Swap            4.49    1.49      3.06    0.26     0.05        6x       5x
Abs             3.74    1.25      3.41    0.33     0.05        4x       7x
CondStore       3.93    1.41      3.24    0.57     0.05        2x      11x
Median3        24.27   21.63      5.79    3.16     0.05        7x      63x
```

The gap grows with the length of the program: the hand-written Median3 spends
about 17 of its 22 seconds stepping through the eight paths with `wp_auto` and
`wp_if_destruct`, which `wp_symex` does in a quarter of a second. What is left of
the reflective proofs is the per-path reasoning (for Median3, refuting the two
infeasible paths with `word`, about 1.7 seconds), which the two proofs share.

Or by hand, e.g.

```
go run ./gocheck -pkg ./checker/examples \
   -pre 'z |-> z0' \
   -post '(⌜x == 0⌝ ∗ z ↦ 37 + 37) ∨ (⌜x != 0⌝ ∗ z ↦ x + x)' Double
```

Exit codes: 0 verified (or strongest postcondition printed when `-post` is
omitted), 1 the checker answered false (unsafe path or post not established),
2 usage/parse/translation error.

## From a run to a Rocq proof

`gocheck -rocq FILE` (with `-post`) also calls `checker.Check` on the input and
writes that input to FILE as Rocq terms over `new/checker/defs.v` (`cfunc`,
`cassn`, `sort`). `gocheck/observe.sh` does this for Median3, producing
`new/proof/github_com/mit_pdos/perennial/checker/examples/observed/median3_input.v`,
and fails unless the checker answers `true`.

`observed/median3.v` then proves `wp_Median3` from one axiom,
`median3_check_run`: some GooseLang run of `checker.Check` on exactly that
input returns `#true` (OBSERVE-EXECUTION). `check_adequate` turns the run into
`triple_holds`. The function in the input is checked to be Goose's `Median3`
by `reflexivity`, so the frontend's translation is not trusted. The
postcondition is read off by computation (`new/checker/post_simp.v`: one
rewrite and `simpl`), with no case analysis or arithmetic per program.

The resulting specification returns a `val`: `RET v` with `⌜v = #b⌝`, not
`RET #r` with `⌜r = b⌝`. The two forms are equivalent, but only the first is
the checker's postcondition up to simplification. In the second, the last two
(contradictory) disjuncts would have to be refuted by arithmetic before an
`r` can be produced, and each of the others would need a case of its own to
pick one.

With the dependencies built, the three proofs of `wp_Median3` cost (`rocq
compile -vok -time`, as in the demo):

```
proof                  total  imports  proof
median3.v              22.88     2.29  20.34   hand-written
reflect/median3.v       5.50     2.11   3.21   wp_symex
observed/median3.v      3.31     2.55   0.57   from the checker's run
gocheck                 0.23                   go run, including go build
```

## Proof by reflection: `wp_symex`

`new/proof/symex/` is a from-scratch reflective symbolic executor for the same
kind of Go code, written in Gallina and proved sound once, so that a proof of a
function's specification does not have to step through the function in the
proof mode. It is independent of the Go checker and of
`new/checker/`: nothing in it mirrors checker/ or the checker's Rocq model.

```
syntax.v   the reflected syntax (sexpr: the loop-free fragment Goose emits for
           int/int64/uint64/bool/pointer code, including its exception monad),
           symbolic values over numbered atoms, and the executor [exec]
           (continuation-passing, forks on if:, one path per branch)
denote.v   what the syntax means: values and expressions as GooseLang,
           symbolic heaps as typed points-to, paths as the residual goal
sound.v    symex_sound, proved once by induction on the executor's fuel
tactic.v   wp_symex: an Ltac reifier and the tactic
```

On a goal `WP e {{ Φ }}` (for instance right after `wp_start`), `wp_symex`
reifies `e`, and the full-ownership typed points-to facts of the spatial context,
into syntax over an environment of the Rocq words, booleans and locations they
mention; runs the executor with `vm_compute`; applies `symex_sound`, checking
that the syntax denotes `e` by conversion and the executor's answer with a
`vm_cast`; frames the initial heap; and leaves one goal per path:

```
∀ (locations allocated on the path) (_ : path condition) .., cells -∗ .. -∗ Φ ret
```

with the path condition stated the way a person would write it
(`uint.Z b ≤ uint.Z a` for the `else` branch of `a < b`), and without the cells
Goose allocates for parameters and locals, which nothing the caller can name
points to. `symex_intros` introduces all of it. For `Max`:

```
wp_start as "_". wp_symex.
- symex_intros. iApply "HΦ". iLeft. by iPureIntro.
- symex_intros. iApply "HΦ". iRight. by iPureIntro.
```

Unlike the Go checker, the executor needs no trust: a `wp_symex` proof is an
ordinary Rocq proof, checked by the kernel. What it does not do is reason about
the path conditions -- infeasible paths are left as goals with contradictory
hypotheses, to be refuted by `word` -- or support loops, calls, structs or slices.

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
