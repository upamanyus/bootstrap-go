# tcheck: a table-driven checker, and OBSERVE-EXECUTION for raft

`tcheck/` is a Go symbolic executor for Goose code whose knowledge of the
program comes entirely from a **table of rules**: Hoare triples, each linked
to a lemma that is already proved in Lean. It establishes a function's
specification by running on real hardware; Lean then trusts the run through
one generated axiom per function, which records exactly the bytes the checker
consumed.

The first client is the Lean port of the raft election proof (the
`etcdGrove` dependency, `.lake/packages/etcdGrove/EtcdGrove/Raft/ElectionProof/`):
the `raft.wp_load_*` / `raft.wp_store_*` accessor lemmas of `InvRaftPhys.lean`,
`Logger.wp_logf` (`InvLogger.lean`), the callees' specs and the pure steps
`wp_auto` takes are rows of `Checkers/TCheck/Raft/raft.tbl`, and
`becomeFollower` is established from one observed run: as the rule callers
use (`raft_rule_becomeFollower_ok`), and, by conversion, as etcdGrove's own
statement `raft.becomeFollower.spec` (`Spec/raft__becomeFollower.lean`), with
the callee specs `raft.reset.spec` and `traceBecomeFollower.spec` as
hypotheses (`theorem raft.becomeFollower.wp_proof`, etcdGrove's spec/proof
discipline).

This is a port of the Rocq development on branch `main`
(`gocheck/tcheck/README.md` there); the Go checker `tcheck/` is unchanged.

## Pieces

```
tcheck/                    the checker (Goose-translated: no imports)
  syntax.go parse.go       its input, and the byte format it reads
  term.go exec.go check.go matching, symbolic execution, well-formedness
gocheck/tcheck/            the frontend (not translated, not trusted)
  table.go sexp.go         table files
  goose.go                 reads a function out of Goose's Lean output
  ser.go lean.go main.go   serialization, Lean output, the command
  observe.sh               recheck and regenerate every observation
  reflect_bench.sh         time the Lean checker against the observation
LCheck/TCheck/
  Syntax.lean Check.lean   the input's types, and `ltcheck` (precompiled)
Checkers/TCheck/
  Syntax.lean              the input in Lean, and `ser_input`
  Denote.lean              what an input means (`input_holds`)
  Observe.lean             `observed_run`, and the axiom `check_adequate`
  Link.lean                tactics and lemmas for linking rules to lemmas
  Reflect/                 `ltcheck_sound` (Terms, Code, Heap, Rules, Eval, Sound)
Checkers/TCheck/Raft/
  raft.tbl                 the raft table (hand-written)
  TableRaft.lean           its syntax and denotation (generated)
  LinkTableRaft.lean       each rule proved from its lemma (hand-written)
  Observed/raft__becomeFollower.lean   one run (generated)
  Proof/raft__becomeFollower.lean      the rule, and etcdGrove's spec, from that run (hand-written)
  Reflect/raft__becomeFollower.lean    the same, from `ltcheck` instead of the run
```

The Goose output the frontend reads is Perennial's Lean translation of the
raft package, `.lake/packages/perennial/Perennial/Code/go_etcd_io/raft/v3.lean`,
where a function is a plain term of GooseLang's constructors
(`raft.becomeFollower.impl := LamV "r" (Lam "term" (… (App (Val exceptionDo) …))))`).

## What is trusted

Reading `Checkers/TCheck/Observe.lean` once is the whole audit:

- **`check_adequate`** (an `axiom`): if `tcheck.Check` returns `true` on
  `ser_input i`, then `input_holds i`. This is the checker's soundness and
  **is not proved yet**; it is stated against the Goose translation of
  `tcheck.Check`
  (`Generated/Code/github_com/upamanyus/bootstrap_go/tcheck.lean`), so it can
  be proved the way `new/checker/` proved `check_sound` for `checker/`.
- **One observation per function**: `axiom f_check_run : observed_run go!"<bytes>"`,
  generated, whose bytes are verbatim what the Go run read (as a Lean string
  literal; Perennial's `go!` elaborator turns it into its UTF-8 bytes).
  `bash gocheck/tcheck/observe.sh` reruns `tcheck.Check` on those bytes,
  regenerates every observation file from scratch (reifying the code and
  running the checker again), and fails unless the output is identical.

Not trusted: the frontend. The function's code is checked to be Goose's by
`rfl` (`f_func_val`); every rule is proved from a lemma (so a mis-transcribed
rule fails to link); the bytes are checked to be `ser_input` of the Lean
input by kernel evaluation (`decide +kernel`, never `native_decide`); and the
final specification is etcdGrove's, imported, not restated.

`#print axioms raft.becomeFollower.wp_proof` lists `check_adequate` and
`becomeFollower_check_run` next to the axioms the raft proof already has
(etcdGrove's `isLogger`, `Logger.wp_logf`, `ownStorage`; Perennial's opaque
types of other packages) and Lean's three; no `sorryAx`.

## The table

A table (`raft.tbl`) declares user **sorts** (Lean types), **symbols** (Lean
functions, including the code's constants: `GoInstruction`s, Go types,
literals), **predicates** (`IProp GF`s, some `persistent`), **rules**
(`∀ vars, {{ pre }} lhs {{ ∃ ex, RET ret; post }}`, where `lhs` is an
application of values) and **facts** (equations, used left to right), and
the Lean it is written against: `(import "Module")`, `(open "Ns ..")`,
`(code "path.lean" NAMESPACE)` and `(assumptions `Class`)`. Each declaration
carries its denotation in backquotes, e.g.

```
(sym fld_step (loc) loc `fun r : Loc => r.[raft, go!"step"]`)
(pred phys (cfgset loc w64 nstate) `ownRaftPhys`)
(rule store_step (vars (cfg cfgset) (r loc) (id w64) (s nstate) (f func))
  (lhs (app k_store_stepFunc (pair (val_loc (fld_step r)) (val_func f))))
  (pre (phys cfg r id s)) (ret unit) (post (phys cfg r id (set_stepfn s f))))
```

`rule_valid` of a rule is, up to unfolding, the lemma's own statement, so a
link is the lemma itself:

```lean
theorem raft_rule_store_step_ok : rule_valid (raft_den (hG := hG)) raft_rule_store_step :=
  raft.wp_store_step
```

Rules proved by hand (pure steps, the slice literal) start with
`raft_rule_start`, which computes the triple (`tc_simp`, `Link.lean`) and
introduces the rule's variables; a pure step is then `rule_pure`.

The table's denotation lives at one ambient setting (the section variables
of a spec, plus the package assumptions), so `cfg` is a parameter of every
rule, `isPkgInit` is a persistent predicate in the precondition of the rules
that need it, and there is one table for the package. An observation records
only the rules and facts its run used, so a proof links just those: shared
rules from `LinkTableRaft.lean`, rules for callees from the callee specs it
takes as hypotheses. The rules are etcdGrove's lemmas exactly: e.g. the rule
for `reset` has both conjuncts of `raft.reset.spec`'s postcondition (the
second as the predicate `reset_matched`), though `becomeFollower` uses only
the first.

## Specifications are rules

A `func` of the table has a `(head TERM)`, the value called (for a method,
`val_func (meth_becomeFollower r)`, i.e. `#(methods T m #r)`). The table file
defines its specification `raft_spec_F` and the rule callers use,
`raft_rule_F := spec_rule head raft_spec_F`: the call of the head on the
arguments after the receiver. Other functions' runs may use that rule; a
function's own run never does. The observation proves `input_holds`, a
triple about `func_val f` applied to the arguments; `spec_rule_valid`
(`Link.lean`, proved once for every function) turns it into `rule_valid` of
the rule, given `F_call_ok` (generated: the head is the method value, and the
method unfolds to the checked function, `F_func_val`, by `rfl`). So the
per-function proof is

```lean
theorem raft_rule_becomeFollower_ok (wp_raft_reset : raft.reset.spec (GF := GF) (hG := hG))
    (wp_traceBecomeFollower : traceBecomeFollower.spec (GF := GF) (hG := hG)) :
    rule_valid (raft_den (hG := hG)) raft_rule_becomeFollower :=
  spec_rule_valid _ _ _ _ (becomeFollower_holds (raft_den (hG := hG))
    (becomeFollower_table_ok wp_raft_reset wp_traceBecomeFollower)) becomeFollower_call_ok
```

and etcdGrove's statement follows by conversion alone (the theorem's body is
the line above). As in Rocq, nothing computes the denotation inside a
hypothesis: `call_ok_of` rewrites the function before anything is unfolded
(computing a denotation inside a hypothesis cost the first Rocq version of
this proof 4.5 minutes).

Costs for `becomeFollower` (this machine; `lake env lean FILE` with the
dependencies built, wall time, about 2.0 s of each being the loading of the
imports; Rocq's from `main`'s README for comparison):

| | Lean | Rocq |
|---|---|---|
| `go run ./gocheck/tcheck ... -func becomeFollower` (built binary: 0.04 s) | 0.13 s | 0.15 s |
| `Observed/raft__becomeFollower.lean` (5.1 s of it the kernel's `decide` of the bytes; `F_func_val`'s `rfl` 0.26 s) | 7.7 s | 8.9 s |
| `Proof/raft__becomeFollower.lean` (`becomeFollower_table_ok` 0.34 s, the conversion to the spec 0.21 s) | 2.8 s | 8.0 s |
| `LinkTableRaft.lean` (once per table; `tc_simp` 0.1–0.25 s per hand-proved rule) | 3.1 s | 9.9 s |
| `TableRaft.lean` (once per table) | 3.8 s | |
| the hand-written proof of `becomeFollower` | (not ported to Lean) | 12.1 s |

## The Lean checker: `becomeFollower` by reflection

`ltcheck` (`LCheck/TCheck/Check.lean`) is this checker's algorithm as Lean
functions, and its soundness is **proved**:

```lean
theorem ltcheck_sound (i : tinput) : ltcheck i = true → input_holds i
```

(`Checkers/TCheck/Reflect/Sound.lean`; `#print axioms`: Lean's three). That is
the statement `check_adequate` claims for a `true` answer of the Go checker, so
`Checkers/TCheck/Raft/Reflect/raft__becomeFollower.lean` proves etcdGrove's
`raft.becomeFollower.spec` (`raft.becomeFollower.wp_proof_reflect`) from
`ltcheck_sound` and `decide +kernel` on the same input, with neither
`check_adequate` nor the observation: `#print axioms` is the observed proof's
minus those two. The file also proves the input's `input_holds` by
`native_decide` (`ltcheck` is in the precompiled library `LCheck`).

`ltcheck` follows `tcheck/` closely, but checks what its soundness needs where
it needs it instead of checking the input's well-formedness up front, has fuel
for its loops, evaluates in GooseLang's order, and is structurally recursive
(the header of `Check.lean` lists the differences). The proof
(`Checkers/TCheck/Reflect/`, about 2,600 lines) is in five layers: terms (sorts,
substitution, matching, normalization by valid facts), the code (substitution
of the environment, the function's beta steps), the symbolic state (persistent
and non-persistent atoms), rules (`applyRule_sound`: the rule's triple, at the
values matching bound; the spine search and `reduce`), and evaluation
(`eval_sound`, one case per construct, in continuation-passing style).

`bash gocheck/tcheck/reflect_bench.sh` (2026-10-07):

```
Lean (version 4.34.1, x86_64-unknown-linux-gnu, commit 5045d0056413266e57c625dcd7c365b10e377c52, Release)

input_holds becomeFollower_input: seconds of wall clock, median of 3 runs, minus imports
  observed  5.13
  kernel    1.50
  native    0.15
  interp    0.12

Lean's profiler (one run; cumulative over the file):
  observed  type checking 4.77s (of which the bytes = ser_input check is most)
  kernel    type checking 1.17s
  native    evaluation 3.84ms
  interp    evaluation 7.64ms

One call of the checker on becomeFollower's input, microseconds, mean of 10000 calls:
  Go        tcheck.Check 327.777, tcheck.Run 192.645
  ltcheck   compiled 208.6, interpreted 3118.8 (1000 calls)
```

The observed proof's cost is nearly all the kernel's check that the axiom's
bytes are `ser_input` of the input; the reflective proof replaces it with the
kernel running the checker itself (1.2 s) or, with `native_decide`, with 4 ms of
evaluation. Compiled, `ltcheck` costs what the Go checker's `tcheck.Run` costs
(about 0.2 ms; `tcheck.Check` also parses the bytes).

## How the checker executes

It interprets core GooseLang. `let:`, `;;` and the exception monad (`do:`,
`return:`, `;;;`, `exception_do`) are built in; everything else is an
application, evaluated in GooseLang's order (argument, then function), and
handed to the rules as an *application of values*. The function position is
kept unreduced, so a spec stated at `#(methods T "reset" #r) #term` applies
before or after the method is resolved: a rule may apply to the whole
application or to any application on its function spine. Rules match
syntactically (first-order matching, then the precondition's predicates
against the symbolic heap, first match), and terms are normalized with the
facts. No `if:` yet.

The Lean Goose output nests statements differently from the Rocq one (a
function's final `return: #()` is the continuation of the whole rest of the
body, `(let: "$r0" := … in (do: … ;;; …)) ;;; return: #()`, where Rocq's is
the innermost statement); the checker handles either, since `;;;` and `let:`
are interpreted compositionally.

## Use

```
go run ./gocheck/tcheck -table T.tbl -gen-table TableT.lean \
    -table-file TableT.lean -func NAME -observe Observed/T__NAME.lean
bash gocheck/tcheck/observe.sh            # recheck everything
go run ./gocheck/tcheck -verify Observed/T__NAME.lean
```

(for raft: `-table Checkers/TCheck/Raft/raft.tbl -gen-table
Checkers/TCheck/Raft/TableRaft.lean -table-file
Checkers/TCheck/Raft/TableRaft.lean -func becomeFollower -observe
Checkers/TCheck/Raft/Observed/raft__becomeFollower.lean`; every generated
file records its command in its header, which is what `observe.sh` reruns.)

When the code uses a constant the table does not declare, the tool prints
the declarations to add, in the form the leaf is compared in. When no rule
applies, it prints the stuck application with the table's names, e.g.

```
checker.Check: false -- no rule applies to
  (app (val_func fn_traceBecomeFollower) (val_loc ?1))
```
