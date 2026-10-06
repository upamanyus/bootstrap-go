# tcheck: a table-driven checker, and OBSERVE-EXECUTION for raft

`tcheck/` is a Go symbolic executor for Goose code whose knowledge of the
program comes entirely from a **table of rules**: Hoare triples, each linked
to a lemma that is already proved in Rocq. It establishes a function's
specification by running on real hardware; Rocq then trusts the run through
one generated axiom per function, which records exactly the bytes the checker
consumed.

The first client is the raft proof (`new/proof/go_etcd_io/raft/`): the
`wp_raft_load_*` / `wp_raft_store_*` accessor lemmas of
`election_proof/inv_raft_phys.v`, the callees' postulated specs, and the pure
steps `wp_auto` takes are rows of `new/proof/go_etcd_io/raft/tcheck/raft.tbl`,
and `becomeFollower` is established from one observed run, as a drop-in
module of type `BECOMEFOLLOWER`.

## Pieces

```
tcheck/                    the checker (Goose-translated: no imports)
  syntax.go parse.go       its input, and the byte format it reads
  term.go exec.go check.go matching, symbolic execution, well-formedness
gocheck/tcheck/            the frontend (not translated, not trusted)
  table.go sexp.go         table files
  goose.go                 reads a function out of Goose's Rocq output
  ser.go rocq.go main.go   serialization, Rocq output, the command
  observe.sh               recheck and regenerate every observation
new/tcheck/
  syntax.v                 the input in Gallina, and [ser_input]
  denote.v                 what an input means ([input_holds])
  observe.v                [observed_run], and the axiom [check_adequate]
  link.v                   tactics for linking rules to lemmas
new/proof/go_etcd_io/raft/tcheck/
  raft.tbl                 the raft table (hand-written)
  table_raft.v             its syntax and denotation (generated)
  link_table_raft.v        each rule proved from its lemma (hand-written)
  observed_raft__becomeFollower.v   one run (generated)
  proof_raft__becomeFollower.v      BECOMEFOLLOWER from that run (hand-written)
```

## What is trusted

Reading `new/tcheck/observe.v` once is the whole audit:

- **`check_adequate`** (an `Axiom`): if `tcheck.Check` returns `true` on
  `ser_input i`, then `input_holds i`. This is the checker's soundness and
  **is not proved yet**; it is stated against the Goose translation of
  `tcheck.Check` (`new/code/github_com/mit_pdos/perennial/tcheck.v`), so it
  can be proved the way `new/checker/` proved `check_sound` for `checker/`.
- **One observation per function**: `Axiom f_check_run : observed_run "<bytes>"%go`,
  generated, whose bytes are verbatim what the Go run read.
  `bash gocheck/tcheck/observe.sh` reruns `tcheck.Check` on those bytes,
  regenerates every observation file from scratch (reifying the code and
  running the checker again), and fails unless the output is identical.

Not trusted: the frontend. The function's code is checked to be Goose's by
`reflexivity`; every rule is proved from a lemma (so a mis-transcribed rule
fails to link); the bytes are checked to be `ser_input` of the Gallina input
by `vm_compute`; and the final specification is stated by hand (it is the
`BECOMEFOLLOWER` module type itself).

## The table

A table (`raft.tbl`) declares user **sorts** (Gallina types), **symbols**
(Gallina functions, including the code's constants: `GoInstruction`s, Go
types, literals), **predicates** (`iProp`s, some `persistent`), **rules**
(`∀ vars, {{{ pre }}} lhs {{{ ∃ ex, RET ret; post }}}`, where `lhs` is an
application of values) and **facts** (equations, used left to right). Each
declaration carries its denotation in backquotes, e.g.

```
(sym fld_step (loc) loc `λ r : loc, r.[raft.raft.t, "step"]`)
(pred phys (cfgset loc w64 nstate) `own_raft_phys`)
(rule store_step (vars (cfg cfgset) (r loc) (id w64) (s nstate) (f func))
  (lhs (app k_store_stepFunc (pair (val_loc (fld_step r)) (val_func f))))
  (pre (phys cfg r id s)) (ret unit) (post (phys cfg r id (set_stepfn s f))))
```

`rule_valid` of a rule computes (`rule_start`, `link.v`) to the lemma's own
statement, so most links are one line:

```coq
Lemma raft_rule_store_step_ok : rule_valid raft_den raft_rule_store_step.
Proof. rule_start raft_unfold. apply wp_raft_store_step. Qed.
```

`cfg` is a parameter of every rule, `is_pkg_init raft` is a persistent
predicate in the precondition of the rules that need it, and there is one
table for the package. An observation records only the rules and facts its
run used, so a proof links just those: shared rules from
`link_table_raft.v`, rules for callees from its own postulates.

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

## Use

```
go run ./gocheck/tcheck -table T.tbl -gen-table table_T.v \
    -table-file table_T.v -func NAME -observe observed_NAME.v
bash gocheck/tcheck/observe.sh            # recheck everything
go run ./gocheck/tcheck -verify observed_NAME.v
```

When the code uses a constant the table does not declare, the tool prints
the declarations to add. When no rule applies, it prints the stuck
application with the table's names, e.g.

```
checker.Check: false -- no rule applies to
  (app (val_func fn_traceBecomeFollower) (val_loc ?1))
```
