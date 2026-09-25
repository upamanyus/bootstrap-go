# rocqgoal: Rocq goals, reified in Go

The first half of a generic way to hand a Rocq proof state to a Go checker
without writing a reifier in Ltac for each thing the checker understands:

1. **Export (Rocq, generic).** `new/proof/rocqgoal/export.v` prints the focused
   goal (the Rocq context and the conclusion) as an S-expression over kernel
   terms, naming every constant, inductive and constructor by its full kernel
   path. It knows nothing about Iris, GooseLang or Perennial and never needs to
   change when the checker learns something new. The format is documented at
   the top of that file.
2. **Reify (Go, untrusted).** This package parses the export (`Parse`), prints
   it back byte for byte (`Goal.String`), and recognizes structure by name:
   an Iris proof mode goal and its two contexts (`Goal.IPM`), typed points-to
   facts (`AsPointsTo`), a WP (`AsWP`), Stdlib strings and positives.
   Everything else is a plain `Term` the checker can match on, or treat as an
   opaque atom.

Not here yet: the way back. The plan is for Go to return the syntax it built,
as a primitive string that a Gallina decoder turns into a term, with atoms
given as positions in the exported tree, and for Rocq to check by one kernel
conversion that the syntax denotes the goal. That conversion is the only
trusted step, so nothing in this package has to be right for a proof to be
sound: a wrong reification makes the check fail.

## Use

In a proof, `ltac2:(print_goal ())` prints the export of the focused goal on
a line of its own (`report_goal "tag"` prints only its size, `dump_goal "tag"`
a `== tag` line and then the export):

```coq
From New.proof.rocqgoal Require Import export.
...
  wp_start as "_". wp_auto.
  ltac2:(print_goal ()).
```

Then, from the repository root, to see what this package makes of it:

```
go run ./gocheck/rocqgoal/cmd/rocqgoal -time FILE     # or the export on stdin
```

For the goal of `wp_Median3` after `wp_auto`
(`testdata/median3_wp_auto.sexp`) that prints the Rocq context, then

```
----------------------------------□
_1 : (is_pkg_init (uPredI (iResUR Σ)) examples (IsPkgInit_instance_0 Σ))
----------------------------------∗
HΦ : ((uPredI (iResUR Σ)).(bi_forall) w64 λ r, ...
x : x_ptr ↦{(DfracOwn (pos_to_Qp xH))} a   (typed_pointsto at w64)
y : y_ptr ↦{(DfracOwn (pos_to_Qp xH))} b   (typed_pointsto at w64)
z : z_ptr ↦{(DfracOwn (pos_to_Qp xH))} c   (typed_pointsto at w64)
----------------------------------
WP (App ext (Val ext (exception_do ext)) ... {{ Φ }}
```

## Tests

`go test ./gocheck/rocqgoal/` runs on the exports in `testdata/`, of the
goals in `new/proof/rocqgoal/examples/` (small goals that use every node of
the format, and two states of the `wp_Median3` proof). Those examples are
built with the rest of the tree and report only the size of each export;
`bash gocheck/rocqgoal/testdata/regen.sh` recompiles copies of them that print
the exports in full and rewrites `testdata/`. Rerun it when the format or the
examples change.

## Cost

Measured on this machine (Rocq 9.4+alpha) when the design was explored:

| goal | export (Ltac2) | size | parse + recognize (Go) |
|---|---|---|---|
| `wp_Median3` after `wp_auto` | 0.09 s | 76 KB | 5 ms |
| 50 points-to facts | 0.10 s | 66 KB | |
| 200 points-to facts | 0.27 s | 200 KB | |
| 800 points-to facts | 1.04 s | 780 KB | |

The export is linear in the size of the goal. For comparison, the hand-written
Ltac reifier of `wp_symex` (`new/proof/symex/tactic.v`) takes 2.7 s on the
heap of 50 points-to facts, 65.6 s on 200, and did not finish on 800 within
the 900 s the run was given.

The export is a tree, so implicit arguments the kernel shares are printed once
per occurrence (the `wp_Median3` goal repeats `uPredI (iResUR Σ)` 57 times).
A DAG format would need an exporter written as an OCaml plugin; Ltac2 has no
hash table on terms.
