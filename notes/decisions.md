# Decisions (Lean branch)

Newest last. The checkers' own design is recorded on `main`
(`git show main:checker/README.md`, `main:gocheck/tcheck/README.md`,
`main:checker/SOUNDNESS_PLAN.md`).

---

## A branch of its own, with Perennial as a dependency

**2026-10-07 · accepted**

`main` is a fork of Perennial with the checkers and the etcd proofs added to
it. The Lean port is an orphan branch `lean` holding only this repository's
own work (the Go checkers, their frontends, and their Lean development) and
depends on Perennial's Lean port through Lake (`lakefile.toml`,
`lake-manifest.json`). Goose too comes from that dependency: `etc/goose.sh`
installs it from `.lake/packages/perennial/goose`, and `go.mod` replaces
`github.com/mit-pdos/perennial` with `.lake/packages/perennial` so that
`gocheck/translate` reads the same Goose AST that produced `Generated/`.

**Pin.** Perennial is pinned at `8c75a3dd4` of its `lean` branch, the head
of that branch in the local checkout on 2026-10-07: five commits (phases 1,
B1, B2, B3a, B3b of the Lean naming migration) ahead of what GitHub had
(`f3b8ef80f`). Those commits rename most of the framework and of the
generated code; writing against the pre-rename names would have meant
migrating everything as soon as they land, and etcdGrove (below) is already
on them. Until they are pushed, `lake` can only resolve the dependency from
an already-populated `.lake/packages`.

**Rejected — pin GitHub's `f3b8ef80f`.** Resolvable today, but every name
written here would be stale on the next push of Perennial's `lean`.

## tcheck's raft client uses the Lean election proof as a dependency

**2026-10-07 · accepted**

tcheck's rules are existing raft lemmas (the `inv_raft_phys` accessors and
callee specs). On `main` those come from `election_proof/`, copied in with
the rest of etcd-grove. Here they come from the Lean port of that proof,
`upamanyus/etcd-grove` branch `lean`, a second Lake dependency (`etcdGrove`,
pinned at `51d6df02d`), and the final theorem proves that development's own
`raft.becomeFollower.spec`. `raft.tbl` was rewritten against its lemmas
(`NState`, `ownRaftPhys`, `PRole`, `GMap w64 Progress`), which differ in
detail from the Rocq version `main`'s table was written for. Like Perennial's
pin, `51d6df02d` is not on GitHub yet.

**Rejected — copy the ~20 needed files of the Lean election proof here.**
Two diverging copies of the same proof, and contrary to the point of using
dependencies.

## Goose's Lean output lives under the module root `Generated.`

**2026-10-07 · accepted**

Goose's Lean backend names modules `Perennial.Code.<pkg>`; a module under
`Perennial.` is resolved to the Perennial package, so a file of this
repository there is not found. `etc/goose.sh` moves the output to
`Generated/{Code,GeneratedProof}/…` and rewrites the imports; the Lean
namespaces inside (`Perennial.github_com.upamanyus.bootstrap_go.checker`, …)
are unchanged. The Go module path is `github.com/upamanyus/bootstrap-go`
(on `main` it was Perennial's own, `github.com/mit-pdos/perennial`).

## Not ported

**2026-10-07 · accepted**

`new/proof/symex/` (`wp_symex`, a reflective symbolic executor written in
Gallina — not one of the checkers), the `reflect/` example proofs that use it,
and the Rocq goal exporter (`new/proof/rocqgoal/`, `gocheck/rocqgoal/`), which
is specific to Rocq.

## A Lean-native checker, run by `native_decide`

**2026-10-07 · accepted**

`Checkers/Native/` (not a port of anything on `main`) writes the checker's
algorithm as Lean functions (`lcheck`) and proves them sound
(`lcheck_sound : lcheck … = true → triple_holds …`), reusing the Go proof's
semantic layer (`exec_sound_*`, `match_path_sat`, `binders_interp_step`, …)
instead of observing a Go run. The six demo examples use `native_decide`, at
the user's request (to see the checker's cost under compiled evaluation).
This is the one exception to porting.md's "no `native_decide`": it is
confined to `Checkers/Native/Examples/`, each use adds its own axiom
(`…._native.native_decide.ax_1_1`), and the same triples also go through
`decide +kernel` with no axiom (`gocheck/native_bench.sh` times both).

**Rejected — port `wp_symex` (`main`'s reflective executor).** It is a
different algorithm from the checker's, with its own soundness proof to
port; writing the checker's own algorithm in Lean reuses the semantic layer
already proved, and keeps one algorithm.
