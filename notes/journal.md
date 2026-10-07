# Journal

Append-only, newest last.

## 2026-10-07 — the Lean port

- Created orphan branch `lean`: the Go checkers (`checker/`, `tcheck/`,
  `gocheck/`) from `main` under module `github.com/upamanyus/bootstrap-go`, a
  Lake project depending on Perennial's Lean port and on the Lean raft
  election proof, and Goose's Lean output (`etc/goose.sh` → `Generated/`).
  Why each of these is so: [decisions.md](decisions.md).
- Ported the Rocq side with parallel agents, one per area: the checker's
  foundation (Defs … Prelude), its exec, match/verify and sorts/parse/pre
  chains, its top layer (Check, `check_sound`, adequacy on a new
  `goose_adequacy_heap`), the hand-written and observed example proofs, and
  all of tcheck including the frontend (it now reads Goose's Lean output and
  emits Lean). How a Rocq proof maps to Lean here, and what tripped the port:
  [checker-port.md](checker-port.md).
- Goose's Lean backend nests `;;;` differently from the Rocq backend (the
  final `return:` of a function sits outside its lets). The checker does not
  care, and `gocheck/translate` reads the same Goose AST that the Lean
  printer prints, so `func_val` of the frontend's input is Goose's `impl` by
  `rfl`; tcheck's observed bytes do differ from `main`'s (6735 bytes).
- Timings (this machine, dependencies built, `lake env lean`): hand-written
  Median3 proof 5.8–6.2 s, observed Median3 3.8–4.0 s, tcheck's observation
  file 7.7 s (5.1 s of it the kernel checking the bytes), its proof 2.8 s;
  a checker run 0.04 s.

## 2026-10-07 — one checkout

- The `lean` branch and both dependency pins (Perennial `8c75a3dd4`,
  etcd-grove `51d6df02d`) are pushed. `~/bootstrap-go` is now the `lean`
  checkout (the temporary `~/bootstrap-go-lean` clone is gone; its
  populated `.lake/` was moved here). The Rocq sources are read with
  `git show main:<path>`.

## 2026-10-07 — scripts need the Lake dependencies

- On a fresh clone, `gocheck/demo.sh` failed in `go build` with "replacement
  directory ./.lake/packages/perennial does not exist": go.mod's replace
  target only exists after Lake fetches the dependencies. `demo.sh`, both
  `observe.sh` and `etc/goose.sh` now check for it up front and say to run
  `lake build` first.
- etcd-grove is private, so `lakefile.toml` and `lake-manifest.json` now
  fetch it over ssh (`git@github.com:upamanyus/etcd-grove`); Perennial and
  the upstream packages stay on https. An existing clone keeps its old
  remote: `git -C .lake/packages/etcdGrove remote set-url origin
  git@github.com:upamanyus/etcd-grove`, or Lake re-clones it at the next
  pin change.

## 2026-10-07 — specs in Iris Unicode notation only

- gocheck's spec language no longer accepts ASCII spellings of Iris
  notation (`|->`, `*`, `[…]`, `\/`, `exists`); write `↦ ∗ ⌜…⌝ ∨ ∃`. The
  `-ascii` print flag is gone too. Term operators keep their Go spellings
  (`<=`, `!=`, `!`) alongside `≤ ≠ ¬`. `TestNoASCII` checks the rejection;
  the demo has 12 cases (the all-ASCII Swap run was dropped).

## 2026-10-07 — a Lean-native checker

- `Checkers/Native/`: `lcheck`, the checker's algorithm as Lean functions, and
  `lcheck_sound` (a `true` answer gives `triple_holds`). The proof reuses the
  Go proof's semantic layer unchanged; only the induction over the Lean
  functions is new (`Sound.lean`, ~700 lines; it compiled in a few rounds).
- Lessons: the pure lemmas of `Checkers/Checker/` take an unused
  `[FfiSyntax]` (Lean 4 always includes an instance-implicit section variable
  whose type has no dependencies), and `penv_below` even takes an FFI, so
  `lcheck_sound` introduces `triple_holds`'s instances before calling them.
  `(h : ∃ …).2` elaborates but the kernel rejects it ("invalid projection");
  destructure instead. `nomatch h, x` parses as `nomatch` on two
  discriminants.
- `matchTerm` is not structurally recursive in Go (the `TResult` case
  recurses on the return term); `mt_core` takes the `TResult` case as a
  parameter and `mt` instantiates it with a copy that rejects `TResult`.
- `gocheck/specs.sh` now holds the six demo specifications, sourced by
  `demo.sh`, `observe.sh` and the new `native.sh` (inputs) and
  `native_bench.sh` (timings). Results are in `Checkers/Native/README.md`:
  `native_decide` evaluation 1-8 ms, kernel 0.12-1.3 s, hand-written proofs
  0.4-4.0 s, gocheck ~0.04 s.
- `native_decide` in this Lean version adds an auxiliary axiom per use, not
  `Lean.ofReduceBool`; and under `lake build` it runs interpreted IR, since
  the library does not set `precompileModules`.

## 2026-10-07 — timing checker.Check alone

- `gocheck -time-check N` reports the mean of N calls of `checker.Check` on
  the built input; `native_bench.sh` shows it as the `Check` column. It is
  8-138 us per example (Median3 the largest), so gocheck's ~40 ms is process
  start plus loading and translating the Go package, and the compiled Go
  check is 50-150x faster than `lcheck` under `native_decide` (1-8 ms,
  interpreted IR). Numbers in `Checkers/Native/README.md`.

## 2026-10-07 — `lcheck` precompiled (`LCheck/`)

- Moved the 15 types and 43 functions `lcheck` depends on (found by walking
  the constants of `lcheck`'s definition) into `LCheck/{Syntax,Fns}.lean`,
  and `lcheck` into `LCheck/Check.lean`; each old location keeps a one-line
  pointer. `lake build` passed with no proof edits.
- First attempt imported `Perennial.Std.ByteString` (for `GoString`, `go!`):
  the build then made `libperennial_Perennial.so` (144 modules) plus Iris
  (277), Batteries (192) and Qq (14) shared libraries, because the LCheck
  library's `.so` needs `initialize_perennial_Perennial_Std_ByteString`. With
  the abbreviations written out, LCheck's `.so` needs only Lean's runtime, and
  the example modules load only it (`.setup.json` "plugins").
- `lake env lean` does not load the plugin; `--plugin=.lake/build/lib/libbootstrapGo_LCheck.so`
  does, as `lake build` does. `native_bench.sh` passes it and gained `interp`
  and `lcheck` (per-call) columns; `Check` is now in microseconds too.
- Results (README in Checkers/Native): compiled `lcheck` 7-115 us per call,
  about Go's `checker.Check` (8-143 us); interpreted 130-2300 us. In a proof,
  `native_decide` evaluation is 0.3-1.6 ms precompiled vs 0.6-6 ms
  interpreted — below wall-clock noise; the rest of the proof file dominates.

## 2026-10-07 — tcheck by reflection

- `ltcheck` (LCheck/TCheck/Check.lean) and `ltcheck_sound`
  (Checkers/TCheck/Reflect/: Terms, Code, Heap, Rules, Eval, Sound; ~2,600
  lines, no `sorry`, Lean's three axioms). The tcheck input types moved from
  Checkers/TCheck/Syntax.lean (which keeps `ser_input`) to
  LCheck/TCheck/Syntax.lean, so the checker is precompiled with `LCheck`.
- Raft: Checkers/TCheck/Raft/Reflect/raft__becomeFollower.lean proves
  `raft.becomeFollower.spec` with `decide +kernel` (axioms: the observed
  proof's minus `check_adequate` and `becomeFollower_check_run`).
- Lessons. Lean derives no `DecidableEq` for the nested `tterm`; a Bool `teq`
  with a soundness lemma is all the checker needs. Proofs are continuation-
  passing over evaluation contexts (`fill K`), which composes the App/Pair/
  let/exception cases and the spine search the same way. Making the
  continuation `kont` an `abbrev` lets the proof mode see through it without
  unfolding the outer one. `Language.ofVal`'s coercion in `wp_bind` is not
  syntactically `Val`: give `iapply` the postcondition explicitly. A section
  variable used only in a proof needs `include`.
- `gocheck/tcheck -verify OBS -time-check N` times `tcheck.Check` (with
  parsing) and `tcheck.Run`; `gocheck/tcheck/reflect_bench.sh` reports
  observed 5.1 s / kernel 1.5 s / native 0.15 s for `input_holds`, and 0.2 ms
  per check compiled (Lean and Go alike), 3 ms interpreted.

## 2026-10-07 — tcheck against the hand-written becomeFollower proof

- etcdGrove's `lean` branch (d96cf39f8, past our pin 51d6df02d) has
  `Proof/raft__becomeFollower.lean`, ~20 tactic lines over the accessor
  lemmas; the specs are unchanged since the pin and it compiles against it.
  Seconds minus imports, median of 5: hand-written 2.24; observed tcheck 5.87
  (Observed 5.17 + Proof 0.70); reflective tcheck 1.47 (kernel) or 0.35
  (`native_decide`). Per table: TableRaft 1.66 + LinkTableRaft 1.04.
- A trap when timing: ascribing `raft.becomeFollower.spec` directly to the
  `spec_rule_valid` term took 5.9 s of elaboration (unification through the
  denotation with metavariables); stating `rule_valid ... raft_rule_becomeFollower`
  first and converting, as both tcheck proofs do, takes 0.2 s.
