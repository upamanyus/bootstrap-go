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
