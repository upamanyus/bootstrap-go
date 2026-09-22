# Checker soundness proof — working notes

Running log of the proof of `check_sound` (see `SOUNDNESS_PLAN.md` in
`checker/` for the design). Newest entries at the bottom.

## Layout

    new/checker/defs.v         definitions the statement is over (was the top
                               of soundness.v; split out so that the proof
                               files can depend on them without depending on
                               the statement file)
    new/checker/soundness.v    `Axiom check_sound`, unchanged text, now
                               `Export`ing defs.v

## Build

Everything is behind the opam switch `perennial` (Rocq 9.4+alpha):

    eval $(opam env --switch=perennial --set-switch)
    make -j7 TIMED=false new/checker/<file>.vos     # fast, no proof checking
    make -j7 TIMED=false new/checker/<file>.vok     # checks proofs against .vos deps

`~/rocq-warm` keeps a warm `rocq repl` per file for the edit loop:

    rocq-warm check new/checker/<file>.v

## Log

### 2026-09-22

- Split `soundness.v` into `defs.v` (definitions) + `soundness.v` (the axiom).
  The axiom's text is character-identical to before, so the statement cannot
  have drifted. Nothing else in the tree required `soundness.v`.
