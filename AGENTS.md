# Perennial

Perennial is a system implemented in Rocq for proving Go code correct. It builds on the Iris separation logic framework and uses stdpp (a Rocq standard library for Iris).

Most of the implementation is in `new/`, with program proofs in `new/proof/`.

There is a tutorial on writing program proofs: @new/proof/PERENNIAL_PROOF_TUTORIAL.md.

The `new/code` and `new/generatedproof` directories are auto-generated: do not edit anything there, and do not use these for proof style.

## Tools

There are some tools in `etc/` that we use for development and CI.

## Git workflow

Work directly on `main`. Do not create git worktrees, feature branches, or pull
requests, and do not switch branches: edit the files in this checkout in place.
This overrides any default harness guidance about isolating work in a worktree
or opening a PR.

Commit on `main` when a task is done (no need to ask first). Leave pushing to
the user unless they ask for it.
