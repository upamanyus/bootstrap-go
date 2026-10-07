#!/usr/bin/env bash
# Times the Lean version of the table-driven checker (`ltcheck`,
# LCheck/TCheck/Check.lean, proved sound by `ltcheck_sound`) on raft's
# becomeFollower, against the observed run of the Go checker.
#
# Each way of obtaining `input_holds becomeFollower_input`:
#
#   observed  Checkers/TCheck/Raft/Observed/raft__becomeFollower.lean: the
#             observation axiom, the kernel's check that its bytes are
#             `ser_input` of the input, and the `rfl` fidelity check
#   kernel    `ltcheck_sound _ (by decide +kernel)`: no axiom beyond Lean's
#   native    `ltcheck_sound _ (by native_decide)`, `ltcheck` precompiled
#             (the LCheck plugin, as `lake build` loads it)
#   interp    the same, `ltcheck` interpreted (no plugin)
#
# in seconds of wall clock, median of $RUNS runs, minus loading the file's
# imports; then Lean's profiler on the same checks (the kernel's type
# checking, `native_decide`'s evaluation), and the cost of one call of each
# checker on the same input, the mean of $CHECK_N calls: `tcheck.Check`
# (parse and run) and `tcheck.Run` (run only) of the Go checker (`gocheck/tcheck
# -verify -time-check`), `ltcheck` compiled and interpreted.
#
# Run from the repository root, after lake build: bash gocheck/tcheck/reflect_bench.sh
set -uo pipefail

cd "$(dirname "$0")/../.." || exit 2

RUNS=${RUNS:-3}
CHECK_N=${CHECK_N:-10000}
OBS=Checkers/TCheck/Raft/Observed/raft__becomeFollower.lean
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
go build -o "$tmp/tcheck" ./gocheck/tcheck || exit 2
lake build LCheck Checkers.TCheck.Reflect.Sound Checkers.TCheck.Raft.Proof.raft__becomeFollower \
	>/dev/null || { echo "lake build failed" >&2; exit 2; }
PLUGIN=--plugin=.lake/build/lib/libbootstrapGo_LCheck.so

now_us() { local t=${EPOCHREALTIME/[.,]/}; printf '%s' "$t"; }

# run_med CMD... -- median wall clock of $RUNS runs, in microseconds; fails if CMD does
run_med() {
	local ts=() i t0 t1
	for ((i = 0; i < RUNS; i++)); do
		t0=$(now_us)
		"$@" >/dev/null 2>&1 || return 1
		t1=$(now_us)
		ts+=($((t1 - t0)))
	done
	printf '%s\n' "${ts[@]}" | sort -n | sed -n "$(((RUNS + 1) / 2))p"
}

# lean_cost FILE [LEAN-FLAGS...] -- median time of FILE minus that of its imports alone
lean_cost() {
	local file=$1 total imports
	shift
	grep '^import ' "$file" >"$tmp/Imports.lean"
	total=$(run_med lake env lean "$@" "$file") || { echo fail; return; }
	imports=$(run_med lake env lean "$@" "$tmp/Imports.lean") || { echo fail; return; }
	awk -v a="$total" -v b="$imports" 'BEGIN { d = (a - b) / 1e6; if (d < 0) d = 0; printf "%.2f", d }'
}

# holds TACTIC -- a file proving input_holds by ltcheck_sound and TACTIC
holds() {
	cat <<LEAN
import Checkers.TCheck.Reflect.Sound
import Checkers.TCheck.Raft.Observed.raft__becomeFollower
open Perennial TCheck
set_option maxRecDepth 100000 in
theorem holds' : input_holds becomeFollower_input := LC.ltcheck_sound _ (by $1)
LEAN
}

lean --version 2>/dev/null | head -1
echo
echo "input_holds becomeFollower_input: seconds of wall clock, median of $RUNS runs, minus imports"
printf '  %-9s %s\n' observed "$(lean_cost "$OBS")"
holds "decide +kernel" >"$tmp/Kernel.lean"
printf '  %-9s %s\n' kernel "$(lean_cost "$tmp/Kernel.lean" "$PLUGIN")"
holds native_decide >"$tmp/Native.lean"
printf '  %-9s %s\n' native "$(lean_cost "$tmp/Native.lean" "$PLUGIN")"
printf '  %-9s %s\n' interp "$(lean_cost "$tmp/Native.lean")"

echo
echo "Lean's profiler (one run; cumulative over the file):"
prof() { # prof FILE FIELD [LEAN-FLAGS...] -- the profiler's cumulative FIELD time
	local f=$1 field=$2
	shift 2
	{ grep '^import ' "$f"; echo 'set_option profiler true'; grep -v '^import ' "$f"; } >"$tmp/Prof.lean"
	lake env lean "$@" "$tmp/Prof.lean" 2>&1 | sed -n "s/^[[:space:]]*$field \([0-9.]*[mµu]*s\)$/\1/p" | tail -1
}
printf '  %-9s type checking %s (of which the bytes = ser_input check is most)\n' observed "$(prof "$OBS" "type checking")"
printf '  %-9s type checking %s\n' kernel "$(prof "$tmp/Kernel.lean" "type checking" "$PLUGIN")"
printf '  %-9s evaluation %s\n' native "$(prof "$tmp/Native.lean" interpretation "$PLUGIN")"
printf '  %-9s evaluation %s\n' interp "$(prof "$tmp/Native.lean" interpretation)"

echo
echo "One call of the checker on becomeFollower's input, microseconds, mean of $CHECK_N calls:"
"$tmp/tcheck" -verify "$OBS" -time-check "$CHECK_N" | sed -n 's/^tcheck.Check: \([0-9.]*\) us\/call, tcheck.Run: \([0-9.]*\) us\/call.*/  Go        tcheck.Check \1, tcheck.Run \2/p'
cat >"$tmp/Loop.lean" <<'LEAN'
import LCheck
import Checkers.TCheck.Raft.Observed.raft__becomeFollower
open Perennial TCheck
#eval show IO Unit from do
  let n := (← IO.getEnv "CHECK_N").bind String.toNat? |>.getD 10000
  let i := becomeFollower_input
  let t0 ← IO.monoNanosNow
  let mut ok := true
  for k in [0:n] do
    -- depends on the loop index (never changing the input), so the call is not hoisted
    let i' := if k == n + 1 then { i with in_facts := [] } else i
    ok := ok && ltcheck i'
  let t1 ← IO.monoNanosNow
  IO.println s!"{ok} {(Float.ofNat (t1 - t0)) / (Float.ofNat n) / 1000.0}"
LEAN
lc=$(CHECK_N=$CHECK_N lake env lean "$PLUGIN" "$tmp/Loop.lean" 2>&1 | tail -1)
li=$(CHECK_N=$((CHECK_N / 10)) lake env lean "$tmp/Loop.lean" 2>&1 | tail -1)
printf '  %-9s compiled %s, interpreted %s (%s calls)\n' ltcheck "$(echo "$lc" | awk '{printf "%.1f", $2}')" \
	"$(echo "$li" | awk '{printf "%.1f", $2}')" "$((CHECK_N / 10))"
