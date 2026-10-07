#!/usr/bin/env bash
# Times the Lean-native checker (Checkers/Native/) on the six specifications
# of gocheck/specs.sh, against the hand-written proofs
# (Checkers/Checker/Examples/) and against the Go checker.
#
# Columns, in seconds of wall clock (median of $RUNS runs):
#
#   hand     the hand-written proof file, minus loading its imports
#   file     Checkers/Native/Examples/<F>.lean -- the gocheck input's function
#            checked against Goose's by rfl, and the triple by lcheck_sound
#            and native_decide (for Median3 also wp_Median3) -- minus loading
#            its imports
#   native   just the triple, by lcheck_sound and native_decide
#   interp   the same, with lcheck interpreted instead of precompiled
#   kernel   just the triple, by lcheck_sound and `decide +kernel` (no axiom
#            beyond Lean's)
#   gocheck  one run of the built gocheck binary on the same specification
#   Check    checker.Check alone, in microseconds: the mean of $CHECK_N calls
#            on gocheck's input (gocheck -time-check), with no process start,
#            Go package loading or translation
#   lcheck   lcheck alone, precompiled, in microseconds: the mean of $CHECK_N
#            calls on the same input
#
# `lcheck` is in the precompiled library LCheck (lakefile.toml), which
# `lake build` loads as a plugin when it elaborates a file that imports it;
# the Lean columns other than `interp` pass the same plugin to `lean`.
#
# Run from the repository root, after lake build:
#   bash gocheck/native_bench.sh
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2
. gocheck/specs.sh

RUNS=${RUNS:-3}
CHECK_N=${CHECK_N:-10000}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
go build -o "$tmp/gocheck" ./gocheck || exit 2
lake build LCheck Checkers.Native.Sound Checkers.Native.Inputs Checkers.Checker.Examples.ExamplesInit \
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

# lean_cost FILE [LEAN-FLAGS...] -- median time of FILE minus that of a file
# with its imports only
lean_cost() {
	local file=$1 total imports
	shift
	grep '^import ' "$file" >"$tmp/Imports.lean"
	total=$(run_med lake env lean "$@" "$file") || { echo fail; return; }
	imports=$(run_med lake env lean "$@" "$tmp/Imports.lean") || { echo fail; return; }
	awk -v a="$total" -v b="$imports" 'BEGIN { d = (a - b) / 1e6; if (d < 0) d = 0; printf "%.2f", d }'
}

secs() { awk -v us="$1" 'BEGIN { printf "%.3f", us / 1e6 }'; }

row() { printf '%-10s %6s %6s %6s %6s %6s %8s %7s %7s\n' "$@"; }

# bench FUNC NAME GOCHECK-ARGS...
bench() {
	local fn=$1 name=$2
	shift 2
	local hand file native interp kernel go check lc
	hand=$(lean_cost "Checkers/Checker/Examples/$fn.lean")
	file=$(lean_cost "Checkers/Native/Examples/$fn.lean" "$PLUGIN")
	triple "$name" native_decide >"$tmp/Native.lean"
	native=$(lean_cost "$tmp/Native.lean" "$PLUGIN")
	interp=$(lean_cost "$tmp/Native.lean")
	triple "$name" "decide +kernel" >"$tmp/Kernel.lean"
	kernel=$(lean_cost "$tmp/Kernel.lean" "$PLUGIN")
	go=$(run_med "$tmp/gocheck" -pkg ./checker/examples "$@" "$fn") && go=$(secs "$go") || go=fail
	check=$("$tmp/gocheck" -pkg ./checker/examples "$@" -time-check "$CHECK_N" "$fn" |
		sed -n 's/^checker.Check: true, \([0-9.]*\) us\/call.*/\1/p')
	[ -n "$check" ] && check=$(awk -v us="$check" 'BEGIN { printf "%.1f", us }') || check=fail
	lc=$(sed -n "s/^$fn: true, \([0-9.]*\) us\/call/\1/p" "$tmp/lcheck.txt")
	[ -n "$lc" ] && lc=$(awk -v us="$lc" 'BEGIN { printf "%.1f", us }') || lc=fail
	row "$fn" "$hand" "$file" "$native" "$interp" "$kernel" "$go" "$check" "$lc"
}

# lcheck alone: the mean of $CHECK_N calls per input, precompiled. The
# argument `vs` depends on the loop index (it is always `vars`) so that the
# call is not hoisted out of the loop.
cat >"$tmp/Loop.lean" <<'LEAN'
import LCheck
import Checkers.Native.Inputs
open Perennial Checker Native
def benchCheck (name : String) (n : Nat) (f : cfunc) (vars : List sort) (pre post : cassn) :
    IO Unit := do
  let t0 ← IO.monoNanosNow
  let mut ok := true
  for i in [0:n] do
    let vs := if i == n + 1 then [] else vars
    ok := ok && lcheck f vs pre post
  let t1 ← IO.monoNanosNow
  IO.println s!"{name}: {ok}, {(Float.ofNat (t1 - t0)) / (Float.ofNat n) / 1000.0} us/call"
#eval show IO Unit from do
  let n := (← IO.getEnv "CHECK_N").bind String.toNat? |>.getD 10000
  benchCheck "Double" n double_func double_vars double_pre double_post
  benchCheck "Max" n max_func max_vars max_pre max_post
  benchCheck "Swap" n swap_func swap_vars swap_pre swap_post
  benchCheck "Abs" n abs_func abs_vars abs_pre abs_post
  benchCheck "CondStore" n condStore_func condStore_vars condStore_pre condStore_post
  benchCheck "Median3" n median3_func median3_vars median3_pre median3_post
LEAN
CHECK_N=$CHECK_N lake env lean "$PLUGIN" "$tmp/Loop.lean" >"$tmp/lcheck.txt" 2>&1

# triple NAME TACTIC -- a file proving NAME's triple by lcheck_sound and TACTIC
triple() {
	cat <<LEAN
import Checkers.Native.Sound
import Checkers.Native.Inputs
open Perennial Checker Native
theorem ${1}_triple' : triple_holds ${1}_func ${1}_vars ${1}_pre ${1}_post :=
  lcheck_sound _ _ _ _ (by $2)
LEAN
}

lean --version 2>/dev/null | head -1
echo "seconds (Check, lcheck: microseconds), median of $RUNS runs; Lean columns exclude loading imports"
row function hand file native interp kernel gocheck "Check" "lcheck"
bench Double double -pre "$DOUBLE_PRE" -post "$DOUBLE_POST"
bench Max max -post "$MAX_POST"
bench Swap swap -pre "$SWAP_PRE" -post "$SWAP_POST"
bench Abs abs -post "$ABS_POST"
bench CondStore condStore -pre "$CONDSTORE_PRE" -post "$CONDSTORE_POST"
bench Median3 median3 -post "$MEDIAN_POST"
