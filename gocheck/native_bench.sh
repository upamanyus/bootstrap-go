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
#   kernel   just the triple, by lcheck_sound and `decide +kernel` (no axiom
#            beyond Lean's)
#   gocheck  one run of the built gocheck binary on the same specification
#
# Run from the repository root, after lake build:
#   bash gocheck/native_bench.sh
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2
. gocheck/specs.sh

RUNS=${RUNS:-3}
tmp=$(mktemp -d)
trap 'rm -rf "$tmp"' EXIT
go build -o "$tmp/gocheck" ./gocheck || exit 2
lake build Checkers.Native.Sound Checkers.Native.Inputs Checkers.Checker.Examples.ExamplesInit \
	>/dev/null || { echo "lake build failed" >&2; exit 2; }

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

# lean_cost FILE -- median time of FILE minus that of a file with its imports only
lean_cost() {
	local file=$1 total imports
	grep '^import ' "$file" >"$tmp/Imports.lean"
	total=$(run_med lake env lean "$file") || { echo fail; return; }
	imports=$(run_med lake env lean "$tmp/Imports.lean") || { echo fail; return; }
	awk -v a="$total" -v b="$imports" 'BEGIN { d = (a - b) / 1e6; if (d < 0) d = 0; printf "%.2f", d }'
}

secs() { awk -v us="$1" 'BEGIN { printf "%.3f", us / 1e6 }'; }

row() { printf '%-10s %7s %7s %7s %7s %8s\n' "$@"; }

# bench FUNC NAME GOCHECK-ARGS...
bench() {
	local fn=$1 name=$2
	shift 2
	local hand file native kernel go
	hand=$(lean_cost "Checkers/Checker/Examples/$fn.lean")
	file=$(lean_cost "Checkers/Native/Examples/$fn.lean")
	triple "$name" native_decide >"$tmp/Native.lean"
	native=$(lean_cost "$tmp/Native.lean")
	triple "$name" "decide +kernel" >"$tmp/Kernel.lean"
	kernel=$(lean_cost "$tmp/Kernel.lean")
	go=$(run_med "$tmp/gocheck" -pkg ./checker/examples "$@" "$fn") && go=$(secs "$go") || go=fail
	row "$fn" "$hand" "$file" "$native" "$kernel" "$go"
}

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
echo "seconds, median of $RUNS runs; Lean columns exclude loading imports"
row function hand file native kernel gocheck
bench Double double -pre "$DOUBLE_PRE" -post "$DOUBLE_POST"
bench Max max -post "$MAX_POST"
bench Swap swap -pre "$SWAP_PRE" -post "$SWAP_POST"
bench Abs abs -post "$ABS_POST"
bench CondStore condStore -pre "$CONDSTORE_PRE" -post "$CONDSTORE_POST"
bench Median3 median3 -post "$MEDIAN_POST"
