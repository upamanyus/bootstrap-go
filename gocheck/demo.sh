#!/usr/bin/env bash
# Demo of the gocheck front end for the CSL symbolic-execution checker.
#
# Every case below runs gocheck on one of the functions in
# checker/examples/examples.go and asserts the exit code:
#
#   0  verified against the given postcondition (or the strongest
#      postcondition was printed, when no -post is given)
#   1  the checker rejected the program (unsafe) or the postcondition
#   2  a usage, parse, translation or sort error
#
# The last section re-checks the same six specifications the slow way, with
# the hand-written Lean proofs in Checkers/Checker/Examples/, and times each
# proof against the corresponding run of the checker.
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2

if [ ! -d .lake/packages/perennial ]; then
	echo "missing .lake/packages/perennial (go.mod's replacement for perennial):" >&2
	echo "run 'lake build' first, which fetches the Lake dependencies" >&2
	exit 2
fi

GOCHECK=${GOCHECK:-/tmp/gocheck}
echo "building $GOCHECK"
go build -o "$GOCHECK" ./gocheck || exit 2

PKG=./checker/examples
pass=0
fail=0

run() {
	local want=$1
	local name=$2
	shift 2
	echo
	echo "=============================================================="
	echo "# $name"
	echo "\$ gocheck $*"
	echo "--------------------------------------------------------------"
	"$GOCHECK" "$@"
	local got=$?
	if [ "$got" -eq "$want" ]; then
		echo "--> exit $got (as expected)"
		pass=$((pass + 1))
	else
		echo "--> exit $got, EXPECTED $want"
		fail=$((fail + 1))
	fi
}

# The specifications that both the checker and a Rocq proof establish. Each
# entry is the function name, the basename of its proof file, and then the
# gocheck arguments; compare() below uses all three.
DOUBLE_PRE='z |-> z0'
DOUBLE_POST='(⌜x == 0⌝ ∗ z ↦ 37 + 37) ∨ (⌜x != 0⌝ ∗ z ↦ x + x)'
MAX_POST='(⌜a <u b⌝ ∗ ⌜ret == b⌝) ∨ (⌜a >=u b⌝ ∗ ⌜ret == a⌝)'
SWAP_PRE='p |-> a ∗ q |-> b'
SWAP_POST='p ↦ b ∗ q ↦ a'
ABS_POST='(⌜x <s 0⌝ ∗ ⌜ret == -x⌝) ∨ (⌜x >=s 0⌝ ∗ ⌜ret == x⌝)'
CONDSTORE_PRE='p |-> v0'
CONDSTORE_POST='(⌜!flag⌝ ∗ p ↦ v0 ∗ ⌜ret == false⌝) ∨ (⌜flag⌝ ∗ p ↦ v ∗ ⌜ret == true⌝)'
# The checker has no arithmetic, so the median is stated path by path, with
# each path's conditions exactly as they print; the last two disjuncts are the
# two infeasible paths, whose conditions contradict.
MEDIAN_POST='(⌜b <u a⌝ ∗ ⌜c <u b⌝ ∗ ⌜ret == b⌝) ∨ (⌜b >=u a⌝ ∗ ⌜c >=u b⌝ ∗ ⌜ret == b⌝) ∨ (⌜c >=u b⌝ ∗ ⌜c <u a⌝ ∗ ⌜ret == c⌝) ∨ (⌜c >=u a⌝ ∗ ⌜c <u b⌝ ∗ ⌜ret == c⌝) ∨ (⌜b <u a⌝ ∗ ⌜c >=u a⌝ ∗ ⌜ret == a⌝) ∨ (⌜c <u a⌝ ∗ ⌜b >=u a⌝ ∗ ⌜ret == a⌝) ∨ (⌜b <u a⌝ ∗ ⌜a <u b⌝) ∨ (⌜b >=u a⌝ ∗ ⌜b <u a⌝)'

# --- Verified examples ------------------------------------------------------

run 0 "Double: heap write, arithmetic, control flow" \
	-pkg $PKG -pre "$DOUBLE_PRE" -post "$DOUBLE_POST" Double

run 0 "Max: unsigned comparison and two returns" \
	-pkg $PKG -post "$MAX_POST" Max

run 0 "Swap: two owned cells exchange their contents" \
	-pkg $PKG -pre "$SWAP_PRE" -post "$SWAP_POST" Swap

run 0 "Abs: signed comparison and a negated result" \
	-pkg $PKG -post "$ABS_POST" Abs

run 0 "CondStore: a boolean result and a conditional write" \
	-pkg $PKG -pre "$CONDSTORE_PRE" -post "$CONDSTORE_POST" CondStore

# The same two assertions in pure ASCII, printed in ASCII notation.
run 0 "Swap again, all ASCII (-ascii)" \
	-pkg $PKG -ascii -pre 'p |-> a * q |-> b' -post 'p |-> b * q |-> a' Swap

# A longer function: Median3 sorts three locals with a three-comparator
# sorting network and returns the middle one, 8 paths in all.
run 0 "Median3: a sorting network, eight paths, the median returned" \
	-pkg $PKG -post "$MEDIAN_POST" Median3

# --- Rejected inputs --------------------------------------------------------

run 1 "Swap without owning q: the load from q is unsafe" \
	-pkg $PKG -pre 'p |-> a' Swap

run 1 "Double against a postcondition it does not establish" \
	-pkg $PKG -pre 'z |-> z0' -post 'z ↦ 74' Double

run 1 "Median3 claiming the maximum, not the median, when c < b < a" \
	-pkg $PKG -post "${MEDIAN_POST/⌜c <u b⌝ ∗ ⌜ret == b⌝)/⌜c <u b⌝ ∗ ⌜ret == a⌝)}" \
	Median3

run 2 "Double against an ill-sorted postcondition" \
	-pkg $PKG -pre 'z |-> z0' -post '⌜x && z0⌝' Double

# --- Strongest postconditions, with no -post at all -------------------------

run 0 "Max: just print the strongest postcondition" -pkg $PKG Max

run 0 "Double: the translated GooseLang body too (-ast)" \
	-pkg $PKG -ast -pre 'z |-> z0' Double

echo
echo "=============================================================="
echo "$pass cases behaved as expected, $fail did not"

# --- The same specifications, checked by Lean -------------------------------
#
# For each function we re-check its hand-written proof (Checkers/Checker/
# Examples/<Name>.lean) with `lake env lean`, against already-built
# dependencies, the way an incremental `lake build` would, run the checker on
# the same specification, and report the wall-clock times.
#
# Most of a check is spent loading the proof's imports (the Perennial and Iris
# prelude), which says nothing about the proof itself, so we also time a file
# holding the same imports and nothing else, and report the difference.

PROOFS=Checkers/Checker/Examples
NCPU=$(nproc 2>/dev/null || echo 4)

# Microseconds since the epoch. $EPOCHREALTIME is a bash 5 builtin; it holds
# seconds and microseconds separated by the locale's decimal point.
now_us() {
	if [ -n "${EPOCHREALTIME:-}" ]; then
		local t=${EPOCHREALTIME/[.,]/}
		printf '%s' "$t"
	else
		python3 -c 'import time; print(int(time.time() * 1e6))'
	fi
}

secs() { awk -v us="$1" 'BEGIN { printf "%.2f", us / 1e6 }'; }
sub_secs() { awk -v a="$1" -v b="$2" 'BEGIN { d = a - b; if (d < 0) d = 0; printf "%.2f", d }'; }

lean_available() {
	if ! command -v lake >/dev/null 2>&1; then
		echo "lake is not in PATH, so the Lean proofs cannot be timed."
		echo "(With elan: export PATH=\$HOME/.elan/bin:\$PATH)"
		return 1
	fi
	if ! lake build Checkers.Checker.Examples.ExamplesInit >/dev/null 2>&1; then
		echo "The proofs' dependencies do not build, so only the checker"
		echo "can be timed. Build them once with"
		echo
		echo "    lake build Checkers.Checker.Examples.ExamplesInit"
		return 1
	fi
	return 0
}

cmp_pass=0
cmp_fail=0

row() { printf '%-10s %7s %8s %7s %8s %8s\n' "$@"; }

# time_lean FILE.lean -- check FILE with lake env lean; set t_total (seconds,
# wall clock) and t_ok.
time_lean() {
	local t0 t1 status
	t0=$(now_us)
	lake env lean "$1" >/dev/null 2>&1
	status=$?
	t1=$(now_us)
	t_total=$(secs $((t1 - t0)))
	t_ok=yes
	if [ "$status" -ne 0 ]; then
		echo "lean failed on $1"
		t_ok=no
	fi
}

# ratio A B -- A / B, as "12x"
ratio() {
	awk -v a="$1" -v b="$2" 'BEGIN { if (b > 0) printf "%.0fx", a / b; else printf "-" }'
}

# compare NAME PROOF-BASENAME GOCHECK-ARGS...
compare() {
	local name=$1 proof=$2
	shift 2
	local t0 t1 gocheck status ok=yes total imports

	time_lean "$PROOFS/$proof.lean"
	total=$t_total
	[ "$t_ok" = yes ] || ok=no
	grep '^import ' "$PROOFS/$proof.lean" >"$IMPORTS"
	time_lean "$IMPORTS"
	imports=$t_total

	# The checker, on the same specification.
	t0=$(now_us)
	"$GOCHECK" "$@" >/dev/null 2>&1
	status=$?
	t1=$(now_us)
	gocheck=$(secs $((t1 - t0)))
	if [ "$status" -ne 0 ]; then
		echo "$name: gocheck exited $status"
		ok=no
	fi

	if [ "$ok" = yes ]; then
		cmp_pass=$((cmp_pass + 1))
	else
		cmp_fail=$((cmp_fail + 1))
	fi
	local p
	p=$(sub_secs "$total" "$imports")
	row "$name" "$total" "$imports" "$p" "$gocheck" "$(ratio "$p" "$gocheck")"
}

echo
echo "=============================================================="
echo "# The same six specifications, proved in Lean and checked"
echo "--------------------------------------------------------------"
if lean_available; then
	lean --version | head -1
	IMPORTS=$(mktemp --suffix=.lean)
	row function lean imports proof gocheck proof/go
	compare Double Double -pkg $PKG -pre "$DOUBLE_PRE" \
		-post "$DOUBLE_POST" Double
	compare Max Max -pkg $PKG -post "$MAX_POST" Max
	compare Swap Swap -pkg $PKG -pre "$SWAP_PRE" -post "$SWAP_POST" Swap
	compare Abs Abs -pkg $PKG -post "$ABS_POST" Abs
	compare CondStore CondStore -pkg $PKG -pre "$CONDSTORE_PRE" \
		-post "$CONDSTORE_POST" CondStore
	compare Median3 Median3 -pkg $PKG -post "$MEDIAN_POST" Median3
	rm -f "$IMPORTS"
	echo "--------------------------------------------------------------"
	echo "Seconds. lean is the wall-clock time of checking that one file"
	echo "against prebuilt dependencies; imports is the time of checking"
	echo "a file with the same imports and nothing else; proof is the"
	echo "difference. proof/go compares it with one whole run of the"
	echo "checker, process startup and loading the Go package included,"
	echo "so that ratio is conservative."
	echo "$cmp_pass of $((cmp_pass + cmp_fail)) comparisons agreed"
	[ "$cmp_fail" -eq 0 ] || fail=$((fail + cmp_fail))
fi

[ "$fail" -eq 0 ]
