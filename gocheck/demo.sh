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
set -uo pipefail

cd "$(dirname "$0")/.." || exit 2

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

# --- Verified examples ------------------------------------------------------

run 0 "Double: heap write, arithmetic, control flow" \
	-pkg $PKG -pre 'z |-> z0' \
	-post '(⌜x == 0⌝ ∗ z ↦ 37 + 37) ∨ (⌜x != 0⌝ ∗ z ↦ x + x)' Double

run 0 "Max: unsigned comparison and two returns" \
	-pkg $PKG \
	-post '(⌜a <u b⌝ ∗ ⌜ret == b⌝) ∨ (⌜a >=u b⌝ ∗ ⌜ret == a⌝)' Max

run 0 "Swap: two owned cells exchange their contents" \
	-pkg $PKG -pre 'p |-> a ∗ q |-> b' \
	-post 'p ↦ b ∗ q ↦ a' Swap

run 0 "Abs: signed comparison and a negated result" \
	-pkg $PKG \
	-post '(⌜x <s 0⌝ ∗ ⌜ret == -x⌝) ∨ (⌜x >=s 0⌝ ∗ ⌜ret == x⌝)' Abs

run 0 "CondStore: a boolean result and a conditional write" \
	-pkg $PKG -pre 'p |-> v0' \
	-post '(⌜!flag⌝ ∗ p ↦ v0 ∗ ⌜ret == false⌝) ∨ (⌜flag⌝ ∗ p ↦ v ∗ ⌜ret == true⌝)' CondStore

# The same two assertions in pure ASCII, printed in ASCII notation.
run 0 "Swap again, all ASCII (-ascii)" \
	-pkg $PKG -ascii -pre 'p |-> a * q |-> b' -post 'p |-> b * q |-> a' Swap

# --- Rejected inputs --------------------------------------------------------

run 1 "Swap without owning q: the load from q is unsafe" \
	-pkg $PKG -pre 'p |-> a' Swap

run 1 "Double against a postcondition it does not establish" \
	-pkg $PKG -pre 'z |-> z0' -post 'z ↦ 74' Double

run 2 "Double against an ill-sorted postcondition" \
	-pkg $PKG -pre 'z |-> z0' -post '⌜x && z0⌝' Double

# --- Strongest postconditions, with no -post at all -------------------------

run 0 "Max: just print the strongest postcondition" -pkg $PKG Max

run 0 "Double: the translated GooseLang body too (-ast)" \
	-pkg $PKG -ast -pre 'z |-> z0' Double

echo
echo "=============================================================="
echo "$pass cases behaved as expected, $fail did not"
[ "$fail" -eq 0 ]
