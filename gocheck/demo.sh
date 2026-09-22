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
# The last section re-checks the same five specifications the slow way, with
# the hand-written Rocq proofs in
# new/proof/github_com/mit_pdos/perennial/checker/examples/, and times each
# proof against the corresponding run of the checker.
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

# --- The same specifications, checked by Rocq -------------------------------
#
# For each function we rebuild just the .vok file of its proof -- that is, we
# re-check that one proof against already-built dependencies, the way an
# incremental `make` would -- and run the checker on the same specification,
# and report both wall-clock times.
#
# Most of a -vok run is spent loading the proof's imports (the Perennial and
# Iris prelude), which says nothing about the proof itself, so we also report
# the time without it: `rocq compile -time` attributes wall-clock time to each
# vernacular command, and every import is one command, so the two phases can
# be summed separately.

PROOFS=new/proof/github_com/mit_pdos/perennial/checker/examples
# examples_init.vos is the last .vos in the proofs' dependency closure, so its
# presence means the whole closure has been built.
DEPS=$PROOFS/examples_init.vos
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

# rocq_phase_secs LOG imports|proof -- add up the times `rocq compile -time`
# reported for the import commands, or for every other command. Its lines look
# like
#
#   Chars 721 - 738 [wp_start~as~"Hz".] 0.158 secs (0.155u,0.001s)
#
# with spaces in the command replaced by ~ and the command truncated to 30
# characters, which is why an import is recognised by its leading From or
# Require rather than by the word Require.
rocq_phase_secs() {
	awk -v want="$2" '
		/^Chars [0-9]+ - [0-9]+ \[/ {
			rest = $0
			sub(/^Chars [0-9]+ - [0-9]+ \[/, "", rest)
			close_bracket = index(rest, "]")
			cmd = substr(rest, 1, close_bracket - 1)
			split(substr(rest, close_bracket + 2), field, " ")
			is_import = (cmd ~ /^(From|Require)/)
			if ((want == "imports") == is_import) {
				total += field[1] + 0
			}
		}
		END { printf "%.2f", total + 0 }
	' "$1"
}

# The global arguments Rocq needs, extracted from _RocqProject the same way
# the Makefile does.
rocq_args() {
	sed -E -e '/^#/d' -e 's/-arg ([^ ]*)/\1/g' _RocqProject
}

rocq_available() {
	if ! command -v rocq >/dev/null 2>&1; then
		echo "rocq is not in PATH, so the Rocq proofs cannot be timed."
		echo "(With opam: eval \$(opam env --switch=perennial))"
		return 1
	fi
	if [ ! -f "$DEPS" ]; then
		echo "The proofs' dependencies have not been built, so only the"
		echo "checker can be timed. Build them once (this takes a few"
		echo "minutes, and is not part of what we time) with"
		echo
		echo "    make -j$NCPU TIMED=false $DEPS"
		return 1
	fi
	return 0
}

cmp_pass=0
cmp_fail=0

row() { printf '%-11s %10s %9s %10s %10s %9s\n' "$@"; }

# compare NAME PROOF-BASENAME GOCHECK-ARGS...
compare() {
	local name=$1 proof=$2
	shift 2
	local vok=$PROOFS/$proof.vok
	local t0 t1 rocq_us gocheck_us status ok=yes imports proof_only

	# Rocq: rebuild this one .vok, nothing else.
	rm -f "$vok"
	t0=$(now_us)
	# shellcheck disable=SC2046 # the _RocqProject arguments must split
	rocq compile $(rocq_args) -vok -time -o "$vok" "$PROOFS/$proof.v" \
		>"$TIMELOG" 2>/dev/null
	status=$?
	t1=$(now_us)
	rocq_us=$((t1 - t0))
	if [ "$status" -ne 0 ]; then
		echo "$name: rocq failed on $PROOFS/$proof.v"
		ok=no
	fi
	imports=$(rocq_phase_secs "$TIMELOG" imports)
	proof_only=$(rocq_phase_secs "$TIMELOG" proof)

	# The checker, on the same specification.
	t0=$(now_us)
	"$GOCHECK" "$@" >/dev/null 2>&1
	status=$?
	t1=$(now_us)
	gocheck_us=$((t1 - t0))
	if [ "$status" -ne 0 ]; then
		echo "$name: gocheck exited $status"
		ok=no
	fi

	if [ "$ok" = yes ]; then
		cmp_pass=$((cmp_pass + 1))
	else
		cmp_fail=$((cmp_fail + 1))
	fi
	row "$name" "$(secs "$rocq_us")" "$imports" "$proof_only" \
		"$(secs "$gocheck_us")" \
		"$(awk -v r="$proof_only" -v g="$gocheck_us" \
			'BEGIN {
				g /= 1e6
				if (g > 0) printf "%.0fx", r / g; else printf "-"
			}')"
}

echo
echo "=============================================================="
echo "# The same five specifications, proved in Rocq and checked"
echo "--------------------------------------------------------------"
if rocq_available; then
	rocq --version | head -1
	TIMELOG=$(mktemp)
	row function "-vok total" imports proof gocheck speedup
	compare Double double -pkg $PKG -pre "$DOUBLE_PRE" \
		-post "$DOUBLE_POST" Double
	compare Max max -pkg $PKG -post "$MAX_POST" Max
	compare Swap swap -pkg $PKG -pre "$SWAP_PRE" -post "$SWAP_POST" Swap
	compare Abs abs -pkg $PKG -post "$ABS_POST" Abs
	compare CondStore cond_store -pkg $PKG -pre "$CONDSTORE_PRE" \
		-post "$CONDSTORE_POST" CondStore
	rm -f "$TIMELOG"
	echo "--------------------------------------------------------------"
	echo "Seconds. -vok total is the wall-clock time of rebuilding that"
	echo "one .vok against prebuilt dependencies; imports and proof split"
	echo "it into loading the proof's imports and checking the proof"
	echo "itself, as rocq -time attributes time per command. The two do"
	echo "not quite add up to the total, which also pays for Rocq's own"
	echo "startup. The gocheck column is one whole run of the checker,"
	echo "process startup and loading the Go package included, so the"
	echo "speedup -- proof over that whole run -- is conservative."
	echo "$cmp_pass of $((cmp_pass + cmp_fail)) comparisons agreed"
	[ "$cmp_fail" -eq 0 ] || fail=$((fail + cmp_fail))
fi

[ "$fail" -eq 0 ]
