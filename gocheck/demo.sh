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
# The last section re-checks the same six specifications the slow way, twice:
# with the hand-written Rocq proofs in
# new/proof/github_com/mit_pdos/perennial/checker/examples/, and with the
# proofs by reflection in its reflect/ subdirectory (which use the reflective
# symbolic executor of new/proof/symex/), and times each proof against the
# corresponding run of the checker.
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

# --- The same specifications, checked by Rocq -------------------------------
#
# For each function we rebuild just the .vok file of each of its two proofs --
# that is, we re-check that one proof against already-built dependencies, the
# way an incremental `make` would -- and run the checker on the same
# specification, and report the wall-clock times.
#
# The two proofs establish the same lemma. The hand-written one steps through
# the program with wp_auto and wp_if_destruct, building a proof term one
# instruction at a time. The one by reflection calls wp_symex, which reifies
# the whole function body, runs a symbolic executor written in Gallina on it
# with vm_compute, and applies a soundness theorem proved once and for all,
# leaving one goal per path.
#
# Most of a -vok run is spent loading the proof's imports (the Perennial and
# Iris prelude), which says nothing about the proof itself, so we also report
# the time without it: `rocq compile -time` attributes wall-clock time to each
# vernacular command, and every import is one command, so the two phases can
# be summed separately.

PROOFS=new/proof/github_com/mit_pdos/perennial/checker/examples
# examples_init and the tactic library are the last files in the proofs'
# dependency closure, so their presence means the whole closure has been
# built (as .vo, or as .vos by `make vos`; a -vok run can load either).
DEPS="$PROOFS/examples_init new/proof/symex/tactic"
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
	local d missing=
	for d in $DEPS; do
		[ -f "$d.vo" ] || [ -f "$d.vos" ] || missing="$missing $d.vo"
	done
	if [ -n "$missing" ]; then
		echo "The proofs' dependencies have not been built, so only the"
		echo "checker can be timed. Build them once (this takes a few"
		echo "minutes, and is not part of what we time) with"
		echo
		echo "    make -j$NCPU TIMED=false$missing"
		return 1
	fi
	return 0
}

cmp_pass=0
cmp_fail=0

row() { printf '%-10s %9s %7s %9s %7s %8s %9s %8s\n' "$@"; }

# time_proof FILE.v -- rebuild FILE.vok alone, and set t_total (seconds,
# wall clock), t_proof (seconds spent on the proof itself, imports excluded)
# and t_ok.
time_proof() {
	local v=$1 vok=${1%.v}.vok t0 t1 status
	rm -f "$vok"
	t0=$(now_us)
	# shellcheck disable=SC2046 # the _RocqProject arguments must split
	rocq compile $(rocq_args) -vok -time -o "$vok" "$v" >"$TIMELOG" 2>/dev/null
	status=$?
	t1=$(now_us)
	t_total=$(secs $((t1 - t0)))
	t_proof=$(rocq_phase_secs "$TIMELOG" proof)
	t_ok=yes
	if [ "$status" -ne 0 ]; then
		echo "rocq failed on $v"
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
	local t0 t1 gocheck status ok=yes hand_total hand_proof refl_total refl_proof

	# Rocq, twice: the hand-written proof and the proof by reflection.
	time_proof "$PROOFS/$proof.v"
	hand_total=$t_total hand_proof=$t_proof
	[ "$t_ok" = yes ] || ok=no
	time_proof "$PROOFS/reflect/$proof.v"
	refl_total=$t_total refl_proof=$t_proof
	[ "$t_ok" = yes ] || ok=no

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
	row "$name" "$hand_total" "$hand_proof" "$refl_total" "$refl_proof" \
		"$gocheck" "$(ratio "$hand_proof" "$refl_proof")" \
		"$(ratio "$refl_proof" "$gocheck")"
}

echo
echo "=============================================================="
echo "# The same six specifications, proved in Rocq and checked"
echo "--------------------------------------------------------------"
if rocq_available; then
	rocq --version | head -1
	TIMELOG=$(mktemp)
	printf '%-10s %17s %17s\n' "" "hand-written" "by reflection"
	row function "-vok" proof "-vok" proof gocheck hand/refl refl/go
	compare Double double -pkg $PKG -pre "$DOUBLE_PRE" \
		-post "$DOUBLE_POST" Double
	compare Max max -pkg $PKG -post "$MAX_POST" Max
	compare Swap swap -pkg $PKG -pre "$SWAP_PRE" -post "$SWAP_POST" Swap
	compare Abs abs -pkg $PKG -post "$ABS_POST" Abs
	compare CondStore cond_store -pkg $PKG -pre "$CONDSTORE_PRE" \
		-post "$CONDSTORE_POST" CondStore
	compare Median3 median3 -pkg $PKG -post "$MEDIAN_POST" Median3
	rm -f "$TIMELOG"
	echo "--------------------------------------------------------------"
	echo "Seconds. -vok is the wall-clock time of rebuilding that one"
	echo ".vok against prebuilt dependencies; proof is the part of it"
	echo "spent checking the proof itself rather than loading its"
	echo "imports, as rocq -time attributes time per command (the rest"
	echo "is imports and Rocq's own startup). hand/refl is how much"
	echo "faster the proof by reflection (wp_symex, new/proof/symex/) is"
	echo "than the hand-written one; refl/go compares it with one whole"
	echo "run of the checker, process startup and loading the Go"
	echo "package included, so that ratio is conservative."
	echo "$cmp_pass of $((cmp_pass + cmp_fail)) comparisons agreed"
	[ "$cmp_fail" -eq 0 ] || fail=$((fail + cmp_fail))
fi

[ "$fail" -eq 0 ]
