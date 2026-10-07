# The six specifications of gocheck/demo.sh, shared with gocheck/native.sh
# (which hands them to the Lean-native checker). Sourced, not run.
#
# Each is a precondition or a postcondition in gocheck's spec language; an
# unset precondition is `emp`.
DOUBLE_PRE='z ↦ z0'
DOUBLE_POST='(⌜x == 0⌝ ∗ z ↦ 37 + 37) ∨ (⌜x != 0⌝ ∗ z ↦ x + x)'
MAX_POST='(⌜a <u b⌝ ∗ ⌜ret == b⌝) ∨ (⌜a >=u b⌝ ∗ ⌜ret == a⌝)'
SWAP_PRE='p ↦ a ∗ q ↦ b'
SWAP_POST='p ↦ b ∗ q ↦ a'
ABS_POST='(⌜x <s 0⌝ ∗ ⌜ret == -x⌝) ∨ (⌜x >=s 0⌝ ∗ ⌜ret == x⌝)'
CONDSTORE_PRE='p ↦ v0'
CONDSTORE_POST='(⌜!flag⌝ ∗ p ↦ v0 ∗ ⌜ret == false⌝) ∨ (⌜flag⌝ ∗ p ↦ v ∗ ⌜ret == true⌝)'
# The checker has no arithmetic, so the median is stated path by path, with
# each path's conditions exactly as they print; the last two disjuncts are the
# two infeasible paths, whose conditions contradict.
MEDIAN_POST='(⌜b <u a⌝ ∗ ⌜c <u b⌝ ∗ ⌜ret == b⌝) ∨ (⌜b >=u a⌝ ∗ ⌜c >=u b⌝ ∗ ⌜ret == b⌝) ∨ (⌜c >=u b⌝ ∗ ⌜c <u a⌝ ∗ ⌜ret == c⌝) ∨ (⌜c >=u a⌝ ∗ ⌜c <u b⌝ ∗ ⌜ret == c⌝) ∨ (⌜b <u a⌝ ∗ ⌜c >=u a⌝ ∗ ⌜ret == a⌝) ∨ (⌜c <u a⌝ ∗ ⌜b >=u a⌝ ∗ ⌜ret == a⌝) ∨ (⌜b <u a⌝ ∗ ⌜a <u b⌝) ∨ (⌜b >=u a⌝ ∗ ⌜b <u a⌝)'

