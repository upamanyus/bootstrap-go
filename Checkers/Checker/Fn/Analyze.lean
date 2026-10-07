/-
Port of `new/checker/fn/Analyze.v`.

`checker.Analyze` (checker/check.go): symbolic execution of a function
body from the state its precondition describes.

After the input checks (`f` non-nil, enough logical variables, no `∨` and
no `∃` in the precondition, the precondition well-sorted), parameter `i`
is bound to `TVar i` by a loop over `f.Params` (`penv`, PreSound.lean), the
entry state is built from `assnHeap`, `assnPure` and a copy of the sort
table (`pre_state`), and `exec` runs the body. The answer is
`analyze_ok`, which `analyze_sound` turns into the WP of the actual
function application in any ghost state.

Lean notes:
* The Go function has its own local `i` and a range loop, whose index
  `wp_auto` also allocates: the Go counter's points-to becomes inaccessible
  and is renamed `gi` (`rename_i` + `irename`, as in Fn/findCell.lean);
  Rocq allocated the range index by hand instead.
* `wp_exec` (Fn/exec.lean) is used through `exec_like_triple` (ExecDef.lean).
* Rocq's `if decide (lfail = null)` is `if lfail = null` (a `Decidable` `if`).
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.ExecSpec
import Checkers.Checker.ExecDef
import Checkers.Checker.PreSound
import Checkers.Checker.Fn.exec
import Checkers.Checker.Fn.assnHasOr
import Checkers.Checker.Fn.assnHasExists
import Checkers.Checker.Fn.assnWellSorted
import Checkers.Checker.Fn.assnHeap
import Checkers.Checker.Fn.assnPure
import Checkers.Checker.Fn.copySorts
import Checkers.Checker.Fn.envBind

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

-- Return `(nil, &Failure{…})`: the postcondition holds trivially.
set_option hygiene false in
local macro "reject" : tactic => `(tactic| (
  try wp_auto
  wp_alloc lfl as Hfl
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hfl
  try wp_auto
  iapply HΦ
  simp only [Hnn, ↓reduceIte]
  itrivial))

theorem wp_Analyze (lf : Loc) (cf : cfunc) (sv : GoSlice) (vs : List sort)
    (lpre : Loc) (P : cassn) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_func lf cf ∗ is_sorts sv vs ∗
        is_assn lpre P }}
      (App (App (App (Val (@! checker.Analyze)) (Val #lf)) (Val #sv)) (Val #lpre))
    {{ (s : GoSlice) (lfail : Loc), RET (PairV #s #lfail);
        if lfail = null then
          iprop(∃ ps, is_paths s ps ∗ ⌜paths_wf vs.length ps⌝ ∗ ⌜analyze_ok cf vs P ps⌝)
        else iprop(True) }} := by
  wp_start as ⟨#Hf, #Hsv, #Hpre⟩
  unfold is_func
  icases Hf with ⟨%sp, %lb, #Hfn, #Hsp, #Hbody⟩
  ihave %Hlfnn := typedPointsto_not_null _ _ _ $$ Hfn
  ihave %Hlsp := ownSlice_len _ _ _ $$ Hsp
  unfold is_sorts
  ihave %Hlsv := ownSlice_len _ _ _ $$ Hsv
  iStructNamed Hfn
  wp_auto
  rw [decide_eq_false Hlfnn]
  wp_auto
  wp_if_destruct
  · -- fewer logical variables than parameters
    reject
  have Hvlen : cf.fparams.length ≤ vs.length := by rw [List.length_map] at Hlsv; word
  wp_apply wp_assnHasOr lpre (some P) $$ []
  · rw [is_oassn_some]; iframe #
  cases Hor : oassn_has_or (some P)
  case true => reject
  wp_auto
  wp_apply wp_assnHasExists lpre (some P) $$ []
  · rw [is_oassn_some]; iframe #
  cases Hex : oassn_has_exists (some P)
  case true => reject
  wp_auto
  ipersist «$r0»
  ihave Henv : is_sortenv (GF := GF) DFrac.discard «$r0_ptr» (vars_env vs) $$ []
  · unfold is_sortenv
    iexists sv, slice.nil, slice.nil
    ihave #Hnil1 := ownSlice_nil (GF := GF) (V := w64) DFrac.discard
    ihave #Hnil2 := ownSlice_nil (GF := GF) (V := Bool) DFrac.discard
    simp only [vars_env, List.map_nil]
    iframe Hsv Hnil1 Hnil2
    iExactEq «$r0»; rfl
  wp_apply wp_assnWellSorted DFrac.discard «$r0_ptr» lpre (vars_env vs) (some P) $$ [Henv]
    as %lws ⟨-, %Hws⟩
  · rw [is_oassn_some]
    iframe Henv Hpre
    ipureintro; rfl
  by_cases Hlws : lws = null
  case neg =>
    -- the precondition is ill-sorted
    rw [decide_eq_false Hlws]
    wp_auto
    iapply HΦ
    simp only [Hlws, ↓reduceIte]
    itrivial
  subst Hlws
  have HwsP : cassn_ws (vars_env vs) P = true := Hws.mp rfl
  clear Hws
  rw [decide_eq_true rfl]
  wp_auto
  -- the Go local `i` and the range loop's index: the Go counter is `gi`
  rename_i gi_ptr
  irename: gi_ptr ↦ (W64 0) => gi
  ihave HI : (∃ (k : w64) (le : Loc) (xc : GoString),
      "gi" ∷ gi_ptr ↦ k ∗
      "i" ∷ i_ptr ↦ k ∗
      "en" ∷ en_ptr ↦ le ∗
      "x" ∷ x_ptr ↦ xc ∗
      "#Hen" ∷ is_env le (penv (cf.fparams.take (sint.nat k))) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ∧ sint.Z k ≤ cf.fparams.length⌝ : IProp GF) $$ [gi i en x]
  · iexists W64 0, null, _
    iframe gi i en x
    isplitl
    · rw [show sint.nat (W64 0) = 0 from rfl, List.take_zero]
      simp only [penv, penv_from, is_env]
      ipureintro; trivial
    ipureintro; word
  wp_for HI
  by_cases Hcmp : sint.Z k < sint.Z sp.len
  case pos =>
    simp only [decide_eq_true Hcmp, ↓reduceIte]
    wp_auto
    rw [ite_eq_left ⟨Hk.1, Hcmp⟩]
    list_elem cf.fparams (sint.nat k) as xn
    wp_apply wp_load_slice_index sp (sint.Z k) cf.fparams _ xn Hk.1 $$ [] with -
    · iframe Hsp; ipureintro; exact Hxn_lookup
    ipersist «$a2»
    wp_apply wp_envBind le _ xn «$a2_ptr» (TVar (sint.nat k)) $$ [] as %le' #Hen'
    · iframe Hen
      simp only [is_term, tnode]
      isplitr
      · ipureintro; unfold idx_wf; word
      · rw [show (W64 (sint.nat k) : w64) = k by word]
        iexact «$a2»
    wp_for_post
    iframe
    iexists k + W64 1, le', xn
    iframe
    have Hk1 : sint.nat (k + W64 1) = sint.nat k + 1 := by word
    rw [Hk1, List.take_add_one, Hxn_lookup, Option.toList_some, penv_snoc,
      List.length_take_of_le (by word)]
    iframe Hen'
    ipureintro; word
  case neg =>
    simp only [decide_eq_false Hcmp, Bool.false_eq_true, ↓reduceIte]
    have Hkl : sint.nat k = cf.fparams.length := by word
    rw [Hkl, List.take_length]
    wp_auto
    wp_apply wp_assnHeap lpre (some P) $$ [] as %hs ⟨Hh, Hhc⟩
    · rw [is_oassn_some]; iframe #
    wp_apply wp_assnPure lpre (some P) $$ [] as %cs ⟨Hc, Hcc⟩
    · rw [is_oassn_some]; iframe #
    wp_apply wp_copySorts sv vs $$ [] as %vs' #Hvs'
    · unfold is_vars; iframe #
    wp_apply exec_like_triple _ _ (wp_exec cf.fbody) lb le «$r0_ptr» (penv cf.fparams)
        (pre_state vs P) $$ [«$r0» Hh Hc] as %s %lfl Hpost
    · iframe Hbody Hen
      isplitl
      · unfold is_state
        rw [show oassn_heap (some P) = sheap (pre_state vs P) from rfl,
          show oassn_pure (some P) = spc (pre_state vs P) from rfl,
          show svars (pre_state vs P) = vs from rfl]
        iexists hs, cs, vs'
        iframe «$r0» Hh Hc Hvs'
      · ipureintro
        exact ⟨pre_state_wf vs P HwsP, penv_below _ _ Hvlen⟩
    iapply HΦ
    unfold exec_post
    by_cases Hl : lfl = null
    · simp only [Hl, ↓reduceIte]
      icases Hpost with ⟨%ps, Hps, %Hwf, %Hsnd⟩
      iexists ps
      iframe Hps
      ipureintro
      exact ⟨Hwf, Hvlen, HwsP, Hsnd⟩
    · simp only [Hl, ↓reduceIte]
      itrivial

end proof

end Checker
end Perennial
