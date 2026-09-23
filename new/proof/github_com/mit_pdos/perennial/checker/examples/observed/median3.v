(* wp_Median3, from one observed run of the checker.

   gocheck/observe.sh runs gocheck on Median3 with the specification of
   gocheck/demo.sh. It records the input gocheck hands to checker.Check in
   median3_input.v ([median3_func], [median3_vars], [median3_pre],
   [median3_post]), and it fails unless checker.Check answers true on it.
   [median3_check_run] is that observation, as an axiom: some GooseLang run of
   checker.Check, from a state whose heap holds this input, returns #true.

   Nothing else is trusted. [check_adequate] (new/checker/adequacy.v) turns
   the run into [triple_holds]. The input's function is checked to be exactly
   Goose's Median3 ([median3_func_val], by reflexivity), and the input's
   postcondition is translated into the one of the other two proofs of
   wp_Median3 (../median3.v, ../reflect/median3.v). *)
From New.checker Require Import prelude layout adequacy post_simp.
From Perennial.goose_lang Require Import adequacy.
From New.proof.github_com.mit_pdos.perennial.checker.examples
  Require Import examples_init.
From New.proof.github_com.mit_pdos.perennial.checker.examples.observed
  Require Import median3_input.

(** OBSERVE-EXECUTION for Median3 (gocheck/observe.sh). The run is under some
    model of GooseLang: an FFI, a Go semantics satisfying [go.Semantics], and
    [checker.Assumptions]. The ghost state is not part of it. *)
Axiom median3_check_run :
  ∃ (ext : ffi_syntax) (ffi : ffi_model) (ffi_sem : ffi_semantics ext ffi)
    (ffi_interp0 : ffi_interp ffi) (Hffi_adequacy : ffi_interp_adequacy)
    (go_gctx : GoGlobalContext) (lctx : GoLocalContext)
    (sem : go.Semantics) (package_sem : checker.Assumptions)
    (lf : loc) (svars : slice.t) (lpre lpost : loc)
    (σ σ' : state) (g g' : global_state) (tp : list expr),
    ffi_initgP g.(global_world) ∧ ffi_initP σ.(world) g.(global_world) ∧
    σ.(go_state).(go_lctx) = lctx ∧
    inputs_in σ.(heap) lf median3_func svars median3_vars lpre median3_pre lpost median3_post ∧
    rtc erased_step ([(@! checker.Check #lf #svars #lpre #lpost)%E], (σ, g))
                    (of_val #true :: tp, (σ', g')).

Lemma median3_triple :
  triple_holds median3_func median3_vars median3_pre median3_post.
Proof.
  destruct median3_check_run as (ext & ffi & ffi_sem & ffi_interp0 & Hffi_adequacy &
    go_gctx & lctx & sem & package_sem & lf & svars & lpre & lpost &
    σ & σ' & g & g' & tp & Hinitg & Hinit & Hlctx & Hin & Hrun).
  exact (check_adequate _ _ _ _ _ _ _ _ _ _ _ _ _ Hinitg Hinit Hlctx Hin Hrun).
Qed.

Section wps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : examples.Assumptions}.
Collection W := sem + package_sem.
Set Default Proof Using "W".

(** gocheck's translation of the body is Goose's. *)
Lemma median3_func_val : func_val median3_func = examples.Median3ⁱᵐᵖˡ.
Proof. reflexivity. Qed.

(** The specification of the other two proofs of wp_Median3 (../median3.v,
    ../reflect/median3.v), except that the result is a [val] [v] with
    [⌜v = #x⌝] in place of [RET #r] with [⌜r = x⌝]. That is what makes it the
    checker's postcondition up to simplification: in the form [RET #r], the
    last two (contradictory) disjuncts would have to be refuted by arithmetic
    to produce an [r], and each of the others would need a case of its own to
    pick one. *)
Lemma wp_Median3 (a b c : w64) :
  {{{ is_pkg_init examples }}}
    @! examples.Median3 #a #b #c
  {{{ (v : val), RET v;
      (⌜uint.Z b < uint.Z a⌝ ∗ ⌜uint.Z c < uint.Z b⌝ ∗ ⌜v = #b⌝) ∨
      (⌜uint.Z a ≤ uint.Z b⌝ ∗ ⌜uint.Z b ≤ uint.Z c⌝ ∗ ⌜v = #b⌝) ∨
      (⌜uint.Z b ≤ uint.Z c⌝ ∗ ⌜uint.Z c < uint.Z a⌝ ∗ ⌜v = #c⌝) ∨
      (⌜uint.Z a ≤ uint.Z c⌝ ∗ ⌜uint.Z c < uint.Z b⌝ ∗ ⌜v = #c⌝) ∨
      (⌜uint.Z b < uint.Z a⌝ ∗ ⌜uint.Z a ≤ uint.Z c⌝ ∗ ⌜v = #a⌝) ∨
      (⌜uint.Z c < uint.Z a⌝ ∗ ⌜uint.Z a ≤ uint.Z b⌝ ∗ ⌜v = #a⌝) ∨
      (⌜uint.Z b < uint.Z a⌝ ∗ ⌜uint.Z a < uint.Z b⌝) ∨
      (⌜uint.Z a ≤ uint.Z b⌝ ∗ ⌜uint.Z b < uint.Z a⌝) }}}.
Proof.
  wp_start_folded as "_". iEval (rewrite func_unfold !ival_eq).
  (* The logical variables 0, 1, 2 are the parameters. *)
  iApply (median3_triple _ _ _ _ Σ hG sem (λ n, nth n [ival a; ival b; ival c] uval)
            with "[//]").
  { intros [|[|[|n]]] s Hs; simpl in Hs; simplify_eq; by eexists. }
  iIntros "!>" (v).
  (* The interpreted postcondition computes to the one above. *)
  rewrite /post_interp assn_interp_simp_eq /median3_post /= -!ival_eq.
  iIntros "Hpost". iApply ("HΦ" with "Hpost").
Qed.

End wps.
