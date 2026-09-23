(** [checker.Analyze] (checker/check.go): symbolic execution of a function
    body from the state its precondition describes.

    After the input checks ([f] non-nil, enough logical variables, no [∨] and
    no [∃] in the precondition, the precondition well-sorted), parameter [i]
    is bound to [TVar i] by a loop over [f.Params] ([penv], pre_sound.v), the
    entry state is built from [assnHeap], [assnPure] and a copy of the sort
    table ([pre_state]), and [exec] runs the body. [analyze_sound] turns
    [exec]'s answer into the WP of the actual function application.

    Naming: the Go locals are [f], [vars], [pre], [se], [fl], [en], [i], [x]
    and [st] (and the range loop's own index is also called [i]), so no Rocq
    variable here may be called any of those (see NOTES.md). *)
From New.checker Require Import prelude nodes exec_spec exec_def pre_sound.
From New.checker.fn Require Import assnHasOr assnHasExists assnWellSorted
  assnHeap assnPure copySorts envBind.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** TEMPORARY: discharged by fn/exec.v (the dispatcher, by induction on the
    [cexpr]). *)
Context (wp_exec : ∀ e : cexpr, ⊢ exec_like checker.exec e).

Local Ltac reject :=
  try wp_auto;
  let lfl := fresh "lfl" in
  wp_alloc lfl as "Hfl"; try wp_auto;
  iDestruct (typed_pointsto_not_null with "Hfl") as %Hnn;
  iApply "HΦ"; rewrite decide_False //.

Lemma wp_Analyze (lf : loc) (cf : cfunc) (sv : slice.t) (vs : list sort)
      (lpre : loc) (P : cassn) :
  {{{ is_pkg_init checker ∗ is_func lf cf ∗ is_sorts sv vs ∗ is_assn lpre P }}}
    @! checker.Analyze #lf #sv #lpre
  {{{ (s : slice.t) (lfail : loc), RET (#s, #lfail);
      if decide (lfail = null) then
        ∃ ps, is_paths s ps ∗ ⌜paths_wf (length vs) ps⌝ ∗
          ⌜∀ θ, vars_sat θ vs → ⊢ pre_interp θ P -∗
               WP apply_vals (func_val cf) (arg_vals cf θ)
                 {{ paths_post (length vs) (mkVal θ (λ _, uval) uval) ps }}⌝
      else True }}}.
Proof.
  wp_start as "(#Hf & #Hsv & #Hpre)".
  iDestruct "Hf" as (sp lb) "(#Hfn & #Hsp & #Hbody)".
  iDestruct (typed_pointsto_not_null with "Hfn") as %Hlfnn.
  iDestruct (own_slice_len with "Hsp") as %[Hlsp Hbsp].
  iDestruct (own_slice_len with "Hsv") as %[Hlsv Hbsv].
  rewrite length_fmap in Hlsv.
  wp_auto.
  wp_if_destruct.
  { done. }
  wp_if_destruct.
  { (* fewer logical variables than parameters *) reject. }
  wp_apply (wp_assnHasOr lpre (Some P) with "[$Hpre]").
  destruct (oassn_has_or (Some P)).
  { reject. }
  wp_auto.
  wp_apply (wp_assnHasExists lpre (Some P) with "[$Hpre]").
  destruct (oassn_has_exists (Some P)).
  { reject. }
  wp_auto.
  wp_alloc lse as "Hse".
  iPersist "Hse".
  wp_auto.
  iAssert (is_sortenv DfracDiscarded lse (vars_env vs)) as "Henv".
  { iExists sv, slice.nil, slice.nil. cbn. iFrame "Hse".
    rewrite /is_sorts. iFrame "Hsv".
    iSplit; iApply own_slice_nil. }
  wp_apply (wp_assnWellSorted DfracDiscarded lse lpre (vars_env vs) (Some P)
              with "[$Henv]") as (lws) "[_ %Hws]".
  { iFrame "Hpre". done. }
  try wp_auto.
  wp_if_destruct.
  2:{ (* the precondition is ill-sorted *)
    iApply "HΦ". rewrite decide_False //. }
  assert (cassn_ws (vars_env vs) P = true) as HwsP by naive_solver.
  clear Hws.
  (* [wp_auto] cannot allocate the range loop's own index: the Go function
     already has a local called [i], so [i_ptr] is taken. *)
  wp_alloc ridx as "Hridx".
  wp_auto.
  iAssert (∃ (k : w64) (le : loc) (xc : go_string),
      "i" ∷ i_ptr ↦ k ∗
      "Hridx" ∷ ridx ↦ k ∗
      "en" ∷ en_ptr ↦ le ∗
      "x" ∷ x_ptr ↦ xc ∗
      "#Hen" ∷ is_env le (penv (take (sint.nat k) (fparams cf))) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ≤ length (fparams cf)⌝)%I
    with "[i Hridx en x]" as "HI".
  { iFrame. replace (sint.nat (W64 0)) with 0%nat by word. rewrite take_0.
    iSplit; first done. iPureIntro. word. }
  wp_for "HI".
  destruct (bool_decide (sint.Z k < sint.Z sp.(slice.len))) eqn:Hcmp;
    [apply bool_decide_eq_true in Hcmp | apply bool_decide_eq_false in Hcmp].
  2:{ (* all parameters bound *)
    assert (sint.nat k = length (fparams cf)) as Hkl by word.
    iEval (rewrite Hkl firstn_all) in "Hen".
    wp_auto.
    wp_apply (wp_assnHeap lpre (Some P) with "[$Hpre]") as (hs) "[Hh _]".
    wp_apply (wp_assnPure lpre (Some P) with "[$Hpre]") as (cs) "[Hc _]".
    wp_apply (wp_copySorts sv vs with "[]") as (vs') "#Hvs'".
    { iExact "Hsv". }
    wp_alloc lst as "Hst".
    wp_auto.
    iPoseProof (wp_exec (fbody cf)) as "Hex".
    wp_apply ("Hex" $! lb le lst (penv (fparams cf)) (pre_state vs P)
                with "[Hst Hh Hc]") as (s lfl) "Hpost".
    { iFrame "Hbody Hen". iSplitL.
      - iExists hs, cs, vs'. iFrame. iFrame "Hvs'".
      - iPureIntro. split; first by apply pre_state_wf.
        apply penv_below. cbn [svars pre_state]. word. }
    iApply "HΦ".
    rewrite /exec_post. destruct (decide (lfl = null)); last done.
    iDestruct "Hpost" as (ps) "(Hps & %Hwf & %Hsnd)".
    iExists ps. iFrame "Hps". iPureIntro. split; first done.
    intros θ Hθ. apply analyze_sound; [word|done|done|done]. }
  wp_auto.
  list_elem (fparams cf) (sint.nat k) as xn.
  rewrite decide_True; last word.
  wp_apply (wp_load_slice_index with "[$Hsp]") as "_"; [word|done|].
  wp_alloc lt as "Ht".
  iPersist "Ht".
  wp_auto.
  wp_apply (wp_envBind le _ xn lt (TVar (sint.nat k)) with "[]") as (le') "#Hen'".
  { iFrame "Hen". cbn [is_term]. rewrite /tnode.
    replace (W64 (sint.nat k)) with k by word. iFrame "Ht".
    iPureIntro. rewrite /idx_wf. word. }
  wp_for_post.
  iFrame.
  replace (sint.nat (word.add k (W64 1))) with (S (sint.nat k)) by word.
  rewrite (take_S_r _ _ xn) // penv_snoc length_take_le; last word.
  iFrame "Hen'". iPureIntro. word.
Qed.

End proof.
