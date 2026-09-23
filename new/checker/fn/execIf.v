(** [checker.execIf] (checker/exec.go): one path of an [if].

    [c] is the condition term reached on the path and [st] its state. The
    condition must be boolean-sorted ([SortOf]). A literal condition takes
    the corresponding branch with the state unchanged; otherwise the state is
    cloned twice, the [then] branch runs with [c] added to the path condition
    and the [else] branch with [negate c], and the result is the
    concatenation.

    Naming: the Go locals are [e], [en], [c], [st], [ok], [s], [st1], [fl1],
    [ps1], [st2], [fl2], [ps2], [out], so no Rocq variable here is called any
    of those (see NOTES.md). *)
From New.checker Require Import prelude nodes exec_spec exec_def exec_sound_c.
From New.checker.fn Require Import SortOf sortOfEnv negate State__clone heapUpdate.

(** The kind test [c.Kind == TBool], without destructing the term. *)
Lemma term_kind_tbool (tc : term) : (∃ b, tc = TBool b) ∨ term_code tc ≠ W64 5.
Proof.
  destruct tc; first [by left; eauto | right; simpl; repeat case_match; by vm_compute].
Qed.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Definition execIf_post (ct cf : cexpr) ρ (tc : term) (sst : sstate)
    (sr : slice.t) (lf : loc) : iProp Σ :=
  (if decide (lf = null) then
     ∃ qvs, is_paths sr qvs ∗ ⌜paths_wf (length (svars sst)) qvs⌝ ∗
            ⌜sort_of_vars (svars sst) tc = Some SBool⌝ ∗
            ⌜if_ok ct cf ρ (mkPath tc sst) qvs⌝
   else True)%I.

Lemma wp_execIf (le lρ lc lst : loc) (cc ct cf : cexpr) (tc : term)
    (ρ : list (go_string * term)) (sst : sstate) :
  (⊢ exec_like checker.exec ct) → (⊢ exec_like checker.exec cf) →
  {{{ is_pkg_init checker ∗ is_expr le (CEIf cc ct cf) ∗ is_env lρ ρ ∗
      is_term lc tc ∗ is_state lst sst ∗
      ⌜wf_state sst⌝ ∗ ⌜env_below (length (svars sst)) ρ⌝ ∗
      ⌜vars_below (length (svars sst)) tc⌝ }}}
    @! checker.execIf #le #lρ #lc #lst
  {{{ (sr : slice.t) (lf : loc), RET (#sr, #lf); execIf_post ct cf ρ tc sst sr lf }}}.
Proof.
  intros Hext Hexf.
  wp_start as "(#He & #Hρ & #Htc & Hst & %Hwf & %Hρb & %Htb)".
  iDestruct "He" as (lcc la lb) "(#Hn & #Hc & #Ha & #Hb)".
  fold (is_expr lcc cc). fold (is_expr la ct). fold (is_expr lb cf).
  iDestruct "Hst" as (hs cs vs) "(Hl & Hh & Hcond & #Hv)".
  wp_auto.
  wp_apply (wp_SortOf vs lc (svars sst) (Some tc) with "[$Hv]").
  { iFrame "#". }
  fold (sort_of_vars (svars sst) tc).
  destruct (sort_of_vars (svars sst) tc) as [srt|] eqn:Hsrt; last first.
  { (* no sort *)
    try wp_auto. wp_alloc lfail as "Hf". try wp_auto.
    iDestruct (typed_pointsto_not_null with "Hf") as %Hnn.
    iApply "HΦ". rewrite /execIf_post. by rewrite decide_False. }
  destruct (decide (srt = SBool)) as [->|Hnb]; last first.
  { (* the wrong sort *)
    destruct srt; try done; try wp_auto; rewrite /checker.SortBool; try wp_auto;
      wp_alloc lfail as "Hf"; try wp_auto;
      iDestruct (typed_pointsto_not_null with "Hf") as %Hnn;
      iApply "HΦ"; rewrite /execIf_post; by rewrite decide_False. }
  try wp_auto.
  iDestruct (is_term_node with "Htc") as (ta tb tcc) "(%Hiw & #Hnode & _ & _ & _)".
  destruct (term_kind_tbool tc) as [[b ->]|Hnk].
  { (* a literal condition *)
    try wp_auto. rewrite /checker.TBool. try wp_auto.
    iAssert (is_state lst sst) with "[Hl Hh Hcond]" as "Hst".
    { iExists hs, cs, vs. iFrame "∗#". }
    destruct b.
    - rewrite (bool_decide_eq_true_2 (bool_code true = W64 1)) //.
      try wp_auto.
      wp_apply (Hext $! la lρ lst ρ sst with "[$Hst]").
      { iFrame "#". done. }
      iIntros (sr lf) "Hpost".
      try wp_auto.
      iApply "HΦ". rewrite /execIf_post /exec_post.
      destruct (decide (lf = null)); last done.
      iDestruct "Hpost" as (qvs) "(Hq & %Hq1 & %Hq2)".
      iExists qvs. iFrame "Hq". iPureIntro. split_and!; [done|done|].
      left. by exists true.
    - rewrite (bool_decide_eq_false_2 (bool_code false = W64 1)); last by vm_compute.
      try wp_auto.
      wp_apply (Hexf $! lb lρ lst ρ sst with "[$Hst]").
      { iFrame "#". done. }
      iIntros (sr lf) "Hpost".
      try wp_auto.
      iApply "HΦ". rewrite /execIf_post /exec_post.
      destruct (decide (lf = null)); last done.
      iDestruct "Hpost" as (qvs) "(Hq & %Hq1 & %Hq2)".
      iExists qvs. iFrame "Hq". iPureIntro. split_and!; [done|done|].
      left. by exists false. }
  try wp_auto. rewrite /checker.TBool. try wp_auto.
  rewrite (bool_decide_eq_false_2 (term_code tc = W64 5)) //.
  try wp_auto.
  iAssert (is_state lst sst) with "[Hl Hh Hcond]" as "Hst".
  { iExists hs, cs, vs. iFrame "∗#". }
  (* the [then] state *)
  wp_apply (wp_State__clone with "[$Hst]") as (lst1) "[Hst Hfr]".
  iDestruct "Hfr" as (hs1 cs1 vs1) "(Hl1 & Hh1 & Hhcap1 & Hc1 & Hccap1 & Hv1 & Hvcap1)".
  iDestruct "Hc1" as (ls1) "[Hls1 #Hls1p]".
  wp_auto.
  wp_apply wp_slice_literal.
  iSplitR; first done.
  iIntros "%sl1 [Hsl1 _]".
  rewrite insert0_singleton. wp_auto.
  wp_apply (wp_slice_append cs1 ls1 _ _ (DfracOwn 1)
             with "[$Hls1 $Hccap1 $Hsl1]") as (cs1') "(Hls1 & Hccap1 & _)".
  try wp_auto.
  iAssert (is_state_fresh lst1 (st_assume sst tc))
    with "[Hl1 Hh1 Hhcap1 Hls1 Hccap1 Hv1 Hvcap1]" as "Hfr".
  { iExists hs1, cs1', vs1. cbn [st_assume sheap spc svars].
    iFrame "Hl1 Hh1 Hhcap1 Hccap1 Hv1 Hvcap1".
    iExists _. iFrame "Hls1".
    iApply (big_sepL2_app with "Hls1p"). cbn. iSplit; last done. iExact "Htc". }
  iMod (is_state_fresh_publish with "Hfr") as "Hst1".
  wp_apply (Hext $! la lρ lst1 ρ (st_assume sst tc) with "[$Hst1]").
  { iFrame "#". iPureIntro. split; last done. by apply wf_state_assume. }
  iIntros (sps1 lfl1) "Hpost1".
  rewrite /exec_post.
  try wp_auto.
  wp_if_destruct.
  2: { try wp_auto. iApply "HΦ". rewrite /execIf_post.
       destruct (decide (lfl1 = null)); [congruence|done]. }
  destruct (decide (null = null)) as [_|]; last congruence.
  iDestruct "Hpost1" as (qv1) "(Hq1 & %Hwfq1 & %Hsndq1)".
  (* the [else] state *)
  wp_apply (wp_State__clone with "[$Hst]") as (lst2) "[_ Hfr]".
  iDestruct "Hfr" as (hs2 cs2 vs2) "(Hl2 & Hh2 & Hhcap2 & Hc2 & Hccap2 & Hv2 & Hvcap2)".
  iDestruct "Hc2" as (ls2) "[Hls2 #Hls2p]".
  wp_auto.
  wp_apply (wp_negate with "[$Htc]") as (lneg) "#Hneg".
  wp_apply wp_slice_literal.
  iSplitR; first done.
  iIntros "%sl2 [Hsl2 _]".
  rewrite insert0_singleton. try wp_auto.
  wp_apply (wp_slice_append cs2 ls2 _ _ (DfracOwn 1)
             with "[$Hls2 $Hccap2 $Hsl2]") as (cs2') "(Hls2 & Hccap2 & _)".
  try wp_auto.
  iAssert (is_state_fresh lst2 (st_assume sst (negate tc)))
    with "[Hl2 Hh2 Hhcap2 Hls2 Hccap2 Hv2 Hvcap2]" as "Hfr".
  { iExists hs2, cs2', vs2. cbn [st_assume sheap spc svars].
    iFrame "Hl2 Hh2 Hhcap2 Hccap2 Hv2 Hvcap2".
    iExists _. iFrame "Hls2".
    iApply (big_sepL2_app with "Hls2p"). cbn. iSplit; last done. iExact "Hneg". }
  iMod (is_state_fresh_publish with "Hfr") as "Hst2".
  wp_apply (Hexf $! lb lρ lst2 ρ (st_assume sst (negate tc)) with "[$Hst2]").
  { iFrame "#". iPureIntro. split; last done.
    apply wf_state_assume; [done|by apply vars_below_negate]. }
  iIntros (sps2 lfl2) "Hpost2".
  rewrite /exec_post.
  try wp_auto.
  wp_if_destruct.
  2: { try wp_auto. iApply "HΦ". rewrite /execIf_post.
       destruct (decide (lfl2 = null)); [congruence|done]. }
  destruct (decide (null = null)) as [_|]; last congruence.
  iDestruct "Hpost2" as (qv2) "(Hq2 & %Hwfq2 & %Hsndq2)".
  iDestruct "Hq1" as (ys1) "[Hys1 Hys1p]".
  iDestruct "Hq2" as (ys2) "[Hys2 Hys2p]".
  iDestruct (own_slice_nil (V:=checker.Path.t) (DfracOwn 1)) as "Hnil".
  iDestruct (own_slice_cap_nil (V:=checker.Path.t)) as "Hnilcap".
  wp_apply (wp_slice_append slice.nil [] sps1 ys1 (DfracOwn 1)
             with "[$Hnil $Hnilcap $Hys1]") as (so1) "(Hso1 & Hso1cap & _)".
  try wp_auto.
  wp_apply (wp_slice_append so1 ([] ++ ys1) sps2 ys2 (DfracOwn 1)
             with "[$Hso1 $Hso1cap $Hys2]") as (so2) "(Hso2 & _ & _)".
  try wp_auto.
  iApply "HΦ". rewrite /execIf_post.
  destruct (decide (null = null)) as [_|]; last congruence.
  iExists (qv1 ++ qv2). iSplitL.
  { iExists (([] ++ ys1) ++ ys2). iFrame "Hso2". rewrite app_nil_l.
    iApply (big_sepL2_app with "Hys1p Hys2p"). }
  iPureIntro. split_and!.
  - by apply paths_wf_app.
  - done.
  - right. split.
    + by apply exec_sound_app_l.
    + by apply exec_sound_app_r.
  Unshelve. all: try apply _.
Qed.

End proof.
