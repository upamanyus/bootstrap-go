(** [checker.matchTerm] (checker/match.go): match a pattern term against a
    path term, binding pattern variables into [subst]. What a [nil] result
    establishes is [match_rel] (match_sound.v); a failure is a freshly
    allocated [Failure] the caller owns (matchAtom writes its [Atom] field).

    Naming: the Go locals are [pat], [act], [subst], [d], [vars], [ret], [s],
    [ok] and [fl], so no Rocq variable here is called any of those (see
    NOTES.md). *)
From New.checker Require Import prelude nodes disjunct disjunct_ro match_sound.
From New.checker.fn Require Import instantiate termEq sortOfEnv SortOf.

Lemma is_tpat_inv x : is_tpat x = true → ∃ n, x = TPat n.
Proof. destruct x; try discriminate. eauto. Qed.
Lemma is_tresult_inv x : is_tresult x = true → x = TResult.
Proof. destruct x; try discriminate. eauto. Qed.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Definition match_post (ss : slice.t) (σ : list (option term)) (pats : list sort)
    (pok : list bool) (PV : list sort) (r : term) (op oa : option term) (lf : loc) : iProp Σ :=
  ∃ σ', is_subst ss σ' ∗ ⌜length σ' = length σ⌝ ∗
    (⌜lf = null ∧ match_rel pats pok PV r op oa σ σ'⌝ ∨ ∃ fv : checker.Failure.t, lf ↦ fv).

Lemma wp_matchTerm (lp lq : loc) (op oa : option term) (ss : slice.t)
      (σ : list (option term)) (ld : loc) (dj : cdisjunct) (sv : slice.t)
      (PV : list sort) (lr : loc) (r : term) :
  {{{ is_pkg_init checker ∗ is_oterm lp op ∗ is_oterm lq oa ∗ is_subst ss σ ∗
      ⌜length σ = length (d_pats dj)⌝ ∗ is_disjunct_ro ld dj ∗
      sv ↦*□ (sort_code <$> PV) ∗ is_term lr r }}}
    @! checker.matchTerm #lp #lq #ss #ld #sv #lr
  {{{ (lf : loc), RET #lf; match_post ss σ (d_pats dj) (d_pat_ok dj) PV r op oa lf }}}.
Proof.
  iLöb as "IH" forall (lp lq op oa σ).
  wp_start as "(#Hop & #Hoa & Hsub & %Hlσ & #Hdj & #Hsv & #Hr)".
  iDestruct (is_oterm_null with "Hop") as %Hnp.
  iDestruct (is_oterm_null with "Hoa") as %Hna.
  wp_auto.
  wp_if_destruct.
  { (* [pat] is nil *)
    assert (op = None) as -> by naive_solver.
    wp_if_destruct.
    - assert (oa = None) as -> by naive_solver.
      try wp_auto. iApply "HΦ". iExists σ. iFrame "Hsub". iSplit; first done. iLeft. iPureIntro.
      split_and!; [done|constructor].
    - wp_alloc lf as "Hf". try wp_auto. iApply "HΦ". iExists σ. iFrame "Hsub". iSplit; first done. iRight. by iFrame. }
  destruct op as [x|]; last naive_solver.
  iDestruct (is_term_node with "Hop") as (lxa lxb lxc) "(%Hwx & #Hxn & #Hxa & #Hxb & #Hxc)".
  try wp_auto.
  iDestruct "Hdj" as (sp sok sa lfl las) "(#Hld & #Hsp & #Hsok & #Hsa & #Has & %Hpl & %Hfail)".
  rewrite is_tpat_code.
  destruct (is_tpat x) eqn:Hpx.
  { (* [pat] is a pattern variable *)
    destruct (is_tpat_inv _ Hpx) as [m ->]. cbn [term_num term_idx_wf] in *.
    rewrite /idx_wf in Hwx.
    iDestruct "Hsub" as (ls) "[Hs #Hls]".
    iDestruct (big_sepL2_length with "Hls") as %Hlen2.
    iDestruct (own_slice_len with "Hs") as %Hlen.
    iDestruct (own_slice_len with "Hsok") as %Hlenok.
    iDestruct (own_slice_len with "Hsp") as %Hlenp. rewrite length_fmap in Hlenp.
    wp_auto.
    wp_if_destruct.
    { (* out of range *)
      wp_alloc lf as "Hf". try wp_auto. iApply "HΦ". iExists σ.
      iSplitL "Hs"; first by iFrame "Hs Hls". iSplit; first done. iRight. by iFrame. }
    assert (m < length σ)%nat as Hm by word.
    list_elem (d_pat_ok dj) m as okm.
    rewrite -> decide_True; last word.
    wp_apply (wp_load_slice_index with "[$Hsok]"); [word| by replace (sint.nat (W64 m)) with m by word |].
    iIntros "_".
    destruct okm.
    2:{ (* not a declared pattern variable *)
      wp_auto. wp_alloc lf as "Hf". try wp_auto. iApply "HΦ". iExists σ.
      iSplitL "Hs"; first by iFrame "Hs Hls". iSplit; first done. iRight. by iFrame. }
    wp_auto.
    list_elem ls m as li.
    list_elem σ m as oi.
    iDestruct (big_sepL2_lookup with "Hls") as "#Hli"; [done|done|].
    iDestruct (is_oterm_null with "Hli") as %Hlin.
    rewrite -> decide_True; last word.
    wp_apply (wp_load_slice_index with "[$Hs]"); [word| by replace (sint.nat (W64 m)) with m by word |].
    iIntros "Hs".
    wp_auto.
    wp_if_destruct.
    - (* unbound so far: bind it, if the sorts agree *)
      assert (oi = None) as Hoi by naive_solver. subst oi.
      wp_apply (wp_SortOf sv lq PV oa with "[$Hsv $Hoa]").
      destruct (osort_of (vars_env PV) oa) as [s0|] eqn:Hso;
        cbn [osort_code osort_ok].
      2:{ wp_auto. wp_alloc lf as "Hf". try wp_auto. iApply "HΦ". iExists σ.
          iSplitL "Hs"; first by iFrame "Hs Hls". iSplit; first done. iRight. by iFrame. }
      destruct oa as [t0|]; last done. cbn [osort_of] in Hso.
      list_elem (d_pats dj) m as pm.
      wp_auto.
      rewrite -> decide_True; last word.
      wp_apply (wp_load_slice_index with "[$Hsp]"); [word| rewrite list_lookup_fmap; replace (sint.nat (W64 m)) with m by word; rewrite Hpm_lookup //|].
      iIntros "_".
      wp_auto.
      destruct (decide (s0 = pm)) as [<-|Hne].
      2:{ rewrite (bool_decide_eq_false_2 (sort_code s0 = sort_code pm)); last first.
          { intros Heq. by apply sort_code_inj in Heq. }
          wp_auto. wp_alloc lf as "Hf". try wp_auto. iApply "HΦ". iExists σ.
          iSplitL "Hs"; first by iFrame "Hs Hls". iSplit; first done. iRight. by iFrame. }
      rewrite (bool_decide_eq_true_2 (sort_code s0 = sort_code s0)) //.
      wp_auto.
      rewrite -> decide_True; last word.
      try wp_auto.
      wp_apply (wp_store_slice_index with "[$Hs]"); first (iPureIntro; word).
      iIntros "Hs".
      replace (Z.to_nat (sint.Z (W64 m))) with m by word.
      wp_auto.
      iApply "HΦ". iExists (<[m := Some t0]> σ).
      iSplitL "Hs".
      { iExists (<[m := lq]> ls). iFrame "Hs".
        iDestruct (big_sepL2_insert_acc with "Hls") as "[_ Hins]"; [done|done|].
        iApply ("Hins" with "Hoa"). }
      iSplit; first by rewrite length_insert.
      iLeft. iPureIntro. split; first done.
      by eapply MR_pat_new.
    - (* already bound: the two terms must agree *)
      destruct oi as [y|]; last naive_solver.
      rewrite -> decide_True; last word.
      wp_apply (wp_load_slice_index with "[$Hs]"); [word| by replace (sint.nat (W64 m)) with m by word |].
      iIntros "Hs".
      wp_auto.
      wp_apply (wp_termEq li lq (Some y) oa with "[$Hli $Hoa]").
      destruct (decide (Some y = oa)) as [<-|Hne].
      + rewrite (bool_decide_eq_true_2 (Some y = Some y)) //.
        wp_auto. iApply "HΦ". iExists σ.
        iSplitL "Hs"; first by iFrame "Hs Hls". iSplit; first done.
        iLeft. iPureIntro. split; first done. by apply MR_pat_old.
      + rewrite (bool_decide_eq_false_2 (Some y = oa)) //.
        cbn [negb]. wp_pures. try wp_auto.
        rewrite -> decide_True; last word.
        wp_apply (wp_load_slice_index with "[$Hs]"); [word| by replace (sint.nat (W64 m)) with m by word |].
        iIntros "Hs". wp_auto.
        wp_alloc lf as "Hf". try wp_auto. iApply "HΦ". iExists σ.
        iSplitL "Hs"; first by iFrame "Hs Hls". iSplit; first done. iRight. by iFrame. }
  try wp_auto.
  rewrite is_tresult_code.
  destruct (is_tresult x) eqn:Hrx.
  { (* [pat] is [ret]: match the return term instead *)
    rewrite (is_tresult_inv _ Hrx).
    try wp_auto.
    wp_apply ("IH" $! lr lq (Some r) oa σ with "[Hsub]").
    { cbn [is_oterm]. iFrame "∗#%". }
    iIntros (lf) "Hpost".
    try wp_auto.
    iApply "HΦ".
    iDestruct "Hpost" as (σ') "(Hs & %Hl & [[%Hn %Hm]|Hf])".
    - iExists σ'. iFrame "Hs". iSplit; first done. iLeft. iPureIntro.
      split; first done. by constructor.
    - iExists σ'. iFrame "Hs". iSplit; first done. iRight. done. }
  try wp_auto.
  wp_if_destruct.
  { (* [act] is nil *)
    wp_alloc lf as "Hf". try wp_auto. iApply "HΦ". iExists σ. iFrame "Hsub".
    iSplit; first done. iRight. by iFrame. }
  destruct oa as [y|]; last naive_solver.
  iDestruct (is_term_node with "Hoa") as (lya lyb lyc) "(%Hwy & #Hyn & #Hya & #Hyb & #Hyc)".
  try wp_auto.
  destruct (decide (term_code x = term_code y)) as [Hc|Hc].
  2:{ rewrite (bool_decide_eq_false_2 (term_code x = term_code y)) //.
      wp_auto. wp_alloc lf as "Hf". try wp_auto. iApply "HΦ". iExists σ. iFrame "Hsub".
      iSplit; first done. iRight. by iFrame. }
  rewrite (bool_decide_eq_true_2 (term_code x = term_code y)) //.
  wp_auto.
  destruct (decide (term_num x = term_num y)) as [Hn|Hn].
  2:{ rewrite (bool_decide_eq_false_2 (term_num x = term_num y)) //.
      wp_auto. wp_alloc lf as "Hf". try wp_auto. iApply "HΦ". iExists σ. iFrame "Hsub".
      iSplit; first done. iRight. by iFrame. }
  rewrite (bool_decide_eq_true_2 (term_num x = term_num y)) //.
  wp_auto.
  (* the three children, left to right *)
  wp_apply ("IH" $! lxa lya (term_a x) (term_a y) σ with "[Hsub]").
  { iFrame "∗#%". }
  iIntros (lf1) "Hp1".
  iDestruct "Hp1" as (σ1) "(Hsub & %Hl1 & [[-> %Hm1]|Hf1])".
  2:{ iDestruct "Hf1" as (fv) "Hf1".
      iDestruct (typed_pointsto_not_null with "Hf1") as %Hnn.
      wp_auto. wp_if_destruct; first done.
      try wp_auto. iApply "HΦ". iExists σ1. iFrame "Hsub". iSplit; first done.
      iRight. by iFrame. }
  wp_auto.
  wp_apply ("IH" $! lxb lyb (term_b x) (term_b y) σ1 with "[Hsub]").
  { iFrame "∗#". iPureIntro. split_and!; try done. lia. }
  iIntros (lf2) "Hp2".
  iDestruct "Hp2" as (σ2) "(Hsub & %Hl2 & [[-> %Hm2]|Hf2])".
  2:{ iDestruct "Hf2" as (fv) "Hf2".
      iDestruct (typed_pointsto_not_null with "Hf2") as %Hnn.
      wp_auto. wp_if_destruct; first done.
      try wp_auto. iApply "HΦ". iExists σ2. iFrame "Hsub". iSplit; first (iPureIntro; lia).
      iRight. by iFrame. }
  wp_auto.
  wp_apply ("IH" $! lxc lyc (term_c x) (term_c y) σ2 with "[Hsub]").
  { iFrame "∗#". iPureIntro. split_and!; try done. lia. }
  iIntros (lf3) "Hp3".
  try wp_auto.
  iApply "HΦ".
  iDestruct "Hp3" as (σ3) "(Hsub & %Hl3 & [[-> %Hm3]|Hf3])".
  - iExists σ3. iFrame "Hsub". iSplit; first (iPureIntro; lia).
    iLeft. iPureIntro. split; first done. by eapply MR_node.
  - iExists σ3. iFrame "Hsub". iSplit; first (iPureIntro; lia).
    iRight. done.
Qed.

End proof.
