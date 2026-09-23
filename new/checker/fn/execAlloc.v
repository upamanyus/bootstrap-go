(** [checker.execAlloc] (checker/exec.go): the [EAlloc] case of [exec].

    Runs the operand, then on each of its paths clones the state, extends its
    sort table by one [SortLoc] variable [n], and adds a cell at [TVar n]
    holding the operand's value; the new path returns [TVar n].

    Naming: the Go locals are [e], [en], [st], [tok], [fl], [ps], [out], [p],
    [st2], [n], [l], and the range loop's [i], so no Rocq variable here is
    called any of those (see NOTES.md). *)
From New.checker Require Import prelude nodes exec_spec exec_def exec_sound_c.
From New.checker.fn Require Import TypeSort State__clone heapUpdate.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_execAlloc_aux cty ce :
  (⊢ exec_like checker.exec ce) → ⊢ exec_like checker.execAlloc (CEAlloc cty ce).
Proof.
  intros Hex.
  iIntros (le lρ lst ρ sst).
  wp_start as "(#He & #Hρ & Hst & %Hwf & %Hρb)".
  iDestruct "He" as (lt la) "(#Hn & #Ht & #Ha)".
  fold (is_expr la ce).
  wp_auto.
  wp_apply (wp_TypeSort lt (Some cty) with "[$Ht]").
  try wp_auto.
  wp_apply (Hex $! la lρ lst ρ sst with "[$Hst]").
  { iFrame "#". done. }
  iIntros (sps lfl) "Hpost".
  rewrite /exec_post.
  try wp_auto.
  wp_if_destruct.
  2: { try wp_auto. iApply "HΦ".
       destruct (decide (lfl = null)); [congruence|done]. }
  destruct (decide (null = null)) as [_|]; last congruence.
  iDestruct "Hpost" as (pl) "(Hpl & %Hwfpl & %Hsnd)".
  iDestruct "Hpl" as (xs) "[Hxs Hxp]".
  iDestruct (big_sepL2_length with "Hxp") as %Hlen2.
  iDestruct (own_slice_len with "Hxs") as %Hlen.
  try wp_auto.
  iAssert (∃ (k : w64) (pcur : checker.Path.t) (so : slice.t) (os : list checker.Path.t),
      "i" ∷ i_ptr ↦ k ∗
      "p" ∷ p_ptr ↦ pcur ∗
      "out" ∷ out_ptr ↦ so ∗
      "Hos" ∷ so ↦* os ∗
      "Hcap" ∷ own_slice_cap checker.Path.t so (DfracOwn 1) ∗
      "Hosp" ∷ ([∗ list] x;q ∈ os; alloc_path <$> take (sint.nat k) pl, is_path x q) ∗
      "Hrest" ∷ ([∗ list] x;q ∈ drop (sint.nat k) xs; drop (sint.nat k) pl, is_path x q) ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ≤ length xs⌝)%I
    with "[i p out Hxp]" as "HI".
  { iFrame. iDestruct own_slice_nil as "$". iDestruct own_slice_cap_nil as "$".
    replace (sint.nat (W64 0)) with 0%nat by word.
    rewrite take_0 !drop_0 /=. iFrame "Hxp". iSplit; first done.
    iPureIntro. word. }
  wp_for "HI".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem xs (sint.nat k) as x0.
    list_elem pl (sint.nat k) as p0.
    rewrite (drop_S xs x0 (sint.nat k)) // (drop_S pl p0 (sint.nat k)) //.
    iDestruct "Hrest" as "[[#Hret Hst0] Hrest]".
    wp_apply (wp_load_slice_index with "[$Hxs]").
    { word. }
    { done. }
    iIntros "Hxs".
    wp_auto.
    wp_apply (wp_State__clone with "[$Hst0]") as (lst2) "[_ Hfr]".
    iDestruct "Hfr" as (hs cs vs) "(Hl & Hh & Hhcap & Hc & Hccap & Hv & Hvcap)".
    iDestruct (own_slice_len with "Hv") as %[Hlv Hbv].
    rewrite length_fmap in Hlv.
    assert (vs.(slice.len) = W64 (length (svars (pst p0)))) as Hvl by word.
    assert (idx_wf (length (svars (pst p0)))) as Hidx by (rewrite /idx_wf; word).
    wp_auto.
    wp_apply wp_slice_literal.
    iSplitR; first done.
    iIntros "%sl [Hsl _]".
    rewrite insert0_singleton. wp_auto.
    wp_apply (wp_slice_append vs (sort_code <$> svars (pst p0)) _ _ (DfracOwn 1)
               with "[$Hv $Hvcap $Hsl]") as (vs') "(Hv & Hvcap & _)".
    wp_alloc lterm as "Hlt".
    iEval (rewrite Hvl) in "Hlt".
    iPersist "Hlt".
    iAssert (is_term lterm (TVar (length (svars (pst p0))))) as "#Hlterm".
    { cbn [is_term]. iSplit; first done. iExact "Hlt". }
    wp_auto.
    wp_apply wp_slice_literal.
    iSplitR; first done.
    iIntros "%sl2 [Hsl2 _]".
    rewrite insert0_singleton. wp_auto.
    iDestruct "Hh" as (cells) "[Hcells #Hcellsp]".
    wp_apply (wp_slice_append hs cells _ _ (DfracOwn 1)
               with "[$Hcells $Hhcap $Hsl2]") as (hs') "(Hcells & Hhcap & _)".
    iAssert (is_state_fresh lst2 (st_alloc (pst p0) (pret p0)))
      with "[Hl Hcells Hhcap Hc Hccap Hv Hvcap]" as "Hfr".
    { iExists hs', cs, vs'. cbn [st_alloc sheap spc svars]. iFrame "Hl Hc Hccap Hhcap Hvcap".
      rewrite fmap_app. iFrame "Hv". iExists _. iFrame "Hcells".
      iApply (big_sepL2_app with "Hcellsp"). cbn. iSplit; last done.
      rewrite /is_cell /=. iFrame "#". }
    iMod (is_state_fresh_publish with "Hfr") as "Hst2".
    wp_apply wp_slice_literal.
    iSplitR; first done.
    iIntros "%sl3 [Hsl3 _]".
    rewrite insert0_singleton. wp_auto.
    wp_apply (wp_slice_append so os _ _ (DfracOwn 1)
               with "[$Hos $Hcap $Hsl3]") as (so') "(Hos & Hcap & _)".
    wp_for_post.
    iFrame "HΦ Hxs".
    iExists (word.add k (W64 1)), x0, so',
      (os ++ [checker.Path.mk lterm lst2]).
    replace (sint.nat (word.add k (W64 1))) with (S (sint.nat k)) by word.
    iFrame "i p out Hos Hcap Hrest".
    iSplitL "Hosp Hst2".
    { rewrite (take_S_r pl (sint.nat k) p0) // fmap_app.
      iApply (big_sepL2_app with "Hosp"). cbn. iSplit; last done.
      rewrite /is_path /=. iFrame "Hlterm Hst2". }
    iPureIntro. word.
  - (* the loop is over *)
    try wp_auto.
    rewrite take_ge; last lia.
    iApply "HΦ".
    destruct (decide (null = null)) as [_|]; last congruence.
    iExists (alloc_path <$> pl). iSplitL "Hos Hosp".
    { iExists os. iFrame. }
    iPureIntro. split; first by apply paths_wf_alloc.
    eapply exec_sound_alloc; [exact Hsnd|exact Hwfpl|].
    intros p1 Hp1. apply list_elem_of_fmap. by exists p1.
  Unshelve. all: try apply _.
Qed.

Lemma wp_execAlloc t e : (⊢ exec_like checker.exec e) → ⊢ exec_like checker.execAlloc (CEAlloc t e).
Proof. apply wp_execAlloc_aux. Qed.
End proof.
