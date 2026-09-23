(** [checker.matchAtom] (checker/match.go): try to resolve one points-to
    atom [x ↦ v] against the path's heap. What a [nil] failure establishes is
    [atom_step] (match_sound.v).

    Naming: the Go locals are [p], [d], [at], [subst], [used], [l], [ok], [j]
    and [fl], so no Rocq variable here is called any of those (see
    NOTES.md); the path is [pth]. *)
From New.checker Require Import prelude nodes disjunct disjunct_ro match_sound.
From New.checker.fn Require Import instantiate hasPat findCell termEq sortOfEnv SortOf matchTerm.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_matchAtom (pth : checker.Path.t) (sp : spath) (ld : loc) (dj : cdisjunct)
      (lat : loc) (x v : term) (ss : slice.t) (σ : list (option term))
      (su : slice.t) (us : list bool) :
  {{{ is_pkg_init checker ∗ is_path pth sp ∗ is_disjunct_ro ld dj ∗
      is_assn lat (CAPointsTo x v) ∗ is_subst ss σ ∗ ⌜length σ = length (d_pats dj)⌝ ∗
      su ↦* us ∗ ⌜length us = length (sheap (pst sp))⌝ }}}
    @! checker.matchAtom #pth #ld #lat #ss #su
  {{{ (okb : bool) (lf : loc), RET (#okb, #lf);
      is_path pth sp ∗
      ∃ σ' us', is_subst ss σ' ∗ su ↦* us' ∗
        ⌜length σ' = length σ ∧ length us' = length us⌝ ∗
        ⌜lf = null → atom_step (sheap (pst sp)) (d_pats dj) (d_pat_ok dj)
                       (svars (pst sp)) (pret sp) x v σ us okb σ' us'⌝ }}}.
Proof.
  wp_start as "(Hpath & #Hdj & #Hat & Hsub & %Hlσ & Hus & %Hlus)".
  iDestruct "Hpath" as "[#Hret Hst]".
  iDestruct "Hst" as (hs cs vs) "(Hstl & Hheap & Hcond & #Hvars)".
  iDestruct "Hat" as (lx ly) "(#Hatn & #Hx & #Hv)".
  wp_auto.
  wp_apply (wp_instantiate_ret lx ss _ (Some x) σ (pret sp) with "[$Hsub]").
  { iFrame "#". }
  iIntros (ll) "[Hsub #Hll]".
  cbn [oinstantiate_t].
  destruct (inst_Some_r x σ (Some (pret sp))) as [y Hy]; first by eexists.
  rewrite Hy.
  wp_auto.
  wp_apply (wp_hasPat ll (Some y) with "[$]").
  cbn [ohas_pat].
  destruct (has_pat y) eqn:Hpy.
  { (* the location is not resolved yet *)
    wp_auto. iApply "HΦ". iFrame "∗#". iPureIntro. split; first done.
    intros _. left. done. }
  wp_auto.
  iDestruct "Hheap" as (cells) "[Hhs #Hcells]".
  iDestruct (big_sepL2_length with "Hcells") as %Hlenc.
  iDestruct (own_slice_len with "Hhs") as %Hlenh.
  iDestruct (own_slice_len with "Hus") as %Hlenu.
  wp_apply (wp_findCell hs su (sheap (pst sp)) us ll y with "[Hhs Hus]").
  { lia. }
  { iFrame "∗#". }
  iIntros (idx okb) "(Hheap & Hus & %Hok & %Hidx)".
  destruct (find_cell (sheap (pst sp)) us y 0) as [jj|] eqn:Hfc.
  2:{ (* no free cell at that location *)
    rewrite bool_decide_eq_false_2 in Hok; last naive_solver. subst okb.
    wp_auto. wp_alloc lf as "Hf".
    iDestruct (typed_pointsto_not_null with "Hf") as %Hnn.
    wp_auto. iApply "HΦ". iFrame "∗#". iPureIntro. split; first done.
    intros ?. done. }
  rewrite bool_decide_eq_true_2 in Hok; last done. subst okb.
  specialize (Hidx jj eq_refl).
  destruct (find_cell_Some _ _ _ _ _ Hfc) as (c & Hc & Huj & Hcl).
  rewrite Nat.sub_0_r in Hc.
  assert (jj < length (sheap (pst sp)))%nat as Hjj by (by eapply lookup_lt_Some).
  wp_auto.
  iDestruct "Hheap" as (cells') "[Hhs #Hcells']".
  iDestruct (big_sepL2_length with "Hcells'") as %Hlenc'.
  iDestruct (own_slice_len with "Hhs") as %Hlenh'.
  list_elem cells' jj as cc.
  iDestruct (big_sepL2_lookup with "Hcells'") as "#Hcc"; [done|done|].
  iDestruct "Hcc" as "[Hccl Hccv]".
  rewrite -> decide_True; last word.
  iDestruct (own_slice_elem_acc (sint.Z idx) with "Hhs") as "[Hel Hclose]".
  { word. }
  { replace (Z.to_nat (sint.Z idx)) with jj by word. done. }
  wp_auto.
  iDestruct ("Hclose" with "Hel") as "Hhs".
  rewrite list_insert_id; last (replace (Z.to_nat (sint.Z idx)) with jj by word; done).
  wp_apply (wp_matchTerm ly cc.(checker.Cell.Val') (Some v) (Some (cval c)) ss σ ld dj
              vs (svars (pst sp)) pth.(checker.Path.Ret') (pret sp) with "[Hsub]").
  { cbn [is_oterm]. iFrame "∗#%". }
  iIntros (lf1) "Hp1".
  iDestruct "Hp1" as (σ1) "(Hsub & %Hl1 & [[-> %Hm1]|Hf1])".
  2:{ (* the value does not match: record the atom in the failure *)
    iDestruct "Hf1" as (fv) "Hf1".
    iDestruct (typed_pointsto_not_null with "Hf1") as %Hnn.
    wp_auto. wp_if_destruct; first done.
    iApply "HΦ". iFrame "∗#". iPureIntro. split; first done. done. }
  wp_auto.
  rewrite -> decide_True; last word.
  try wp_auto.
  wp_apply (wp_store_slice_index with "[$Hus]"); first (iPureIntro; word).
  iIntros "Hus".
  replace (Z.to_nat (sint.Z idx)) with jj by word.
  wp_auto.
  iApply "HΦ". iFrame "∗#". iPureIntro. split.
  { rewrite length_insert. done. }
  intros _. right. split; first done.
  exists jj, c. split_and!; try done.
  - by rewrite Hcl.
  - by rewrite Hcl.
  - rewrite -Huj. apply list_lookup_lookup_total_lt. lia.
Qed.

End proof.
