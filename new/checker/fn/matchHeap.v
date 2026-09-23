(** [checker.matchHeap] (checker/match.go): phase 1 of [checkDisjunct].
    [matchPass] runs until every points-to atom is resolved; a pass that
    resolves nothing is a failure. Partial correctness: the loop maintains
    [phase1_inv] (match_sound.v), and [remaining] is the number of
    unresolved points-to atoms.

    Naming: the Go locals are [p], [d], [subst], [used], [done],
    [remaining], [fl] and [n], so no Rocq variable here is called any of
    those (see NOTES.md); the path is [pth]. *)
From New.checker Require Import prelude nodes disjunct disjunct_ro match_sound.
From New.checker.fn Require Import instantiate countPointsTo firstUnresolved matchPass.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_matchHeap (pth : checker.Path.t) (sp : spath) (ld : loc) (dj : cdisjunct)
      (ss : slice.t) :
  {{{ is_pkg_init checker ∗ is_path pth sp ∗ is_disjunct_ro ld dj ∗
      is_subst ss (replicate (length (d_pats dj)) None) }}}
    @! checker.matchHeap #pth #ld #ss
  {{{ (lf : loc), RET #lf;
      is_path pth sp ∗
      ∃ σ, is_subst ss σ ∗
        ⌜lf = null → ∃ us dn,
           phase1_inv (sheap (pst sp)) (d_atoms dj) (d_pats dj) (d_pat_ok dj)
             (svars (pst sp)) (pret sp) σ us dn ∧ undone (d_atoms dj) dn = 0%nat⌝ }}}.
Proof.
  wp_start as "(Hpath & #Hdj & Hsub)".
  iPoseProof "Hdj" as "Hdj'".
  iDestruct "Hdj'" as (sp' sok sa lfl las) "(#Hld & #Hsp & #Hsok & #Hsa & #Has & %Hpl & %Hfail)".
  iDestruct (big_sepL2_length with "Has") as %Hlen2.
  iDestruct (own_slice_len with "Hsa") as %Hlena.
  iDestruct "Hpath" as "[#Hret Hst]".
  iDestruct "Hst" as (hs cs vs) "(Hstl & Hheap & Hcond & #Hvars)".
  iDestruct "Hheap" as (cells) "[Hhs #Hcells]".
  iDestruct (big_sepL2_length with "Hcells") as %Hlenc.
  iDestruct (own_slice_len with "Hhs") as %Hlenh.
  wp_auto.
  wp_apply wp_slice_make2 as (su) "[Hus _]"; first (iPureIntro; word).
  try wp_auto.
  wp_apply wp_slice_make2 as (sdn) "[Hdn _]"; first (iPureIntro; word).
  try wp_auto.
  wp_apply (wp_countPointsTo sa DfracDiscarded las (d_atoms dj) with "[$Hsa]").
  { iModIntro. iFrame "#". }
  iIntros "_".
  iAssert (is_path pth sp) with "[Hstl Hhs Hcond]" as "Hpath".
  { iFrame "Hret". iExists hs, cs, vs. iFrame "∗#". }
  wp_auto.
  rewrite count_pts_undone.
  pose proof (phase1_inv_init (sheap (pst sp)) (d_atoms dj) (d_pats dj) (d_pat_ok dj)
                (svars (pst sp)) (pret sp)) as Hinit.
  iAssert (∃ (σk : list (option term)) (usk dnk : list bool),
      "remaining" ∷ remaining_ptr ↦ W64 (undone (d_atoms dj) dnk) ∗
      "Hsub" ∷ is_subst ss σk ∗
      "Hus" ∷ su ↦* usk ∗
      "Hdn" ∷ sdn ↦* dnk ∗
      "%Hinvk" ∷ ⌜phase1_inv (sheap (pst sp)) (d_atoms dj) (d_pats dj) (d_pat_ok dj)
                    (svars (pst sp)) (pret sp) σk usk dnk⌝)%I
    with "[remaining Hsub Hus Hdn]" as "HI".
  { replace (Z.to_nat (sint.Z hs.(slice.len))) with (length (sheap (pst sp))) by lia.
    replace (Z.to_nat (sint.Z sa.(slice.len))) with (length (d_atoms dj)) by lia.
    iExists _, _, _. iFrame "remaining Hsub Hus Hdn". done. }
  wp_for "HI".
  pose proof (undone_le (d_atoms dj) dnk) as Hule.
  wp_if_destruct.
  - try wp_auto.
    wp_apply (wp_matchPass pth sp ld dj ss σk su usk sdn dnk with "[$Hpath $Hsub $Hus $Hdn]").
    { iFrame "#%". }
    iIntros (cnt lf) "(Hpath & %σ' & %us' & %dn' & Hsub & Hus & Hdn & %Hst)".
    wp_auto.
    wp_if_destruct.
    2:{ (* the pass failed *)
      try wp_auto. wp_for_post. iApply "HΦ". iFrame. iPureIntro. done. }
    destruct (Hst eq_refl) as [Hinv' Hund'].
    wp_if_destruct.
    + (* no progress: report the first unresolved atom *)
      wp_apply (wp_firstUnresolved ld dj sdn dn' with "[$Hdj $Hdn]").
      { iPureIntro. by destruct Hinv'. }
      iIntros (lat) "Hdn".
      wp_auto. wp_alloc lf' as "Hf".
      iDestruct (typed_pointsto_not_null with "Hf") as %Hnn.
      wp_auto. wp_for_post. iApply "HΦ". iFrame. iPureIntro. done.
    + try wp_auto. wp_for_post.
      iFrame "HΦ subst d p used done Hpath".
      iExists σ', us', dn'.
      replace (word.sub (W64 (undone (d_atoms dj) dnk)) cnt)
        with (W64 (undone (d_atoms dj) dn')) by word.
      iFrame. done.
  - (* nothing left to resolve *)
    assert (undone (d_atoms dj) dnk = 0%nat) as Hz by word.
    try wp_auto. iApply "HΦ". iFrame. iPureIntro. intros _. eauto.
Qed.

End proof.
