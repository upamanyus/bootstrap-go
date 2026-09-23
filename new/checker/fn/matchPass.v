(** [checker.matchPass] (checker/match.go): one pass of phase 1 over the
    points-to atoms not resolved yet. It preserves [phase1_inv]
    (match_sound.v) and returns how many atoms it resolved.

    Naming: the Go locals are [p], [d], [subst], [used], [done], [n], [i],
    [at], [fl] and [ok], so no Rocq variable here is called any of those (see
    NOTES.md); the path is [pth]. Since the Go function has its own [i], the
    range loop's index is allocated by hand. *)
From New.checker Require Import prelude nodes disjunct disjunct_ro match_sound.
From New.checker.fn Require Import instantiate countPointsTo matchAtom.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_matchPass (pth : checker.Path.t) (sp : spath) (ld : loc) (dj : cdisjunct)
      (ss : slice.t) (σ : list (option term)) (su : slice.t) (us : list bool)
      (sdn : slice.t) (dn : list bool) :
  {{{ is_pkg_init checker ∗ is_path pth sp ∗ is_disjunct_ro ld dj ∗
      is_subst ss σ ∗ su ↦* us ∗ sdn ↦* dn ∗
      ⌜phase1_inv (sheap (pst sp)) (d_atoms dj) (d_pats dj) (d_pat_ok dj)
         (svars (pst sp)) (pret sp) σ us dn⌝ }}}
    @! checker.matchPass #pth #ld #ss #su #sdn
  {{{ (cnt : w64) (lf : loc), RET (#cnt, #lf);
      is_path pth sp ∗
      ∃ σ' us' dn', is_subst ss σ' ∗ su ↦* us' ∗ sdn ↦* dn' ∗
        ⌜lf = null →
           phase1_inv (sheap (pst sp)) (d_atoms dj) (d_pats dj) (d_pat_ok dj)
             (svars (pst sp)) (pret sp) σ' us' dn' ∧
           (undone (d_atoms dj) dn' + uint.nat cnt)%nat = undone (d_atoms dj) dn⌝ }}}.
Proof.
  wp_start as "(Hpath & #Hdj & Hsub & Hus & Hdn & %Hinv)".
  iPoseProof "Hdj" as "Hdj'".
  iDestruct "Hdj'" as (sp' sok sa lfl las) "(#Hld & #Hsp & #Hsok & #Hsa & #Has & %Hpl & %Hfail)".
  iDestruct (big_sepL2_length with "Has") as %Hlen2.
  iDestruct (own_slice_len with "Hsa") as %Hlena.
  wp_auto.
  wp_alloc ridx as "Hridx".
  wp_auto.
  iAssert (∃ (k cnt : w64) (lcur : loc) (σk : list (option term)) (usk dnk : list bool),
      "i" ∷ i_ptr ↦ k ∗
      "Hridx" ∷ ridx ↦ k ∗
      "n" ∷ n_ptr ↦ cnt ∗
      "at" ∷ at_ptr ↦ lcur ∗
      "Hsub" ∷ is_subst ss σk ∗
      "Hus" ∷ su ↦* usk ∗
      "Hdn" ∷ sdn ↦* dnk ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ≤ length las⌝ ∗
      "%Hcnt" ∷ ⌜uint.Z cnt ≤ sint.Z k⌝ ∗
      "%Hinvk" ∷ ⌜phase1_inv (sheap (pst sp)) (d_atoms dj) (d_pats dj) (d_pat_ok dj)
                    (svars (pst sp)) (pret sp) σk usk dnk⌝ ∗
      "%Hund" ∷ ⌜(undone (d_atoms dj) dnk + uint.nat cnt)%nat = undone (d_atoms dj) dn⌝)%I
    with "[i Hridx n at Hsub Hus Hdn]" as "HI".
  { iFrame. iPureIntro. split_and!; try done; try word. }
  wp_for "HI".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem las (sint.nat k) as lcur'.
    list_elem (d_atoms dj) (sint.nat k) as acur.
    iDestruct (big_sepL2_lookup with "Has") as "#Hcur"; [done|done|].
    wp_apply (wp_load_slice_index with "[$Hsa]"); [word|done|].
    iIntros "_".
    iDestruct (is_assn_node with "Hcur") as (lL lR lX lY) "(_ & #Hnode & _)".
    wp_auto.
    rewrite is_pts_code.
    destruct (is_pts acur) eqn:Hpts.
    2:{ wp_auto. wp_for_post. iFrame. iPureIntro. split_and!; try done; word. }
    destruct (is_pts_inv _ Hpts) as (x & v & ->).
    destruct Hinvk as [Hlσ Hlu Hld Hwf Hmap].
    wp_auto.
    iDestruct (own_slice_len with "Hdn") as %Hlendn.
    list_elem dnk (sint.nat k) as dcur.
    rewrite -> decide_True; last word.
    wp_apply (wp_load_slice_index with "[$Hdn]"); [word|done|].
    iIntros "Hdn".
    destruct dcur.
    { wp_auto. wp_for_post. iFrame. iPureIntro. split_and!; try done; try word; by split. }
    wp_auto.
    wp_apply (wp_matchAtom pth sp ld dj lcur' x v ss σk su usk with "[$Hpath $Hsub $Hus]").
    { iFrame "#%". }
    iIntros (okb lf) "(Hpath & %σ' & %us' & Hsub & Hus & %Hls & %Hstep)".
    wp_auto.
    wp_if_destruct.
    2:{ (* matchAtom failed *)
      try wp_auto. wp_for_post. iApply "HΦ". iFrame. iPureIntro. done. }
    specialize (Hstep eq_refl).
    destruct okb.
    + (* resolved: mark it done *)
      wp_auto.
      rewrite -> decide_True; last word.
      try wp_auto.
      wp_apply (wp_store_slice_index with "[$Hdn]"); first (iPureIntro; word).
      iIntros "Hdn".
      wp_auto. wp_for_post. iFrame.
      iPureIntro. split; [word|]. split; [word|]. split.
      * eapply phase1_inv_step; [by split|done|done|done].
      * pose proof (undone_insert _ _ _ _ _ Hacur_lookup Hdcur_lookup) as Hu.
        rewrite -Hund. rewrite -Hu.
        replace (Z.to_nat (sint.Z k)) with (sint.nat k) by word.
        word.
    + wp_auto. wp_for_post. iFrame.
      iPureIntro. split; [word|]. split; [word|]. split; last done.
      eapply phase1_inv_skip; [by split|done].
  - (* the pass is over *)
    try wp_auto. iApply "HΦ". iFrame. iPureIntro. intros _. done.
Qed.

End proof.
