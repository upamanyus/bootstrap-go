(** [checker.checkPure] (checker/match.go): phase 2 of [checkDisjunct]. Each
    pure atom, instantiated with the substitution phase 1 built, must mention
    no pattern variable and be justified by the path condition: [pure_ok]
    (match_sound.v).

    Naming: the Go locals are [p], [d], [subst], [at] and [t] (and the range
    loop's [i]), so no Rocq variable here is called any of those (see
    NOTES.md); the path is [pth]. *)
From New.checker Require Import prelude nodes disjunct disjunct_ro match_sound.
From New.checker.fn Require Import instantiate hasPat condHolds countPointsTo.

Lemma pure_ok_step (pc : list term) (atms : list cassn) (σ : list (option term)) (r : term)
    (k : nat) (acur : cassn) :
  atms !! k = Some acur →
  (∀ j x, (j < k)%nat → atms !! j = Some (CAPure x) →
     ∃ y, instantiate_t x σ (Some r) = Some y ∧ has_pat y = false ∧ cond_holds pc (Some y) = true) →
  (∀ x, acur = CAPure x →
     ∃ y, instantiate_t x σ (Some r) = Some y ∧ has_pat y = false ∧ cond_holds pc (Some y) = true) →
  (∀ j x, (j < S k)%nat → atms !! j = Some (CAPure x) →
     ∃ y, instantiate_t x σ (Some r) = Some y ∧ has_pat y = false ∧ cond_holds pc (Some y) = true).
Proof.
  intros Hk Hpre Hcur j x Hj Hx. destruct (decide (j = k)) as [->|Hne].
  - rewrite Hk in Hx. injection Hx as ->. by apply Hcur.
  - apply (Hpre j x); [lia|done].
Qed.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_checkPure (pth : checker.Path.t) (sp : spath) (ld : loc) (dj : cdisjunct)
      (ss : slice.t) (σ : list (option term)) :
  {{{ is_pkg_init checker ∗ is_path pth sp ∗ is_disjunct_ro ld dj ∗ is_subst ss σ }}}
    @! checker.checkPure #pth #ld #ss
  {{{ (lf : loc), RET #lf;
      is_path pth sp ∗ is_subst ss σ ∗
      ⌜lf = null → pure_ok (spc (pst sp)) (d_atoms dj) σ (pret sp)⌝ }}}.
Proof.
  wp_start as "(Hpath & #Hdj & Hsub)".
  iDestruct "Hpath" as "[#Hret Hst]".
  iDestruct "Hst" as (hs cs vs) "(Hstl & Hheap & Hcond & #Hvars)".
  iDestruct "Hdj" as (sp' sok sa lf las) "(#Hld & #Hsp & #Hsok & #Hsa & #Has & %Hpl & %Hfail)".
  iDestruct (big_sepL2_length with "Has") as %Hlen2.
  iDestruct (own_slice_len with "Hsa") as %Hlena.
  wp_auto.
  iAssert (∃ (k : w64) (lcur : loc),
      "i" ∷ i_ptr ↦ k ∗
      "at" ∷ at_ptr ↦ lcur ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ≤ length las⌝ ∗
      "%Hpre" ∷ ⌜∀ j x, (j < sint.nat k)%nat → d_atoms dj !! j = Some (CAPure x) →
         ∃ y, instantiate_t x σ (Some (pret sp)) = Some y ∧ has_pat y = false ∧
              cond_holds (spc (pst sp)) (Some y) = true⌝)%I
    with "[i at]" as "HI".
  { iFrame. iPureIntro. split; first word. intros j x Hj. word. }
  wp_for "HI".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem las (sint.nat k) as lcur'.
    list_elem (d_atoms dj) (sint.nat k) as acur.
    iDestruct (big_sepL2_lookup with "Has") as "#Hcur"; [done|done|].
    wp_apply (wp_load_slice_index with "[$Hsa]"); [word|done|].
    iIntros "_".
    iDestruct (is_assn_node with "Hcur") as (lL lR lX lY) "(_ & #Hnode & _ & _ & #HX & _)".
    wp_auto.
    rewrite is_pure_code.
    destruct (is_pure acur) eqn:Hpure.
    + destruct (is_pure_inv _ Hpure) as [x ->]. cbn [assn_x].
      wp_auto.
      wp_apply (wp_instantiate_ret lX ss _ (Some x) σ (pret sp) with "[$Hsub]").
      { iFrame "#". }
      iIntros (lt) "[Hsub #Hlt]".
      cbn [oinstantiate_t].
      destruct (inst_Some_r x σ (Some (pret sp))) as [y Hy]; first by eexists.
      rewrite Hy.
      wp_auto.
      wp_apply (wp_hasPat lt (Some y) with "[$]").
      cbn [ohas_pat].
      destruct (has_pat y) eqn:Hpy.
      * wp_auto. wp_alloc lf' as "Hf".
        iDestruct (typed_pointsto_not_null with "Hf") as %Hnn.
        wp_auto. wp_for_post. iApply "HΦ". iFrame "∗#". iPureIntro. done.
      * wp_auto.
        wp_apply (wp_condHolds cs (spc (pst sp)) lt (Some y) with "[$Hcond $Hlt]").
        iIntros "Hcond".
        destruct (cond_holds (spc (pst sp)) (Some y)) eqn:Hch.
        -- wp_auto. wp_for_post. iFrame. iPureIntro. split; first word.
           replace (sint.nat (word.add k (W64 1))) with (S (sint.nat k)) by word.
           eapply pure_ok_step; [done|done|]. intros x' [= <-]. eauto.
        -- wp_auto. wp_alloc lf' as "Hf".
           iDestruct (typed_pointsto_not_null with "Hf") as %Hnn.
           wp_auto. wp_for_post. iApply "HΦ". iFrame "∗#". iPureIntro. done.
    + wp_auto. wp_for_post. iFrame. iPureIntro. split; first word.
      replace (sint.nat (word.add k (W64 1))) with (S (sint.nat k)) by word.
      eapply pure_ok_step; [done|done|]. intros x' ->. done.
  - try wp_auto. iApply "HΦ". iFrame "∗#". iPureIntro. intros _ j x Hx.
    apply (Hpre j x); last done.
    apply lookup_lt_Some in Hx. word.
Qed.

End proof.
