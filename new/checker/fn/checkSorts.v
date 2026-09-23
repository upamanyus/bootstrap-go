(** [checker.checkSorts] (checker/match.go): phase 0 of [checkDisjunct].
    Every atom must be well-sorted under the *declared* logical variables
    [vars], the disjunct's pattern variables, and the sort of the path's
    return term (computed under the path's own variables). What the proof
    needs from it is [atom_scoped] (match_sound.v): the atoms name no logical
    variable beyond [vars], so the caller's valuation and the path's agree on
    them.

    Naming: the Go locals are [p], [d], [vars], [rok], [rs], [se], [at] and
    [fl] (and the range loop's [i]), so no Rocq variable here is called any of
    those (see NOTES.md); the path is [pth] and the declared sorts [vl]. *)
From New.checker Require Import prelude nodes disjunct disjunct_ro match_sound.
From New.checker.fn Require Import sortOfEnv SortOf atomWellSorted.

Lemma sort_code_default os : sort_code (default SInt os) = osort_code os.
Proof. by destruct os. Qed.

Lemma atom_well_sorted_scoped E a :
  atom_well_sorted E (Some a) = true → atom_scoped (length (se_vars E)) a.
Proof.
  destruct a as [| | | |x|x v]; simpl; try discriminate.
  - destruct (sort_of E x) as [[]|] eqn:Hx; try discriminate. intros _.
    by eapply sort_of_pvars.
  - destruct (sort_of E x) as [[]|] eqn:Hx; try discriminate.
    destruct (sort_of E v) as [s|] eqn:Hv; try discriminate. intros _.
    split; by eapply sort_of_pvars.
Qed.

Lemma scoped_step (k0 : nat) (atms : list cassn) (k : nat) (acur : cassn) :
  atms !! k = Some acur →
  (∀ j a, (j < k)%nat → atms !! j = Some a → atom_scoped k0 a) →
  atom_scoped k0 acur →
  (∀ j a, (j < S k)%nat → atms !! j = Some a → atom_scoped k0 a).
Proof.
  intros Hk Hpre Hcur j a Hj Ha. destruct (decide (j = k)) as [->|Hne].
  - rewrite Hk in Ha. by injection Ha as <-.
  - apply (Hpre j a); [lia|done].
Qed.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

Lemma wp_checkSorts (pth : checker.Path.t) (sp : spath) (ld : loc) (dj : cdisjunct)
      (sv : slice.t) (vl : list sort) :
  {{{ is_pkg_init checker ∗ is_path pth sp ∗ is_disjunct_ro ld dj ∗ is_sorts sv vl }}}
    @! checker.checkSorts #pth #ld #sv
  {{{ (lf : loc), RET #lf;
      is_path pth sp ∗ ⌜lf = null → ∀ a, a ∈ d_atoms dj → atom_scoped (length vl) a⌝ }}}.
Proof.
  wp_start as "(Hpath & #Hdj & #Hsv)".
  iDestruct "Hpath" as "[#Hret Hst]".
  iDestruct "Hst" as (hs cs vs) "(Hstl & Hheap & Hcond & #Hvars)".
  iDestruct "Hdj" as (sp' sok sa lfl las) "(#Hld & #Hsp & #Hsok & #Hsa & #Has & %Hpl & %Hfail)".
  iDestruct (big_sepL2_length with "Has") as %Hlen2.
  iDestruct (own_slice_len with "Hsa") as %Hlena.
  wp_auto.
  wp_apply (wp_SortOf vs _ (svars (pst sp)) (Some (pret sp)) with "[$Hvars]").
  { cbn [is_oterm]. iFrame "#". }
  try wp_auto.
  wp_alloc lse as "Hse".
  wp_auto.
  iPersist "Hse".
  set (os := sort_of (vars_env (svars (pst sp))) (pret sp)).
  set (E := disjunct_env vl dj (default SInt os) (osort_ok os)).
  iAssert (is_sortenv DfracDiscarded lse E) as "#Henv".
  { iExists sv, sp', sok. rewrite /E /disjunct_env /= sort_code_default. iFrame "#". }
  assert (sort_env_wf E) as HE by (rewrite /sort_env_wf /E /disjunct_env /=; done).
  iAssert (∃ (k : w64) (lcur : loc),
      "i" ∷ i_ptr ↦ k ∗
      "at" ∷ at_ptr ↦ lcur ∗
      "%Hk" ∷ ⌜0 ≤ sint.Z k ≤ length las⌝ ∗
      "%Hpre" ∷ ⌜∀ j a, (j < sint.nat k)%nat → d_atoms dj !! j = Some a →
                  atom_scoped (length vl) a⌝)%I
    with "[i at]" as "HI".
  { iFrame. iPureIntro. split; first word. intros j a Hj. word. }
  wp_for "HI".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem las (sint.nat k) as lcur'.
    list_elem (d_atoms dj) (sint.nat k) as acur.
    iDestruct (big_sepL2_lookup with "Has") as "#Hcur"; [done|done|].
    wp_apply (wp_load_slice_index with "[$Hsa]"); [word|done|].
    iIntros "_".
    wp_auto.
    wp_apply (wp_atomWellSorted DfracDiscarded lse lcur' E (Some acur) with "[]").
    { cbn [is_oassn]. iFrame "#". done. }
    iIntros (lf) "[_ %Hlf]".
    wp_auto.
    wp_if_destruct.
    + (* the atom is well-sorted *)
      assert (atom_well_sorted E (Some acur) = true) as Hws by naive_solver.
      pose proof (atom_well_sorted_scoped _ _ Hws) as Hsc.
      wp_for_post. iFrame. iPureIntro. split; first word.
      replace (sint.nat (word.add k (W64 1))) with (S (sint.nat k)) by word.
      by eapply scoped_step.
    + try wp_auto. wp_for_post. iApply "HΦ". iFrame "∗#". iPureIntro. done.
  - try wp_auto. iApply "HΦ". iFrame "∗#". iPureIntro. intros _ a Ha.
    apply list_elem_of_lookup in Ha as [j Hj].
    apply (Hpre j a); last done.
    apply lookup_lt_Some in Hj. word.
Qed.

End proof.
