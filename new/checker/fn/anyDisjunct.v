(** [checker.anyDisjunct] (checker/check.go): does path [p] satisfy some
    disjunct of the (parsed, frozen) postcondition?

    Naming: the Go locals are [p], [ds], [vars] and [d], and the range loop
    introduces [i], so no Rocq variable here is called any of those (see
    NOTES.md). *)
From New.checker Require Import prelude nodes disjunct disjunct_ro verify_def.
From New.checker.fn Require Import checkDisjunct.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The parsed postcondition, frozen: [Verify] only reads it. *)
Definition is_disjuncts_ro (s : slice.t) (djs : list cdisjunct) : iProp Σ :=
  (∃ lds : list loc, s ↦*□ lds ∗ [∗ list] ld;dj ∈ lds; djs, is_disjunct_ro ld dj)%I.

#[global] Instance is_disjuncts_ro_persistent s djs : Persistent (is_disjuncts_ro s djs).
Proof. apply _. Qed.

Lemma wp_anyDisjunct (pp : checker.Path.t) (sp : spath) (sd : slice.t)
      (djs : list cdisjunct) (svs : slice.t) (vs : list sort) :
  {{{ is_pkg_init checker ∗ is_path pp sp ∗ is_disjuncts_ro sd djs ∗ is_sorts svs vs }}}
    @! checker.anyDisjunct #pp #sd #svs
  {{{ (b : bool), RET #b;
      is_path pp sp ∗
      ⌜b = true → ∃ dj, dj ∈ djs ∧ d_fail dj = false ∧ path_sat_dj vs sp dj⌝ }}}.
Proof.
  wp_start as "(Hp & #Hds & #Hvs)".
  iDestruct "Hds" as (lds) "[Hsd Hlds]".
  iDestruct (big_sepL2_length with "Hlds") as %Hlen2.
  iDestruct (own_slice_len with "Hsd") as %Hlen.
  wp_auto.
  iAssert (∃ (n : w64) (lcur : loc),
      "i" ∷ i_ptr ↦ n ∗
      "d" ∷ d_ptr ↦ lcur ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ≤ length lds⌝)%I
    with "[i d]" as "HI".
  { iFrame. iPureIntro. word. }
  wp_for "HI".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem lds (sint.nat n) as lcur'.
    list_elem djs (sint.nat n) as dj.
    iDestruct (big_sepL2_lookup with "Hlds") as "#Hdj"; [done|done|].
    wp_apply (wp_load_slice_index with "[$Hsd]") as "_".
    { word. }
    { done. }
    try wp_auto.
    wp_apply (wp_checkDisjunct pp sp lcur' dj svs vs with "[$Hp $Hdj $Hvs]")
      as (lf) "[Hp %Hlf]".
    wp_if_destruct.
    + (* this disjunct matches *)
      try wp_auto. wp_for_post. try wp_auto.
      iApply "HΦ". iFrame "Hp". iPureIntro. intros _.
      destruct (Hlf eq_refl) as [Hf Hsat].
      exists dj. split; last done.
      by eapply list_elem_of_lookup_2.
    + try wp_auto. wp_for_post.
      iFrame. iPureIntro. word.
  - try wp_auto.
    iApply "HΦ". iFrame "Hp". iPureIntro. discriminate.
Qed.

End proof.
