(** the [flatten] method of the postcondition matcher's [disjunct]
    (checker/match.go): collect the atoms of a separating conjunction into
    [d.atoms].

    [AOr] and [AExists] are only allowed *above* a disjunct's separating
    conjunction, so meeting either here -- or meeting nil -- is a failure,
    and the atoms appended before the failure are left in place (the caller
    sets [d.fail] and never looks at them again).

    Naming: the Go locals are [d], [a] and [fl], so no Rocq variable here is
    called any of those (see NOTES.md). *)
From New.checker Require Import prelude nodes disjunct.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All - package_sem".

(** Appending to a disjunct's atom list. *)
Definition dj_atoms (dj : cdisjunct) (ats : list cassn) : cdisjunct :=
  mkDisjunct (d_pats dj) (d_pat_ok dj) (d_atoms dj ++ ats) (d_fail dj).

Lemma dj_atoms_nil dj : dj_atoms dj [] = dj.
Proof. destruct dj; rewrite /dj_atoms /= app_nil_r //. Qed.

Lemma dj_atoms_app dj l1 l2 : dj_atoms (dj_atoms dj l1) l2 = dj_atoms dj (l1 ++ l2).
Proof. destruct dj; rewrite /dj_atoms /= app_assoc //. Qed.

(** The Gallina mirror: the atoms of a separating conjunction, left to right,
    or [None] if the assertion is not a separating conjunction of atoms. *)
Fixpoint assn_flatten (x : cassn) : option (list cassn) :=
  match x with
  | CAEmp => Some []
  | CASep p q =>
      match assn_flatten p with
      | Some l1 => match assn_flatten q with
                   | Some l2 => Some (l1 ++ l2)
                   | None => None
                   end
      | None => None
      end
  | CAPure _ => Some [x]
  | CAPointsTo _ _ => Some [x]
  | CAOr _ _ => None
  | CAExists _ _ _ => None
  end.

Definition oassn_flatten (x : option cassn) : option (list cassn) :=
  match x with None => None | Some x' => assn_flatten x' end.

Lemma wp_disjunct__flatten (ld : loc) (dj : cdisjunct) (la : loc) (x : option cassn) :
  {{{ is_pkg_init checker ∗ is_disjunct ld dj ∗ is_oassn la x }}}
    ld @! (go.PointerType checker.disjunct) @! "flatten" #la
  {{{ (lres : loc), RET #lres;
      match oassn_flatten x with
      | Some ats => ⌜lres = null⌝ ∗ is_disjunct ld (dj_atoms dj ats)
      | None => ⌜lres ≠ null⌝ ∗ ∃ ats, is_disjunct ld (dj_atoms dj ats)
      end }}}.
Proof using All.
  iLöb as "IH" forall (la x dj).
  wp_start as "[Hdj #Hx]".
  iDestruct (is_oassn_null with "Hx") as %Hnull.
  wp_auto.
  wp_if_destruct.
  - (* nil: unsupported *)
    assert (x = None) as -> by naive_solver.
    wp_alloc lfail as "Hfail".
    iDestruct (typed_pointsto_not_null with "Hfail") as %?.
    try wp_auto.
    iApply "HΦ". simpl. iSplit; first by iPureIntro.
    iExists []. by rewrite dj_atoms_nil.
  - destruct x as [x'|]; last naive_solver.
    iDestruct (is_assn_node with "Hx")
      as (lL lR lX lY) "(%Hwf & #Hnode & #HL & #HR & #HX & #HY)".
    destruct x'; simpl.
    + (* CAEmp *)
      try wp_auto.
      iApply "HΦ". iSplit; first by iPureIntro. by rewrite dj_atoms_nil.
    + (* CASep: the left conjunct, then the right one *)
      try wp_auto.
      wp_apply ("IH" $! lL (Some x'1) dj with "[$]") as (lres1) "Hres1".
      simpl.
      destruct (assn_flatten x'1) as [ats1|] eqn:Hf1.
      * iDestruct "Hres1" as "[-> Hdj1]".
        try wp_auto.
        wp_apply ("IH" $! lR (Some x'2) (dj_atoms dj ats1) with "[$]")
          as (lres2) "Hres2".
        simpl.
        destruct (assn_flatten x'2) as [ats2|] eqn:Hf2.
        -- iDestruct "Hres2" as "[-> Hdj2]".
           try wp_auto.
           iApply "HΦ". iSplit; first by iPureIntro.
           rewrite -dj_atoms_app. iExact "Hdj2".
        -- iDestruct "Hres2" as "[%Hnn Hdj2]".
           try wp_auto.
           iApply "HΦ". iSplit; first by iPureIntro.
           iDestruct "Hdj2" as (ats2) "Hdj2".
           iExists (ats1 ++ ats2). rewrite -dj_atoms_app. iExact "Hdj2".
      * iDestruct "Hres1" as "[%Hnn Hdj1]".
        try wp_auto.
        wp_if_destruct; first congruence.
        try wp_auto.
        iApply "HΦ". iSplit; first by iPureIntro. iExact "Hdj1".
    + (* CAOr: unsupported inside a disjunct *)
      try wp_auto.
      wp_alloc lfail as "Hfail".
      iDestruct (typed_pointsto_not_null with "Hfail") as %?.
      try wp_auto.
      iApply "HΦ". iSplit; first by iPureIntro.
      iExists []. by rewrite dj_atoms_nil.
    + (* CAExists: likewise *)
      try wp_auto.
      wp_alloc lfail as "Hfail".
      iDestruct (typed_pointsto_not_null with "Hfail") as %?.
      try wp_auto.
      iApply "HΦ". iSplit; first by iPureIntro.
      iExists []. by rewrite dj_atoms_nil.
    + (* CAPure: one atom *)
      iDestruct "Hdj"
        as (sp sok sa lf las) "(Hs & Hp & Hpc & Hok & Hokc & Ha & Hac & #Hats & %Hlen & %Hf)".
      try wp_auto.
      wp_apply wp_slice_literal.
      iSplitR; first done.
      iIntros "% [Hsl Hslc]".
      try wp_auto.
      wp_apply (wp_slice_append sa las _ [la] (DfracOwn 1)
                 with "[$Ha $Hac $Hsl]") as (sa') "(Ha' & Hac' & _)".
      try wp_auto.
      iApply "HΦ". iSplit; first by iPureIntro.
      iExists sp, sok, sa', lf, (las ++ [la]).
      rewrite /dj_atoms /=. iFrame "Hs Hp Hpc Hok Hokc Ha' Hac'".
      iSplitL; last by iPureIntro.
      iApply (big_sepL2_app with "Hats"). by iFrame "Hx".
    + (* CAPointsTo: one atom *)
      iDestruct "Hdj"
        as (sp sok sa lf las) "(Hs & Hp & Hpc & Hok & Hokc & Ha & Hac & #Hats & %Hlen & %Hf)".
      try wp_auto.
      wp_apply wp_slice_literal.
      iSplitR; first done.
      iIntros "% [Hsl Hslc]".
      try wp_auto.
      wp_apply (wp_slice_append sa las _ [la] (DfracOwn 1)
                 with "[$Ha $Hac $Hsl]") as (sa') "(Ha' & Hac' & _)".
      try wp_auto.
      iApply "HΦ". iSplit; first by iPureIntro.
      iExists sp, sok, sa', lf, (las ++ [la]).
      rewrite /dj_atoms /=. iFrame "Hs Hp Hpc Hok Hokc Ha' Hac'".
      iSplitL; last by iPureIntro.
      iApply (big_sepL2_app with "Hats"). by iFrame "Hx".
  Unshelve.
  all: try apply _.
Qed.

End proof.
