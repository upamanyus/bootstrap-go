(** [checker.parseDisjunct] (checker/match.go): peel the leading [AExists]
    binders off one disjunct of a postcondition, recording each binder's
    sort, and flatten the separating conjunction underneath.

    A pattern variable bound twice, a nil disjunct, and a body that is not a
    separating conjunction of atoms all set [d.fail]. A disjunct that parsed
    without failure entails the assertion it was parsed from
    ([parse_sound.v]).

    Naming: the Go locals are [a], [d], [body] and [fl], so no Rocq variable
    here is called any of those (see NOTES.md). *)
From New.checker Require Import prelude nodes disjunct verify_def parse_sound.
From New.checker.fn Require Import growPats flatten.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** The loop condition [body != nil && body.Kind == AExists]. *)
Definition oassn_is_exists (ob : option cassn) : bool :=
  match ob with Some (CAExists _ _ _) => true | _ => false end.

Lemma oassn_is_exists_true ob :
  oassn_is_exists ob = true → ∃ k s p, ob = Some (CAExists k s p).
Proof. destruct ob as [[]|]; naive_solver. Qed.

Definition dj_failed (dj : cdisjunct) : cdisjunct :=
  mkDisjunct (d_pats dj) (d_pat_ok dj) (d_atoms dj) true.

(** Storing a non-nil [*Failure] into [d.fail]. *)
Lemma is_disjunct_fail ld dj sp sok sa (las : list loc) (lf' : loc) :
  lf' ≠ null →
  ld ↦ checker.disjunct.mk sp sok sa lf' -∗
  sp ↦* (sort_code <$> d_pats dj) -∗
  own_slice_cap w64 sp (DfracOwn 1) -∗
  sok ↦* d_pat_ok dj -∗
  own_slice_cap bool sok (DfracOwn 1) -∗
  sa ↦* las -∗
  own_slice_cap loc sa (DfracOwn 1) -∗
  ([∗ list] la;y ∈ las; d_atoms dj, is_assn la y) -∗
  ⌜length (d_pats dj) = length (d_pat_ok dj)⌝ -∗
  is_disjunct ld (dj_failed dj).
Proof.
  iIntros (Hnn) "Hs Hp Hpc Hok Hokc Ha Hac Hats %Hlen".
  iExists sp, sok, sa, lf', las. iFrame. iPureIntro. split; first done.
  simpl. split; [done|discriminate].
Qed.

Lemma wp_parseDisjunct (lx : loc) (x : option cassn) :
  {{{ is_pkg_init checker ∗ is_oassn lx x }}}
    @! checker.parseDisjunct #lx
  {{{ (ld : loc) (dj : cdisjunct), RET #ld;
      is_disjunct ld dj ∗
      ⌜d_fail dj = false → ∃ y, x = Some y ∧ dj_entails dj y⌝ }}}.
Proof.
  wp_start as "#Hx".
  wp_auto.
  wp_alloc ld as "Hld".
  wp_auto.
  iAssert (is_disjunct ld (mkDisjunct [] [] [] false)) with "[Hld]" as "Hdj".
  { iExists slice.nil, slice.nil, slice.nil, null, [].
    iFrame "Hld". simpl.
    iDestruct (own_slice_nil (V:=w64) (DfracOwn 1)) as "$".
    iDestruct (own_slice_cap_nil (V:=w64)) as "$".
    iDestruct (own_slice_nil (V:=bool) (DfracOwn 1)) as "$".
    iDestruct (own_slice_cap_nil (V:=bool)) as "$".
    iDestruct (own_slice_nil (V:=loc) (DfracOwn 1)) as "$".
    iDestruct (own_slice_cap_nil (V:=loc)) as "$".
    iPureIntro. naive_solver. }
  iAssert (∃ (dj : cdisjunct) (lb : loc) (ob : option cassn),
      "body" ∷ body_ptr ↦ lb ∗
      "Hdj" ∷ is_disjunct ld dj ∗
      "#Hb" ∷ is_oassn lb ob ∗
      "%Hfl" ∷ ⌜d_fail dj = false⌝ ∗
      "%Hat" ∷ ⌜d_atoms dj = []⌝ ∗
      "%Hsem" ∷ ⌜∀ b, ob = Some b → ∃ y, x = Some y ∧ binders_entails dj b y⌝)%I
    with "[body Hdj]" as "HI".
  { iExists _, lx, x. iFrame "body Hdj Hx". iPureIntro.
    split; first done. split; first done.
    intros b ->. exists b. split; first done.
    intros Σ' hG' sem' package_sem' V. by apply binders_interp_init. }
  wp_for "HI".
  iApply (wp_wand_r _ _ _ (λ v, ⌜v = #(oassn_is_exists ob)⌝ ∗ body_ptr ↦ lb)%I).
  iSplitL "body".
  { iDestruct (is_oassn_null with "Hb") as %Hnull.
    wp_if_destruct.
    - assert (ob = None) as -> by naive_solver.
      by iFrame.
    - destruct ob as [b|]; last naive_solver.
      iDestruct (is_assn_node with "Hb")
        as (lL lR lX lY) "(%Hwf & #Hnode & #HL & #HR & #HX & #HY)".
      wp_auto.
      iSplit; last done. iPureIntro. f_equal.
      destruct b; simpl;
        first [apply bool_decide_eq_true_2; done
              | apply bool_decide_eq_false_2; by vm_compute]. }
  iIntros (v) "[-> body]".
  destruct (oassn_is_exists ob) eqn:Hex.
  - (* one more binder *)
    destruct (oassn_is_exists_true _ Hex) as (k & s & p & ->).
    iDestruct (is_assn_node with "Hb")
      as (lL lR lX lY) "(%Hidx & #Hnode & #HL & _)".
    simpl in Hidx. iSimpl in "Hnode HL".
    rewrite decide_True //.
    wp_auto.
    iDestruct (is_disjunct_wf _ _ [] SInt false with "Hdj") as %Hlen0.
    rewrite /sort_env_wf /disjunct_env /= in Hlen0.
    wp_apply (wp_disjunct__growPats with "[$Hdj]") as "Hdj".
    rewrite Hidx.
    iDestruct "Hdj"
      as (sp sok sa lf las) "(Hs & Hp & Hpc & Hok & Hokc & Ha & Hac & #Hats & %Hlen & %Hf)".
    destruct (grow_pats_lookup dj k) as [Hk1 Hk2].
    iDestruct (own_slice_len with "Hok") as %[Hl1 Hl2].
    iDestruct (own_slice_len with "Hp") as %[Hl3 Hl4].
    rewrite length_fmap in Hl3.
    assert (sint.Z (W64 k) = Z.of_nat k) as Hsk by word.
    wp_auto.
    rewrite -> decide_True; last word.
    destruct (lookup_lt_is_Some_2 _ _ Hk2) as [okk Hokk].
    wp_apply (wp_load_slice_index _ _ _ _ okk with "[$Hok]") as "Hok".
    { word. }
    { rewrite Hsk Nat2Z.id. done. }
    destruct okk.
    + (* the same pattern variable bound twice *)
      wp_auto.
      wp_alloc lfail as "Hfail".
      iDestruct (typed_pointsto_not_null with "Hfail") as %Hnn.
      wp_auto.
      wp_for_post.
      iApply "HΦ". iSplitL.
      * iApply (is_disjunct_fail ld (grow_pats dj k) sp sok sa las lfail Hnn
                  with "Hs Hp Hpc Hok Hokc Ha Hac Hats [//]").
      * iPureIntro. simpl. discriminate.
    + (* record the binder and move on to its body *)
      assert (d_pat_ok (grow_pats dj k) !! k ≠ Some true) as Hnot
        by (rewrite Hokk; discriminate).
      wp_auto.
      rewrite -> decide_True; last word. wp_auto.
      wp_apply (wp_store_slice_index with "[$Hp]") as "Hp".
      { iPureIntro. rewrite length_fmap. word. }
      try wp_auto.
      rewrite -> decide_True; last word. try wp_auto.
      wp_apply (wp_store_slice_index with "[$Hok]") as "Hok".
      { iPureIntro. word. }
      try wp_auto.
      wp_for_post.
      iFrame "HΦ d".
      iExists (bind_pat (grow_pats dj k) k s), lL, (Some p).
      iFrame "body HL".
      rewrite Hsk Nat2Z.id.
      iSplitL.
      * iExists sp, sok, sa, lf, las.
        rewrite /bind_pat /= list_fmap_insert.
        rewrite /grow_pats /= in Hlen Hf.
        iFrame "Hs Hp Hpc Hok Hokc Ha Hac Hats".
        iPureIntro. rewrite !length_insert. done.
      * iPureIntro. split; first done. split; first done.
        intros b [= <-].
        destruct (Hsem (CAExists k s p) eq_refl) as (y & Hy & Hent).
        exists y. split; first done.
        intros Σ' hG' sem' package_sem' V.
        etrans; last apply (Hent _ _ _ _). by apply binders_interp_step.
  - (* the binders are done: flatten the body *)
    rewrite decide_False; last done. rewrite decide_True; last done. wp_auto.
    wp_apply (wp_disjunct__flatten with "[$Hdj $Hb]") as (lres) "Hres".
    destruct (oassn_flatten ob) as [ats|] eqn:Hof.
    + iDestruct "Hres" as "[-> Hdj]".
      try wp_auto.
      iApply "HΦ". iFrame "Hdj". iPureIntro. intros _.
      destruct ob as [b|]; last done. simpl in Hof.
      destruct (Hsem b eq_refl) as (y & Hy & Hent).
      exists y. split; first done.
      intros Σ' hG' sem' package_sem' V.
      etrans; last apply (Hent _ _ _ _). by apply dj_interp_flatten.
    + iDestruct "Hres" as "[%Hnn Hdj]".
      iDestruct "Hdj" as (ats sp sok sa lf las)
        "(Hs & Hp & Hpc & Hok & Hokc & Ha & Hac & #Hats & %Hlen & %Hf)".
      wp_if_destruct; first congruence.
      try wp_auto.
      iApply "HΦ". iSplitL.
      * iApply (is_disjunct_fail ld (dj_atoms dj ats) sp sok sa las lres Hnn
                  with "Hs Hp Hpc Hok Hokc Ha Hac Hats [//]").
      * iPureIntro. simpl. discriminate.
  Unshelve. all: try apply _.
Qed.

End proof.
