(** [checker.condHolds] (checker/match.go): does the path condition
    syntactically justify a term?

    Note on naming: the Go function's locals are [cond], [t] and [c], and the
    range loop introduces [i], so no Rocq variable here may be called any of
    those (see NOTES.md). *)
From New.checker Require Import prelude.
From New.checker.fn Require Import termEq.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All - package_sem".

(** What the [range] loop decides: [t] is non-nil and is one of the recorded
    facts.  [termEq c t] is [bool_decide (Some c = ox)], and every cell of
    [is_cond] is a real term, so a nil [t] never matches. *)
Definition cond_mem (pc : list term) (ox : option term) : bool :=
  match ox with None => false | Some y => bool_decide (y ∈ pc) end.

(** ... and what it checks afterwards. *)
Definition cond_refl (y : term) : bool :=
  match y with
  | TEq p q => bool_decide (p = q)
  | TBool b => b
  | _ => false
  end.

Definition cond_holds (pc : list term) (ox : option term) : bool :=
  match ox with None => false | Some y => bool_decide (y ∈ pc) || cond_refl y end.

Lemma cond_mem_holds pc ox : cond_mem pc ox = true → cond_holds pc ox = true.
Proof. destruct ox as [y|]; simpl; last done. intros ->. done. Qed.

(** The loop hits a matching fact ... *)
Lemma cond_holds_hit pc (n : nat) (y : term) ox :
  pc !! n = Some y → ox = Some y → cond_holds pc ox = true.
Proof.
  intros Hn ->. simpl. rewrite bool_decide_eq_true_2; first done.
  by eapply list_elem_of_lookup_2.
Qed.

(** ... or passes it. *)
Lemma cond_mem_step pc (n : nat) (y : term) ox :
  pc !! n = Some y → cond_mem (take n pc) ox = false → ox ≠ Some y →
  cond_mem (take (S n) pc) ox = false.
Proof.
  intros Hn Hmiss Hne. destruct ox as [z|]; last done. simpl in *.
  rewrite (take_S_r _ _ y) //.
  apply bool_decide_eq_false_2. intros Hin.
  apply elem_of_app in Hin as [Hin|Hin].
  - rewrite (bool_decide_eq_true_2 _ Hin) in Hmiss. congruence.
  - apply list_elem_of_singleton in Hin as ->. naive_solver.
Qed.

(** The kind tests, in the node view the Go code uses. *)
Definition is_teq (x : term) : bool := match x with TEq _ _ => true | _ => false end.
Definition is_tbool (x : term) : bool := match x with TBool _ => true | _ => false end.

Lemma is_teq_code x : bool_decide (term_code x = W64 12) = is_teq x.
Proof. destruct x; simpl; repeat case_match; by vm_compute. Qed.

Lemma is_tbool_code x : bool_decide (term_code x = W64 5) = is_tbool x.
Proof. destruct x; simpl; repeat case_match; by vm_compute. Qed.

Lemma cond_refl_teq y : is_teq y = true → cond_refl y = bool_decide (term_a y = term_b y).
Proof.
  destruct y; try done. intros _. simpl.
  apply bool_decide_ext. naive_solver.
Qed.

Lemma cond_refl_tbool y : is_tbool y = true → cond_refl y = bool_decide (term_num y = W64 1).
Proof. destruct y; try done. intros _. destruct b; by vm_compute. Qed.

Lemma cond_refl_other y : is_teq y = false → is_tbool y = false → cond_refl y = false.
Proof. destruct y; done. Qed.

Lemma is_teq_tbool y : is_teq y = true → is_tbool y = false.
Proof. destruct y; done. Qed.

Lemma wp_condHolds (s : slice.t) (pc : list term) (lx : loc) (ox : option term) :
  {{{ is_pkg_init checker ∗ is_cond s pc ∗ is_oterm lx ox }}}
    @! checker.condHolds #s #lx
  {{{ RET #(cond_holds pc ox); is_cond s pc }}}.
Proof using All.
  wp_start as "[Hcond #Hox]".
  iDestruct "Hcond" as (ls) "[Hs #Hls]".
  iDestruct (big_sepL2_length with "Hls") as %Hlen2.
  iDestruct (own_slice_len with "Hs") as %Hlen.
  wp_auto.
  iAssert (∃ (n : w64) (lcur : loc),
      "i" ∷ i_ptr ↦ n ∗
      "c" ∷ c_ptr ↦ lcur ∗
      "%Hn" ∷ ⌜0 ≤ sint.Z n ≤ length ls⌝ ∗
      "%Hmiss" ∷ ⌜cond_mem (take (sint.nat n) pc) ox = false⌝)%I
    with "[i c]" as "HI".
  { iFrame. iPureIntro. split; first word.
    replace (sint.nat (W64 0)) with 0%nat by word.
    by destruct ox as [y|]; simpl. }
  wp_for "HI".
  wp_if_destruct.
  - rewrite -> decide_True; last word.
    list_elem ls (sint.nat n) as lcur'.
    list_elem pc (sint.nat n) as tcur.
    iDestruct (big_sepL2_lookup with "Hls") as "#Hcur"; [done|done|].
    wp_apply (wp_load_slice_index with "[$Hs]").
    { word. }
    { done. }
    iIntros "Hs".
    wp_auto.
    wp_apply (wp_termEq lcur' lx (Some tcur) ox with "[$]").
    wp_if_destruct.
    + (* this fact is the one *)
      try wp_auto. wp_for_post. try wp_auto.
      rewrite (cond_holds_hit pc (sint.nat n) tcur); [|done|done].
      iApply "HΦ". iFrame "Hs Hls".
    + (* keep scanning *)
      try wp_auto. wp_for_post.
      iFrame. iPureIntro. split; first word.
      replace (sint.nat (word.add n (W64 1))) with (S (sint.nat n)) by word.
      eapply cond_mem_step; [done|done|congruence].
  - (* the scan reached the end of the path condition *)
    try wp_auto.
    rewrite take_ge in Hmiss; last lia.
    iDestruct (is_oterm_null with "Hox") as %Hnull.
    wp_if_destruct.
    { (* [t] is nil *)
      assert (ox = None) as -> by naive_solver.
      try wp_auto. iApply "HΦ". iFrame "Hs Hls". }
    destruct ox as [y|]; last naive_solver.
    simpl in Hmiss.
    iDestruct (is_term_node with "Hox") as (la lb lc) "(%Hw & #Hn & #Ha & #Hb & #Hc)".
    assert (cond_holds pc (Some y) = cond_refl y) as Hch
      by (simpl; by rewrite Hmiss).
    rewrite Hch.
    try wp_auto.
    rewrite is_teq_code.
    destruct (is_teq y) eqn:Hq.
    + (* [t.Kind == TEq]: compare the two children *)
      rewrite (cond_refl_teq _ Hq). try wp_auto.
      wp_apply (wp_termEq la lb (term_a y) (term_b y) with "[$]").
      wp_if_destruct.
      * (* the children are equal *)
        try wp_auto. iApply "HΦ". iFrame "Hs Hls".
      * (* they differ, and a [TEq] node is not a [TBool] node *)
        try wp_auto.
        rewrite is_tbool_code (is_teq_tbool _ Hq). try wp_auto.
        iApply "HΦ". iFrame "Hs Hls".
    + try wp_auto.
      rewrite is_tbool_code.
      destruct (is_tbool y) eqn:Hb.
      * (* [t.Kind == TBool]: is it the literal [true]? *)
        rewrite (cond_refl_tbool _ Hb). try wp_auto.
        wp_if_destruct.
        ** try wp_auto. iApply "HΦ". iFrame "Hs Hls".
        ** try wp_auto. iApply "HΦ". iFrame "Hs Hls".
      * rewrite (cond_refl_other _ Hq Hb). try wp_auto.
        iApply "HΦ". iFrame "Hs Hls".
Qed.

End proof.
