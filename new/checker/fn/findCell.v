(** [checker.findCell] (checker/match.go): the index of the first not-yet-used
    heap cell whose location term is syntactically the given term.

    Naming: the Go locals are [h], [used], [l], [i] and [c], so no Rocq
    variable here may be called any of those (see NOTES.md). *)
From New.checker Require Import prelude nodes.
From New.checker.fn Require Import termEq.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All".

(** Mirrors [findCell]: the first index [i] at which the cell is unused and
    its location term is [y], counting from [i]. *)
Fixpoint find_cell (cs : list scell) (u : list bool) (y : term) (i : nat) : option nat :=
  match cs with
  | [] => None
  | c :: cs' =>
      if (negb (u !!! i) && bool_decide (cloc c = y))%bool then Some i
      else find_cell cs' u y (S i)
  end.

(** What a caller gets out of the mirror: the answer is in range, and names a
    free cell whose location term really is [y]. *)
Lemma find_cell_lt (cs : list scell) :
  ∀ (u : list bool) (y : term) (i j : nat),
    find_cell cs u y i = Some j → (i ≤ j < i + length cs)%nat.
Proof.
  induction cs as [|ce cs' IH]; simpl; intros u y i j Hf; first done.
  destruct (negb (u !!! i) && bool_decide (cloc ce = y))%bool.
  - injection Hf as <-. lia.
  - specialize (IH u y (S i) j Hf). lia.
Qed.

Lemma find_cell_Some (cs : list scell) :
  ∀ (u : list bool) (y : term) (i j : nat),
    find_cell cs u y i = Some j →
    ∃ sc, cs !! (j - i)%nat = Some sc ∧ u !!! j = false ∧ cloc sc = y.
Proof.
  induction cs as [|ce cs' IH]; simpl; intros u y i j Hf; first done.
  destruct (negb (u !!! i) && bool_decide (cloc ce = y))%bool eqn:Ht.
  - injection Hf as <-. rewrite Nat.sub_diag /=.
    apply andb_prop in Ht as [Hu Hc].
    exists ce. split_and!; [done| by apply negb_true_iff in Hu
                          | by apply bool_decide_eq_true in Hc].
  - destruct (IH u y (S i) j Hf) as (sc & Hsc & Hu & Hc).
    pose proof (find_cell_lt cs' u y (S i) j Hf) as Hlt.
    exists sc. split_and!; [|done|done].
    replace (j - i)%nat with (S (j - S i))%nat by lia. done.
Qed.

Lemma bool_decide_Some (a b : term) :
  bool_decide (Some a = Some b) = bool_decide (a = b).
Proof.
  destruct (decide (a = b)) as [->|Hne].
  - by rewrite !bool_decide_eq_true_2.
  - rewrite !bool_decide_eq_false_2 //. naive_solver.
Qed.

Lemma wp_findCell (sh su : slice.t) (cs : list scell) (u : list bool)
      (ly : loc) (y : term) :
  (length cs ≤ length u)%nat →
  {{{ is_pkg_init checker ∗ is_heap sh cs ∗ su ↦* u ∗ is_term ly y }}}
    @! checker.findCell #sh #su #ly
  {{{ (idx : w64) (ok : bool), RET (#idx, #ok);
      is_heap sh cs ∗ su ↦* u ∗
      ⌜ok = bool_decide (find_cell cs u y 0 ≠ None)⌝ ∗
      ⌜∀ j, find_cell cs u y 0 = Some j → uint.nat idx = j⌝ }}}.
Proof.
  intros Hlen.
  wp_start as "(Hheap & Hu & #Hy)".
  iDestruct "Hheap" as (xs) "[Hsh #Hcells]".
  iDestruct (big_sepL2_length with "Hcells") as %Hxlen.
  iDestruct (own_slice_len with "Hsh") as %[Hlh Hbh].
  iDestruct (own_slice_len with "Hu") as %[Hlu Hbu].
  assert (length cs = sint.nat sh.(slice.len)) as Hcs by lia.
  wp_auto.
  (* [wp_auto] cannot allocate the range loop's own index: the Go function
     already has a local called [i], so [i_ptr] is taken. *)
  wp_alloc ridx as "Hridx".
  wp_auto.
  iAssert (∃ (n : w64) (cc : checker.Cell.t),
    "i" ∷ i_ptr ↦ n ∗
    "Hridx" ∷ ridx ↦ n ∗
    "c" ∷ c_ptr ↦ cc ∗
    "%Hn" ∷ ⌜0 ≤ sint.Z n ≤ length cs⌝ ∗
    "%Hinv" ∷ ⌜find_cell cs u y 0 = find_cell (drop (sint.nat n) cs) u y (sint.nat n)⌝)%I
    with "[i Hridx c]" as "HI".
  { iFrame. iPureIntro.
    replace (sint.nat (W64 0)) with 0%nat by word.
    rewrite drop_0. split; [word|done]. }
  wp_for "HI".
  (* [case_bool_decide] would pick the [bool_decide] in the postcondition. *)
  destruct (bool_decide (sint.Z n < sint.Z sh.(slice.len))) eqn:Hcmp;
    [apply bool_decide_eq_true in Hcmp | apply bool_decide_eq_false in Hcmp].
  2:{ (* the range is exhausted *)
    assert (sint.nat n = length cs) as Heq by word.
    rewrite Heq drop_all in Hinv. simpl in Hinv.
    wp_auto. iApply "HΦ". rewrite /is_heap. iFrame "Hsh Hu Hcells".
    rewrite Hinv. iPureIntro. split.
    - rewrite bool_decide_eq_false_2 //. naive_solver.
    - naive_solver. }
  wp_auto.
  assert (is_Some (xs !! sint.nat n)) as [xc Hxc]
    by (apply lookup_lt_is_Some_2; word).
  assert (is_Some (cs !! sint.nat n)) as [sc Hsc]
    by (apply lookup_lt_is_Some_2; word).
  iDestruct (big_sepL2_lookup with "Hcells") as "#Hcell"; [exact Hxc|exact Hsc|].
  rewrite decide_True; last word.
  wp_apply (wp_load_slice_index with "[$Hsh]") as "Hsh"; [word|done|].
  assert (is_Some (u !! sint.nat n)) as [ub Hub]
    by (apply lookup_lt_is_Some_2; word).
  rewrite decide_True; last word.
  wp_apply (wp_load_slice_index with "[$Hu]") as "Hu"; [word|done|].
  assert (u !!! sint.nat n = ub) as Hut by (by apply list_lookup_total_correct).
  destruct ub.
  - (* the cell is already claimed by an earlier atom *)
    wp_auto. wp_for_post. iFrame "∗#". iPureIntro. split; first word.
    rewrite Hinv (drop_S cs sc _ Hsc) /= Hut /=.
    replace (sint.nat (word.add n (W64 1))) with (S (sint.nat n)) by word.
    done.
  - (* the cell is free: compare its location with [y] *)
    wp_auto.
    iDestruct "Hcell" as "[Hcl _]".
    wp_apply (wp_termEq xc.(checker.Cell.Loc') ly (Some (cloc sc)) (Some y) with "[]").
    { cbn [is_oterm]. iFrame "#". }
    rewrite bool_decide_Some.
    destruct (decide (cloc sc = y)) as [Heq|Hne].
    + assert (bool_decide (cloc sc = y) = true) as Hbd
        by (by apply bool_decide_eq_true_2).
      rewrite Hbd. wp_auto. wp_for_post.
      assert (find_cell cs u y 0 = Some (sint.nat n)) as Hfound.
      { rewrite Hinv (drop_S cs sc _ Hsc) /= Hut /= Hbd //. }
      iApply "HΦ". rewrite /is_heap. iFrame "Hsh Hu Hcells". iPureIntro.
      rewrite Hfound. split.
      * symmetry. by apply bool_decide_eq_true_2.
      * intros ? [= <-]. word.
    + assert (bool_decide (cloc sc = y) = false) as Hbd
        by (by apply bool_decide_eq_false_2).
      rewrite Hbd. wp_auto. wp_for_post.
      iFrame "∗#". iPureIntro. split; first word.
      rewrite Hinv (drop_S cs sc _ Hsc) /= Hut /= Hbd /=.
      replace (sint.nat (word.add n (W64 1))) with (S (sint.nat n)) by word.
      done.
Qed.

End proof.
