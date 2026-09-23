(** Helpers for the per-case proofs of [exec] (fn/execLet.v, fn/execSeq.v,
    fn/execLoad.v, fn/execUnOp.v, fn/execBinOp.v), and the semantic
    composition lemmas for the operator cases, [exec_sound_at_unop] and
    [exec_sound_at_binop], in the style of exec_spec.v. *)
From New.checker Require Import prelude nodes exec_spec exec_def.
From New.checker.fn Require Import heapLookup.

(** * Load: the value found is scoped by the state *)
Lemma heap_lookup_below k H x y :
  heap_below k H → heap_lookup H x = Some y → vars_below k y.
Proof.
  induction H as [|c H IH]; first done.
  intros Hb. simpl. destruct (decide (cloc c = x)).
  - intros [= <-]. apply (Hb c). set_solver.
  - apply IH. intros c' Hc'. apply Hb. set_solver.
Qed.

(** * Operator results are scoped by their operands *)
Lemma apply_unop_below k op cty u r :
  apply_unop op cty u = Some r → vars_below k u → vars_below k r.
Proof.
  rewrite /apply_unop. intros Hr Hu.
  destruct op; try done;
    repeat (case_match || destruct (decide _)); simplify_eq; done.
Qed.

Lemma apply_binop_below k op cty u w r :
  apply_binop op cty u w = Some r → vars_below k u → vars_below k w → vars_below k r.
Proof.
  rewrite /apply_binop. intros Hr Hu Hw.
  destruct op; try done;
    repeat destruct (decide _); simplify_eq; cbn [vars_below]; done.
Qed.

Section exec_sound_b.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Set Default Proof Using "All".

(** * [exec_post] *)

Lemma exec_post_fail ce ρ sst s lf : lf ≠ null → ⊢ exec_post ce ρ sst s lf.
Proof. intros Hne. rewrite /exec_post. by destruct (decide (lf = null)). Qed.

Lemma exec_post_ok ce ρ sst s :
  exec_post ce ρ sst s null ⊣⊢
  ∃ ps, is_paths s ps ∗ ⌜paths_wf (length (svars sst)) ps⌝ ∗ ⌜exec_sound ce ρ sst ps⌝.
Proof. rewrite /exec_post. by destruct (decide (null = null)). Qed.

(** * Unary operators

    The checker has checked, at the operand's own state, that the operand has
    the sort of the operator's type; that makes the GooseLang step
    ([wp_unop]) go through, and the result term is what [apply_unop]
    built. *)
Lemma exec_sound_at_unop (op : cop) (cty : ctype) (ce : cexpr) ρ sst ps out :
  exec_sound_at ce ρ sst ps →
  (∀ p, p ∈ ps → ∃ r,
     sort_of_vars (svars (pst p)) (pret p) = Some (ctype_sort cty) ∧
     apply_unop op cty (pret p) = Some r ∧ mkPath r (pst p) ∈ out) →
  exec_sound_at (CEUnOp op cty ce) ρ sst out.
Proof.
  intros He Hcont Hwf Hρ V Hsat. iIntros "Hheap". simpl.
  iApply (wp_bind (fill [AppRCtx (Val (GoInstruction (GoUnOp (unop_of op) (type_of cty))))])).
  iApply (wp_wand_r _ _ _ (paths_post (length (svars sst)) V ps)).
  iSplitL "Hheap".
  { by iApply (He Hwf Hρ V Hsat with "Hheap"). }
  iIntros (w) "Hw".
  iDestruct "Hw" as (p V') "(%Hin & %Hag & %Hret & %Hsat' & Hheap')".
  destruct (Hcont p Hin) as (r & Hsort & Hr & Hout).
  assert (has_sort (teval V' (pret p)) (ctype_sort cty)) as Hs.
  { eapply sort_of_vars_sound; last done. by destruct Hsat'. }
  rewrite Hret. simpl.
  iApply (wp_unop op cty (pret p) r V' with "[Hheap']"); [done|done|].
  iExists (mkPath r (pst p)), V'. iFrame "Hheap'". iPureIntro.
  split_and!; [done|done|done|done].
Qed.

(** * Binary operators

    GooseLang evaluates a [Pair] left to right, as the checker does: [ce1]
    first, then [ce2] from each of its paths, then the operator. The left
    operand's term is scoped by the state [ce1] ended in, so it keeps its
    value under the valuation [ce2] ended with; the sort checks are made at
    the final state, whose valuation is the one the operator step sees. *)
Lemma exec_sound_at_binop (op : cop) (cty : ctype) (ce1 ce2 : cexpr) ρ sst ps out :
  exec_sound_at ce1 ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (∀ p, p ∈ ps → ∃ qs, exec_sound_at ce2 ρ (pst p) qs ∧
     ∀ q, q ∈ qs → ∃ r,
       sort_of_vars (svars (pst q)) (pret p) = Some (ctype_sort cty) ∧
       sort_of_vars (svars (pst q)) (pret q) = Some (ctype_sort cty) ∧
       apply_binop op cty (pret p) (pret q) = Some r ∧ mkPath r (pst q) ∈ out) →
  exec_sound_at (CEBinOp op cty ce1 ce2) ρ sst out.
Proof.
  intros He1 Hwfps Hcont Hwf Hρ V Hsat. iIntros "Hheap". simpl.
  set (f := Val (GoInstruction (GoOp (binop_of op) (type_of cty)))).
  iApply (wp_bind (fill [PairLCtx (csubst (env_interp V ρ) ce2); AppRCtx f])).
  iApply (wp_wand_r _ _ _ (paths_post (length (svars sst)) V ps)).
  iSplitL "Hheap".
  { by iApply (He1 Hwf Hρ V Hsat with "Hheap"). }
  iIntros (w) "Hw".
  iDestruct "Hw" as (p V') "(%Hin & %Hag & %Hret & %Hsat' & Hheap')".
  destruct (Hcont p Hin) as (qs & Hqs & Hcont2).
  assert (wf_state (pst p)) as Hwfp by (by apply (paths_wf_state _ _ Hwfps)).
  assert ((length (svars sst) ≤ length (svars (pst p)))%nat) as Hgrow
    by (by apply (paths_wf_grow _ _ Hwfps)).
  assert (vars_below (length (svars (pst p))) (pret p)) as Hbret
    by (by apply (paths_wf_ret _ _ Hwfps)).
  assert (env_below (length (svars (pst p))) ρ) as Hbp
    by (by eapply env_below_mono).
  rewrite (env_interp_agree (length (svars sst)) V V') //.
  iApply (wp_bind (fill [PairRCtx w; AppRCtx f])).
  iApply (wp_wand_r _ _ _ (paths_post (length (svars (pst p))) V' qs)).
  iSplitL "Hheap'".
  { by iApply (Hqs Hwfp Hbp V' Hsat' with "Hheap'"). }
  iIntros (w2) "Hw2".
  iDestruct "Hw2" as (q V'') "(%Hin2 & %Hag2 & %Hret2 & %Hsat'' & Hheap'')".
  destruct (Hcont2 q Hin2) as (r & Hs1 & Hs2 & Hr & Hout).
  assert (st_sat V'' (pst q)) as [Hv'' _] by done.
  assert (has_sort (teval V'' (pret p)) (ctype_sort cty)) as Ha
    by (by eapply sort_of_vars_sound).
  assert (has_sort (teval V'' (pret q)) (ctype_sort cty)) as Hb
    by (by eapply sort_of_vars_sound).
  rewrite Hret Hret2 (teval_agree (length (svars (pst p))) V' V'' (pret p)) //.
  simpl. subst f.
  wp_pure.
  iApply (wp_binop op cty (pret p) (pret q) r V'' with "[Hheap'']"); [done|done|done|].
  iExists (mkPath r (pst q)), V''. iFrame "Hheap''". iPureIntro.
  split_and!; [done| |done|done].
  eapply agree_below_trans; first exact Hag.
  by eapply agree_below_weaken.
Qed.

End exec_sound_b.

(** * The ghost-state-independent layer (see exec_spec.v) *)
Section exec_uniform_b.

Lemma exec_sound_unop (op : cop) (cty : ctype) (ce : cexpr) ρ sst ps out :
  exec_sound ce ρ sst ps →
  (∀ p, p ∈ ps → ∃ r,
     sort_of_vars (svars (pst p)) (pret p) = Some (ctype_sort cty) ∧
     apply_unop op cty (pret p) = Some r ∧ mkPath r (pst p) ∈ out) →
  exec_sound (CEUnOp op cty ce) ρ sst out.
Proof. exec_lift exec_sound_at_unop. Qed.

Lemma exec_sound_binop (op : cop) (cty : ctype) (ce1 ce2 : cexpr) ρ sst ps out :
  exec_sound ce1 ρ sst ps →
  paths_wf (length (svars sst)) ps →
  (∀ p, p ∈ ps → ∃ qs, exec_sound ce2 ρ (pst p) qs ∧
     ∀ q, q ∈ qs → ∃ r,
       sort_of_vars (svars (pst q)) (pret p) = Some (ctype_sort cty) ∧
       sort_of_vars (svars (pst q)) (pret q) = Some (ctype_sort cty) ∧
       apply_binop op cty (pret p) (pret q) = Some r ∧ mkPath r (pst q) ∈ out) →
  exec_sound (CEBinOp op cty ce1 ce2) ρ sst out.
Proof. exec_lift exec_sound_at_binop. Qed.

End exec_uniform_b.
