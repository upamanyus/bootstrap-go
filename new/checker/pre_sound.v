(** The meaning of a precondition that [Analyze] accepts, and of the entry
    environment it builds.

    [Analyze] (checker/check.go) turns the precondition into the initial
    symbolic state -- its points-to atoms become the heap ([assnHeap]), its
    pure atoms the path condition ([assnPure]) -- and binds parameter [i] to
    the logical variable [TVar i]. This file proves that this is faithful:

    - a precondition that passes [assnWellSorted] has no [∨] and no [∃]
      (those forms are rejected), so its interpretation is exactly the
      heap of [assnHeap] plus the facts of [assnPure] ([pre_interp_state]);
    - its terms are sorted by the declared variables alone, so they mention
      no pattern variable, no [ret], and only variables below [length vars]
      ([pre_state_wf]);
    - the environment the parameter loop builds stands for the substitution
      [binds] that applying [func_val f] performs ([env_interp_penv]).

    [analyze_sound] puts these together with [exec_sound] of the body into
    the WP that [Analyze]'s specification promises. *)
From New.checker Require Import prelude nodes exec_spec.
From New.checker.fn Require Import assnHeap assnPure assnWellSorted.

(** * Pure facts *)

(** A term sorted by the declared variables alone mentions only them. *)
Lemma sort_of_vars_below (vars : list sort) (t : term) (s : sort) :
  sort_of (vars_env vars) t = Some s → vars_below (length vars) t.
Proof.
  revert s. induction t; cbn [sort_of vars_below]; intros s Hs;
    try done;
    repeat case_match; simplify_eq/=; try naive_solver.
  by eapply lookup_lt_Some.
Qed.

(** The initial symbolic state [Analyze] builds. *)
Definition pre_state (vars : list sort) (pre : cassn) : sstate :=
  mkState (cassn_heap pre) (cassn_pure pre) vars.

Lemma pre_below (vars : list sort) (pre : cassn) :
  cassn_ws (vars_env vars) pre = true →
  heap_below (length vars) (cassn_heap pre) ∧ pc_below (length vars) (cassn_pure pre).
Proof.
  induction pre as [|p IHp q IHq|p IHp q IHq|n s p IHp|t|x v];
    cbn [cassn_ws cassn_heap cassn_pure]; intros Hws; try done.
  - split; intros ? Hin; by apply elem_of_nil in Hin.
  - apply andb_prop in Hws as [Hp Hq].
    destruct (IHp Hp) as [Hp1 Hp2]. destruct (IHq Hq) as [Hq1 Hq2].
    split; intros c [Hc|Hc]%elem_of_app; eauto.
  - destruct (sort_of _ t) as [[]|] eqn:Ht; try done.
    split; intros c Hc; first by apply elem_of_nil in Hc.
    apply list_elem_of_singleton in Hc as ->. by eapply sort_of_vars_below.
  - destruct (sort_of _ x) as [[]|] eqn:Hx; try done.
    destruct (sort_of _ v) as [sv|] eqn:Hv; try done.
    split; intros c Hc; last by apply elem_of_nil in Hc.
    apply list_elem_of_singleton in Hc as ->. cbn [cloc cval].
    split; by eapply sort_of_vars_below.
Qed.

Lemma pre_state_wf (vars : list sort) (pre : cassn) :
  cassn_ws (vars_env vars) pre = true → wf_state (pre_state vars pre).
Proof.
  intros Hws. destruct (pre_below vars pre Hws). by split.
Qed.

(** * The entry environment

    Mirrors the parameter loop of [Analyze]: parameter [k + i] is bound to
    [TVar (k + i)], each new binding in front, so a later parameter shadows an
    earlier one of the same name. *)
Fixpoint penv_from (k : nat) (xs : list go_string) (ρ : list (go_string * term))
    : list (go_string * term) :=
  match xs with
  | [] => ρ
  | x :: xs' => penv_from (S k) xs' ((x, TVar k) :: ρ)
  end.

Definition penv (xs : list go_string) : list (go_string * term) := penv_from 0 xs [].

Lemma penv_from_snoc k xs x ρ :
  penv_from k (xs ++ [x]) ρ = (x, TVar (k + length xs)) :: penv_from k xs ρ.
Proof.
  revert k ρ. induction xs as [|y xs IH]; intros k ρ; cbn [penv_from app length].
  - by rewrite Nat.add_0_r.
  - rewrite IH. do 3 f_equal. lia.
Qed.

Lemma penv_snoc xs x : penv (xs ++ [x]) = (x, TVar (length xs)) :: penv xs.
Proof. apply penv_from_snoc. Qed.

Section pre_sound.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Set Default Proof Using "All".

Lemma penv_from_below K k xs ρ :
  env_below K ρ → (k + length xs ≤ K)%nat → env_below K (penv_from k xs ρ).
Proof.
  revert k ρ. induction xs as [|x xs IH]; intros k ρ Hρ Hlen; cbn [penv_from]; first done.
  cbn [length] in Hlen. apply IH; last lia.
  apply env_below_cons; last done. cbn [vars_below]. lia.
Qed.

Lemma penv_below K xs : (length xs ≤ K)%nat → env_below K (penv xs).
Proof.
  intros Hlen. apply penv_from_below; last lia.
  intros ? Hin. by apply elem_of_nil in Hin.
Qed.

Lemma env_interp_penv_from (V : valuation) k xs ρ :
  env_interp V (penv_from k xs ρ) =
    binds (pnames xs) (vvar V <$> seq k (length xs)) (env_interp V ρ).
Proof.
  revert k ρ. induction xs as [|x xs IH]; intros k ρ; first done.
  cbn [penv_from length seq fmap list_fmap]. rewrite IH pnames_cons binds_cons.
  done.
Qed.

Lemma env_interp_penv (V : valuation) xs :
  env_interp V (penv xs) = binds (pnames xs) (vvar V <$> seq 0 (length xs)) ∅.
Proof. apply env_interp_penv_from. Qed.

(** An accepted precondition means exactly its heap and its path condition. *)
Lemma assn_interp_ws E V (pre : cassn) :
  cassn_ws E pre = true →
  assn_interp V pre ⊢ heap_interp V (cassn_heap pre) ∗ ⌜pc_sat V (cassn_pure pre)⌝.
Proof.
  induction pre as [|p IHp q IHq|p IHp q IHq|n s p IHp|t|x v];
    cbn [cassn_ws cassn_heap cassn_pure assn_interp]; intros Hws; try done.
  - iIntros "_". rewrite heap_interp_nil. iSplit; first done.
    iPureIntro. apply pc_sat_nil.
  - apply andb_prop in Hws as [Hp Hq].
    iIntros "[Hp Hq]".
    iDestruct (IHp Hp with "Hp") as "[Hhp %Hcp]".
    iDestruct (IHq Hq with "Hq") as "[Hhq %Hcq]".
    rewrite heap_interp_app. iFrame. iPureIntro. by apply pc_sat_app.
  - iIntros "%Ht". rewrite heap_interp_nil. iSplit; first done.
    iPureIntro. intros t' Ht'. by apply list_elem_of_singleton in Ht' as ->.
  - iIntros "H". rewrite heap_interp_cons heap_interp_nil. cbn [cloc cval].
    iFrame "H". iPureIntro. apply pc_sat_nil.
Qed.

Lemma pre_interp_state θ (vars : list sort) (pre : cassn) :
  vars_sat θ vars →
  cassn_ws (vars_env vars) pre = true →
  pre_interp θ pre ⊢
    ⌜st_sat (mkVal θ (λ _, uval) uval) (pre_state vars pre)⌝ ∗
    heap_interp (mkVal θ (λ _, uval) uval) (sheap (pre_state vars pre)).
Proof.
  intros Hθ Hws. rewrite /pre_interp.
  iIntros "H". iDestruct (assn_interp_ws with "H") as "[$ %Hpc]"; first done.
  iPureIntro. split; last done. intros n s Hn. by apply Hθ.
Qed.

(** [Analyze]'s promise, from [exec_sound] of the body in the entry state. *)
Lemma analyze_sound (f : cfunc) (vars : list sort) (pre : cassn) (ps : list spath) θ :
  (length (fparams f) ≤ length vars)%nat →
  cassn_ws (vars_env vars) pre = true →
  exec_sound (fbody f) (penv (fparams f)) (pre_state vars pre) ps →
  vars_sat θ vars →
  ⊢ pre_interp θ pre -∗
    WP apply_vals (func_val f) (arg_vals f θ)
      {{ paths_post (length vars) (mkVal θ (λ _, uval) uval) ps }}.
Proof.
  intros Hlen Hws Hsnd Hθ.
  iIntros "Hpre".
  iDestruct (pre_interp_state with "Hpre") as "[%Hsat Hh]"; [done|done|].
  pose proof (Hsnd _ _ _ _ _ hG sem (pre_state_wf vars pre Hws) (penv_below _ _ Hlen) _ Hsat) as Hwp.
  iPoseProof (Hwp with "Hh") as "Hwp". clear Hwp.
  rewrite env_interp_penv. cbn [vvar svars pre_state].
  destruct (fparams f) as [|x xs] eqn:Hps.
  - iApply wp_func_val_nil; first done.
    cbn [pnames fmap list_fmap binds] in *.
    by rewrite csubst_empty.
  - rewrite /arg_vals Hps.
    iApply wp_func_val; [by rewrite length_fmap length_seq Hps|by rewrite Hps|].
    rewrite Hps. iExact "Hwp".
Qed.

End pre_sound.

(** What [Analyze] establishes, independent of the ghost state: the premises
    of [analyze_sound]. *)
Definition analyze_ok (f : cfunc) (vars : list sort) (pre : cassn) (ps : list spath) : Prop :=
  (length (fparams f) ≤ length vars)%nat ∧
  cassn_ws (vars_env vars) pre = true ∧
  exec_sound (fbody f) (penv (fparams f)) (pre_state vars pre) ps.
