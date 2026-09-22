(** Interpretation of the checker's *internal* data.

    [State] and [Path] (checker/state.go) never appear in the soundness
    statement, but every exec-level specification has to say what a symbolic
    state means, so they get Gallina mirrors here together with their
    interpretation as an Iris assertion. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.generatedproof.github_com.mit_pdos.perennial Require Import checker.
From New.checker Require Import defs term_lemmas.

Set Default Proof Using "All".

Section interp.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.

(** Mirrors [checker.Cell]: a location term and the value term stored there. *)
Record scell := mkCell { cloc : term; cval : term }.

(** Mirrors [checker.State]. *)
Record sstate := mkState {
  sheap : list scell;
  spc : list term;
  svars : list sort;
}.

(** Mirrors [checker.Path]. *)
Record spath := mkPath { pret : term; pst : sstate }.

#[global] Instance scell_inhabited : Inhabited scell := populate (mkCell TUnit TUnit).
#[global] Instance sstate_inhabited : Inhabited sstate := populate (mkState [] [] []).
#[global] Instance spath_inhabited : Inhabited spath := populate (mkPath TUnit inhabitant).

#[global] Instance scell_eq_dec : EqDecision scell.
Proof. solve_decision. Defined.

(** * The meaning of a symbolic state *)

(** The separating conjunction of the cells the state owns. *)
Definition heap_interp (V : valuation) (H : list scell) : iProp Σ :=
  ([∗ list] c ∈ H, ∃ lo : loc,
      ⌜teval V (cloc c) = lval lo⌝ ∗ heap_pointsto lo (DfracOwn 1) (teval V (cval c)))%I.

Lemma heap_interp_nil V : heap_interp V [] ⊣⊢ True.
Proof. by rewrite /heap_interp big_sepL_nil. Qed.

Lemma heap_interp_cons V c H :
  heap_interp V (c :: H) ⊣⊢
  (∃ lo : loc, ⌜teval V (cloc c) = lval lo⌝ ∗ heap_pointsto lo (DfracOwn 1) (teval V (cval c)))
  ∗ heap_interp V H.
Proof. by rewrite /heap_interp big_sepL_cons. Qed.

Lemma heap_interp_app V H1 H2 :
  heap_interp V (H1 ++ H2) ⊣⊢ heap_interp V H1 ∗ heap_interp V H2.
Proof. by rewrite /heap_interp big_sepL_app. Qed.

(** The pure side: the valuation respects the state's sort table and makes
    every recorded path condition true. *)
Definition st_sat (V : valuation) (st : sstate) : Prop :=
  (∀ n s, svars st !! n = Some s → has_sort (vvar V n) s) ∧ pc_sat V (spc st).

(** Every term in a state mentions only the logical variables the state
    declares, so extending the valuation beyond [length (svars st)] is
    harmless. *)
Definition heap_below (k : nat) (H : list scell) : Prop :=
  ∀ c, c ∈ H → vars_below k (cloc c) ∧ vars_below k (cval c).

Record wf_state (st : sstate) : Prop := mkWfState {
  wf_heap : heap_below (length (svars st)) (sheap st);
  wf_pc : pc_below (length (svars st)) (spc st);
}.

Lemma heap_below_mono k k' H : (k ≤ k')%nat → heap_below k H → heap_below k' H.
Proof. intros ? Hb c Hc. destruct (Hb c Hc). eauto using vars_below_mono. Qed.

Lemma pc_below_mono k k' pc : (k ≤ k')%nat → pc_below k pc → pc_below k' pc.
Proof. intros ? Hb t Ht. eauto using vars_below_mono. Qed.

(** Agreeing valuations give the same interpretation of a well-scoped heap. *)
Lemma heap_interp_agree k V V' H :
  agree_below k V V' → heap_below k H → heap_interp V H ⊣⊢ heap_interp V' H.
Proof.
  intros Hag Hb. rewrite /heap_interp.
  iSplit; iApply big_sepL_mono; iIntros (i c Hc) "H";
    ( assert (c ∈ H) as Hin by (eapply list_elem_of_lookup_2; done) );
    destruct (Hb c Hin) as [Hl Hv];
    rewrite (teval_agree k V V' (cloc c)) // (teval_agree k V V' (cval c)) //.
Qed.

Lemma st_sat_agree k V V' st :
  agree_below k V V' → (length (svars st) ≤ k)%nat → wf_state st →
  st_sat V st → st_sat V' st.
Proof.
  intros Hag Hlen Hwf [Hv Hpc]. split.
  - intros n s Hn.
    assert (n < k)%nat.
    { apply lookup_lt_Some in Hn. lia. }
    destruct Hag as (Hag & _ & _). rewrite -Hag //. by apply Hv.
  - eapply pc_sat_agree; [done| |done].
    eapply pc_below_mono; last apply Hwf. done.
Qed.

(** * Path lists

    A path list is a *disjunction*: the program ends in some one of them. This
    is the postcondition every exec-level specification produces. [k] is the
    number of logical variables the caller had, which the callee may only
    extend. *)
Definition paths_post (k : nat) (V : valuation) (ps : list spath) : val → iProp Σ :=
  (λ v, ∃ (p : spath) (V' : valuation),
      ⌜p ∈ ps⌝ ∗ ⌜agree_below k V V'⌝ ∗
      ⌜v = teval V' (pret p)⌝ ∗ ⌜st_sat V' (pst p)⌝ ∗
      heap_interp V' (sheap (pst p)))%I.

Lemma paths_post_mono k V ps ps' v :
  ps ⊆ ps' → paths_post k V ps v -∗ paths_post k V ps' v.
Proof.
  iIntros (Hsub) "H". iDestruct "H" as (p V') "(%Hin & ? & ? & ? & ?)".
  iExists p, V'. iFrame. iPureIntro. by apply Hsub.
Qed.

Lemma paths_post_app_l k V ps ps' v : paths_post k V ps v -∗ paths_post k V (ps ++ ps') v.
Proof. apply paths_post_mono. set_solver. Qed.

Lemma paths_post_app_r k V ps ps' v : paths_post k V ps' v -∗ paths_post k V (ps ++ ps') v.
Proof. apply paths_post_mono. set_solver. Qed.

(** Well-formedness of a result list: each path's state is well-formed and has
    at least the caller's logical variables, and its return term is scoped by
    that state. *)
Record paths_wf (k : nat) (ps : list spath) : Prop := mkPathsWf {
  paths_wf_state : ∀ p, p ∈ ps → wf_state (pst p);
  paths_wf_grow : ∀ p, p ∈ ps → (k ≤ length (svars (pst p)))%nat;
  paths_wf_ret : ∀ p, p ∈ ps → vars_below (length (svars (pst p))) (pret p);
}.

Lemma paths_wf_nil k : paths_wf k [].
Proof. split; intros ? H; by apply elem_of_nil in H. Qed.

Lemma paths_wf_app k ps ps' : paths_wf k ps → paths_wf k ps' → paths_wf k (ps ++ ps').
Proof.
  intros [??? ] [???]. split; intros p [?|?]%elem_of_app; eauto.
Qed.

Lemma paths_wf_mono k k' ps : (k' ≤ k)%nat → paths_wf k ps → paths_wf k' ps.
Proof. intros ? [H1 H2 H3]. split; auto. intros p Hp. specialize (H2 p Hp). lia. Qed.

(** * Environments *)

(** Every term an environment binds is scoped by the current variables. *)
Definition env_below (k : nat) (ρ : list (go_string * term)) : Prop :=
  ∀ xt, xt ∈ ρ → vars_below k xt.2.

Lemma env_below_mono k k' ρ : (k ≤ k')%nat → env_below k ρ → env_below k' ρ.
Proof. intros ? Hb xt Hxt. eauto using vars_below_mono. Qed.

Lemma env_below_cons k x t ρ :
  vars_below k t → env_below k ρ → env_below k ((x, t) :: ρ).
Proof. intros ?? xt [->|?]%elem_of_cons; [done|auto]. Qed.

End interp.
