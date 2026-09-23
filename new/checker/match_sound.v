(** Soundness of the postcondition matcher (checker/match.go), on Gallina
    mirrors.

    The Go specifications of [matchTerm], [matchAtom], [matchPass],
    [matchHeap], [checkSorts] and [checkPure] (new/checker/fn/) report what
    happened as the relations and predicates defined here; this file proves,
    once and without any Go in sight, that a successful run of all three
    phases gives [path_sat_dj].

    The pure part lives outside any section with Iris context (see NOTES.md,
    "Set Default Proof Using All poisons pure lemmas"). *)
From New.checker Require Import prelude nodes disjunct verify_def.
From New.checker.fn Require Import instantiate hasPat findCell condHolds.

(** * Substitutions *)

(** [σ'] extends [σ]: every bound entry stays bound to the same term. *)
Definition subst_ext (σ σ' : list (option term)) : Prop :=
  ∀ n y, σ !! n = Some (Some y) → σ' !! n = Some (Some y).

Lemma subst_ext_refl σ : subst_ext σ σ.
Proof. by intros ??. Qed.

Lemma subst_ext_trans σ1 σ2 σ3 : subst_ext σ1 σ2 → subst_ext σ2 σ3 → subst_ext σ1 σ3.
Proof. intros H1 H2 n y Hn. by apply H2, H1. Qed.

(** Every bound entry is at a declared pattern variable and is a term of that
    variable's declared sort, under the path's sort table [PV]. *)
Definition subst_wf (pats : list sort) (pok : list bool) (PV : list sort)
    (σ : list (option term)) : Prop :=
  ∀ n y, σ !! n = Some (Some y) →
    pok !! n = Some true ∧ ∃ s, pats !! n = Some s ∧ sort_of_vars PV y = Some s.

Lemma subst_wf_empty pats pok PV k : subst_wf pats pok PV (replicate k None).
Proof. intros n y Hn. apply lookup_replicate in Hn as [? _]. done. Qed.

(** * [matchTerm], as a relation

    One constructor per way the Go function can return [nil]. The [TResult]
    case matches the path's return term [r] in place of the pattern, which is
    not a subterm, so this is a relation rather than a structurally recursive
    function; a derivation is finite even when the Go recursion would not be. *)
Inductive match_rel (pats : list sort) (pok : list bool) (PV : list sort) (r : term) :
    option term → option term → list (option term) → list (option term) → Prop :=
| MR_nil σ : match_rel pats pok PV r None None σ σ
| MR_pat_new n y s σ :
    σ !! n = Some None → pok !! n = Some true → pats !! n = Some s →
    sort_of_vars PV y = Some s →
    match_rel pats pok PV r (Some (TPat n)) (Some y) σ (<[n := Some y]> σ)
| MR_pat_old n y σ :
    σ !! n = Some (Some y) → pok !! n = Some true →
    match_rel pats pok PV r (Some (TPat n)) (Some y) σ σ
| MR_result oy σ σ' :
    match_rel pats pok PV r (Some r) oy σ σ' →
    match_rel pats pok PV r (Some TResult) oy σ σ'
| MR_node x y σ σ1 σ2 σ3 :
    is_tpat x = false → is_tresult x = false →
    term_code x = term_code y → term_num x = term_num y →
    term_idx_wf x → term_idx_wf y →
    match_rel pats pok PV r (term_a x) (term_a y) σ σ1 →
    match_rel pats pok PV r (term_b x) (term_b y) σ1 σ2 →
    match_rel pats pok PV r (term_c x) (term_c y) σ2 σ3 →
    match_rel pats pok PV r (Some x) (Some y) σ σ3.

Lemma match_rel_ext pats pok PV r ox oy σ σ' :
  match_rel pats pok PV r ox oy σ σ' → subst_ext σ σ'.
Proof.
  induction 1; try apply subst_ext_refl; eauto using subst_ext_trans.
  intros m z Hm. rewrite list_lookup_insert_ne //. congruence.
Qed.

Lemma match_rel_wf pats pok PV r ox oy σ σ' :
  match_rel pats pok PV r ox oy σ σ' → subst_wf pats pok PV σ → subst_wf pats pok PV σ'.
Proof.
  induction 1; intros Hwf; eauto.
  intros m z Hm. destruct (decide (m = n)) as [->|Hne].
  - rewrite list_lookup_insert_eq in Hm; last by eapply lookup_lt_Some.
    injection Hm as <-. eauto.
  - rewrite list_lookup_insert_ne // in Hm. by apply Hwf.
Qed.

Lemma match_rel_len pats pok PV r ox oy σ σ' :
  match_rel pats pok PV r ox oy σ σ' → length σ' = length σ.
Proof. induction 1; try done; try congruence. by rewrite length_insert. Qed.

(** * [instantiate] *)

Local Ltac inst_destr :=
  repeat match goal with
  | H : tbind1 _ ?o = Some _ |- _ =>
      destruct o eqn:?; simpl in H; [injection H as <-|discriminate H]
  | H : tbind2 _ ?o1 ?o2 = Some _ |- _ =>
      destruct o1 eqn:?; [destruct o2 eqn:?|]; simpl in H; [injection H as <-|discriminate H|discriminate H]
  | H : tbind3 _ ?o1 ?o2 ?o3 = Some _ |- _ =>
      destruct o1 eqn:?; [destruct o2 eqn:?; [destruct o3 eqn:?|]|]; simpl in H;
      [injection H as <-|discriminate H|discriminate H|discriminate H]
  end.

(** A result without pattern variables survives extending the substitution. *)
Lemma inst_ext x σ σ' r y :
  subst_ext σ σ' → instantiate_t x σ r = Some y → has_pat y = false →
  instantiate_t x σ' r = Some y.
Proof.
  intros Hext. revert y. induction x; intros y Hi Hp; simpl in Hi |- *; inst_destr;
    simpl in Hp; rewrite ?orb_false_iff in Hp; destruct_and?;
    repeat match goal with
    | IH : ∀ y, Some ?t = Some y → has_pat y = false → instantiate_t ?p σ' r = Some y,
      H : has_pat ?t = false |- _ =>
        rewrite (IH t eq_refl H); clear IH
    end; try done.
  (* TPat *)
  destruct (σ !! n) as [[z|]|] eqn:Hn; injection Hi as <-; try done.
  by rewrite (Hext _ _ Hn).
Qed.

(** A term without pattern variables and [ret] is its own instance. *)
Lemma inst_nopat x σ r : has_pat x = false → has_result x = false → instantiate_t x σ r = Some x.
Proof.
  induction x; simpl; intros Hp Hr; rewrite ?orb_false_iff in Hp Hr; destruct_and?;
    repeat match goal with
    | IH : has_pat ?p = false → has_result ?p = false → instantiate_t ?p σ r = Some ?p,
      H1 : has_pat ?p = false, H2 : has_result ?p = false |- _ =>
        rewrite (IH H1 H2); clear IH
    end; done.
Qed.

(** The node view of [instantiate] on a node that is neither [TPat] nor
    [TResult]. *)
Lemma inst_node x σ r y :
  is_tpat x = false → is_tresult x = false → instantiate_t x σ r = Some y →
  term_code y = term_code x ∧ term_num y = term_num x ∧
  term_a y = oinstantiate_t (term_a x) σ r ∧ term_b y = oinstantiate_t (term_b x) σ r ∧
  term_c y = oinstantiate_t (term_c x) σ r ∧ (term_idx_wf x → term_idx_wf y).
Proof.
  intros Hp Hr Hi. destruct x; simpl in Hp, Hr, Hi |- *; try discriminate;
    inst_destr; try (injection Hi as <-); simpl; rewrite ?Heqo ?Heqo0 ?Heqo1; done.
Qed.

(** Kind codes as [nat]s, so that comparing two nodes' shapes is a
    [discriminate] per case rather than a [w64] computation. *)
Definition tcode_nat (x : term) : nat :=
  match x with
  | TVar _ => 1 | TPat _ => 2 | TResult => 3 | TInt _ => 4
  | TBool _ => 5 | TUnit => 6 | TNull => 7
  | TPlus _ _ => 8 | TMinus _ _ => 9 | TMul _ _ => 10
  | TNeg _ => 11 | TEq _ _ => 12
  | TLt sg _ _ => (if sg then 13 else 14)%nat
  | TLe sg _ _ => (if sg then 15 else 16)%nat
  | TNot _ => 17 | TIte _ _ _ => 18 | TExec => 19 | TRet _ => 20
  end.

Definition w64_nat (w : w64) : nat := uint.nat w.

Lemma tcode_nat_code x : w64_nat (term_code x) = tcode_nat x.
Proof. destruct x; simpl; try (by vm_compute); destruct signed; by vm_compute. Qed.

Lemma term_eq_nodes x y :
  term_idx_wf x → term_idx_wf y →
  term_code x = term_code y → term_num x = term_num y →
  term_a x = term_a y → term_b x = term_b y → term_c x = term_c y → x = y.
Proof.
  intros Hwx Hwy Hc Hn Ha Hb Hc2.
  apply (f_equal w64_nat) in Hc. rewrite !tcode_nat_code in Hc.
  destruct x, y;
    repeat match goal with sg : bool |- _ => destruct sg end;
    simpl in *; try discriminate; try congruence.
Qed.

(** * What a successful [matchTerm] establishes *)

Lemma has_pat_node' x :
  has_pat x = false →
  ohas_pat (term_a x) = false ∧ ohas_pat (term_b x) = false ∧ ohas_pat (term_c x) = false.
Proof. destruct x; simpl; rewrite ?orb_false_iff; tauto. Qed.

(** When the actual term has no pattern variables (every path term), the
    pattern instantiated with the final substitution *is* the actual term. *)
Lemma match_rel_inst pats pok PV r ox oy σ σ' :
  match_rel pats pok PV r ox oy σ σ' →
  has_pat r = false → has_result r = false → ohas_pat oy = false →
  oinstantiate_t ox σ' (Some r) = oy.
Proof.
  intros Hm Hpr Hrr. induction Hm as [σ|n y s σ Hn ???|n y σ Hn ?|oy σ σ' Hm IH
    |x y σ σ1 σ2 σ3 Hp Hr Hc Hnum Hwx Hwy Ha IHa Hb IHb Hcc IHc]; intros Hpy; simpl.
  - done.
  - rewrite list_lookup_insert_eq //. by eapply lookup_lt_Some.
  - by rewrite Hn.
  - specialize (IH Hpy). simpl in IH. rewrite inst_nopat // in IH.
  - simpl in Hpy. destruct (has_pat_node' y Hpy) as (Hpa & Hpb & Hpc).
    specialize (IHa Hpa). specialize (IHb Hpb). specialize (IHc Hpc).
    pose proof (match_rel_ext _ _ _ _ _ _ _ _ Hb) as E12.
    pose proof (match_rel_ext _ _ _ _ _ _ _ _ Hcc) as E23.
    destruct (inst_Some_r x σ3 (Some r)) as [x' Hx']; first by eexists.
    destruct (inst_node x σ3 (Some r) x' Hp Hr Hx') as (Hc' & Hn' & Ha' & Hb' & Hc'' & Hw').
    rewrite Hx'. f_equal. apply term_eq_nodes; auto; try congruence.
    + rewrite Ha'. destruct (term_a x) as [p|] eqn:Ep; simpl in *; last done.
      destruct (term_a y) as [q|]; simpl in *.
      * eapply inst_ext; [|exact IHa|done]. eauto using subst_ext_trans.
      * destruct (inst_Some_r p σ1 (Some r)) as [? E']; first by eexists. congruence.
    + rewrite Hb'. destruct (term_b x) as [p|] eqn:Ep; simpl in *; last done.
      destruct (term_b y) as [q|]; simpl in *.
      * by eapply inst_ext.
      * destruct (inst_Some_r p σ2 (Some r)) as [? E']; first by eexists. congruence.
Qed.


(** * Scoping *)

(** Like [vars_below], but for a postcondition's terms, which may mention
    pattern variables and [ret]. *)
Fixpoint pvars_below (k : nat) (t : term) : Prop :=
  match t with
  | TVar n => (n < k)%nat
  | TPat _ | TResult | TInt _ | TBool _ | TUnit | TNull | TExec => True
  | TPlus a b | TMinus a b | TMul a b | TEq a b | TLt _ a b | TLe _ a b =>
      pvars_below k a ∧ pvars_below k b
  | TNeg a | TNot a | TRet a => pvars_below k a
  | TIte c a b => pvars_below k c ∧ pvars_below k a ∧ pvars_below k b
  end.

(** A term [sortOfEnv] accepts mentions only the logical variables in the
    environment's table. *)
Lemma sort_of_pvars E t s : sort_of E t = Some s → pvars_below (length (se_vars E)) t.
Proof.
  revert s. induction t; simpl; intros s Hs; try done;
    repeat match goal with
    | H : context [match sort_of E ?u with _ => _ end] |- _ =>
        destruct (sort_of E u) as [[]|] eqn:?; try discriminate H
    end;
    repeat match goal with
    | H : context [decide ?P] |- _ => destruct (decide P); try discriminate H
    end;
    eauto 10.
  by eapply lookup_lt_Some.
Qed.

Lemma vars_below_nopat k t : vars_below k t → has_pat t = false ∧ has_result t = false.
Proof. induction t; simpl; intros; destruct_and?; rewrite ?orb_false_iff; naive_solver. Qed.

(** An atom of a well-sorted disjunct: a pure or points-to atom whose terms
    mention only logical variables below [k]. *)
Definition atom_scoped (k : nat) (a : cassn) : Prop :=
  match a with
  | CAPure x => pvars_below k x
  | CAPointsTo x v => pvars_below k x ∧ pvars_below k v
  | _ => False
  end.

(** * Phase 1: the points-to atoms *)

Definition is_pts (a : cassn) : bool := match a with CAPointsTo _ _ => true | _ => false end.
Definition is_pure (a : cassn) : bool := match a with CAPure _ => true | _ => false end.

Lemma is_pts_inv a : is_pts a = true → ∃ x v, a = CAPointsTo x v.
Proof. destruct a; try discriminate. eauto. Qed.
Lemma is_pure_inv a : is_pure a = true → ∃ x, a = CAPure x.
Proof. destruct a; try discriminate. eauto. Qed.

(** What one successful [matchAtom] on the points-to atom [x ↦ v] did: either
    nothing (its location is not resolved yet), or it claimed a free cell
    whose location is the instantiated [x], and matched [v] against the
    cell's value. *)
Definition atom_step (H : list scell) (pats : list sort) (pok : list bool)
    (PV : list sort) (r : term) (x v : term)
    (σ : list (option term)) (used : list bool) (ok : bool)
    (σ' : list (option term)) (used' : list bool) : Prop :=
  (ok = false ∧ σ' = σ ∧ used' = used) ∨
  (ok = true ∧ ∃ j c,
     instantiate_t x σ (Some r) = Some (cloc c) ∧ has_pat (cloc c) = false ∧
     H !! j = Some c ∧ used !! j = Some false ∧ used' = <[j := true]> used ∧
     match_rel pats pok PV r (Some v) (Some (cval c)) σ σ').

(** The invariant of phase 1: each resolved atom [i] owns the cell [f i]
    (distinct atoms, distinct cells, all marked used), whose location is the
    atom's instantiated location and whose value its value matched. *)
Record phase1_inv (H : list scell) (atoms : list cassn) (pats : list sort)
    (pok : list bool) (PV : list sort) (r : term)
    (σ : list (option term)) (used done : list bool) : Prop := {
  p1_len_σ : length σ = length pats;
  p1_len_used : length used = length H;
  p1_len_done : length done = length atoms;
  p1_wf : subst_wf pats pok PV σ;
  p1_map : ∃ f : nat → nat,
    (∀ i, done !! i = Some true →
       ∃ x v c σ0 σ1,
         atoms !! i = Some (CAPointsTo x v) ∧ H !! f i = Some c ∧
         used !! f i = Some true ∧
         instantiate_t x σ0 (Some r) = Some (cloc c) ∧ has_pat (cloc c) = false ∧
         match_rel pats pok PV r (Some v) (Some (cval c)) σ0 σ1 ∧ subst_ext σ1 σ) ∧
    (∀ i i', done !! i = Some true → done !! i' = Some true → f i = f i' → i = i')
}.

Lemma phase1_inv_init H atoms pats pok PV r :
  phase1_inv H atoms pats pok PV r
    (replicate (length pats) None) (replicate (length H) false)
    (replicate (length atoms) false).
Proof.
  split; rewrite ?length_replicate //.
  - apply subst_wf_empty.
  - exists id. split.
    + intros i Hi. apply lookup_replicate in Hi as [? _]. done.
    + intros i ? Hi. apply lookup_replicate in Hi as [? _]. done.
Qed.

Lemma phase1_inv_skip H atoms pats pok PV r x v σ used done σ' used' :
  phase1_inv H atoms pats pok PV r σ used done →
  atom_step H pats pok PV r x v σ used false σ' used' →
  phase1_inv H atoms pats pok PV r σ' used' done.
Proof. intros Hi [(_ & -> & ->)|[? _]]; [done|discriminate]. Qed.

Lemma phase1_inv_step H atoms pats pok PV r x v σ used done σ' used' i :
  phase1_inv H atoms pats pok PV r σ used done →
  atoms !! i = Some (CAPointsTo x v) → done !! i = Some false →
  atom_step H pats pok PV r x v σ used true σ' used' →
  phase1_inv H atoms pats pok PV r σ' used' (<[i := true]> done).
Proof.
  intros [Hlσ Hlu Hld Hwf (f & Hf & Hinj)] Hat Hdi
    [[? _]|(_ & j & c & Hx & Hpx & Hj & Huj & -> & Hm)]; first discriminate.
  pose proof (match_rel_ext _ _ _ _ _ _ _ _ Hm) as Hext.
  assert (i < length done)%nat by (by eapply lookup_lt_Some).
  (* a resolved atom's cell is used, so it is not [j] *)
  assert (∀ i', done !! i' = Some true → f i' ≠ j) as Hne.
  { intros i' Hi' Heq. destruct (Hf i' Hi') as (?&?&?&?&?&_&_&Hu&_). rewrite Heq in Hu. congruence. }
  split.
  - rewrite (match_rel_len _ _ _ _ _ _ _ _ Hm). done.
  - by rewrite length_insert.
  - by rewrite length_insert.
  - by eapply match_rel_wf.
  - exists (λ i', if decide (i' = i) then j else f i'). split.
    + intros i' Hi'. cbv beta. destruct (decide (i' = i)) as [->|Hii].
      * exists x, v, c, σ, σ'. split_and!; try done.
        -- rewrite list_lookup_insert_eq //. by eapply lookup_lt_Some.
        -- apply subst_ext_refl.
      * rewrite list_lookup_insert_ne // in Hi'.
        destruct (Hf i' Hi') as (x' & v' & c' & σ0 & σ1 & ? & ? & ? & ? & ? & ? & ?).
        exists x', v', c', σ0, σ1. split_and!; try done.
        -- rewrite list_lookup_insert_ne //. by apply not_eq_sym, Hne.
        -- by eapply subst_ext_trans.
    + intros i1 i2 Hi1 Hi2. cbv beta.
      destruct (decide (i1 = i)) as [->|H1]; destruct (decide (i2 = i)) as [->|H2]; try done.
      * rewrite list_lookup_insert_ne // in Hi2. intros Heq. by destruct (Hne i2 Hi2).
      * rewrite list_lookup_insert_ne // in Hi1. intros Heq. by destruct (Hne i1 Hi1).
      * rewrite list_lookup_insert_ne // in Hi1. rewrite list_lookup_insert_ne // in Hi2.
        by apply Hinj.
Qed.

(** The number of points-to atoms not resolved yet: [remaining] in
    [matchHeap]. *)
Fixpoint undone (atoms : list cassn) (done : list bool) : nat :=
  match atoms, done with
  | a :: atoms', d :: done' => ((if is_pts a && negb d then 1 else 0) + undone atoms' done')%nat
  | _, _ => 0%nat
  end.

(** Mirrors [countPointsTo]. *)
Fixpoint count_pts (atoms : list cassn) : nat :=
  match atoms with
  | [] => 0%nat
  | a :: atoms' => ((if is_pts a then 1 else 0) + count_pts atoms')%nat
  end.

Lemma count_pts_app l1 l2 : count_pts (l1 ++ l2) = (count_pts l1 + count_pts l2)%nat.
Proof. induction l1 as [|a l1 IH]; simpl; lia. Qed.

Lemma count_pts_undone atoms : count_pts atoms = undone atoms (replicate (length atoms) false).
Proof.
  induction atoms as [|a atoms IH]; first done.
  simpl. rewrite IH. destruct (is_pts a); simpl; lia.
Qed.

Lemma undone_le atoms done : (undone atoms done ≤ length atoms)%nat.
Proof.
  revert done. induction atoms as [|a atoms IH]; intros [|d done]; simpl; try lia.
  specialize (IH done). destruct (is_pts a && negb d); lia.
Qed.

Lemma undone_insert atoms done i x v :
  atoms !! i = Some (CAPointsTo x v) → done !! i = Some false →
  (undone atoms (<[i := true]> done) + 1)%nat = undone atoms done.
Proof.
  revert done i. induction atoms as [|a atoms IH]; intros [|d done] [|i] Ha Hd; simpl in *; try discriminate.
  - simplify_eq; simpl; lia.
  - rewrite -(IH done i) //. lia.
Qed.

Lemma undone_zero atoms done i x v :
  length done = length atoms → undone atoms done = 0%nat →
  atoms !! i = Some (CAPointsTo x v) → done !! i = Some true.
Proof.
  revert done i. induction atoms as [|a atoms IH]; intros [|d done] [|i] Hl Hu Ha;
    simpl in *; try discriminate.
  - simplify_eq; destruct d; simpl in Hu; [done|lia].
  - apply (IH done i); [lia|lia|done].
Qed.

(** * Phase 2: the pure atoms *)

(** What a successful [checkPure] established. *)
Definition pure_ok (pc : list term) (atoms : list cassn) (σ : list (option term)) (r : term)
  : Prop :=
  ∀ i x, atoms !! i = Some (CAPure x) →
    ∃ y, instantiate_t x σ (Some r) = Some y ∧ has_pat y = false ∧
         cond_holds pc (Some y) = true.

(** * Evaluation *)

Section teval.
Context {ext : ffi_syntax}.

(** Instantiating is substitution: evaluating a pattern under a valuation
    that sends each bound pattern variable to the value of its term, and
    [ret] to the value of the return term, gives the value of the instance. *)
Lemma inst_teval (θ W : nat → val) (V' : valuation) (r : term) σ k :
  (∀ n, (n < k)%nat → θ n = vvar V' n) →
  (∀ n y, σ !! n = Some (Some y) → W n = teval V' y) →
  ∀ x y, pvars_below k x → instantiate_t x σ (Some r) = Some y → has_pat y = false →
  teval (mkVal θ W (teval V' r)) x = teval V' y.
Proof.
  intros Hθ HW x. induction x; intros y Hb Hi Hp; simpl in Hi, Hb; inst_destr;
    try (injection Hi as <-);
    simpl in Hp |- *; rewrite ?orb_false_iff in Hp; destruct_and?;
    repeat match goal with
    | IH : ∀ y, _ → Some ?t = Some y → _ |- _ => rewrite (IH t) //; clear IH
    end; try done.
  - by apply Hθ.
  - destruct (σ !! n) as [[z|]|] eqn:Hn; simplify_eq; try done. by apply HW.
Qed.

(** A default value of each sort, for the declared pattern variables that
    phase 1 left unbound (they occur in no atom, or phase 2 would have
    failed). *)
Definition sort_default (s : sort) : val :=
  match s with SInt => ival (W64 0) | SBool => bval false | SLoc => lval null | SUnit => uval end.

Lemma sort_default_has_sort s : has_sort (sort_default s) s.
Proof. destruct s; rewrite /has_sort /sort_default; eauto. Qed.

(** The witnesses for the disjunct's [∃]s. *)
Definition pat_witness (V' : valuation) (σ : list (option term)) (pats : list sort)
    (pok : list bool) (n : nat) : val :=
  match σ !! n with
  | Some (Some y) => teval V' y
  | _ => match pok !! n, pats !! n with
         | Some true, Some s => sort_default s
         | _, _ => uval
         end
  end.

(** The facts [condHolds] accepts are true. *)
Lemma cond_holds_sound (V : valuation) pc y :
  pc_sat V pc → cond_holds pc (Some y) = true → teval V y = bval true.
Proof.
  intros Hpc. simpl. rewrite orb_true_iff. intros [Hin|Hr].
  - apply Hpc. by apply bool_decide_eq_true in Hin.
  - destruct y; simpl in Hr; try discriminate.
    + by subst.
    + apply bool_decide_eq_true in Hr as ->. simpl. by rewrite bool_decide_eq_true_2.
Qed.

End teval.

(** * The soundness of a successful match *)

Section sound.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Set Default Proof Using "All".

Lemma big_sepL_seq_lookup {A} `{!Inhabited A} (Φ : A → iProp Σ) (l : list A) :
  ([∗ list] c ∈ l, Φ c) ⊣⊢ [∗ list] j ∈ seq 0 (length l), Φ (l !!! j).
Proof.
  assert ((λ j, l !!! j) <$> seq 0 (length l) = l) as Heq.
  { apply list_eq. intros i. rewrite list_lookup_fmap.
    destruct (decide (i < length l)%nat) as [Hi|Hi].
    - rewrite lookup_seq_lt //=. symmetry. apply list_lookup_lookup_total_lt. done.
    - rewrite lookup_ge_None_2; last (rewrite length_seq; lia).
      rewrite lookup_ge_None_2 //. lia. }
  rewrite -{1}Heq big_sepL_fmap. done.
Qed.

(** Handing each points-to atom its own cell, and dropping the cells no atom
    asked for. [R] is the list of cells still available. *)
Lemma atoms_from_cells (P : nat → iProp Σ) (Q : cassn → iProp Σ)
    (atoms : list cassn) (g : nat → nat) (R : list nat) :
  (∀ i a, atoms !! i = Some a → is_pts a = true → g i ∈ R) →
  (∀ i i' a a', atoms !! i = Some a → atoms !! i' = Some a' →
     is_pts a = true → is_pts a' = true → g i = g i' → i = i') →
  (∀ i a, atoms !! i = Some a → is_pts a = false → ⊢ Q a) →
  (∀ i a, atoms !! i = Some a → is_pts a = true → P (g i) ⊢ Q a) →
  ([∗ list] j ∈ R, P j) ⊢ [∗ list] a ∈ atoms, Q a.
Proof.
  revert g R. induction atoms as [|a atoms IH]; intros g R Hin Hinj Hpure Hpts.
  { iIntros "_". done. }
  rewrite big_sepL_cons.
  destruct (is_pts a) eqn:Ha.
  - destruct (elem_of_Permutation R (g 0%nat)) as [[R' HR] _]; first by apply (Hin 0%nat a).
    rewrite HR big_sepL_cons. iIntros "[HP HR]". iSplitL "HP".
    { by iApply (Hpts 0%nat a with "HP"). }
    iApply (IH (λ i, g (S i)) R' with "HR").
    + intros i a' Ha' Hp'.
      assert (g (S i) ∈ g 0%nat :: R') as Hc by (rewrite -HR; by apply (Hin (S i) a')).
      apply elem_of_cons in Hc as [Hc|Hc]; last done.
      by pose proof (Hinj (S i) 0%nat a' a Ha' eq_refl Hp' Ha Hc).
    + intros i i' b b' Hb Hb' Hp Hp' Heq. by pose proof (Hinj (S i) (S i') b b' Hb Hb' Hp Hp' Heq) as [= ?].
    + intros i b Hb Hp. by apply (Hpure (S i) b).
    + intros i b Hb Hp. by apply (Hpts (S i) b).
  - iIntros "HR". iSplitR.
    { by iApply (Hpure 0%nat a). }
    iApply (IH (λ i, g (S i)) R with "HR").
    + intros i a' Ha' Hp'. by apply (Hin (S i) a').
    + intros i i' b b' Hb Hb' Hp Hp' Heq. by pose proof (Hinj (S i) (S i') b b' Hb Hb' Hp Hp' Heq) as [= ?].
    + intros i b Hb Hp. by apply (Hpure (S i) b).
    + intros i b Hb Hp. by apply (Hpts (S i) b).
Qed.

(** The matcher's soundness: phase 0 (every atom is scoped by the declared
    variables), phase 1 (every points-to atom resolved) and phase 2 (every
    pure atom justified) together give [path_sat_dj]. *)
Lemma match_path_sat (vars : list sort) (sp : spath) (dj : cdisjunct)
    (σ : list (option term)) (used done : list bool) :
  length (d_pats dj) = length (d_pat_ok dj) →
  (∀ a, a ∈ d_atoms dj → atom_scoped (length vars) a) →
  phase1_inv (sheap (pst sp)) (d_atoms dj) (d_pats dj) (d_pat_ok dj)
    (svars (pst sp)) (pret sp) σ used done →
  undone (d_atoms dj) done = 0%nat →
  pure_ok (spc (pst sp)) (d_atoms dj) σ (pret sp) →
  path_sat_dj_at vars sp dj.
Proof.
  intros Hlpats Hscoped [Hlσ Hlu Hld Hswf (f & Hf & Hinj)] Hundone Hpure.
  intros θ V' Hθ Hag Hst Hwf Hlen Hr.
  destruct Hag as (Hagv & _ & _). simpl in Hagv.
  destruct (vars_below_nopat _ _ Hr) as [Hpr Hrr].
  set (W := pat_witness V' σ (d_pats dj) (d_pat_ok dj)).
  assert (∀ n y, σ !! n = Some (Some y) → W n = teval V' y) as HW.
  { intros n y Hn. rewrite /W /pat_witness Hn //. }
  destruct Hst as [Hsv Hpc].
  iIntros "HH". rewrite /dj_interp. iExists W. iSplit; [|iSplit].
  - iPureIntro. intros n Hn. rewrite /W /pat_witness.
    destruct (σ !! n) as [[y|]|] eqn:Hσ.
    + destruct (Hswf n y Hσ) as (_ & s & Hs & Hsy). exists s. split; first done.
      by eapply sort_of_vars_sound.
    + rewrite Hn. destruct (d_pats dj !! n) as [s|] eqn:Hp.
      * exists s. split; first done. apply sort_default_has_sort.
      * exfalso. apply lookup_ge_None_1 in Hp. apply lookup_lt_Some in Hn. lia.
    + rewrite Hn. destruct (d_pats dj !! n) as [s|] eqn:Hp.
      * exists s. split; first done. apply sort_default_has_sort.
      * exfalso. apply lookup_ge_None_1 in Hp. apply lookup_lt_Some in Hn. lia.
  - iPureIntro. intros n Hn. rewrite /W /pat_witness /=.
    destruct (σ !! n) as [[y|]|] eqn:Hσ.
    + destruct (Hswf n y Hσ) as (Hok & _). done.
    + destruct (d_pat_ok dj !! n) as [[]|]; done.
    + destruct (d_pat_ok dj !! n) as [[]|]; done.
  - rewrite /heap_interp big_sepL_seq_lookup.
    iApply (atoms_from_cells _ _ _ f with "HH").
    + intros i a Ha Hp. destruct a as [| | | | |x v]; try discriminate.
      pose proof (undone_zero _ _ _ _ _ Hld Hundone Ha) as Hdi.
      destruct (Hf i Hdi) as (? & ? & c & ? & ? & _ & Hc & _).
      apply elem_of_seq. apply lookup_lt_Some in Hc. lia.
    + intros i i' a a' Ha Ha' Hp Hp' Heq.
      destruct a as [| | | | |x v]; try discriminate.
      destruct a' as [| | | | |x' v']; try discriminate.
      apply Hinj; [by eapply undone_zero|by eapply undone_zero|done].
    + intros i a Ha Hp.
      pose proof (Hscoped a (list_elem_of_lookup_2 _ _ _ Ha)) as Hsc.
      destruct a as [| | | |x|x v]; try done.
      destruct (Hpure i x Ha) as (y & Hy & Hpy & Hch).
      iPureIntro. simpl.
      rewrite (inst_teval θ W V' (pret sp) σ (length vars) Hagv HW x y Hsc Hy Hpy).
      by eapply cond_holds_sound.
    + intros i a Ha Hp. destruct a as [| | | | |x v]; try discriminate.
      pose proof (Hscoped _ (list_elem_of_lookup_2 _ _ _ Ha)) as [Hsx Hsv'].
      pose proof (undone_zero _ _ _ _ _ Hld Hundone Ha) as Hdi.
      destruct (Hf i Hdi) as (x' & v' & c & σ0 & σ1 & Ha' & Hc & _ & Hx & Hpx & Hm & Hext).
      rewrite Ha in Ha'. injection Ha' as <- <-.
      pose proof (match_rel_ext _ _ _ _ _ _ _ _ Hm) as Hext01.
      assert (c ∈ sheap (pst sp)) as Hcin by (by eapply list_elem_of_lookup_2).
      destruct (wf_heap _ Hwf c Hcin) as [_ Hbv].
      destruct (vars_below_nopat _ _ Hbv) as [Hpv _].
      pose proof (match_rel_inst _ _ _ _ _ _ _ _ Hm Hpr Hrr Hpv) as Hiv. simpl in Hiv.
      assert (instantiate_t x σ (Some (pret sp)) = Some (cloc c)) as Hx'.
      { eapply inst_ext; [|exact Hx|done]. by eapply subst_ext_trans. }
      assert (instantiate_t v σ (Some (pret sp)) = Some (cval c)) as Hv'.
      { by eapply inst_ext. }
      rewrite (list_lookup_total_correct _ _ _ Hc). simpl.
      rewrite (inst_teval θ W V' (pret sp) σ (length vars) Hagv HW x _ Hsx Hx' Hpx).
      rewrite (inst_teval θ W V' (pret sp) σ (length vars) Hagv HW v _ Hsv' Hv' Hpv).
      iIntros "H". iExact "H".
Qed.

End sound.
