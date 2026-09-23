(** [checker.hasPat] (checker/match.go): does a term still mention a pattern
    variable?

    Naming: the Go function's local is [t], so no Rocq variable here is
    called [t]. *)
From New.checker Require Import prelude nodes.

Section proof.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics} {package_sem : checker.Assumptions}.
Set Default Proof Using "All - package_sem".

(** Mirrors [hasPat]: [TPat] anywhere below, reached through the [A], [B] and
    [C] fields, which is exactly [term_a]/[term_b]/[term_c]. *)
Fixpoint has_pat (x : term) : bool :=
  match x with
  | TPat _ => true
  | TPlus p q | TMinus p q | TMul p q | TEq p q | TLt _ p q | TLe _ p q =>
      has_pat p || has_pat q
  | TNeg p | TNot p | TRet p => has_pat p
  | TIte p q r => has_pat p || has_pat q || has_pat r
  | _ => false
  end.

Definition ohas_pat (x : option term) : bool :=
  match x with None => false | Some x' => has_pat x' end.

Definition is_tpat (x : term) : bool := match x with TPat _ => true | _ => false end.

(** The Go code walks the three child fields, so the mirror has to agree with
    that view of a node. *)
Lemma has_pat_node x :
  has_pat x = (is_tpat x || ohas_pat (term_a x) || ohas_pat (term_b x)
               || ohas_pat (term_c x))%bool.
Proof. destruct x; simpl; by rewrite ?orb_false_r. Qed.

Lemma is_tpat_code x : bool_decide (term_code x = W64 2) = is_tpat x.
Proof. destruct x; simpl; repeat case_match; by vm_compute. Qed.

Lemma wp_hasPat (l : loc) (ox : option term) :
  {{{ is_pkg_init checker ∗ is_oterm l ox }}}
    @! checker.hasPat #l
  {{{ RET #(ohas_pat ox); True }}}.
Proof using All.
  iLöb as "IH" forall (l ox).
  wp_start as "#Hox".
  iDestruct (is_oterm_null with "Hox") as %Hnull.
  wp_auto. wp_if_destruct.
  { assert (ox = None) as -> by naive_solver.
    iSpecialize ("HΦ" with "[//]"); iExact "HΦ". }
  destruct ox as [x|]; last naive_solver.
  iDestruct (is_term_node with "Hox") as (la lb lc) "(%Hw & #Hn & #Ha & #Hb & #Hc)".
  try wp_auto.
  rewrite /ohas_pat has_pat_node.
  wp_if_destruct.
  { (* the kind code says [TPat] *)
    assert (is_tpat x = true) as Hp.
    { rewrite -is_tpat_code. by apply bool_decide_eq_true_2. }
    rewrite Hp !orb_true_l. try wp_auto.
    iSpecialize ("HΦ" with "[//]"); iExact "HΦ". }
  assert (is_tpat x = false) as Hp.
  { rewrite -is_tpat_code. by apply bool_decide_eq_false_2. }
  rewrite Hp orb_false_l.
  (* the three children, each guarded by [if: <recursive call> then return: true] *)
  try wp_auto.
  wp_apply ("IH" $! la (term_a x) with "[$]").
  fold (ohas_pat (term_a x)).
  destruct (ohas_pat (term_a x)) eqn:Hfa.
  { rewrite !orb_true_l. try wp_auto.
    iSpecialize ("HΦ" with "[//]"); iExact "HΦ". }
  rewrite orb_false_l. try wp_auto.
  wp_apply ("IH" $! lb (term_b x) with "[$]").
  fold (ohas_pat (term_b x)).
  destruct (ohas_pat (term_b x)) eqn:Hfb.
  { rewrite !orb_true_l. try wp_auto.
    iSpecialize ("HΦ" with "[//]"); iExact "HΦ". }
  rewrite orb_false_l. try wp_auto.
  wp_apply ("IH" $! lc (term_c x) with "[$]").
  fold (ohas_pat (term_c x)). try wp_auto.
  iSpecialize ("HΦ" with "[//]"); iExact "HΦ".
Qed.

End proof.
