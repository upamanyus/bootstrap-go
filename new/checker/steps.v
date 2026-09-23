(** Per-instruction WP lemmas at the types of the fragment.

    The exec proof needs, for every supported [ctype], the step the GooseLang
    instruction takes, phrased in the untyped vocabulary the symbolic heap and
    [teval] use ([ival]/[bval]/[lval]/[uval] and [heap_pointsto]) rather than
    in the [IntoValTyped] vocabulary of [new/golang/theory]. That is what this
    file provides. *)
From New.proof Require Import proof_prelude.
From New.golang Require Import theory.
From New.generatedproof.github_com.mit_pdos.perennial Require Import checker.
From New.checker Require Import defs term_lemmas subst.

Set Default Proof Using "All".

Section steps.
Context `{hG: heapGS Σ, !ffi_semantics _ _}.
Context {sem : go.Semantics}.
Set Default Proof Using "All".

(** * [into_val] at the four value shapes *)

Lemma ival_eq (w : w64) : #w = ival w.
Proof. by rewrite go.into_val_unfold. Qed.
Lemma bval_eq (b : bool) : #b = bval b.
Proof. by rewrite go.into_val_unfold. Qed.
Lemma lval_eq (l : loc) : #l = lval l.
Proof. by rewrite go.into_val_unfold. Qed.
Lemma uval_eq : #() = uval.
Proof. by rewrite go.into_val_unfold. Qed.
Lemma sval_eq (s : go_string) : #s = LitV (LitString s).
Proof. by rewrite go.into_val_unfold. Qed.

(** * The sort of a supported type

    Every [ctype] is supported, so unlike [TypeSort] in checker/sorts.go this
    is total. *)
Definition ctype_sort (t : ctype) : sort :=
  match t with
  | CTyInt | CTyInt64 | CTyUint64 => SInt
  | CTyBool => SBool
  | CTyPtr _ => SLoc
  end.

(** Mirrors [typeSigned]. *)
Definition ctype_signed (t : ctype) : bool :=
  match t with CTyInt | CTyInt64 => true | _ => false end.

(** The zero value, mirroring [typeZero]. *)
Definition ctype_zero (t : ctype) : term :=
  match t with
  | CTyInt | CTyInt64 | CTyUint64 => TInt (W64 0)
  | CTyBool => TBool false
  | CTyPtr _ => TNull
  end.

(** * Memory

    Stated over the untyped [heap_pointsto] so that the same lemma covers
    every supported type; [assn_interp] in the statement of soundness uses
    [heap_pointsto] for the same reason. *)

(** The typed points-to of each of the three value types the fragment uses is
    the untyped one (the [TypedPointsto] instances in
    new/golang/theory/postlifting.v are all [heap_pointsto l dq #v]); the
    extra [l ≠ null] it carries is already implied by [heap_pointsto]. *)
Lemma pointsto_w64 l dq (w : w64) : l ↦{dq} w ⊣⊢ heap_pointsto l dq #w.
Proof.
  rewrite typed_pointsto_unseal /typed_pointsto_wrap /=.
  iSplit; first by iIntros "[$ _]".
  iIntros "H". iDestruct (heap_pointsto_non_null with "H") as %?. by iFrame.
Qed.

Lemma pointsto_bool l dq (b : bool) : l ↦{dq} b ⊣⊢ heap_pointsto l dq #b.
Proof.
  rewrite typed_pointsto_unseal /typed_pointsto_wrap /=.
  iSplit; first by iIntros "[$ _]".
  iIntros "H". iDestruct (heap_pointsto_non_null with "H") as %?. by iFrame.
Qed.

Lemma pointsto_loc l dq (lo : loc) : l ↦{dq} lo ⊣⊢ heap_pointsto l dq #lo.
Proof.
  rewrite typed_pointsto_unseal /typed_pointsto_wrap /=.
  iSplit; first by iIntros "[$ _]".
  iIntros "H". iDestruct (heap_pointsto_non_null with "H") as %?. by iFrame.
Qed.

Lemma wp_ctype_load t l dq v :
  has_sort v (ctype_sort t) →
  {{{ heap_pointsto l dq v }}} ![type_of t] #l {{{ RET v; heap_pointsto l dq v }}}.
Proof.
  intros Hs. iIntros (Φ) "Hl HΦ". destruct t; simpl in Hs.
  - destruct Hs as [w ->]. rewrite -ival_eq -pointsto_w64.
    wp_apply (wp_load (V:=w64) with "Hl"). iIntros "Hl". by iApply "HΦ".
  - destruct Hs as [w ->]. rewrite -ival_eq -pointsto_w64.
    wp_apply (wp_load (V:=w64) with "Hl"). iIntros "Hl". by iApply "HΦ".
  - destruct Hs as [w ->]. rewrite -ival_eq -pointsto_w64.
    wp_apply (wp_load (V:=w64) with "Hl"). iIntros "Hl". by iApply "HΦ".
  - destruct Hs as [b ->]. rewrite -bval_eq -pointsto_bool.
    wp_apply (wp_load (V:=bool) with "Hl"). iIntros "Hl". by iApply "HΦ".
  - destruct Hs as [lo ->]. rewrite -lval_eq -pointsto_loc.
    wp_apply (wp_load (V:=loc) with "Hl"). iIntros "Hl". by iApply "HΦ".
Qed.

Lemma wp_ctype_store t l v w :
  has_sort v (ctype_sort t) → has_sort w (ctype_sort t) →
  {{{ heap_pointsto l (DfracOwn 1) v }}}
    GoStore (type_of t) (#l, w)%V
  {{{ RET #(); heap_pointsto l (DfracOwn 1) w }}}.
Proof.
  intros Hv Hw. iIntros (Φ) "Hl HΦ". destruct t; simpl in Hv, Hw.
  - destruct Hv as [x ->]. destruct Hw as [y ->].
    rewrite -!ival_eq -pointsto_w64.
    wp_apply (wp_store (V:=w64) with "Hl"). iIntros "Hl".
    iApply "HΦ". by rewrite -pointsto_w64.
  - destruct Hv as [x ->]. destruct Hw as [y ->].
    rewrite -!ival_eq -pointsto_w64.
    wp_apply (wp_store (V:=w64) with "Hl"). iIntros "Hl".
    iApply "HΦ". by rewrite -pointsto_w64.
  - destruct Hv as [x ->]. destruct Hw as [y ->].
    rewrite -!ival_eq -pointsto_w64.
    wp_apply (wp_store (V:=w64) with "Hl"). iIntros "Hl".
    iApply "HΦ". by rewrite -pointsto_w64.
  - destruct Hv as [x ->]. destruct Hw as [y ->].
    rewrite -!bval_eq -pointsto_bool.
    wp_apply (wp_store (V:=bool) with "Hl"). iIntros "Hl".
    iApply "HΦ". by rewrite -pointsto_bool.
  - destruct Hv as [x ->]. destruct Hw as [y ->].
    rewrite -!lval_eq -pointsto_loc.
    wp_apply (wp_store (V:=loc) with "Hl"). iIntros "Hl".
    iApply "HΦ". by rewrite -pointsto_loc.
Qed.

Lemma wp_ctype_alloc t v :
  has_sort v (ctype_sort t) →
  {{{ True }}} GoAlloc (type_of t) v {{{ (l : loc), RET #l; heap_pointsto l (DfracOwn 1) v }}}.
Proof.
  intros Hv. iIntros (Φ) "_ HΦ". destruct t; simpl in Hv.
  - destruct Hv as [x ->]. rewrite -ival_eq.
    wp_apply (wp_alloc (V:=w64)). iIntros (l) "Hl". iApply "HΦ". by rewrite -pointsto_w64.
  - destruct Hv as [x ->]. rewrite -ival_eq.
    wp_apply (wp_alloc (V:=w64)). iIntros (l) "Hl". iApply "HΦ". by rewrite -pointsto_w64.
  - destruct Hv as [x ->]. rewrite -ival_eq.
    wp_apply (wp_alloc (V:=w64)). iIntros (l) "Hl". iApply "HΦ". by rewrite -pointsto_w64.
  - destruct Hv as [x ->]. rewrite -bval_eq.
    wp_apply (wp_alloc (V:=bool)). iIntros (l) "Hl". iApply "HΦ". by rewrite -pointsto_bool.
  - destruct Hv as [x ->]. rewrite -lval_eq.
    wp_apply (wp_alloc (V:=loc)). iIntros (l) "Hl". iApply "HΦ". by rewrite -pointsto_loc.
Qed.

(** [GoZeroVal] produces exactly the term [typeZero] builds. *)
Lemma ctype_zero_sort V t : has_sort (teval V (ctype_zero t)) (ctype_sort t).
Proof. destruct t; simpl; rewrite /has_sort; eauto. Qed.

Lemma wp_ctype_zero t V Φ :
  Φ (teval V (ctype_zero t)) -∗ WP GoZeroVal (type_of t) #() {{ Φ }}.
Proof.
  iIntros "HΦ". destruct t; simpl; wp_pures.
  - by rewrite ival_eq.
  - by rewrite ival_eq.
  - by rewrite ival_eq.
  - by rewrite bval_eq.
  - by rewrite lval_eq.
Qed.

(** * Operators

    [apply_binop]/[apply_unop] mirror the term-building half of [applyBinOp]
    and [applyUnOp] in checker/exec.go; the sort checks those functions also
    perform become hypotheses of the WP lemmas below. *)

Definition apply_binop (op : cop) (t : ctype) (a b : term) : option term :=
  match op with
  | COEq => if decide (ctype_sort t = SUnit) then None else Some (TEq a b)
  | COAdd => if decide (ctype_sort t = SInt) then Some (TPlus a b) else None
  | COSub => if decide (ctype_sort t = SInt) then Some (TMinus a b) else None
  | COMul => if decide (ctype_sort t = SInt) then Some (TMul a b) else None
  | COLt => if decide (ctype_sort t = SInt) then Some (TLt (ctype_signed t) a b) else None
  | COLe => if decide (ctype_sort t = SInt) then Some (TLe (ctype_signed t) a b) else None
  | COGt => if decide (ctype_sort t = SInt) then Some (TLt (ctype_signed t) b a) else None
  | COGe => if decide (ctype_sort t = SInt) then Some (TLe (ctype_signed t) b a) else None
  | CONeg | CONot => None
  end.

(** Unary minus exists only at the signed integer types: GooseLang has no
    [GoUnOp GoNeg] at [go.uint64] (see new/golang/defn/predeclared.v), which
    is why [applyUnOp] asks for [typeSigned]. *)
Definition apply_unop (op : cop) (t : ctype) (a : term) : option term :=
  match op with
  | CONeg => if decide (ctype_sort t = SInt) then
               (if ctype_signed t then Some (TNeg a) else None) else None
  | CONot => if decide (ctype_sort t = SBool) then Some (TNot a) else None
  | _ => None
  end.

(** The operands of a [GoOp] are [#x] for a Gallina [x]; these turn a
    [has_sort] fact into that form. *)
Lemma has_sort_int v : has_sort v SInt → ∃ w : w64, v = #w.
Proof. intros [w ->]. exists w. by rewrite ival_eq. Qed.
Lemma has_sort_bool v : has_sort v SBool → ∃ b : bool, v = #b.
Proof. intros [b ->]. exists b. by rewrite bval_eq. Qed.
Lemma has_sort_loc v : has_sort v SLoc → ∃ l : loc, v = #l.
Proof. intros [l ->]. exists l. by rewrite lval_eq. Qed.

(** [TEq] compares GooseLang values; [GoEquals] compares the Gallina values
    they come from. [into_val] is injective at each of these types. *)
Lemma bool_decide_iv_w64 (x y : w64) : bool_decide (#x = #y) = bool_decide (x = y).
Proof. apply bool_decide_ext. split; [apply (inj into_val)|by intros ->]. Qed.
Lemma bool_decide_iv_bool (x y : bool) : bool_decide (#x = #y) = bool_decide (x = y).
Proof. apply bool_decide_ext. split; [apply (inj into_val)|by intros ->]. Qed.
Lemma bool_decide_iv_loc (x y : loc) : bool_decide (#x = #y) = bool_decide (x = y).
Proof. apply bool_decide_ext. split; [apply (inj into_val)|by intros ->]. Qed.

Ltac op_operands :=
  repeat match goal with
         | H : has_sort _ SInt |- _ => apply has_sort_int in H as [? ->]
         | H : has_sort _ SBool |- _ => apply has_sort_bool in H as [? ->]
         | H : has_sort _ SLoc |- _ => apply has_sort_loc in H as [? ->]
         end.

(** After the instruction has stepped, the goal is the GooseLang result and
    the assumption is [teval] of the term the checker built; unfolding
    [into_val] lets both reduce to the same literal. *)
Ltac op_finish :=
  rewrite ?bool_decide_iv_w64 ?bool_decide_iv_bool ?bool_decide_iv_loc;
  rewrite ?(go.into_val_unfold w64) ?(go.into_val_unfold bool) ?(go.into_val_unfold loc);
  simpl; iExact "HΦ".

Lemma wp_binop op t a b r V Φ :
  apply_binop op t a b = Some r →
  has_sort (teval V a) (ctype_sort t) →
  has_sort (teval V b) (ctype_sort t) →
  Φ (teval V r) -∗
  WP GoOp (binop_of op) (type_of t) (teval V a, teval V b)%V {{ Φ }}.
Proof.
  rewrite /apply_binop. intros Hr Ha Hb. iIntros "HΦ".
  destruct op, t; simpl in Hr; cbn [ctype_sort] in Ha, Hb; simplify_eq;
    cbn [teval]; op_operands; wp_pures; op_finish.
Qed.

Lemma wp_unop op t a r V Φ :
  apply_unop op t a = Some r →
  has_sort (teval V a) (ctype_sort t) →
  Φ (teval V r) -∗
  WP GoUnOp (unop_of op) (type_of t) (teval V a) {{ Φ }}.
Proof.
  rewrite /apply_unop. intros Hr Ha. iIntros "HΦ".
  destruct op, t; simpl in Hr; cbn [ctype_sort] in Ha; simplify_eq;
    cbn [teval]; op_operands; wp_pures; op_finish.
Qed.

(** An identity conversion is the identity. *)
Lemma wp_convert t (v : val) (Φ : val → iProp Σ) :
  Φ v -∗ WP Convert (type_of t) (type_of t) (Val v) {{ Φ }}.
Proof. iIntros "HΦ". by wp_pures. Qed.

(** * The exception monad

    [teval] of [TExec]/[TRet] is exactly [execute_val]/[return_val], so the
    [PureWp] instances of new/golang/theory/exception.v apply directly. *)

Lemma exec_v_eq : exec_v = execute_val.
Proof.
  by rewrite execute_val_unseal /execute_val_def /exec_v sval_eq uval_eq.
Qed.

Lemma ret_v_eq (v : val) : ret_v v = return_val v.
Proof. by rewrite return_val_unseal /return_val_def /ret_v sval_eq. Qed.

Lemma wp_do (v : val) (Φ : val → iProp Σ) : Φ exec_v -∗ WP (do: (Val v))%E {{ Φ }}.
Proof. iIntros "HΦ". wp_pures. by rewrite exec_v_eq. Qed.

Lemma wp_return (v : val) (Φ : val → iProp Σ) : Φ (ret_v v) -∗ WP (return: (Val v))%E {{ Φ }}.
Proof. iIntros "HΦ". wp_pures. by rewrite ret_v_eq. Qed.

(** [;;;] runs its second argument only when the first executed normally. *)
Lemma wp_exc_seq_exec e2 (Φ : val → iProp Σ) :
  WP e2 {{ Φ }} -∗ WP (Val exec_v ;;; e2)%E {{ Φ }}.
Proof. iIntros "H". rewrite exec_v_eq. by wp_pures. Qed.

Lemma wp_exc_seq_ret (v : val) e2 (Φ : val → iProp Σ) :
  Φ (ret_v v) -∗ WP (Val (ret_v v) ;;; e2)%E {{ Φ }}.
Proof. iIntros "H". rewrite !ret_v_eq. by wp_pures. Qed.

Lemma wp_exc_do_exec (Φ : val → iProp Σ) : Φ uval -∗ WP exception_do (Val exec_v) {{ Φ }}.
Proof. iIntros "H". rewrite exec_v_eq. wp_pures. by rewrite uval_eq. Qed.

Lemma wp_exc_do_ret (v : val) (Φ : val → iProp Σ) :
  Φ v -∗ WP exception_do (Val (ret_v v)) {{ Φ }}.
Proof. iIntros "H". rewrite ret_v_eq. by wp_pures. Qed.

(** * Applying a curried function to its arguments

    [apply_vals (func_val f) (arg_vals f θ)] beta-reduces to the body with the
    parameters bound, which is exactly [csubst] under the environment
    [binds]. Later parameters shadow earlier ones, matching [envBind] in
    [Analyze]. *)

Definition apply_vals_e (h : expr) (vs : list val) : expr :=
  foldl (λ e v, App e (Val v)) h vs.

Lemma apply_vals_e_cons h v vs : apply_vals_e h (v :: vs) = apply_vals_e (App h (Val v)) vs.
Proof. done. Qed.

Lemma apply_vals_unfold (f : val) vs : apply_vals f vs = apply_vals_e (Val f) vs.
Proof. done. Qed.

(** The argument list is an evaluation context. *)
Definition app_ctx (vs : list val) : list ectx_item := AppLCtx <$> vs.

Lemma apply_vals_e_fill h vs : apply_vals_e h vs = fill (app_ctx vs) h.
Proof.
  revert h. induction vs as [|v vs IH]; intros h; first done.
  by rewrite /app_ctx fmap_cons /= -IH.
Qed.

(** These three are proved once with [B] abstract, so that applying one takes
    exactly the steps of a beta reduction and does not reduce the body. *)
Lemma wp_beta_recv x (B : expr) (v : val) (Ψ : val → iProp Σ) :
  WP subst x v B {{ Ψ }} -∗ WP App (Val (RecV BAnon (BNamed x) B)) (Val v) {{ Ψ }}.
Proof. iIntros "H". by wp_pures. Qed.

Lemma wp_beta_func x (B : expr) (v : val) (Ψ : val → iProp Σ) :
  WP subst x v B {{ Ψ }} -∗ WP App (Val #(func.mk BAnon (BNamed x) B)) (Val v) {{ Ψ }}.
Proof. iIntros "H". by wp_pures. Qed.

Lemma wp_beta_anon (B : expr) (v : val) (Ψ : val → iProp Σ) :
  WP B {{ Ψ }} -∗ WP App (Val (RecV BAnon BAnon B)) (Val v) {{ Ψ }}.
Proof. iIntros "H". by wp_pures. Qed.

(** Consuming the arguments one at a time. The postcondition is the "rest of
    the application", which is what makes the induction go through without an
    inverse bind rule (Perennial has none). *)
Lemma wp_lams xs vs m e (Φ : val → iProp Σ) :
  length xs = length vs →
  WP csubst (binds (pnames xs) vs m) e {{ Φ }} -∗
  WP lams xs (csubst (delete_names (pnames xs) m) e)
     {{ w, WP apply_vals_e (Val w) vs {{ Φ }} }}.
Proof.
  revert vs m Φ. induction xs as [|x xs IH]; intros vs m Φ Hlen; iIntros "H".
  { destruct vs; last done.
    rewrite /pnames /=.
    iApply (wp_wand_r _ _ _ Φ). iSplitL "H"; first iExact "H".
    iIntros (w) "H". by wp_pures. }
  destruct vs as [|v vs]; first done.
  cbn [lams]. wp_pures.
  rewrite apply_vals_e_cons apply_vals_e_fill.
  iApply wp_bind. iApply wp_beta_func.
  rewrite lams_step.
  iApply (wp_wand_r _ _ _ (λ w, WP apply_vals_e (Val w) vs {{ Φ }})%I).
  iSplitL "H".
  { iApply IH; first (simpl in Hlen; lia). by rewrite pnames_cons. }
  iIntros (w) "Hw". by rewrite apply_vals_e_fill.
Qed.

(** The top-level application: [func_val f] applied to its arguments. *)
Lemma wp_func_val f (args : list val) (Φ : val → iProp Σ) :
  length args = length f.(fparams) →
  f.(fparams) ≠ [] →
  WP csubst (binds (pnames f.(fparams)) args ∅) f.(fbody) {{ Φ }} -∗
  WP apply_vals (func_val f) args {{ Φ }}.
Proof.
  intros Hlen Hne. iIntros "H".
  destruct f as [ps body]. simpl in *. destruct ps as [|x xs]; first done.
  destruct args as [|v vs]; first done.
  rewrite pnames_cons binds_cons.
  rewrite apply_vals_unfold apply_vals_e_cons apply_vals_e_fill /func_val /=.
  iApply wp_bind. iApply wp_beta_recv.
  rewrite lams_step_empty.
  iApply (wp_wand_r _ _ _ (λ w, WP apply_vals_e (Val w) vs {{ Φ }})%I).
  iSplitL "H".
  { iApply (wp_lams xs vs); first (simpl in Hlen; lia). iExact "H". }
  iIntros (w) "Hw". by rewrite apply_vals_e_fill.
Qed.

Lemma wp_func_val_nil f θ (Φ : val → iProp Σ) :
  f.(fparams) = [] →
  WP expr_of f.(fbody) {{ Φ }} -∗
  WP apply_vals (func_val f) (arg_vals f θ) {{ Φ }}.
Proof.
  intros Hnil. iIntros "H". destruct f as [ps body]. simpl in *. subst ps.
  rewrite /apply_vals /arg_vals /func_val /=.
  by iApply wp_beta_anon.
Qed.

End steps.
