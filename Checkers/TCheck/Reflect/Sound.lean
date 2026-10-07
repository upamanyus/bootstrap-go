/-
Soundness of the Lean table checker (LCheck/TCheck/Check.lean):

    theorem ltcheck_sound (i : tinput) : ltcheck i = true → input_holds i

`input_holds i` (Checkers/TCheck/Denote.lean) is what the Go checker's
soundness axiom `check_adequate` (Checkers/TCheck/Observe.lean) claims for a
`true` answer of `tcheck.Check` on `ser_input i`. So `ltcheck_sound` with
`decide` (or `native_decide`) replaces both that axiom and the observation of
a Go run.

The proof: the precondition is the initial symbolic state (`addAtoms`); the
function's beta steps bind its parameters (`wp_func_val`); evaluation is sound
(`eval_sound`, Eval.lean); and the final state and value satisfy the
postcondition, with the existentials matching bound (`checkPost_sound`).
-/
import Checkers.TCheck.Reflect.Eval

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace TCheck
namespace LC

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic

section den
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {syms : List symdecl} {preds : List preddecl} (DA : DenAt GF syms preds)

theorem forall_sorts_intro : ∀ (ss : List srt) (P : List (dyn DA) → Prop),
    (∀ θ, sorted DA θ ss → P θ) → forall_sorts DA ss P
  | [], P, h => h [] rfl
  | s :: ss, P, h => fun x =>
      forall_sorts_intro ss (fun θ => P (⟨s, x⟩ :: θ)) (fun θ hθ => h _ (by simp [sorted] at hθ ⊢; exact hθ))

/-! ## The postcondition -/

theorem checkPost_sound (rules : List trule) (facts : List tfact) (Hf : Forall (fact_valid DA) facts)
    (Hp : preds_valid DA) (sp : tspec) (st : lstate) (t : tterm) (θs θx : List (dyn DA)) :
    checkPost (mkCtx syms preds rules facts) sp st t = true → sorted DA θs sp.sp_vars →
    st_den DA (θs ++ θx) st ⊢ iprop(∃ θe : List (dyn DA), ⌜sorted DA θe sp.sp_ex⌝ ∗
      ⌜val_den DA (θs ++ θx) t = val_den DA (θs ++ θe) sp.sp_ret⌝ ∗ assn_den DA (θs ++ θe) sp.sp_post) := by
  intro H hs
  simp only [checkPost] at H
  split at H; · cases H
  rename_i b1 hm1
  split at H; · cases H
  rename_i b2 h' hm2
  split at H
  · rename_i bs hbs
    have hnv : θs.length = sp.sp_vars.length := sorted_length DA θs _ hs
    -- the specification's own variables, bound to themselves
    let b0 : Bind := (List.range sp.sp_vars.length).map (fun i => some (TVar i)) ++
      List.replicate sp.sp_ex.length none
    have hb0i : ∀ i, i < sp.sp_vars.length → b0[i]? = some (some (TVar i)) := by
      intro i hi
      simp only [b0]
      rw [List.getElem?_append_left (by simpa using hi)]
      simp [hi]
    have hl0 : b0.length = (sp.sp_vars ++ sp.sp_ex).length := by simp [b0]
    unfold st_den
    iintro ⟨%Hθ, %Hpure, Hheap⟩
    have hvars : ∀ i, i < sp.sp_vars.length → st.vars[i]? = sp.sp_vars[i]? := by
      intro i hi
      rw [← Hθ, ← hs, List.getElem?_map, List.getElem?_map, List.getElem?_append_left (by omega)]
    have Hbwf0 : bwf syms st.vars (sp.sp_vars ++ sp.sp_ex) b0 := by
      intro i u hi
      by_cases hlt : i < sp.sp_vars.length
      · rw [hb0i i hlt] at hi
        cases hi
        refine ⟨sp.sp_vars[i], by rw [List.getElem?_append_left hlt]; simp [hlt], ?_⟩
        simp only [sortOf, hvars i hlt, List.getElem?_eq_getElem hlt]
      · simp only [b0] at hi
        rw [List.getElem?_append_right (by simp; omega)] at hi
        simp [List.getElem?_replicate] at hi
    obtain ⟨A1, B1, C1⟩ := mterm_sound syms st.vars _ sp.sp_ret t b0 b1 hm1
    obtain ⟨A2, B2, _⟩ := matchPreds_sound DA rules facts Hp st.vars (sp.sp_vars ++ sp.sp_ex)
      (θs ++ θx) (θs ++ θx) sp.sp_post st.heap b1 b2 h' hm2
    have hl2 : b2.length = (sp.sp_vars ++ sp.sp_ex).length := by
      rw [matchPreds_length _ _ _ _ _ _ _ _ hm2, mterm_length _ _ _ _ _ _ _ hm1, hl0]
    obtain ⟨hag, hlbs, _⟩ := allBound_sound b2 bs hbs
    obtain ⟨θb, hev, hsb⟩ := evs_of_bound DA (θs ++ θx) st.vars _ Hθ b2 bs hl2 (B2 (B1 Hbwf0)) hbs
    -- θb starts with θs
    have hθb : θb = θs ++ θb.drop θs.length := by
      have htake : θb.take θs.length = θs := by
        apply List.ext_getElem?
        intro i
        by_cases hi : i < θs.length
        · rw [List.getElem?_take, ite_eq_left_of_eq_true _ _ (eq_true hi)]
          have hbi : bs[i]? = some (TVar i) :=
            hag i (TVar i) (bext_trans A1 A2 i (TVar i) (hb0i i (by omega)))
          obtain ⟨d, hd, htd⟩ := forall2_lookup i (TVar i) hev hbi
          simp only [teval, nth_error_eq, List.getElem?_append_left hi] at htd
          rw [hd, htd]
        · rw [List.getElem?_take]; simp only [hi, ↓reduceIte]; rw [List.getElem?_eq_none (by omega)]
      conv => lhs; rw [← List.take_append_drop θs.length θb]
      rw [htake]
    have hse : sorted DA (θb.drop θs.length) sp.sp_ex := by
      have := congrArg (List.drop θs.length) hsb
      simp only [sorted, List.map_drop] at this ⊢
      rw [this, hnv, List.drop_left]
    have Hret : val_den DA (θs ++ θx) t = val_den DA θb sp.sp_ret := by
      simp only [val_den, inst_teval DA _ θb bs hev sp.sp_ret t (C1 bs (agrees_of_bext A2 hag))]
    have Heqs := eqsHold_sound DA rules facts Hf st (θs ++ θx) θb Hθ Hpure bs hev sp.sp_post H
    icases (matchPreds_sound DA rules facts Hp st.vars (sp.sp_vars ++ sp.sp_ex) (θs ++ θx) θb
      sp.sp_post st.heap b1 b2 h' hm2).2.2 bs hag hev Heqs $$ Hheap with ⟨Hpost, -⟩
    iexists θb.drop θs.length
    rw [← hθb]
    isplitr
    · ipureintro; exact hse
    isplitr
    · ipureintro; exact Hret
    iapply (assn_den_eq DA θb sp.sp_post).2 $$ Hpost
  · cases H

/-! ## The whole run -/

theorem mem_bindParams : ∀ (xs : List String) (ts : List tterm) (en : env) (xt : String × tterm),
    xt ∈ bindParams xs ts en → xt ∈ en ∨ xt.2 ∈ ts
  | x :: xs, t :: ts, en, xt, h => by
      simp only [bindParams] at h
      rcases mem_bindParams xs ts _ xt h with h | h
      · rcases List.mem_cons.mp h with rfl | h
        · exact .inr List.mem_cons_self
        · exact .inl h
      · exact .inr (List.mem_cons_of_mem _ h)
  | [], _, _, _, h => .inl h
  | _ :: _, [], _, _, h => .inl h

theorem valsOf_isval (θ : List (dyn DA)) (vars : List srt) (Hθ : sorted DA θ vars) :
    ∀ ts : List tterm, valsOf syms vars ts = true → ∀ t, t ∈ ts → isval DA θ t
  | [], _, _, h => by cases h
  | u :: ts, h, t, ht => by
      simp only [valsOf, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases List.mem_cons.mp ht with rfl | ht
      · exact isval_of_sort DA θ vars Hθ _ h.1
      · exact valsOf_isval θ vars Hθ ts h.2 t ht

theorem map_val_den (θ : List (dyn DA)) : ∀ (l l' : List tterm),
    tevals DA θ l = tevals DA θ l' → l.map (val_den DA θ) = l'.map (val_den DA θ)
  | [], [], _ => rfl
  | a :: l, b :: l', h => by
      simp only [tevals, List.cons.injEq] at h
      simp only [List.map_cons, val_den, h.1, map_val_den θ l l' h.2]
  | [], _ :: _, h | _ :: _, [], h => by simp [tevals] at h

theorem apply_vals_not_val (f : val) (a : val) (rest : List val) :
    toVal (apply_vals f (a :: rest)) = none := by
  simp only [apply_vals, List.foldl_cons]
  rw [apply_vals_fill']
  exact EctxItemLanguage.fill_not_val (K := rest.map EctxItem.AppLCtx) (e := App (Val f) (Val a)) rfl

/-- The function meets its specification, in every denotation in which the
table is valid. -/
theorem spec_sound (i : tinput) (DA : DenAt GF i.in_syms i.in_preds) :
    ltcheck i = true → table_valid DA i.in_rules i.in_facts → spec_valid DA i.in_func i.in_spec := by
  intro H ⟨Hr, Hf, Hp⟩
  simp only [ltcheck] at H
  split at H
  case isFalse => cases H
  rename_i hpar
  split at H; · cases H
  rename_i h0 p0 hadd
  split at H; · cases H
  rename_i nargs hargs
  split at H
  case isFalse => cases H
  rename_i hvals
  split at H
  case h_2 => cases H
  rename_i t st heval
  -- names
  have Hrules := Hr; have Hfacts := Hf
  unfold spec_valid
  apply forall_sorts_intro
  intro θs hθs
  unfold triple_at
  iintro %Φ Hpre HΦ
  -- the initial state
  have hids : evs DA θs ((List.range i.in_spec.sp_vars.length).map TVar) θs := by
    have := evs_fresh DA [] θs
    simp only [List.nil_append, List.length_nil, Nat.zero_add] at this
    rwa [sorted_length DA θs _ hθs] at this
  ihave Hst0 := addAtoms_sound DA i.in_rules i.in_facts Hf i.in_spec.sp_vars θs θs hθs _ hids
    i.in_spec.sp_pre [] [] h0 p0 hadd $$ [Hpre]
  · isplitr
    · unfold heap_den; iapply BigSepL.bigSepL_nil_intro; iempintro
    isplitr
    · ipureintro; intro q hq; cases hq
    · iapply (assn_den_eq DA θs i.in_spec.sp_pre).1 $$ Hpre
  icases Hst0 with ⟨Hh0, %Hp0⟩
  -- the arguments
  have Hargs : i.in_spec.sp_args.map (val_den DA θs) = nargs.map (val_den DA θs) :=
    (map_val_den DA θs _ _ (mapOpt_norm_tevals DA i.in_facts Hf θs _ hθs i.in_rules _ _ hargs)).symm
  have hlen : nargs.length = i.in_func.fn_params.length := by
    rw [mapOpt_length _ _ _ hargs, hpar.2]
  have Hen : env_good DA θs (bindParams i.in_func.fn_params nargs []) := by
    intro xt hxt
    rcases mem_bindParams _ _ _ xt hxt with h | h
    · cases h
    · exact valsOf_isval DA θs _ hθs nargs hvals _ h
  rw [Hargs]
  obtain ⟨x, xs, hx⟩ : ∃ x xs, nargs.map (val_den DA θs) = x :: xs := by
    cases hn : nargs with
    | nil => rw [hn] at hlen; exact absurd (List.length_eq_zero_iff.mp hlen.symm) hpar.1
    | cons a l => exact ⟨_, _, rfl⟩
  -- run, keeping the postcondition's continuation for after the first step
  let Post : val → IProp GF := fun v => iprop(∃ θx : List (dyn DA),
    st_den DA (θs ++ θx) st ∗ ⌜v = val_den DA (θs ++ θx) t⌝)
  iapply wp_wand_r (Φ := fun v => iprop(bi_forall_sorts DA i.in_spec.sp_ex (fun θx =>
      iprop(assn_den DA (vapp θs θx) i.in_spec.sp_post -∗ Φ (val_den DA (vapp θs θx) i.in_spec.sp_ret)))
    ∗ Post v))
  isplitl
  · rw [hx]
    iapply wp_frame_step_l' (apply_vals_not_val _ x xs) Iris.Std.LawfulSet.subset_refl
    iframe HΦ
    rw [← hx]
    iapply wp_func_val DA i.in_func _ Post (by simpa using hlen) hpar.1
    rw [show Checker.binds i.in_func.fn_params (nargs.map (val_den DA θs)) ∅ =
      env_den DA θs (bindParams i.in_func.fn_params nargs []) by
        rw [env_den_bindParams]; rfl]
    rw [show csubst DA (env_den DA θs (bindParams i.in_func.fn_params nargs [])) i.in_func.fn_body =
      fill [] (csubst DA (env_den DA θs (bindParams i.in_func.fn_params nargs [])) i.in_func.fn_body)
      from rfl]
    iapply eval_sound DA i.in_rules i.in_facts Hf Hp Hr _ false _ _ _ _ heval θs [] Post Hen
    isplitl [Hh0]
    · unfold st_den; iframe Hh0; ipureintro; exact ⟨hθs, Hp0⟩
    iintro %θx Hst %-
    rw [show fill [] (eres_den DA (θs ++ θx) (eR (rVal t))) = Val (val_den DA (θs ++ θx) t) from rfl]
    iapply wp_value'
    iexists θx
    iframe Hst
    ipureintro; rfl
  iintro %v ⟨HΦ, Hpost⟩
  icases Hpost with ⟨%θx, Hst, %Hv⟩
  icases checkPost_sound DA i.in_rules i.in_facts Hf Hp i.in_spec st t θs θx H hθs $$ Hst with
    ⟨%θe, %hse, %Hret, Hassn⟩
  ihave Hk := bi_forall_elim DA i.in_spec.sp_ex _ θe hse $$ HΦ
  rw [vapp_eq] at *
  rw [Hv, Hret]
  iapply Hk $$ Hassn

end den

/-- Soundness of the Lean table checker. -/
theorem ltcheck_sound (i : tinput) : ltcheck i = true → input_holds i := by
  intro H ext ffi _ _ _ hlc GF hG _ DA Ht
  exact spec_sound i DA H Ht

end LC
end TCheck
end Perennial
