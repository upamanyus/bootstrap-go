/-
Soundness of the Lean table checker, part 5: evaluation.

`eval_sound`: if `eval` takes the code `e`, in environment `en` and state
`st`, to the result `er` and state `st'`, then the WP of `e` (with the
environment substituted) in any evaluation context `K` follows from the
state's denotation and a continuation `kont` that, for some extension of the
valuation, receives the new state and the result's denotation. In shallow
mode the result is the application spine the expression evaluates to; it is
handed to `reduce` (`reduce_sound`, Rules.lean) by the enclosing application.
-/
import Checkers.TCheck.Reflect.Rules

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace TCheck
namespace LC

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open GMap (delete)

section den
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {syms : List symdecl} {preds : List preddecl} (DA : DenAt GF syms preds)

/-! ## Results -/

def res_den (θ : List (dyn DA)) : lres → val
  | rVal t => val_den DA θ t
  | rExec => Checker.exec_v
  | rRet t => Checker.ret_v (val_den DA θ t)

def res_good (θ : List (dyn DA)) : lres → Prop
  | rVal t => isval DA θ t
  | rExec => True
  | rRet t => isval DA θ t

def eres_den (θ : List (dyn DA)) : eres → Expr
  | eR r => Val (res_den DA θ r)
  | eS p => pat_den DA θ p

def eres_good (θ : List (dyn DA)) : eres → Prop
  | eR r => res_good DA θ r
  | eS p => pat_good DA θ p

def env_good (θ : List (dyn DA)) (en : env) : Prop := ∀ xt, xt ∈ en → isval DA θ xt.2

theorem res_ext (θ θx : List (dyn DA)) : ∀ r, res_good DA θ r →
    res_good DA (θ ++ θx) r ∧ res_den DA (θ ++ θx) r = res_den DA θ r
  | rVal t, h => ⟨isval_ext DA θ θx t h, by simp only [res_den, val_den_ext DA θ θx t h]⟩
  | rExec, _ => ⟨trivial, rfl⟩
  | rRet t, h => ⟨isval_ext DA θ θx t h, by simp only [res_den, val_den_ext DA θ θx t h]⟩

theorem env_ext (θ θx : List (dyn DA)) (en : env) : env_good DA θ en →
    env_good DA (θ ++ θx) en ∧ env_den DA (θ ++ θx) en = env_den DA θ en := by
  intro h
  refine ⟨fun xt hxt => isval_ext DA θ θx _ (h xt hxt), ?_⟩
  induction en with
  | nil => rfl
  | cons xt en ih =>
    obtain ⟨x, t⟩ := xt
    rw [env_den_cons, env_den_cons, val_den_ext DA θ θx t (h _ List.mem_cons_self),
      ih (fun yt hyt => h yt (List.mem_cons_of_mem _ hyt))]

theorem env_good_cons (θ : List (dyn DA)) (x : String) (t : tterm) (en : env) :
    isval DA θ t → env_good DA θ en → env_good DA θ ((x, t) :: en) := by
  intro ht h yt hyt
  rcases List.mem_cons.mp hyt with rfl | hyt
  · exact ht
  · exact h yt hyt

theorem lookup_mem : ∀ (en : env) (x : String) (t : tterm), lookup en x = some t → (x, t) ∈ en
  | [], _, _, h => by simp [lookup] at h
  | (y, u) :: en, x, t, h => by
      simp only [lookup, beq_iff_eq] at h
      split at h
      · rename_i hy; cases h; subst hy; exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (lookup_mem en x t h)

/-! ## Continuations -/

/-- What a step of evaluation promises: for some extension `θx` of the
valuation, the new state and the result. -/
abbrev kont (θ : List (dyn DA)) (st' : lstate) (er : eres) (K : List EctxItem) (Ψ : val → IProp GF) :
    IProp GF :=
  iprop(∀ θx, st_den DA (θ ++ θx) st' -∗ ⌜eres_good DA (θ ++ θx) er⌝ -∗
    WP (fill K (eres_den DA (θ ++ θx) er)) {{ Ψ }})

theorem fin_eq (sh : Bool) (r : lres) (st : lstate) (er : eres) (st' : lstate) :
    fin sh r st = some (er, st') → st' = st ∧
      ∀ θ : List (dyn DA), eres_den DA θ er = Val (res_den DA θ r) ∧
        (res_good DA θ r → eres_good DA θ er) := by
  intro h
  cases sh
  · simp only [fin, Bool.false_eq_true, ↓reduceIte, Option.some.injEq, Prod.mk.injEq] at h
    obtain ⟨rfl, rfl⟩ := h
    exact ⟨rfl, fun _ => ⟨rfl, id⟩⟩
  · simp only [fin, ↓reduceIte] at h
    split at h
    · rename_i t
      simp only [Option.some.injEq, Prod.mk.injEq] at h
      obtain ⟨rfl, rfl⟩ := h
      exact ⟨rfl, fun _ => ⟨rfl, id⟩⟩
    · cases h

/-- Finishing a case at the extended valuation `θ ++ θx1`. -/
theorem fin_kont (sh : Bool) (r : lres) (st0 : lstate) (er : eres) (st' : lstate)
    (θ θx1 : List (dyn DA)) (K : List EctxItem) (Ψ : val → IProp GF) :
    fin sh r st0 = some (er, st') → res_good DA (θ ++ θx1) r →
    iprop(st_den DA (θ ++ θx1) st0 ∗ kont DA θ st' er K Ψ) ⊢
      WP (fill K (Val (res_den DA (θ ++ θx1) r))) {{ Ψ }} := by
  intro hf hr
  obtain ⟨rfl, E⟩ := fin_eq DA sh r st0 er st' hf
  obtain ⟨E1, E2⟩ := E (θ ++ θx1)
  unfold kont
  iintro ⟨Hst, Hk⟩
  rw [← E1]
  iapply Hk $$ %θx1 Hst
  ipureintro; exact E2 hr

/-- A subexpression's result, passed on to the case's own finish. -/
theorem fin_cont (sh : Bool) (r : lres) (st2 : lstate) (er : eres) (st' : lstate)
    (θ θx1 : List (dyn DA)) (K : List EctxItem) (Ψ : val → IProp GF) :
    fin sh r st2 = some (er, st') →
    kont DA θ st' er K Ψ ⊢ kont DA (θ ++ θx1) st2 (eR r) K Ψ := by
  intro hf
  iintro Hk
  unfold kont
  iintro %θx2 Hst %Hr
  simp only [eres_good] at Hr
  rw [show eres_den DA (θ ++ θx1 ++ θx2) (eR r) = Val (res_den DA (θ ++ θx1 ++ θx2) r) from rfl,
    List.append_assoc]
  rw [List.append_assoc] at Hr
  iapply fin_kont DA sh r st2 er st' θ (θx1 ++ θx2) K Ψ hf Hr
  isplitl [Hst]
  · iexact Hst
  · unfold kont; iexact Hk

/-- The value of a closed term of sort `val`. -/
theorem closed_val (θ : List (dyn DA)) (t : tterm) :
    sortOf syms [] t = some SVal → ∃ v, teval DA [] t = some ⟨SVal, v⟩ ∧ teval DA θ t = some ⟨SVal, v⟩ := by
  intro h
  obtain ⟨v, hv⟩ := sortOf_sound DA [] [] rfl t SVal h
  exact ⟨v, hv, by simpa using teval_ext DA [] θ t _ hv⟩

theorem st_den_sorted (θ : List (dyn DA)) (st : lstate) :
    st_den DA θ st ⊢ iprop(⌜sorted DA θ st.vars⌝ ∗ st_den DA θ st) := by
  unfold st_den
  iintro ⟨%H1, %H2, H3⟩
  iframe H3
  ipureintro; exact ⟨H1, H1, H2⟩

/-! ## Literals -/

theorem litElems_sound (c : ctx) (θ : List (dyn DA)) (en : env) (Hen : env_good DA θ en)
    (Hc : c.syms = syms) (T : go.GoType) :
    ∀ (es : List cexpr) (ts : List tterm), litElems c en es = some ts →
      ∃ vs, csubst_lit DA (env_den DA θ en) T es =
          vs.map (fun v => KeyedElement none (ElementExpression T (Val v))) ∧
        vals_of DA (tevals DA θ ts) = some vs
  | [], ts, h => by simp only [litElems, Option.some.injEq] at h; subst h; exact ⟨[], rfl, rfl⟩
  | CVal t :: es, ts, h => by
      simp only [litElems] at h
      split at h
      · rename_i hs
        split at h
        · rename_i ts' hts
          cases h
          rw [Hc] at hs
          obtain ⟨v, h0, hv⟩ := closed_val DA θ t hs
          obtain ⟨vs, E1, E2⟩ := litElems_sound c θ en Hen Hc T es ts' hts
          refine ⟨v :: vs, ?_, ?_⟩
          · simp only [csubst_lit, csubst, E1, val_den_of DA [] t v h0]; rfl
          · simp only [tevals, vals_of, hv, as_val, E2]; rfl
        · cases h
      · cases h
  | CVar x :: es, ts, h => by
      simp only [litElems] at h
      split at h
      · rename_i t ts' hl hts
        cases h
        obtain ⟨v, hv⟩ := Hen _ (lookup_mem en x t hl)
        obtain ⟨vs, E1, E2⟩ := litElems_sound c θ en Hen Hc T es ts' hts
        refine ⟨v :: vs, ?_, ?_⟩
        · simp only [csubst_lit, csubst, env_den_lookup, hl, Option.map_some, E1,
            val_den_of DA θ t v hv]; rfl
        · simp only [tevals, vals_of, hv, as_val, E2]; rfl
      · cases h
  | CApp _ _ :: _, _, h | CPair _ _ :: _, _, h | CLet _ _ _ :: _, _, h | CSeq _ _ :: _, _, h
  | CLit _ _ :: _, _, h | CDo _ :: _, _, h | CRet _ :: _, _, h | CXSeq _ _ :: _, _, h
  | CXDo _ :: _, _, h => by simp [litElems] at h


theorem teval_pair (θ : List (dyn DA)) (ta tb : tterm) (xa xb : val) :
    teval DA θ ta = some ⟨SVal, xa⟩ → teval DA θ tb = some ⟨SVal, xb⟩ →
    teval DA θ (TPair ta tb) = some ⟨SVal, PairV xa xb⟩ := by
  intro ha hb; simp only [teval, ha, hb, as_val]; rfl

theorem isval_val (θ : List (dyn DA)) (t : tterm) :
    isval DA θ t → teval DA θ t = some ⟨SVal, val_den DA θ t⟩ := by
  intro ⟨v, hv⟩; rw [val_den_of DA θ t v hv]; exact hv

section eval
variable (rules : List trule) (facts : List tfact) (Hf : Forall (fact_valid DA) facts)
variable (Hp : preds_valid DA) (Hr : Forall (rule_valid DA) rules)

include Hf Hp Hr in
theorem eval_sound :
    ∀ (e : cexpr) (sh : Bool) (en : env) (st : lstate) (er : eres) (st' : lstate),
    eval (mkCtx syms preds rules facts) sh en e st = some (er, st') →
    ∀ (θ : List (dyn DA)) (K : List EctxItem) (Ψ : val → IProp GF), env_good DA θ en →
      iprop(st_den DA θ st ∗ kont DA θ st' er K Ψ) ⊢
        WP (fill K (csubst DA (env_den DA θ en) e)) {{ Ψ }}
  | CVal t, sh, en, st, er, st', H, θ, K, Ψ, Hen => by
      simp only [eval] at H
      split at H
      · rename_i hs
        split at H
        · rename_i t' ht'
          obtain ⟨v, h0, hv⟩ := closed_val DA θ t hs
          simp only [csubst, val_den_of DA [] t v h0]
          iintro ⟨Hst, Hk⟩
          icases st_den_sorted DA θ st $$ Hst with ⟨%Hθ, Hst⟩
          have E : teval DA θ t' = some ⟨SVal, v⟩ := by
            rw [norm_teval DA θ st.vars Hθ facts Hf _ t t' ht']; exact hv
          have := fin_kont DA sh (rVal t') st er st' θ [] K Ψ H (by simp only [List.append_nil]; exact ⟨v, E⟩)
          simp only [res_den, List.append_nil, val_den_of DA θ t' v E] at this
          iapply this
          iframe Hst Hk
        · cases H
      · cases H
  | CVar x, sh, en, st, er, st', H, θ, K, Ψ, Hen => by
      simp only [eval] at H
      split at H
      · rename_i t hl
        obtain ⟨v, hv⟩ := Hen _ (lookup_mem en x t hl)
        simp only [csubst, env_den_lookup, hl, Option.map_some, val_den_of DA θ t v hv]
        have := fin_kont DA sh (rVal t) st er st' θ [] K Ψ H (by simp only [List.append_nil]; exact ⟨v, hv⟩)
        simp only [res_den, List.append_nil, val_den_of DA θ t v hv] at this
        exact this
      · cases H
  | CApp a b, sh, en, st, er, st', H, θ, K, Ψ, Hen => by
      simp only [eval] at H
      split at H
      · rename_i arg st1 Hb
        split at H
        · rename_i sp st2 Ha
          simp only [csubst]
          rw [show fill K (App (csubst DA (env_den DA θ en) a) (csubst DA (env_den DA θ en) b)) =
            fill (EctxItem.AppRCtx (csubst DA (env_den DA θ en) a) :: K) (csubst DA (env_den DA θ en) b)
            from rfl]
          iintro ⟨Hst, Hk⟩
          iapply eval_sound b false en st (eR (rVal arg)) st1 Hb θ _ Ψ Hen
          iframe Hst
          iintro %θx1 Hst1 %Harg
          simp only [eres_good, res_good] at Harg
          obtain ⟨Hen1, E1⟩ := env_ext DA θ θx1 en Hen
          rw [show fill (EctxItem.AppRCtx (csubst DA (env_den DA θ en) a) :: K)
              (eres_den DA (θ ++ θx1) (eR (rVal arg))) =
            fill (EctxItem.AppLCtx (val_den DA (θ ++ θx1) arg) :: K) (csubst DA (env_den DA θ en) a)
            from rfl, ← E1]
          iapply eval_sound a true en st1 (eS sp) st2 Ha (θ ++ θx1) _ Ψ Hen1
          iframe Hst1
          iintro %θx2 Hst2 %Hsp
          simp only [eres_good] at Hsp
          have Hv := val_den_ext DA (θ ++ θx1) θx2 arg Harg
          have Hg : pat_good DA (θ ++ θx1 ++ θx2) (PApp sp (PVal arg)) :=
            ⟨Hsp, isval_ext DA (θ ++ θx1) θx2 arg Harg⟩
          rw [show fill (EctxItem.AppLCtx (val_den DA (θ ++ θx1) arg) :: K)
              (eres_den DA (θ ++ θx1 ++ θx2) (eS sp)) =
            fill K (pat_den DA (θ ++ θx1 ++ θx2) (PApp sp (PVal arg))) by
              simp only [eres_den, pat_den, Hv]; rfl]
          split at H
          · simp only [Option.some.injEq, Prod.mk.injEq] at H
            obtain ⟨rfl, rfl⟩ := H
            rw [List.append_assoc, show pat_den DA (θ ++ (θx1 ++ θx2)) (PApp sp (PVal arg)) =
              eres_den DA (θ ++ (θx1 ++ θx2)) (eS (PApp sp (PVal arg))) from rfl]
            rw [List.append_assoc] at Hg
            iapply Hk $$ %(θx1 ++ θx2) Hst2
            ipureintro; exact Hg
          · split at H
            · rename_i t st3 hred
              simp only [Option.some.injEq, Prod.mk.injEq] at H
              obtain ⟨rfl, rfl⟩ := H
              iapply reduce_sound DA rules facts Hf Hp Hr _ st2 _ t st3 hred _ K Ψ Hg
              iframe Hst2
              iintro %θx3 Hst3 %Ht
              rw [List.append_assoc, List.append_assoc,
                show (Val (val_den DA (θ ++ (θx1 ++ (θx2 ++ θx3))) t) : Expr) =
                  eres_den DA (θ ++ (θx1 ++ (θx2 ++ θx3))) (eR (rVal t)) from rfl]
              rw [List.append_assoc, List.append_assoc] at Ht
              iapply Hk $$ %(θx1 ++ (θx2 ++ θx3)) Hst3
              ipureintro; exact Ht
            · cases H
        · cases H
      · cases H
  | CPair a b, sh, en, st, er, st', H, θ, K, Ψ, Hen => by
      simp only [eval] at H
      split at H
      · rename_i ta st1 Ha
        split at H
        · rename_i tb st2 Hb
          split at H
          · rename_i t ht
            simp only [csubst]
            rw [show fill K (Pair (csubst DA (env_den DA θ en) a) (csubst DA (env_den DA θ en) b)) =
              fill (EctxItem.PairLCtx (csubst DA (env_den DA θ en) b) :: K) (csubst DA (env_den DA θ en) a)
              from rfl]
            iintro ⟨Hst, Hk⟩
            iapply eval_sound a false en st (eR (rVal ta)) st1 Ha θ _ Ψ Hen
            iframe Hst
            iintro %θx1 Hst1 %Hta
            simp only [eres_good, res_good] at Hta
            obtain ⟨Hen1, E1⟩ := env_ext DA θ θx1 en Hen
            rw [show fill (EctxItem.PairLCtx (csubst DA (env_den DA θ en) b) :: K)
                (eres_den DA (θ ++ θx1) (eR (rVal ta))) =
              fill (EctxItem.PairRCtx (val_den DA (θ ++ θx1) ta) :: K) (csubst DA (env_den DA θ en) b)
              from rfl, ← E1]
            iapply eval_sound b false en st1 (eR (rVal tb)) st2 Hb (θ ++ θx1) _ Ψ Hen1
            iframe Hst1
            iintro %θx2 Hst2 %Htb
            simp only [eres_good, res_good] at Htb
            rw [show fill (EctxItem.PairRCtx (val_den DA (θ ++ θx1) ta) :: K)
                (eres_den DA (θ ++ θx1 ++ θx2) (eR (rVal tb))) =
              fill K (Pair (Val (val_den DA (θ ++ θx1) ta)) (Val (val_den DA (θ ++ θx1 ++ θx2) tb)))
              from rfl]
            icases st_den_sorted DA _ st2 $$ Hst2 with ⟨%Hθ2, Hst2⟩
            have Ea := isval_val DA _ ta (isval_ext DA (θ ++ θx1) θx2 ta Hta)
            rw [val_den_ext DA (θ ++ θx1) θx2 ta Hta] at Ea
            have Et : teval DA (θ ++ θx1 ++ θx2) t = some ⟨SVal,
                PairV (val_den DA (θ ++ θx1) ta) (val_den DA (θ ++ θx1 ++ θx2) tb)⟩ := by
              rw [norm_teval DA _ st2.vars Hθ2 facts Hf _ _ t ht]
              exact teval_pair DA _ ta tb _ _ Ea (isval_val DA _ tb Htb)
            iapply wp_ctx_val K (Pair (Val (val_den DA (θ ++ θx1) ta)) (Val (val_den DA (θ ++ θx1 ++ θx2) tb)))
              (PairV (val_den DA (θ ++ θx1) ta) (val_den DA (θ ++ θx1 ++ θx2) tb)) Ψ
              (fun Φ => by iintro H; wp_pures; iexact H)
            have := fin_kont DA sh (rVal t) st2 er st' θ (θx1 ++ θx2) K Ψ H
              (by rw [← List.append_assoc]; exact ⟨_, Et⟩)
            simp only [res_den, ← List.append_assoc, val_den_of DA _ t _ Et] at this
            iapply this
            iframe Hst2 Hk
          · cases H
        · cases H
      · cases H
  | CLet x a b, sh, en, st, er, st', H, θ, K, Ψ, Hen => by
      simp only [eval] at H
      split at H
      · rename_i v st1 Ha
        split at H
        · rename_i r st2 Hb
          simp only [csubst]
          rw [show fill K (App (Rec BAnon (BNamed x) (csubst DA (delete x (env_den DA θ en)) b))
              (csubst DA (env_den DA θ en) a)) =
            fill (EctxItem.AppRCtx (Rec BAnon (BNamed x) (csubst DA (delete x (env_den DA θ en)) b)) :: K)
              (csubst DA (env_den DA θ en) a) from rfl]
          iintro ⟨Hst, Hk⟩
          iapply eval_sound a false en st (eR (rVal v)) st1 Ha θ _ Ψ Hen
          iframe Hst
          iintro %θx1 Hst1 %Hv
          simp only [eres_good, res_good] at Hv
          obtain ⟨Hen1, E1⟩ := env_ext DA θ θx1 en Hen
          rw [show fill (EctxItem.AppRCtx (Rec BAnon (BNamed x) (csubst DA (delete x (env_den DA θ en)) b)) :: K)
              (eres_den DA (θ ++ θx1) (eR (rVal v))) =
            fill K (App (Rec BAnon (BNamed x) (csubst DA (delete x (env_den DA θ en)) b))
              (Val (val_den DA (θ ++ θx1) v))) from rfl]
          iapply wp_ctx_expr K _ _ Ψ (fun Φ => Checker.wp_beta_rec_expr _ _ _ Φ)
          rw [csubst_insert, ← E1, ← env_den_cons]
          iapply eval_sound b false ((x, v) :: en) st1 (eR r) st2 Hb (θ ++ θx1) K Ψ
            (env_good_cons DA _ x v en Hv Hen1)
          iframe Hst1
          iapply fin_cont DA sh r st2 er st' θ θx1 K Ψ H $$ Hk
        · cases H
      · cases H
  | CSeq a b, sh, en, st, er, st', H, θ, K, Ψ, Hen => by
      simp only [eval] at H
      split at H
      · rename_i v st1 Ha
        split at H
        · rename_i r st2 Hb
          simp only [csubst]
          rw [show fill K (App (Rec BAnon BAnon (csubst DA (env_den DA θ en) b))
              (csubst DA (env_den DA θ en) a)) =
            fill (EctxItem.AppRCtx (Rec BAnon BAnon (csubst DA (env_den DA θ en) b)) :: K)
              (csubst DA (env_den DA θ en) a) from rfl]
          iintro ⟨Hst, Hk⟩
          iapply eval_sound a false en st (eR (rVal v)) st1 Ha θ _ Ψ Hen
          iframe Hst
          iintro %θx1 Hst1 %Hv
          obtain ⟨Hen1, E1⟩ := env_ext DA θ θx1 en Hen
          rw [show fill (EctxItem.AppRCtx (Rec BAnon BAnon (csubst DA (env_den DA θ en) b)) :: K)
              (eres_den DA (θ ++ θx1) (eR (rVal v))) =
            fill K (App (Rec BAnon BAnon (csubst DA (env_den DA θ en) b))
              (Val (val_den DA (θ ++ θx1) v))) from rfl]
          iapply wp_ctx_expr K _ _ Ψ (fun Φ => Checker.wp_beta_anon_expr _ _ Φ)
          rw [← E1]
          iapply eval_sound b false en st1 (eR r) st2 Hb (θ ++ θx1) K Ψ Hen1
          iframe Hst1
          iapply fin_cont DA sh r st2 er st' θ θx1 K Ψ H $$ Hk
        · cases H
      · cases H
  | CLit ty es, sh, en, st, er, st', H, θ, K, Ψ, Hen => by
      simp only [eval] at H
      split at H
      · rename_i hty
        split at H
        · rename_i ts hts
          split at H
          · rename_i t ht
            obtain ⟨T, hT⟩ := sortOf_sound DA [] [] rfl ty SType hty
            have hTd : type_den DA ty = T := by simp only [type_den, hT]; rfl
            obtain ⟨vs, E1, E2⟩ := litElems_sound DA _ θ en Hen rfl (type_den DA ty) es ts hts
            simp only [csubst]
            rw [E1, hTd]
            iintro ⟨Hst, Hk⟩
            icases st_den_sorted DA θ st $$ Hst with ⟨%Hθ, Hst⟩
            have Et : teval DA θ t = some ⟨SVal, LiteralValueV
                (vs.map fun v => KeyedElement none (ElementExpression T (Val v)))⟩ := by
              rw [norm_teval DA θ st.vars Hθ facts Hf _ _ t ht]
              have hT' : teval DA θ ty = some ⟨SType, T⟩ := by simpa using teval_ext DA [] θ ty _ hT
              simp only [teval, hT', E2]
              rfl
            iapply wp_ctx_val K (LiteralValue (vs.map fun v => KeyedElement none (ElementExpression T (Val v))))
              (LiteralValueV (vs.map fun v => KeyedElement none (ElementExpression T (Val v)))) Ψ
              (fun Φ => by iintro H; wp_pures; iexact H)
            have := fin_kont DA sh (rVal t) st er st' θ [] K Ψ H
              (by simp only [List.append_nil]; exact ⟨_, Et⟩)
            simp only [res_den, List.append_nil, val_den_of DA θ t _ Et] at this
            iapply this
            iframe Hst Hk
          · cases H
        · cases H
      · cases H
  | CDo a, sh, en, st, er, st', H, θ, K, Ψ, Hen => by
      simp only [eval] at H
      split at H
      · rename_i v st1 Ha
        simp only [csubst]
        rw [show fill K (App (Val doExecute) (csubst DA (env_den DA θ en) a)) =
          fill (EctxItem.AppRCtx (Val doExecute) :: K) (csubst DA (env_den DA θ en) a) from rfl]
        iintro ⟨Hst, Hk⟩
        iapply eval_sound a false en st (eR (rVal v)) st1 Ha θ _ Ψ Hen
        iframe Hst
        iintro %θx1 Hst1 %Hv
        rw [show fill (EctxItem.AppRCtx (Val doExecute) :: K) (eres_den DA (θ ++ θx1) (eR (rVal v))) =
          fill K (App (Val doExecute) (Val (val_den DA (θ ++ θx1) v))) from rfl]
        iapply wp_ctx_val K _ _ Ψ (fun Φ => Checker.wp_do _ Φ)
        have := fin_kont DA sh rExec st1 er st' θ θx1 K Ψ H trivial
        simp only [res_den] at this
        iapply this
        iframe Hst1 Hk
      · cases H
  | CRet a, sh, en, st, er, st', H, θ, K, Ψ, Hen => by
      simp only [eval] at H
      split at H
      · rename_i v st1 Ha
        simp only [csubst]
        rw [show fill K (App (Val doReturn) (csubst DA (env_den DA θ en) a)) =
          fill (EctxItem.AppRCtx (Val doReturn) :: K) (csubst DA (env_den DA θ en) a) from rfl]
        iintro ⟨Hst, Hk⟩
        iapply eval_sound a false en st (eR (rVal v)) st1 Ha θ _ Ψ Hen
        iframe Hst
        iintro %θx1 Hst1 %Hv
        simp only [eres_good, res_good] at Hv
        rw [show fill (EctxItem.AppRCtx (Val doReturn) :: K) (eres_den DA (θ ++ θx1) (eR (rVal v))) =
          fill K (App (Val doReturn) (Val (val_den DA (θ ++ θx1) v))) from rfl]
        iapply wp_ctx_val K _ _ Ψ (fun Φ => Checker.wp_return _ Φ)
        have := fin_kont DA sh (rRet v) st1 er st' θ θx1 K Ψ H Hv
        simp only [res_den] at this
        iapply this
        iframe Hst1 Hk
      · cases H
  | CXSeq a b, sh, en, st, er, st', H, θ, K, Ψ, Hen => by
      simp only [eval] at H
      simp only [csubst]
      rw [show fill K (App (App (Val exceptionSeq) (Rec BAnon BAnon (csubst DA (env_den DA θ en) b)))
          (csubst DA (env_den DA θ en) a)) =
        fill (EctxItem.AppRCtx (App (Val exceptionSeq) (Rec BAnon BAnon (csubst DA (env_den DA θ en) b)))
          :: K) (csubst DA (env_den DA θ en) a) from rfl]
      split at H
      · rename_i t st1 Ha
        iintro ⟨Hst, Hk⟩
        iapply eval_sound a false en st (eR (rRet t)) st1 Ha θ _ Ψ Hen
        iframe Hst
        iintro %θx1 Hst1 %Ht
        simp only [eres_good, res_good] at Ht
        rw [show fill (EctxItem.AppRCtx (App (Val exceptionSeq) (Rec BAnon BAnon
              (csubst DA (env_den DA θ en) b))) :: K) (eres_den DA (θ ++ θx1) (eR (rRet t))) =
          fill K (App (App (Val exceptionSeq) (Rec BAnon BAnon (csubst DA (env_den DA θ en) b)))
            (Val (Checker.ret_v (val_den DA (θ ++ θx1) t)))) from rfl]
        iapply wp_ctx_val K _ _ Ψ (fun Φ => Checker.wp_exc_seq_ret _ _ Φ)
        have := fin_kont DA sh (rRet t) st1 er st' θ θx1 K Ψ H Ht
        simp only [res_den] at this
        iapply this
        iframe Hst1 Hk
      · rename_i st1 Ha
        split at H
        · rename_i r st2 Hb
          iintro ⟨Hst, Hk⟩
          iapply eval_sound a false en st (eR rExec) st1 Ha θ _ Ψ Hen
          iframe Hst
          iintro %θx1 Hst1 %-
          obtain ⟨Hen1, E1⟩ := env_ext DA θ θx1 en Hen
          rw [show fill (EctxItem.AppRCtx (App (Val exceptionSeq) (Rec BAnon BAnon
                (csubst DA (env_den DA θ en) b))) :: K) (eres_den DA (θ ++ θx1) (eR rExec)) =
            fill K (App (App (Val exceptionSeq) (Rec BAnon BAnon (csubst DA (env_den DA θ en) b)))
              (Val Checker.exec_v)) from rfl]
          iapply wp_ctx_expr K _ _ Ψ (fun Φ => Checker.wp_exc_seq_exec _ Φ)
          rw [← E1]
          iapply eval_sound b false en st1 (eR r) st2 Hb (θ ++ θx1) K Ψ Hen1
          iframe Hst1
          iapply fin_cont DA sh r st2 er st' θ θx1 K Ψ H $$ Hk
        · cases H
      · cases H
  | CXDo a, sh, en, st, er, st', H, θ, K, Ψ, Hen => by
      simp only [eval] at H
      simp only [csubst]
      rw [show fill K (App (Val exceptionDo) (csubst DA (env_den DA θ en) a)) =
        fill (EctxItem.AppRCtx (Val exceptionDo) :: K) (csubst DA (env_den DA θ en) a) from rfl]
      split at H
      · rename_i st1 Ha
        iintro ⟨Hst, Hk⟩
        iapply eval_sound a false en st (eR rExec) st1 Ha θ _ Ψ Hen
        iframe Hst
        iintro %θx1 Hst1 %-
        rw [show fill (EctxItem.AppRCtx (Val exceptionDo) :: K) (eres_den DA (θ ++ θx1) (eR rExec)) =
          fill K (App (Val exceptionDo) (Val Checker.exec_v)) from rfl]
        iapply wp_ctx_val K _ _ Ψ (fun Φ => Checker.wp_exc_do_exec Φ)
        have Eu : teval DA (θ ++ θx1) TUnit = some ⟨SVal, #()⟩ := rfl
        have := fin_kont DA sh (rVal TUnit) st1 er st' θ θx1 K Ψ H ⟨_, Eu⟩
        simp only [res_den, val_den_of DA _ TUnit _ Eu, Checker.uval_eq] at this
        iapply this
        iframe Hst1 Hk
      · rename_i t st1 Ha
        iintro ⟨Hst, Hk⟩
        iapply eval_sound a false en st (eR (rRet t)) st1 Ha θ _ Ψ Hen
        iframe Hst
        iintro %θx1 Hst1 %Ht
        simp only [eres_good, res_good] at Ht
        rw [show fill (EctxItem.AppRCtx (Val exceptionDo) :: K) (eres_den DA (θ ++ θx1) (eR (rRet t))) =
          fill K (App (Val exceptionDo) (Val (Checker.ret_v (val_den DA (θ ++ θx1) t)))) from rfl]
        iapply wp_ctx_val K _ _ Ψ (fun Φ => Checker.wp_exc_do_ret _ Φ)
        have := fin_kont DA sh (rVal t) st1 er st' θ θx1 K Ψ H Ht
        simp only [res_den] at this
        iapply this
        iframe Hst1 Hk
      · cases H

end eval

end den

end LC
end TCheck
end Perennial
