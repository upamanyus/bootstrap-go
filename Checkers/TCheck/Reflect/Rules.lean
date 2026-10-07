/-
Soundness of the Lean table checker, part 4: rules.

`applyRule_sound`: when `applyRule` rewrites an application of values `p`
to the term `t`, the WP of `p`'s denotation follows from the rule's triple
(`rule_valid`, which the table proves), instantiated at the values the
matching bound: the precondition is taken out of the state, the
postcondition (with the rule's existentials as fresh logical variables) is
put back, and `t` denotes the returned value. `reduce_sound` lifts this to
the checker's search along the function spine of an application.

Results are kept *good* -- they evaluate to values -- so that their
denotation does not change when later steps add variables (`*_ext`).
-/
import Checkers.TCheck.Reflect.Heap

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

/-! ## Good results -/

/-- `t` evaluates to a value. -/
def isval (θ : List (dyn DA)) (t : tterm) : Prop := ∃ v, teval DA θ t = some ⟨SVal, v⟩

theorem val_den_of (θ : List (dyn DA)) (t : tterm) (v : val) :
    teval DA θ t = some ⟨SVal, v⟩ → val_den DA θ t = v := by
  intro h; simp only [val_den, as_val, h]; rfl

theorem isval_ext (θ θx : List (dyn DA)) (t : tterm) : isval DA θ t → isval DA (θ ++ θx) t :=
  fun ⟨v, h⟩ => ⟨v, teval_ext DA θ θx t _ h⟩

theorem val_den_ext (θ θx : List (dyn DA)) (t : tterm) :
    isval DA θ t → val_den DA (θ ++ θx) t = val_den DA θ t := fun ⟨v, h⟩ => by
  rw [val_den_of DA _ t v (teval_ext DA θ θx t _ h), val_den_of DA _ t v h]

theorem isval_of_sort (θ : List (dyn DA)) (vars : List srt) (Hθ : sorted DA θ vars) (t : tterm) :
    sortOf syms vars t = some SVal → isval DA θ t := sortOf_sound DA θ vars Hθ t SVal

/-- Good spines: applications of values to values. -/
def pat_good (θ : List (dyn DA)) : tpat → Prop
  | PVal t => isval DA θ t
  | PApp a (PVal t) => pat_good θ a ∧ isval DA θ t
  | PApp _ (PApp _ _) => False

theorem pat_good_ext (θ θx : List (dyn DA)) : ∀ p, pat_good DA θ p →
    pat_good DA (θ ++ θx) p ∧ pat_den DA (θ ++ θx) p = pat_den DA θ p
  | PVal t, h => ⟨isval_ext DA θ θx t h, by simp only [pat_den, val_den_ext DA θ θx t h]⟩
  | PApp a (PVal t), ⟨ha, ht⟩ => by
      obtain ⟨A, B⟩ := pat_good_ext θ θx a ha
      exact ⟨⟨A, isval_ext DA θ θx t ht⟩, by simp only [pat_den, B, val_den_ext DA θ θx t ht]⟩
  | PApp _ (PApp _ _), h => h.elim

/-! ## Applying one rule -/

theorem vapp_eq {A : Type} : ∀ (l l' : List A), vapp l l' = l ++ l'
  | [], _ => rfl
  | x :: l, l' => by simp [vapp, vapp_eq l l']

theorem bi_forall_intro (ss : List srt) (P : List (dyn DA) → IProp GF) (Q : IProp GF) :
    (∀ θx, sorted DA θx ss → Q ⊢ P θx) → Q ⊢ bi_forall_sorts DA ss P := by
  induction ss generalizing P with
  | nil => intro h; exact h [] rfl
  | cons s ss ih =>
    intro h
    simp only [bi_forall_sorts]
    iintro HQ %x
    iapply ih (fun θ => P (⟨s, x⟩ :: θ)) (fun θx hs => h _ (by simp [sorted] at hs ⊢; exact hs)) $$ HQ

theorem bi_forall_elim (ss : List srt) (P : List (dyn DA) → IProp GF) (θx : List (dyn DA)) :
    sorted DA θx ss → bi_forall_sorts DA ss P ⊢ P θx := by
  induction ss generalizing P θx with
  | nil => intro h; simp [sorted] at h; subst h; exact .rfl
  | cons s ss ih =>
    intro h
    cases θx with
    | nil => simp [sorted] at h
    | cons d θx =>
      obtain ⟨s', x⟩ := d
      simp only [sorted, List.map_cons, List.cons.injEq] at h
      obtain ⟨rfl, h⟩ := h
      simp only [bi_forall_sorts]
      iintro H
      iapply ih (fun θ => P (⟨s', x⟩ :: θ)) θx h
      iapply H

theorem forall2_append {A B : Type} {R : A → B → Prop} {l1 l2 : List A} {m1 m2 : List B} :
    List.Forall₂ R l1 m1 → List.Forall₂ R l2 m2 → List.Forall₂ R (l1 ++ l2) (m1 ++ m2)
  | .nil, h => h
  | .cons h1 h2, h => .cons h1 (forall2_append h2 h)

theorem forall2_mono {A B : Type} {R S : A → B → Prop} (H : ∀ a b, R a b → S a b) :
    ∀ {l : List A} {m : List B}, List.Forall₂ R l m → List.Forall₂ S l m
  | _, _, .nil => .nil
  | _, _, .cons h1 h2 => .cons (H _ _ h1) (forall2_mono H h2)

theorem forall2_of_getElem {A B : Type} {R : A → B → Prop} : ∀ {l1 : List A} {l2 : List B},
    l1.length = l2.length → (∀ (i : Nat) (h1 : i < l1.length) (h2 : i < l2.length), R l1[i] l2[i]) →
    List.Forall₂ R l1 l2
  | [], [], _, _ => .nil
  | a :: l1, b :: l2, hl, h =>
      .cons (h 0 (by simp) (by simp))
        (forall2_of_getElem (by simpa using hl)
          (fun i h1 h2 => h (i + 1) (by simp; omega) (by simp; omega)))
  | [], _ :: _, hl, _ | _ :: _, [], hl, _ => by simp at hl

/-- The fresh variables `|θ|, |θ|+1, ...` evaluate to the new values `θx`. -/
theorem evs_fresh (θ θx : List (dyn DA)) :
    evs DA (θ ++ θx) ((List.range θx.length).map (fun i => TVar (θ.length + i))) θx := by
  refine forall2_of_getElem (by simp) (fun i h1 h2 => ?_)
  simp only [List.getElem_map, List.getElem_range, teval, nth_error_eq]
  rw [List.getElem?_append_right (by omega), show θ.length + i - θ.length = i by omega]
  exact List.getElem?_eq_getElem h2

theorem evs_ext (θ θx θb : List (dyn DA)) (bs : List tterm) :
    evs DA θ bs θb → evs DA (θ ++ θx) bs θb :=
  forall2_mono (fun t d h => teval_ext DA θ θx t d h)

theorem sorted_length (θ : List (dyn DA)) (vars : List srt) : sorted DA θ vars → θ.length = vars.length := by
  intro h; rw [← h, List.length_map]

/-- One rule, applied to the application `p`. -/
theorem applyRule_sound (rules : List trule) (facts : List tfact) (Hf : Forall (fact_valid DA) facts)
    (Hp : preds_valid DA) (st : lstate) (r : trule) (Hr : rule_valid DA r) (p : tpat)
    (t : tterm) (st' : lstate) :
    applyRule (mkCtx syms preds rules facts) st r p = some (t, st') →
    ∀ (θ : List (dyn DA)) (Φ : val → IProp GF),
      iprop(st_den DA θ st ∗ (∀ θx, st_den DA (θ ++ θx) st' -∗ ⌜isval DA (θ ++ θx) t⌝ -∗
        Φ (val_den DA (θ ++ θx) t))) ⊢ WP (pat_den DA θ p) {{ Φ }} := by
  intro H θ Φ
  simp only [applyRule] at H
  split at H; · cases H
  rename_i b1 hb1
  split at H; · cases H
  rename_i b2 h hm
  split at H; · cases H
  rename_i bs hbs
  split at H
  case isFalse => cases H
  rename_i heqs
  split at H; · cases H
  rename_i h' p' hadd
  split at H; · cases H
  rename_i t0 ht0
  split at H; · cases H
  rename_i t1 ht1
  split at H
  case isFalse => cases H
  rename_i hsort
  simp only [Option.some.injEq, Prod.mk.injEq] at H
  obtain ⟨rfl, rfl⟩ := H
  -- what matching established
  obtain ⟨A1, B1, C1⟩ := mpat_sound syms st.vars r.r_vars r.r_lhs p _ b1 hb1
  have hl1 : b1.length = r.r_vars.length := by
    rw [mpat_length _ _ _ _ _ _ _ hb1, List.length_replicate]
  obtain ⟨A2, B2, _⟩ := matchPreds_sound DA rules facts Hp st.vars r.r_vars θ θ r.r_pre st.heap
    b1 b2 h hm
  have Hb2 : bwf syms st.vars r.r_vars b2 := B2 (B1 (bwf_replicate _ _ _ _))
  have hl2 : b2.length = r.r_vars.length := by
    rw [matchPreds_length _ _ _ _ _ _ _ _ hm, hl1]
  obtain ⟨hag, _, _⟩ := allBound_sound b2 bs hbs
  unfold st_den
  iintro ⟨⟨%Hθ, %Hpure, Hheap⟩, Hk⟩
  obtain ⟨θr, hev, hsr⟩ := evs_of_bound DA θ st.vars r.r_vars Hθ b2 bs hl2 Hb2 hbs
  have Hpat : pat_den DA θ p = pat_den DA θr r.r_lhs :=
    pinst_den DA θ θr bs hev r.r_lhs p (C1 bs (agrees_of_bext A2 hag))
  have Heqs := eqsHold_sound DA rules facts Hf st θ θr Hθ Hpure bs hev r.r_pre heqs
  have Htr := forall_sorts_at DA r.r_vars _ θr Hr hsr
  simp only [triple_at] at Htr
  rw [Hpat]
  have Hcont : iprop(heap_den DA θ h ∗ (∀ θx, st_den DA (θ ++ θx) (mkLState h' p' (st.vars ++ r.r_ex)) -∗
        ⌜isval DA (θ ++ θx) t1⌝ -∗ Φ (val_den DA (θ ++ θx) t1))) ⊢
      bi_forall_sorts DA r.r_ex (fun θx =>
        iprop(assn_den DA (vapp θr θx) r.r_post -∗ Φ (val_den DA (vapp θr θx) r.r_ret))) := by
    apply bi_forall_intro
    intro θx hsx
    have HΘ : sorted DA (θ ++ θx) (st.vars ++ r.r_ex) := sorted_app DA θ θx _ _ Hθ hsx
    have hlen : θx.length = r.r_ex.length := sorted_length DA θx r.r_ex hsx
    have hev' : evs DA (θ ++ θx)
        (bs ++ (List.range r.r_ex.length).map (fun i => TVar (st.vars.length + i))) (θr ++ θx) := by
      refine forall2_append (evs_ext DA θ θx θr bs hev) ?_
      have := evs_fresh DA θ θx
      rwa [hlen, sorted_length DA θ st.vars Hθ] at this
    have Hret : teval DA (θ ++ θx) t1 = teval DA (θr ++ θx) r.r_ret := by
      rw [norm_teval DA _ _ HΘ facts Hf _ t0 t1 ht1, inst_teval DA _ _ _ hev' r.r_ret t0 ht0]
    have Hval : val_den DA (θ ++ θx) t1 = val_den DA (θr ++ θx) r.r_ret := by
      simp only [val_den, Hret]
    rw [vapp_eq, ← Hval]
    iintro ⟨Hrest, Hk⟩ Hpost
    ihave Hnew := addAtoms_sound DA rules facts Hf _ (θ ++ θx) (θr ++ θx) HΘ _ hev' r.r_post h
      st.pure h' p' hadd $$ [Hrest Hpost]
    · isplitl [Hrest]
      · iapply heap_den_ext DA θ θx $$ Hrest
      isplitr
      · ipureintro; exact fun q hq => pure_den_ext DA θ θx q (Hpure q hq)
      · iapply (assn_den_eq DA _ r.r_post).1 $$ Hpost
    icases Hnew with ⟨Hh', %Hp'⟩
    iapply Hk $$ %θx [Hh']
    · unfold st_den
      iframe Hh'
      ipureintro
      exact ⟨HΘ, Hp'⟩
    ipureintro
    exact isval_of_sort DA _ _ HΘ t1 hsort
  ihave Ht := Htr
  icases (matchPreds_sound DA rules facts Hp st.vars r.r_vars θ θr r.r_pre st.heap b1 b2 h
    hm).2.2 bs hag hev Heqs $$ Hheap with ⟨Hpre, Hrest⟩
  iapply Ht $$ [Hpre] [Hrest Hk]
  · iapply (assn_den_eq DA θr r.r_pre).2 $$ Hpre
  inext
  iapply Hcont
  iframe


theorem tryRules_some (c : ctx) (st : lstate) (p : tpat) :
    ∀ (l : List trule) (res : tterm × lstate), tryRules c st p l = some res →
      ∃ r, r ∈ l ∧ applyRule c st r p = some res
  | [], _, h => by simp [tryRules] at h
  | r :: l, res, h => by
      simp only [tryRules] at h
      split at h
      · rename_i res' hr
        cases h
        exact ⟨r, List.mem_cons_self, hr⟩
      · obtain ⟨r', hr', h'⟩ := tryRules_some c st p l res h
        exact ⟨r', List.mem_cons_of_mem _ hr', h'⟩

theorem tryRules_sound (rules : List trule) (facts : List tfact) (Hf : Forall (fact_valid DA) facts)
    (Hp : preds_valid DA) (Hr : Forall (rule_valid DA) rules) (st : lstate) (p : tpat)
    (t : tterm) (st' : lstate) :
    tryRules (mkCtx syms preds rules facts) st p rules = some (t, st') →
    ∀ (θ : List (dyn DA)) (Φ : val → IProp GF),
      iprop(st_den DA θ st ∗ (∀ θx, st_den DA (θ ++ θx) st' -∗ ⌜isval DA (θ ++ θx) t⌝ -∗
        Φ (val_den DA (θ ++ θx) t))) ⊢ WP (pat_den DA θ p) {{ Φ }} := by
  intro h
  obtain ⟨r, hr, ha⟩ := tryRules_some _ st p rules (t, st') h
  exact applyRule_sound DA rules facts Hf Hp st r (forall_mem Hr hr) p t st' ha

/-! ## The function spine -/

def spine_at : tpat → Nat → tpat
  | s, 0 => s
  | PApp a _, d + 1 => spine_at a d
  | s, _ + 1 => s

/-- The evaluation context around the node `d` steps down the spine: the
arguments, as values. -/
def spine_ctx (θ : List (dyn DA)) : tpat → Nat → List EctxItem
  | _, 0 => []
  | PApp a (PVal t), d + 1 => spine_ctx θ a d ++ [EctxItem.AppLCtx (val_den DA θ t)]
  | _, _ + 1 => []

theorem spine_split (θ : List (dyn DA)) : ∀ (s : tpat) (d : Nat), pat_good DA θ s →
    pat_den DA θ s = fill (spine_ctx DA θ s d) (pat_den DA θ (spine_at s d))
  | s, 0, _ => by cases s <;> rfl
  | PVal t, _ + 1, _ => rfl
  | PApp a (PVal t), d + 1, ⟨ha, _⟩ => by
      simp only [spine_ctx, spine_at, EctxItemLanguage.fill_append, EctxItemLanguage.fill_cons,
        EctxItemLanguage.fill_nil, pat_den]
      rw [← spine_split θ a d ha]
      rfl
  | PApp _ (PApp _ _), _ + 1, h => h.elim

theorem spine_ctx_ext (θ θx : List (dyn DA)) : ∀ (s : tpat) (d : Nat), pat_good DA θ s →
    spine_ctx DA (θ ++ θx) s d = spine_ctx DA θ s d
  | _, 0, _ => by simp [spine_ctx]
  | PVal _, _ + 1, _ => rfl
  | PApp a (PVal t), d + 1, ⟨ha, ht⟩ => by
      simp only [spine_ctx, spine_ctx_ext θ θx a d ha, val_den_ext DA θ θx t ht]
  | PApp _ (PApp _ _), _ + 1, h => h.elim

theorem spineTry_sound (c : ctx) (st : lstate) : ∀ (s : tpat) (d : Nat) (t : tterm) (st' : lstate),
    spineTry c st s = some (d, t, st') →
    tryRules c st (spine_at s d) c.rules = some (t, st') ∧
    ∀ (θ : List (dyn DA)) (t' : tterm), pat_good DA θ s → isval DA θ t' →
      pat_good DA θ (replaceSpine t' d s) ∧
      pat_den DA θ (replaceSpine t' d s) = fill (spine_ctx DA θ s d) (Val (val_den DA θ t'))
  | PVal _, _, _, _, h => by simp [spineTry] at h
  | PApp a b, d, t, st', h => by
      simp only [spineTry] at h
      split at h
      · rename_i t1 st1 hr
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl, rfl⟩ := h
        refine ⟨hr, fun θ t' _ ht' => ⟨ht', ?_⟩⟩
        simp only [replaceSpine, pat_den, spine_ctx, EctxItemLanguage.fill_nil]
      · split at h
        · rename_i d1 t1 st1 ha
          simp only [Option.some.injEq, Prod.mk.injEq] at h
          obtain ⟨rfl, rfl, rfl⟩ := h
          obtain ⟨A, B⟩ := spineTry_sound c st a d1 t1 st1 ha
          refine ⟨A, fun θ t' hg ht' => ?_⟩
          cases b with
          | PApp _ _ => exact hg.elim
          | PVal u =>
            obtain ⟨hga, hu⟩ := hg
            obtain ⟨B1, B2⟩ := B θ t' hga ht'
            refine ⟨⟨B1, hu⟩, ?_⟩
            simp only [replaceSpine, pat_den, spine_ctx, B2, EctxItemLanguage.fill_append,
              EctxItemLanguage.fill_cons, EctxItemLanguage.fill_nil]
            rfl
        · cases h

/-- `reduce`: rules rewrite the application, outermost first along its spine,
until one applies to the whole of it. -/
theorem reduce_sound (rules : List trule) (facts : List tfact) (Hf : Forall (fact_valid DA) facts)
    (Hp : preds_valid DA) (Hr : Forall (rule_valid DA) rules) :
    ∀ (fuel : Nat) (st : lstate) (s : tpat) (t : tterm) (st' : lstate),
    reduce (mkCtx syms preds rules facts) fuel st s = some (t, st') →
    ∀ (θ : List (dyn DA)) (K : List EctxItem) (Ψ : val → IProp GF), pat_good DA θ s →
      iprop(st_den DA θ st ∗ (∀ θx, st_den DA (θ ++ θx) st' -∗ ⌜isval DA (θ ++ θx) t⌝ -∗
        WP (fill K (Val (val_den DA (θ ++ θx) t))) {{ Ψ }})) ⊢ WP (fill K (pat_den DA θ s)) {{ Ψ }}
  | 0, _, _, _, _, h => by simp [reduce] at h
  | fuel + 1, st, s, t, st', h => by
      intro θ K Ψ hg
      simp only [reduce] at h
      split at h
      · rename_i t1 st1 hs
        simp only [Option.some.injEq, Prod.mk.injEq] at h
        obtain ⟨rfl, rfl⟩ := h
        obtain ⟨A, _⟩ := spineTry_sound DA _ st s 0 t1 st1 hs
        simp only [spine_at] at A
        iintro Hst
        iapply wp_bind (fill K)
        iapply tryRules_sound DA rules facts Hf Hp Hr st s t1 st1 A θ
          (fun v => iprop(WP (fill K (Val v)) {{ Ψ }})) $$ Hst
      · rename_i d t1 st1 hs
        obtain ⟨A, B⟩ := spineTry_sound DA _ st s (d + 1) t1 st1 hs
        have IH := reduce_sound rules facts Hf Hp Hr fuel st1 _ t st' h
        rw [spine_split DA θ s (d + 1) hg, ← EctxItemLanguage.fill_append]
        iintro ⟨Hst, Hk⟩
        iapply wp_bind (fill (spine_ctx DA θ s (d + 1) ++ K))
        iapply tryRules_sound DA rules facts Hf Hp Hr st _ t1 st1 A θ
          (fun v => iprop(WP (fill (spine_ctx DA θ s (d + 1) ++ K) (Val v)) {{ Ψ }}))
        iframe Hst
        iintro %θx1 Hst1 %Ht1
        obtain ⟨hg1, hp1⟩ := pat_good_ext DA θ θx1 s hg
        obtain ⟨B1, B2⟩ := B (θ ++ θx1) t1 hg1 Ht1
        rw [EctxItemLanguage.fill_append, ← spine_ctx_ext DA θ θx1 s (d + 1) hg, ← B2]
        iapply IH (θ ++ θx1) K Ψ B1
        iframe Hst1
        iintro %θx2 Hst2 %Ht2
        rw [List.append_assoc]
        rw [List.append_assoc] at Ht2
        iapply Hk $$ %(θx1 ++ θx2) Hst2
        ipureintro; exact Ht2
      · cases h

end den

end LC
end TCheck
end Perennial
