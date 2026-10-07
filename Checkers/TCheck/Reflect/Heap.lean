/-
Soundness of the Lean table checker, part 3: the symbolic state.

`st_den DA θ st`: the valuation `θ` has the state's sorts, the state's
equations hold at `θ`, and the state's predicate atoms are owned. Matching
an assertion's predicates against the heap (`matchPreds`) takes their
denotation out of it -- consuming a non-persistent atom, keeping a
persistent one, whose predicate the table proves persistent
(`preds_valid`) -- and adding an assertion's atoms (`addAtoms`) puts them
back.
-/
import Checkers.TCheck.Reflect.Code

set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace TCheck
namespace LC

open Iris Iris.BI Iris.ProofMode

theorem perm_eraseIdx {α : Type} : ∀ (l : List α) (i : Nat) (x : α), l[i]? = some x →
    l.Perm (x :: l.eraseIdx i)
  | [], _, _, h => by simp at h
  | y :: l, 0, x, h => by simp at h; subst h; simp
  | y :: l, i + 1, x, h => by
      simp only [List.getElem?_cons_succ] at h
      simp only [List.eraseIdx_cons_succ]
      exact ((perm_eraseIdx l i x h).cons y).trans (List.Perm.swap x y _)

theorem findAtom_sound (c : ctx) (vars psorts : List srt) (n : Nat) (args : List tterm) :
    ∀ (h : List tatom) (j : Nat) (b b1 : Bind) (k : Nat),
      findAtom c vars psorts n args h j b = some (b1, k) →
      ∃ hargs, j ≤ k ∧ h[k - j]? = some (APred n hargs) ∧
        mterms c.syms vars psorts args hargs b = some b1
  | [], _, _, _, _, hf => by simp [findAtom] at hf
  | APred m hargs :: h, j, b, b1, k, hf => by
      simp only [findAtom] at hf
      split at hf
      · rename_i hnm
        simp only [beq_iff_eq] at hnm
        subst hnm
        split at hf
        · rename_i b2 hm
          simp only [Option.some.injEq, Prod.mk.injEq] at hf
          obtain ⟨rfl, rfl⟩ := hf
          exact ⟨hargs, Nat.le_refl _, by simp, hm⟩
        · obtain ⟨ha, hjk, hk, hm⟩ := findAtom_sound c vars psorts n args h (j + 1) b b1 k hf
          exact ⟨ha, by omega, by rw [show k - j = (k - (j + 1)) + 1 by omega]; simpa using hk, hm⟩
      · obtain ⟨ha, hjk, hk, hm⟩ := findAtom_sound c vars psorts n args h (j + 1) b b1 k hf
        exact ⟨ha, by omega, by rw [show k - j = (k - (j + 1)) + 1 by omega]; simpa using hk, hm⟩
  | AEq _ _ :: h, j, b, b1, k, hf => by
      simp only [findAtom] at hf
      obtain ⟨ha, hjk, hk, hm⟩ := findAtom_sound c vars psorts n args h (j + 1) b b1 k hf
      exact ⟨ha, by omega, by rw [show k - j = (k - (j + 1)) + 1 by omega]; simpa using hk, hm⟩

theorem matchPreds_length (c : ctx) (vars psorts : List srt) :
    ∀ (xs h : List tatom) (b b' : Bind) (h' : List tatom),
      matchPreds c vars psorts xs h b = some (b', h') → b'.length = b.length
  | [], _, _, _, _, hm => by simp only [matchPreds, Option.some.injEq, Prod.mk.injEq] at hm; rw [hm.1]
  | APred n args :: xs, h, b, b', h', hm => by
      simp only [matchPreds] at hm
      split at hm
      · rename_i b1 k hf
        obtain ⟨_, _, _, hmt⟩ := findAtom_sound c vars psorts n args h 0 b b1 k hf
        rw [matchPreds_length c vars psorts xs _ b1 b' h' hm, mterms_length _ _ _ _ _ _ _ hmt]
      · cases hm
  | AEq _ _ :: xs, h, b, b', h', hm => by
      simp only [matchPreds] at hm
      exact matchPreds_length c vars psorts xs h b b' h' hm

section den
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable {syms : List symdecl} {preds : List preddecl} (DA : DenAt GF syms preds)

/-! ## The state -/

def pure_den (θ : List (dyn DA)) (p : tterm × tterm) : Prop :=
  ∃ d, teval DA θ p.1 = some d ∧ teval DA θ p.2 = some d

def heap_den (θ : List (dyn DA)) (h : List tatom) : IProp GF :=
  iprop([∗list] a ∈ h, atom_den DA θ a)

def st_den (θ : List (dyn DA)) (st : lstate) : IProp GF :=
  iprop(⌜sorted DA θ st.vars⌝ ∗ ⌜∀ p, p ∈ st.pure → pure_den DA θ p⌝ ∗ heap_den DA θ st.heap)

theorem cons_intro {A : Type} (Φ : A → IProp GF) (x : A) (l : List A) :
    iprop(Φ x ∗ [∗list] y ∈ l, Φ y) ⊢ iprop([∗list] y ∈ x :: l, Φ y) :=
  (BigSepL.bigSepL_cons (Φ := fun _ y => Φ y)).2
theorem cons_elim {A : Type} (Φ : A → IProp GF) (x : A) (l : List A) :
    iprop([∗list] y ∈ x :: l, Φ y) ⊢ iprop(Φ x ∗ [∗list] y ∈ l, Φ y) :=
  (BigSepL.bigSepL_cons (Φ := fun _ y => Φ y)).1
theorem nil_intro {A : Type} (Φ : A → IProp GF) : ⊢ iprop([∗list] y ∈ ([] : List A), Φ y) :=
  BigSepL.bigSepL_nil_intro

theorem assn_den_eq (θ : List (dyn DA)) :
    ∀ (xs : List tatom), assn_den DA θ xs ⊣⊢ iprop([∗list] a ∈ xs, atom_den DA θ a)
  | [] => ⟨BigSepL.bigSepL_nil_intro, true_intro⟩
  | [a] => by
      simp only [assn_den]
      constructor
      · iintro H; iapply cons_intro; iframe H; iapply nil_intro
      · iintro H; icases cons_elim _ _ _ $$ H with ⟨H, -⟩; iexact H
  | a :: b :: xs => by
      have IH := assn_den_eq θ (b :: xs)
      simp only [assn_den] at IH ⊢
      constructor
      · iintro ⟨Ha, Hl⟩; iapply cons_intro; iframe Ha; iapply IH.1 $$ Hl
      · iintro H; icases cons_elim _ _ _ $$ H with ⟨Ha, Hl⟩; iframe Ha; iapply IH.2 $$ Hl

theorem atom_den_pred (θ θ' : List (dyn DA)) (n : Nat) (args args' : List tterm) :
    tevals DA θ args = tevals DA θ' args' → atom_den DA θ (APred n args) = atom_den DA θ' (APred n args') := by
  intro h; simp only [atom_den, h]

theorem atom_den_ext (θ θx : List (dyn DA)) (a : tatom) :
    atom_den DA θ a ⊢ atom_den DA (θ ++ θx) a := by
  cases a with
  | APred n args =>
    simp only [atom_den]
    split
    · rename_i P hP
      rw [tevals_ext DA θ θx args (sym_apply_some DA _ _ _ P hP), hP]
    · iintro H; icases H with %H; exact H.elim
  | AEq a b =>
    simp only [atom_den]
    iintro %H
    ipureintro
    obtain ⟨d, ha, hb⟩ := H
    exact ⟨d, teval_ext DA θ θx a d ha, teval_ext DA θ θx b d hb⟩

theorem heap_den_ext (θ θx : List (dyn DA)) (h : List tatom) :
    heap_den DA θ h ⊢ heap_den DA (θ ++ θx) h :=
  BigSepL.bigSepL_mono fun {_ _} _ => atom_den_ext DA θ θx _

theorem pure_den_ext (θ θx : List (dyn DA)) (p : tterm × tterm) :
    pure_den DA θ p → pure_den DA (θ ++ θx) p := fun ⟨d, ha, hb⟩ =>
  ⟨d, teval_ext DA θ θx _ d ha, teval_ext DA θ θx _ d hb⟩

/-! ## Persistent predicates -/

theorem pers_ok_sym_apply : ∀ (ss : List srt) (P : arrows DA.d_sort ss (IProp GF))
    (vs : List (Option (dyn DA))) (Q : IProp GF),
    pers_ok DA ss P → sym_apply DA ss P vs = some Q → Persistent Q
  | [], P, [], Q, hp, h => by simp only [sym_apply] at h; obtain rfl := Option.some.inj h; exact hp
  | [], _, _ :: _, _, _, h => by simp [sym_apply] at h
  | _ :: _, _, [], _, _, h => by simp [sym_apply] at h
  | _ :: _, _, none :: _, _, _, h => by simp [sym_apply] at h
  | a :: ss, P, some d :: vs, Q, hp, h => by
      simp only [sym_apply] at h
      split at h
      · rename_i x _
        exact pers_ok_sym_apply ss (P x) vs Q (hp x) h
      · cases h

theorem pers_obl_get : ∀ (l : List preddecl) (n0 k : Nat) (d : preddecl),
    pers_obl DA l n0 → l[k]? = some d → d.pd_pers = true →
    pers_ok DA (lookup_pred preds (n0 + k)).pd_args (DA.d_pred (n0 + k))
  | [], _, _, _, _, hk, _ => by simp at hk
  | d' :: l, n0, 0, d, ⟨h1, _⟩, hk, hp => by
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hk
      subst hk
      simp only [hp] at h1
      exact h1
  | _ :: l, n0, k + 1, d, ⟨_, h2⟩, hk, hp => by
      have := pers_obl_get l (n0 + 1) k d h2 (by simpa using hk) hp
      rwa [show n0 + 1 + k = n0 + (k + 1) by omega] at this

theorem atom_persistent (rules : List trule) (facts : List tfact) (Hp : preds_valid DA)
    (θ : List (dyn DA)) (n : Nat) (args : List tterm) :
    pers (mkCtx syms preds rules facts) n = true → Persistent (atom_den DA θ (APred n args)) := by
  intro hpn
  simp only [pers] at hpn
  split at hpn
  · rename_i d hd
    have hok := pers_obl_get DA preds 0 n d Hp hd hpn
    rw [Nat.zero_add] at hok
    simp only [atom_den]
    split
    · rename_i Q hQ
      exact pers_ok_sym_apply DA _ _ _ Q hok hQ
    · infer_instance
  · cases hpn

/-! ## Matching an assertion's predicates against the heap -/

/-- The equations of an assertion hold at `θb`. -/
def eqs_den (θb : List (dyn DA)) (xs : List tatom) : Prop :=
  ∀ a b, AEq a b ∈ xs → pure_den DA θb (a, b)

theorem matchPreds_sound (rules : List trule) (facts : List tfact) (Hp : preds_valid DA)
    (vars psorts : List srt) (θ θb : List (dyn DA)) :
    ∀ (xs h : List tatom) (b b' : Bind) (h' : List tatom),
      matchPreds (mkCtx syms preds rules facts) vars psorts xs h b = some (b', h') →
      bext b b' ∧ (bwf syms vars psorts b → bwf syms vars psorts b') ∧
      ∀ bs, agrees b' bs → evs DA θ bs θb → eqs_den DA θb xs →
        heap_den DA θ h ⊢ iprop(([∗list] a ∈ xs, atom_den DA θb a) ∗ heap_den DA θ h')
  | [], h, b, b', h', hm => by
      simp only [matchPreds, Option.some.injEq, Prod.mk.injEq] at hm
      obtain ⟨rfl, rfl⟩ := hm
      refine ⟨bext_refl b, id, fun bs _ _ _ => ?_⟩
      iintro H; isplitr
      · iapply BigSepL.bigSepL_nil_intro; iempintro
      · iexact H
  | APred n args :: xs, h, b, b', h', hm => by
      simp only [matchPreds] at hm
      split at hm
      · rename_i b1 k hf
        obtain ⟨hargs, _, hk, hmt⟩ := findAtom_sound _ vars psorts n args h 0 b b1 k hf
        simp only [Nat.sub_zero] at hk
        obtain ⟨A1, B1, C1⟩ := mterms_sound syms vars psorts args hargs b b1 hmt
        obtain ⟨A2, B2, C2⟩ := matchPreds_sound rules facts Hp vars psorts θ θb xs _ b1 b' h' hm
        refine ⟨bext_trans A1 A2, fun hb => B2 (B1 hb), fun bs hag hev heq => ?_⟩
        have heq' : eqs_den DA θb xs := fun a b' hin => heq a b' (List.mem_cons_of_mem _ hin)
        have hatom : atom_den DA θb (APred n args) = atom_den DA θ (APred n hargs) :=
          (atom_den_pred DA θ θb n hargs args
            (insts_tevals DA θ θb bs hev args hargs (C1 bs (agrees_of_bext A2 hag)))).symm
        have IH := C2 bs hag hev heq'
        by_cases hpn : pers (mkCtx syms preds rules facts) n = true
        · simp only [hpn, ↓reduceIte] at IH
          have := atom_persistent DA rules facts Hp θ n hargs hpn
          unfold heap_den at IH ⊢
          iintro H
          ihave #Ha := BigSepL.bigSepL_lookup (Φ := fun _ a => atom_den DA θ a) hk $$ H
          icases IH $$ H with ⟨Hxs, Hh⟩
          iframe Hh
          iapply cons_intro
          rw [hatom]
          iframe Ha Hxs
        · simp only [Bool.not_eq_true] at hpn
          simp only [hpn, Bool.false_eq_true, ↓reduceIte] at IH
          unfold heap_den at IH ⊢
          refine (BigSepL.bigSepL_perm (Φ := atom_den DA θ) (perm_eraseIdx h k _ hk)).1.trans ?_
          iintro H
          icases cons_elim _ _ _ $$ H with ⟨Ha, H⟩
          icases IH $$ H with ⟨Hxs, Hh⟩
          iframe Hh
          iapply cons_intro
          rw [hatom]
          iframe Ha Hxs
      · cases hm
  | AEq x y :: xs, h, b, b', h', hm => by
      simp only [matchPreds] at hm
      obtain ⟨A, B, C⟩ := matchPreds_sound rules facts Hp vars psorts θ θb xs h b b' h' hm
      refine ⟨A, B, fun bs hag hev heq => ?_⟩
      have IH := C bs hag hev (fun a b' hin => heq a b' (List.mem_cons_of_mem _ hin))
      have hxy := heq x y List.mem_cons_self
      iintro H
      icases IH $$ H with ⟨Hxs, Hh⟩
      iframe Hh
      iapply cons_intro
      iframe Hxs
      simp only [atom_den]; ipureintro; exact hxy

/-! ## Equations -/

theorem holds_sound (rules : List trule) (facts : List tfact) (Hf : Forall (fact_valid DA) facts)
    (st : lstate) (θ : List (dyn DA)) (Hθ : sorted DA θ st.vars)
    (Hpure : ∀ p, p ∈ st.pure → pure_den DA θ p) (a b : tterm) :
    holds (mkCtx syms preds rules facts) st a b = true → pure_den DA θ (a, b) := by
  intro h
  simp only [holds] at h
  split at h
  · rename_i na nb ha hb
    have Ea := norm_teval DA θ st.vars Hθ facts Hf _ a na ha
    have Eb := norm_teval DA θ st.vars Hθ facts Hf _ b nb hb
    simp only [Bool.or_eq_true, Bool.and_eq_true, Option.isSome_iff_exists, List.any_eq_true] at h
    rcases h with ⟨heq, s, hs⟩ | ⟨p, hp, hpe⟩
    · have := teq_sound na nb heq
      subst this
      obtain ⟨x, hx⟩ := sortOf_sound DA θ st.vars Hθ na s hs
      exact ⟨_, Ea ▸ hx, Eb ▸ hx⟩
    · obtain ⟨d, h1, h2⟩ := Hpure p hp
      rcases hpe with ⟨e1, e2⟩ | ⟨e1, e2⟩
      · rw [teq_sound _ _ e1] at h1; rw [teq_sound _ _ e2] at h2
        exact ⟨d, Ea ▸ h1, Eb ▸ h2⟩
      · rw [teq_sound _ _ e1] at h1; rw [teq_sound _ _ e2] at h2
        exact ⟨d, Ea ▸ h2, Eb ▸ h1⟩
  · cases h

theorem eqsHold_sound (rules : List trule) (facts : List tfact) (Hf : Forall (fact_valid DA) facts)
    (st : lstate) (θ θb : List (dyn DA)) (Hθ : sorted DA θ st.vars)
    (Hpure : ∀ p, p ∈ st.pure → pure_den DA θ p) (bs : List tterm) (hev : evs DA θ bs θb)
    (xs : List tatom) : eqsHold (mkCtx syms preds rules facts) st bs xs = true → eqs_den DA θb xs := by
  induction xs with
  | nil => intro _ a b hin; cases hin
  | cons x xs ih =>
    intro h a b hin
    cases x with
    | APred _ _ =>
      simp only [eqsHold] at h
      rcases List.mem_cons.mp hin with he | hin
      · cases he
      · exact ih h a b hin
    | AEq x y =>
      simp only [eqsHold, Bool.and_eq_true] at h
      rcases List.mem_cons.mp hin with he | hin
      · cases he
        obtain ⟨h1, _⟩ := h
        split at h1
        · rename_i x' y' hx hy
          obtain ⟨d, e1, e2⟩ := holds_sound DA rules facts Hf st θ Hθ Hpure x' y' h1
          refine ⟨d, ?_, ?_⟩
          · rw [← inst_teval DA θ θb bs hev a x' hx]; exact e1
          · rw [← inst_teval DA θ θb bs hev b y' hy]; exact e2
        · cases h1
      · exact ih h.2 a b hin

/-! ## Adding an assertion's atoms -/

theorem mapOpt_norm_tevals (facts : List tfact) (Hf : Forall (fact_valid DA) facts)
    (θ : List (dyn DA)) (vars : List srt) (Hθ : sorted DA θ vars) (rules : List trule)
    (ts us : List tterm) :
    mapOpt (normT (mkCtx syms preds rules facts) vars) ts = some us → tevals DA θ us = tevals DA θ ts :=
  mapOpt_tevals DA θ _ (fun a a' h => norm_teval DA θ vars Hθ facts Hf _ a a' h) ts us

theorem addAtoms_sound (rules : List trule) (facts : List tfact) (Hf : Forall (fact_valid DA) facts)
    (vars : List srt) (Θ θb : List (dyn DA)) (HΘ : sorted DA Θ vars) (bs : List tterm)
    (hev : evs DA Θ bs θb) :
    ∀ (xs h : List tatom) (p : List (tterm × tterm)) (h' : List tatom) (p' : List (tterm × tterm)),
      addAtoms (mkCtx syms preds rules facts) vars bs xs h p = some (h', p') →
      iprop(heap_den DA Θ h ∗ ⌜∀ q, q ∈ p → pure_den DA Θ q⌝ ∗ [∗list] a ∈ xs, atom_den DA θb a) ⊢
      iprop(heap_den DA Θ h' ∗ ⌜∀ q, q ∈ p' → pure_den DA Θ q⌝)
  | [], h, p, h', p', ha => by
      simp only [addAtoms, Option.some.injEq, Prod.mk.injEq] at ha
      obtain ⟨rfl, rfl⟩ := ha
      iintro ⟨H, %Hp, -⟩
      iframe H
      ipureintro; exact Hp
  | APred n args :: xs, h, p, h', p', ha => by
      simp only [addAtoms] at ha
      split at ha
      · rename_i args' hargs
        split at ha
        · rename_i nargs hn
          have IH := addAtoms_sound rules facts Hf vars Θ θb HΘ bs hev xs _ p h' p' ha
          have hatom : atom_den DA θb (APred n args) = atom_den DA Θ (APred n nargs) := by
            apply atom_den_pred
            rw [mapOpt_norm_tevals DA facts Hf Θ vars HΘ rules args' nargs hn,
              insts_tevals DA Θ θb bs hev args args' hargs]
          iintro ⟨H, %Hp, Hl⟩
          icases cons_elim _ _ _ $$ Hl with ⟨Ha, Hxs⟩
          rw [hatom]
          iapply IH
          isplitl [H Ha]
          · unfold heap_den
            iapply BigSepL.bigSepL_append.2
            iframe H
            iapply BigSepL.bigSepL_singleton.2
            iexact Ha
          isplitr
          · ipureintro; exact Hp
          · iexact Hxs
        · cases ha
      · cases ha
  | AEq a b :: xs, h, p, h', p', ha => by
      simp only [addAtoms] at ha
      split at ha
      · rename_i a' b' hai hbi
        split at ha
        · rename_i na nb hna hnb
          have IH := addAtoms_sound rules facts Hf vars Θ θb HΘ bs hev xs h _ h' p' ha
          iintro ⟨H, %Hp, Hl⟩
          icases cons_elim _ _ _ $$ Hl with ⟨Hab, Hxs⟩
          ihave %Hab := (show atom_den DA θb (AEq a b) ⊢
            iprop(⌜∃ d, teval DA θb a = some d ∧ teval DA θb b = some d⌝) from .rfl) $$ Hab
          iapply IH
          iframe H Hxs
          ipureintro
          intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact Hp q hq
          · simp only [List.mem_singleton] at hq
            subst hq
            obtain ⟨d, h1, h2⟩ := Hab
            refine ⟨d, ?_, ?_⟩
            · rw [norm_teval DA Θ vars HΘ facts Hf _ a' na hna, inst_teval DA Θ θb bs hev a a' hai]
              exact h1
            · rw [norm_teval DA Θ vars HΘ facts Hf _ b' nb hnb, inst_teval DA Θ θb bs hev b b' hbi]
              exact h2
        · cases ha
      · cases ha

end den

end LC
end TCheck
end Perennial
