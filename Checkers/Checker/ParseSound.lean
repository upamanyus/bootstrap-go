/-
Port of `new/checker/parse_sound.v`.

Semantics of the parsing half of the postcondition check
(checker/match.go: `parseDisjunct`, `parseDisjuncts`).

`parseDisjunct` peels a chain of `AExists` binders off a disjunct,
recording each binder's sort in `pats`/`patOk`, and then flattens the
separating conjunction underneath into `atoms`. The invariant of that
loop is `binders_interp`: the binders declared so far, existentially
quantified exactly as `dj_interp` quantifies them, over the remaining
body. This file proves that each step of the parse preserves the
entailment towards the original assertion, and that the flattened atoms
entail the body, so that a disjunct that parsed without failure entails
the assertion it was parsed from.

Lean notes:
* `<[k:=s]> l` is `l.set k s`; `l !! n` is `l[n]?`.
* `binders_entails`, like `dj_entails` (VerifyDef.lean), also quantifies over
  `GoGlobalContext` and `HasLC`.
-/
import Checkers.Checker.VerifyDef
import Checkers.Checker.Fn.growPats
import Checkers.Checker.Fn.flatten
import Checkers.Checker.Fn.collectDisjuncts

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode
open github_com.upamanyus.bootstrap_go

-- `bind_pat`: in LCheck/Fns.lean.

theorem lookup_pad_Some {A : Type} (xs : List A) (x y : A) (k m : Nat) :
    (pad xs x k)[m]? = some y → xs[m]? = some y ∨ y = x := by
  simp only [pad, List.getElem?_append]
  split
  · exact Or.inl
  · intro h
    right
    simp only [List.getElem?_replicate] at h
    split at h <;> simp_all

theorem lookup_pad_l {A : Type} (xs : List A) (x y : A) (k m : Nat) :
    xs[m]? = some y → (pad xs x k)[m]? = some y := by
  intro h
  simp only [pad]
  rw [List.getElem?_append_left (List.getElem?_eq_some_iff.mp h).1]
  exact h

section parse_sound
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem teval_ext (V V' : valuation) (t : term) :
    (∀ n, vvar V n = vvar V' n) → (∀ n, vpat V n = vpat V' n) → vret V = vret V' →
    teval V t = teval V' t := by
  intro Hv Hp Hr
  induction t with
  | TVar n => exact Hv n
  | TPat n => exact Hp n
  | TResult => exact Hr
  | TPlus a b iha ihb | TMinus a b iha ihb | TMul a b iha ihb | TEq a b iha ihb
  | TLt _ a b iha ihb | TLe _ a b iha ihb =>
    simp only [teval, iha, ihb]
  | TNeg a iha | TNot a iha | TRet a iha => simp only [teval, iha]
  | TIte c a b ihc iha ihb => simp only [teval, ihc, iha, ihb]
  | _ => rfl

theorem assn_interp_ext_1 (V V' : valuation) (a : cassn) :
    (∀ n, vvar V n = vvar V' n) → (∀ n, vpat V n = vpat V' n) → vret V = vret V' →
    assn_interp (GF := GF) V a ⊢ assn_interp V' a := by
  induction a generalizing V V' with
  | CAEmp => intro _ _ _; exact .rfl
  | CASep p q ihp ihq =>
    intro Hv Hp Hr
    simp only [assn_interp]
    iintro ⟨H1, H2⟩
    isplitl [H1]
    · iapply ihp V V' Hv Hp Hr $$ H1
    · iapply ihq V V' Hv Hp Hr $$ H2
  | CAOr p q ihp ihq =>
    intro Hv Hp Hr
    simp only [assn_interp]
    iintro (H | H)
    · ileft; iapply ihp V V' Hv Hp Hr $$ H
    · iright; iapply ihq V V' Hv Hp Hr $$ H
  | CAExists k s p ihp =>
    intro Hv Hp Hr
    simp only [assn_interp]
    iintro ⟨%w, %Hs, H⟩
    iexists w
    isplitr
    · ipureintro; exact Hs
    iapply ihp (upd_pat V k w) (upd_pat V' k w) (fun n => Hv n)
      (fun m => by simp only [upd_pat]; split <;> simp [Hp]) Hr $$ H
  | CAPure t =>
    intro Hv Hp Hr
    simp only [assn_interp, teval_ext V V' t Hv Hp Hr]
    exact .rfl
  | CAPointsTo x y =>
    intro Hv Hp Hr
    simp only [assn_interp, teval_ext V V' x Hv Hp Hr, teval_ext V V' y Hv Hp Hr]
    exact .rfl

theorem assn_interp_ext (V V' : valuation) (a : cassn) :
    (∀ n, vvar V n = vvar V' n) → (∀ n, vpat V n = vpat V' n) → vret V = vret V' →
    assn_interp (GF := GF) V a ⊣⊢ assn_interp V' a := by
  intro Hv Hp Hr
  exact ⟨assn_interp_ext_1 V V' a Hv Hp Hr,
    assn_interp_ext_1 V' V a (fun n => (Hv n).symm) (fun n => (Hp n).symm) Hr.symm⟩

/-- The loop invariant of `parseDisjunct`: the binders declared so far over
the remaining body `b`. -/
def binders_interp (V : valuation) (dj : cdisjunct) (b : cassn) : IProp GF :=
  iprop(∃ W : Nat → val,
     ⌜∀ n, (d_pat_ok dj)[n]? = some true →
           ∃ s, (d_pats dj)[n]? = some s ∧ has_sort (W n) s⌝ ∗
     ⌜∀ n, (d_pat_ok dj)[n]? ≠ some true → W n = vpat V n⌝ ∗
     assn_interp (mkVal (vvar V) W (vret V)) b)

/-- Before any binder: the body itself. -/
theorem binders_interp_init (V : valuation) (dj : cdisjunct) (b : cassn) :
    d_pat_ok dj = [] → binders_interp (GF := GF) V dj b ⊢ assn_interp V b := by
  intro Hok
  unfold binders_interp
  iintro ⟨%W, -, %HW, H⟩
  iapply (assn_interp_ext (mkVal (vvar V) W (vret V)) V b (fun _ => rfl)
    (fun n => HW n (by simp [Hok])) rfl).1 $$ H

/-- One binder peeled: `growPats` and then the two stores. -/
theorem binders_interp_step (V : valuation) (dj : cdisjunct) (k : Nat) (s : sort) (p : cassn) :
    (d_pats dj).length = (d_pat_ok dj).length →
    (d_pat_ok (grow_pats dj k))[k]? ≠ some true →
    binders_interp (GF := GF) V (bind_pat (grow_pats dj k) k s) p ⊢
      binders_interp V dj (CAExists k s p) := by
  intro Hlen Hnot
  obtain ⟨Hk1, Hk2⟩ := grow_pats_lookup dj k
  simp only [grow_pats] at Hnot Hk1 Hk2
  unfold binders_interp
  simp only [bind_pat, grow_pats]
  iintro ⟨%W, %H1, %H2, H⟩
  iexists (fun m => if m = k then vpat V m else W m)
  isplitr
  · ipureintro
    intro m Hm
    by_cases hmk : m = k
    · subst hmk; exact absurd (lookup_pad_l _ _ _ _ _ Hm) Hnot
    · obtain ⟨s', Hs', Hsort⟩ := H1 m (by
        rw [List.getElem?_set_ne (Ne.symm hmk)]; exact lookup_pad_l _ _ _ _ _ Hm)
      refine ⟨s', ?_, by simp [hmk, Hsort]⟩
      rw [List.getElem?_set_ne (Ne.symm hmk)] at Hs'
      have Hlt : m < (d_pats dj).length := by
        rw [Hlen]; exact (List.getElem?_eq_some_iff.mp Hm).1
      simp only [pad, List.getElem?_append_left Hlt] at Hs'
      exact Hs'
  isplitr
  · ipureintro
    intro m Hm
    by_cases hmk : m = k
    · simp [hmk]
    · simp only [hmk, ↓reduceIte]
      apply H2
      rw [List.getElem?_set_ne (Ne.symm hmk)]
      intro Hp
      rcases lookup_pad_Some _ _ _ _ _ Hp with h | h
      · exact Hm h
      · cases h
  · simp only [assn_interp]
    obtain ⟨s', Hs', Hsort⟩ := H1 k (by rw [List.getElem?_set_self Hk2])
    rw [List.getElem?_set_self Hk1] at Hs'
    cases Hs'
    iexists W k
    isplitr
    · ipureintro; exact Hsort
    iapply (assn_interp_ext (mkVal (vvar V) W (vret V))
      (upd_pat (mkVal (vvar V) (fun m => if m = k then vpat V m else W m) (vret V)) k (W k)) p
      (fun _ => rfl) (fun m => by
        simp only [upd_pat]; split <;> simp_all) rfl).1 $$ H

theorem assn_flatten_sound (V : valuation) (b : cassn) (ats : List cassn) :
    assn_flatten b = some ats →
    ([∗list] a ∈ ats, assn_interp (GF := GF) V a) ⊢ assn_interp V b := by
  induction b generalizing ats with
  | CAEmp => intro _; simp only [assn_interp]; iintro _; itrivial
  | CASep p q ihp ihq =>
    intro Hf
    simp only [assn_flatten] at Hf
    cases H1 : assn_flatten p with
    | none => simp [H1] at Hf
    | some l1 =>
      cases H2 : assn_flatten q with
      | none => simp [H1, H2] at Hf
      | some l2 =>
        simp only [H1, H2, Option.some.injEq] at Hf
        subst Hf
        simp only [assn_interp]
        iintro H
        icases BigSepL.bigSepL_append.1 $$ H with ⟨A, B⟩
        isplitl [A]
        · iapply ihp l1 H1 $$ A
        · iapply ihq l2 H2 $$ B
  | CAOr => intro Hf; simp [assn_flatten] at Hf
  | CAExists => intro Hf; simp [assn_flatten] at Hf
  | CAPure t =>
    intro Hf
    simp only [assn_flatten, Option.some.injEq] at Hf
    subst Hf
    iintro H
    iapply BigSepL.bigSepL_singleton.1 $$ H
  | CAPointsTo x y =>
    intro Hf
    simp only [assn_flatten, Option.some.injEq] at Hf
    subst Hf
    iintro H
    iapply BigSepL.bigSepL_singleton.1 $$ H

/-- The flattened body: `dj_interp` of the finished disjunct. -/
theorem dj_interp_flatten (V : valuation) (dj : cdisjunct) (b : cassn) (ats : List cassn) :
    d_atoms dj = [] → assn_flatten b = some ats →
    dj_interp (GF := GF) V (dj_atoms dj ats) ⊢ binders_interp V dj b := by
  intro Hat Hf
  unfold dj_interp binders_interp
  simp only [dj_atoms, Hat, List.nil_append]
  iintro ⟨%W, %H1, %H2, H⟩
  iexists W
  isplitr
  · ipureintro; exact H1
  isplitr
  · ipureintro; exact H2
  iapply assn_flatten_sound _ b ats Hf $$ H

/-- The whole postcondition: `collectDisjuncts` flattens the top-level `∨`
chain, and each of its members entails the chain. -/
theorem assn_disjuncts_sound (V : valuation) (post a : cassn) :
    some a ∈ assn_disjuncts post → assn_interp (GF := GF) V a ⊢ assn_interp V post := by
  induction post with
  | CAOr p q ihp ihq =>
    intro Hin
    simp only [assn_disjuncts, List.mem_append] at Hin
    simp only [assn_interp]
    rcases Hin with Hin | Hin
    · iintro H; ileft; iapply ihp Hin $$ H
    · iintro H; iright; iapply ihq Hin $$ H
  | _ =>
    intro Hin
    simp only [assn_disjuncts, List.mem_singleton, Option.some.injEq] at Hin
    subst Hin
    exact .rfl

end parse_sound

/-- `binders_interp` entails an assertion, in any ghost state: the invariant
of `parseDisjunct`'s loop, which ends in `dj_entails` (VerifyDef.lean). -/
def binders_entails (dj : cdisjunct) (b y : cassn) : Prop :=
  ∀ (ext : FfiSyntax) (ffi : FfiModel) (_ffi_interp : FfiInterp ffi)
    (_ffi_sem : FfiSemantics ext ffi) (_go_gctx : GoGlobalContext)
    (hlc : HasLC) (GF : BundledGFunctors) (_hG : HeapGS hlc GF) (_sem : go.Semantics),
    ∀ V, binders_interp (GF := GF) V dj b ⊢ assn_interp V y

end Checker
end Perennial
