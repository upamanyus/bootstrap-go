/-
Port of `new/checker/fn/instantiate.v`.

`checker.instantiate` (checker/match.go): substitute the bound pattern
variables and `ret` into a term, rebuilding the spine above them.

Lean notes:
* `is_tpat`/`is_tpat_code` are imported from Fn/hasPat.lean (Rocq repeats
  them here; one Lean namespace cannot hold both copies).
* `is_Some r` is `r.isSome`.
* Iris's `a || b || c` notation forces parenthesised Boolean chains.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Fn.hasPat

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-! ## The mirror -/

-- `tbind1`, `tbind2`, `tbind3`, `instantiate_t`: in LCheck/Fns.lean.


def oinstantiate_t (ox : Option term) (σ : List (Option term)) (r : Option term) :
    Option term :=
  match ox with | none => none | some x => instantiate_t x σ r

/-! ## When the result of a child is a real term

`instantiate(t, subst, nil)` with a `TResult` strictly below the root
builds a node with a nil child, which no `term` describes (see the report
in NOTES.md). `inst_wf` excludes exactly that; it is vacuous whenever
`ret` is a real term, which is the case at every call site. -/

def has_result : term → Bool
  | TResult => true
  | TPlus p q | TMinus p q | TMul p q | TEq p q | TLt _ p q | TLe _ p q =>
      has_result p || has_result q
  | TNeg p | TNot p | TRet p => has_result p
  | TIte p q z => (has_result p || has_result q) || has_result z
  | _ => false

def ohas_result : Option term → Bool
  | none => false
  | some x => has_result x

def is_tresult : term → Bool
  | TResult => true
  | _ => false

theorem is_tresult_code (x : term) : decide (term_code x = W64 3) = is_tresult x := by
  cases x <;> simp only [term_code, is_tresult] <;> (try split) <;> rfl

theorem has_result_node (x : term) :
    has_result x = (((is_tresult x || ohas_result (term_a x)) || ohas_result (term_b x))
                    || ohas_result (term_c x)) := by
  cases x <;> simp [has_result, is_tresult, ohas_result, term_a, term_b, term_c, Bool.or_assoc]

theorem has_result_children (x : term) :
    has_result x = false →
    ohas_result (term_a x) = false ∧ ohas_result (term_b x) = false ∧
    ohas_result (term_c x) = false := by
  rw [has_result_node]; simp only [Bool.or_eq_false_iff]
  intro ⟨⟨⟨_, a⟩, b⟩, c⟩; exact ⟨a, b, c⟩

theorem tbind1_isSome (f : term → term) (oa : Option term) :
    (tbind1 f oa).isSome = oa.isSome := by
  cases oa <;> rfl
theorem tbind2_isSome (f : term → term → term) (oa ob : Option term) :
    (tbind2 f oa ob).isSome = (oa.isSome && ob.isSome) := by
  cases oa <;> cases ob <;> rfl
theorem tbind3_isSome (f : term → term → term → term) (oa ob oc : Option term) :
    (tbind3 f oa ob oc).isSome = ((oa.isSome && ob.isSome) && oc.isSome) := by
  cases oa <;> cases ob <;> cases oc <;> rfl

theorem inst_Some_r (x : term) (σ : List (Option term)) (r : Option term) :
    r.isSome → ∃ y, instantiate_t x σ r = some y := by
  intro Hr
  apply Option.isSome_iff_exists.mp
  induction x <;>
    simp_all [instantiate_t, tbind1_isSome, tbind2_isSome, tbind3_isSome]

theorem inst_Some_n (x : term) (σ : List (Option term)) (r : Option term) :
    has_result x = false → ∃ y, instantiate_t x σ r = some y := by
  intro Hn
  apply Option.isSome_iff_exists.mp
  induction x <;>
    simp_all [instantiate_t, has_result, tbind1_isSome, tbind2_isSome, tbind3_isSome]

theorem inst_Some (x : term) (σ : List (Option term)) (r : Option term) :
    (r.isSome ∨ has_result x = false) → ∃ y, instantiate_t x σ r = some y := by
  rintro (H | H)
  · exact inst_Some_r x σ r H
  · exact inst_Some_n x σ r H

def inst_wf (r : Option term) (x : term) : Prop :=
  r.isSome ∨ (ohas_result (term_a x) = false ∧ ohas_result (term_b x) = false ∧
               ohas_result (term_c x) = false)

def inst_wf_o (r : Option term) : Option term → Prop
  | none => True
  | some x => inst_wf r x

theorem inst_wf_child (r : Option term) (x p : term) :
    inst_wf r x → (term_a x = some p ∨ term_b x = some p ∨ term_c x = some p) →
    inst_wf r p := by
  rintro (Hr | ⟨Ha, Hb, Hc⟩) Hin
  · exact Or.inl Hr
  · right; apply has_result_children
    rcases Hin with H | H | H
    · rw [H] at Ha; exact Ha
    · rw [H] at Hb; exact Hb
    · rw [H] at Hc; exact Hc

theorem inst_wf_o_a (r : Option term) (x : term) : inst_wf r x → inst_wf_o r (term_a x) := by
  intro H; cases E : term_a x with
  | none => trivial
  | some p => exact inst_wf_child r x p H (Or.inl E)
theorem inst_wf_o_b (r : Option term) (x : term) : inst_wf r x → inst_wf_o r (term_b x) := by
  intro H; cases E : term_b x with
  | none => trivial
  | some p => exact inst_wf_child r x p H (Or.inr (Or.inl E))
theorem inst_wf_o_c (r : Option term) (x : term) : inst_wf r x → inst_wf_o r (term_c x) := by
  intro H; cases E : term_c x with
  | none => trivial
  | some p => exact inst_wf_child r x p H (Or.inr (Or.inr E))

/-- A node with no children is returned unchanged. -/
theorem instantiate_leaf (x : term) (σ : List (Option term)) (r : Option term) :
    is_tpat x = false → is_tresult x = false →
    term_a x = none → term_b x = none → term_c x = none →
    instantiate_t x σ r = some x := by
  cases x <;> simp [is_tpat, is_tresult, term_a, term_b, term_c, instantiate_t]

/-- What each child needs for the rebuilt node to have no nil child. -/
def inst_ok (r : Option term) : Option term → Prop
  | none => True
  | some p => r.isSome ∨ has_result p = false

theorem inst_wf_ok_a (r : Option term) (x : term) : inst_wf r x → inst_ok r (term_a x) := by
  rintro (H | ⟨H, _, _⟩) <;> cases E : term_a x <;> simp_all [inst_ok, ohas_result]
theorem inst_wf_ok_b (r : Option term) (x : term) : inst_wf r x → inst_ok r (term_b x) := by
  rintro (H | ⟨_, H, _⟩) <;> cases E : term_b x <;> simp_all [inst_ok, ohas_result]
theorem inst_wf_ok_c (r : Option term) (x : term) : inst_wf r x → inst_ok r (term_c x) := by
  rintro (H | ⟨_, _, H⟩) <;> cases E : term_c x <;> simp_all [inst_ok, ohas_result]

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

/-! ## The specification -/

def is_subst (s : GoSlice) (σ : List (Option term)) : IProp GF :=
  iprop(∃ ls : List Loc, s ↦* ls ∗ [∗list] li;oi ∈ ls;σ, is_oterm li oi)

/-- The rebuilt node. Every constructor with a child is covered here, so
that the `wp` proof below can stay generic in the node's kind. -/
theorem is_oterm_rebuild (lz : Loc) (x : term) (l2 l3 l4 : Loc)
    (σ : List (Option term)) (r : Option term) :
    inst_wf r x →
    (term_a x ≠ none ∨ term_b x ≠ none ∨ term_c x ≠ none) →
    lz ↦□ tnode (term_code x) (term_num x) l2 l3 l4 ⊢
    is_oterm (GF := GF) l2 (oinstantiate_t (term_a x) σ r) -∗
    is_oterm l3 (oinstantiate_t (term_b x) σ r) -∗
    is_oterm l4 (oinstantiate_t (term_c x) σ r) -∗
    is_oterm lz (instantiate_t x σ r) := by
  intro Hwf Hch
  have Hoa := inst_wf_ok_a _ _ Hwf
  have Hob := inst_wf_ok_b _ _ Hwf
  have Hoc := inst_wf_ok_c _ _ Hwf
  clear Hwf
  cases x with
  | TPlus p q | TMinus p q | TMul p q | TEq p q =>
    simp only [inst_ok, term_a, term_b] at Hoa Hob
    obtain ⟨ya, Hya⟩ := inst_Some p σ r Hoa
    obtain ⟨yb, Hyb⟩ := inst_Some q σ r Hob
    simp only [oinstantiate_t, instantiate_t, Hya, Hyb, tbind2, is_oterm, is_term, term_code,
      term_num, term_a, term_b, term_c]
    iintro #Hl #H2 #H3 %H4
    subst H4
    iexists l2, l3
    iframe Hl H2 H3
  | TLt sg p q | TLe sg p q =>
    simp only [inst_ok, term_a, term_b] at Hoa Hob
    obtain ⟨ya, Hya⟩ := inst_Some p σ r Hoa
    obtain ⟨yb, Hyb⟩ := inst_Some q σ r Hob
    simp only [oinstantiate_t, instantiate_t, Hya, Hyb, tbind2, is_oterm, is_term, term_code,
      term_num, term_a, term_b, term_c]
    iintro #Hl #H2 #H3 %H4
    subst H4
    iexists l2, l3
    iframe Hl H2 H3
  | TNeg p | TNot p | TRet p =>
    simp only [inst_ok, term_a] at Hoa
    obtain ⟨ya, Hya⟩ := inst_Some p σ r Hoa
    simp only [oinstantiate_t, instantiate_t, Hya, tbind1, is_oterm, is_term, term_code,
      term_num, term_a, term_b, term_c]
    iintro #Hl #H2 %H3 %H4
    subst H3 H4
    iexists l2
    iframe Hl H2
  | TIte p q z =>
    simp only [inst_ok, term_a, term_b, term_c] at Hoa Hob Hoc
    obtain ⟨ya, Hya⟩ := inst_Some p σ r Hoa
    obtain ⟨yb, Hyb⟩ := inst_Some q σ r Hob
    obtain ⟨yc, Hyc⟩ := inst_Some z σ r Hoc
    simp only [oinstantiate_t, instantiate_t, Hya, Hyb, Hyc, tbind3, is_oterm, is_term,
      term_code, term_num, term_a, term_b, term_c]
    iintro #Hl #H2 #H3 #H4
    iexists l2, l3, l4
    iframe Hl H2 H3 H4
  | _ => simp [term_a, term_b, term_c] at Hch

theorem wp_instantiate (lx : Loc) (s : GoSlice) (lr : Loc)
    (ox : Option term) (σ : List (Option term)) (oret : Option term) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ ⌜inst_wf_o oret ox⌝ ∗
        is_oterm lx ox ∗ is_subst s σ ∗ is_oterm lr oret }}
      (App (App (App (Val (@! checker.instantiate)) (Val #lx)) (Val #s)) (Val #lr))
    {{ (l : Loc), RET #l; is_subst s σ ∗ is_oterm l (oinstantiate_t ox σ oret) }} := by
  iloeb as IH generalizing %lx %ox
  wp_start as ⟨%Hwf, #Hox, Hsub, #Hor⟩
  ihave %Hnull := is_oterm_null _ _ $$ Hox
  wp_auto
  wp_if_destruct
  · -- `t` is nil
    obtain rfl : ox = none := Hnull.mp rfl
    iapply HΦ
    iframe Hsub
    simp only [oinstantiate_t, is_oterm]
    ipureintro; trivial
  · cases ox with
    | none => exact absurd (Hnull.mpr rfl) Hif
    | some x =>
    rw [is_oterm_some]
    icases is_term_node _ _ $$ Hox with ⟨%la, %lb, %lc, %Hw, #Hn, #Ha, #Hb, #Hc⟩
    iStructNamed Hn
    wp_auto
    rw [is_tpat_code]
    cases Hp : is_tpat x
    · wp_auto
      rw [is_tresult_code]
      cases Hr : is_tresult x
      · ihave %Hna := is_oterm_null _ _ $$ Ha
        ihave %Hnb := is_oterm_null _ _ $$ Hb
        ihave %Hnc := is_oterm_null _ _ $$ Hc
        wp_auto
        have Hwf' : inst_wf oret x := Hwf
        have Hrebuild : (la ≠ null ∨ lb ≠ null ∨ lc ≠ null) →
            term_a x ≠ none ∨ term_b x ≠ none ∨ term_c x ≠ none := by
          rintro (H | H | H)
          · exact Or.inl (fun e => H (Hna.mpr e))
          · exact Or.inr (Or.inl (fun e => H (Hnb.mpr e)))
          · exact Or.inr (Or.inr (fun e => H (Hnc.mpr e)))
        by_cases Hleaf : la = null ∧ lb = null ∧ lc = null
        · -- no children: the node is returned unchanged
          obtain ⟨Ea, Eb, Ec⟩ := Hleaf
          subst Ea Eb Ec
          wp_auto
          iapply HΦ
          iframe Hsub
          rw [show oinstantiate_t (some x) σ oret = instantiate_t x σ oret from rfl,
            instantiate_leaf x σ oret Hp Hr (Hna.mp rfl) (Hnb.mp rfl) (Hnc.mp rfl),
            is_oterm_some]
          iexact Hox
        -- the node has at least one child: rebuild it
        have Hch : term_a x ≠ none ∨ term_b x ≠ none ∨ term_c x ≠ none := by
          apply Hrebuild
          by_cases h1 : la = null <;> by_cases h2 : lb = null <;> simp_all
        wp_if_destruct <;> (try wp_if_destruct) <;> (try wp_if_destruct)
        all_goals try (exfalso; simp_all; done)
        all_goals
          wp_apply IH $$ %_ %(term_a x) [Hsub] as %l2 ⟨Hsub, #Hia⟩
          · iframe Hsub; iframe #; ipureintro; exact inst_wf_o_a _ _ Hwf'
          wp_apply IH $$ %_ %(term_b x) [Hsub] as %l3 ⟨Hsub, #Hib⟩
          · iframe Hsub; iframe #; ipureintro; exact inst_wf_o_b _ _ Hwf'
          wp_apply IH $$ %_ %(term_c x) [Hsub] as %l4 ⟨Hsub, #Hic⟩
          · iframe Hsub; iframe #; ipureintro; exact inst_wf_o_c _ _ Hwf'
          wp_alloc lz as Hl
          ipersist Hl
          wp_auto
          iapply HΦ
          iframe Hsub
          rw [show oinstantiate_t (some x) σ oret = instantiate_t x σ oret from rfl]
          iapply (is_oterm_rebuild lz x l2 l3 l4 σ oret Hwf' Hch) $$ [] Hia Hib Hic
          iExactEq Hl; rfl
      · -- `t.Kind == TResult`: return `ret`
        obtain rfl : x = TResult := by cases x <;> simp_all [is_tresult]
        wp_auto
        iapply HΦ
        simp only [oinstantiate_t, instantiate_t]
        iframe Hsub Hor
    · -- `t.Kind == TPat`: look the index up in `subst`
      obtain ⟨m, rfl⟩ : ∃ m, x = TPat m := by cases x <;> simp_all [is_tpat]
      simp only [term_code, term_num, term_a, term_b, term_c, term_idx_wf] at *
      unfold is_subst
      icases Hsub with ⟨%ls, Hs, #Hls⟩
      ihave %Hlen2 := BigSepL2.bigSepL2_length $$ Hls
      ihave %Hlen := ownSlice_len _ _ _ $$ Hs
      wp_auto
      wp_if_destruct
      · -- the index is in range
        have Hb : 0 ≤ sint.Z (W64 m) ∧ sint.Z (W64 m) < sint.Z s.len := by
          unfold idx_wf at Hw; word
        have Hsn : sint.nat (W64 m) = m := by unfold idx_wf at Hw; word
        rw [ite_eq_left Hb]
        list_elem ls (sint.nat (W64 m)) as li
        list_elem σ (sint.nat (W64 m)) as oi
        ihave #Hli := BigSepL2.bigSepL2_lookup (Φ := fun _ li oi => is_oterm (GF := GF) li oi)
          Hli_lookup Hoi_lookup $$ Hls
        ihave %Hlin := is_oterm_null _ _ $$ Hli
        wp_apply wp_load_slice_index s (sint.Z (W64 m)) ls _ li Hb.1 $$ [Hs] with Hs
        · iframe Hs; ipureintro; exact Hli_lookup
        rw [Hsn] at Hoi_lookup
        wp_if_destruct
        · -- `subst[n]` is nil: the pattern variable is unbound
          obtain rfl : oi = none := Hlin.mp rfl
          iapply HΦ
          simp only [oinstantiate_t, instantiate_t, Hoi_lookup, is_oterm]
          iframe Hox
          iexists ls; iframe Hs Hls
        · -- `subst[n]` is non-nil: return it
          cases oi with
          | none => exact absurd (Hlin.mpr rfl) Hif
          | some y =>
          rw [ite_eq_left Hb]
          wp_apply wp_load_slice_index s (sint.Z (W64 m)) ls _ li Hb.1 $$ [Hs] with Hs
          · iframe Hs; ipureintro; exact Hli_lookup
          wp_auto
          iapply HΦ
          simp only [oinstantiate_t, instantiate_t, Hoi_lookup, is_oterm]
          iframe Hli
          iexists ls; iframe Hs Hls
      · -- the index is out of range
        have Hoob : σ[m]? = none := by
          apply List.getElem?_eq_none; unfold idx_wf at Hw; word
        iapply HΦ
        simp only [oinstantiate_t, instantiate_t, Hoob, is_oterm]
        iframe Hox
        iexists ls; iframe Hs Hls

/-- The side condition is vacuous whenever `ret` is a real term, which is the
case at every call site (`is_path` describes `p.Ret` with `is_term`). -/
theorem wp_instantiate_ret (lx : Loc) (s : GoSlice) (lr : Loc)
    (ox : Option term) (σ : List (Option term)) (rt : term) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_oterm lx ox ∗ is_subst s σ ∗
        is_term lr rt }}
      (App (App (App (Val (@! checker.instantiate)) (Val #lx)) (Val #s)) (Val #lr))
    {{ (l : Loc), RET #l; is_subst s σ ∗ is_oterm l (oinstantiate_t ox σ (some rt)) }} := by
  iintro %Φ ⟨#Hpkg, #Hox, Hsub, #Hor⟩ HΦ
  iapply (wp_instantiate lx s lr ox σ (some rt)) $$ [Hsub] HΦ
  iframe Hsub
  rw [is_oterm_some]
  iframe #
  ipureintro
  cases ox <;> simp [inst_wf_o, inst_wf]

end proof

end Checker
end Perennial
