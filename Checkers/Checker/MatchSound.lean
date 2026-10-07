/-
Port of `new/checker/match_sound.v`.

Soundness of the postcondition matcher (checker/match.go), on Lean
mirrors.

The Go specifications of `matchTerm`, `matchAtom`, `matchPass`,
`matchHeap`, `checkSorts` and `checkPure` (new/checker/fn/) report what
happened as the relations and predicates defined here; this file proves,
once and without any Go in sight, that a successful run of all three
phases gives `path_sat_dj`.

The pure part lives outside any section with Iris context (see NOTES.md,
"Set Default Proof Using All poisons pure lemmas").

Lean notes:
* `<[n := v]> σ` is `σ.set n v`; `l !!! j` is `l[j]!` (with the
  `Inhabited scell` instance of Interp.lean); `seq 0 n` is `List.range n`.
* Rocq imports `fn/findCell` here without using it; this file does not.
* `has_pat_node` and `term_eq_iff` are reused from Fn/hasPat.lean and
  Fn/termEq.lean (pure there, unlike in Rocq), so Rocq's `has_pat_node'`,
  `tcode_nat`, `w64_nat`, `tcode_nat_code` are replaced by a direct use of
  `term_eq_iff` in `term_eq_nodes`.
* `big_sepL_seq_lookup` is stated over `List.range`.
-/
import Checkers.Checker.Prelude
import Checkers.Checker.Nodes
import Checkers.Checker.Disjunct
import Checkers.Checker.VerifyDef
import Checkers.Checker.Fn.instantiate
import Checkers.Checker.Fn.hasPat
import Checkers.Checker.Fn.condHolds
import Checkers.Checker.Fn.termEq

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode
open github_com.upamanyus.bootstrap_go

/-! ## Substitutions -/

/-- `σ'` extends `σ`: every bound entry stays bound to the same term. -/
def subst_ext (σ σ' : List (Option term)) : Prop :=
  ∀ (n : Nat) (y : term), σ[n]? = some (some y) → σ'[n]? = some (some y)

theorem subst_ext_refl (σ : List (Option term)) : subst_ext σ σ := fun _ _ h => h

theorem subst_ext_trans (σ1 σ2 σ3 : List (Option term)) :
    subst_ext σ1 σ2 → subst_ext σ2 σ3 → subst_ext σ1 σ3 :=
  fun H1 H2 n y Hn => H2 n y (H1 n y Hn)

/-- Every bound entry is at a declared pattern variable and is a term of that
variable's declared sort, under the path's sort table `PV`. -/
def subst_wf (pats : List sort) (pok : List Bool) (PV : List sort)
    (σ : List (Option term)) : Prop :=
  ∀ (n : Nat) (y : term), σ[n]? = some (some y) →
    pok[n]? = some true ∧ ∃ s, pats[n]? = some s ∧ sort_of_vars PV y = some s

theorem subst_wf_empty (pats : List sort) (pok : List Bool) (PV : List sort) (k : Nat) :
    subst_wf pats pok PV (List.replicate k none) := by
  intro n y Hn
  simp [List.getElem?_replicate] at Hn

/-! ## `matchTerm`, as a relation

One constructor per way the Go function can return `nil`. The `TResult`
case matches the path's return term `r` in place of the pattern, which is
not a subterm, so this is a relation rather than a structurally recursive
function; a derivation is finite even when the Go recursion would not be. -/
inductive match_rel (pats : List sort) (pok : List Bool) (PV : List sort) (r : term) :
    Option term → Option term → List (Option term) → List (Option term) → Prop where
  | MR_nil (σ : List (Option term)) : match_rel pats pok PV r none none σ σ
  | MR_pat_new (n : Nat) (y : term) (s : sort) (σ : List (Option term)) :
      σ[n]? = some none → pok[n]? = some true → pats[n]? = some s →
      sort_of_vars PV y = some s →
      match_rel pats pok PV r (some (TPat n)) (some y) σ (σ.set n (some y))
  | MR_pat_old (n : Nat) (y : term) (σ : List (Option term)) :
      σ[n]? = some (some y) → pok[n]? = some true →
      match_rel pats pok PV r (some (TPat n)) (some y) σ σ
  | MR_result (oy : Option term) (σ σ' : List (Option term)) :
      match_rel pats pok PV r (some r) oy σ σ' →
      match_rel pats pok PV r (some TResult) oy σ σ'
  | MR_node (x y : term) (σ σ1 σ2 σ3 : List (Option term)) :
      is_tpat x = false → is_tresult x = false →
      term_code x = term_code y → term_num x = term_num y →
      term_idx_wf x → term_idx_wf y →
      match_rel pats pok PV r (term_a x) (term_a y) σ σ1 →
      match_rel pats pok PV r (term_b x) (term_b y) σ1 σ2 →
      match_rel pats pok PV r (term_c x) (term_c y) σ2 σ3 →
      match_rel pats pok PV r (some x) (some y) σ σ3

export match_rel (MR_nil MR_pat_new MR_pat_old MR_result MR_node)

theorem match_rel_ext {pats pok PV r ox oy σ σ'} :
    match_rel pats pok PV r ox oy σ σ' → subst_ext σ σ' := by
  intro H
  induction H with
  | MR_nil σ => exact subst_ext_refl σ
  | MR_pat_new n y s σ Hn _ _ _ =>
    intro m z Hm
    have : m ≠ n := by rintro rfl; rw [Hn] at Hm; cases Hm
    rw [List.getElem?_set_ne (Ne.symm this)]; exact Hm
  | MR_pat_old => exact subst_ext_refl _
  | MR_result _ _ _ _ ih => exact ih
  | MR_node _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ iha ihb ihc =>
    exact subst_ext_trans _ _ _ (subst_ext_trans _ _ _ iha ihb) ihc

theorem match_rel_wf {pats pok PV r ox oy σ σ'} :
    match_rel pats pok PV r ox oy σ σ' → subst_wf pats pok PV σ → subst_wf pats pok PV σ' := by
  intro H
  induction H with
  | MR_nil σ => exact id
  | MR_pat_new n y s σ Hn Hok Hs Hy =>
    intro Hwf m z Hm
    by_cases Hmn : m = n
    · subst Hmn
      have Hlt : m < σ.length := (List.getElem?_eq_some_iff.mp Hn).1
      rw [List.getElem?_set_self Hlt] at Hm
      cases Hm
      exact ⟨Hok, s, Hs, Hy⟩
    · rw [List.getElem?_set_ne (Ne.symm Hmn)] at Hm
      exact Hwf m z Hm
  | MR_pat_old => exact id
  | MR_result _ _ _ _ ih => exact ih
  | MR_node _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ iha ihb ihc =>
    exact fun h => ihc (ihb (iha h))

theorem match_rel_len {pats pok PV r ox oy σ σ'} :
    match_rel pats pok PV r ox oy σ σ' → σ'.length = σ.length := by
  intro H
  induction H with
  | MR_nil => rfl
  | MR_pat_new => exact List.length_set
  | MR_pat_old => rfl
  | MR_result _ _ _ _ ih => exact ih
  | MR_node _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ iha ihb ihc => rw [ihc, ihb, iha]

/-! ## `instantiate` -/

theorem tbind1_eq_some (f : term → term) (oa : Option term) (y : term) :
    tbind1 f oa = some y → ∃ a, oa = some a ∧ y = f a := by
  cases oa <;> simp [tbind1, eq_comm]
theorem tbind2_eq_some (f : term → term → term) (oa ob : Option term) (y : term) :
    tbind2 f oa ob = some y → ∃ a b, oa = some a ∧ ob = some b ∧ y = f a b := by
  cases oa <;> cases ob <;> simp [tbind2, eq_comm]
theorem tbind3_eq_some (f : term → term → term → term) (oa ob oc : Option term) (y : term) :
    tbind3 f oa ob oc = some y → ∃ a b c, oa = some a ∧ ob = some b ∧ oc = some c ∧ y = f a b c := by
  cases oa <;> cases ob <;> cases oc <;> simp [tbind3, eq_comm]

/-- A result without pattern variables survives extending the substitution. -/
theorem inst_ext (x : term) (σ σ' : List (Option term)) (r : Option term) (y : term) :
    subst_ext σ σ' → instantiate_t x σ r = some y → has_pat y = false →
    instantiate_t x σ' r = some y := by
  intro Hext
  induction x generalizing y with
  | TPat n =>
    intro Hi Hp
    simp only [instantiate_t] at Hi ⊢
    cases Hn : σ[n]? with
    | none => rw [Hn] at Hi; cases Hi; simp [has_pat] at Hp
    | some o =>
      cases o with
      | none => rw [Hn] at Hi; cases Hi; simp [has_pat] at Hp
      | some z => rw [Hn] at Hi; cases Hi; rw [Hext n _ Hn]
  | TPlus p q ihp ihq | TMinus p q ihp ihq | TMul p q ihp ihq | TEq p q ihp ihq
  | TLt _ p q ihp ihq | TLe _ p q ihp ihq =>
    intro Hi Hp
    simp only [instantiate_t] at Hi ⊢
    obtain ⟨a, b, Ha, Hb, rfl⟩ := tbind2_eq_some _ _ _ _ Hi
    simp only [has_pat, Bool.or_eq_false_iff] at Hp
    rw [ihp a Ha Hp.1, ihq b Hb Hp.2]; rfl
  | TNeg p ihp | TNot p ihp | TRet p ihp =>
    intro Hi Hp
    simp only [instantiate_t] at Hi ⊢
    obtain ⟨a, Ha, rfl⟩ := tbind1_eq_some _ _ _ Hi
    simp only [has_pat] at Hp
    rw [ihp a Ha Hp]; rfl
  | TIte p q z ihp ihq ihz =>
    intro Hi Hp
    simp only [instantiate_t] at Hi ⊢
    obtain ⟨a, b, c, Ha, Hb, Hc, rfl⟩ := tbind3_eq_some _ _ _ _ _ Hi
    simp only [has_pat, Bool.or_eq_false_iff] at Hp
    rw [ihp a Ha Hp.1.1, ihq b Hb Hp.1.2, ihz c Hc Hp.2]; rfl
  | _ => intro Hi _; simpa only [instantiate_t] using Hi

/-- A term without pattern variables and `ret` is its own instance. -/
theorem inst_nopat (x : term) (σ : List (Option term)) (r : Option term) :
    has_pat x = false → has_result x = false → instantiate_t x σ r = some x := by
  induction x <;> simp_all [instantiate_t, has_pat, has_result, tbind1, tbind2, tbind3]

/-- The node view of `instantiate` on a node that is neither `TPat` nor
`TResult`. -/
theorem inst_node (x : term) (σ : List (Option term)) (r : Option term) (y : term) :
    is_tpat x = false → is_tresult x = false → instantiate_t x σ r = some y →
    term_code y = term_code x ∧ term_num y = term_num x ∧
    term_a y = oinstantiate_t (term_a x) σ r ∧ term_b y = oinstantiate_t (term_b x) σ r ∧
    term_c y = oinstantiate_t (term_c x) σ r ∧ (term_idx_wf x → term_idx_wf y) := by
  intro Hp Hr Hi
  cases x with
  | TPat => simp [is_tpat] at Hp
  | TResult => simp [is_tresult] at Hr
  | TPlus p q | TMinus p q | TMul p q | TEq p q | TLt _ p q | TLe _ p q =>
    simp only [instantiate_t] at Hi
    obtain ⟨a, b, Ha, Hb, rfl⟩ := tbind2_eq_some _ _ _ _ Hi
    simp [term_code, term_num, term_a, term_b, term_c, oinstantiate_t, Ha, Hb, term_idx_wf]
  | TNeg p | TNot p | TRet p =>
    simp only [instantiate_t] at Hi
    obtain ⟨a, Ha, rfl⟩ := tbind1_eq_some _ _ _ Hi
    simp [term_code, term_num, term_a, term_b, term_c, oinstantiate_t, Ha, term_idx_wf]
  | TIte p q z =>
    simp only [instantiate_t] at Hi
    obtain ⟨a, b, c, Ha, Hb, Hc, rfl⟩ := tbind3_eq_some _ _ _ _ _ Hi
    simp [term_code, term_num, term_a, term_b, term_c, oinstantiate_t, Ha, Hb, Hc, term_idx_wf]
  | _ =>
    simp only [instantiate_t, Option.some.injEq] at Hi; subst Hi
    simp [oinstantiate_t, term_a, term_b, term_c]

theorem term_eq_nodes (x y : term) :
    term_idx_wf x → term_idx_wf y →
    term_code x = term_code y → term_num x = term_num y →
    term_a x = term_a y → term_b x = term_b y → term_c x = term_c y → x = y := by
  intro Hwx Hwy Hc Hn Ha Hb Hc2
  exact (term_eq_iff x y Hwx Hwy).mpr ⟨Hc, Hn, Ha, Hb, Hc2⟩

/-! ## What a successful `matchTerm` establishes -/

theorem has_pat_node' (x : term) :
    has_pat x = false →
    ohas_pat (term_a x) = false ∧ ohas_pat (term_b x) = false ∧ ohas_pat (term_c x) = false := by
  rw [has_pat_node]; simp only [Bool.or_eq_false_iff]
  intro ⟨⟨⟨_, a⟩, b⟩, c⟩; exact ⟨a, b, c⟩

theorem oinst_ext (ox oy : Option term) (σ σ' : List (Option term)) (r : term) :
    subst_ext σ σ' → oinstantiate_t ox σ (some r) = oy → ohas_pat oy = false →
    oinstantiate_t ox σ' (some r) = oy := by
  intro Hext Hi Hp
  cases ox with
  | none => exact Hi
  | some p =>
    cases oy with
    | none =>
      obtain ⟨_, E⟩ := inst_Some_r p σ (some r) rfl
      simp only [oinstantiate_t] at Hi; rw [E] at Hi; cases Hi
    | some q => exact inst_ext p σ σ' (some r) q Hext Hi Hp

/-- When the actual term has no pattern variables (every path term), the
pattern instantiated with the final substitution *is* the actual term. -/
theorem match_rel_inst {pats pok PV r ox oy σ σ'} :
    match_rel pats pok PV r ox oy σ σ' →
    has_pat r = false → has_result r = false → ohas_pat oy = false →
    oinstantiate_t ox σ' (some r) = oy := by
  intro Hm Hpr Hrr
  induction Hm with
  | MR_nil => intro _; rfl
  | MR_pat_new n y s σ Hn _ _ _ =>
    intro _
    have Hlt : n < σ.length := (List.getElem?_eq_some_iff.mp Hn).1
    simp [oinstantiate_t, instantiate_t, List.getElem?_set_self Hlt]
  | MR_pat_old n y σ Hn _ =>
    intro _
    simp [oinstantiate_t, instantiate_t, Hn]
  | MR_result oy σ σ' _ ih =>
    intro Hpy
    have := ih Hpy
    simp only [oinstantiate_t, inst_nopat r σ' _ Hpr Hrr] at this
    simp only [oinstantiate_t, instantiate_t]; exact this
  | MR_node x y σ σ1 σ2 σ3 Hp Hr Hc Hnum Hwx Hwy Hma Hmb Hmc iha ihb ihc =>
    intro Hpy
    simp only [ohas_pat] at Hpy
    obtain ⟨Hpa, Hpb, Hpc⟩ := has_pat_node' y Hpy
    have E12 := match_rel_ext Hmb
    have E23 := match_rel_ext Hmc
    obtain ⟨x', Hx'⟩ := inst_Some_r x σ3 (some r) rfl
    obtain ⟨Hc', Hn', Ha', Hb', Hc'', Hw'⟩ := inst_node x σ3 (some r) x' Hp Hr Hx'
    simp only [oinstantiate_t]
    rw [Hx']
    congr 1
    apply term_eq_nodes x' y (Hw' Hwx) Hwy (Hc'.trans Hc) (Hn'.trans Hnum)
    · rw [Ha']; exact oinst_ext _ _ _ _ r (subst_ext_trans _ _ _ E12 E23) (iha Hpa) Hpa
    · rw [Hb']; exact oinst_ext _ _ _ _ r E23 (ihb Hpb) Hpb
    · rw [Hc'']; exact ihc Hpc

/-! ## Scoping -/

/-- Like `vars_below`, but for a postcondition's terms, which may mention
pattern variables and `ret`. -/
def pvars_below (k : Nat) : term → Prop
  | TVar n => n < k
  | TPat _ | TResult | TInt _ | TBool _ | TUnit | TNull | TExec => True
  | TPlus a b | TMinus a b | TMul a b | TEq a b | TLt _ a b | TLe _ a b =>
      pvars_below k a ∧ pvars_below k b
  | TNeg a | TNot a | TRet a => pvars_below k a
  | TIte c a b => pvars_below k c ∧ pvars_below k a ∧ pvars_below k b

/-- A sorted node has sorted children. -/
theorem sort_of_children (E : sort_env) (t : term) (s : sort) :
    sort_of E t = some s →
    (∀ c, term_a t = some c → ∃ s', sort_of E c = some s') ∧
    (∀ c, term_b t = some c → ∃ s', sort_of E c = some s') ∧
    (∀ c, term_c t = some c → ∃ s', sort_of E c = some s') := by
  intro Hs
  cases t <;> simp only [sort_of] at Hs <;> (repeat' split at Hs) <;>
    simp_all [term_a, term_b, term_c]

/-- A term `sortOfEnv` accepts mentions only the logical variables in the
environment's table. -/
theorem sort_of_pvars (E : sort_env) (t : term) (s : sort) :
    sort_of E t = some s → pvars_below (se_vars E).length t := by
  induction t generalizing s with
  | TVar n =>
    intro Hs; simp only [sort_of] at Hs
    exact (List.getElem?_eq_some_iff.mp Hs).1
  | TPlus a b iha ihb | TMinus a b iha ihb | TMul a b iha ihb | TEq a b iha ihb
  | TLt _ a b iha ihb | TLe _ a b iha ihb =>
    intro Hs
    obtain ⟨Ha, Hb, _⟩ := sort_of_children E _ s Hs
    obtain ⟨sa, Hsa⟩ := Ha a rfl
    obtain ⟨sb, Hsb⟩ := Hb b rfl
    exact ⟨iha sa Hsa, ihb sb Hsb⟩
  | TNeg a iha | TNot a iha | TRet a iha =>
    intro Hs
    obtain ⟨Ha, _, _⟩ := sort_of_children E _ s Hs
    obtain ⟨sa, Hsa⟩ := Ha a rfl
    exact iha sa Hsa
  | TIte c a b ihc iha ihb =>
    intro Hs
    obtain ⟨Hc, Ha, Hb⟩ := sort_of_children E _ s Hs
    obtain ⟨sc, Hsc⟩ := Hc c rfl
    obtain ⟨sa, Hsa⟩ := Ha a rfl
    obtain ⟨sb, Hsb⟩ := Hb b rfl
    exact ⟨ihc sc Hsc, iha sa Hsa, ihb sb Hsb⟩
  | _ => intro _; trivial

theorem vars_below_nopat (k : Nat) (t : term) :
    vars_below k t → has_pat t = false ∧ has_result t = false := by
  induction t <;> simp_all [vars_below, has_pat, has_result]

/-- An atom of a well-sorted disjunct: a pure or points-to atom whose terms
mention only logical variables below `k`. -/
def atom_scoped (k : Nat) : cassn → Prop
  | CAPure x => pvars_below k x
  | CAPointsTo x v => pvars_below k x ∧ pvars_below k v
  | _ => False

/-! ## Phase 1: the points-to atoms -/

def is_pts : cassn → Bool
  | CAPointsTo _ _ => true
  | _ => false
def is_pure : cassn → Bool
  | CAPure _ => true
  | _ => false

theorem is_pts_inv (a : cassn) : is_pts a = true → ∃ x v, a = CAPointsTo x v := by
  cases a <;> simp [is_pts]
theorem is_pure_inv (a : cassn) : is_pure a = true → ∃ x, a = CAPure x := by
  cases a <;> simp [is_pure]

/-- What one successful `matchAtom` on the points-to atom `x ↦ v` did: either
nothing (its location is not resolved yet), or it claimed a free cell
whose location is the instantiated `x`, and matched `v` against the
cell's value. -/
def atom_step (H : List scell) (pats : List sort) (pok : List Bool)
    (PV : List sort) (r : term) (x v : term)
    (σ : List (Option term)) (used : List Bool) (ok : Bool)
    (σ' : List (Option term)) (used' : List Bool) : Prop :=
  (ok = false ∧ σ' = σ ∧ used' = used) ∨
  (ok = true ∧ ∃ (j : Nat) (c : scell),
     instantiate_t x σ (some r) = some (cloc c) ∧ has_pat (cloc c) = false ∧
     H[j]? = some c ∧ used[j]? = some false ∧ used' = used.set j true ∧
     match_rel pats pok PV r (some v) (some (cval c)) σ σ')

/-- The invariant of phase 1: each resolved atom `i` owns the cell `f i`
(distinct atoms, distinct cells, all marked used), whose location is the
atom's instantiated location and whose value its value matched. -/
structure phase1_inv (H : List scell) (atoms : List cassn) (pats : List sort)
    (pok : List Bool) (PV : List sort) (r : term)
    (σ : List (Option term)) (used done : List Bool) : Prop where
  p1_len_σ : σ.length = pats.length
  p1_len_used : used.length = H.length
  p1_len_done : done.length = atoms.length
  p1_wf : subst_wf pats pok PV σ
  p1_map : ∃ f : Nat → Nat,
    (∀ i, done[i]? = some true →
       ∃ x v c σ0 σ1,
         atoms[i]? = some (CAPointsTo x v) ∧ H[f i]? = some c ∧
         used[f i]? = some true ∧
         instantiate_t x σ0 (some r) = some (cloc c) ∧ has_pat (cloc c) = false ∧
         match_rel pats pok PV r (some v) (some (cval c)) σ0 σ1 ∧ subst_ext σ1 σ) ∧
    (∀ i i', done[i]? = some true → done[i']? = some true → f i = f i' → i = i')

theorem phase1_inv_init (H : List scell) (atoms : List cassn) (pats : List sort)
    (pok : List Bool) (PV : List sort) (r : term) :
    phase1_inv H atoms pats pok PV r
      (List.replicate pats.length none) (List.replicate H.length false)
      (List.replicate atoms.length false) := by
  refine ⟨List.length_replicate, List.length_replicate, List.length_replicate,
    subst_wf_empty _ _ _ _, id, ?_, ?_⟩
  · intro i Hi; simp [List.getElem?_replicate] at Hi
  · intro i _ Hi; simp [List.getElem?_replicate] at Hi

theorem phase1_inv_skip {H atoms pats pok PV r x v σ used done σ' used'} :
    phase1_inv H atoms pats pok PV r σ used done →
    atom_step H pats pok PV r x v σ used false σ' used' →
    phase1_inv H atoms pats pok PV r σ' used' done := by
  rintro Hi (⟨_, rfl, rfl⟩ | ⟨h, _⟩)
  · exact Hi
  · cases h

theorem phase1_inv_step {H atoms pats pok PV r x v σ used done σ' used'} (i : Nat) :
    phase1_inv H atoms pats pok PV r σ used done →
    atoms[i]? = some (CAPointsTo x v) → done[i]? = some false →
    atom_step H pats pok PV r x v σ used true σ' used' →
    phase1_inv H atoms pats pok PV r σ' used' (done.set i true) := by
  rintro ⟨Hlσ, Hlu, Hld, Hwf, f, Hf, Hinj⟩ Hat Hdi
    (⟨h, _⟩ | ⟨_, j, c, Hx, Hpx, Hj, Huj, rfl, Hm⟩)
  · cases h
  have Hext := match_rel_ext Hm
  have Hilt : i < done.length := (List.getElem?_eq_some_iff.mp Hdi).1
  have Hjlt : j < used.length := (List.getElem?_eq_some_iff.mp Huj).1
  -- a resolved atom's cell is used, so it is not `j`
  have Hne : ∀ i', done[i']? = some true → f i' ≠ j := by
    intro i' Hi' Heq
    obtain ⟨_, _, _, _, _, _, _, Hu, _⟩ := Hf i' Hi'
    rw [Heq, Huj] at Hu; cases Hu
  refine ⟨(match_rel_len Hm).trans Hlσ, by rw [List.length_set]; exact Hlu,
    by rw [List.length_set]; exact Hld, match_rel_wf Hm Hwf,
    fun i' => if i' = i then j else f i', ?_, ?_⟩
  · intro i' Hi'
    by_cases Hii : i' = i
    · subst Hii
      refine ⟨x, v, c, σ, σ', Hat, by simp [Hj], ?_, Hx, Hpx, Hm, subst_ext_refl _⟩
      simp [List.getElem?_set_self Hjlt]
    · rw [List.getElem?_set_ne (Ne.symm Hii)] at Hi'
      obtain ⟨x', v', c', σ0, σ1, H1, H2, H3, H4, H5, H6, H7⟩ := Hf i' Hi'
      refine ⟨x', v', c', σ0, σ1, H1, by simp [Hii, H2], ?_, H4, H5, H6,
        subst_ext_trans _ _ _ H7 Hext⟩
      simp only [Hii, ↓reduceIte]
      rw [List.getElem?_set_ne (Hne i' Hi').symm]; exact H3
  · intro i1 i2 Hi1 Hi2
    by_cases H1 : i1 = i <;> by_cases H2 : i2 = i <;> simp only [H1, H2, ↓reduceIte]
    · intro _; trivial
    · rw [List.getElem?_set_ne (Ne.symm H2)] at Hi2
      intro Heq; exact absurd Heq.symm (Hne i2 Hi2)
    · rw [List.getElem?_set_ne (Ne.symm H1)] at Hi1
      intro Heq; exact absurd Heq (Hne i1 Hi1)
    · rw [List.getElem?_set_ne (Ne.symm H1)] at Hi1
      rw [List.getElem?_set_ne (Ne.symm H2)] at Hi2
      exact Hinj i1 i2 Hi1 Hi2

/-- The number of points-to atoms not resolved yet: `remaining` in
`matchHeap`. -/
def undone : List cassn → List Bool → Nat
  | a :: atoms', d :: done' => (if is_pts a && !d then 1 else 0) + undone atoms' done'
  | _, _ => 0

/-- Mirrors `countPointsTo`. -/
def count_pts : List cassn → Nat
  | [] => 0
  | a :: atoms' => (if is_pts a then 1 else 0) + count_pts atoms'

theorem count_pts_app (l1 l2 : List cassn) :
    count_pts (l1 ++ l2) = count_pts l1 + count_pts l2 := by
  induction l1 with
  | nil => simp [count_pts]
  | cons a l1 ih => simp only [List.cons_append, count_pts, ih]; omega

theorem count_pts_undone (atoms : List cassn) :
    count_pts atoms = undone atoms (List.replicate atoms.length false) := by
  induction atoms with
  | nil => rfl
  | cons a atoms ih =>
    simp only [count_pts, List.length_cons, List.replicate_succ, undone, ih, Bool.not_false,
      Bool.and_true]

theorem undone_le (atoms : List cassn) (done : List Bool) : undone atoms done ≤ atoms.length := by
  induction atoms generalizing done with
  | nil => cases done <;> simp [undone]
  | cons a atoms ih =>
    cases done with
    | nil => simp [undone]
    | cons d done =>
      have := ih done
      simp only [undone, List.length_cons]; split <;> omega

theorem undone_insert (atoms : List cassn) (done : List Bool) (i : Nat) (x v : term) :
    atoms[i]? = some (CAPointsTo x v) → done[i]? = some false →
    undone atoms (done.set i true) + 1 = undone atoms done := by
  induction atoms generalizing done i with
  | nil => intro Ha; simp at Ha
  | cons a atoms ih =>
    cases done with
    | nil => intro _ Hd; simp at Hd
    | cons d done =>
      cases i with
      | zero =>
        intro Ha Hd
        simp only [List.getElem?_cons_zero, Option.some.injEq] at Ha Hd
        subst Ha Hd
        simp [undone, is_pts]; omega
      | succ i =>
        intro Ha Hd
        simp only [List.getElem?_cons_succ] at Ha Hd
        have := ih done i Ha Hd
        simp only [List.set_cons_succ, undone]; omega

theorem undone_zero (atoms : List cassn) (done : List Bool) (i : Nat) (x v : term) :
    done.length = atoms.length → undone atoms done = 0 →
    atoms[i]? = some (CAPointsTo x v) → done[i]? = some true := by
  induction atoms generalizing done i with
  | nil => intro _ _ Ha; simp at Ha
  | cons a atoms ih =>
    cases done with
    | nil => intro Hl; simp at Hl
    | cons d done =>
      intro Hl Hu Ha
      simp only [undone] at Hu
      cases i with
      | zero =>
        simp only [List.getElem?_cons_zero, Option.some.injEq] at Ha ⊢
        subst Ha
        cases d <;> simp_all [is_pts]
      | succ i =>
        simp only [List.getElem?_cons_succ] at Ha ⊢
        exact ih done i (by simpa using Hl) (by omega) Ha

/-! ## Phase 2: the pure atoms -/

/-- What a successful `checkPure` established. -/
def pure_ok (pc : List term) (atoms : List cassn) (σ : List (Option term)) (r : term) : Prop :=
  ∀ (i : Nat) (x : term), atoms[i]? = some (CAPure x) →
    ∃ y, instantiate_t x σ (some r) = some y ∧ has_pat y = false ∧
         cond_holds pc (some y) = true

/-! ## Evaluation -/

section teval
variable [ext : FfiSyntax]

/-- Instantiating is substitution: evaluating a pattern under a valuation
that sends each bound pattern variable to the value of its term, and
`ret` to the value of the return term, gives the value of the instance. -/
theorem inst_teval (θ W : Nat → val) (V' : valuation) (r : term) (σ : List (Option term))
    (k : Nat) :
    (∀ n, n < k → θ n = vvar V' n) →
    (∀ n y, σ[n]? = some (some y) → W n = teval V' y) →
    ∀ x y, pvars_below k x → instantiate_t x σ (some r) = some y → has_pat y = false →
    teval (mkVal θ W (teval V' r)) x = teval V' y := by
  intro Hθ HW x
  induction x with
  | TVar n =>
    intro y Hb Hi _
    simp only [instantiate_t, Option.some.injEq] at Hi; subst Hi
    exact Hθ n Hb
  | TPat n =>
    intro y _ Hi Hp
    simp only [instantiate_t, Option.some.injEq] at Hi
    cases Hn : σ[n]? with
    | none => rw [Hn] at Hi; subst Hi; simp [has_pat] at Hp
    | some o =>
      cases o with
      | none => rw [Hn] at Hi; subst Hi; simp [has_pat] at Hp
      | some z => rw [Hn] at Hi; subst Hi; exact HW n z Hn
  | TResult =>
    intro y _ Hi _
    simp only [instantiate_t, Option.some.injEq] at Hi; subst Hi; rfl
  | TPlus p q ihp ihq | TMinus p q ihp ihq | TMul p q ihp ihq | TEq p q ihp ihq
  | TLt _ p q ihp ihq | TLe _ p q ihp ihq =>
    intro y Hb Hi Hp
    simp only [instantiate_t] at Hi
    obtain ⟨a, b, Ha, Hb', rfl⟩ := tbind2_eq_some _ _ _ _ Hi
    simp only [has_pat, Bool.or_eq_false_iff] at Hp
    simp only [teval, ihp a Hb.1 Ha Hp.1, ihq b Hb.2 Hb' Hp.2]
  | TNeg p ihp | TNot p ihp | TRet p ihp =>
    intro y Hb Hi Hp
    simp only [instantiate_t] at Hi
    obtain ⟨a, Ha, rfl⟩ := tbind1_eq_some _ _ _ Hi
    simp only [has_pat] at Hp
    simp only [teval, ihp a Hb Ha Hp]
  | TIte c p q ihc ihp ihq =>
    intro y Hb Hi Hp
    simp only [instantiate_t] at Hi
    obtain ⟨a1, a2, a3, Ha1, Ha2, Ha3, rfl⟩ := tbind3_eq_some _ _ _ _ _ Hi
    simp only [has_pat, Bool.or_eq_false_iff] at Hp
    simp only [teval, ihc a1 Hb.1 Ha1 Hp.1.1, ihp a2 Hb.2.1 Ha2 Hp.1.2, ihq a3 Hb.2.2 Ha3 Hp.2]
  | _ =>
    intro y _ Hi _
    simp only [instantiate_t, Option.some.injEq] at Hi; subst Hi; rfl

/-- A default value of each sort, for the declared pattern variables that
phase 1 left unbound (they occur in no atom, or phase 2 would have
failed). -/
def sort_default : sort → val
  | SInt => ival (W64 0)
  | SBool => bval false
  | SLoc => lval null
  | SUnit => uval

theorem sort_default_has_sort (s : sort) : has_sort (sort_default s) s := by
  cases s <;> simp only [has_sort, sort_default] <;> first | rfl | exact ⟨_, rfl⟩

/-- The witnesses for the disjunct's `∃`s. -/
def pat_witness (V' : valuation) (σ : List (Option term)) (pats : List sort)
    (pok : List Bool) (n : Nat) : val :=
  match σ[n]? with
  | some (some y) => teval V' y
  | _ => match pok[n]?, pats[n]? with
         | some true, some s => sort_default s
         | _, _ => uval

/-- The facts `condHolds` accepts are true. -/
theorem cond_holds_sound (V : valuation) (pc : List term) (y : term) :
    pc_sat V pc → cond_holds pc (some y) = true → teval V y = bval true := by
  intro Hpc
  simp only [cond_holds, Bool.or_eq_true, decide_eq_true_eq]
  rintro (Hin | Hr)
  · exact Hpc y Hin
  · cases y with
    | TBool b => simp only [cond_refl] at Hr; subst Hr; rfl
    | TEq p q => simp only [cond_refl, decide_eq_true_eq] at Hr; subst Hr; simp [teval]
    | _ => simp [cond_refl] at Hr

end teval

/-! ## The soundness of a successful match -/

section sound
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]

theorem big_sepL_seq_lookup {A : Type} [Inhabited A] (Φ : A → IProp GF) (l : List A) :
    ([∗list] c ∈ l, Φ c) = [∗list] j ∈ List.range l.length, Φ l[j]! := by
  have Heq : (List.range l.length).map (fun j => l[j]!) = l := by
    apply List.ext_getElem (by simp)
    intro i h1 h2
    simp [List.getElem?_eq_getElem h2]
  conv => lhs; rw [← Heq]
  exact BigSepL.bigSepL_map (fun j => l[j]!)

/-- Handing each points-to atom its own cell, and dropping the cells no atom
asked for. `R` is the list of cells still available. -/
theorem atoms_from_cells (P : Nat → IProp GF) (Q : cassn → IProp GF)
    (atoms : List cassn) (g : Nat → Nat) (R : List Nat) :
    (∀ (i : Nat) a, atoms[i]? = some a → is_pts a = true → g i ∈ R) →
    (∀ (i i' : Nat) a a', atoms[i]? = some a → atoms[i']? = some a' →
       is_pts a = true → is_pts a' = true → g i = g i' → i = i') →
    (∀ (i : Nat) a, atoms[i]? = some a → is_pts a = false → ⊢ Q a) →
    (∀ (i : Nat) a, atoms[i]? = some a → is_pts a = true → P (g i) ⊢ Q a) →
    ([∗list] j ∈ R, P j) ⊢ [∗list] a ∈ atoms, Q a := by
  induction atoms generalizing g R with
  | nil => intro _ _ _ _; iintro _; iempintro
  | cons a atoms ih =>
    intro Hin Hinj Hpure Hpts
    cases Ha : is_pts a
    · iintro HR
      isplitl []
      · iapply (Hpure 0 a rfl Ha)
      · iapply (ih (fun i => g (i + 1)) R
          (fun i a' Ha' Hp' => Hin (i + 1) a' Ha' Hp')
          (fun i i' b b' Hb Hb' Hp Hp' Heq => by
            have := Hinj (i + 1) (i' + 1) b b' Hb Hb' Hp Hp' Heq; omega)
          (fun i b Hb Hp => Hpure (i + 1) b Hb Hp)
          (fun i b Hb Hp => Hpts (i + 1) b Hb Hp)) $$ HR
    · have Hmem : g 0 ∈ R := Hin 0 a rfl Ha
      refine (BigSepL.bigSepL_perm (List.perm_cons_erase Hmem)).1.trans ?_
      iintro ⟨HP, HR⟩
      isplitl [HP]
      · iapply (Hpts 0 a rfl Ha) $$ HP
      · iapply (ih (fun i => g (i + 1)) (R.erase (g 0))
          (fun i a' Ha' Hp' => by
            apply List.mem_erase_of_ne ?_ |>.mpr (Hin (i + 1) a' Ha' Hp')
            intro Heq
            have := Hinj (i + 1) 0 a' a Ha' rfl Hp' Ha Heq
            omega)
          (fun i i' b b' Hb Hb' Hp Hp' Heq => by
            have := Hinj (i + 1) (i' + 1) b b' Hb Hb' Hp Hp' Heq; omega)
          (fun i b Hb Hp => Hpure (i + 1) b Hb Hp)
          (fun i b Hb Hp => Hpts (i + 1) b Hb Hp)) $$ HR

/-- The matcher's soundness: phase 0 (every atom is scoped by the declared
variables), phase 1 (every points-to atom resolved) and phase 2 (every
pure atom justified) together give `path_sat_dj`. -/
theorem match_path_sat (vars : List sort) (sp : spath) (dj : cdisjunct)
    (σ : List (Option term)) (used done : List Bool) :
    (d_pats dj).length = (d_pat_ok dj).length →
    (∀ a, a ∈ d_atoms dj → atom_scoped vars.length a) →
    phase1_inv (sheap (pst sp)) (d_atoms dj) (d_pats dj) (d_pat_ok dj)
      (svars (pst sp)) (pret sp) σ used done →
    undone (d_atoms dj) done = 0 →
    pure_ok (spc (pst sp)) (d_atoms dj) σ (pret sp) →
    path_sat_dj_at (GF := GF) vars sp dj := by
  intro Hlpats Hscoped ⟨Hlσ, Hlu, Hld, Hswf, f, Hf, Hinj⟩ Hundone Hpure
  intro θ V' _ Hag ⟨Hsv, Hpc⟩ Hwf _ Hr
  obtain ⟨Hagv, _, _⟩ := Hag
  obtain ⟨Hpr, Hrr⟩ := vars_below_nopat _ _ Hr
  let W := pat_witness V' σ (d_pats dj) (d_pat_ok dj)
  have HW : ∀ (n : Nat) (y : term), σ[n]? = some (some y) → W n = teval V' y := by
    intro n y Hn; simp only [W, pat_witness, Hn]
  have Hlen_ok : ∀ n : Nat, (d_pat_ok dj)[n]? = some true → ∃ s, (d_pats dj)[n]? = some s := by
    intro n Hn
    have : n < (d_pats dj).length := by
      rw [Hlpats]; exact (List.getElem?_eq_some_iff.mp Hn).1
    exact ⟨_, List.getElem?_eq_getElem this⟩
  unfold dj_interp heap_interp
  rw [big_sepL_seq_lookup]
  iintro HH
  iexists W
  isplitr
  · ipureintro
    intro n Hn
    simp only [W, pat_witness]
    cases Hσ : σ[n]? with
    | some o =>
      cases o with
      | some y =>
        obtain ⟨_, s, Hs, Hsy⟩ := Hswf n y Hσ
        exact ⟨s, Hs, sort_of_vars_sound V' _ y s Hsv Hsy⟩
      | none =>
        obtain ⟨s, Hs⟩ := Hlen_ok n Hn
        simp only [Hn, Hs]
        exact ⟨s, rfl, sort_default_has_sort s⟩
    | none =>
      obtain ⟨s, Hs⟩ := Hlen_ok n Hn
      simp only [Hn, Hs]
      exact ⟨s, rfl, sort_default_has_sort s⟩
  isplitr
  · ipureintro
    intro n Hn
    simp only [W, pat_witness]
    cases Hσ : σ[n]? with
    | some o =>
      cases o with
      | some y => exact absurd (Hswf n y Hσ).1 Hn
      | none =>
        simp only
        split
        · rename_i h _; exact absurd h Hn
        · rfl
    | none =>
      simp only
      split
      · rename_i h _; exact absurd h Hn
      · rfl
  iapply (atoms_from_cells _ _ _ f _ ?_ ?_ ?_ ?_) $$ HH
  · intro i a Ha Hp
    obtain ⟨x, v, rfl⟩ := is_pts_inv a Hp
    have Hdi := undone_zero _ _ _ _ _ Hld Hundone Ha
    obtain ⟨_, _, c, _, _, _, Hc, _⟩ := Hf i Hdi
    exact List.mem_range.mpr (List.getElem?_eq_some_iff.mp Hc).1
  · intro i i' a a' Ha Ha' Hp Hp' Heq
    obtain ⟨x, v, rfl⟩ := is_pts_inv a Hp
    obtain ⟨x', v', rfl⟩ := is_pts_inv a' Hp'
    exact Hinj i i' (undone_zero _ _ _ _ _ Hld Hundone Ha)
      (undone_zero _ _ _ _ _ Hld Hundone Ha') Heq
  · intro i a Ha Hp
    have Hsc := Hscoped a (List.mem_of_getElem? Ha)
    cases a with
    | CAPure x =>
      obtain ⟨y, Hy, Hpy, Hch⟩ := Hpure i x Ha
      simp only [assn_interp]
      ipureintro
      rw [inst_teval θ W V' (pret sp) σ vars.length Hagv HW x y Hsc Hy Hpy]
      exact cond_holds_sound V' _ y Hpc Hch
    | CAPointsTo => simp [is_pts] at Hp
    | _ => exact absurd Hsc id
  · intro i a Ha Hp
    obtain ⟨x, v, rfl⟩ := is_pts_inv a Hp
    obtain ⟨Hsx, Hsv'⟩ := Hscoped _ (List.mem_of_getElem? Ha)
    have Hdi := undone_zero _ _ _ _ _ Hld Hundone Ha
    obtain ⟨x', v', c, σ0, σ1, Ha', Hc, _, Hx, Hpx, Hm, Hext⟩ := Hf i Hdi
    rw [Ha] at Ha'
    cases Ha'
    have Hext01 := match_rel_ext Hm
    have Hcin : c ∈ sheap (pst sp) := List.mem_of_getElem? Hc
    obtain ⟨_, Hbv⟩ := Hwf.wf_heap c Hcin
    obtain ⟨Hpv, _⟩ := vars_below_nopat _ _ Hbv
    have Hiv := match_rel_inst Hm Hpr Hrr Hpv
    simp only [oinstantiate_t] at Hiv
    have Hx' : instantiate_t x σ (some (pret sp)) = some (cloc c) :=
      inst_ext x σ0 σ _ _ (subst_ext_trans _ _ _ Hext01 Hext) Hx Hpx
    have Hv' : instantiate_t v σ (some (pret sp)) = some (cval c) :=
      inst_ext v σ1 σ _ _ Hext Hiv Hpv
    have Hget : (sheap (pst sp))[f i]! = c := by
      simp [Hc]
    simp only [assn_interp, Hget]
    rw [inst_teval θ W V' (pret sp) σ vars.length Hagv HW x _ Hsx Hx' Hpx,
      inst_teval θ W V' (pret sp) σ vars.length Hagv HW v _ Hsv' Hv' Hpv]

end sound

end Checker
end Perennial
