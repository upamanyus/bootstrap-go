/-
Port of `new/checker/fn/sortOfEnv.v`.

`checker.sortOfEnv` (checker/sorts.go): the sort of a term in a sort
environment.

Note on shape: the specification is stated once as an `IProp`
(`sortOfEnv_spec`) and proved by one lemma per shape of a recursive term,
each taking the Löb induction hypothesis as an argument. (In Rocq, proving
all eighteen cases inside a single `Lemma` built a proof term of several
gigabytes.)

Lean notes:
* `sortOfEnv_spec` is a `def` (with a `Persistent` instance) rather than a
  notation-level `iProp`, so that the case lemmas can `unfold` it.
* `osort_of`/`osort_code`/`osort_ok`/`sort_code_inj` are pure, outside the
  proof section.
* The case lemmas share the macros `open_node` (everything up to the dispatch
  on the node's kind) and `rec_call` (one recursive call); they are declared
  with `hygiene false` so that the Iris hypothesis names they introduce are
  visible to the caller.
* After the recursive calls, the case analysis is over all combinations of
  the operand sorts (`rcases … with _ | (_|_|_|_)`), each finished by
  `wp_auto`: Lean evaluates the remaining tests quickly enough that Rocq's
  narrower per-shape tactics (`bin_int`, `eq_sorts`, …) are not needed.
-/
import Checkers.Checker.Nodes

set_option linter.iris.style.nameCheck false
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false

noncomputable section

namespace Perennial
namespace Checker

open Iris Iris.BI Iris.ProofMode Iris.ProgramLogic
open github_com.upamanyus.bootstrap_go

/-- The Go function is nil-safe, so its specification is over an
`Option term`; the nil pointer has no sort. -/
def osort_of (E : sort_env) : Option term → Option sort
  | none => none
  | some ty => sort_of E ty

/-- The two components the Go function returns. On failure it answers
`(SortInt, false)`, and `SortInt`'s code is `W64 0`. -/
def osort_code : Option sort → w64
  | some s => sort_code s
  | none => W64 0

def osort_ok : Option sort → Bool
  | some _ => true
  | none => false

/-- The Go code compares sorts by their codes, `sort_of` by `decide`; the two
agree because the encoding is injective. -/
theorem sort_code_inj (s1 s2 : sort) : sort_code s1 = sort_code s2 → s1 = s2 := by
  cases s1 <;> cases s2 <;> first | (intro; rfl) | (intro h; revert h; decide)

section proof
variable [ext : FfiSyntax] [ffi : FfiModel] [FfiInterp ffi] [FfiSemantics ext ffi]
variable [go_gctx : GoGlobalContext]
variable {hlc : HasLC} {GF : BundledGFunctors} [hG : HeapGS hlc GF]
variable [sem : go.Semantics]
variable [package_sem : checker.Assumptions]

/-- The four points-to that `sortOfEnv` reads. They are kept apart from
`is_sortenv` so that `wp_auto` can see them and so that every recursive
call is about the same three slices. -/
def env_pts (dq : DFrac) (lenv : Loc) (Env : sort_env) (svs sps sks : GoSlice) : IProp GF :=
  iprop(lenv ↦{dq} checker.sortEnv.mk svs sps sks (sort_code (se_ret Env)) (se_ret_ok Env) ∗
   svs ↦*{dq} ((se_vars Env).map sort_code) ∗
   sps ↦*{dq} ((se_pats Env).map sort_code) ∗
   sks ↦*{dq} se_pat_ok Env)

def sortOfEnv_spec (dq : DFrac) (lenv : Loc) (Env : sort_env) (svs sps sks : GoSlice)
    (lterm : Loc) (oty : Option term) : IProp GF :=
  iprop({{ isPkgInit (PROP := IProp GF) checker_pkg ∗ env_pts dq lenv Env svs sps sks ∗
          is_oterm lterm oty }}
     (App (App (Val (@! checker.sortOfEnv)) (Val #lenv)) (Val #lterm))
   {{ RET (PairV #(osort_code (osort_of Env oty)) #(osort_ok (osort_of Env oty)));
       env_pts dq lenv Env svs sps sks }})

instance sortOfEnv_spec_persistent (dq : DFrac) (lenv : Loc) (Env : sort_env)
    (svs sps sks : GoSlice) (lterm : Loc) (oty : Option term) :
    Persistent (sortOfEnv_spec (GF := GF) dq lenv Env svs sps sks lterm oty) := by
  unfold sortOfEnv_spec; infer_instance

set_option hygiene false in
/-- Everything up to the dispatch on the node's kind. -/
local macro "open_node" : tactic => `(tactic| (
  unfold sortOfEnv_spec env_pts
  wp_start as ⟨⟨Hstruct, Hvars, Hpats, Hpok⟩, #Hot⟩
  ihave %Hnull := is_oterm_null _ _ $$ Hot
  wp_auto
  wp_if_destruct
  · exact absurd (Hnull.mp rfl) (by simp)
  rw [is_oterm_some]
  icases is_term_node _ _ $$ Hot with ⟨%la, %lb, %lc, %Hidx, #Hnode, #Hta, #Htb, #Htc⟩
  iStructNamed Hnode
  simp only [term_code, term_num, term_a, term_b, term_c, term_idx_wf] at *))

set_option hygiene false in
/-- One recursive call, on the child at `l` (whose `is_oterm` is `H`). -/
local macro "rec_call" l:term:max o:term:max H:ident : tactic => `(tactic| (
  wp_apply IH $$ %$l %$o [Hstruct Hvars Hpats Hpok] as ⟨Hstruct, Hvars, Hpats, Hpok⟩
  · iframe Hstruct Hvars Hpats Hpok $H:ident))

set_option hygiene false in
/-- The end of every case: the returned pair is the spec's. -/
local macro "finish" : tactic => `(tactic| (
  try simp only [checker.SortInt, checker.SortBool, checker.SortLoc, checker.SortUnit]
  iapply HΦ; iframe))

set_option hygiene false in
/-- The leaf cases read fields of the `sortEnv` struct: split it (into `vars`,
`pats`, `patOk`, `ret`, `retOk`). -/
local macro "split_env" : tactic => `(tactic| (
  ihave %Hnn := typedPointsto_not_null _ _ _ $$ Hstruct
  iStructNamed Hstruct))

set_option hygiene false in
/-- `finish` after `split_env`: put the struct back together. -/
local macro "finish_split" : tactic => `(tactic| (
  try simp only [checker.SortInt, checker.SortBool, checker.SortLoc, checker.SortUnit]
  iapply HΦ
  isplitl [vars pats patOk ret retOk]
  · iapply typedPointsto_combine _ _ _ Hnn
    simp only [TypedPointsto.typedPointstoDef]
    iframe
  · iframe))

local notation "SPEC" => sortOfEnv_spec (GF := GF)

/-! ## The recursive cases, one lemma each -/

section cases
variable (dq : DFrac) (lenv : Loc) (Env : sort_env) (svs sps sks : GoSlice) (lterm : Loc)

/-- `x` and `y` must both have sort `SInt`; shared by `+`, `-`, `*`. -/
theorem step_arith (k : term → term → term) (x1 x2 : term)
    (Hk : k = TPlus ∨ k = TMinus ∨ k = TMul) :
    (▷ (∀ l o, SPEC dq lenv Env svs sps sks l o)) ⊢
      SPEC dq lenv Env svs sps sks lterm (some (k x1 x2)) := by
  iintro #IH
  rcases Hk with rfl | rfl | rfl
  all_goals
    open_node
    wp_auto
    rec_call la (some x1) Hta
    try wp_auto
    rec_call lb (some x2) Htb
    simp only [osort_of, sort_of]
    rcases sort_of Env x1 with _ | (_|_|_|_) <;> rcases sort_of Env x2 with _ | (_|_|_|_) <;>
      simp only [osort_ok, osort_code, sort_code, reduceCtorEq, ↓reduceIte, ite_true, ite_false] <;> wp_auto <;> finish

theorem step_cmp (sg : Bool) (k : Bool → term → term → term) (x1 x2 : term)
    (Hk : k = TLt ∨ k = TLe) :
    (▷ (∀ l o, SPEC dq lenv Env svs sps sks l o)) ⊢
      SPEC dq lenv Env svs sps sks lterm (some (k sg x1 x2)) := by
  iintro #IH
  rcases Hk with rfl | rfl <;> cases sg
  all_goals
    open_node
    wp_auto
    rec_call la (some x1) Hta
    try wp_auto
    rec_call lb (some x2) Htb
    simp only [osort_of, sort_of]
    rcases sort_of Env x1 with _ | (_|_|_|_) <;> rcases sort_of Env x2 with _ | (_|_|_|_) <;>
      simp only [osort_ok, osort_code, sort_code, reduceCtorEq, ↓reduceIte, ite_true, ite_false] <;> wp_auto <;> finish

theorem step_TEq (x1 x2 : term) :
    (▷ (∀ l o, SPEC dq lenv Env svs sps sks l o)) ⊢
      SPEC dq lenv Env svs sps sks lterm (some (TEq x1 x2)) := by
  iintro #IH
  open_node
  wp_auto
  rec_call la (some x1) Hta
  try wp_auto
  rec_call lb (some x2) Htb
  simp only [osort_of, sort_of]
  rcases sort_of Env x1 with _ | (_|_|_|_) <;> rcases sort_of Env x2 with _ | (_|_|_|_) <;>
    simp only [osort_ok, osort_code, sort_code, reduceCtorEq, ↓reduceIte, ite_true, ite_false] <;> wp_auto <;> finish

theorem step_un (k : term → term) (x1 : term) (Hk : k = TNeg ∨ k = TNot) :
    (▷ (∀ l o, SPEC dq lenv Env svs sps sks l o)) ⊢
      SPEC dq lenv Env svs sps sks lterm (some (k x1)) := by
  iintro #IH
  rcases Hk with rfl | rfl
  all_goals
    open_node
    wp_auto
    rec_call la (some x1) Hta
    simp only [osort_of, sort_of]
    rcases sort_of Env x1 with _ | (_|_|_|_) <;>
      simp only [osort_ok, osort_code, sort_code, reduceCtorEq, ↓reduceIte, ite_true, ite_false] <;> wp_auto <;> finish

theorem step_TIte (x1 x2 x3 : term) :
    (▷ (∀ l o, SPEC dq lenv Env svs sps sks l o)) ⊢
      SPEC dq lenv Env svs sps sks lterm (some (TIte x1 x2 x3)) := by
  iintro #IH
  open_node
  wp_auto
  rec_call la (some x1) Hta
  try wp_auto
  rec_call lb (some x2) Htb
  try wp_auto
  rec_call lc (some x3) Htc
  simp only [osort_of, sort_of]
  rcases sort_of Env x1 with _ | (_|_|_|_) <;> rcases sort_of Env x2 with _ | (_|_|_|_) <;>
    rcases sort_of Env x3 with _ | (_|_|_|_) <;>
    simp only [osort_ok, osort_code, sort_code, reduceCtorEq, ↓reduceIte, ite_true, ite_false] <;> wp_auto <;> finish

end cases

/-! ## The dispatch -/

theorem sortOfEnv_spec_holds (dq : DFrac) (lenv : Loc) (Env : sort_env)
    (svs sps sks : GoSlice) (Hwf : sort_env_wf Env) :
    ⊢ ∀ (lterm : Loc) (oty : Option term), SPEC dq lenv Env svs sps sks lterm oty := by
  iloeb as IH
  iintro %lterm %oty
  cases oty with
  | none =>
    -- the term is nil
    unfold sortOfEnv_spec env_pts
    rw [is_oterm_none]
    wp_start as ⟨⟨Hstruct, Hvars, Hpats, Hpok⟩, %Hot⟩
    subst Hot
    wp_auto
    simp only [osort_of, osort_code, osort_ok]
    finish
  | some ty =>
  cases ty with
  | TPlus x1 x2 => iapply step_arith (Hk := Or.inl rfl); iexact IH
  | TMinus x1 x2 => iapply step_arith (Hk := Or.inr (Or.inl rfl)); iexact IH
  | TMul x1 x2 => iapply step_arith (Hk := Or.inr (Or.inr rfl)); iexact IH
  | TLt sg x1 x2 => iapply step_cmp _ (Hk := Or.inl rfl); iexact IH
  | TLe sg x1 x2 => iapply step_cmp _ (Hk := Or.inr rfl); iexact IH
  | TEq x1 x2 => iapply step_TEq; iexact IH
  | TNeg x1 => iapply step_un (Hk := Or.inl rfl); iexact IH
  | TNot x1 => iapply step_un (Hk := Or.inr rfl); iexact IH
  | TIte x1 x2 x3 => iapply step_TIte; iexact IH
  | TVar k =>
    open_node
    ihave %Hlv := ownSlice_len _ _ _ $$ Hvars
    simp only [List.length_map] at Hlv
    unfold idx_wf at Hidx
    split_env
    try wp_auto
    wp_if_destruct
    · -- the index is out of range
      have Hlook : (se_vars Env)[k]? = none := List.getElem?_eq_none (by word)
      simp only [osort_of, sort_of, Hlook, osort_code, osort_ok]
      finish_split
    · -- the index is in range
      have Hk : k < (se_vars Env).length := by word
      obtain ⟨srt, Hlook⟩ : ∃ s, (se_vars Env)[k]? = some s :=
        ⟨_, List.getElem?_eq_getElem Hk⟩
      simp only [osort_of, sort_of, Hlook, osort_code, osort_ok]
      simp only [show 0 ≤ sint.Z (W64 k) ∧ sint.Z (W64 k) < sint.Z svs.len from by word,
        ↓reduceIte]
      wp_apply wp_load_slice_index svs (sint.Z (W64 k)) _ dq (sort_code srt) (by word) $$ [Hvars]
        as Hvars
      · iframe Hvars; ipureintro
        rw [show (sint.Z (W64 k)).toNat = k by word, List.getElem?_map, Hlook]; rfl
      wp_auto
      finish_split
  | TPat k =>
    open_node
    ihave %Hlp := ownSlice_len _ _ _ $$ Hpats
    ihave %Hlk := ownSlice_len _ _ _ $$ Hpok
    simp only [List.length_map] at Hlp
    unfold idx_wf at Hidx
    unfold sort_env_wf at Hwf
    split_env
    try wp_auto
    wp_if_destruct
    · -- the index is out of range
      have Hlook : (se_pats Env)[k]? = none := List.getElem?_eq_none (by word)
      simp only [osort_of, sort_of, Hlook, osort_code, osort_ok]
      finish_split
    · -- the index is in range; `sort_env_wf` makes `patOk` in range too
      have Hk : k < (se_pats Env).length := by word
      obtain ⟨srt, Hlook⟩ : ∃ s, (se_pats Env)[k]? = some s :=
        ⟨_, List.getElem?_eq_getElem Hk⟩
      obtain ⟨bk, Hok⟩ : ∃ b, (se_pat_ok Env)[k]? = some b :=
        ⟨_, List.getElem?_eq_getElem (by omega)⟩
      simp only [osort_of, sort_of, Hlook, Hok]
      simp only [show 0 ≤ sint.Z (W64 k) ∧ sint.Z (W64 k) < sint.Z sks.len from by word,
        ↓reduceIte]
      wp_apply wp_load_slice_index sks (sint.Z (W64 k)) _ dq bk (by word) $$ [Hpok]
        as Hpok
      · iframe Hpok; ipureintro
        rw [show (sint.Z (W64 k)).toNat = k by word, Hok]
      cases bk
      · -- no binder declared it
        wp_auto
        simp only [osort_code, osort_ok]
        finish_split
      · -- the pattern variable is declared
        wp_auto
        simp only [show 0 ≤ sint.Z (W64 k) ∧ sint.Z (W64 k) < sint.Z sps.len from by word,
          ↓reduceIte]
        wp_apply wp_load_slice_index sps (sint.Z (W64 k)) _ dq (sort_code srt) (by word) $$ [Hpats]
          as Hpats
        · iframe Hpats; ipureintro
          rw [show (sint.Z (W64 k)).toNat = k by word, List.getElem?_map, Hlook]; rfl
        wp_auto
        simp only [osort_code, osort_ok]
        finish_split
  | TResult =>
    open_node
    split_env
    simp only [osort_of, sort_of]
    cases se_ret_ok Env <;> wp_auto <;>
      simp only [osort_code, osort_ok, Bool.false_eq_true, ↓reduceIte] <;> finish_split
  | TInt w => open_node; wp_auto; simp only [osort_of, sort_of, osort_code, osort_ok, sort_code]; finish
  | TBool b => open_node; wp_auto; simp only [osort_of, sort_of, osort_code, osort_ok, sort_code]; finish
  | TUnit => open_node; wp_auto; simp only [osort_of, sort_of, osort_code, osort_ok, sort_code]; finish
  | TNull => open_node; wp_auto; simp only [osort_of, sort_of, osort_code, osort_ok, sort_code]; finish
  | TExec => open_node; wp_auto; simp only [osort_of, sort_of, osort_code, osort_ok, sort_code]; finish
  | TRet x1 => open_node; wp_auto; simp only [osort_of, sort_of, osort_code, osort_ok, sort_code]; finish

/-! ## The public specifications -/

/-- The unpacked form, with the `sortEnv` struct and its three slices written
out: what `SortOf` needs, since it builds the struct itself. -/
theorem wp_sortOfEnv_pts (dq : DFrac) (lenv : Loc) (Env : sort_env)
    (svs sps sks : GoSlice) (lterm : Loc) (oty : Option term) (Hwf : sort_env_wf Env) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗
        lenv ↦{dq} checker.sortEnv.mk svs sps sks (sort_code (se_ret Env)) (se_ret_ok Env) ∗
        svs ↦*{dq} ((se_vars Env).map sort_code) ∗
        sps ↦*{dq} ((se_pats Env).map sort_code) ∗
        sks ↦*{dq} se_pat_ok Env ∗
        is_oterm lterm oty }}
      (App (App (Val (@! checker.sortOfEnv)) (Val #lenv)) (Val #lterm))
    {{ RET (PairV #(osort_code (osort_of Env oty)) #(osort_ok (osort_of Env oty)));
        lenv ↦{dq} checker.sortEnv.mk svs sps sks (sort_code (se_ret Env)) (se_ret_ok Env) ∗
        svs ↦*{dq} ((se_vars Env).map sort_code) ∗
        sps ↦*{dq} ((se_pats Env).map sort_code) ∗
        sks ↦*{dq} se_pat_ok Env }} := by
  iintro %Φ ⟨#Hinit, Hstruct, Hvars, Hpats, Hpok, #Hot⟩ HΦ
  ihave #Hspec := sortOfEnv_spec_holds dq lenv Env svs sps sks Hwf
  ispecialize Hspec $$ %lterm %oty
  unfold sortOfEnv_spec env_pts
  iapply Hspec $$ [Hstruct Hvars Hpats Hpok]
  · iframe # ∗
  · inext; iexact HΦ

/-- The packaged form: `is_sortenv` hides the three slices. -/
theorem wp_sortOfEnv (dq : DFrac) (lenv lterm : Loc) (Env : sort_env) (oty : Option term)
    (Hwf : sort_env_wf Env) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_sortenv dq lenv Env ∗ is_oterm lterm oty }}
      (App (App (Val (@! checker.sortOfEnv)) (Val #lenv)) (Val #lterm))
    {{ RET (PairV #(osort_code (osort_of Env oty)) #(osort_ok (osort_of Env oty)));
        is_sortenv dq lenv Env }} := by
  iintro %Φ ⟨#Hinit, Henv, #Hot⟩ HΦ
  unfold is_sortenv
  icases Henv with ⟨%svs, %sps, %sks, Hstruct, Hvars, Hpats, Hpok⟩
  wp_apply wp_sortOfEnv_pts dq lenv Env svs sps sks lterm oty Hwf $$ [Hstruct Hvars Hpats Hpok]
    as ⟨Hstruct, Hvars, Hpats, Hpok⟩
  · iframe # ∗
  iapply HΦ
  iexists svs, sps, sks
  iframe

/-- The form a caller usually wants: the boolean decides whether the term has
a sort at all, and the code is then that sort's. -/
theorem wp_sortOfEnv' (dq : DFrac) (lenv lterm : Loc) (Env : sort_env) (oty : Option term) :
    {{ isPkgInit (PROP := IProp GF) checker_pkg ∗ is_sortenv dq lenv Env ∗ is_oterm lterm oty ∗
        ⌜sort_env_wf Env⌝ }}
      (App (App (Val (@! checker.sortOfEnv)) (Val #lenv)) (Val #lterm))
    {{ (scode : w64) (ok : Bool), RET (PairV #scode #ok);
        is_sortenv dq lenv Env ∗
        ⌜ok = true ↔ ∃ ty s, oty = some ty ∧ sort_of Env ty = some s⌝ ∗
        ⌜∀ ty s, oty = some ty → sort_of Env ty = some s → scode = sort_code s⌝ }} := by
  iintro %Φ ⟨#Hinit, Henv, #Hot, %Hwf⟩ HΦ
  wp_apply wp_sortOfEnv dq lenv lterm Env oty Hwf $$ [Henv] as Henv
  · iframe # ∗
  iapply HΦ
  iframe Henv
  ipureintro
  cases oty with
  | none => simp [osort_of, osort_ok]
  | some ty =>
    simp only [osort_of]
    cases Hs : sort_of Env ty with
    | none =>
      simp only [osort_ok, Hs]
      refine ⟨by simp [Hs], ?_⟩
      intro ty' s Heq H; cases Heq; rw [Hs] at H; cases H
    | some s' =>
      simp only [osort_ok, osort_code]
      refine ⟨by simp [Hs], ?_⟩
      intro ty' s Heq H; cases Heq; rw [Hs] at H; cases H; rfl

end proof
end Checker
end Perennial
