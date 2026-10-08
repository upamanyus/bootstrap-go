/-
# The serialization as one big number: fast for the kernel

An observation's axiom records the bytes a Go run of `tcheck.Check` read, and
its proof must show that they are `ser_input` of the Lean input. As a list of
bytes (`GoString`), that equation costs the kernel about 0.4 ms per byte (it
builds `ser_input`'s list one cons cell at a time): 4.8 s by `decide` for
raft's `becomeFollower` (6,735 bytes). The kernel's fast data is `Nat`
(literals and arithmetic are GMP numbers), so here:

* `asEnc l = (l.length, natOf l)` reads bytes as a length and a big-endian
  number;
* `encInput i` computes `asEnc (ser_input i)` directly, appending whole tokens
  at a time (`tok!"(sym "` elaborates to the token's `(length, number)`
  literal, with a proof that it is `asEnc go!"(sym "`): `encInput_eq`;
* `bytes_of_nat len N` decodes, and `bytes_of_nat_asEnc` inverts `asEnc`.

So `encInput i = (len, N)` -- an equation of two closed `Nat` pairs, proved by
`rfl` (`kernel_rfl`, Observe.lean) in about 0.5 s -- gives
`ser_input i = bytes_of_nat len N` (`ser_eq_of_enc`). The observation's axiom
is stated with `obs!"<bytes>"` (Observe.lean), which elaborates the recorded
bytes to `bytes_of_nat len N` instead of a list.
-/
import Checkers.TCheck.Syntax

namespace Perennial
namespace TCheck

/-! ## Bytes as numbers -/

/-- A byte string as a big-endian number. -/
def natOf (l : GoString) : Nat := l.foldl (fun acc b => acc * 256 + b.toNat) 0

/-- What the encoder computes: length and number. -/
abbrev Enc := Nat × Nat

def asEnc (l : GoString) : Enc := (l.length, natOf l)

/-- Appending, on encodings. -/
def eapp (e t : Enc) : Enc := (e.1 + t.1, e.2 * 256 ^ t.1 + t.2)

theorem foldl_natOf (l : GoString) : ∀ a : Nat,
    l.foldl (fun acc b => acc * 256 + b.toNat) a = a * 256 ^ l.length + natOf l := by
  induction l with
  | nil => intro a; simp [natOf]
  | cons b l ih =>
    intro a
    simp only [List.foldl_cons, natOf, List.length_cons]
    rw [ih, ih (0 * 256 + b.toNat), Nat.pow_succ]
    simp only [Nat.zero_mul, Nat.zero_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]
    rw [Nat.mul_comm 256 (256 ^ l.length)]

theorem natOf_append (l1 l2 : GoString) : natOf (List.append l1 l2) = natOf l1 * 256 ^ l2.length + natOf l2 := by
  show (l1 ++ l2).foldl _ 0 = _
  rw [List.foldl_append, foldl_natOf]
  rfl

theorem asEnc_append (l1 l2 : GoString) : asEnc (List.append l1 l2) = eapp (asEnc l1) (asEnc l2) := by
  simp only [asEnc, eapp, natOf_append]
  show ((l1 ++ l2).length, _) = _
  rw [List.length_append]

theorem eapp_assoc (e a b : Enc) : eapp (eapp e a) b = eapp e (eapp a b) := by
  obtain ⟨e1, e2⟩ := e; obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
  simp only [eapp, Nat.add_assoc, Nat.pow_add, Nat.add_mul, Nat.mul_assoc]

theorem eapp_nil (e : Enc) : eapp e (asEnc []) = e := by
  obtain ⟨e1, e2⟩ := e; simp [eapp, asEnc, natOf]

/-- The number of `bytes_of_nat len N`'s bytes is `len`, the last one
`N % 256`. -/
def bytes_of_nat : Nat → Nat → GoString
  | 0, _ => []
  | k + 1, n => bytes_of_nat k (n / 256) ++ [BitVec.ofNat 8 (n % 256)]

theorem bytes_of_nat_rev (r : GoString) :
    bytes_of_nat r.reverse.length (natOf r.reverse) = r.reverse := by
  induction r with
  | nil => rfl
  | cons b r ih =>
    have hb : b.toNat < 256 := b.isLt
    have hn : natOf (r.reverse ++ [b]) = natOf r.reverse * 256 + b.toNat := by
      show natOf (List.append r.reverse [b]) = _
      rw [natOf_append]; simp [natOf]
    simp only [List.reverse_cons, List.length_append, List.length_singleton, bytes_of_nat, hn]
    rw [show (natOf r.reverse * 256 + b.toNat) / 256 = natOf r.reverse by omega,
      show (natOf r.reverse * 256 + b.toNat) % 256 = b.toNat by omega, ih]
    simp

theorem bytes_of_nat_asEnc (l : GoString) : bytes_of_nat l.length (natOf l) = l := by
  have := bytes_of_nat_rev l.reverse
  rwa [List.reverse_reverse] at this

/-! ## Tokens -/

/-- A token: its encoding `(len, n)`, with the proof that it encodes `l`. -/
def tokv (l : GoString) (len n : Nat) (_h : (len, n) = asEnc l) : Enc := (len, n)

theorem tokv_eq (l : GoString) (len n : Nat) (h : (len, n) = asEnc l) : tokv l len n h = asEnc l := h

open Lean Elab Term Meta in
/-- `tok!"s"`: the token `go!"s"`, encoded at elaboration (the proof is
`rfl`, checked by the kernel when the definition using it is). -/
elab:max "tok!" s:str : term => do
  let bs := s.getString.toUTF8.toList
  let n := bs.foldl (fun acc b => acc * 256 + b.toNat) 0
  let l ← elabTerm (← `(go!$s)) (some (mkConst ``GoString))
  let pair := mkApp4 (mkConst ``Prod.mk [0, 0]) (mkConst ``Nat) (mkConst ``Nat) (mkNatLit bs.length) (mkNatLit n)
  let h ← mkExpectedTypeHint (← mkEqRefl pair) (← mkEq pair (mkApp (mkConst ``asEnc) l))
  return mkApp4 (mkConst ``tokv) l (mkNatLit bs.length) (mkNatLit n) h

/-! ## The encoder

Each `enc_X e x` is `eapp e (asEnc (ser_X x))` (`enc_*_eq`), appending
tokens and recursing as `ser_X` does; the leaves `ser_nat`, `ser_srt` and
`ser_str` are encoded from their bytes. -/

def enc_leaf (e : Enc) (l : GoString) : Enc := eapp e (asEnc l)

mutual
def enc_term (e : Enc) : tterm → Enc
  | TVar n => eapp (enc_leaf (eapp e tok!"(var ") (ser_nat n)) tok!")"
  | TSym n args => eapp (enc_terms (enc_leaf (eapp e tok!"(sym ") (ser_nat n)) args) tok!")"
  | TPair a b => eapp (enc_term (eapp (enc_term (eapp e tok!"(pair ") a) tok!" ") b) tok!")"
  | TLit ty es => eapp (enc_terms (enc_term (eapp e tok!"(lit ") ty) es) tok!")"
  | TUnit => eapp e tok!"unit"
def enc_terms (e : Enc) : List tterm → Enc
  | [] => e
  | t :: ts => enc_terms (enc_term (eapp e tok!" ") t) ts
end

/-- `ser_tail`, accumulating. -/
def enc_tail {A : Type} (f : Enc → A → Enc) : Enc → List A → Enc
  | e, [] => e
  | e, y :: l => enc_tail f (f (eapp e tok!" ") y) l

def enc_list {A : Type} (f : Enc → A → Enc) (e : Enc) : List A → Enc
  | [] => eapp e tok!"()"
  | x :: l => eapp (enc_tail f (f (eapp e tok!"(") x) l) tok!")"

def enc_pat (e : Enc) : tpat → Enc
  | PVal t => eapp (enc_term (eapp e tok!"(pval ") t) tok!")"
  | PApp a b => eapp (enc_pat (eapp (enc_pat (eapp e tok!"(papp ") a) tok!" ") b) tok!")"

def enc_atom (e : Enc) : tatom → Enc
  | APred n args => eapp (enc_tail enc_term (enc_leaf (eapp e tok!"(pred ") (ser_nat n)) args) tok!")"
  | AEq a b => eapp (enc_term (eapp (enc_term (eapp e tok!"(eq ") a) tok!" ") b) tok!")"

def enc_srt (e : Enc) (s : srt) : Enc := enc_leaf e (ser_srt s)
def enc_str (e : Enc) (x : String) : Enc := enc_leaf e (ser_str x)

mutual
def enc_cexpr (e : Enc) : cexpr → Enc
  | CVal t => eapp (enc_term (eapp e tok!"(val ") t) tok!")"
  | CVar x => eapp (enc_str (eapp e tok!"(cvar ") x) tok!")"
  | CApp a b => eapp (enc_cexpr (eapp (enc_cexpr (eapp e tok!"(app ") a) tok!" ") b) tok!")"
  | CPair a b => eapp (enc_cexpr (eapp (enc_cexpr (eapp e tok!"(cpair ") a) tok!" ") b) tok!")"
  | CLet x a b =>
      eapp (enc_cexpr (eapp (enc_cexpr (eapp (enc_str (eapp e tok!"(let ") x) tok!" ") a) tok!" ") b) tok!")"
  | CSeq a b => eapp (enc_cexpr (eapp (enc_cexpr (eapp e tok!"(seq ") a) tok!" ") b) tok!")"
  | CLit ty es => eapp (enc_cexprs (enc_term (eapp e tok!"(clit ") ty) es) tok!")"
  | CDo a => eapp (enc_cexpr (eapp e tok!"(do ") a) tok!")"
  | CRet a => eapp (enc_cexpr (eapp e tok!"(ret ") a) tok!")"
  | CXSeq a b => eapp (enc_cexpr (eapp (enc_cexpr (eapp e tok!"(xseq ") a) tok!" ") b) tok!")"
  | CXDo a => eapp (enc_cexpr (eapp e tok!"(xdo ") a) tok!")"
def enc_cexprs (e : Enc) : List cexpr → Enc
  | [] => e
  | x :: xs => enc_cexprs (enc_cexpr (eapp e tok!" ") x) xs
end

def enc_sym (e : Enc) (d : symdecl) : Enc :=
  eapp (enc_srt (eapp (enc_list enc_srt (eapp e tok!"(sym ") d.sd_args) tok!" ") d.sd_res) tok!")"
def enc_pred (e : Enc) (d : preddecl) : Enc :=
  eapp (enc_list enc_srt (eapp (eapp (eapp e tok!"(pred ") (if d.pd_pers then tok!"1" else tok!"0"))
    tok!" ") d.pd_args) tok!")"
def enc_rule (e : Enc) (r : trule) : Enc :=
  eapp (enc_list enc_atom (eapp (enc_term (eapp (enc_list enc_srt (eapp (enc_list enc_atom (eapp
    (enc_pat (eapp (enc_list enc_srt (eapp e tok!"(rule ") r.r_vars) tok!" ") r.r_lhs) tok!" ") r.r_pre)
    tok!" ") r.r_ex) tok!" ") r.r_ret) tok!" ") r.r_post) tok!")"
def enc_fact (e : Enc) (f : tfact) : Enc :=
  eapp (enc_term (eapp (enc_term (eapp (enc_list enc_srt (eapp e tok!"(fact ") f.f_vars) tok!" ")
    f.f_lhs) tok!" ") f.f_rhs) tok!")"
def enc_func (e : Enc) (f : cfunc) : Enc :=
  eapp (enc_cexpr (eapp (enc_list enc_str (eapp e tok!"(func ") f.fn_params) tok!" ") f.fn_body) tok!")"
def enc_spec (e : Enc) (s : tspec) : Enc :=
  eapp (enc_list enc_atom (eapp (enc_term (eapp (enc_list enc_srt (eapp (enc_list enc_atom (eapp
    (enc_list enc_term (eapp (enc_list enc_srt (eapp e tok!"(spec ") s.sp_vars) tok!" ") s.sp_args)
    tok!" ") s.sp_pre) tok!" ") s.sp_ex) tok!" ") s.sp_ret) tok!" ") s.sp_post) tok!")"

/-- `asEnc (ser_input i)`, computed from the input. -/
def encInput (i : tinput) : Enc :=
  eapp (enc_spec (eapp (enc_func (eapp (enc_tail enc_fact (eapp (enc_tail enc_rule (eapp
    (enc_tail enc_pred (eapp (enc_tail enc_sym (asEnc go!"(input (syms") i.in_syms) tok!") (preds")
    i.in_preds) tok!") (rules") i.in_rules) tok!") (facts") i.in_facts) tok!") ") i.in_func) tok!" ")
    i.in_spec) tok!")"

/-! ## The encoder computes `asEnc` of the serialization

Both sides normalize to a left-nested chain of `eapp`s: `asEnc_append`
turns the encoding of an append into an `eapp`, `← eapp_assoc` nests to the
left, and `tokv_eq` turns a token back into the encoding of its bytes. -/

theorem enc_leaf_eq (e : Enc) (l : GoString) : enc_leaf e l = eapp e (asEnc l) := rfl

mutual
theorem enc_term_eq : ∀ (t : tterm) (e : Enc), enc_term e t = eapp e (asEnc (ser_term t))
  | TVar n, e => by simp only [enc_term, ser_term, tokv_eq, enc_leaf_eq, asEnc_append, ← eapp_assoc]
  | TSym n args, e => by
      simp only [enc_term, ser_term, tokv_eq, enc_leaf_eq, enc_terms_eq args, asEnc_append, ← eapp_assoc]
  | TPair a b, e => by
      simp only [enc_term, ser_term, tokv_eq, enc_term_eq a, enc_term_eq b, asEnc_append, ← eapp_assoc]
  | TLit ty es, e => by
      simp only [enc_term, ser_term, tokv_eq, enc_term_eq ty, enc_terms_eq es, asEnc_append, ← eapp_assoc]
  | TUnit, e => by simp only [enc_term, ser_term, tokv_eq]
theorem enc_terms_eq : ∀ (ts : List tterm) (e : Enc), enc_terms e ts = eapp e (asEnc (ser_terms ts))
  | [], e => by simp only [enc_terms, ser_terms, eapp_nil]
  | t :: ts, e => by
      simp only [enc_terms, ser_terms, tokv_eq, enc_term_eq t, enc_terms_eq ts, asEnc_append, ← eapp_assoc]
end

theorem enc_tail_eq {A : Type} (f : Enc → A → Enc) (g : A → GoString)
    (hf : ∀ e y, f e y = eapp e (asEnc (g y))) :
    ∀ (l : List A) (e : Enc), enc_tail f e l = eapp e (asEnc (ser_tail g l))
  | [], e => by simp only [enc_tail, ser_tail, List.foldr_nil, eapp_nil]
  | y :: l, e => by
      simp only [enc_tail, ser_tail, List.foldr_cons] at *
      rw [enc_tail_eq f g hf l, hf]
      simp only [ser_tail, tokv_eq, asEnc_append, ← eapp_assoc]

theorem foldr_tail {A : Type} (g : A → GoString) (a z : GoString) : ∀ l : List A,
    l.foldr (fun y s => List.append a (List.append (g y) s)) z =
      List.append (l.foldr (fun y s => List.append a (List.append (g y) s)) []) z
  | [] => rfl
  | y :: l => by
      simp only [List.foldr_cons]
      rw [foldr_tail g a z l]
      show a ++ (g y ++ (_ ++ z)) = a ++ (g y ++ _) ++ z
      simp

theorem enc_list_eq {A : Type} (f : Enc → A → Enc) (g : A → GoString)
    (hf : ∀ e y, f e y = eapp e (asEnc (g y))) :
    ∀ (l : List A) (e : Enc), enc_list f e l = eapp e (asEnc (ser_list g l))
  | [], e => by simp only [enc_list, ser_list, tokv_eq]
  | x :: l, e => by
      simp only [enc_list, ser_list]
      rw [foldr_tail, enc_tail_eq f g hf, hf]
      simp only [ser_tail, tokv_eq, asEnc_append, ← eapp_assoc]

theorem enc_pat_eq : ∀ (p : tpat) (e : Enc), enc_pat e p = eapp e (asEnc (ser_pat p))
  | PVal t, e => by simp only [enc_pat, ser_pat, tokv_eq, enc_term_eq, asEnc_append, ← eapp_assoc]
  | PApp a b, e => by
      simp only [enc_pat, ser_pat, tokv_eq, enc_pat_eq a, enc_pat_eq b, asEnc_append, ← eapp_assoc]

theorem enc_atom_eq (e : Enc) (a : tatom) : enc_atom e a = eapp e (asEnc (ser_atom a)) := by
  cases a with
  | APred n args =>
    simp only [enc_atom, ser_atom, tokv_eq, enc_leaf_eq,
      enc_tail_eq enc_term ser_term (fun e t => enc_term_eq t e), asEnc_append, ← eapp_assoc]
  | AEq a b => simp only [enc_atom, ser_atom, tokv_eq, enc_term_eq, asEnc_append, ← eapp_assoc]

theorem enc_srt_eq (e : Enc) (s : srt) : enc_srt e s = eapp e (asEnc (ser_srt s)) := rfl
theorem enc_str_eq (e : Enc) (x : String) : enc_str e x = eapp e (asEnc (ser_str x)) := rfl

mutual
theorem enc_cexpr_eq : ∀ (x : cexpr) (e : Enc), enc_cexpr e x = eapp e (asEnc (ser_cexpr x))
  | CVal t, e => by simp only [enc_cexpr, ser_cexpr, tokv_eq, enc_term_eq, asEnc_append, ← eapp_assoc]
  | CVar x, e => by simp only [enc_cexpr, ser_cexpr, tokv_eq, enc_str_eq, asEnc_append, ← eapp_assoc]
  | CApp a b, e => by
      simp only [enc_cexpr, ser_cexpr, tokv_eq, enc_cexpr_eq a, enc_cexpr_eq b, asEnc_append, ← eapp_assoc]
  | CPair a b, e => by
      simp only [enc_cexpr, ser_cexpr, tokv_eq, enc_cexpr_eq a, enc_cexpr_eq b, asEnc_append, ← eapp_assoc]
  | CLet x a b, e => by
      simp only [enc_cexpr, ser_cexpr, tokv_eq, enc_str_eq, enc_cexpr_eq a, enc_cexpr_eq b, asEnc_append,
        ← eapp_assoc]
  | CSeq a b, e => by
      simp only [enc_cexpr, ser_cexpr, tokv_eq, enc_cexpr_eq a, enc_cexpr_eq b, asEnc_append, ← eapp_assoc]
  | CLit ty es, e => by
      simp only [enc_cexpr, ser_cexpr, tokv_eq, enc_term_eq, enc_cexprs_eq es, asEnc_append, ← eapp_assoc]
  | CDo a, e => by simp only [enc_cexpr, ser_cexpr, tokv_eq, enc_cexpr_eq a, asEnc_append, ← eapp_assoc]
  | CRet a, e => by simp only [enc_cexpr, ser_cexpr, tokv_eq, enc_cexpr_eq a, asEnc_append, ← eapp_assoc]
  | CXSeq a b, e => by
      simp only [enc_cexpr, ser_cexpr, tokv_eq, enc_cexpr_eq a, enc_cexpr_eq b, asEnc_append, ← eapp_assoc]
  | CXDo a, e => by simp only [enc_cexpr, ser_cexpr, tokv_eq, enc_cexpr_eq a, asEnc_append, ← eapp_assoc]
theorem enc_cexprs_eq : ∀ (xs : List cexpr) (e : Enc), enc_cexprs e xs = eapp e (asEnc (ser_cexprs xs))
  | [], e => by simp only [enc_cexprs, ser_cexprs, eapp_nil]
  | x :: xs, e => by
      simp only [enc_cexprs, ser_cexprs, tokv_eq, enc_cexpr_eq x, enc_cexprs_eq xs, asEnc_append,
        ← eapp_assoc]
end

theorem enc_sym_eq (e : Enc) (d : symdecl) : enc_sym e d = eapp e (asEnc (ser_sym d)) := by
  simp only [enc_sym, ser_sym, tokv_eq, enc_srt_eq, enc_list_eq enc_srt ser_srt (fun _ _ => rfl),
    asEnc_append, ← eapp_assoc]

theorem enc_pred_eq (e : Enc) (d : preddecl) : enc_pred e d = eapp e (asEnc (ser_pred d)) := by
  simp only [enc_pred, ser_pred, enc_list_eq enc_srt ser_srt (fun _ _ => rfl)]
  cases d.pd_pers <;> simp only [Bool.false_eq_true, ↓reduceIte, tokv_eq, asEnc_append, ← eapp_assoc]

theorem enc_rule_eq (e : Enc) (r : trule) : enc_rule e r = eapp e (asEnc (ser_rule r)) := by
  simp only [enc_rule, ser_rule, tokv_eq, enc_term_eq, enc_pat_eq,
    enc_list_eq enc_srt ser_srt (fun _ _ => rfl), enc_list_eq enc_atom ser_atom enc_atom_eq,
    asEnc_append, ← eapp_assoc]

theorem enc_fact_eq (e : Enc) (f : tfact) : enc_fact e f = eapp e (asEnc (ser_fact f)) := by
  simp only [enc_fact, ser_fact, tokv_eq, enc_term_eq, enc_list_eq enc_srt ser_srt (fun _ _ => rfl),
    asEnc_append, ← eapp_assoc]

theorem enc_func_eq (e : Enc) (f : cfunc) : enc_func e f = eapp e (asEnc (ser_func f)) := by
  simp only [enc_func, ser_func, tokv_eq, enc_cexpr_eq, enc_list_eq enc_str ser_str (fun _ _ => rfl),
    asEnc_append, ← eapp_assoc]

theorem enc_spec_eq (e : Enc) (s : tspec) : enc_spec e s = eapp e (asEnc (ser_spec s)) := by
  simp only [enc_spec, ser_spec, tokv_eq, enc_term_eq, enc_list_eq enc_srt ser_srt (fun _ _ => rfl),
    enc_list_eq enc_atom ser_atom enc_atom_eq, enc_list_eq enc_term ser_term (fun e t => enc_term_eq t e),
    asEnc_append, ← eapp_assoc]

theorem encInput_eq (i : tinput) : encInput i = asEnc (ser_input i) := by
  simp only [encInput, ser_input, tokv_eq, enc_spec_eq, enc_func_eq,
    enc_tail_eq enc_fact ser_fact enc_fact_eq, enc_tail_eq enc_rule ser_rule enc_rule_eq,
    enc_tail_eq enc_pred ser_pred enc_pred_eq, enc_tail_eq enc_sym ser_sym enc_sym_eq,
    asEnc_append, ← eapp_assoc]

/-- What an observation's proof needs: the encoder's answer, as two numbers,
is the serialization. -/
theorem ser_eq_of_enc (i : tinput) (len n : Nat) (h : encInput i = (len, n)) :
    ser_input i = bytes_of_nat len n := by
  rw [encInput_eq] at h
  simp only [asEnc, Prod.mk.injEq] at h
  rw [← h.1, ← h.2, bytes_of_nat_asEnc]

end TCheck
end Perennial
