/-
Port of `new/tcheck/syntax.v`.

# The input of the table-driven checker (tcheck/), and its serialization

Every type here mirrors one in tcheck/syntax.go, and `ser_input` writes
exactly the format tcheck/parse.go reads: the bytes that `tcheck.Check`
is run on.  A generated observation file (see `Observe.lean`) states that a
run of `Check` on some bytes returned `true`, and proves that those bytes
are `ser_input` of its input by computation; so nothing on the Go side
of the serialization has to be trusted.

Lean notes:
* The variable names of the code (`CVar`, `CLet`, `fn_params`) are Lean
  `String`s, the type of GooseLang's `Var` and `BNamed`, rather than Rocq's
  `go_string` taken through `go.go_string_to_string`: the code's denotation
  then is Goose's term itself, with nothing to convert, and the conversion
  moves to the serialization, `ser_str`, which writes a name's UTF-8 bytes
  (`ser_char`, by hand: `String.toUTF8` does not reduce in the kernel). UTF-8
  is injective, so `ser_input` stays injective on names.
* The digits of `ser_nat` are `BitVec.ofNat 8 (48 + n % 10)` (Rocq
  `W8 (Z.of_nat ..)`); the byte strings are `go!"…"` literals, which
  elaborate to explicit lists, so that `ser_input` of a closed input computes
  in the kernel (`decide`).
-/
import Perennial.Std.ByteString
import LCheck.TCheck.Syntax

namespace Perennial
namespace TCheck

-- The input's types (`srt`, `tterm`, ..., `tinput`): in LCheck/TCheck/Syntax.lean.

/-! ## Serialization -/

section ser

/-- Byte strings are joined right-nested (Rocq's `++` associates to the
right; Lean's to the left), with `List.append` itself rather than `++`'s
instance, so that the kernel computes `ser_input` of a closed input in time
linear in its length. -/
local infixr:65 " ⧺ " => List.append

def ser_digits : (fuel n : Nat) → (acc : GoString) → GoString
  | 0, _, acc => acc
  | fuel + 1, n, acc =>
      let d : w8 := BitVec.ofNat 8 (48 + n % 10)
      if n < 10 then d :: acc else ser_digits fuel (n / 10) (d :: acc)

def ser_nat (n : Nat) : GoString := ser_digits 20 n []

def ser_list {A : Type} (f : A → GoString) (l : List A) : GoString :=
  match l with
  | [] => go!"()"
  | x :: l => go!"(" ⧺ f x ⧺ l.foldr (fun y s => go!" " ⧺ f y ⧺ s) go!")"

/-- `" x1 .. xn"` -/
def ser_tail {A : Type} (f : A → GoString) (l : List A) : GoString :=
  l.foldr (fun y s => go!" " ⧺ f y ⧺ s) []

def ser_srt (s : srt) : GoString :=
  match s with
  | SVal => go!"v"
  | SType => go!"y"
  | SU n => go!"(u " ⧺ ser_nat n ⧺ go!")"

mutual
def ser_term : tterm → GoString
  | TVar n => go!"(var " ⧺ ser_nat n ⧺ go!")"
  | TSym n args => go!"(sym " ⧺ ser_nat n ⧺ ser_terms args ⧺ go!")"
  | TPair a b => go!"(pair " ⧺ ser_term a ⧺ go!" " ⧺ ser_term b ⧺ go!")"
  | TLit ty es => go!"(lit " ⧺ ser_term ty ⧺ ser_terms es ⧺ go!")"
  | TUnit => go!"unit"
/-- `" t1 .. tn"`: Rocq's `foldr (λ y s, " " ⧺ ser_term y ⧺ s) ")"` without
the `")"`, as a function of its own so that the recursion is structural. -/
def ser_terms : List tterm → GoString
  | [] => []
  | t :: ts => go!" " ⧺ ser_term t ⧺ ser_terms ts
end

def ser_pat : tpat → GoString
  | PVal t => go!"(pval " ⧺ ser_term t ⧺ go!")"
  | PApp a b => go!"(papp " ⧺ ser_pat a ⧺ go!" " ⧺ ser_pat b ⧺ go!")"

def ser_atom (a : tatom) : GoString :=
  match a with
  | APred n args => go!"(pred " ⧺ ser_nat n ⧺ ser_tail ser_term args ⧺ go!")"
  | AEq a b => go!"(eq " ⧺ ser_term a ⧺ go!" " ⧺ ser_term b ⧺ go!")"

/-- The UTF-8 encoding of a character. -/
def ser_char (c : Char) : GoString :=
  let n := c.toNat
  if n < 0x80 then [BitVec.ofNat 8 n]
  else if n < 0x800 then [BitVec.ofNat 8 (0xC0 + n / 0x40), BitVec.ofNat 8 (0x80 + n % 0x40)]
  else if n < 0x10000 then
    [BitVec.ofNat 8 (0xE0 + n / 0x1000), BitVec.ofNat 8 (0x80 + n / 0x40 % 0x40),
     BitVec.ofNat 8 (0x80 + n % 0x40)]
  else
    [BitVec.ofNat 8 (0xF0 + n / 0x40000), BitVec.ofNat 8 (0x80 + n / 0x1000 % 0x40),
     BitVec.ofNat 8 (0x80 + n / 0x40 % 0x40), BitVec.ofNat 8 (0x80 + n % 0x40)]

def ser_str (x : String) : GoString := go!"\"" ⧺ x.toList.flatMap ser_char ⧺ go!"\""

mutual
def ser_cexpr : cexpr → GoString
  | CVal t => go!"(val " ⧺ ser_term t ⧺ go!")"
  | CVar x => go!"(cvar " ⧺ ser_str x ⧺ go!")"
  | CApp a b => go!"(app " ⧺ ser_cexpr a ⧺ go!" " ⧺ ser_cexpr b ⧺ go!")"
  | CPair a b => go!"(cpair " ⧺ ser_cexpr a ⧺ go!" " ⧺ ser_cexpr b ⧺ go!")"
  | CLet x a b => go!"(let " ⧺ ser_str x ⧺ go!" " ⧺ ser_cexpr a ⧺ go!" " ⧺ ser_cexpr b ⧺ go!")"
  | CSeq a b => go!"(seq " ⧺ ser_cexpr a ⧺ go!" " ⧺ ser_cexpr b ⧺ go!")"
  | CLit ty es => go!"(clit " ⧺ ser_term ty ⧺ ser_cexprs es ⧺ go!")"
  | CDo a => go!"(do " ⧺ ser_cexpr a ⧺ go!")"
  | CRet a => go!"(ret " ⧺ ser_cexpr a ⧺ go!")"
  | CXSeq a b => go!"(xseq " ⧺ ser_cexpr a ⧺ go!" " ⧺ ser_cexpr b ⧺ go!")"
  | CXDo a => go!"(xdo " ⧺ ser_cexpr a ⧺ go!")"
/-- `" e1 .. en"` (as `ser_terms`). -/
def ser_cexprs : List cexpr → GoString
  | [] => []
  | e :: es => go!" " ⧺ ser_cexpr e ⧺ ser_cexprs es
end

def ser_sym (d : symdecl) : GoString :=
  go!"(sym " ⧺ ser_list ser_srt d.sd_args ⧺ go!" " ⧺ ser_srt d.sd_res ⧺ go!")"
def ser_pred (d : preddecl) : GoString :=
  go!"(pred " ⧺ (if d.pd_pers then go!"1" else go!"0") ⧺ go!" " ⧺ ser_list ser_srt d.pd_args ⧺
    go!")"
def ser_rule (r : trule) : GoString :=
  go!"(rule " ⧺ ser_list ser_srt r.r_vars ⧺ go!" " ⧺ ser_pat r.r_lhs ⧺ go!" " ⧺
  ser_list ser_atom r.r_pre ⧺ go!" " ⧺ ser_list ser_srt r.r_ex ⧺ go!" " ⧺
  ser_term r.r_ret ⧺ go!" " ⧺ ser_list ser_atom r.r_post ⧺ go!")"
def ser_fact (f : tfact) : GoString :=
  go!"(fact " ⧺ ser_list ser_srt f.f_vars ⧺ go!" " ⧺ ser_term f.f_lhs ⧺ go!" " ⧺
  ser_term f.f_rhs ⧺ go!")"
def ser_func (f : cfunc) : GoString :=
  go!"(func " ⧺ ser_list ser_str f.fn_params ⧺ go!" " ⧺ ser_cexpr f.fn_body ⧺ go!")"
def ser_spec (s : tspec) : GoString :=
  go!"(spec " ⧺ ser_list ser_srt s.sp_vars ⧺ go!" " ⧺ ser_list ser_term s.sp_args ⧺ go!" " ⧺
  ser_list ser_atom s.sp_pre ⧺ go!" " ⧺ ser_list ser_srt s.sp_ex ⧺ go!" " ⧺
  ser_term s.sp_ret ⧺ go!" " ⧺ ser_list ser_atom s.sp_post ⧺ go!")"

def ser_input (i : tinput) : GoString :=
  go!"(input (syms" ⧺ ser_tail ser_sym i.in_syms ⧺ go!") (preds" ⧺
  ser_tail ser_pred i.in_preds ⧺ go!") (rules" ⧺ ser_tail ser_rule i.in_rules ⧺
  go!") (facts" ⧺ ser_tail ser_fact i.in_facts ⧺ go!") " ⧺ ser_func i.in_func ⧺ go!" " ⧺
  ser_spec i.in_spec ⧺ go!")"

end ser

/-! ## Specifications as rules

A function's specification, as callers use it: the rule whose left-hand
side is the call `h a1 .. an`, where `h` is the value called (for a
method, `#(methods T m recv)`) and `a1 .. an` are the specification's
arguments after the first (the receiver, which `h` already contains). -/

def call_pat (h : tterm) (args : List tterm) : tpat :=
  args.foldl (fun p a => PApp p (PVal a)) (PVal h)

def spec_rule (h : tterm) (sp : tspec) : trule :=
  mkRule sp.sp_vars (call_pat h sp.sp_args.tail) sp.sp_pre sp.sp_ex sp.sp_ret sp.sp_post

end TCheck
end Perennial
