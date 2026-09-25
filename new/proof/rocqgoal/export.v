(** * A generic goal exporter: Rocq proof state -> S-expression.

    [export_goal ()] prints the focused goal -- every hypothesis of the Rocq
    context, then the conclusion -- as one S-expression over kernel terms.
    It knows nothing about Iris, GooseLang or Perennial: constants,
    inductives and constructors are written by their full kernel names, and
    recognizing them is left to the reader of the output. The reader in this
    repository is the Go package [gocheck/rocqgoal], which parses this format
    and recognizes the Iris proof mode structure (the two contexts, typed
    points-to facts, a WP) by name.

    The point is that nothing on this side has to change when the checker
    learns a new construct: reification happens in Go, untrusted, and the
    only thing a later import step has to trust is a kernel conversion check
    that the syntax it gets back denotes the goal.

    Format (a node per kernel term constructor; [n] is a decimal integer,
    [id] an identifier and [name] a dot-separated kernel path, neither of
    which contains a space, a parenthesis or a double quote):

<<
    goal ::= (Goal hyp* (Concl t))
    hyp  ::= (Hyp id t)                    hypothesis id : t
           | (Def id t t)                  let-bound hypothesis id := t : t
    b    ::= (id t) | (_ t)                a binder and its type
    t    ::= (R n)                         de Bruijn index, from 1
           | (V id)                        variable of the context
           | Prop | SProp | Set | Type     sorts (universe levels dropped)
           | (Pi b t) | (Lam b t) | (Let b t t)
           | (A t t+)                      application
           | (C name) | (I name) | (K name)   constant, inductive, constructor
           | (M name t t t* )               match on inductive name: the return
                                           clause, the scrutinee, the branches
           | (Fix n b+ t+) | (CoFix n b+ t+)
           | (Proj name t)                 primitive projection
           | (U n)                         primitive integer
           | Float                         primitive float (value dropped)
           | (Str s)                       primitive string, s a double-quoted
                                           literal: a double quote, a backslash
                                           and a byte outside 32-126 are
                                           escaped as in Go, the rest verbatim
           | (Arr t t t* )                 primitive array: its type, its
                                           default element, its elements
           | ?                             existential variable
>>

    Casts are dropped, and so are universe instances. The output is a tree:
    a subterm the kernel shares is printed once per occurrence. *)
From Ltac2 Require Import Ltac2.
From Ltac2 Require Pstring.
Import Ltac2.Constr.Unsafe.

Ltac2 export_path (r : Std.reference) : string :=
  String.concat "." (List.map Ident.to_string (Env.path r)).

Ltac2 export_int (n : int) : string := Message.to_string (Message.of_int n).

(** A primitive string as a Go-style quoted literal. *)
Ltac2 export_quote (s : string) : string :=
  let hex d := String.make 1 (Char.of_int (Int.add d (if Int.lt d 10 then 48 else 87))) in
  let escape c := String.concat "" ["\x"; hex (Int.div c 16); hex (Int.mod c 16)] in
  let rec go i acc :=
    if Int.equal i (String.length s) then String.concat "" (List.rev acc)
    else
      let c := Char.to_int (String.get s i) in
      let piece :=
        if Int.equal c 34 then "\"""
        else if Int.equal c 92 then "\\"
        else if Int.lt c 32 then escape c
        else if Int.le 127 c then escape c
        else String.make 1 (String.get s i) in
      go (Int.add i 1) (piece :: acc) in
  String.concat "" ["""" ; go 0 []; """"].

Ltac2 export_sort (c : constr) : string :=
  if Constr.equal c 'Prop then "Prop"
  else if Constr.equal c 'SProp then "SProp"
  else if Constr.equal c 'Set then "Set"
  else "Type".

(** Append the S-expression of [c] to [out], in reverse. *)
Ltac2 rec export_term (out : string list Ref.ref) (c : constr) : unit :=
  let emit s := Ref.set out (s :: Ref.get out) in
  let binder b :=
    emit "(";
    (match Constr.Binder.name b with
     | Some id => emit (Ident.to_string id)
     | None => emit "_"
     end);
    emit " "; export_term out (Constr.Binder.type b); emit ")" in
  let all a := Array.iter (fun x => emit " "; export_term out x) a in
  match kind c with
  | Rel n => emit "(R "; emit (export_int n); emit ")"
  | Var id => emit "(V "; emit (Ident.to_string id); emit ")"
  | Meta _ => emit "?"
  | Evar _ _ => emit "?"
  | Sort _ => emit (export_sort c)
  | Cast c _ _ => export_term out c
  | Prod b t => emit "(Pi "; binder b; emit " "; export_term out t; emit ")"
  | Lambda b t => emit "(Lam "; binder b; emit " "; export_term out t; emit ")"
  | LetIn b v t =>
      emit "(Let "; binder b; emit " "; export_term out v; emit " ";
      export_term out t; emit ")"
  | App f args => emit "(A "; export_term out f; all args; emit ")"
  | Constant k _ => emit "(C "; emit (export_path (Std.ConstRef k)); emit ")"
  | Ind i _ => emit "(I "; emit (export_path (Std.IndRef i)); emit ")"
  | Constructor k _ => emit "(K "; emit (export_path (Std.ConstructRef k)); emit ")"
  | Case ci (ret, _) _ scrut brs =>
      emit "(M "; emit (export_path (Std.IndRef (Case.inductive ci)));
      emit " "; export_term out ret; emit " "; export_term out scrut; all brs;
      emit ")"
  | Fix _ i bs bodies =>
      emit "(Fix "; emit (export_int i);
      Array.iter (fun b => emit " "; binder b) bs; all bodies; emit ")"
  | CoFix i bs bodies =>
      emit "(CoFix "; emit (export_int i);
      Array.iter (fun b => emit " "; binder b) bs; all bodies; emit ")"
  | Proj p _ c =>
      emit "(Proj ";
      (match Proj.to_constant p with
       | Some k => emit (export_path (Std.ConstRef k))
       | None =>
           emit (export_path (Std.IndRef (Proj.ind p))); emit "#";
           emit (export_int (Proj.index p))
       end);
      emit " "; export_term out c; emit ")"
  | Uint63 n => emit "(U "; emit (Message.to_string (Uint63.print n)); emit ")"
  | Float _ => emit "Float"
  | String s => emit "(Str "; emit (export_quote (Pstring.to_string s)); emit ")"
  | Array _ elems def ty =>
      emit "(Arr "; export_term out ty; emit " "; export_term out def; all elems;
      emit ")"
  end.

(** The focused goal: every hypothesis, oldest first, then the conclusion. *)
Ltac2 export_goal () : string :=
  let out := Ref.ref [] in
  let emit s := Ref.set out (s :: Ref.get out) in
  emit "(Goal";
  List.iter
    (fun (id, body, ty) =>
       match body with
       | Some v =>
           emit " (Def "; emit (Ident.to_string id); emit " "; export_term out v;
           emit " "; export_term out ty; emit ")"
       | None =>
           emit " (Hyp "; emit (Ident.to_string id); emit " "; export_term out ty;
           emit ")"
       end)
    (Control.hyps ());
  emit " (Concl "; export_term out (Control.goal ()); emit "))";
  String.concat "" (List.rev (Ref.get out)).

(** Print the export on a line of its own. *)
Ltac2 print_goal () : unit := Message.print (Message.of_string (export_goal ())).

(** Print a line [== tag], then the export on a line of its own: what
    [gocheck/rocqgoal/testdata/regen.sh] collects. *)
Ltac2 dump_goal (tag : string) : unit :=
  Message.print (Message.of_string (String.concat "" ["== "; tag]));
  print_goal ().

(** Print only the size of the export: for a build log. *)
Ltac2 report_goal (tag : string) : unit :=
  Message.print
    (Message.concat (Message.of_string (String.concat "" ["export "; tag; ": "]))
       (Message.concat (Message.of_int (String.length (export_goal ())))
          (Message.of_string " bytes"))).
