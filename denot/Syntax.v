(** * Terms

    This file defines the terms of the language. Each other file uses it.

    ** Main definitions

    - [tm]: a term.
    - [tm_mutind]: the mutual induction principle for terms, lists of terms
      and lists of branches. *)
From Stdlib Require Import Utf8 String List.

(** The name of a variable. *)
Definition var := string.

(** The name of a constructor. *)
Definition cstr := string.

(** A term. A list of terms holds the arguments of a constructor. A list of
    branches holds the branches of a match, each with a constructor, its
    pattern variables and a term. *)
Inductive tm :=
  | Var (x : var)
  | Fn (x : var) (e : tm)                 (* λx.e *)
  | App (e1 e2 : tm)
  | Link (e1 e2 : tm)                     (* [e1 ⋊ e2]: evaluate [e2] in the module of [e1] *)
  | Mt                                    (* [ε]: the empty module *)
  | Bind (x : var) (e1 e2 : tm)           (* [x = e1; e2]: bind [x], then the module of [e2] *)
  | Cstr (c : cstr) (es : tms)            (* [C e1 … en] *)
  | Case (e : tm) (bs : branches)         (* [match e { C x1 … xn → e' | … }] *)
with tms :=
  | tnil
  | tcons (e : tm) (es : tms)
with branches :=
  | brnil
  | brcons (c : cstr) (xs : list var) (e : tm) (bs : branches).

Scheme tm_ind' := Induction for tm Sort Prop
  with tms_ind' := Induction for tms Sort Prop
  with branches_ind' := Induction for branches Sort Prop.
Combined Scheme tm_mutind from tm_ind', tms_ind', branches_ind'.
