(** * Syntax of the module language

    A call-by-value λ-calculus with first-class modules (collections of
    bindings as values), constructors and pattern matching. *)
From Stdlib Require Import Utf8 String List.

Definition var := string.
Definition cstr := string.

Inductive tm :=
  | Var (x : var)
  | Fn (x : var) (e : tm)                 (* λx.e *)
  | App (e1 e2 : tm)
  | Link (e1 e2 : tm)                     (* e1 ⋊ e2 : evaluate e2 under the module e1 *)
  | Mt                                    (* ε : the empty module *)
  | Bind (x : var) (e1 e2 : tm)           (* x = e1; e2 : export x, then the module e2 *)
  | Cstr (c : cstr) (es : tms)            (* C e1 … en *)
  | Case (e : tm) (bs : branches)         (* match e { C x1 … xn → e' | … } *)
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
