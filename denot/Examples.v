(** * Examples

    This file runs the denotation and the reference interpreter on the same
    terms, and compares the results. It also shows the denotation of open
    terms, and links a client with a module that runs first.

    ** Main definitions

    - [both]: the result of a closed term in the 2 semantics.
    - [link_then]: run a module, then link its environment into the
      denotation of a client. *)
From Stdlib Require Import Utf8 String List.
From Denot Require Import Syntax Anchor Domain Semantics Reference Lift Adequacy.
Local Open Scope string_scope.

(** The terms of the constructors [O], [S], [true] and [false]. *)
Definition O' := Cstr "O" tnil.
Definition S' e := Cstr "S" (tcons e tnil).
Definition T' := Cstr "true" tnil.
Definition F' := Cstr "false" tnil.

(** The term of a natural number. *)
Fixpoint num (n : nat) := match n with 0 => O' | S n' => S' (num n') end.

(** Print a value. A closure, a module and a shadow print as a tag. *)
Fixpoint show (v : vl) : string :=
  match v with
  | vl_cstr c vs => c ++ "(" ++ show_list vs ++ ")"
  | vl_clos _ _ _ => "<fun>"
  | vl_exp _ => "<module>"
  | vl_sh _ => "<shadow>"
  end
with show_list (vs : vls) : string :=
  match vs with vnil => "" | vcons v vs' => show v ++ show_list vs' end.

(** The result of a closed term in the denotation and in the interpreter. *)
Definition both n N e :=
  (option_map show (run n nv_mt e), option_map show (option_map lift (ev N e rnil))).

(** ** Recursive functions

    A binding is recursive, so [add] can call [add]. *)

(** [add = λm. λn. match m { O → n | S p → S (add p n) }] *)
Definition add :=
  Fn "m" (Fn "n"
    (Case (Var "m")
      (brcons "O" nil (Var "n")
      (brcons "S" ("p" :: nil) (S' (App (App (Var "add") (Var "p")) (Var "n")))
       brnil)))).

(** A module with the function [add] and the number 2, and a client that adds
    2 and 2. *)
Definition Arith := Bind "add" add (Bind "two" (num 2) Mt).
Definition client := App (App (Var "add") (Var "two")) (Var "two").
Definition prog := Link Arith client.

(** The 2 semantics give the same value for [prog], that is 4. *)
Example prog_agrees : run 12 nv_mt prog = option_map lift (ev 30 prog rnil).
Proof. vm_compute. reflexivity. Qed.

(** The 2 semantics give 4. *)
Eval vm_compute in both 12 30 prog.

(** ** Mutually recursive modules

    The module [Top] holds the modules [Even] and [Odd]. Each calls the
    function of the other through [Top]. *)

(** The term [a ⋊ b ⋊ c]. *)
Definition path3 a b c := Link (Link (Var a) (Var b)) (Var c).

(** [even = λx. match x { O → true | S n → (Top ⋊ Odd ⋊ odd) n }] *)
Definition even :=
  Fn "x" (Case (Var "x")
    (brcons "O" nil T'
    (brcons "S" ("n" :: nil) (App (path3 "Top" "Odd" "odd") (Var "n")) brnil))).

(** [odd = λx. match x { O → false | S n → (Top ⋊ Even ⋊ even) n }] *)
Definition odd :=
  Fn "x" (Case (Var "x")
    (brcons "O" nil F'
    (brcons "S" ("n" :: nil) (App (path3 "Top" "Even" "even") (Var "n")) brnil))).

(** [Top = (Even = (even = …; ε); Odd = (odd = …; ε); ε); ε] *)
Definition Top :=
  Bind "Top" (Bind "Even" (Bind "even" even Mt)
             (Bind "Odd" (Bind "odd" odd Mt) Mt)) Mt.

(** Apply [even] to the number [k]. *)
Definition is_even k := Link Top (App (path3 "Top" "Even" "even") (num k)).

(** The 2 semantics give the same value for 3. *)
Example even_agrees : run 20 nv_mt (is_even 3) = option_map lift (ev 40 (is_even 3) rnil).
Proof. vm_compute. reflexivity. Qed.

(** The 2 semantics give the same module for [Top]. *)
Example Top_agrees : run 20 nv_mt Top = option_map lift (ev 40 Top rnil).
Proof. vm_compute. reflexivity. Qed.

(** The number 3 is not even, and the number 4 is even. *)
Eval vm_compute in (both 20 40 (is_even 3), both 20 40 (is_even 4)).

(** ** A recursive functor

    The functor [F] takes a module [M] and gives a module with the function
    [go]. The function [go] applies [F] to [M] again. *)

(** [F = λM. (go = λx. match x { O → M ⋊ base | S n → (F M ⋊ go) n }; ε)] *)
Definition Fct :=
  Fn "M" (Bind "go" (Fn "x" (Case (Var "x")
     (brcons "O" nil (Link (Var "M") (Var "base"))
     (brcons "S" ("n" :: nil)
        (App (Link (App (Var "F") (Var "M")) (Var "go")) (Var "n")) brnil)))) Mt).

(** Apply [F] to a module whose [base] is 7, and call [go] at 2. *)
Definition functor_prog := Link (Bind "F" Fct Mt)
   (App (Link (App (Var "F") (Bind "base" (num 7) Mt)) (Var "go")) (num 2)).

(** The 2 semantics give the same value, that is 7. *)
Example functor_agrees :
  run 20 nv_mt functor_prog = option_map lift (ev 40 functor_prog rnil).
Proof. vm_compute. reflexivity. Qed.

(** ** Terms with no value *)

(** The term [λx. x x]. *)
Definition omega := Fn "x" (App (Var "x") (Var "x")).

(** The term [(λx. O) (ω ω)] has no result in call-by-value, in the 2
    semantics. *)
Eval vm_compute in both 8 50 (App (Fn "x" O') (App omega omega)).

(** The terms [x = x; ε] and [x = S x; ε] read [x] before its value exists.
    They have no value. *)
Eval vm_compute in
  (both 12 30 (Bind "x" (Var "x") Mt), both 12 30 (Bind "x" (S' (Var "x")) Mt)).

(** The denotation of [f x] is a call shadow. *)
Eval vm_compute in denote 3 (App (Var "f") (Var "x")).

(** The denotation of [(λx. O) (f y)] is [O] behind a guard. The guard holds
    the call [f y]. *)
Eval vm_compute in denote 3 (App (Fn "x" O') (App (Var "f") (Var "y"))).

(** The denotation of [match x { O → O | S p → p }] is a branch node on the
    shadow of [x]. *)
Eval vm_compute in
  denote 3 (Case (Var "x")
              (brcons "O" nil O' (brcons "S" ("p" :: nil) (Var "p") brnil))).

(** The denotation of [x = g (λy. x); ε] holds a recursive value whose body
    is a call shadow. The anchor of [x] is the index [B 0] under [wvl_mu]. In
    the guards it is the dead anchor [F 0]. *)
Eval vm_compute in denote 3 (Bind "x" (App (Var "g") (Fn "y" (Var "x"))) Mt).

(** ** Separate evaluation, then linking *)

(** Run a term, and give the environment of its module. *)
Definition env_of (e : tm) : option nv :=
  match run 8 nv_mt e with Some (vl_exp σ) => Some σ | _ => None end.

(** Run the module [m], then link its environment into the denotation of
    [client]. *)
Definition link_then (m : tm) (client : tm) : option vl :=
  match env_of m with Some σ => dest (linkb 20 σ (den client)) | None => None end.

(** The denotation of the client, linked with the module, gives the value of
    the whole term. *)
Example separate_arith :
  link_then Arith client = option_map lift (ev 30 prog rnil).
Proof. vm_compute. reflexivity. Qed.

(** A client with a binding that goes through the free variable [g]: [(x = g
    (λy. x); ε) ⋊ x O]. *)
Definition knot := Link (Bind "x" (App (Var "g") (Fn "y" (Var "x"))) Mt) (App (Var "x") O').

(** The client [knot] with a module that binds [g]. *)
Definition whole g := Link (Bind "g" g Mt) knot.

(** With [g = λh. h], the linked client and the whole term give the same
    closure. *)
Example separate_knot :
  link_then (Bind "g" (Fn "h" (Var "h")) Mt) knot =
  option_map lift (ev 40 (whole (Fn "h" (Var "h"))) rnil).
Proof. vm_compute. reflexivity. Qed.

(** With [g = λh. h], linking gives a closure. With [g = λh. h O], the call
    reads [x] before its value exists. Then the linked client and the whole
    term have no value. *)
Eval vm_compute in
  (option_map show (link_then (Bind "g" (Fn "h" (Var "h")) Mt) knot),
   option_map show (link_then (Bind "g" (Fn "h" (App (Var "h") O')) Mt) knot),
   both 20 40 (whole (Fn "h" (App (Var "h") O')))).

(** The term [(λx. O) (f y)]. Its result is [O], behind a guard that holds
    the call [f y]. *)
Definition guarded := App (Fn "x" O') (App (Var "f") (Var "y")).

(** A module that binds [f], and [y] to [O]. *)
Definition fy (f : tm) := Bind "f" f (Bind "y" O' Mt).

(** Link [guarded] with an [f] that does not return, and with an [f] that
    returns its argument. *)
Eval vm_compute in
  (option_map show (link_then (fy (Fn "z" (App omega omega))) guarded),
   option_map show (link_then (fy (Fn "z" (Var "z"))) guarded)).
