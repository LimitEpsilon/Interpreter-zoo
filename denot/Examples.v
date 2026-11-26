(** * Examples: the two semantics side by side *)
From Stdlib Require Import Utf8 String List.
From Denot Require Import Syntax Domain Semantics Reference Lift Adequacy.
Local Open Scope string_scope.

Definition O' := Cstr "O" tnil.
Definition S' e := Cstr "S" (tcons e tnil).
Fixpoint num (n : nat) := match n with 0 => O' | S n' => S' (num n') end.

(** Recursion comes from a call-by-value fixed-point combinator. *)
Definition Z :=
  Fn "f" (App (Fn "x" (App (Var "f") (Fn "v" (App (App (Var "x") (Var "x")) (Var "v")))))
              (Fn "x" (App (Var "f") (Fn "v" (App (App (Var "x") (Var "x")) (Var "v")))))).

(** add = fix (λadd. λm. λn. match m { O → n | S p → S (add p n) }) *)
Definition add :=
  App Z (Fn "add" (Fn "m" (Fn "n"
    (Case (Var "m")
      (brcons "O" nil (Var "n")
      (brcons "S" ("p" :: nil) (S' (App (App (Var "add") (Var "p")) (Var "n")))
       brnil)))))).

(** A module exporting [add] and [two], and a client that imports it. *)
Definition Arith := Bind "add" add (Bind "two" (num 2) Mt).
Definition client := App (App (Var "add") (Var "two")) (Var "two").
Definition prog := Link Arith client.

Definition omega := Fn "x" (App (Var "x") (Var "x")).

(** ** Closed programs: both semantics compute the same thing *)

Example prog_agrees : run 12 nv_mt prog = option_map lift (ev 30 prog rnil).
Proof. vm_compute. reflexivity. Qed.

Eval vm_compute in ev 30 prog rnil.

(** [(λx. O) (ω ω)] diverges in call-by-value, in both semantics. *)
Eval vm_compute in
  (run 8 nv_mt (App (Fn "x" O') (App omega omega)),
   ev 50 (App (Fn "x" O') (App omega omega)) rnil).

(** ** Open programs: the denotation needs no environment *)

(** [f x] : a pending call of the unknown [f]. *)
Eval vm_compute in denote 3 (App (Var "f") (Var "x")).

(** [(λx. O) (f y)] : the result is [O], but only once [f y] has returned.
    The pending call is kept in a guard. *)
Eval vm_compute in denote 3 (App (Fn "x" O') (App (Var "f") (Var "y"))).

(** [match x { O → O | S p → p }] : a branch on the unknown [x]. *)
Eval vm_compute in
  denote 3 (Case (Var "x")
              (brcons "O" nil O' (brcons "S" ("p" :: nil) (Var "p") brnil))).

(** ** Separate evaluation, then linking

    The client is denoted on its own; the module is run on its own; linking
    the module's environment into the client's denotation gives 4. *)

Definition client_den : body := den client.

Definition arith_env : option nv :=
  match run 6 nv_mt Arith with Some (vl_exp σ) => Some σ | _ => None end.

Fixpoint show (v : vl) : string :=
  match v with
  | vl_cstr c vs => c ++ "(" ++ show_list vs ++ ")"
  | vl_clos _ _ _ => "<fun>"
  | vl_exp _ => "<module>"
  | vl_sh _ => "<shadow>"
  end
with show_list (vs : vls) : string :=
  match vs with vnil => "" | vcons v vs' => show v ++ show_list vs' end.

Eval vm_compute in
  match arith_env with
  | Some σ => option_map show (dest (linkb 12 σ client_den))
  | None => None
  end.

(** The same guard at work: link [(λx. O) (f y)] with an [f] that diverges
    and with one that returns. *)
Definition guarded := App (Fn "x" O') (App (Var "f") (Var "y")).
Definition env_of (f : tm) : option nv :=
  match run 6 nv_mt (Bind "f" f (Bind "y" O' Mt)) with
  | Some (vl_exp σ) => Some σ
  | _ => None
  end.

Eval vm_compute in
  (match env_of (Fn "z" (App omega omega)) with
   | Some σ => option_map show (dest (linkb 20 σ (den guarded)))
   | None => Some "no env"
   end,
   match env_of (Fn "z" (Var "z")) with
   | Some σ => option_map show (dest (linkb 20 σ (den guarded)))
   | None => Some "no env"
   end).
