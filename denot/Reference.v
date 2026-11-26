(** * The reference interpreter

    This file defines an interpreter with environments and fuel. It has no
    shadows, no traces and no linking, and a closure holds a term.
    [Adequacy.v] compares it with the denotation.

    For a binding [x = e1; e2], the interpreter evaluates [e1] with [x] bound
    to a fresh anchor. Then it binds [x] to the recursive value of the
    result. A read of [x] unrolls the recursive value. A read of [x] before
    [e1] returns gives no value.

    ** Main definitions

    - [rvl], [renv]: the values and the environments of the interpreter.
    - [rclose], [runr]: close an anchor, and replace an index by a recursive
      value.
    - [rread]: the value of a variable.
    - [ev]: the interpreter. *)
From Stdlib Require Import Utf8 String Bool Arith List.
From Denot Require Import Syntax Anchor.

(** A value of the interpreter is a module, a closure or a constructor value.
    An entry of an environment holds a value, a recursive value or an anchor. *)
Inductive rvl :=
  | r_exp (ρ : renv)                       (* a module *)
  | r_clos (x : var) (e : tm) (ρ : renv)
  | r_cstr (c : cstr) (vs : rvls)
with renv :=
  | rnil
  | rcons (x : var) (v : rvl) (ρ : renv)   (* x ↦ v *)
  | rmu (x : var) (v : rvl) (ρ : renv)     (* x ↦ μ.v *)
  | ran (x : var) (a : anc) (ρ : renv)     (* x ↦ an anchor *)
with rvls :=
  | rvnil
  | rvcons (v : rvl) (vs : rvls).

Scheme rvl_ind' := Induction for rvl Sort Prop
  with renv_ind' := Induction for renv Sort Prop
  with rvls_ind' := Induction for rvls Sort Prop.
Combined Scheme ref_mutind from rvl_ind', renv_ind', rvls_ind'.

(** Close an anchor. Under [k] recursive values, the name [ℓ] becomes the
    index [k]. *)
Fixpoint rclose (k : nat) (ℓ : loc) (v : rvl) : rvl :=
  match v with
  | r_exp ρ => r_exp (rclose_env k ℓ ρ)
  | r_clos x e ρ => r_clos x e (rclose_env k ℓ ρ)
  | r_cstr c vs => r_cstr c (rclose_list k ℓ vs)
  end
with rclose_env (k : nat) (ℓ : loc) (ρ : renv) : renv :=
  match ρ with
  | rnil => rnil
  | rcons x v ρ' => rcons x (rclose k ℓ v) (rclose_env k ℓ ρ')
  | rmu x v ρ' => rmu x (rclose (S k) ℓ v) (rclose_env k ℓ ρ')
  | ran x a ρ' => ran x (fclose ℓ k a) (rclose_env k ℓ ρ')
  end
with rclose_list (k : nat) (ℓ : loc) (vs : rvls) : rvls :=
  match vs with
  | rvnil => rvnil
  | rvcons v vs' => rvcons (rclose k ℓ v) (rclose_list k ℓ vs')
  end.

(** Replace the index [k] by the recursive value of [u]. *)
Fixpoint runr (k : nat) (u : rvl) (v : rvl) : rvl :=
  match v with
  | r_exp ρ => r_exp (runr_env k u ρ)
  | r_clos x e ρ => r_clos x e (runr_env k u ρ)
  | r_cstr c vs => r_cstr c (runr_list k u vs)
  end
with runr_env (k : nat) (u : rvl) (ρ : renv) : renv :=
  match ρ with
  | rnil => rnil
  | rcons x v ρ' => rcons x (runr k u v) (runr_env k u ρ')
  | rmu x v ρ' => rmu x (runr (S k) u v) (runr_env k u ρ')
  | ran x a ρ' =>
    match a with
    | B j => if Nat.eqb j k then rmu x u (runr_env k u ρ')
             else ran x a (runr_env k u ρ')
    | F _ => ran x a (runr_env k u ρ')
    end
  end
with runr_list (k : nat) (u : rvl) (vs : rvls) : rvls :=
  match vs with
  | rvnil => rvnil
  | rvcons v vs' => rvcons (runr k u v) (runr_list k u vs')
  end.

(** The largest name of a free anchor, or 0. *)
Fixpoint rsup (v : rvl) : nat :=
  match v with
  | r_exp ρ => rsup_env ρ
  | r_clos _ _ ρ => rsup_env ρ
  | r_cstr _ vs => rsup_list vs
  end
with rsup_env (ρ : renv) : nat :=
  match ρ with
  | rnil => 0
  | rcons _ v ρ' => Nat.max (rsup v) (rsup_env ρ')
  | rmu _ v ρ' => Nat.max (rsup v) (rsup_env ρ')
  | ran _ a ρ' => Nat.max (match a with F ℓ => ℓ | B _ => 0 end) (rsup_env ρ')
  end
with rsup_list (vs : rvls) : nat :=
  match vs with
  | rvnil => 0
  | rvcons v vs' => Nat.max (rsup v) (rsup_list vs')
  end.

(** The value of the variable [x]. A read of a recursive value unrolls it. A
    read of an anchor gives no value. *)
Fixpoint rread (x : var) (ρ : renv) : option rvl :=
  match ρ with
  | rnil => None
  | rcons x' v ρ' => if String.eqb x x' then Some v else rread x ρ'
  | rmu x' v ρ' => if String.eqb x x' then Some (runr 0 v v) else rread x ρ'
  | ran x' _ ρ' => if String.eqb x x' then None else rread x ρ'
  end.

(** The length of a list of values. *)
Fixpoint rlen (vs : rvls) : nat :=
  match vs with rvnil => 0 | rvcons _ vs' => S (rlen vs') end.

(** Bind the pattern variables to the fields of a constructor value. *)
Fixpoint rbind (xs : list var) (vs : rvls) (ρ : renv) : renv :=
  match xs, vs with
  | x :: xs', rvcons v vs' => rcons x v (rbind xs' vs' ρ)
  | _, _ => ρ
  end.

Section ev.
  Context (ev : tm → renv → option rvl).

  (** ** The interpreter *)

  (** Evaluate the arguments of a constructor from left to right. *)
  Fixpoint ev_list (es : tms) (ρ : renv) : option rvls :=
    match es with
    | tnil => Some rvnil
    | tcons e es' =>
      match ev e ρ with
      | Some v =>
        match ev_list es' ρ with
        | Some vs => Some (rvcons v vs)
        | None => None
        end
      | None => None
      end
    end.

  (** Evaluate the first branch for the constructor [c] with as many pattern
      variables as [vs] has values. *)
  Fixpoint ev_sel (c : cstr) (vs : rvls) (bs : branches) (ρ : renv) : option rvl :=
    match bs with
    | brnil => None
    | brcons c' xs e bs' =>
      if String.eqb c c' && Nat.eqb (rlen vs) (length xs)
      then ev e (rbind xs vs ρ)
      else ev_sel c vs bs' ρ
    end.

  (** The interpreter with one more unit of fuel than [ev]. *)
  Definition ev_step (e : tm) (ρ : renv) : option rvl :=
    match e with
    | Var x => rread x ρ
    | Fn x e' => Some (r_clos x e' ρ)
    | App e1 e2 =>
      match ev e1 ρ with
      | Some (r_clos x e' ρ') =>
        match ev e2 ρ with
        | Some a => ev e' (rcons x a ρ')
        | None => None
        end
      | _ => None
      end
    | Link e1 e2 =>
      match ev e1 ρ with
      | Some (r_exp ρ1) => ev e2 ρ1
      | _ => None
      end
    | Mt => Some (r_exp rnil)
    | Bind x e1 e2 =>
      let ℓ := S (rsup_env ρ) in             (* a fresh anchor *)
      match ev e1 (ran x (F ℓ) ρ) with
      | Some v1 =>
        let w := rclose 0 ℓ v1 in             (* x ↦ μ.v1 *)
        match ev e2 (rmu x w ρ) with
        | Some (r_exp ρ2) => Some (r_exp (rmu x w ρ2))
        | _ => None
        end
      | None => None
      end
    | Cstr c es =>
      match ev_list es ρ with
      | Some vs => Some (r_cstr c vs)
      | None => None
      end
    | Case e' bs =>
      match ev e' ρ with
      | Some (r_cstr c vs) => ev_sel c vs bs ρ
      | _ => None
      end
    end.
End ev.

(** The interpreter. [ev n e ρ] is the value of [e] in [ρ], or [None] when
    the fuel [n] is too small or [e] has no value. *)
Fixpoint ev (n : nat) : tm → renv → option rvl :=
  match n with
  | 0 => fun _ _ => None
  | S n' => ev_step (ev n')
  end.
