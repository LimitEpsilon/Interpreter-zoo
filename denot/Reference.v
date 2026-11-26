(** * The reference interpreter

    This file defines an interpreter with environments and fuel. It has no
    shadows, no traces and no linking, and a closure holds a term.
    [Adequacy.v] compares it with the denotation.

    For a binding [x = e1; e2], the interpreter evaluates [e1] with [x] bound
    to a fresh anchor. Then it binds [x] to the recursive value of the
    result. A read of [x] unrolls the recursive value. A read of [x] before
    [e1] returns gives no value.

    ** Main definitions

    - [rvl], [renv], [rwvl]: the values, the environments and the weak values
      of the interpreter.
    - [rclose], [runr]: close an anchor, and replace an index by a recursive
      value.
    - [rforce]: the value of a weak value.
    - [rread]: the value of a variable.
    - [ev]: the interpreter.

    ** Notes

    - [rw_v] is a coercion. Thus [rcons x v ρ] is the entry of the value
      [v]. *)
From Stdlib Require Import Utf8 String Bool Arith List.
From Denot Require Import Syntax Anchor.

(** A value of the interpreter is a module, a closure or a constructor value.
    An entry of an environment binds a variable to a weak value. A weak value
    is a value, a recursive value or an anchor. *)
Inductive rvl :=
  | r_exp (ρ : renv)                       (* a module *)
  | r_clos (x : var) (e : tm) (ρ : renv)
  | r_cstr (c : cstr) (vs : rvls)
with renv :=
  | rnil
  | rcons (x : var) (w : rwvl) (ρ : renv)  (* the entry x ↦ w *)
with rwvl :=
  | rw_v (v : rvl)                         (* a value *)
  | rw_mu (v : rvl)                        (* μ.v, a recursive value *)
  | rw_an (a : anc)                        (* an anchor *)
with rvls :=
  | rvnil
  | rvcons (v : rvl) (vs : rvls).

Scheme rvl_ind' := Induction for rvl Sort Prop
  with renv_ind' := Induction for renv Sort Prop
  with rwvl_ind' := Induction for rwvl Sort Prop
  with rvls_ind' := Induction for rvls Sort Prop.
Combined Scheme ref_mutind from rvl_ind', renv_ind', rwvl_ind', rvls_ind'.

(** A value is a weak value. *)
Coercion rw_v : rvl >-> rwvl.

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
  | rcons x w ρ' => rcons x (rclose_wvl k ℓ w) (rclose_env k ℓ ρ')
  end
with rclose_wvl (k : nat) (ℓ : loc) (w : rwvl) : rwvl :=
  match w with
  | rw_v v => rw_v (rclose k ℓ v)
  | rw_mu v => rw_mu (rclose (S k) ℓ v)
  | rw_an a => rw_an (fclose ℓ k a)
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
  | rcons x w ρ' => rcons x (runr_wvl k u w) (runr_env k u ρ')
  end
with runr_wvl (k : nat) (u : rvl) (w : rwvl) : rwvl :=
  match w with
  | rw_v v => rw_v (runr k u v)
  | rw_mu v => rw_mu (runr (S k) u v)
  | rw_an a =>
    match a with
    | B j => if Nat.eqb j k then rw_mu u else w
    | F _ => w
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
  | rcons _ w ρ' => Nat.max (rsup_wvl w) (rsup_env ρ')
  end
with rsup_wvl (w : rwvl) : nat :=
  match w with
  | rw_v v => rsup v
  | rw_mu v => rsup v
  | rw_an a => match a with F ℓ => ℓ | B _ => 0 end
  end
with rsup_list (vs : rvls) : nat :=
  match vs with
  | rvnil => 0
  | rvcons v vs' => Nat.max (rsup v) (rsup_list vs')
  end.

(** The value of a weak value. A value gives itself. A recursive value gives
    its unrolling. An anchor gives no value. *)
Definition rforce (w : rwvl) : option rvl :=
  match w with
  | rw_v v => Some v
  | rw_mu v => Some (runr 0 v v)
  | rw_an _ => None
  end.

(** The value of the variable [x], that is the value of the weak value of the
    first entry for [x]. *)
Fixpoint rread (x : var) (ρ : renv) : option rvl :=
  match ρ with
  | rnil => None
  | rcons x' w ρ' => if String.eqb x x' then rforce w else rread x ρ'
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
      match ev e1 (rcons x (rw_an (F ℓ)) ρ) with
      | Some v1 =>
        let w := rw_mu (rclose 0 ℓ v1) in     (* the recursive value μ.v1 *)
        match ev e2 (rcons x w ρ) with
        | Some (r_exp ρ2) => Some (r_exp (rcons x w ρ2))
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
