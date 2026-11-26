(** * The reference interpreter

    A completely standard environment-passing, call-by-value definitional
    interpreter with fuel.  It knows nothing about shadows, traces or
    linking: closures hold syntax. *)
From Stdlib Require Import Utf8 String Bool Arith List.
From Denot Require Import Syntax.

Inductive rvl :=
  | r_exp (ρ : renv)                       (* a module *)
  | r_clos (x : var) (e : tm) (ρ : renv)
  | r_cstr (c : cstr) (vs : rvls)
with renv :=
  | rnil
  | rcons (x : var) (v : rvl) (ρ : renv)
with rvls :=
  | rvnil
  | rvcons (v : rvl) (vs : rvls).

Scheme rvl_ind' := Induction for rvl Sort Prop
  with renv_ind' := Induction for renv Sort Prop
  with rvls_ind' := Induction for rvls Sort Prop.
Combined Scheme ref_mutind from rvl_ind', renv_ind', rvls_ind'.

Fixpoint rread (x : var) (ρ : renv) : option rvl :=
  match ρ with
  | rnil => None
  | rcons x' v ρ' => if String.eqb x x' then Some v else rread x ρ'
  end.

Fixpoint rlen (vs : rvls) : nat :=
  match vs with rvnil => 0 | rvcons _ vs' => S (rlen vs') end.

Fixpoint rbind (xs : list var) (vs : rvls) (ρ : renv) : renv :=
  match xs, vs with
  | x :: xs', rvcons v vs' => rcons x v (rbind xs' vs' ρ)
  | _, _ => ρ
  end.

Section ev.
  (** one more unit of fuel, given the interpreter with [n] units *)
  Context (ev : tm → renv → option rvl).

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

  Fixpoint ev_sel (c : cstr) (vs : rvls) (bs : branches) (ρ : renv) : option rvl :=
    match bs with
    | brnil => None
    | brcons c' xs e bs' =>
      if String.eqb c c' && Nat.eqb (rlen vs) (length xs)
      then ev e (rbind xs vs ρ)
      else ev_sel c vs bs' ρ
    end.

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
      match ev e1 ρ with
      | Some v =>
        match ev e2 (rcons x v ρ) with
        | Some (r_exp ρ2) => Some (r_exp (rcons x v ρ2))
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

Fixpoint ev (n : nat) : tm → renv → option rvl :=
  match n with
  | 0 => fun _ _ => None
  | S n' => ev_step (ev n')
  end.
