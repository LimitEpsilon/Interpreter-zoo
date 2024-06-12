Require Import String.

#[bypass_check(guard)]
Fixpoint magic (x : nat) : False := magic x.

Goal False.
  exact (magic 0).
Abort.

#[bypass_check(positivity)]
Inductive D := Fix (f : D -> D).

Fixpoint magic_ind (d : D) : False :=
  match d with
  | Fix f => magic_ind (f d)
  end.

Fixpoint inhab (d : D) : D :=
  match d with
  | Fix f => Fix (fun d => inhab (f d))
  end.

Goal False.
  exact (magic_ind (Fix inhab)).
Abort.

(* test locality of bypass_check *)
Definition var := string.

Inductive tm := Var (x : var) | Lam (x : var) (e : tm) | App (e1 e2 : tm).

Inductive value := Clos (x : var) (e : tm) (σ : var -> option value).

Definition env := var -> option value.

Fixpoint eval (e : tm) (σ : env) {struct e} : option value.
Proof.
  exact (
  match e with
  | Var x => σ x
  | Lam x e => Some (Clos x e σ)
  | App e1 e2 =>
    match eval e1 σ, eval e2 σ with
    | Some (Clos x e σ), Some v =>
      eval e (fun x' => if x =? x' then Some v else σ x')%string
    | _, _ => None
    end
  end).
Fail Qed.

