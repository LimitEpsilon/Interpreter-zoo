From Coq Require Import Arith String List.
Import ListNotations.

Local Open Scope string_scope.

Inductive tm :=
  | Var (x : string)
  | Fn (x : string) (e : tm)
  | App (f a : tm)
  | Link (m e : tm)
  | Mt
  | Bind (x : string) (v m : tm)
.

Inductive env :=
  | Env (β : list (string * val)) (s : option shadow)

with val :=
  | Clos (x : string) (k : option val) (σ : env)
  | Mod (σ : env)
  | Shadow_val (s : shadow)

with shadow :=
  | Init
  | Read (s : shadow) (x : string)
  | Call (s : shadow) (v : val)
.

Local Notation "'⟨' 'λ' x k σ '⟩'" := (Clos x (Some k) σ) (at level 60, right associativity, only printing).
Local Notation "'⟨' 'λ' x '⊥' σ '⟩'" := (Clos x None σ) (at level 60, right associativity, only printing).
Local Notation "'⟨' σ '⟩'" := (Mod σ) (at level 60, right associativity, only printing).
Local Notation "'⟨' s '⟩'" := (Shadow_val s) (at level 60, right associativity, only printing).
Local Notation "'⟪' β  s '⟫'" := (Env β (Some s)) (at level 60, right associativity, only printing).
Local Notation "'⟪' β  • '⟫'" := (Env β None) (at level 60, right associativity, only printing).

Definition ω := Fn "x" (App (Var "x") (Var "x")).
Definition ι := Fn "x" (Var "x").
Definition α := Fn "f" (Fn "x" (App (Var "f") (Var "x"))).

Definition upd_env (σ : env) (x : string) (v : val) :=
  match σ with
  | Env β s => Env ((x, v) :: β) s
  end.

Definition app_env β σ :=
  match σ with
  | Env β' s => Env (β ++ β') s
  end.

Fixpoint read_list (β : list (string * val)) (x : string) :=
  match β with
  | [] => None
  | (x', v) :: β' =>
    if x =? x' then Some v else read_list β' x
  end.

Definition read_env (σ : env) (x : string) :=
  match σ with
  | Env β s =>
    match read_list β x with
    | Some v => Some v
    | None =>
      match s with
      | None => None
      | Some s => Some (Shadow_val (Read s x))
      end
    end
  end.

Definition eval (link : env -> val -> option val) :=
  fix eval (e : tm) : option val :=
  match e with
  | Var x => Some (Shadow_val (Read Init x))
  | Fn x M => Some (Clos x (eval M) (Env [] (Some Init)))
  | App M N =>
    match eval M, eval N with
    | Some (Clos x B σ), Some v =>
      match B with
      | Some k => link (upd_env σ x v) k
      | None => None
      end
    | Some (Shadow_val s), Some v => Some (Shadow_val (Call s v))
    | Some (Mod _), Some _
    | Some _, None | None, Some _ | None, None => None
    end
  | Link M N =>
    match eval M, eval N with
    | Some (Mod σ), Some v => link σ v
    | Some (Shadow_val s), Some v => link (Env [] (Some s)) v
    | Some (Clos _ _ _), Some _
    | Some _, None | None, Some _ | None, None => None
    end
  | Mt => Some (Mod (Env [] None))
  | Bind x M N =>
    match eval M, eval N with
    | Some v, Some σ =>
      match link (Env [(x, v)] (Some Init)) σ with
      | Some (Mod σ) => Some (Mod (upd_env σ x v))
      | Some (Shadow_val s) => Some (Mod (Env [(x, v)] (Some s)))
      | Some (Clos _ _ _) => None
      | None => None
      end
    | Some _, None | None, Some _ | None, None => None
    end
  end.

(* linking, up to n steps *)
Fixpoint link (n : nat) (σ : env) : val -> option val :=
  match n with 0 => (fun _ => None) | S n =>
  fix link_val v : option val :=
    match v with
    | Clos x k σ' =>
      match link_env σ' with
      | None => None
      | Some σ' => Some (Clos x k σ')
      end
    | Mod σ' =>
      match link_env σ' with
      | None => None
      | Some σ' => Some (Mod σ')
      end
    | Shadow_val s => link_shadow s
    end
  with link_env σ' : option env :=
    let fix link_list β :=
      match β with
      | [] => Some []
      | (x, v) :: β =>
        match link_val v, link_list β with
        | None, _ | _, None => None
        | Some v, Some β => Some ((x, v) :: β)
        end
      end
    in match σ' with
    | Env β None =>
      match link_list β with None => None | Some β => Some (Env β None) end
    | Env β (Some s) =>
      match link_list β, link_shadow s with
      | None, _ | _, None => None
      | Some _, Some (Clos _ _ _) => None
      | Some β, Some (Mod σ) => Some (app_env β σ)
      | Some β, Some (Shadow_val s) => Some (Env β (Some s))
      end
    end
  with link_shadow s : option val :=
    match s with
    | Init => Some (Mod σ)
    | Read s x =>
      match link_shadow s with
      | None | Some (Clos _ _ _) => None
      | Some (Mod σ) => read_env σ x
      | Some (Shadow_val s) => Some (Shadow_val (Read s x))
      end
    | Call s v =>
      match link_shadow s, link_val v with
      | None, _ | _, None | Some (Mod _), _ => None
      | Some (Clos x k σ), Some v =>
        match k with
        | None => None
        | Some k => link n (upd_env σ x v) k
        end
      | Some (Shadow_val s), Some v => Some (Shadow_val (Call s v))
      end
    end
  for link_val
  end.

Definition interp n := eval (link n).

Local Coercion Shadow_val : shadow >-> val.
Local Coercion Mod : env >-> val.
Compute interp 1 ω.
Compute interp 100 (App ω ω).
Compute interp 1 (App ι ι).
Definition test_module := Bind "app" α (Bind "id" ι Mt).
Definition open1 := App (Var "id") (Var "id").
Definition open2 := App (Var "app") (Var "id").
Definition compute_in_fun1 := Fn "x" (App (App ι ι) (Var "x")).
Definition compute_in_fun2 := Fn "x" (App ι (App ι (Var "x"))).
Compute interp 2 (Link test_module open1).
Compute interp 2 (Link test_module open2).
Compute interp 1 compute_in_fun1.
Compute interp 1 compute_in_fun2.

Definition bomb := Bind "w" ω Mt.
Definition bomber := Bind "div" (App (Var "w") (Var "w")) Mt.
Compute interp 1 (Link bomb (Link bomber Mt)).
Compute interp 100 (Link (Link bomb bomber) Mt).

