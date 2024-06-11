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
  | Clos (x : string) (k : list val) (σ : env)
  | Mod (σ : env)
  | Shadow_val (s : shadow)

with shadow :=
  | Init
  | Read (s : shadow) (x : string)
  | Call (s : shadow) (v : val)
.

Local Notation "'⟨' 'λ' x k σ '⟩'" := (Clos x k σ) (at level 60, right associativity, only printing).
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

Definition eval (link : env -> val -> list val) :=
  fix eval (e : tm) : list val :=
  match e with
  | Var x => [Shadow_val (Read Init x)]
  | Fn x M => [Clos x (eval M) (Env [] (Some Init))]
  | App M N =>
    let foldM acc fn :=
      let foldN acc' arg :=
        match fn with
        | Clos x B σ =>
          flat_map (link (upd_env σ x arg)) B ++ acc'
        | Shadow_val fn =>
          Shadow_val (Call fn arg) :: acc'
        | Mod _ => acc'
        end
      in fold_left foldN (eval N) acc
    in fold_left foldM (eval M) []
  | Link M N =>
    let foldM acc m :=
      let foldN acc' cli :=
        match m with
        | Mod σ =>
          link σ cli ++ acc'
        | Shadow_val m =>
          link (Env [] (Some m)) cli ++ acc'
        | Clos _ _ _ => acc'
        end
      in fold_left foldN (eval N) acc
    in fold_left foldM (eval M) []
  | Mt => [Mod (Env [] None)]
  | Bind x M N =>
    let foldM acc v :=
      let foldN acc' m :=
        let foldL acc'' m' :=
          match m' with
          | Mod σ => Mod (upd_env σ x v) :: acc''
          | Shadow_val s => Mod (Env [(x, v)] (Some s)) :: acc''
          | Clos _ _ _ => acc''
          end
        in fold_left foldL (link (Env [(x, v)] (Some Init)) m) acc'
      in fold_left foldN (eval N) acc
    in fold_left foldM (eval M) []
  end%list.

(* linking, up to n steps *)
Fixpoint link (n : nat) (σ : env) : val -> list val :=
  match n with 0 => (fun _ => []) | S n =>
  fix link_val v : list val :=
    match v with
    | Clos x k σ' => map (Clos x k) (link_env σ')
    | Mod σ' => map Mod (link_env σ')
    | Shadow_val s => link_shadow s
    end
  with link_env σ' : list env :=
    let fix link_list β :=
      match β with
      | [] => [[]] 
      | (x, v) :: β =>
        let foldv acc v :=
          let foldβ acc' β := ((x, v) :: β) :: acc'
          in fold_left foldβ (link_list β) acc
        in fold_left foldv (link_val v) []
      end
    in match σ' with
    | Env β None => map (fun β => Env β None) (link_list β)
    | Env β (Some s) =>
      let folds acc s :=
        let foldβ acc' β :=
          match s with
          | Mod σ => app_env β σ :: acc'
          | Shadow_val s => Env β (Some s) :: acc'
          | Clos _ _ _ => acc'
          end
        in fold_left foldβ (link_list β) acc
      in fold_left folds (link_shadow s) []
    end
  with link_shadow s : list val :=
    match s with
    | Init => [Mod σ]
    | Read s x =>
      let folds acc s :=
        match s with
        | Mod σ =>
          match read_env σ x with
          | None => acc
          | Some v => v :: acc
          end
        | Shadow_val s => Shadow_val (Read s x) :: acc
        | Clos _ _ _ => acc
        end
      in fold_left folds (link_shadow s) []
    | Call s v =>
      let folds acc s :=
        let foldv acc' v :=
          match s with
          | Clos x k σ =>
            flat_map (link n (upd_env σ x v)) k ++ acc'
          | Shadow_val s =>
            Shadow_val (Call s v) :: acc'
          | Mod _ => acc'
          end
        in fold_left foldv (link_val v) acc
      in fold_left folds (link_shadow s) []
    end
  for link_val
  end%list.

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

