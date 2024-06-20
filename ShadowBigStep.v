From Coq Require Import Arith String List.
Import ListNotations.

Local Open Scope string_scope.
Unset Elimination Schemes.

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
  | Clos (x : string) (e : tm) (σ : env)
  | Mod (σ : env)
  | Shadow_val (s : shadow)

with shadow :=
  | Init
  | Read (s : shadow) (x : string)
  | Call (s : shadow) (v : val)
.

Local Notation "'⟨' 'λ' x e σ '⟩'" := (Clos x e σ) (at level 60, right associativity, only printing).
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

Inductive eval : env -> tm -> val -> Prop :=
  | ev_id σ x v (READ : read_env σ x = Some v)
  : eval σ (Var x) v
  | ev_fn σ x e
  : eval σ (Fn x e) (Clos x e σ)
  | ev_app σ e1 e2 x e σ1 v2 v v'
    (EVAL1 : eval σ e1 (Clos x e σ1))
    (EVAL2 : eval σ e2 v2)
    (EVAL3 : eval (Env [] (Some Init)) e v)
    (LINK : link (upd_env σ1 x v2) v v')
  : eval σ (App e1 e2) v'

with link : env -> val -> val -> Prop :=
  | link_Init σ
  : link σ (Shadow_val Init) (Mod σ)
  | link_Read_val σ s x σ' v
    (LINK : link σ (Shadow_val s) (Mod σ'))
    (READ : read_env σ' x = Some v)
  : link σ (Shadow_val (Read s x)) v
.

Section IND.
  Context (Pev : forall σ e v (EVAL : eval σ e v), Prop)
          (Plink : forall σ v v' (LINK : link σ v v'), Prop).
  Context (Pid : forall σ x v READ, Pev σ (Var x) v (ev_id σ x v READ))
          (Pfn : forall σ x e, Pev σ (Fn x e) (Clos x e σ) (ev_fn σ x e))
          (Papp : forall σ e1 e2 x e σ1 v2 v v' EVAL1 EVAL2 EVAL3 LINK,
            Plink (upd_env σ1 x v2) v v' LINK ->
            Pev σ (App e1 e2) v' (ev_app σ e1 e2 x e σ1 v2 v v' EVAL1 EVAL2 EVAL3 LINK))
          (PInit : forall σ, Plink σ (Shadow_val Init) (Mod σ) (link_Init σ))
          (PRead_val : forall σ s x σ' v LINK READ,
            Plink σ (Shadow_val s) (Mod σ') LINK ->
            Plink σ (Shadow_val (Read s x)) v (link_Read_val σ s x σ' v LINK READ)).

  Fixpoint ev_ind σ e v EVAL {struct EVAL} : Pev σ e v EVAL :=
    match EVAL with
    | ev_id σ x v READ => Pid σ x v READ
    | ev_fn σ x e => Pfn σ x e
    | ev_app σ e1 e2 x e σ1 v2 v v' EVAL1 EVAL2 EVAL3 LINK =>
      Papp σ e1 e2 x e σ1 v2 v v' EVAL1 EVAL2 EVAL3 LINK
      (link_ind (upd_env σ1 x v2) v v' LINK)
    end

  with link_ind σ v v' LINK {struct LINK} : Plink σ v v' LINK :=
    match LINK with
    | link_Init σ => PInit σ
    | link_Read_val σ s x σ' v LINK READ =>
      PRead_val σ s x σ' v LINK READ (link_ind σ (Shadow_val s) (Mod σ') LINK)
    end.
End IND.

