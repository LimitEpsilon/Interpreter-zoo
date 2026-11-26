(** * Semantic domain

    Everything here is an ordinary inductive type.  A closure does not hold
    syntax and does not hold a Coq function on values: it holds the
    denotation of its body, a [nat]-indexed family of finite traces. *)
From Stdlib Require Import Utf8 String Bool Arith List.
From Denot Require Import Syntax.

(** Shadows are computations blocked on the unknown environment [Init]. *)
Inductive shdw :=
  | Init                                   (* the unknown environment *)
  | Read (s : shdw) (x : var)              (* project x out of the module s *)
  | Call (s : shdw) (v : vl)               (* apply the unknown function s *)
  | Dstr (s : shdw) (c : cstr) (i : nat)   (* i-th field of s, if s is a C *)
with nv :=
  | nv_mt                                  (* • *)
  | nv_sh (s : shdw)                       (* [s] : a module that is still unknown *)
  | nv_bd (x : var) (v : vl) (σ : nv)
with vl :=
  | vl_exp (σ : nv)                        (* a module *)
  | vl_sh (s : shdw)
  | vl_clos (x : var) (b : nat → trace) (σ : nv)
  | vl_cstr (c : cstr) (vs : vls)
with vls :=
  | vnil
  | vcons (v : vl) (vs : vls)
(** Finite traces.  [Bot] is "no information yet". *)
with trace :=
  | Bot
  | Ret (v : vl)
  | Guard (v : vl) (t : trace)             (* v must be resolved before t *)
  | Match (s : shdw) (bs : brs)            (* branch on the unknown s *)
with brs :=
  | bnil
  | bcons (c : cstr) (n : nat) (t : trace) (bs : brs).

Scheme shdw_ind' := Induction for shdw Sort Prop
  with nv_ind' := Induction for nv Sort Prop
  with vl_ind' := Induction for vl Sort Prop
  with vls_ind' := Induction for vls Sort Prop
  with trace_ind' := Induction for trace Sort Prop
  with brs_ind' := Induction for brs Sort Prop.
Combined Scheme dom_mutind from
  shdw_ind', nv_ind', vl_ind', vls_ind', trace_ind', brs_ind'.

(** The denotation of a function body. *)
Definition body := nat → trace.

Fixpoint read (x : var) (σ : nv) : option vl :=
  match σ with
  | nv_mt => None
  | nv_sh s => Some (vl_sh (Read s x))
  | nv_bd x' v σ' => if String.eqb x x' then Some v else read x σ'
  end.

Fixpoint vnth (i : nat) (vs : vls) {struct vs} : option vl :=
  match vs with
  | vnil => None
  | vcons v vs' => match i with 0 => Some v | S i' => vnth i' vs' end
  end.

Fixpoint vlen (vs : vls) : nat :=
  match vs with vnil => 0 | vcons _ vs' => S (vlen vs') end.

(** Bind pattern variables to the fields of a known constructor … *)
Fixpoint bindV (xs : list var) (vs : vls) (σ : nv) : nv :=
  match xs, vs with
  | x :: xs', vcons v vs' => nv_bd x v (bindV xs' vs' σ)
  | _, _ => σ
  end.

(** … or to the fields of an unknown one. *)
Fixpoint bindD (xs : list var) (s : shdw) (c : cstr) (i : nat) (σ : nv) : nv :=
  match xs with
  | nil => σ
  | x :: xs' => nv_bd x (vl_sh (Dstr s c i)) (bindD xs' s c (S i) σ)
  end.

(** Monadic bind on traces: graft [k] at every leaf. *)
Fixpoint bind (k : vl → trace) (t : trace) : trace :=
  match t with
  | Bot => Bot
  | Ret v => k v
  | Guard u t' => Guard u (bind k t')
  | Match s bs => Match s (bind_brs k bs)
  end
with bind_brs (k : vl → trace) (bs : brs) : brs :=
  match bs with
  | bnil => bnil
  | bcons c n t bs' => bcons c n (bind k t) (bind_brs k bs')
  end.

(** What a finished, unbranched trace returns. *)
Fixpoint dest (t : trace) : option vl :=
  match t with
  | Bot => None
  | Ret v => Some v
  | Guard _ t' => dest t'
  | Match _ _ => None
  end.

(** Continuations that expect a module, or a constructor. *)
Definition on_env (k : nv → trace) (m : vl) : trace :=
  match m with vl_exp σ => k σ | _ => Bot end.

Definition on_mod (k : nv → trace) (m : vl) : trace :=
  match m with vl_exp σ => k σ | vl_sh s => k (nv_sh s) | _ => Bot end.

Definition on_cstr (k : cstr → vls → trace) (m : vl) : trace :=
  match m with vl_cstr c vs => k c vs | _ => Bot end.

(** Induction over values only, and over traces only. *)
Lemma val_mutind (P : shdw → Prop) (P0 : nv → Prop) (P1 : vl → Prop) (P2 : vls → Prop)
  (HInit : P Init)
  (HRead : ∀ s x, P s → P (Read s x))
  (HCall : ∀ s v, P s → P1 v → P (Call s v))
  (HDstr : ∀ s c i, P s → P (Dstr s c i))
  (Hmt : P0 nv_mt)
  (Hsh : ∀ s, P s → P0 (nv_sh s))
  (Hbd : ∀ x v σ, P1 v → P0 σ → P0 (nv_bd x v σ))
  (Hexp : ∀ σ, P0 σ → P1 (vl_exp σ))
  (Hvsh : ∀ s, P s → P1 (vl_sh s))
  (Hclos : ∀ x b σ, P0 σ → P1 (vl_clos x b σ))
  (Hcstr : ∀ c vs, P2 vs → P1 (vl_cstr c vs))
  (Hnil : P2 vnil)
  (Hcons : ∀ v vs, P1 v → P2 vs → P2 (vcons v vs)) :
  (∀ s, P s) ∧ (∀ σ, P0 σ) ∧ (∀ v, P1 v) ∧ (∀ vs, P2 vs).
Proof.
  pose proof (dom_mutind P P0 P1 P2 (fun _ => True) (fun _ => True)) as H.
  assert ((∀ s, P s) ∧ (∀ σ, P0 σ) ∧ (∀ v, P1 v) ∧ (∀ vs, P2 vs) ∧
          (∀ t : trace, True) ∧ (∀ bs : brs, True)) as H'.
  { apply H; auto. }
  intuition.
Qed.

Lemma tr_mutind (P : trace → Prop) (Q : brs → Prop)
  (HBot : P Bot)
  (HRet : ∀ v, P (Ret v))
  (HGuard : ∀ u t, P t → P (Guard u t))
  (HMatch : ∀ s bs, Q bs → P (Match s bs))
  (Hbnil : Q bnil)
  (Hbcons : ∀ c n t bs, P t → Q bs → Q (bcons c n t bs)) :
  (∀ t, P t) ∧ (∀ bs, Q bs).
Proof.
  pose proof (dom_mutind (fun _ => True) (fun _ => True) (fun _ => True)
                (fun _ => True) P Q) as H.
  assert ((∀ s : shdw, True) ∧ (∀ σ : nv, True) ∧ (∀ v : vl, True) ∧
          (∀ vs : vls, True) ∧ (∀ t, P t) ∧ (∀ bs, Q bs)) as H'.
  { apply H; auto. }
  intuition.
Qed.
