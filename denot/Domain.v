(** * Semantic domain

    This file defines shadows, environments, values and traces, and the
    operations on them. Each type is inductive. A closure holds the
    denotation of its body, that is one finite trace for each fuel.

    Open, close and unroll are structural recursions. They do not change the
    body of a closure, because a body has no anchor of a binding around it.

    ** Main definitions

    - [shdw], [nv], [vl], [trace]: shadows, environments, values and traces.
    - [am_vl]: apply a function to each anchor of a value. Open, close and
      rename are instances.
    - [su_vl]: replace anchors by recursive values. [unroll] is an instance.
    - [fresh]: a name that is fresh for an environment and a value.
    - [read]: the value of a variable in an environment.
    - [bind]: put a trace at each leaf of a trace.
    - [tmap], [ren_tr], [killg]: change the values of a trace.
    - [dest]: the result of a finished trace.
    - [val_mutind], [tr_mutind]: induction on values only, and on traces
      only. *)
From Stdlib Require Import Utf8 String Bool Arith List.
From Denot Require Import Syntax Anchor.

(** The 6 mutual types of the domain.
    - A shadow is a computation that waits for the unknown environment.
    - An environment is a list of entries, or a shadow that stands for a
      module.
    - A value is a module, a shadow, a closure or a constructor value.
    - A trace is a finite tree. Its leaves are values. *)
Inductive shdw :=
  | Init                                   (* the unknown environment *)
  | Read (s : shdw) (x : var)              (* variable [x] of the module [s] *)
  | Call (s : shdw) (v : vl)               (* the result of the function [s] at [v] *)
  | Dstr (s : shdw) (c : cstr) (i : nat)   (* field [i] of [s], when [s] is a [c] *)
with nv :=
  | nv_mt                                  (* • *)
  | nv_sh (s : shdw)                       (* a module that is a shadow *)
  | nv_bd (x : var) (v : vl) (σ : nv)      (* x ↦ v *)
  | nv_mu (x : var) (v : vl) (σ : nv)      (* x ↦ μ.v, a recursive value *)
  | nv_an (x : var) (a : anc) (σ : nv)     (* x ↦ an anchor *)
with vl :=
  | vl_exp (σ : nv)                        (* a module *)
  | vl_sh (s : shdw)
  | vl_clos (x : var) (b : nat → trace) (σ : nv)
  | vl_cstr (c : cstr) (vs : vls)
with vls :=
  | vnil
  | vcons (v : vl) (vs : vls)
with trace :=
  | Bot
  | Ret (v : vl)
  | Guard (v : vl) (t : trace)             (* resolve [v] before [t] *)
  | Match (s : shdw) (bs : brs)            (* branch on the shadow [s] *)
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

(** A body, that is one trace for each fuel. *)
Definition body := nat → trace.

(** ** Anchors *)

(** Apply [f] to each anchor. The number [k] counts the recursive values
    around the anchor. *)
Fixpoint am_shdw (f : nat → anc → anc) (k : nat) (s : shdw) : shdw :=
  match s with
  | Init => Init
  | Read s' x => Read (am_shdw f k s') x
  | Call s' v => Call (am_shdw f k s') (am_vl f k v)
  | Dstr s' c i => Dstr (am_shdw f k s') c i
  end
with am_nv (f : nat → anc → anc) (k : nat) (σ : nv) : nv :=
  match σ with
  | nv_mt => nv_mt
  | nv_sh s => nv_sh (am_shdw f k s)
  | nv_bd x v σ' => nv_bd x (am_vl f k v) (am_nv f k σ')
  | nv_mu x v σ' => nv_mu x (am_vl f (S k) v) (am_nv f k σ')
  | nv_an x a σ' => nv_an x (f k a) (am_nv f k σ')
  end
with am_vl (f : nat → anc → anc) (k : nat) (v : vl) : vl :=
  match v with
  | vl_exp σ => vl_exp (am_nv f k σ)
  | vl_sh s => vl_sh (am_shdw f k s)
  | vl_clos x b σ => vl_clos x b (am_nv f k σ)
  | vl_cstr c vs => vl_cstr c (am_vls f k vs)
  end
with am_vls (f : nat → anc → anc) (k : nat) (vs : vls) : vls :=
  match vs with
  | vnil => vnil
  | vcons v vs' => vcons (am_vl f k v) (am_vls f k vs')
  end.

Set Warnings "-notation-for-abbreviation".

(** The 3 instances of [am_vl] for anchors.
    - [open_vl i ℓ]: the index [i] becomes the name [ℓ].
    - [close_vl i ℓ]: the name [ℓ] becomes the index [i].
    - [ren_vl ξ]: rename the free anchors with [ξ]. *)
Notation open_shdw i ℓ := (am_shdw (fopen ℓ) i) (only parsing).
Notation open_nv i ℓ := (am_nv (fopen ℓ) i) (only parsing).
Notation open_vl i ℓ := (am_vl (fopen ℓ) i) (only parsing).
Notation open_vls i ℓ := (am_vls (fopen ℓ) i) (only parsing).
Notation close_shdw i ℓ := (am_shdw (fclose ℓ) i) (only parsing).
Notation close_nv i ℓ := (am_nv (fclose ℓ) i) (only parsing).
Notation close_vl i ℓ := (am_vl (fclose ℓ) i) (only parsing).
Notation close_vls i ℓ := (am_vls (fclose ℓ) i) (only parsing).
Notation ren_shdw ξ := (am_shdw (fren ξ) 0) (only parsing).
Notation ren_nv ξ := (am_nv (fren ξ) 0) (only parsing).
Notation ren_vl ξ := (am_vl (fren ξ) 0) (only parsing).
Notation ren_vls ξ := (am_vls (fren ξ) 0) (only parsing).

(** Replace each entry whose anchor [g] selects by a recursive value. An
    entry that [g] does not select stays. *)
Fixpoint su_shdw (g : nat → anc → option vl) (k : nat) (s : shdw) : shdw :=
  match s with
  | Init => Init
  | Read s' x => Read (su_shdw g k s') x
  | Call s' v => Call (su_shdw g k s') (su_vl g k v)
  | Dstr s' c i => Dstr (su_shdw g k s') c i
  end
with su_nv (g : nat → anc → option vl) (k : nat) (σ : nv) : nv :=
  match σ with
  | nv_mt => nv_mt
  | nv_sh s => nv_sh (su_shdw g k s)
  | nv_bd x v σ' => nv_bd x (su_vl g k v) (su_nv g k σ')
  | nv_mu x v σ' => nv_mu x (su_vl g (S k) v) (su_nv g k σ')
  | nv_an x a σ' =>
    match g k a with
    | Some u => nv_mu x u (su_nv g k σ')
    | None => nv_an x a (su_nv g k σ')
    end
  end
with su_vl (g : nat → anc → option vl) (k : nat) (v : vl) : vl :=
  match v with
  | vl_exp σ => vl_exp (su_nv g k σ)
  | vl_sh s => vl_sh (su_shdw g k s)
  | vl_clos x b σ => vl_clos x b (su_nv g k σ)
  | vl_cstr c vs => vl_cstr c (su_vls g k vs)
  end
with su_vls (g : nat → anc → option vl) (k : nat) (vs : vls) : vls :=
  match vs with
  | vnil => vnil
  | vcons v vs' => vcons (su_vl g k v) (su_vls g k vs')
  end.

(** Select the index [k], and give it the recursive value of [u]. *)
Definition funr (u : vl) (k : nat) (a : anc) : option vl :=
  match a with B j => if Nat.eqb j k then Some u else None | F _ => None end.

(** Select the name [ℓ], and give it the recursive value of [u]. *)
Definition fsub (ℓ : loc) (u : vl) (_ : nat) (a : anc) : option vl :=
  match a with F ℓ' => if Nat.eqb ℓ' ℓ then Some u else None | B _ => None end.

(** Unroll the recursive value of [v]. The anchor of [v] becomes the
    recursive value of [v] again. *)
Definition unroll (v : vl) : vl := su_vl (funr v) 0 v.

(** The largest name of a free anchor, or 0. *)
Fixpoint sup_shdw (s : shdw) : nat :=
  match s with
  | Init => 0
  | Read s' _ => sup_shdw s'
  | Call s' v => Nat.max (sup_shdw s') (sup_vl v)
  | Dstr s' _ _ => sup_shdw s'
  end
with sup_nv (σ : nv) : nat :=
  match σ with
  | nv_mt => 0
  | nv_sh s => sup_shdw s
  | nv_bd _ v σ' => Nat.max (sup_vl v) (sup_nv σ')
  | nv_mu _ v σ' => Nat.max (sup_vl v) (sup_nv σ')
  | nv_an _ a σ' => Nat.max (match a with F ℓ => ℓ | B _ => 0 end) (sup_nv σ')
  end
with sup_vl (v : vl) : nat :=
  match v with
  | vl_exp σ => sup_nv σ
  | vl_sh s => sup_shdw s
  | vl_clos _ _ σ => sup_nv σ
  | vl_cstr _ vs => sup_vls vs
  end
with sup_vls (vs : vls) : nat :=
  match vs with
  | vnil => 0
  | vcons v vs' => Nat.max (sup_vl v) (sup_vls vs')
  end.

(** A name that is fresh for [σ] and for [v], and that is not the dead
    anchor. *)
Definition fresh (σ : nv) (v : vl) : loc := S (Nat.max (sup_nv σ) (sup_vl v)).

(** ** Environments *)

(** The value of the variable [x]. A read of a recursive value unrolls it. A
    read of an anchor gives no value. *)
Fixpoint read (x : var) (σ : nv) : option vl :=
  match σ with
  | nv_mt => None
  | nv_sh s => Some (vl_sh (Read s x))
  | nv_bd x' v σ' => if String.eqb x x' then Some v else read x σ'
  | nv_mu x' v σ' => if String.eqb x x' then Some (unroll v) else read x σ'
  | nv_an x' _ σ' => if String.eqb x x' then None else read x σ'
  end.

(** Value number [i] of a list of values. *)
Fixpoint vnth (i : nat) (vs : vls) {struct vs} : option vl :=
  match vs with
  | vnil => None
  | vcons v vs' => match i with 0 => Some v | S i' => vnth i' vs' end
  end.

(** The length of a list of values. *)
Fixpoint vlen (vs : vls) : nat :=
  match vs with vnil => 0 | vcons _ vs' => S (vlen vs') end.

(** Bind the pattern variables to the fields of a constructor value. *)
Fixpoint bindV (xs : list var) (vs : vls) (σ : nv) : nv :=
  match xs, vs with
  | x :: xs', vcons v vs' => nv_bd x v (bindV xs' vs' σ)
  | _, _ => σ
  end.

(** Bind the pattern variables to the field shadows of the shadow [s], from
    field [i]. *)
Fixpoint bindD (xs : list var) (s : shdw) (c : cstr) (i : nat) (σ : nv) : nv :=
  match xs with
  | nil => σ
  | x :: xs' => nv_bd x (vl_sh (Dstr s c i)) (bindD xs' s c (S i) σ)
  end.

(** ** Traces *)

(** Put the trace [k v] at each leaf [v] of a trace. *)
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

(** Apply [g] to each guard, [gs] to each scrutinee and [h] to each leaf. *)
Fixpoint tmap (g : vl → vl) (gs : shdw → shdw) (h : vl → vl) (t : trace) : trace :=
  match t with
  | Bot => Bot
  | Ret v => Ret (h v)
  | Guard u t' => Guard (g u) (tmap g gs h t')
  | Match s bs => Match (gs s) (tmap_brs g gs h bs)
  end
with tmap_brs (g : vl → vl) (gs : shdw → shdw) (h : vl → vl) (bs : brs) : brs :=
  match bs with
  | bnil => bnil
  | bcons c n t bs' => bcons c n (tmap g gs h t) (tmap_brs g gs h bs')
  end.

(** Rename the free anchors of each value of a trace. *)
Definition ren_tr (ξ : loc → loc) : trace → trace :=
  tmap (ren_vl ξ) (ren_shdw ξ) (ren_vl ξ).

(** Kill the anchor [ℓ] in the spine of a trace. The leaves stay, because
    their anchor is closed next. *)
Definition killg (ℓ : loc) : trace → trace :=
  tmap (ren_vl (kap ℓ)) (ren_shdw (kap ℓ)) (fun v => v).

(** The result of a finished trace. A trace that is not finished has no
    result. *)
Fixpoint dest (t : trace) : option vl :=
  match t with
  | Bot => None
  | Ret v => Some v
  | Guard _ t' => dest t'
  | Match _ _ => None
  end.

(** Continue with the environment of a module. Each other value gives [Bot]. *)
Definition on_env (k : nv → trace) (m : vl) : trace :=
  match m with vl_exp σ => k σ | _ => Bot end.

(** Continue with the environment of a module, or with a shadow as an
    environment. *)
Definition on_mod (k : nv → trace) (m : vl) : trace :=
  match m with vl_exp σ => k σ | vl_sh s => k (nv_sh s) | _ => Bot end.

(** Continue with the name and the fields of a constructor value. *)
Definition on_cstr (k : cstr → vls → trace) (m : vl) : trace :=
  match m with vl_cstr c vs => k c vs | _ => Bot end.

(** ** Induction principles *)

(** Mutual induction on shadows, environments, values and lists of values. *)
Lemma val_mutind (P : shdw → Prop) (P0 : nv → Prop) (P1 : vl → Prop) (P2 : vls → Prop)
  (HInit : P Init)
  (HRead : ∀ s x, P s → P (Read s x))
  (HCall : ∀ s v, P s → P1 v → P (Call s v))
  (HDstr : ∀ s c i, P s → P (Dstr s c i))
  (Hmt : P0 nv_mt)
  (Hsh : ∀ s, P s → P0 (nv_sh s))
  (Hbd : ∀ x v σ, P1 v → P0 σ → P0 (nv_bd x v σ))
  (Hmu : ∀ x v σ, P1 v → P0 σ → P0 (nv_mu x v σ))
  (Han : ∀ x a σ, P0 σ → P0 (nv_an x a σ))
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

(** Mutual induction on traces and lists of branches. *)
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
