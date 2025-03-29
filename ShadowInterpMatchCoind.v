From Coq Require Import Utf8 Arith Lia String List.
From Paco Require Import paco.
Import ListNotations.

Local Open Scope string_scope.
Local Unset Elimination Schemes.
Local Set Primitive Projections.

Definition var := string.

Module simple.

Inductive shdw {vl} :=
  | Rd (x : var)
  | Ap (s : shdw) (v : vl)
.

Arguments shdw : clear implicits.

Inductive nv {vl} :=
  | Init
  | nv_mt
  | nv_bd (x : var) (v : vl) (σ : nv)
.

Arguments nv : clear implicits.

Inductive vl {tr} :=
  | vl_sh (s : shdw vl) (* s *)
  | vl_clos (x : var) (t : tr) (σ : nv vl) (* ⟨ λx.t, σ ⟩ *)
.

Arguments vl : clear implicits.

Section link.
  Context {trace : Type}.
  Let value := vl trace.
  Let shadow := shdw value.
  Let env := nv value.

  Definition rd x :=
    fix rd (σ : env) :=
      match σ with
      | Init => Some (vl_sh (Rd x))
      | nv_mt => None
      | nv_bd x' v σ' =>
        if x =? x' then Some v else rd σ'
      end.

  Definition link_shdw stuck link_value link_trace (σ0 : env) :=
    fix link (s : shadow) k : trace :=
      match s with
      | Rd x =>
        match rd x σ0 with
        | None => stuck
        | Some v => k v
        end
      | Ap s' v =>
        let k_s f :=
          let k_v a :=
            match f with
            | vl_sh f' => k (vl_sh (Ap f' a))
            | vl_clos x k' σ => link_trace (nv_bd x a σ) k' k
            end
          in link_value v k_v
        in link s' k_s
      end.

  Definition link_nv link_value (σ0 : env) :=
    fix link (σ : env) k : trace :=
      match σ with
      | Init => k σ0
      | nv_mt => k nv_mt
      | nv_bd x v σ' =>
        let k_v v' :=
          let k_σ σ'' := k (nv_bd x v' σ'')
          in link σ' k_σ
        in link_value v k_v
      end.

  Definition link_vl stuck link_trace (σ0 : env) :=
    fix link (v : value) k : trace :=
      match v with
      | vl_sh s => link_shdw stuck link link_trace σ0 s k
      | vl_clos x t σ =>
        let k_σ σ' := k (vl_clos x t σ')
        in link_nv link σ0 σ k_σ
      end.
End link.

Variant traceF {trace} :=
  | Stuck
  | Ret (v : vl trace)
  | Step (s : nv (vl trace)) (k : trace)
.

Arguments traceF : clear implicits.

(* Finite approximation *)
Inductive trace' := mkTrace' (k : traceF trace').
Definition obs_tr' (t : trace') :=
  match t with
  | mkTrace' k => k
  end.

(* Infinite tree *)
CoInductive trace := mkTrace { obs_tr : traceF trace }.

Definition value' := vl trace'.
Definition value := vl trace.
Definition shadow' := shdw value'.
Definition shadow := shdw value.
Definition env' := nv value'.
Definition env := nv value.

Notation stuck' := (mkTrace' Stuck) (only parsing).
Notation stuck := (mkTrace Stuck) (only parsing).
Notation ret' v := (mkTrace' (Ret v)) (only parsing).
Notation ret v := (mkTrace (Ret v)) (only parsing).
Notation step' σ k := (mkTrace' (Step σ k)) (only parsing).
Notation step σ k := (mkTrace (Step σ k)) (only parsing).

Fixpoint link_trace n σ0 (t : trace) k :=
  match n with
  | 0 => stuck
  | S n' =>
    match obs_tr t with
    | Stuck => stuck
    | Ret v => link_vl stuck (link_trace n') σ0 v k
    | Step σ t' =>
      let k_σ σ' := step σ' (link_trace n' σ0 t' k)
      in link_nv (link_vl stuck (link_trace n') σ0) σ0 σ k_σ
    end
  end.

Fixpoint link_trace' n σ0 (t : trace') k :=
  match n with
  | 0 => stuck'
  | S n' =>
    match obs_tr' t with
    | Stuck => stuck'
    | Ret v => link_vl stuck' (link_trace' n') σ0 v k
    | Step σ t' =>
      let k_σ σ' := step' σ' (link_trace' n' σ0 t' k)
      in link_nv (link_vl stuck' (link_trace' n') σ0) σ0 σ k_σ
    end
  end.

Definition link_value n := link_vl stuck (link_trace n).
Definition link_value' n := link_vl stuck' (link_trace' n).
Definition link_env n σ0 := link_nv (link_value n σ0) σ0.
Definition link_env' n σ0 := link_nv (link_value' n σ0) σ0.
Definition link_shadow n σ0 := link_shdw stuck (link_value n σ0) (link_trace n) σ0.
Definition link_shadow' n σ0 := link_shdw stuck' (link_value' n σ0) (link_trace' n) σ0.

Inductive term :=
  | Var (x : var)
  | Lam (x : var) (t : term)
  | App (fn arg : term)
.

Definition sem :=
  fix sem (t : term) k : nat → trace :=
  match t with
  | Var x => fun _ =>
    let r := vl_sh (Rd x)
    in step Init (k r)
  | Lam x e => fun n =>
    let r := vl_clos x (sem e (fun r => ret r) n) Init
    in step Init (k r)
  | App fn arg => fun n =>
    let k_fn f :=
      let k_arg a :=
        match f with
        | vl_sh f' => k (vl_sh (Ap f' a))
        | vl_clos x k' σ => link_trace n (nv_bd x a σ) k' k
        end
      in sem arg k_arg n
    in step Init (sem fn k_fn n)
  end.

Definition sem' :=
  fix sem (t : term) k : nat → trace' :=
  match t with
  | Var x => fun _ =>
    let r := vl_sh (Rd x)
    in step' Init (k r)
  | Lam x e => fun n =>
    let r := vl_clos x (sem e (fun r => ret' r) n) Init
    in step' Init (k r)
  | App fn arg => fun n =>
    let k_fn f :=
      let k_arg a :=
        match f with
        | vl_sh f' => k (vl_sh (Ap f' a))
        | vl_clos x k' σ => link_trace' n (nv_bd x a σ) k' k
        end
      in sem arg k_arg n
    in step' Init (sem fn k_fn n)
  end.

Definition ω := Lam "x" (App (Var "x") (Var "x")).
Compute sem' (App ω ω) (fun r => ret' r) 10.
End simple.

Inductive shdw {nv wvl} :=
  | Init
  | Rd (s : shdw) (σ : nv) (x : var)
  | Ap (s : shdw) (w : wvl)
.

Arguments shdw : clear implicits.

Inductive nv {wvl} :=
  | nv_sh (s : shdw nv wvl) (* [s] *)
  | nv_one (x : var) (w : wvl) (* x ↦ w *)
  | nv_mrg (σ σ' : nv) (* σ ;; σ' *)
.

Arguments nv : clear implicits.

Variant vl {P wvl tr} :=
  | vl_prim (p : P) (* primitive value *)
  | vl_nv (σ : nv wvl)
  | vl_sh (s : shdw (nv wvl) wvl) (* s *)
  | vl_clos (x : var) (t : tr) (σ : nv wvl) (* ⟨ λx.t, σ ⟩ *)
.

Arguments vl : clear implicits.

Inductive wvl {P L tr} :=
  | wvl_v (v : vl P wvl tr) (* v *)
  | wvl_recv (v : L → vl P wvl tr) (* μℓ.v *)
  | wvl_loc (ℓ : L) (* free location *)
.

Arguments wvl : clear implicits.

Variant traceF {P L trace} :=
  | Stuck
  | Ret (w : wvl P L trace)
  | Step (σ : nv (wvl P L trace)) (t : trace)
.

Arguments traceF : clear implicits.

(* Finite approximation *)
Inductive trace' {P L} := mkTrace' (k : traceF P L trace').
Definition obs_tr' {P L} (t : @trace' P L) :=
  match t with
  | mkTrace' k => k
  end.

(* Infinite tree *)
CoInductive trace {P L} := mkTrace { obs_tr : traceF P L trace }.

Arguments trace' : clear implicits.
Arguments trace : clear implicits.
Arguments mkTrace {_ _} _.

Definition walue' P L := wvl P L (trace' P L).
Definition walue P L := wvl P L (trace P L).
Definition env' P L := nv (walue' P L).
Definition env P L := nv (walue P L).
Definition shadow' P L := shdw (env' P L) (walue' P L).
Definition shadow P L := shdw (env' P L) (walue P L).
Definition value' P L := vl P (walue' P L) (trace' P L).
Definition value P L := vl P (walue P L) (trace P L).

Notation stuck' := (mkTrace' Stuck) (only parsing).
Notation stuck := (mkTrace Stuck) (only parsing).
Notation ret' w := (mkTrace' (Ret w)) (only parsing).
Notation ret w := (mkTrace (Ret w)) (only parsing).
Notation step' σ t := (mkTrace' (Step σ t)) (only parsing).
Notation step σ t := (mkTrace (Step σ t)) (only parsing).

Section ind.
  Context {P L tr : Type}.
  Let Walue := wvl P L tr.
  Let Value := vl P Walue tr.
  Let Env := nv Walue.
  Let Shadow := shdw Env Walue.
  Context (Ptr : tr → Prop) (tr_ind : ∀ k, Ptr k)
          (Pshdw : Shadow → Prop)
          (Pnv : Env → Prop)
          (Pvl : Value → Prop)
          (Pwvl : Walue → Prop).
  Context (PInit : Pshdw Init)
          (PRd : ∀ s σ x, Pshdw s → Pnv σ → Pshdw (Rd s σ x))
          (PAp : ∀ s w, Pshdw s → Pwvl w → Pshdw (Ap s w)).
  Context (Pnv_sh : ∀ s, Pshdw s → Pnv (nv_sh s))
          (Pnv_one : ∀ x w, Pwvl w → Pnv (nv_one x w))
          (Pnv_mrg : ∀ σ σ', Pnv σ → Pnv σ' -> Pnv (nv_mrg σ σ')).
  Context (Pvl_prim : ∀ p, Pvl (vl_prim p))
          (Pvl_nv : ∀ σ, Pnv σ → Pvl (vl_nv σ))
          (Pvl_sh : ∀ s, Pshdw s → Pvl (vl_sh s))
          (Pvl_clos : ∀ x k σ, Ptr k → Pnv σ → Pvl (vl_clos x k σ)).
  Context (Pwvl_v : ∀ v, Pvl v → Pwvl (wvl_v v))
          (Pwvl_recv : ∀ v, (∀ ℓ, Pvl (v ℓ)) → Pwvl (wvl_recv v))
          (Pwvl_loc : ∀ ℓ, Pwvl (wvl_loc ℓ)).

  Definition shdw_ind nv_ind wvl_ind :=
    fix go s : Pshdw s :=
      match s as s' return Pshdw s' with
      | Init => PInit
      | Rd s σ x => PRd s σ x (go s) (nv_ind σ)
      | Ap f w => PAp f w (go f) (wvl_ind w)
      end.

  Definition nv_ind wvl_ind :=
    fix go σ : Pnv σ :=
      match σ as σ' return Pnv σ' with
      | nv_sh s => Pnv_sh s (shdw_ind go wvl_ind s)
      | nv_one x w => Pnv_one x w (wvl_ind w)
      | nv_mrg σ1 σ2 => Pnv_mrg σ1 σ2 (go σ1) (go σ2)
      end.

  Definition vl_ind wvl_ind v : Pvl v :=
    match v as v' return Pvl v' with
    | vl_prim p => Pvl_prim p
    | vl_nv σ => Pvl_nv σ (nv_ind wvl_ind σ)
    | vl_sh s => Pvl_sh s (shdw_ind (nv_ind wvl_ind) wvl_ind s)
    | vl_clos x t σ => Pvl_clos x t σ (tr_ind t) (nv_ind wvl_ind σ)
    end.

  Fixpoint wvl_ind w : Pwvl w :=
    match w with
    | wvl_v v => Pwvl_v v (vl_ind wvl_ind v)
    | wvl_recv v => Pwvl_recv v (fun ℓ => vl_ind wvl_ind (v ℓ))
    | wvl_loc ℓ => Pwvl_loc ℓ
    end.

  Lemma pre_val_ind :
    (∀ s, Pshdw s) ∧ (∀ σ, Pnv σ) ∧ (∀ v, Pvl v) ∧ (∀ w, Pwvl w).
  Proof.
    pose proof (nv_ind wvl_ind).
    pose proof (vl_ind wvl_ind).
    pose proof (shdw_ind (nv_ind wvl_ind) wvl_ind).
    eauto using wvl_ind.
  Qed.
End ind.

Section trace'_ind.
  Context {P L : Type}.
  Let tr := trace' P L.
  Let Walue := wvl P L tr.
  Let Value := vl P Walue tr.
  Let Env := nv Walue.
  Let Shadow := shdw Env Walue.
  Context (Ptr : tr → Prop)
          (Pshdw : Shadow → Prop)
          (Pnv : Env → Prop)
          (Pvl : Value → Prop)
          (Pwvl : Walue → Prop).
  Context (PInit : Pshdw Init)
          (PRd : ∀ s σ x, Pshdw s → Pnv σ → Pshdw (Rd s σ x))
          (PAp : ∀ s w, Pshdw s → Pwvl w → Pshdw (Ap s w)).
  Context (Pnv_sh : ∀ s, Pshdw s → Pnv (nv_sh s))
          (Pnv_one : ∀ x w, Pwvl w → Pnv (nv_one x w))
          (Pnv_mrg : ∀ σ σ', Pnv σ → Pnv σ' -> Pnv (nv_mrg σ σ')).
  Context (Pvl_prim : ∀ p, Pvl (vl_prim p))
          (Pvl_nv : ∀ σ, Pnv σ → Pvl (vl_nv σ))
          (Pvl_sh : ∀ s, Pshdw s → Pvl (vl_sh s))
          (Pvl_clos : ∀ x k σ, Ptr k → Pnv σ → Pvl (vl_clos x k σ)).
  Context (Pwvl_v : ∀ v, Pvl v → Pwvl (wvl_v v))
          (Pwvl_recv : ∀ v, (∀ ℓ, Pvl (v ℓ)) → Pwvl (wvl_recv v))
          (Pwvl_loc : ∀ ℓ, Pwvl (wvl_loc ℓ)).
  Context (Pstuck : Ptr stuck')
          (Pret : ∀ w, Pwvl w → Ptr (ret' w))
          (Pstep : ∀ σ t, Pnv σ → Ptr t → Ptr (step' σ t)).

  Check shdw_ind.
  Fixpoint trace'_ind (t : tr) : Ptr t :=
    let wvl_ind' := wvl_ind _ trace'_ind _ _ _ _
      PInit PRd PAp
      Pnv_sh Pnv_one Pnv_mrg
      Pvl_prim Pvl_nv Pvl_sh Pvl_clos
      Pwvl_v Pwvl_recv Pwvl_loc in
    let nv_ind' := nv_ind _ _ _
      PInit PRd PAp
      Pnv_sh Pnv_one Pnv_mrg wvl_ind' in
    match t with
    | mkTrace' k =>
      match k as k' return Ptr (mkTrace' k') with
      | Stuck => Pstuck
      | Ret w => Pret w (wvl_ind' w)
      | Step σ t => Pstep σ t (nv_ind' σ) (trace'_ind t)
      end
    end.

  Lemma val'_ind :
    (∀ s, Pshdw s) ∧ (∀ σ, Pnv σ) ∧ (∀ v, Pvl v) ∧ (∀ w, Pwvl w) ∧ (∀ t, Ptr t).
  Proof.
    pose proof
      (pre_val_ind (tr := tr) (L := L) Ptr trace'_ind Pshdw Pnv Pvl Pwvl
        PInit PRd PAp
        Pnv_sh Pnv_one Pnv_mrg
        Pvl_prim Pvl_nv Pvl_sh Pvl_clos
        Pwvl_v Pwvl_recv Pwvl_loc).
    intuition auto.
    apply trace'_ind.
  Qed.
End trace'_ind.

Section map.
  Definition map_shdw {wvl wvl'}
    (map_wvl : wvl → wvl')
    (map_nv : nv wvl → nv wvl') :=
    fix map_s (s : shdw (nv wvl) wvl) : shdw (nv wvl') wvl' :=
      match s with
      | Init => Init
      | Rd s' σ x => Rd (map_s s') (map_nv σ) x
      | Ap f w => Ap (map_s f) (map_wvl w)
      end.

  Definition map_nv {wvl wvl'}
    (map_wvl : wvl → wvl') :=
    fix map_nv (σ : nv wvl) : nv wvl' :=
      match σ with
      | nv_sh s => nv_sh (map_shdw map_wvl map_nv s)
      | nv_one x w => nv_one x (map_wvl w)
      | nv_mrg σ1 σ2 => nv_mrg (map_nv σ1) (map_nv σ2)
      end.

  Definition map_vl {P wvl wvl' tr tr'}
    (map_wvl : wvl → wvl')
    (map_tr : tr → tr')
    (v : vl P wvl tr) : vl P wvl' tr' :=
    match v with
    | vl_prim p => vl_prim p
    | vl_nv σ => vl_nv (map_nv map_wvl σ)
    | vl_sh s => vl_sh (map_shdw map_wvl (map_nv map_wvl) s)
    | vl_clos x t σ => vl_clos x (map_tr t) (map_nv map_wvl σ)
    end.

  Definition map_wvl {P L tr tr'}
    (map_tr : tr → tr') :=
    fix map_w (w : wvl P L tr) : wvl P L tr' :=
      match w with
      | wvl_v v => wvl_v (map_vl map_w map_tr v)
      | wvl_recv v => wvl_recv (fun ℓ => map_vl map_w map_tr (v ℓ))
      | wvl_loc ℓ => wvl_loc ℓ
      end.
End map.

Section rel.
  Definition rel_shdw {wvl wvl'}
    (rel_wvl : wvl → wvl' → Prop)
    (rel_nv : nv wvl → nv wvl' → Prop) :=
    fix rel_s (s : shdw (nv wvl) wvl) (s' : shdw (nv wvl') wvl') : Prop :=
      match s with
      | Init => match s' with Init => True | _ => False end
      | Rd s σ x =>
        match s' with
        | Rd s' σ' x' => rel_s s s' ∧ rel_nv σ σ' ∧ x = x'
        | _ => False
        end
      | Ap f w =>
        match s' with
        | Ap f' w' => rel_s f f' ∧ rel_wvl w w'
        | _ => False
        end
      end.

  Definition rel_nv {wvl wvl'}
    (rel_wvl : wvl → wvl' → Prop) :=
    fix rel_nv (σ : nv wvl) (σ' : nv wvl') : Prop :=
      match σ with
      | nv_sh s =>
        match σ' with
        | nv_sh s' => rel_shdw rel_wvl rel_nv s s'
        | _ => False
        end
      | nv_one x w =>
        match σ' with
        | nv_one x' w' => x = x' ∧ rel_wvl w w'
        | _ => False
        end
      | nv_mrg σ1 σ2 =>
        match σ' with
        | nv_mrg σ1' σ2' => rel_nv σ1 σ1' ∧ rel_nv σ2 σ2'
        | _ => False
        end
      end.

  Definition rel_vl {P wvl wvl' tr tr'}
    (rel_wvl : wvl → wvl' → Prop)
    (rel_tr : tr → tr' → Prop)
    (v : vl P wvl tr) (v' : vl P wvl' tr') :=
    match v with
    | vl_prim p =>
      match v' with
      | vl_prim p' => p = p'
      | _ => False
      end
    | vl_nv σ =>
      match v' with
      | vl_nv σ' => rel_nv rel_wvl σ σ'
      | _ => False
      end
    | vl_sh s =>
      match v' with
      | vl_sh s' => rel_shdw rel_wvl (rel_nv rel_wvl) s s'
      | _ => False
      end
    | vl_clos x t σ =>
      match v' with
      | vl_clos x' t' σ' =>
        x = x' ∧ rel_tr t t' ∧ rel_nv rel_wvl σ σ'
      | _ => False
      end
    end.

  Definition rel_wvl {P L tr tr'}
    (rel_tr : tr → tr' → Prop) :=
    fix rel_w (w : wvl P L tr) (w' : wvl P L tr') :=
      match w with
      | wvl_v v =>
        match w' with
        | wvl_v v' => rel_vl rel_w rel_tr v v'
        | _ => False
        end
      | wvl_recv v =>
        match w' with
        | wvl_recv v' => ∀ ℓ, rel_vl rel_w rel_tr (v ℓ) (v' ℓ)
        | _ => False
        end
      | wvl_loc ℓ => match w' with wvl_loc ℓ' => ℓ = ℓ' | _ => False end
      end.

  Context {P L tr tr' : Type}
    (r r' : tr → tr' → Prop)
    (LEt : ∀ t t', r t t' → r' t t').

  Definition rel_shdw_monotone (s : shdw (nv (wvl P L tr)) (wvl P L tr)) :=
    ∀ s', rel_shdw (rel_wvl r) (rel_nv (rel_wvl r)) s s' →
          rel_shdw (rel_wvl r') (rel_nv (rel_wvl r')) s s'
  .
  Definition rel_nv_monotone (σ : nv (wvl P L tr)) :=
    ∀ σ', rel_nv (rel_wvl r) σ σ' → rel_nv (rel_wvl r') σ σ'
  .
  Definition rel_vl_monotone (v : vl P (wvl P L tr) tr) :=
    ∀ v', rel_vl (rel_wvl r) r v v' → rel_vl (rel_wvl r') r' v v'
  .
  Definition rel_wvl_monotone (w : wvl P L tr) :=
    ∀ w', rel_wvl r w w' → rel_wvl r' w w'
  .

  Lemma rel_monotone :
    (∀ s, rel_shdw_monotone s) ∧
    (∀ σ, rel_nv_monotone σ) ∧
    (∀ v, rel_vl_monotone v) ∧
    (∀ w, rel_wvl_monotone w).
  Proof.
    apply (pre_val_ind _ (fun _ => I));
    cbv [rel_shdw_monotone rel_nv_monotone rel_vl_monotone rel_wvl_monotone];
    simpl; intros;
    match goal with
    | _ : match ?x with _ => _ end |- _ =>
      destruct x; intuition auto
    end.
  Qed.
End rel.

(* partial order between finite approximations *)
Definition le_trace' {P L} :=
  fix le_t (t t' : trace' P L) :=
    let le_wvl := rel_wvl le_t in
    match obs_tr' t with
    | Stuck => True
    | Ret w =>
      match obs_tr' t' with
      | Ret w' => le_wvl w w'
      | _ => False
      end
    | Step σ k =>
      match obs_tr' t' with
      | Step σ' k' => rel_nv le_wvl σ σ' ∧ le_t k k'
      | _ => False
      end
    end.

Lemma le_trace'_refl {P L} :
  let le_wvl (w : walue' P L) := rel_wvl le_trace' w in
  let le_vl (v : value' P L) := rel_vl le_wvl le_trace' v in
  let le_nv (σ : env' P L) := rel_nv le_wvl σ in
  let le_shdw (s : shadow' P L) := rel_shdw le_wvl le_nv s in
  (∀ s, le_shdw s s) ∧
  (∀ σ, le_nv σ σ) ∧
  (∀ v, le_vl v v) ∧
  (∀ w, le_wvl w w) ∧
  (∀ t : trace' P L, le_trace' t t).
Proof. cbn zeta. apply val'_ind; simpl; auto. Qed.

Lemma le_trace'_trans {P L} :
  let le_wvl (w : walue' P L) := rel_wvl le_trace' w in
  let le_vl (v : value' P L) := rel_vl le_wvl le_trace' v in
  let le_nv (σ : env' P L) := rel_nv le_wvl σ in
  let le_shdw (s : shadow' P L) := rel_shdw le_wvl le_nv s in
  (∀ s' : shadow' P L,
    ∀ s s'', le_shdw s s' → le_shdw s' s'' → le_shdw s s'') ∧
  (∀ σ' : env' P L,
    ∀ σ σ'', le_nv σ σ' → le_nv σ' σ'' → le_nv σ σ'') ∧
  (∀ v' : value' P L,
    ∀ v v'', le_vl v v' → le_vl v' v'' → le_vl v v'') ∧
  (∀ w' : walue' P L,
    ∀ w w'', le_wvl w w' → le_wvl w' w'' → le_wvl w w'') ∧
  (∀ t' : trace' P L,
    ∀ t t'', le_trace' t t' → le_trace' t' t'' → le_trace' t t'').
Proof.
  cbn zeta. apply val'_ind; simpl; intros;
  match goal with
  | |- rel_shdw _ _ ?s ?s'' =>
    destruct s; simpl in *; intuition eauto;
    subst; destruct s''; intuition eauto
  | |- rel_nv _ ?σ ?σ'' =>
    destruct σ; simpl in *; intuition eauto;
    subst; destruct σ''; intuition eauto
  | |- rel_vl _ _ ?v ?v'' =>
    destruct v; simpl in *; intuition eauto;
    subst; destruct v''; intuition eauto
  | |- rel_wvl _ ?w ?w'' =>
    destruct w; simpl in *; intuition eauto;
    subst; destruct w''; intuition eauto
  | |- le_trace' ?t ?t'' =>
    destruct t; simpl in *; intuition eauto;
    subst; destruct t''; intuition eauto
  end.
  - destruct k; simpl in *; intuition eauto.
  - destruct k; simpl in *; intuition eauto.
    destruct k0; simpl in *; intuition eauto.
  - destruct k; simpl in *; intuition eauto.
    destruct k0; simpl in *; intuition eauto.
Qed.

(* approx t' t : t' is a finite approximation of t *)
Definition approx {P L} :=
  fix approx (t' : trace' P L) (t : trace P L) :=
    let approx_w := rel_wvl approx in
    match obs_tr' t' with
    | Stuck => True
    | Ret w' =>
      match obs_tr t with
      | Ret w => approx_w w' w
      | _ => False
      end
    | Step σ' k' =>
      match obs_tr t with
      | Step σ k => rel_nv approx_w σ' σ ∧ approx k' k
      | _ => False
      end
    end.

Variant eq_traceF {P L} eq : trace P L → trace P L → Prop :=
  | eq_stuck : eq_traceF eq stuck stuck
  | eq_ret w w'
    (EQw : rel_wvl eq w w')
  : eq_traceF eq (ret w) (ret w')
  | eq_step σ σ' k k'
    (EQσ : rel_nv (rel_wvl eq) σ σ')
    (EQk : eq k k')
  : eq_traceF eq (step σ k) (step σ' k')
.

Arguments eq_traceF : clear implicits.

Lemma eq_traceF_monotone {P L} : monotone2 (eq_traceF P L).
Proof.
  repeat intro. inversion IN; try constructor; subst; auto.
  all: eapply rel_monotone; eauto.
Qed.

Hint Resolve eq_traceF_monotone : paco.
Definition eq_trace P L := paco2 (eq_traceF P L) bot2.

Fixpoint nth_trace {P L} (n : nat) (t : trace P L) : trace' P L :=
  match n with
  | 0 => stuck'
  | S n' =>
    match obs_tr t with
    | Stuck => stuck'
    | Ret w =>
      let w' := map_wvl (nth_trace n') w in
      ret' w'
    | Step σ k =>
      let σ' := map_nv (map_wvl (nth_trace n')) σ in
      step' σ' (nth_trace n' k)
    end
  end.

Section flatten.
  Context {P L : Type} (flatten_walue' : walue' P (walue' P L) → walue' P L).
 
  Definition flatten_shadow' flatten_env' :=
    fix flatten (s : shadow' P (walue' P L)) : shadow' P L :=
    match s with
    | Init => Init
    | Rd s σ x => Rd (flatten s) (flatten_env' σ) x
    | Ap s w => Ap (flatten s) (flatten_walue' w)
    end.

  Fixpoint flatten_env' (σ : env' P (walue' P L)) : env' P L :=
    match σ with
    | nv_sh s => nv_sh (flatten_shadow' flatten_env' s)
    | nv_one x w => nv_one x (flatten_walue' w)
    | nv_mrg σ σ' => nv_mrg (flatten_env' σ) (flatten_env' σ')
    end.

  Context (flatten_trace' : trace' P (walue' P L) → trace' P L).

  Definition flatten_value' (v : value' P (walue' P L)) : value' P L :=
    match v with
    | vl_prim p => vl_prim p
    | vl_nv σ => vl_nv (flatten_env' σ)
    | vl_sh s => vl_sh (flatten_shadow' flatten_env' s)
    | vl_clos x t σ =>
      vl_clos x
        (flatten_trace' t)
        (flatten_env' σ)
    end.
End flatten.

Definition flatten_walue' {P L} flatten_trace' :=
  fix flatten_walue' (w : walue' P (walue' P L)) : walue' P L :=
  let f := flatten_value' flatten_walue' flatten_trace' in
  match w with
  | wvl_v v => wvl_v (f v)
  | wvl_recv v => wvl_recv (fun ℓ => f (v (wvl_loc ℓ)))
  | wvl_loc ℓ => ℓ (* flatten *)
  end.

Definition flatten_trace' {P L} :=
  fix flatten_trace' (t : trace' P (walue' P L)) : trace' P L :=
  let f := flatten_walue' flatten_trace' in
  match t with
  | mkTrace' k =>
    match k with
    | Stuck => stuck'
    | Ret w => ret' (f w)
    | Step σ t => step' (flatten_env' f σ) (flatten_trace' t)
    end
  end.

(* Define : coinductive version of traces *)
(* Define : strong bisimilarity between traces *)
(* Define : depth-n approximation between traces *)
(* Prove : strong bisimilarity ↔ equality of approximation for all n *)
(* Conclusion : represent coinductive trace with a stream of "increasing" approximations *)
