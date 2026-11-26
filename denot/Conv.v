(** * Finished traces

    This file gives the tools for a proof about finished traces. More fuel
    does not change a finished trace. The files [LinkLink.v] and [Adequacy.v]
    state their results with the 2 predicates of this file.

    ** Main definitions

    - [evc F r c]: from some fuel, the trace [F m] is finished with the
      result [r], and its cost is at most [c].
    - [ev2 G r]: from some pair of fuels, the trace [G n m] is finished with
      the result [r].
    - [leaves P t]: [P] holds of each leaf of [t].

    ** Main results

    - [up_vl], [up_tr], [up_trace], [up_linkb], [up_linkv]: more fuel does
      not change a finished trace.
    - [evc_bind], [evc_guard]: [evc] for [bind] and for a guard.
    - [link_nv_leaf], [link_vls_leaf]: the result of linking into an
      environment is a module, and into a list of values is a constructor
      value.
    - [sel_leaf], [link_tr_leaves]: linking into the spine keeps the leaves. *)
From Stdlib Require Import Utf8 String Bool Arith Lia List.
From Denot Require Import Syntax Anchor Domain Nominal Semantics Laws Wf Order.

(** When [bind k t] is finished, [t] and [k v] are finished, and the costs
    add. *)
Lemma inv_bind k t r (D : dest (bind k t) = Some r) :
  ∃ v, dest t = Some v ∧ dest (k v) = Some r ∧
       cost (bind k t) = cost t + cost (k v).
Proof.
  destruct (dest_bind_inv _ _ _ D) as (v & Dt & Dk).
  exists v. repeat split; auto. apply cost_bind; auto.
Qed.

Section up.
  Context (n m : nat) (LE : n ≤ m) (σ0 : nv) (Hσ0 : wf_nv σ0).

  Let Hwf : ∀ σ b, wf_nv σ → wfb b → wf_tr (call n σ b).
  Proof. intros; apply wf_call; auto. Qed.
  Let Hle : ∀ σ b, wf_nv σ → wfb b → le_tr (call n σ b) (call m σ b).
  Proof. intros; apply le_call; auto. Qed.
  Let Hwfl : ∀ σ v, wf_nv σ → wf_vl v → wf_tr (linkv n σ v).
  Proof. intros; apply wf_linkv; auto. Qed.
  Let Hlel : ∀ σ v, wf_nv σ → wf_vl v → le_tr (linkv n σ v) (linkv m σ v).
  Proof. intros; apply le_linkv; auto. Qed.

  (** More fuel does not change a finished linking into a shadow. *)
  Lemma up_shdw s r (W : wf_shdw s) (D : dest (link_shdw (call n) (linkv n) σ0 s) = Some r) :
    link_shdw (call m) (linkv m) σ0 s = link_shdw (call n) (linkv n) σ0 s.
  Proof. eapply le_total; eauto. apply le_link; auto. Qed.

  (** More fuel does not change a finished linking into an environment. *)
  Lemma up_nv σ r (W : wf_nv σ) (D : dest (link_nv (call n) (linkv n) σ0 σ) = Some r) :
    link_nv (call m) (linkv m) σ0 σ = link_nv (call n) (linkv n) σ0 σ.
  Proof. eapply le_total; eauto. apply le_link; auto. Qed.

  (** More fuel does not change a finished linking into a value. *)
  Lemma up_vl v r (W : wf_vl v) (D : dest (link_vl (call n) (linkv n) σ0 v) = Some r) :
    link_vl (call m) (linkv m) σ0 v = link_vl (call n) (linkv n) σ0 v.
  Proof. eapply le_total; eauto. apply le_link; auto. Qed.

  (** More fuel does not change a finished linking into a list of values. *)
  Lemma up_vls c vs r (W : wf_vls vs) (D : dest (link_vls (call n) (linkv n) σ0 c vs) = Some r) :
    link_vls (call m) (linkv m) σ0 c vs = link_vls (call n) (linkv n) σ0 c vs.
  Proof. eapply le_total; eauto. apply le_link; auto. Qed.

  (** More fuel, and an extension of the trace, do not change a finished
      linking into a spine. *)
  Lemma up_tr t t' r (W : wf_tr t) (LEt : le_tr t t')
    (D : dest (link_tr (call n) (linkv n) σ0 t) = Some r) :
    link_tr (call m) (linkv m) σ0 t' = link_tr (call n) (linkv n) σ0 t.
  Proof. eapply le_total; eauto. apply le_link_tr; auto. Qed.

  (** More fuel does not change a finished linking into a selected branch. *)
  Lemma up_sel c k bs r (W : wf_brs bs)
    (D : dest (link_sel (call n) (linkv n) σ0 c k bs) = Some r) :
    link_sel (call m) (linkv m) σ0 c k bs = link_sel (call n) (linkv n) σ0 c k bs.
  Proof.
    eapply le_total; eauto.
    eapply (le_link_tr (call n) (call m) (linkv n) (linkv m)); eauto.
    apply le_refl_mut.
  Qed.

  (** More fuel, and an extension of the trace, do not change a finished
      linking into a trace. *)
  Lemma up_trace t t' r (W : wf_tr t) (LEt : le_tr t t')
    (D : dest (link_trace (call n) (linkv n) σ0 t) = Some r) :
    link_trace (call m) (linkv m) σ0 t' = link_trace (call n) (linkv n) σ0 t.
  Proof. eapply le_total; eauto. apply le_link_trace; auto. Qed.
End up.

(** More fuel does not change a finished [linkb]. *)
Lemma up_linkb n m (LE : n ≤ m) σ b r (Hσ : wf_nv σ) (Hb : wfb b)
  (D : dest (linkb n σ b) = Some r) : linkb m σ b = linkb n σ b.
Proof. eapply le_total; eauto. apply le_linkb; auto. Qed.

(** More fuel does not change a finished [linkv]. *)
Lemma up_linkv n m (LE : n ≤ m) σ v r (Hσ : wf_nv σ) (Hv : wf_vl v)
  (D : dest (linkv n σ v) = Some r) : linkv m σ v = linkv n σ v.
Proof. eapply le_total; eauto. apply le_linkv; auto. Qed.

(** More fuel does not change a finished [ap]. *)
Lemma up_ap n m (LE : n ≤ m) f a r (Hf : wf_vl f) (Ha : wf_vl a)
  (D : dest (ap (call n) f a) = Some r) : ap (call m) f a = ap (call n) f a.
Proof.
  eapply le_total; eauto. apply le_ap; auto. intros. apply le_call; auto.
Qed.

(** ** A result from some fuel, with a bound on the cost *)

(** From some fuel, the trace [F m] is finished with the result [r] and a
    cost of at most [c]. *)
Definition evc (F : nat → trace) (r : vl) (c : nat) : Prop :=
  ∃ m0, ∀ m, m0 ≤ m → dest (F m) = Some r ∧ cost (F m) ≤ c.

(** [evc] for a trace that does not depend on the fuel. *)
Lemma evc_const t r c (D : dest t = Some r) (C : cost t ≤ c) : evc (fun _ => t) r c.
Proof. exists 0. auto. Qed.

(** [evc] with a larger bound on the cost. *)
Lemma evc_weaken F r c c' (E : evc F r c) (LE : c ≤ c') : evc F r c'.
Proof.
  destruct E as (m0 & E). exists m0. intros m Hm.
  destruct (E m Hm). split; auto. lia.
Qed.

(** [evc] for an equal family of traces. *)
Lemma evc_ext F G r c (EXT : ∀ m, F m = G m) (E : evc F r c) : evc G r c.
Proof.
  destruct E as (m0 & E). exists m0. intros m Hm. rewrite <- EXT. auto.
Qed.

(** [evc] for [bind]. The bounds on the cost add. *)
Lemma evc_bind F K w r c1 c2 (E1 : evc F w c1) (E2 : evc (fun m => K m w) r c2) :
  evc (fun m => bind (K m) (F m)) r (c1 + c2).
Proof.
  destruct E1 as (m1 & E1), E2 as (m2 & E2). exists (Nat.max m1 m2).
  intros m Hm. destruct (E1 m ltac:(lia)) as [D1 C1].
  destruct (E2 m ltac:(lia)) as [D2 C2]. split.
  - eapply dest_bind_intro; eauto.
  - erewrite cost_bind; eauto. lia.
Qed.

(** [evc] behind a guard. The bound on the cost grows by 1. *)
Lemma evc_guard F u r c (E : evc F r c) : evc (fun m => Guard u (F m)) r (S c).
Proof.
  destruct E as (m0 & E). exists m0. intros m Hm.
  destruct (E m Hm). simpl. split; auto. lia.
Qed.

(** [evc] for a family that does not change from the fuel [m0]. *)
Lemma evc_up (F : nat → trace) m0 r c
  (UP : ∀ m, m0 ≤ m → F m = F m0)
  (D : dest (F m0) = Some r) (C : cost (F m0) ≤ c) : evc F r c.
Proof. exists m0. intros m Hm. rewrite UP; auto. Qed.

Section shapes.
  Context (cl : nv → body → trace) (lk : nv → vl → trace) (σ0 : nv).

  (** ** The form of a result of linking *)

  (** The result of linking into an environment is a module. *)
  Lemma link_nv_leaf σ w (D : dest (link_nv cl lk σ0 σ) = Some w) : ∃ σ', w = vl_exp σ'.
  Proof.
    destruct σ; simpl in D.
    - inversion D; eauto.
    - apply dest_bind_inv in D as (m & _ & D).
      destruct m; simpl in D; inversion D; eauto.
    - apply dest_bind_inv in D as (v' & _ & D).
      apply dest_bind_inv in D as (m & _ & D).
      destruct m; simpl in D; inversion D; eauto.
    - apply dest_bind_inv in D as (v' & _ & D).
      apply dest_bind_inv in D as (m & _ & D).
      destruct m; simpl in D; inversion D; eauto.
    - apply dest_bind_inv in D as (m & _ & D).
      destruct m; simpl in D; inversion D; eauto.
  Qed.

  (** The result of linking into a list of values is a constructor value of
      the same name and length. *)
  Lemma link_vls_leaf vs : ∀ c w, dest (link_vls cl lk σ0 c vs) = Some w →
    ∃ vs', w = vl_cstr c vs' ∧ vlen vs' = vlen vs.
  Proof.
    induction vs as [|v vs IH]; simpl; intros c w D.
    - inversion D; eauto.
    - apply dest_bind_inv in D as (v' & _ & D).
      apply dest_bind_inv in D as (m & Dm & D).
      destruct (IH _ _ Dm) as (vs' & -> & Hlen). simpl in D. inversion D.
      eexists; split; eauto. simpl. congruence.
  Qed.

  (** A field of the linked list is the result of linking into the field. *)
  Lemma vnth_link vs : ∀ c i vs' v r,
    dest (link_vls cl lk σ0 c vs) = Some (vl_cstr c vs') → vnth i vs = Some v →
    dest (link_vl cl lk σ0 v) = Some r → vnth i vs' = Some r.
  Proof.
    induction vs as [|u vs IH]; simpl; intros c i vs' v r D N Dv; try discriminate.
    apply dest_bind_inv in D as (u' & Du & D).
    apply dest_bind_inv in D as (m & Dm & D).
    destruct (link_vls_leaf _ _ _ Dm) as (vs1 & -> & _). simpl in D.
    inversion D; subst; clear D. simpl. destruct i.
    - inversion N; subst. congruence.
    - eauto.
  Qed.

  (** A field of the linked list comes from a field of the list, and is the
      result of linking into it. *)
  Lemma vnth_link_inv vs : ∀ c i vs' r,
    dest (link_vls cl lk σ0 c vs) = Some (vl_cstr c vs') → vnth i vs' = Some r →
    ∃ v, vnth i vs = Some v ∧ dest (link_vl cl lk σ0 v) = Some r.
  Proof.
    induction vs as [|u vs IH]; simpl; intros c i vs' r D N.
    - inversion D; subst. simpl in N. discriminate.
    - apply dest_bind_inv in D as (u' & Du & D).
      apply dest_bind_inv in D as (m & Dm & D).
      destruct (link_vls_leaf _ _ _ Dm) as (vs1 & -> & _). simpl in D.
      inversion D; subst; clear D. simpl in N. destruct i.
      + inversion N; subst. eauto.
      + eauto.
  Qed.
End shapes.

(** ** A property of each leaf *)

(** [P] holds of each leaf of a trace. *)
Fixpoint leaves (P : vl → Prop) (t : trace) : Prop :=
  match t with
  | Bot => True
  | Ret v => P v
  | Guard _ t' => leaves P t'
  | Match _ bs => leaves_brs P bs
  end
with leaves_brs (P : vl → Prop) (bs : brs) : Prop :=
  match bs with
  | bnil => True
  | bcons _ _ t bs' => leaves P t ∧ leaves_brs P bs'
  end.

(** The value is a module. *)
Definition is_exp (w : vl) : Prop := match w with vl_exp _ => True | _ => False end.

(** The value is a constructor value of the name [c]. *)
Definition is_cstr (c : cstr) (w : vl) : Prop :=
  match w with vl_cstr c' _ => c' = c | _ => False end.

(** The mutual form of [leaves_bind]. *)
Lemma leaves_bind_mut (P Q : vl → Prop) k (Hk : ∀ v, Q v → leaves P (k v)) :
  (∀ t, leaves Q t → leaves P (bind k t)) ∧
  (∀ bs, leaves_brs Q bs → leaves_brs P (bind_brs k bs)).
Proof. apply tr_mutind; simpl; intuition auto. Qed.

(** [P] holds of each leaf of [bind k t] when it holds of each leaf of each
    [k v]. *)
Lemma leaves_bind (P Q : vl → Prop) k t (Hk : ∀ v, Q v → leaves P (k v))
  (Ht : leaves Q t) : leaves P (bind k t).
Proof. eapply leaves_bind_mut; eauto. Qed.

(** The mutual form of [leaves_True]. *)
Lemma leaves_True_mut :
  (∀ t, leaves (fun _ => True) t) ∧ (∀ bs, leaves_brs (fun _ => True) bs).
Proof. apply tr_mutind; simpl; auto. Qed.

(** The trivial predicate holds of each leaf. *)
Lemma leaves_True t : leaves (fun _ => True) t.
Proof. apply leaves_True_mut. Qed.

(** The mutual form of [leaves_tall]. *)
Lemma leaves_tall_mut (Pg : vl → Prop) (Ps : shdw → Prop) (Pl : vl → Prop) :
  (∀ t, tall Pg Ps Pl t → leaves Pl t) ∧
  (∀ bs, tall_brs Pg Ps Pl bs → leaves_brs Pl bs).
Proof. apply tr_mutind; simpl; intuition auto. Qed.

(** [tall] gives [leaves] for the predicate of the leaves. *)
Lemma leaves_tall (Pg : vl → Prop) (Ps : shdw → Prop) (Pl : vl → Prop) t :
  tall Pg Ps Pl t → leaves Pl t.
Proof. apply leaves_tall_mut. Qed.

Section leaf_shapes.
  Context (cl : nv → body → trace) (lk : nv → vl → trace) (σ0 : nv).

  (** Each leaf of linking into an environment is a module. *)
  Lemma link_nv_leaves σ : leaves is_exp (link_nv cl lk σ0 σ).
  Proof.
    destruct σ; simpl; auto.
    - eapply leaves_bind; [|apply leaves_True]. intros [] _; simpl; auto.
    - eapply leaves_bind; [|apply leaves_True]. intros v' _.
      eapply leaves_bind; [|apply leaves_True]. intros [] _; simpl; auto.
    - eapply leaves_bind; [|apply leaves_True]. intros v' _.
      eapply leaves_bind; [|apply leaves_True]. intros [] _; simpl; auto.
    - eapply leaves_bind; [|apply leaves_True]. intros [] _; simpl; auto.
  Qed.

  (** Each leaf of linking into a list of values is a constructor value of
      the name [c]. *)
  Lemma link_vls_leaves vs : ∀ c, leaves (is_cstr c) (link_vls cl lk σ0 c vs).
  Proof.
    induction vs as [|v vs IH]; simpl; intros c; auto.
    eapply leaves_bind; [|apply leaves_True]. intros v' _.
    eapply leaves_bind; [|apply IH]. intros [] Hc; simpl in *; auto; tauto.
  Qed.

  (** The mutual form of [sel_leaf]. *)
  Lemma sel_leaf_mut (P : vl → Prop) :
    (∀ t w, leaves P t → dest (link_tr cl lk σ0 t) = Some w → P w) ∧
    (∀ bs w c k, leaves_brs P bs → dest (link_sel cl lk σ0 c k bs) = Some w → P w).
  Proof.
    apply tr_mutind; simpl.
    - intros; discriminate.
    - intros v w Hv D. inversion D; subst; auto.
    - intros u t IH w Ht D.
      apply dest_bind_inv in D as (u' & _ & D). simpl in D. eauto.
    - intros s bs IH w Hb D.
      apply dest_bind_inv in D as (m & _ & D).
      destruct m; simpl in D; try discriminate. eauto.
    - intros; discriminate.
    - intros c n t bs IHt IHb w c0 k [Ht Hb] D.
      destruct (_ && _); eauto.
  Qed.

  (** The result of linking into the spine of a trace is one of the leaves of
      the trace. *)
  Lemma sel_leaf (P : vl → Prop) t w (Ht : leaves P t)
    (D : dest (link_tr cl lk σ0 t) = Some w) : P w.
  Proof. destruct (sel_leaf_mut P) as [H _]. eauto. Qed.

  (** The mutual form of [link_tr_leaves]. *)
  Lemma link_tr_leaves_mut (P : vl → Prop) :
    (∀ t, leaves P t → leaves P (link_tr cl lk σ0 t)) ∧
    (∀ bs, leaves_brs P bs →
       leaves_brs P (link_brs cl lk σ0 bs) ∧
       ∀ c k, leaves P (link_sel cl lk σ0 c k bs)).
  Proof.
    apply tr_mutind; simpl; auto.
    - intros u t IH Ht. eapply leaves_bind; [|apply leaves_True].
      intros u' _. simpl. auto.
    - intros s bs IH Hb. destruct (IH Hb) as [IH1 IH2].
      eapply leaves_bind; [|apply leaves_True].
      intros m _. destruct m; simpl; auto.
    - intros c n t bs IHt IHb [Ht Hb]. destruct (IHb Hb) as [IH1 IH2].
      repeat split; auto. intros c' k'. destruct (_ && _); auto.
  Qed.

  (** Linking into the spine keeps a property of each leaf. *)
  Lemma link_tr_leaves (P : vl → Prop) t :
    leaves P t → leaves P (link_tr cl lk σ0 t).
  Proof. apply link_tr_leaves_mut. Qed.
End leaf_shapes.

(** ** A result from some pair of fuels *)

(** From some pair of fuels, the trace [G n m] is finished with the result
    [r]. *)
Definition ev2 (G : nat → nat → trace) (r : vl) : Prop :=
  ∃ n0 m0, ∀ n m, n0 ≤ n → m0 ≤ m → dest (G n m) = Some r.
