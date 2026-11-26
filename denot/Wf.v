(** * Well-formed values and traces

    This file defines when a value is well formed, and proves that the
    semantics gives only well-formed values. Each later file assumes that its
    values are well formed.

    ** Main definitions

    - [wfb]: a body is the denotation of a term.
    - [wfk_vl k]: under [k] recursive values, a value is well formed. Each
      body of a closure is the denotation of a term, and each index is below
      [k] plus the number of recursive values around it.
    - [wf_vl], [wf_tr]: a value or a trace is well formed, under 0 recursive
      values.

    ** Main results

    - [wf_open], [wf_close], [wf_unroll]: open, close and unroll keep values
      well formed, with the right number of recursive values.
    - [open_close]: open after close gives a locally closed value back.
    - [wf_link], [wf_link_tr], [wf_link_trace]: linking keeps traces well
      formed.
    - [wf_linkb], [wf_linkv], [wf_call], [wf_den]: each trace of the
      semantics is well formed.

    ** Tactics

    - [wf_tac]: prove that a trace of the semantics is well formed. *)
From Stdlib Require Import Utf8 String Bool Arith Lia List.
From Denot Require Import Syntax Anchor Domain Nominal Semantics Laws.
Set Warnings "-notation-for-abbreviation".

(** A body is well formed when it is the denotation of a term. *)
Definition wfb (b : body) : Prop := ∃ e, b = den e.

(** Under [k] recursive values, an index is below [k]. A name has no
    condition. *)
Definition wf_anc (k : nat) (a : anc) : Prop :=
  match a with B j => j < k | F _ => True end.

(** A shadow, an environment, a weak value, a value or a list of values is
    well formed under [k] recursive values. *)
Fixpoint wfk_shdw (k : nat) (s : shdw) : Prop :=
  match s with
  | Init => True
  | Read s' _ => wfk_shdw k s'
  | Call s' v => wfk_shdw k s' ∧ wfk_vl k v
  | Dstr s' _ _ => wfk_shdw k s'
  end
with wfk_nv (k : nat) (σ : nv) : Prop :=
  match σ with
  | nv_mt => True
  | nv_sh s => wfk_shdw k s
  | nv_bd _ w σ' => wfk_wvl k w ∧ wfk_nv k σ'
  end
with wfk_wvl (k : nat) (w : wvl) : Prop :=
  match w with
  | wvl_v v => wfk_vl k v
  | wvl_mu v => wfk_vl (S k) v
  | wvl_an a => wf_anc k a
  end
with wfk_vl (k : nat) (v : vl) : Prop :=
  match v with
  | vl_exp σ => wfk_nv k σ
  | vl_sh s => wfk_shdw k s
  | vl_clos _ b σ => wfb b ∧ wfk_nv k σ
  | vl_cstr _ vs => wfk_vls k vs
  end
with wfk_vls (k : nat) (vs : vls) : Prop :=
  match vs with
  | vnil => True
  | vcons v vs' => wfk_vl k v ∧ wfk_vls k vs'
  end.

(** Well formed under 0 recursive values, that is with locally closed
    anchors. *)
Notation wf_shdw := (wfk_shdw 0).
Notation wf_nv := (wfk_nv 0).
Notation wf_wvl := (wfk_wvl 0).
Notation wf_vl := (wfk_vl 0).
Notation wf_vls := (wfk_vls 0).

(** A trace is well formed when each of its values is well formed. *)
Fixpoint wf_tr (t : trace) : Prop :=
  match t with
  | Bot => True
  | Ret v => wf_vl v
  | Guard u t' => wf_vl u ∧ wf_tr t'
  | Match s bs => wf_shdw s ∧ wf_brs bs
  end
with wf_brs (bs : brs) : Prop :=
  match bs with
  | bnil => True
  | bcons _ _ t bs' => wf_tr t ∧ wf_brs bs'
  end.

(** ** Well-formed values and the operations on anchors *)

(** A value that is well formed under [k] recursive values is well formed
    under more. *)
Lemma wfk_mono v : ∀ k k', k ≤ k' → wfk_vl k v → wfk_vl k' v.
Proof.
  induction v using vl_ind1; simpl in *; intros k k' LE H; dconj;
    repeat split; eauto.
  - eapply IHv; [|eassumption]. lia.
  - destruct a; simpl in *; auto. lia.
Qed.

(** Open of the index [k] takes away one recursive value around. *)
Lemma wf_open ℓ v : ∀ k, wfk_vl (S k) v → wfk_vl k (open_vl k ℓ v).
Proof.
  induction v using vl_ind1; simpl in *; intros k H; dconj; repeat split; eauto.
  destruct a as [j|z]; simpl in *; auto.
  destruct (Nat.eqb j k) eqn:E; simpl; auto. apply Nat.eqb_neq in E. lia.
Qed.

(** Close to the index [k] adds one recursive value around. *)
Lemma wf_close ℓ v : ∀ k, wfk_vl k v → wfk_vl (S k) (close_vl k ℓ v).
Proof.
  induction v using vl_ind1; simpl in *; intros k H; dconj; repeat split; eauto.
  destruct a as [j|z]; simpl in *; auto.
  destruct (Nat.eqb z ℓ); simpl; auto.
Qed.

(** Rename keeps a value well formed. *)
Lemma wf_ren ξ v : ∀ k k', wfk_vl k v → wfk_vl k (am_vl (fren ξ) k' v).
Proof.
  induction v using vl_ind1; simpl in *; intros k k' H; dconj; repeat split; eauto.
  destruct a; simpl in *; auto.
Qed.

(** [wf_ren] for an environment. *)
Lemma wf_ren_nv ξ σ : wf_nv σ → wf_nv (ren_nv ξ σ).
Proof. exact (wf_ren ξ (vl_exp σ) 0 0). Qed.

(** [wf_ren] for a shadow. *)
Lemma wf_ren_shdw ξ s : wf_shdw s → wf_shdw (ren_shdw ξ s).
Proof. exact (wf_ren ξ (vl_sh s) 0 0). Qed.

(** The replacement of the index [k] by a well-formed recursive value takes
    away one recursive value around. *)
Lemma wf_su u v : ∀ k, wfk_vl 1 u → wfk_vl (S k) v → wfk_vl k (su_vl (funr u) k v).
Proof.
  induction v using vl_ind1; simpl in *; intros k Hu H; dconj; repeat split; eauto.
  destruct a as [j|z]; simpl in *; auto.
  destruct (Nat.eqb j k) eqn:E; simpl.
  - eapply wfk_mono; [|exact Hu]. lia.
  - apply Nat.eqb_neq in E. lia.
Qed.

(** Unroll of a well-formed recursive value gives a well-formed value. *)
Lemma wf_unroll v : wfk_vl 1 v → wf_vl (unroll v).
Proof. intros H. apply wf_su; auto. Qed.

(** Open after close of the same anchor gives a well-formed value back. *)
Lemma open_close ℓ v : ∀ k, wfk_vl k v → open_vl k ℓ (close_vl k ℓ v) = v.
Proof.
  induction v using vl_ind1; simpl in *; intros k H; dconj; veq.
  destruct a as [j|z]; simpl in *.
  - destruct (Nat.eqb j k) eqn:E; auto. apply Nat.eqb_eq in E. lia.
  - destruct (Nat.eqb z ℓ) eqn:E; simpl; auto.
    rewrite Nat.eqb_refl. apply Nat.eqb_eq in E. congruence.
Qed.

(** ** Traces *)

(** The mutual form of [wf_bind]. *)
Lemma wf_bind_mut k (Hk : ∀ v, wf_vl v → wf_tr (k v)) :
  (∀ t, wf_tr t → wf_tr (bind k t)) ∧ (∀ bs, wf_brs bs → wf_brs (bind_brs k bs)).
Proof. apply tr_mutind; simpl; intuition auto. Qed.

(** [bind k t] is well formed when [t] is, and [k v] is for each well-formed
    [v]. *)
Lemma wf_bind k t (Hk : ∀ v, wf_vl v → wf_tr (k v)) (Ht : wf_tr t) : wf_tr (bind k t).
Proof. apply wf_bind_mut; auto. Qed.

(** [tmap] keeps a trace well formed when its 3 functions keep values well
    formed. *)
Lemma wf_tmap_mut g gs h (Hg : ∀ v, wf_vl v → wf_vl (g v))
  (Hgs : ∀ s, wf_shdw s → wf_shdw (gs s)) (Hh : ∀ v, wf_vl v → wf_vl (h v)) :
  (∀ t, wf_tr t → wf_tr (tmap g gs h t)) ∧
  (∀ bs, wf_brs bs → wf_brs (tmap_brs g gs h bs)).
Proof. apply tr_mutind; simpl; intuition auto. Qed.

(** [killg] keeps a trace well formed. *)
Lemma wf_killg ℓ t : wf_tr t → wf_tr (killg ℓ t).
Proof.
  apply wf_tmap_mut; auto.
  - intros; apply wf_ren; auto.
  - intros; apply wf_ren_shdw; auto.
Qed.

(** [ren_tr] keeps a trace well formed. *)
Lemma wf_ren_tr ξ t : wf_tr t → wf_tr (ren_tr ξ t).
Proof.
  apply wf_tmap_mut.
  - intros; apply wf_ren; auto.
  - intros; apply wf_ren_shdw; auto.
  - intros; apply wf_ren; auto.
Qed.

(** The mutual form of [wf_tall]. *)
Lemma wf_tall_mut :
  (∀ t, wf_tr t → tall (wfk_vl 0) (wfk_shdw 0) (wfk_vl 0) t) ∧
  (∀ bs, wf_brs bs → tall_brs (wfk_vl 0) (wfk_shdw 0) (wfk_vl 0) bs).
Proof. apply tr_mutind; simpl; intuition auto. Qed.

(** Each value of a well-formed trace is well formed. *)
Lemma wf_tall t : wf_tr t → tall (wfk_vl 0) (wfk_shdw 0) (wfk_vl 0) t.
Proof. apply wf_tall_mut. Qed.

(** The value of a well-formed weak value is well formed. *)
Lemma wf_force w v (Hw : wf_wvl w) (R : force w = Some v) : wf_vl v.
Proof.
  destruct w; simpl in *; inversion R; subst; auto. apply wf_unroll; auto.
Qed.

(** A read in a well-formed environment gives a well-formed value. *)
Lemma wf_read x σ v (Hσ : wf_nv σ) (R : read x σ = Some v) : wf_vl v.
Proof.
  induction σ as [|s|y w σ IH]; simpl in *; try discriminate.
  - inversion R; subst. simpl. auto.
  - destruct (String.eqb x y); [|intuition auto].
    apply (wf_force w); tauto.
Qed.

(** Each value of a well-formed list is well formed. *)
Lemma wf_vnth vs : ∀ i v, wf_vls vs → vnth i vs = Some v → wf_vl v.
Proof.
  induction vs as [|u vs IH]; simpl; intros i w Hw N; try discriminate.
  destruct Hw as [Hu Hvs]. destruct i as [|i].
  - inversion N; subst; auto.
  - eapply IH; eauto.
Qed.

(** [bindV] keeps an environment well formed. *)
Lemma wf_bindV xs : ∀ vs σ, wf_vls vs → wf_nv σ → wf_nv (bindV xs vs σ).
Proof.
  induction xs as [|x xs IH]; simpl; intros vs σ Hvs Hσ; auto.
  destruct vs as [|v vs]; simpl in *; auto.
  destruct Hvs. split; auto.
Qed.

(** [bindD] keeps an environment well formed. *)
Lemma wf_bindD xs s c : ∀ i σ, wf_shdw s → wf_nv σ → wf_nv (bindD xs s c i σ).
Proof.
  induction xs as [|x xs IH]; simpl; intros i σ Hs Hσ; auto.
Qed.

(** The result of a well-formed trace is well formed. *)
Lemma wf_dest t v (Ht : wf_tr t) (D : dest t = Some v) : wf_vl v.
Proof.
  induction t; simpl in *; try discriminate; intuition auto.
  inversion D; subst; auto.
Qed.

(** One step of [wf_tac]. *)
Ltac wf_step :=
  match goal with
  | |- wf_tr (bind _ _) => apply wf_bind; [intros ? ?|]
  | H : _ ∧ _ |- _ => destruct H
  | |- _ ∧ _ => split
  | |- wf_tr (on_env _ ?m) => destruct m; simpl
  | |- wf_tr (on_mod _ ?m) => destruct m; simpl
  | |- wf_tr (on_cstr _ ?m) => destruct m; simpl
  | |- wf_tr (match ?m with _ => _ end) => destruct m eqn:?; simpl
  | |- wf_tr (if ?b then _ else _) => destruct b eqn:?; simpl
  | _ => progress (simpl in *)
  | _ => solve [eauto using wf_read, wf_vnth, wf_bindV, wf_bindD]
  end.

(** Prove that a trace of the semantics is well formed. The tactic splits the
    binds and the cases. *)
Ltac wf_tac := repeat wf_step.

Section wf_link.
  Context (cl : nv → body → trace) (lk : nv → vl → trace).
  Context (Hcl : ∀ σ b, wf_nv σ → wfb b → wf_tr (cl σ b)).
  Context (Hlk : ∀ σ v, wf_nv σ → wf_vl v → wf_tr (lk σ v)).
  Context (σ0 : nv) (Hσ0 : wf_nv σ0).

  (** ** Linking keeps traces well formed *)

  (** [ap] gives a well-formed trace. *)
  Lemma wf_ap f a (Hf : wf_vl f) (Ha : wf_vl a) : wf_tr (ap cl f a).
  Proof. destruct f; simpl in *; intuition auto. apply Hcl; simpl; auto. Qed.

  (** [rd] gives a well-formed trace. *)
  Lemma wf_rd x m (Hm : wf_vl m) : wf_tr (rd x m).
  Proof. unfold rd. destruct m; wf_tac. Qed.

  (** [ds] gives a well-formed trace. *)
  Lemma wf_ds c i m (Hm : wf_vl m) : wf_tr (ds c i m).
  Proof. unfold ds. destruct m; wf_tac. Qed.

  (** Linking a well-formed environment into a well-formed value gives a
      well-formed trace. *)
  Lemma wf_link :
    (∀ s, wf_shdw s → wf_tr (link_shdw cl lk σ0 s)) ∧
    (∀ σ, wf_nv σ → wf_tr (link_nv cl lk σ0 σ)) ∧
    (∀ v, wf_vl v → wf_tr (link_vl cl lk σ0 v)) ∧
    (∀ vs, wf_vls vs → ∀ c, wf_tr (link_vls cl lk σ0 c vs)).
  Proof.
    apply val_mutind.
    8: { (* The case of a recursive value. *)
      intros x w σ _ IHσ [Hw Hσ]. simpl. apply wf_bind.
      - intros w' Hw'. apply wf_bind; auto.
        intros m Hm. destruct m; simpl in *; auto. split; auto.
        apply wf_close; auto.
      - apply wf_killg. apply Hlk; auto. apply wf_open; auto. }
    all: intros; simpl in *;
      repeat first [apply wf_rd | apply wf_ds | apply wf_ap | wf_step]; auto.
  Qed.

  (** Linking into the spine of a well-formed trace gives a well-formed
      trace. *)
  Lemma wf_link_tr :
    (∀ t, wf_tr t → wf_tr (link_tr cl lk σ0 t)) ∧
    (∀ bs, wf_brs bs →
       wf_brs (link_brs cl lk σ0 bs) ∧ ∀ c n, wf_tr (link_sel cl lk σ0 c n bs)).
  Proof.
    destruct wf_link as (Hs & Hn & Hv & Hvs).
    apply tr_mutind; simpl.
    - auto.
    - auto.
    - intros u t IH [Hu Ht]. wf_tac; auto.
    - intros s bs IH [Hs' Hb]. destruct (IH Hb) as [Hb1 Hb2]. wf_tac; auto.
    - auto.
    - intros c n t bs IHt IHb [Ht Hb]. destruct (IHb Hb) as [Hb1 Hb2].
      repeat split; auto. intros c' n'. destruct (_ && _); auto.
  Qed.

  (** Linking into a well-formed trace gives a well-formed trace. *)
  Lemma wf_link_trace t (Ht : wf_tr t) : wf_tr (link_trace cl lk σ0 t).
  Proof.
    unfold link_trace. apply wf_bind.
    - intros. apply wf_link; auto.
    - apply wf_link_tr; auto.
  Qed.
End wf_link.

(** ** The semantics gives well-formed traces *)

(** The trace of a term at the fuel [n] is well formed, when [call n] gives
    well-formed traces. *)
Lemma wf_denote n (Hcl : ∀ σ b, wf_nv σ → wfb b → wf_tr (call n σ b)) :
  (∀ e, wf_tr (denote n e)) ∧
  (∀ es c, wf_tr (denote_list n c es)) ∧
  (∀ bs, (∀ c vs, wf_vls vs → wf_tr (denote_sel n c vs bs)) ∧
         (∀ s, wf_shdw s → wf_brs (denote_brs n s bs))).
Proof.
  assert (∀ e, wfb (fun m => denote m e)) as Hb by (intros e; exists e; reflexivity).
  apply tm_mutind.
  6: { (* The case of a binding. *)
    intros x e1 IH1 e2 IH2. simpl. apply wf_bind.
    - intros v Hv.
      assert (wfk_vl 1 (close_vl 0 1 v)) as Hc by (apply wf_close; auto).
      apply wf_bind.
      + intros m Hm. destruct m; simpl in *; auto.
      + apply Hcl; simpl; auto.
    - apply wf_killg. apply Hcl; simpl; auto. }
  all: intros; simpl;
    repeat first [progress intros | apply wf_ap | apply Hcl | wf_step]; auto;
    first [apply wf_bindV | apply wf_bindD]; simpl; auto.
Qed.

(** [linkb n] and [linkv n] give well-formed traces, by induction on the
    fuel. *)
Lemma wf_linkbv n :
  (∀ σ b, wf_nv σ → wfb b → wf_tr (linkb n σ b)) ∧
  (∀ σ v, wf_nv σ → wf_vl v → wf_tr (linkv n σ v)).
Proof.
  induction n as [|n [IHb IHv]].
  - split; intros; [rewrite linkb_0|rewrite linkv_0]; simpl; auto.
  - assert (∀ σ b, wf_nv σ → wfb b → wf_tr (call n σ b)) as Hcl.
    { intros. rewrite call_eq. simpl. auto. }
    split.
    + intros σ b Hσ [e ->]. rewrite linkb_S. apply wf_link_trace; auto.
      unfold den. apply wf_denote; auto.
    + intros σ v Hσ Hv. rewrite linkv_S. apply wf_link; auto.
Qed.

(** [linkb] gives a well-formed trace. *)
Lemma wf_linkb n σ b : wf_nv σ → wfb b → wf_tr (linkb n σ b).
Proof. apply wf_linkbv. Qed.

(** [linkv] gives a well-formed trace. *)
Lemma wf_linkv n σ v : wf_nv σ → wf_vl v → wf_tr (linkv n σ v).
Proof. apply wf_linkbv. Qed.

(** [call] gives a well-formed trace. *)
Lemma wf_call n σ b (Hσ : wf_nv σ) (Hb : wfb b) : wf_tr (call n σ b).
Proof. rewrite call_eq. simpl. split; auto. apply wf_linkb; auto. Qed.

(** The trace of a term at each fuel is well formed. *)
Lemma wf_den n e : wf_tr (denote n e).
Proof. apply wf_denote. intros. apply wf_call; auto. Qed.

(** The denotation of a term is a well-formed body. *)
Lemma wfb_den e : wfb (den e).
Proof. exists e; reflexivity. Qed.
