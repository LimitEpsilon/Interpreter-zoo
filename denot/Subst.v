(** * Linking and unrolling

    This file proves that linking moves through unrolling. Assume that
    linking [Σ0] into the recursive value of [w] gives the recursive value of
    [W]. Then linking [Σ0] into the unrolling of [w] gives the unrolling of
    [W]. A read of a variable unrolls, so this result makes a read move
    through linking ([read_link]). [LinkLink.v] uses the 2 lemmas on reads.

    To unroll is to open and then to replace the anchor by the recursive
    value. So the proof has 2 lemmas on the replacement of an anchor.

    ** Main definitions

    - [sub_vl ℓ u]: replace the free anchor [ℓ] by the recursive value of
      [u].
    - [sub_tr ℓ u]: the same for each value of a trace.

    ** Main results

    - [sub2_linkb]: replace an anchor of the environment. The linked trace
      extends the trace with the anchor replaced.
    - [sub1_linkv]: replace an anchor of the value by a recursive value, and
      the same anchor of the result by the linked recursive value.
    - [link_unroll]: linking moves through unrolling, from some fuel.
    - [read_link], [read_link_inv]: a read moves through linking. *)
From Stdlib Require Import Utf8 String Bool Arith Lia List.
From Denot Require Import Syntax Anchor Domain Nominal Semantics Laws Wf Order
  Conv Fresh Equiv.
Set Warnings "-notation-for-abbreviation".

(** Replace the free anchor [ℓ] by the recursive value of [u]. *)
Notation sub_shdw ℓ u := (su_shdw (fsub ℓ u) 0) (only parsing).
Notation sub_nv ℓ u := (su_nv (fsub ℓ u) 0) (only parsing).
Notation sub_vl ℓ u := (su_vl (fsub ℓ u) 0) (only parsing).
Notation sub_vls ℓ u := (su_vls (fsub ℓ u) 0) (only parsing).

(** Replace the free anchor [ℓ] by the recursive value of [u] in each value
    of a trace. *)
Definition sub_tr (ℓ : loc) (u : vl) : trace → trace :=
  tmap (sub_vl ℓ u) (sub_shdw ℓ u) (sub_vl ℓ u).

(** ** The replacement and the other operations on anchors *)

(** Split the case of an anchor into an index, the name [ℓ] and each other
    name. *)
Ltac an_case a z ℓ :=
  destruct a as [?j|z]; simpl; [|destruct (Nat.eqb z ℓ) eqn:?E; simpl]; veq.

(** The replacement does not depend on the number of recursive values around. *)
Lemma sub_k ℓ u v : ∀ k k', su_vl (fsub ℓ u) k v = su_vl (fsub ℓ u) k' v.
Proof.
  induction v using vl_ind1; intros k0 k'; veq.
  an_case a z ℓ.
Qed.

(** The replacement of a fresh anchor changes nothing. *)
Lemma sub_nf ℓ u v : nf_vl ℓ v → ∀ k, su_vl (fsub ℓ u) k v = v.
Proof.
  induction v using vl_ind1; simpl in *; intros H k0; dconj; veq.
  an_case a z ℓ. apply Nat.eqb_eq in E. congruence.
Qed.

(** The replacement by a well-formed recursive value keeps a value well
    formed. *)
Lemma wf_sub ℓ u v : wfk_vl 1 u → ∀ k k', wfk_vl k v → wfk_vl k (su_vl (fsub ℓ u) k' v).
Proof.
  induction v using vl_ind1; simpl in *; intros Hu k0 k' H; dconj;
    repeat split; eauto.
  destruct a as [j|z]; simpl; [split; auto|].
  destruct (Nat.eqb z ℓ); simpl; split; auto.
  eapply wfk_mono; [|exact Hu]. lia.
Qed.

(** A property of each anchor of [u] and of [v] holds after the replacement. *)
Lemma aan_sub (P : anc → Prop) ℓ u v : aan_vl P u → ∀ k, aan_vl P v →
  aan_vl P (su_vl (fsub ℓ u) k v).
Proof.
  induction v using vl_ind1; simpl in *; intros Hu k0 H; try solve [intuition auto].
  destruct a as [j|z]; simpl; [intuition auto|].
  destruct (Nat.eqb z ℓ); simpl; intuition auto.
Qed.

(** Apply an induction hypothesis whose conditions are a well-formed value
    and an inequality. *)
Ltac ihl :=
  match goal with IH : ∀ k d, _ → _ → _ |- _ => eapply IH; [eassumption|lia] end.

(** Apply [ihl] to a part of a value. *)
Ltac ih_lia :=
  first [ solve [ihl] | apply vl_sh_inj; solve [ihl]
        | apply vl_exp_inj; solve [ihl] | eapply vl_cstr_inj; solve [ihl] ].

(** Open of an index that a well-formed value does not have changes nothing. *)
Lemma open_wf ℓ v : ∀ k d, wfk_vl k v → k ≤ d → am_vl (fopen ℓ) d v = v.
Proof.
  induction v using vl_ind1; simpl in *; intros k0 d H LE; dconj; veq;
    try ih_lia.
  destruct a as [j|z]; simpl in *; auto.
  destruct (Nat.eqb j d) eqn:E; auto. apply Nat.eqb_eq in E. lia.
Qed.

(** The replacement of an index that a well-formed value does not have
    changes nothing. *)
Lemma unr_wf w v : ∀ k d, wfk_vl k v → k ≤ d → su_vl (funr w) d v = v.
Proof.
  induction v using vl_ind1; simpl in *; intros k0 d H LE; dconj; veq;
    try ih_lia.
  destruct a as [j|z]; simpl in *.
  - destruct (Nat.eqb j d) eqn:E; [apply Nat.eqb_eq in E; lia|]. f_equal. ih_lia.
  - f_equal. ih_lia.
Qed.

(** The kill of a fresh anchor changes nothing. *)
Lemma kap_nf ℓ v : nf_vl ℓ v → ∀ k, am_vl (fren (kap ℓ)) k v = v.
Proof.
  intros H k. rewrite <- (ren_id v k) at 2. apply ren_ext_nf.
  intros y NE. destruct (Nat.eq_dec y ℓ) as [->|NE']; auto.
  exfalso. apply NE. apply kap_fix; auto.
Qed.

(** The replacement moves through open with another anchor. *)
Lemma sub_open ℓ u ℓ' v (Wu : wfk_vl 1 u) (NE : ℓ' ≠ ℓ) : ∀ d k,
  am_vl (fopen ℓ') d (su_vl (fsub ℓ u) k v) =
  su_vl (fsub ℓ u) k (am_vl (fopen ℓ') d v).
Proof.
  induction v using vl_ind1; intros d k0; veq.
  destruct a as [j|z]; simpl.
  - destruct (Nat.eqb j d); simpl; veq.
    apply Nat.eqb_neq in NE. rewrite NE. veq.
  - destruct (Nat.eqb z ℓ) eqn:E; simpl; rewrite ?E; veq.
    apply (open_wf ℓ' u 1); auto. lia.
Qed.

(** The replacement moves through close of another anchor that is fresh for
    [u]. *)
Lemma sub_close ℓ u ℓ' v (NE : ℓ' ≠ ℓ) (Nu : nf_vl ℓ' u) : ∀ d k,
  am_vl (fclose ℓ') d (su_vl (fsub ℓ u) k v) =
  su_vl (fsub ℓ u) k (am_vl (fclose ℓ') d v).
Proof.
  induction v using vl_ind1; intros d k0; veq.
  destruct a as [j|z]; simpl; [veq|].
  destruct (Nat.eqb z ℓ) eqn:E; simpl.
  - apply Nat.eqb_eq in E. subst z.
    assert (Nat.eqb ℓ ℓ' = false) as E' by (apply Nat.eqb_neq; auto).
    rewrite E'. simpl. rewrite Nat.eqb_refl. veq. apply close_nf; auto.
  - destruct (Nat.eqb z ℓ'); simpl; rewrite ?E; veq.
Qed.

(** The replacement moves through the kill of another anchor that is fresh
    for [u]. *)
Lemma sub_kap ℓ u ℓ' v (NE : ℓ' ≠ ℓ) (NZ : ℓ ≠ 0) (Nu : nf_vl ℓ' u) : ∀ k d,
  am_vl (fren (kap ℓ')) k (su_vl (fsub ℓ u) d v) =
  su_vl (fsub ℓ u) d (am_vl (fren (kap ℓ')) k v).
Proof.
  induction v using vl_ind1; intros k0 d; veq.
  destruct a as [j|z]; simpl; [veq|].
  destruct (Nat.eqb z ℓ) eqn:E; simpl.
  - apply Nat.eqb_eq in E. subst z. rewrite (kap_fix ℓ' ℓ) by auto.
    rewrite Nat.eqb_refl. veq. apply kap_nf; auto.
  - assert (Nat.eqb (kap ℓ' z) ℓ = false) as E'.
    { apply Nat.eqb_neq. apply Nat.eqb_neq in E. unfold kap.
      destruct (Nat.eqb z ℓ'); congruence. }
    rewrite E'. veq.
Qed.

(** The replacement of a name moves through the replacement of an index. *)
Lemma sub_unr ℓ u w v (Wu : wfk_vl 1 u) : ∀ k k' d,
  su_vl (fsub ℓ u) k (su_vl (funr w) d v) =
  su_vl (funr (su_vl (fsub ℓ u) k' w)) d (su_vl (fsub ℓ u) k v).
Proof.
  induction v using vl_ind1; intros k0 k' d; veq.
  destruct a as [j|z]; simpl.
  - destruct (Nat.eqb j d) eqn:E; simpl; rewrite ?E; veq. apply sub_k.
  - destruct (Nat.eqb z ℓ) eqn:E; simpl; rewrite ?E; veq.
    symmetry. apply (unr_wf _ u 1); auto. lia.
Qed.

(** The replacement of an index is open with a fresh anchor, then the
    replacement of that anchor. *)
Lemma unr_sub ℓ u v : nf_vl ℓ v → ∀ d k,
  su_vl (funr u) d v = su_vl (fsub ℓ u) k (am_vl (fopen ℓ) d v).
Proof.
  induction v using vl_ind1; simpl in *; intros H d k0; dconj; veq.
  destruct a as [j|z]; simpl.
  - destruct (Nat.eqb j d); simpl; rewrite ?Nat.eqb_refl; veq.
  - destruct (Nat.eqb z ℓ) eqn:E; veq. apply Nat.eqb_eq in E. congruence.
Qed.

(** To unroll is to open with a fresh anchor and to replace it. *)
Lemma unroll_sub ℓ w : nf_vl ℓ w → unroll w = sub_vl ℓ w (open_vl 0 ℓ w).
Proof. intros H. apply unr_sub; auto. Qed.

(** The unrolling of a closed value is the value with the closed anchor
    replaced. *)
Lemma unroll_close ℓ w' : wf_vl w' →
  unroll (close_vl 0 ℓ w') = sub_vl ℓ (close_vl 0 ℓ w') w'.
Proof.
  intros W. rewrite (unroll_sub ℓ) by apply nf_close_self.
  rewrite open_close; auto.
Qed.

(** A read after the replacement gives the value with the anchor replaced. *)
Lemma read_sub ℓ u x σ v (Wu : wfk_vl 1 u) :
  read x σ = Some v → read x (sub_nv ℓ u σ) = Some (sub_vl ℓ u v).
Proof.
  induction σ as [|s|y w σ IH|y w σ IH|y a σ IH]; simpl; intros R;
    try discriminate.
  - inversion R; subst. reflexivity.
  - destruct (String.eqb x y); [inversion R; subst|]; auto.
  - destruct (String.eqb x y) eqn:E; auto. inversion R; subst.
    unfold unroll. rewrite (sub_unr ℓ u w w Wu 0 1 0). f_equal. f_equal.
    apply sub_k.
  - destruct (String.eqb x y) eqn:E; [discriminate|].
    destruct (fsub ℓ u 0 a); simpl; rewrite E; auto.
Qed.

(** A field of a list after [su_vls] is the field after [su_vl]. *)
Lemma vnth_su g k vs : ∀ i,
  vnth i (su_vls g k vs) = option_map (su_vl g k) (vnth i vs).
Proof. induction vs as [|v vs IH]; simpl; intros [|i]; auto. Qed.

(** [su_vls] keeps the length. *)
Lemma vlen_su g k vs : vlen (su_vls g k vs) = vlen vs.
Proof. induction vs; simpl; auto. Qed.

(** The result after [sub_tr] is the result with the anchor replaced. *)
Lemma dest_sub_tr ℓ u t : dest (sub_tr ℓ u t) = option_map (sub_vl ℓ u) (dest t).
Proof. apply dest_tmap. Qed.

Section sub2.
  Context (ℓ : loc) (W : vl) (NZ : ℓ ≠ 0) (WW : wfk_vl 1 W).
  Local Notation S := (su_vl (fsub ℓ W) 0) (only parsing).
  Local Notation Sn := (su_nv (fsub ℓ W) 0) (only parsing).
  Local Notation ST := (sub_tr ℓ W) (only parsing).

  (** ** An anchor of the environment

      Replace an anchor of the environment by a recursive value. Then the
      linked trace extends the first trace with the anchor replaced. A read
      of the anchor gives [Bot], and a read of the recursive value gives a
      value. *)

  (** The mutual form of [sub_bind_le_P]. *)
  Lemma sub_bind_le_mut (P : vl → Prop) k k'
    (Hk : ∀ v, wf_vl v → P v → le_tr (ST (k v)) (k' (S v))) :
    (∀ t, wf_tr t → leaves P t → ∀ t', le_tr (ST t) t' →
          le_tr (ST (bind k t)) (bind k' t')) ∧
    (∀ bs, wf_brs bs → leaves_brs P bs → ∀ bs',
       le_brs (tmap_brs S (su_shdw (fsub ℓ W) 0) S bs) bs' →
       le_brs (tmap_brs S (su_shdw (fsub ℓ W) 0) S (bind_brs k bs))
              (bind_brs k' bs')).
  Proof.
    apply tr_mutind; simpl; auto.
    - intros v Wv Pv t' ->. simpl. auto.
    - intros u t IH [Wu Wt] Pt [| |u' t'|]; simpl; try tauto. intros [-> H]. auto.
    - intros s bs IH [Ws Wb] Pb [| | |s' bs']; simpl; try tauto.
      intros [-> H]. auto.
    - intros _ _ bs' ->. simpl. auto.
    - intros c n t bs IHt IHb [Wt Wb] [Pt Pb] [|c' n' t' bs']; simpl; try tauto.
      intros (-> & -> & Ht & Hb). auto.
  Qed.

  (** [bind] keeps the relation between a trace with the anchor replaced and
      its extension. The continuations must keep it at each leaf that
      satisfies [P]. *)
  Lemma sub_bind_le_P (P : vl → Prop) k k' t t' (Wt : wf_tr t) (Pt : leaves P t)
    (LE : le_tr (ST t) t')
    (Hk : ∀ v, wf_vl v → P v → le_tr (ST (k v)) (k' (S v))) :
    le_tr (ST (bind k t)) (bind k' t').
  Proof. eapply sub_bind_le_mut; eauto. Qed.

  (** [sub_bind_le_P] with no condition on the leaves. *)
  Lemma sub_bind_le k k' t t' (Wt : wf_tr t) (LE : le_tr (ST t) t')
    (Hk : ∀ v, wf_vl v → le_tr (ST (k v)) (k' (S v))) :
    le_tr (ST (bind k t)) (bind k' t').
  Proof.
    eapply sub_bind_le_P with (P := fun _ => True); eauto. apply leaves_True.
  Qed.

  (** The replacement moves through the kill of another anchor that is fresh
      for [W]. *)
  Lemma sub_killg ℓ' t (NE : ℓ' ≠ ℓ) (N : nf_vl ℓ' W) :
    ST (killg ℓ' t) = killg ℓ' (ST t).
  Proof.
    unfold sub_tr, killg. rewrite !tmap_tmap. apply tmap_ext.
    eapply tall_impl; [| | |apply (proj1 tall_True_mut t)]; simpl; auto.
    - intros u _. symmetry. apply sub_kap; auto.
    - intros s _. symmetry. apply vl_sh_inj. apply (sub_kap ℓ W ℓ' (vl_sh s)); auto.
  Qed.

  Section at_fuel.
    Context (n : nat).
    Context (IHb : ∀ σ b, wf_nv σ → wfb b →
      le_tr (ST (linkb n σ b)) (linkb n (Sn σ) b)).
    Context (IHv : ∀ σ v, wf_nv σ → wf_vl v → nf_vl ℓ v →
      le_tr (ST (linkv n σ v)) (linkv n (Sn σ) v)).
    Context (σ0 : nv) (Wσ0 : wf_nv σ0).
    Local Notation σ1 := (su_nv (fsub ℓ W) 0 σ0) (only parsing).

    Let Wσ1 : wf_nv σ1.
    Proof. apply (wf_sub ℓ W (vl_exp σ0)); auto. Qed.

    (** [ap] of the values with the anchor replaced extends the trace of [ap]
        with the anchor replaced. *)
    Lemma sub2_ap f a (Wf : wf_vl f) (Wa : wf_vl a) :
      le_tr (ST (ap (call n) f a)) (ap (call n) (S f) (S a)).
    Proof.
      destruct f; simpl in *; auto. destruct Wf. rewrite !call_eq. simpl.
      split; auto. apply (IHb (nv_bd x a σ) b); simpl; auto.
    Qed.

    (** The same for a read. *)
    Lemma sub2_rd x m (Wm : wf_vl m) : le_tr (ST (rd x m)) (rd x (S m)).
    Proof.
      unfold rd. destruct m; simpl; auto.
      destruct (read x σ) eqn:R; simpl; auto.
      rewrite (read_sub ℓ W x σ v WW R). simpl. auto.
    Qed.

    (** The same for a field. *)
    Lemma sub2_ds c i m (Wm : wf_vl m) : le_tr (ST (ds c i m)) (ds c i (S m)).
    Proof.
      unfold ds. destruct m; simpl; auto.
      destruct (String.eqb c c0); simpl; auto. rewrite vnth_su.
      destruct (vnth i vs); simpl; auto.
    Qed.

    (** Linking the environment with the anchor replaced into a value extends
        the first linked trace with the anchor replaced. The anchor must be
        fresh for the value. *)
    Lemma sub2_vals :
      (∀ s, wf_shdw s → nf_shdw ℓ s →
         le_tr (ST (link_shdw (call n) (linkv n) σ0 s))
               (link_shdw (call n) (linkv n) σ1 s)) ∧
      (∀ σ, wf_nv σ → nf_nv ℓ σ →
         le_tr (ST (link_nv (call n) (linkv n) σ0 σ))
               (link_nv (call n) (linkv n) σ1 σ)) ∧
      (∀ v, wf_vl v → nf_vl ℓ v →
         le_tr (ST (link_vl (call n) (linkv n) σ0 v))
               (link_vl (call n) (linkv n) σ1 v)) ∧
      (∀ vs, wf_vls vs → nf_vls ℓ vs → ∀ c,
         le_tr (ST (link_vls (call n) (linkv n) σ0 c vs))
               (link_vls (call n) (linkv n) σ1 c vs)).
    Proof.
      assert (∀ σ b, wf_nv σ → wfb b → wf_tr (call n σ b)) as Wcl
          by (intros; apply wf_call; auto).
      assert (∀ σ v, wf_nv σ → wf_vl v → wf_tr (linkv n σ v)) as Wlk
          by (intros; apply wf_linkv; auto).
      destruct (wf_link (call n) (linkv n) Wcl Wlk σ0 Wσ0) as (Ws & Wn & Wv & Wvs).
      apply val_mutind.
      - simpl. auto.
      - intros s x IH Wf N. simpl. apply sub_bind_le; auto.
        intros; apply sub2_rd; auto.
      - intros s v IHs IHv' [W1 W2] [N1 N2]. simpl. apply sub_bind_le; auto.
        intros f Wf. apply sub_bind_le; auto. intros a Wa. apply sub2_ap; auto.
      - intros s c i IH Wf N. simpl. apply sub_bind_le; auto.
        intros; apply sub2_ds; auto.
      - simpl. auto.
      - intros s IH Wf N. simpl. apply sub_bind_le; auto.
        intros m Wm. destruct m; simpl; auto.
      - intros x v σ IHv' IHσ [W1 W2] [N1 N2]. simpl. apply sub_bind_le; auto.
        intros v' Wv'. apply sub_bind_le; auto.
        intros m Wm. destruct m; simpl; auto.
      - (* The case of a recursive value. Open it with one anchor that is fresh for each object. *)
        intros x w σ _ IHσ [W1 W2] [N1 N2].
        set (ℓ' := Datatypes.S (Nat.max (sup_nv σ0) (Nat.max (sup_nv σ1)
                     (Nat.max (sup_vl w) (Nat.max (sup_vl W) ℓ))))).
        assert (ℓ' ≠ 0) as Z' by (unfold ℓ'; lia).
        assert (ℓ' ≠ ℓ) as NE by (unfold ℓ'; lia).
        assert (nf_nv ℓ' σ0) as F0 by (apply sup_nf_nv; unfold ℓ'; lia).
        assert (nf_nv ℓ' σ1) as F1 by (apply sup_nf_nv; unfold ℓ'; lia).
        assert (nf_vl ℓ' w) as Fw by (apply sup_nf; unfold ℓ'; lia).
        assert (nf_vl ℓ' W) as FW by (apply sup_nf; unfold ℓ'; lia).
        assert (wf_vl (open_vl 0 ℓ' w)) as Wo by (apply wf_open; auto).
        rewrite (linkn_mu n σ0 x w σ ℓ'), (linkn_mu n σ1 x w σ ℓ'); auto.
        apply sub_bind_le.
        + apply wf_killg. auto.
        + rewrite sub_killg; auto. apply le_killg. apply IHv; auto.
          apply nf_open; auto.
        + intros w' Ww'. apply sub_bind_le; auto.
          intros m Wm. destruct m; simpl; auto.
          rewrite (sub_close ℓ W ℓ' w' NE FW 0 0).
          rewrite (sub_k ℓ W (am_vl (fclose ℓ') 0 w') 0 1). reflexivity.
      - intros x a σ IH [W1 W2] [N1 N2]. simpl. apply sub_bind_le; auto.
        intros m Wm. destruct m; simpl; auto.
        destruct a as [j|z]; simpl; auto.
        destruct (Nat.eqb z ℓ) eqn:E; simpl; auto.
        apply Nat.eqb_eq in E. congruence.
      - intros σ IH. exact IH.
      - intros s IH. exact IH.
      - intros x b σ IH [W1 W2] N. simpl. apply sub_bind_le; auto.
        intros m Wm. destruct m; simpl; auto.
      - intros c vs IH Wf N. apply IH; auto.
      - simpl. auto.
      - intros v vs IHv' IHvs [W1 W2] [N1 N2] c. simpl. apply sub_bind_le; auto.
        intros v' Wv'. apply sub_bind_le; auto.
        intros m Wm. destruct m; simpl; auto.
    Qed.

    (** The same for the spine of a trace. *)
    Lemma sub2_tr :
      (∀ t, wf_tr t → nft ℓ t →
         le_tr (ST (link_tr (call n) (linkv n) σ0 t))
               (link_tr (call n) (linkv n) σ1 t)) ∧
      (∀ bs, wf_brs bs →
         tall_brs (aan_vl (fun a => a ≠ F ℓ)) (aan_shdw (fun a => a ≠ F ℓ))
           (aan_vl (fun a => a ≠ F ℓ)) bs →
         le_brs (tmap_brs S (su_shdw (fsub ℓ W) 0) S
                   (link_brs (call n) (linkv n) σ0 bs))
                (link_brs (call n) (linkv n) σ1 bs) ∧
         ∀ c k, le_tr (ST (link_sel (call n) (linkv n) σ0 c k bs))
                      (link_sel (call n) (linkv n) σ1 c k bs)).
    Proof.
      assert (∀ σ b, wf_nv σ → wfb b → wf_tr (call n σ b)) as Wcl
          by (intros; apply wf_call; auto).
      assert (∀ σ v, wf_nv σ → wf_vl v → wf_tr (linkv n σ v)) as Wlk
          by (intros; apply wf_linkv; auto).
      destruct (wf_link (call n) (linkv n) Wcl Wlk σ0 Wσ0) as (Ws & Wn & Wv & Wvs).
      destruct sub2_vals as (Vs & Vn & Vv & Vvs).
      apply tr_mutind; simpl.
      - auto.
      - intros v Wv' Nv. rewrite sub_nf; auto.
      - intros u t IH [W1 W2] [N1 N2]. apply sub_bind_le; auto.
        intros u' Wu'. simpl. auto.
      - intros s bs IH [W1 W2] [N1 N2]. destruct (IH W2 N2) as [IH1 IH2].
        apply sub_bind_le; auto.
        intros m Wm. destruct m; simpl; auto.
        split; auto. rewrite vlen_su. apply IH2.
      - auto.
      - intros c k t bs IHt IHbs [W1 W2] [N1 N2].
        destruct (IHbs W2 N2) as [IH1 IH2].
        repeat split; auto. intros c' k'. destruct (_ && _); auto.
    Qed.

    (** The same for a trace. *)
    Lemma sub2_trace t (Wt : wf_tr t) (N : nft ℓ t) :
      le_tr (ST (link_trace (call n) (linkv n) σ0 t))
            (link_trace (call n) (linkv n) σ1 t).
    Proof.
      assert (∀ σ b, wf_nv σ → wfb b → wf_tr (call n σ b)) as Wcl
          by (intros; apply wf_call; auto).
      assert (∀ σ v, wf_nv σ → wf_vl v → wf_tr (linkv n σ v)) as Wlk
          by (intros; apply wf_linkv; auto).
      unfold link_trace.
      apply sub_bind_le_P with (P := aan_vl (fun a => a ≠ F ℓ)).
      - apply wf_link_tr; auto.
      - apply link_tr_leaves. eapply leaves_tall; eauto.
      - apply sub2_tr; auto.
      - intros v Wv Nv. rewrite (sub_nf ℓ W v Nv 0). apply sub2_vals; auto.
    Qed.
  End at_fuel.
End sub2.

(** ** An anchor of the environment, at each fuel *)

(** [linkb n] and [linkv n] with the anchor of the environment replaced, by
    induction on the fuel. *)
Lemma sub2_linkbv ℓ W (NZ : ℓ ≠ 0) (WW : wfk_vl 1 W) n :
  (∀ σ b, wf_nv σ → wfb b →
     le_tr (sub_tr ℓ W (linkb n σ b)) (linkb n (sub_nv ℓ W σ) b)) ∧
  (∀ σ v, wf_nv σ → wf_vl v → nf_vl ℓ v →
     le_tr (sub_tr ℓ W (linkv n σ v)) (linkv n (sub_nv ℓ W σ) v)).
Proof.
  induction n as [|n [IHb IHv]].
  - split; intros; rewrite ?linkb_0, ?linkv_0; simpl; auto.
  - split.
    + intros σ b Wσ [e ->]. rewrite !linkb_S. apply sub2_trace; auto.
      * apply wf_den.
      * apply nf_den; auto.
    + intros σ v Wσ Wv Nv. rewrite !linkv_S. apply sub2_vals; auto.
Qed.

(** When [linkb n σ b] is finished with the result [r], the anchor of [σ] can
    be replaced. The result is then [r] with the anchor replaced. *)
Lemma sub2_linkb ℓ W n σ b r (NZ : ℓ ≠ 0) (WW : wfk_vl 1 W) (Wσ : wf_nv σ)
  (Wb : wfb b) (D : dest (linkb n σ b) = Some r) :
  dest (linkb n (sub_nv ℓ W σ) b) = Some (sub_vl ℓ W r).
Proof.
  eapply le_dest; [apply sub2_linkbv; auto|].
  rewrite dest_sub_tr, D. reflexivity.
Qed.

Section sub1.
  Context (Σ0 : nv) (WΣ0 : wf_nv Σ0).
  Context (ℓ : loc) (NZ : ℓ ≠ 0) (NΣ : nf_nv ℓ Σ0).
  Context (w : vl) (Ww : wfk_vl 1 w) (Nw : nf_vl ℓ w).
  Context (N0 : nat) (w' : vl).
  Context (D0 : dest (linkv N0 Σ0 (open_vl 0 ℓ w)) = Some w').
  Local Notation W := (close_vl 0 ℓ w') (only parsing).
  Local Notation s := (su_vl (fsub ℓ w) 0) (only parsing).
  Local Notation S := (su_vl (fsub ℓ (close_vl 0 ℓ w')) 0) (only parsing).

  Let Wo : wf_vl (open_vl 0 ℓ w).
  Proof. apply wf_open; auto. Qed.
  Let Ww' : wf_vl w'.
  Proof. eapply wf_dest; [|exact D0]. apply wf_linkv; auto. Qed.
  Let WW : wfk_vl 1 W.
  Proof. apply wf_close; auto. Qed.

  Section at_fuel.
    Context (n : nat).
    Context (IHlk : ∀ v r, wf_vl v → dest (linkv n Σ0 v) = Some r →
      ∀ m, n + N0 ≤ m → dest (linkv m Σ0 (s v)) = Some (S r)).

    (** ** An anchor of the value

        The recursive value of [w] links to the recursive value of [W] under
        [Σ0]. Assume that [v] links to [r]. Then [v] with the anchor [ℓ]
        replaced by the recursive value of [w] links to [r] with [ℓ] replaced
        by the recursive value of [W]. *)

    (** When [T] is finished with a result [r], each [T' m] with [m] at least
        [n + N0] is finished with [r] after the replacement. *)
    Definition SB (T : trace) (T' : nat → trace) : Prop :=
      ∀ r, dest T = Some r → ∀ m, n + N0 ≤ m → dest (T' m) = Some (S r).

    (** [SB] for [bind]. *)
    Lemma SB_bind T T' k k' :
      SB T T' → (∀ v, dest T = Some v → SB (k v) (fun m => k' m (S v))) →
      SB (bind k T) (fun m => bind (k' m) (T' m)).
    Proof.
      intros H1 H2 r D m Hm. apply dest_bind_inv in D as (v & Dv & Dk).
      eapply dest_bind_intro; [apply H1; eauto|]. apply (H2 v Dv r Dk m Hm).
    Qed.

    Let Wcl : ∀ m σ b, wf_nv σ → wfb b → wf_tr (call m σ b).
    Proof. intros; apply wf_call; auto. Qed.
    Let Wlk : ∀ m σ v, wf_nv σ → wf_vl v → wf_tr (linkv m σ v).
    Proof. intros; apply wf_linkv; auto. Qed.

    (** A read of a module after the replacement gives the result after the
        replacement. *)
    Lemma sub1_rd x mv r : dest (rd x mv) = Some r → dest (rd x (S mv)) = Some (S r).
    Proof.
      unfold rd. destruct mv; simpl; try discriminate.
      - destruct (read x σ) eqn:R; simpl; try discriminate. intros D.
        inversion D; subst. rewrite (read_sub _ _ x σ r WW R). reflexivity.
      - intros D. inversion D; subst. reflexivity.
    Qed.

    (** The same for a field. *)
    Lemma sub1_ds c i mv r :
      dest (ds c i mv) = Some r → dest (ds c i (S mv)) = Some (S r).
    Proof.
      unfold ds. destruct mv; simpl; try discriminate.
      - intros D. inversion D; subst. reflexivity.
      - destruct (String.eqb c c0); simpl; try discriminate. rewrite vnth_su.
        destruct (vnth i vs); simpl; try discriminate.
        intros D. inversion D; subst. reflexivity.
    Qed.

    (** The same for [ap], with more fuel. *)
    Lemma sub1_ap f a r (Wf : wf_vl f) (Wa : wf_vl a)
      (D : dest (ap (call n) f a) = Some r) :
      ∀ m, n + N0 ≤ m → dest (ap (call m) (S f) (S a)) = Some (S r).
    Proof.
      intros m Hm. destruct f; simpl in *; try discriminate.
      - inversion D; subst. reflexivity.
      - destruct Wf as [Wb Wσ]. rewrite call_eq in *. simpl in *.
        assert (wf_nv (nv_bd x a σ)) as Wc by (simpl; auto).
        pose proof (sub2_linkb ℓ W n _ b r NZ WW Wc Wb D) as D'.
        assert (wf_nv (su_nv (fsub ℓ W) 0 (nv_bd x a σ))) as Wc'
            by (apply (wf_sub ℓ W (vl_exp (nv_bd x a σ))); auto).
        pose proof (up_linkb n m ltac:(lia) _ b _ Wc' Wb D') as U.
        simpl in U, D'. rewrite U. exact D'.
    Qed.

    (** The main lemma at the fuel [n], for shadows, environments, values and
        lists of values. *)
    Lemma sub1_vals :
      (∀ v0, wf_shdw v0 →
         SB (link_shdw (call n) (linkv n) Σ0 v0)
            (fun m => link_shdw (call m) (linkv m) Σ0 (su_shdw (fsub ℓ w) 0 v0))) ∧
      (∀ σ, wf_nv σ →
         SB (link_nv (call n) (linkv n) Σ0 σ)
            (fun m => link_nv (call m) (linkv m) Σ0 (su_nv (fsub ℓ w) 0 σ))) ∧
      (∀ v, wf_vl v →
         SB (link_vl (call n) (linkv n) Σ0 v)
            (fun m => link_vl (call m) (linkv m) Σ0 (s v))) ∧
      (∀ vs, wf_vls vs → ∀ c,
         SB (link_vls (call n) (linkv n) Σ0 c vs)
            (fun m => link_vls (call m) (linkv m) Σ0 c (su_vls (fsub ℓ w) 0 vs))).
    Proof.
      destruct (wf_link (call n) (linkv n) (Wcl n) (Wlk n) Σ0 WΣ0)
        as (Ws & Wn & Wv & Wvs).
      apply val_mutind.
      - intros _ r D m Hm. simpl in *. inversion D; subst. simpl.
        assert (su_nv (fsub ℓ W) 0 Σ0 = Σ0) as EΣ
            by (apply vl_exp_inj; apply (sub_nf ℓ W (vl_exp Σ0) NΣ 0)).
        rewrite EΣ. reflexivity.
      - intros s0 x IH Wf. simpl. apply SB_bind; auto.
        intros mv _ r D m Hm. apply sub1_rd; auto.
      - intros s0 v IHs IHv [W1 W2]. simpl. apply SB_bind; auto.
        intros f Df. apply SB_bind; auto.
        intros a Da r D m Hm. apply sub1_ap; auto.
        + eapply wf_dest; [|exact Df]; auto.
        + eapply wf_dest; [|exact Da]; auto.
      - intros s0 c i IH Wf. simpl. apply SB_bind; auto.
        intros mv _ r D m Hm. apply sub1_ds; auto.
      - intros _ r D m Hm. simpl in *. inversion D; subst. reflexivity.
      - intros s0 IH Wf. simpl. apply SB_bind; auto.
        intros mv _ r D m Hm. destruct mv; simpl in *; try discriminate;
          inversion D; subst; reflexivity.
      - intros x v σ IHv IHσ [W1 W2]. simpl. apply SB_bind; auto.
        intros v' _. apply SB_bind; auto.
        intros mv _ r D m Hm. destruct mv; simpl in *; try discriminate;
          inversion D; subst; reflexivity.
      - (* The case of a recursive value. *)
        intros x w2 σ _ IHσ [W1 W2] r D m Hm.
        set (ℓ2 := Datatypes.S (Nat.max (sup_nv Σ0) (Nat.max (sup_vl w2)
                     (Nat.max (sup_vl w) (Nat.max (sup_vl W) ℓ))))).
        assert (ℓ2 ≠ 0) as Z2 by (unfold ℓ2; lia).
        assert (ℓ2 ≠ ℓ) as NE by (unfold ℓ2; lia).
        assert (nf_nv ℓ2 Σ0) as F0 by (apply sup_nf_nv; unfold ℓ2; lia).
        assert (nf_vl ℓ2 w2) as F2 by (apply sup_nf; unfold ℓ2; lia).
        assert (nf_vl ℓ2 w) as Fw by (apply sup_nf; unfold ℓ2; lia).
        assert (nf_vl ℓ2 W) as FW by (apply sup_nf; unfold ℓ2; lia).
        assert (wf_vl (open_vl 0 ℓ2 w2)) as Wo2 by (apply wf_open; auto).
        rewrite (linkn_mu n Σ0 x w2 σ ℓ2) in D; auto.
        apply dest_bind_inv in D as (w2' & D1 & D2). rewrite dest_killg in D1.
        apply dest_bind_inv in D2 as (mσ & D3 & D4).
        destruct (link_nv_leaf _ _ _ _ _ D3) as (σ' & ->). simpl in D4.
        inversion D4; subst r; clear D4.
        change (su_nv (fsub ℓ w) 0 (nv_mu x w2 σ)) with
          (nv_mu x (su_vl (fsub ℓ w) 1 w2) (su_nv (fsub ℓ w) 0 σ)).
        rewrite (linkn_mu m Σ0 x _ _ ℓ2); auto.
        + eapply dest_bind_intro.
          * rewrite dest_killg. rewrite (sub_open ℓ w ℓ2 w2 Ww NE 0 1).
            rewrite (sub_k ℓ w _ 1 0). apply (IHlk _ _ Wo2 D1 m Hm).
          * eapply dest_bind_intro; [apply (IHσ W2 _ D3 m Hm)|]. simpl.
            rewrite (sub_close ℓ W ℓ2 w2' NE FW 0 0).
            rewrite (sub_k ℓ W (am_vl (fclose ℓ2) 0 w2') 0 1). reflexivity.
        + apply wf_sub; auto.
        + apply aan_sub; auto.
      - (* The case of an anchor. *)
        intros x a σ IHσ [W1 W2] r D m Hm. simpl in D.
        apply dest_bind_inv in D as (mσ & D3 & D4).
        destruct (link_nv_leaf _ _ _ _ _ D3) as (σ' & ->). simpl in D4.
        inversion D4; subst r; clear D4.
        pose proof (IHσ W2 _ D3 m Hm) as D5.
        destruct a as [j|z].
        + simpl. eapply dest_bind_intro; [exact D5|]. reflexivity.
        + simpl. destruct (Nat.eqb z ℓ) eqn:E.
          * (* The anchor is [ℓ]. Linking resolves the recursive value of [w] here. *)
            rewrite (linkn_mu m Σ0 x w _ ℓ); auto.
            eapply dest_bind_intro.
            -- rewrite dest_killg.
               rewrite (up_linkv N0 m ltac:(lia) Σ0 _ _ WΣ0 Wo D0). exact D0.
            -- eapply dest_bind_intro; [exact D5|]. reflexivity.
          * eapply dest_bind_intro; [exact D5|]. reflexivity.
      - intros σ IH. exact IH.
      - intros s0 IH. exact IH.
      - intros x b σ IH [W1 W2]. simpl. apply SB_bind; auto.
        intros mv _ r D m Hm. destruct mv; simpl in *; try discriminate;
          inversion D; subst; reflexivity.
      - intros c vs IH Wf. apply IH; auto.
      - intros _ c r D m Hm. simpl in *. inversion D; subst. reflexivity.
      - intros v vs IHv IHvs [W1 W2] c. simpl. apply SB_bind; auto.
        intros v' _. apply SB_bind; auto.
        intros mv _ r D m Hm. destruct mv; simpl in *; try discriminate;
          inversion D; subst; reflexivity.
    Qed.
  End at_fuel.

  (** When [linkv n Σ0 v] is finished with [r], linking into [v] after the
      replacement is finished with [r] after the replacement, from the fuel
      [n + N0]. *)
  Lemma sub1_linkv n : ∀ v r, wf_vl v → dest (linkv n Σ0 v) = Some r →
    ∀ m, n + N0 ≤ m → dest (linkv m Σ0 (s v)) = Some (S r).
  Proof.
    induction n as [|n IH]; intros v r Wv D m Hm.
    - rewrite linkv_0 in D. discriminate.
    - rewrite linkv_S in D. destruct m as [|m]; [lia|]. rewrite linkv_S.
      apply (proj1 (proj2 (proj2 (sub1_vals n IH))) v Wv r D m). lia.
  Qed.

  (** Linking into the unrolling of [w] gives the unrolling of [W], from the
      fuel [N0 + N0]. *)
  Lemma link_unroll m (Hm : N0 + N0 ≤ m) :
    dest (link_vl (call m) (linkv m) Σ0 (unroll w)) = Some (unroll W).
  Proof.
    rewrite <- linkv_S. rewrite (unroll_sub ℓ w Nw), (unroll_close ℓ w' Ww').
    apply (sub1_linkv N0 _ _ Wo D0). lia.
  Qed.
End sub1.

Section read_link.
  Context (Σ0 : nv) (WΣ0 : wf_nv Σ0).

  (** ** A read moves through linking *)

  (** A finished linking into a recursive value opens it with a fresh anchor.
      It gives a result for the opened value and a result for the rest of the
      environment. *)
  Lemma mu_inv m x w σ r (Ww : wfk_vl 1 w)
    (D : dest (link_nv (call m) (linkv m) Σ0 (nv_mu x w σ)) = Some r) :
    ∃ ℓ w' σ', ℓ ≠ 0 ∧ nf_nv ℓ Σ0 ∧ nf_vl ℓ w ∧
      dest (linkv m Σ0 (open_vl 0 ℓ w)) = Some w' ∧
      dest (link_nv (call m) (linkv m) Σ0 σ) = Some (vl_exp σ') ∧
      r = vl_exp (nv_mu x (close_vl 0 ℓ w') σ').
  Proof.
    simpl in D. apply dest_bind_inv in D as (w' & D1 & D2).
    rewrite dest_killg in D1. apply dest_bind_inv in D2 as (mσ & D3 & D4).
    destruct (link_nv_leaf _ _ _ _ _ D3) as (σ' & ->). simpl in D4.
    inversion D4; subst r.
    exists (fresh Σ0 w), w', σ'. repeat split; auto.
    - apply fresh_pos.
    - apply fresh_nv.
    - apply fresh_vl.
  Qed.

  (** Read a variable of [σ], then link into the value. The result is the
      read of the same variable in the linked environment. *)
  Lemma read_link m x σ : ∀ σ' v r, wf_nv σ →
    dest (link_nv (call m) (linkv m) Σ0 σ) = Some (vl_exp σ') →
    read x σ = Some v →
    dest (link_vl (call m) (linkv m) Σ0 v) = Some r → read x σ' = Some r.
  Proof.
    induction σ as [|s|y u σ IH|y w σ IH|y a σ IH]; simpl; intros σ' v r Wσ D R Dv;
      try discriminate.
    - inversion R; subst; clear R. simpl in Dv.
      apply dest_bind_inv in D as (m0 & Dm & D).
      apply dest_bind_inv in Dv as (m' & Dm' & Dv).
      rewrite Dm in Dm'. inversion Dm'; subst; clear Dm'.
      unfold rd in Dv. destruct m'; simpl in *; try discriminate.
      + inversion D; subst. destruct (read x σ'); simpl in Dv; congruence.
      + inversion D; subst. simpl. congruence.
    - destruct Wσ as [Wu Wσ].
      apply dest_bind_inv in D as (u' & Du & D).
      apply dest_bind_inv in D as (m0 & Dm & D).
      destruct m0; simpl in D; try discriminate. inversion D; subst; clear D.
      simpl. destruct (String.eqb x y).
      + inversion R; subst. congruence.
      + eauto.
    - destruct Wσ as [Ww Wσ].
      destruct (mu_inv m y w σ _ Ww D) as (ℓ & w' & σ1 & Z & N1 & N2 & D1 & D2 & E).
      inversion E; subst σ'; clear E. simpl.
      destruct (String.eqb x y).
      + inversion R; subst v; clear R.
        pose proof (link_unroll Σ0 WΣ0 ℓ Z N1 w Ww N2 m w' D1 (m + m) (Nat.le_refl _))
          as U.
        assert (wf_vl (unroll w)) as Wun by (apply wf_unroll; auto).
        rewrite (up_vl m (m + m) ltac:(lia) Σ0 WΣ0 _ _ Wun Dv) in U. congruence.
      + eauto.
    - destruct Wσ as [Wa Wσ].
      apply dest_bind_inv in D as (m0 & Dm & D).
      destruct m0; simpl in D; try discriminate. inversion D; subst; clear D.
      simpl. destruct (String.eqb x y); [discriminate|eauto].
  Qed.

  (** A read in the linked environment comes from a read in [σ]. From some
      fuel, linking into that value gives the same result. *)
  Lemma read_link_inv m x σ : ∀ σ' r, wf_nv σ →
    dest (link_nv (call m) (linkv m) Σ0 σ) = Some (vl_exp σ') →
    read x σ' = Some r →
    ∃ v M, read x σ = Some v ∧
      ∀ m', M ≤ m' → dest (link_vl (call m') (linkv m') Σ0 v) = Some r.
  Proof.
    induction σ as [|s|y u σ IH|y w σ IH|y a σ IH]; simpl; intros σ' r Wσ D R.
    - inversion D; subst. simpl in R. discriminate.
    - exists (vl_sh (Read s x)), m. split; auto.
      assert (dest (link_vl (call m) (linkv m) Σ0 (vl_sh (Read s x))) = Some r) as Dv.
      { simpl. apply dest_bind_inv in D as (m0 & Dm & D).
        eapply dest_bind_intro; eauto. unfold rd.
        destruct m0; simpl in *; try discriminate; inversion D; subst.
        - rewrite R. auto.
        - simpl in R. inversion R; auto. }
      intros m' Hm'.
      rewrite (up_vl m m' Hm' Σ0 WΣ0 (vl_sh (Read s x)) r Wσ Dv). exact Dv.
    - destruct Wσ as [Wu Wσ].
      apply dest_bind_inv in D as (u' & Du & D).
      apply dest_bind_inv in D as (m0 & Dm & D).
      destruct m0; simpl in D; try discriminate. inversion D; subst; clear D.
      simpl in R. destruct (String.eqb x y).
      + inversion R; subst. exists u, m. split; auto. intros m' Hm'.
        rewrite (up_vl m m' Hm' Σ0 WΣ0 u r Wu Du). exact Du.
      + eauto.
    - destruct Wσ as [Ww Wσ].
      destruct (mu_inv m y w σ _ Ww D) as (ℓ & w' & σ1 & Z & N1 & N2 & D1 & D2 & E).
      inversion E; subst σ'; clear E. simpl in R.
      destruct (String.eqb x y).
      + inversion R; subst r; clear R. exists (unroll w), (m + m). split; auto.
        intros m' Hm'. apply (link_unroll Σ0 WΣ0 ℓ Z N1 w Ww N2 m w' D1 m' Hm').
      + eauto.
    - destruct Wσ as [Wa Wσ].
      apply dest_bind_inv in D as (m0 & Dm & D).
      destruct m0; simpl in D; try discriminate. inversion D; subst; clear D.
      simpl in R. destruct (String.eqb x y); [discriminate|eauto].
  Qed.
End read_link.
