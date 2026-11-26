(** * Equational laws of traces and linking *)
From Stdlib Require Import Utf8 String Bool Arith Lia List.
From Denot Require Import Syntax Domain Semantics.

(** ** [bind] is a monad *)

Lemma bind_ext_mut k k' (EXT : ∀ v, k v = k' v) :
  (∀ t, bind k t = bind k' t) ∧ (∀ bs, bind_brs k bs = bind_brs k' bs).
Proof.
  assert (∀ t, bind k t = bind k' t) as Ht.
  { fix IH 1. intros [|v|u t|s bs]; simpl; auto.
    - f_equal. apply IH.
    - f_equal. induction bs as [|c n t bs IHbs]; simpl; auto.
      f_equal; auto. }
  split; auto. induction bs; simpl; f_equal; auto.
Qed.

Lemma bind_ext k k' t (EXT : ∀ v, k v = k' v) : bind k t = bind k' t.
Proof. apply bind_ext_mut; auto. Qed.

Lemma bind_bind_mut k k' :
  (∀ t, bind k (bind k' t) = bind (fun v => bind k (k' v)) t) ∧
  (∀ bs, bind_brs k (bind_brs k' bs) = bind_brs (fun v => bind k (k' v)) bs).
Proof.
  assert (∀ t, bind k (bind k' t) = bind (fun v => bind k (k' v)) t) as Ht.
  { fix IH 1. intros [|v|u t|s bs]; simpl; auto.
    - f_equal. apply IH.
    - f_equal. induction bs as [|c n t bs IHbs]; simpl; auto.
      f_equal; auto. }
  split; auto. induction bs; simpl; f_equal; auto.
Qed.

Lemma bind_bind k k' t : bind k (bind k' t) = bind (fun v => bind k (k' v)) t.
Proof. apply bind_bind_mut. Qed.

Lemma bind_Ret_mut :
  (∀ t, bind Ret t = t) ∧ (∀ bs, bind_brs Ret bs = bs).
Proof.
  assert (∀ t, bind Ret t = t) as Ht.
  { fix IH 1. intros [|v|u t|s bs]; simpl; auto.
    - f_equal. apply IH.
    - f_equal. induction bs as [|c n t bs IHbs]; simpl; auto.
      f_equal; auto. }
  split; auto. induction bs; simpl; f_equal; auto.
Qed.

Lemma bind_Ret t : bind Ret t = t.
Proof. apply bind_Ret_mut. Qed.

(** ** Observations: the returned value, and the number of guards passed *)

Fixpoint cost (t : trace) : nat :=
  match t with Guard _ t' => S (cost t') | _ => 0 end.

Lemma dest_bind k t :
  dest (bind k t) = match dest t with Some v => dest (k v) | None => None end.
Proof. induction t; simpl; auto. Qed.

Lemma dest_bind_inv k t r (D : dest (bind k t) = Some r) :
  ∃ v, dest t = Some v ∧ dest (k v) = Some r.
Proof. rewrite dest_bind in D. destruct (dest t); [eauto|discriminate]. Qed.

Lemma dest_bind_intro k t v r (D : dest t = Some v) (D' : dest (k v) = Some r) :
  dest (bind k t) = Some r.
Proof. rewrite dest_bind, D. auto. Qed.

Lemma cost_bind k t v (D : dest t = Some v) :
  cost (bind k t) = cost t + cost (k v).
Proof.
  induction t; simpl in *; try discriminate; auto.
  inversion D; subst. auto.
Qed.

(** ** Linking distributes over [bind] *)

Section link_bind.
  Context (cl : nv → body → trace) (σ0 : nv) (K : vl → trace).

  Lemma link_tr_bind_mut :
    (∀ t, link_tr cl σ0 (bind K t) =
          bind (fun w => link_tr cl σ0 (K w)) (link_tr cl σ0 t)) ∧
    (∀ bs, link_brs cl σ0 (bind_brs K bs) =
           bind_brs (fun w => link_tr cl σ0 (K w)) (link_brs cl σ0 bs)) ∧
    (∀ bs c n, link_sel cl σ0 c n (bind_brs K bs) =
               bind (fun w => link_tr cl σ0 (K w)) (link_sel cl σ0 c n bs)).
  Proof.
    assert (∀ t, link_tr cl σ0 (bind K t) =
                 bind (fun w => link_tr cl σ0 (K w)) (link_tr cl σ0 t)) as Ht.
    { fix IH 1. intros [|v|u t|s bs]; simpl; auto.
      - rewrite bind_bind. apply bind_ext. intros u'. simpl. f_equal. apply IH.
      - rewrite bind_bind. apply bind_ext. intros m.
        assert (link_brs cl σ0 (bind_brs K bs) =
                bind_brs (fun w => link_tr cl σ0 (K w)) (link_brs cl σ0 bs)) as Hb.
        { induction bs as [|c n t bs IHbs]; simpl; auto. f_equal; auto. }
        assert (∀ c n, link_sel cl σ0 c n (bind_brs K bs) =
                bind (fun w => link_tr cl σ0 (K w)) (link_sel cl σ0 c n bs)) as Hs.
        { clear Hb. intros c n. induction bs as [|c' n' t bs IHbs]; simpl; auto.
          destruct (_ && _); auto. }
        destruct m; simpl; auto; f_equal; auto. }
    split; [auto|split].
    - induction bs; simpl; f_equal; auto.
    - intros bs c n. induction bs; simpl; auto. destruct (_ && _); auto.
  Qed.

  Lemma link_tr_bind t :
    link_tr cl σ0 (bind K t) = bind (fun w => link_tr cl σ0 (K w)) (link_tr cl σ0 t).
  Proof. apply link_tr_bind_mut. Qed.

  Lemma link_trace_bind t :
    link_trace cl σ0 (bind K t) =
    bind (fun w => link_trace cl σ0 (K w)) (link_tr cl σ0 t).
  Proof.
    unfold link_trace. rewrite link_tr_bind, bind_bind. reflexivity.
  Qed.
End link_bind.
