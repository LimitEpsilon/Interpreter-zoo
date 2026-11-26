(** * Equations of traces and linking

    This file proves the monad laws of [bind], and that linking moves through
    [bind]. It also defines the cost of a trace. The files of proofs use
    these equations to split a trace into its parts.

    ** Main definitions

    - [cost]: the number of guards before the first node that is not a guard.

    ** Main results

    - [bind_bind], [bind_Ret], [bind_ext]: the monad laws.
    - [dest_bind], [cost_bind]: the result and the cost of [bind k t].
    - [link_tr_bind], [link_trace_bind]: linking moves through [bind]. *)
From Stdlib Require Import Utf8 String Bool Arith Lia List.
From Denot Require Import Syntax Anchor Domain Nominal Semantics.

(** ** The monad laws *)

(** The mutual form of [bind_ext]. *)
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

(** 2 continuations that are equal at each value give the same trace. *)
Lemma bind_ext k k' t (EXT : ∀ v, k v = k' v) : bind k t = bind k' t.
Proof. apply bind_ext_mut; auto. Qed.

(** The mutual form of [bind_bind]. *)
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

(** [bind] is associative. *)
Lemma bind_bind k k' t : bind k (bind k' t) = bind (fun v => bind k (k' v)) t.
Proof. apply bind_bind_mut. Qed.

(** The mutual form of [bind_Ret]. *)
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

(** [Ret] is a right unit of [bind]. *)
Lemma bind_Ret t : bind Ret t = t.
Proof. apply bind_Ret_mut. Qed.

(** ** The result and the cost *)

(** The number of guards before the first node that is not a guard. For a
    finished trace it is the number of its guards. *)
Fixpoint cost (t : trace) : nat :=
  match t with Guard _ t' => S (cost t') | _ => 0 end.

(** The result of [bind k t] is the result of [k v], for the result [v] of
    [t]. *)
Lemma dest_bind k t :
  dest (bind k t) = match dest t with Some v => dest (k v) | None => None end.
Proof. induction t; simpl; auto. Qed.

(** When [bind k t] is finished, [t] is finished with a result [v], and [k v]
    is finished. *)
Lemma dest_bind_inv k t r (D : dest (bind k t) = Some r) :
  ∃ v, dest t = Some v ∧ dest (k v) = Some r.
Proof. rewrite dest_bind in D. destruct (dest t); [eauto|discriminate]. Qed.

(** When [t] is finished with the result [v] and [k v] is finished, [bind k
    t] is finished. *)
Lemma dest_bind_intro k t v r (D : dest t = Some v) (D' : dest (k v) = Some r) :
  dest (bind k t) = Some r.
Proof. rewrite dest_bind, D. auto. Qed.

(** The cost of [bind k t] is the sum of the costs of [t] and of [k v], for
    the result [v] of [t]. *)
Lemma cost_bind k t v (D : dest t = Some v) :
  cost (bind k t) = cost t + cost (k v).
Proof.
  induction t; simpl in *; try discriminate; auto.
  inversion D; subst. auto.
Qed.

(** [tmap] keeps the cost. *)
Lemma cost_tmap g gs h t : cost (tmap g gs h t) = cost t.
Proof. induction t; simpl; auto. Qed.

(** [killg] keeps the cost. *)
Lemma cost_killg ℓ t : cost (killg ℓ t) = cost t.
Proof. apply cost_tmap. Qed.

Section link_bind.
  Context (cl : nv → body → trace) (lk : nv → vl → trace) (σ0 : nv) (K : vl → trace).

  (** ** Linking moves through [bind] *)

  (** The mutual form of [link_tr_bind]. *)
  Lemma link_tr_bind_mut :
    (∀ t, link_tr cl lk σ0 (bind K t) =
          bind (fun w => link_tr cl lk σ0 (K w)) (link_tr cl lk σ0 t)) ∧
    (∀ bs, link_brs cl lk σ0 (bind_brs K bs) =
           bind_brs (fun w => link_tr cl lk σ0 (K w)) (link_brs cl lk σ0 bs)) ∧
    (∀ bs c n, link_sel cl lk σ0 c n (bind_brs K bs) =
               bind (fun w => link_tr cl lk σ0 (K w)) (link_sel cl lk σ0 c n bs)).
  Proof.
    assert (∀ t, link_tr cl lk σ0 (bind K t) =
                 bind (fun w => link_tr cl lk σ0 (K w)) (link_tr cl lk σ0 t)) as Ht.
    { fix IH 1. intros [|v|u t|s bs]; simpl; auto.
      - rewrite bind_bind. apply bind_ext. intros u'. simpl. f_equal. apply IH.
      - rewrite bind_bind. apply bind_ext. intros m.
        assert (link_brs cl lk σ0 (bind_brs K bs) =
                bind_brs (fun w => link_tr cl lk σ0 (K w)) (link_brs cl lk σ0 bs)) as Hb.
        { induction bs as [|c n t bs IHbs]; simpl; auto. f_equal; auto. }
        assert (∀ c n, link_sel cl lk σ0 c n (bind_brs K bs) =
                bind (fun w => link_tr cl lk σ0 (K w)) (link_sel cl lk σ0 c n bs)) as Hs.
        { clear Hb. intros c n. induction bs as [|c' n' t bs IHbs]; simpl; auto.
          destruct (_ && _); auto. }
        destruct m; simpl; auto; f_equal; auto. }
    split; [auto|split].
    - induction bs; simpl; f_equal; auto.
    - intros bs c n. induction bs; simpl; auto. destruct (_ && _); auto.
  Qed.

  (** Linking into the spine moves through [bind]. *)
  Lemma link_tr_bind t :
    link_tr cl lk σ0 (bind K t) = bind (fun w => link_tr cl lk σ0 (K w)) (link_tr cl lk σ0 t).
  Proof. apply link_tr_bind_mut. Qed.

  (** Linking into [bind K t] links into the spine of [t], then into each [K
      w]. *)
  Lemma link_trace_bind t :
    link_trace cl lk σ0 (bind K t) =
    bind (fun w => link_trace cl lk σ0 (K w)) (link_tr cl lk σ0 t).
  Proof.
    unfold link_trace. rewrite link_tr_bind, bind_bind. reflexivity.
  Qed.
End link_bind.
