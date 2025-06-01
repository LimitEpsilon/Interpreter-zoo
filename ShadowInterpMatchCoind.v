From Stdlib Require Import Utf8.
From Stdlib Require Import PArith Lia.
From Stdlib Require Import String List.
From Paco Require Import paco.
Import ListNotations.

Local Open Scope string_scope.
Local Unset Elimination Schemes.
Local Set Primitive Projections.

Module StreamTest.
  Variant streamF {T stream : Type} :=
  | snil
  | scons (hd : T) (tl : stream)
  .

  Arguments streamF : clear implicits.

  Inductive streamA {T : Type} := Str (k : streamF T streamA).
  Arguments streamA : clear implicits.

  Definition streamA_ind T P (Psnil : P (Str snil))
    (Pscons : ∀ (hd : T) (tl : streamA T), P tl → P (Str (scons hd tl)))
  : ∀ s, P s :=
    fix go s :=
      match s with
      | Str snil => Psnil
      | Str (scons hd tl) => Pscons hd tl (go tl)
      end.

  CoInductive stream {T : Type} := mkStream { obs_st : streamF T stream }.
  Arguments stream : clear implicits.
  Arguments mkStream {_} _.

  (* define approximation order *)
  Definition le_streamF {T st} (le_st : st → st → Prop) :=
    fun (sF sF' : streamF T st) =>
    match sF with
    | snil => True
    | scons hd tl =>
      match sF' with
      | scons hd' tl' => hd = hd' ∧ le_st tl tl'
      | _ => False
      end
    end.

  Definition lt_streamF {T st} (lt_st : st → st → Prop) :=
    fun (sF sF' : streamF T st) =>
    match sF with
    | snil =>
      match sF' with
      | snil => False
      | scons _ _ => True
      end
    | scons hd tl =>
      match sF' with
      | scons hd' tl' => hd = hd' ∧ lt_st tl tl'
      | _ => False
      end
    end.

  Fixpoint le_streamA {T} (s s' : streamA T) :=
    match s with
    | Str k =>
      match s' with
      | Str k' => le_streamF le_streamA k k'
      end
    end.

  Fixpoint lt_streamA {T} (s s' : streamA T) :=
    match s with
    | Str k =>
      match s' with
      | Str k' => lt_streamF lt_streamA k k'
      end
    end.

  Fixpoint nth_approxA {T} (s : streamA T) (n : nat) : streamA T :=
    Str match n with
    | 0 => snil
    | S n' =>
      match s with
      | Str snil => snil
      | Str (scons hd tl) => scons hd (nth_approxA tl n')
      end
    end.

  Fixpoint nth_approx {T} (s : stream T) (n : nat) : streamA T :=
    Str match n with
    | 0 => snil
    | S n' =>
      match obs_st s with
      | snil => snil
      | scons hd tl => scons hd (nth_approx tl n')
      end
    end.

  Definition eq_streamF T eq_st (s s' : stream T) :=
    match obs_st s with
    | snil =>
      match obs_st s' with
      | snil => True
      | _ => False
      end
    | scons hd tl =>
      match obs_st s' with
      | scons hd' tl' => hd = hd' ∧ eq_st tl tl'
      | snil => False
      end
    end.
 
  Lemma eq_streamF_monotone {T} : monotone2 (eq_streamF T).
  Proof.
    repeat intro. unfold eq_streamF in *.
    destruct (obs_st _); auto.
    destruct (obs_st _); intuition auto.
  Qed.

  Hint Resolve eq_streamF_monotone : paco.

  Definition eq_stream {T} := paco2 (eq_streamF T) bot2.

  (* eq_stream is an equivalence relation *)
  Lemma eq_stream_refl {T} (s : stream T)
  : eq_stream s s.
  Proof.
    revert s. pcofix CIH.
    intros. pfold. unfold eq_streamF.
    destruct (obs_st s); auto.
  Qed.

  Lemma eq_stream_sym {T} (s s' : stream T) (EQ : eq_stream s s')
  : eq_stream s' s.
  Proof.
    revert s s' EQ. pcofix CIH.
    intros. pfold. unfold eq_streamF.
    destruct (obs_st _) eqn:OBS'.
    - punfold EQ.
      unfold eq_streamF in EQ.
      rewrite OBS' in *. auto.
    - punfold EQ. unfold eq_streamF in EQ.
      rewrite OBS' in *.
      destruct (obs_st s) eqn:OBS; auto.
      destruct EQ as (? & EQ); subst.
      split; auto.
      destruct EQ as [?|?]; try contradiction.
      right. auto.
  Qed.

  Lemma eq_stream_trans {T} (s s' s'' : stream T)
    (EQ : eq_stream s s') (EQ' : eq_stream s' s'')
  : eq_stream s s''.
  Proof.
    revert s s' s'' EQ EQ'. pcofix CIH.
    intros. punfold EQ. punfold EQ'. pfold.
    unfold eq_streamF in *.
    destruct (obs_st s) eqn:OBS.
    { destruct (obs_st s') eqn:OBS'; try contradiction. auto. }
    destruct (obs_st s') eqn:OBS'; try contradiction.
    destruct EQ as (? & EQ); subst.
    destruct (obs_st s'') eqn:OBS''; try contradiction.
    destruct EQ' as (? & EQ'); subst.
    pclearbot.
    split; auto. right. eauto.
  Qed.

  Lemma eq_streamA_eq_stream {T} (s s' : stream T)
    (LE : ∀ n, ∃ m, le_streamA (nth_approx s n) (nth_approx s' m))
    (LE' : ∀ n, ∃ m, le_streamA (nth_approx s' n) (nth_approx s m))
  : eq_stream s s'.
  Proof.
    revert s s' LE LE'. pcofix CIH.
    intros. pfold. unfold eq_streamF.
    destruct (obs_st _) eqn:OBS.
    - destruct (LE' 1) as (m & LE'').
      destruct m; simpl in *; destruct (obs_st s') eqn:OBS'; auto.
      rewrite OBS in *. cbn in LE''. auto.
    - destruct (obs_st s') eqn:OBS'.
      { specialize (LE 1) as (m & LE'').
        destruct m; simpl in *. rewrite OBS in *. simpl in *. auto.
        rewrite OBS, OBS' in *. simpl in *. auto. }
      destruct (LE 1) as (m & LE''). destruct m; simpl in *.
      { rewrite OBS in *. simpl in *. contradiction. }
      rewrite OBS, OBS' in *. simpl in *. destruct LE'' as (? & _); subst.
      split; auto. clear m.
      right. apply CIH; intros.
      { destruct (LE (S n)) as (m & LE'').
        destruct m; simpl in *. rewrite OBS in *. destruct LE''.
        rewrite OBS, OBS' in *.
        exists m. eapply LE''. }
      { destruct (LE' (S n)) as (m & LE'').
        destruct m; simpl in *. rewrite OBS' in *. destruct LE''.
        rewrite OBS, OBS' in *.
        exists m. eapply LE''. }
  Qed.

  Lemma le_streamA_refl {T} (s : streamA T) :
    le_streamA s s.
  Proof. induction s; simpl; auto. Qed.

  Lemma le_streamA_trans {T} :
    (∀ s' : streamA T,
      ∀ s s'', le_streamA s s' → le_streamA s' s'' → le_streamA s s'').
  Proof.
    induction s'; destruct s; destruct k; simpl.
    - destruct s''; auto.
    - intuition auto.
    - destruct s''. destruct k; intuition auto.
    - intros ? (? & LE); subst.
      destruct s''; intuition auto.
      destruct k; intuition auto.
  Qed.

  Lemma lt_streamA_trans {T} :
    (∀ s' : streamA T,
      ∀ s s'', lt_streamA s s' → lt_streamA s' s'' → lt_streamA s s'').
  Proof.
    induction s'; destruct s; destruct k; simpl.
    - destruct s''; auto.
    - intuition auto.
    - destruct s''. destruct k; intuition auto.
    - intros ? (? & LE); subst.
      destruct s''; intuition auto.
      destruct k; intuition auto.
  Qed.

  Lemma le_lt_eq {T} (s s' : streamA T) :
    le_streamA s s' ↔
    s = s' ∨ lt_streamA s s'.
  Proof.
    revert s'. induction s; simpl.
    { destruct s'; destruct k; simpl; intuition auto. }
    destruct s'; destruct k; simpl; intuition auto; subst; try congruence;
    try rewrite IHs in *; intuition auto; subst; eauto.
    match goal with H : _ |- _ => revert H end.
    inversion 1; subst; eauto.
  Qed.

  Lemma eq_stream_eq_approx {T} (s s' : stream T) (EQ : eq_stream s s')
  : ∀ n, nth_approx s n = nth_approx s' n.
  Proof.
    intros; revert s s' EQ; induction n; simpl; intros; auto.
    punfold EQ. unfold eq_streamF in EQ.
    destruct (obs_st s) eqn:OBS; destruct (obs_st s') eqn:OBS';
    auto; destruct EQ; subst.
    pclearbot.
    erewrite IHn; eauto.
  Qed.

  (* s = s' ↔ ⌊ s ⌋ ≈ ⌊ s' ⌋ *)
  Lemma eq_stream_iff_eq_streamA {T} (s s' : stream T) :
    eq_stream s s' ↔
    (∀ n, ∃ m, le_streamA (nth_approx s n) (nth_approx s' m)) ∧
    (∀ n, ∃ m, le_streamA (nth_approx s' n) (nth_approx s m)).
  Proof.
    split; [|intro; apply eq_streamA_eq_stream; intuition auto].
    intro EQ. apply eq_stream_sym in EQ as EQ'.
    split; intros; exists n; erewrite eq_stream_eq_approx; eauto.
    all: apply le_streamA_refl.
  Qed.

  Definition stable {T} (s : nat → streamA T) :=
    ∀ n, lt_streamA (s n) (s (S n)) ∨ ∀ m (LE : n ≤ m), s n = s m
  .

  Definition stable_le {T} (s : nat → streamA T) (ST : stable s)
  : ∀ n m (LE : n ≤ m), le_streamA (s n) (s m).
  Proof.
    do 2 intro. revert n s ST. induction m; simpl.
    { intros. assert (n = 0) by lia; subst. apply le_streamA_refl. }
    intros. inversion LE; subst. apply le_streamA_refl.
    eapply le_streamA_trans. apply IHm; auto.
    rewrite le_lt_eq.
    destruct (ST m); auto.
  Qed.

  Lemma nth_approx_stable {T} (s : stream T) :
    stable (nth_approx s).
  Proof.
    intro. revert s. induction n; intros; simpl.
    { destruct (obs_st s) eqn:OBS; intuition auto. right.
      induction m; simpl; eauto; rewrite OBS; auto. }
    destruct (obs_st s) eqn:OBS; simpl.
    { right. induction m; simpl; eauto; rewrite OBS; auto. }
    destruct (obs_st tl) eqn:OBS'.
    - right. induction m; [lia|].
      intros. simpl. rewrite OBS. do 2 f_equal.
      destruct (IHn tl).
      { simpl in *; rewrite OBS' in *.
        destruct (nth_approx tl n); destruct k; simpl in *; intuition. }
      assert (n ≤ m) by lia; eauto.
    - destruct (IHn tl).
      { simpl in *; rewrite OBS' in *. eauto. }
      right. intros. destruct m; [lia|].
      simpl in *; rewrite OBS. do 2 f_equal.
      assert (n ≤ m) by lia; eauto.
  Qed.

  CoFixpoint mkStream' {T} (s : nat → streamA T) : stream T :=
    match s 1 with
    | Str snil => {| obs_st := snil |} (* s 0 must be nil *)
    | Str (scons hd _) => {|
      obs_st := scons hd (mkStream' (fun n =>
        match s (S n) with
        | Str snil => Str snil
        | Str (scons _ tl) => tl
        end))
      |}
    end.

  Lemma mkStream'_ext {T} (s s' : nat → streamA T) (EXT : ∀ n, s n = s' n) :
    ∀ d, nth_approx (mkStream' s) d = nth_approx (mkStream' s') d.
  Proof.
    intros. revert s s' EXT. induction d; intros; simpl; eauto.
    rewrite <- EXT. destruct (s 1); destruct k; simpl; eauto.
    erewrite IHd; eauto; simpl.
    intros. rewrite EXT. eauto.
  Qed.

  Fixpoint depth {T} (s : streamA T) :=
    match s with
    | Str snil => 0
    | Str (scons _ tl) => S (depth tl)
    end.

  Lemma stable_tl {T} (s : nat → streamA T) (INC : stable s)
    (NONNIL : s 1 ≠ Str snil)
  : stable (fun n =>
      match s (S n) with
      | Str snil => Str snil
      | Str (scons _ tl) => tl
      end).
  Proof.
    destruct (s 1) eqn:EQ; destruct k. congruence.
    intro n'.
    specialize (stable_le s INC 1 (S n') ltac:(lia)).
    specialize (stable_le s INC 1 (S (S n')) ltac:(lia)).
    rewrite EQ.
    destruct (s (S n')) eqn:OBS; destruct k; simpl.
    destruct 2.
    destruct (s (S (S n'))) eqn:OBS'; destruct k; simpl.
    destruct 1.
    intuition auto; subst.
    destruct (INC (S n')) as [LT|EQ''].
    rewrite OBS, OBS' in LT. simpl in LT. left; apply LT.
    right. intros.
    rewrite <- EQ'' by lia.
    rewrite OBS. auto.
  Qed.

  Lemma le_streamA_nth_approxA {T} (s s' : streamA T) (LE : le_streamA s s')
  : ∀ d (LEd : d ≤ depth s), nth_approxA s d = nth_approxA s' d.
  Proof.
    intros. revert s' LE d LEd.
    induction s; simpl.
    { destruct s'; destruct d; simpl; intros; auto; lia. }
    destruct s'; destruct d; simpl; intros; auto.
    destruct k; destruct LE; subst.
    erewrite IHs; eauto. lia.
  Qed.

  Lemma le_streamA_depth {T} (s s' : streamA T) (LE : le_streamA s s')
  : depth s ≤ depth s'.
  Proof.
    revert s' LE. induction s; simpl; [lia|].
    destruct s'; destruct k; intros; destruct LE; subst.
    simpl. assert (depth s ≤ depth tl) by auto.
    lia.
  Qed.

  Lemma nth_approxA_depth {T} (s : streamA T)
  : ∀ d (LE : depth s ≤ d), nth_approxA s d = s.
  Proof.
    induction s; simpl; destruct d; simpl; auto.
    - lia.
    - intros. repeat f_equal. apply IHs. lia.
  Qed.

  Lemma stable_approx_mkStream' {T} (s : nat → streamA T) (INC : stable s)
  : ∀ d n (DEPTH : d ≤ depth (s n)),
      nth_approxA (s n) d = nth_approx (mkStream' s) d.
  Proof.
    intro. revert s INC. induction d; simpl.
    - intros. destruct (s n); destruct k; simpl in *; congruence.
    - intros. destruct (s n) eqn:EQ; destruct k; simpl in *. lia.
      destruct (s 1) eqn:EQ'; destruct k; simpl.
      { assert (∀ n, s n = Str snil) as RR.
        { specialize (INC 0). destruct INC as [LT|STABLE].
          rewrite EQ' in LT. destruct (s 0); destruct k; destruct LT.
          rewrite <- STABLE in EQ' by lia. intros. rewrite <- STABLE by lia. auto. }
        rewrite RR in EQ. congruence. }
      set (s' m :=
        match s (S m) with
        | Str snil => Str snil
        | Str (scons _ tl') => tl'
        end).
      assert (stable s') as ST' by (apply stable_tl; auto; congruence).
      specialize (IHd s' ST') as IHd'.
      destruct n.
      { specialize (stable_le s INC 0 1 ltac:(lia)).
        rewrite EQ, EQ'; simpl; intros (? & LE); subst.
        do 2 f_equal; auto.
        rewrite <- (IHd' 0); subst s'; simpl; rewrite EQ'.
        apply le_streamA_nth_approxA; auto. lia.
        transitivity (depth tl). lia. apply le_streamA_depth; auto. }
      specialize (stable_le s INC 1 (S n) ltac:(lia)).
      rewrite EQ, EQ'; simpl; intros (? & _); subst.
      do 2 f_equal; auto.
      rewrite <- (IHd' n); subst s'; simpl; rewrite EQ; auto. lia.
  Qed.

  Lemma stable_mkStream' {T} (s : nat → streamA T) (INC : stable s)
  : ∀ n, s n = nth_approx (mkStream' s) (depth (s n)).
  Proof.
    intros. erewrite <- stable_approx_mkStream'; auto.
    symmetry. apply nth_approxA_depth. auto.
  Qed.
End StreamTest.

Definition var := string.

Inductive shdw {vl} :=
  | Rd (x : var)
  | Ap (s : shdw) (v : vl)
.

Arguments shdw : clear implicits.

Inductive nv {vl} :=
  | Init
  | nv_bd (x : var) (v : vl) (σ : nv)
.

Arguments nv : clear implicits.

Inductive vl {tr} :=
  | vl_sh (s : shdw vl) (* s *)
  | vl_clos (x : var) (t : tr) (σ : nv vl) (* ⟨ λx.t, σ ⟩ *)
.

Arguments vl : clear implicits.

Definition shadow trace := shdw (vl trace).
Definition env trace := nv (vl trace).

Inductive traceF {trace} :=
  | Stuck
  | Ret (v : vl trace)
  | Step (s : env trace) (k : traceF)
.

Arguments traceF : clear implicits.

Section ind.
  Context {T : Type}.
  Let Value := vl T.
  Let Env := env T.
  Let Shadow := shadow T.
  Let TraceF := traceF T.
  Context (Ptr : T → Prop) (tr_ind : ∀ t, Ptr t)
          (Pshdw : Shadow → Prop)
          (Pnv : Env → Prop)
          (Pvl : Value → Prop)
          (PtrF : TraceF → Prop).
  Context (PRd : ∀ x, Pshdw (Rd x))
          (PAp : ∀ s v (IHs : Pshdw s) (IHv : Pvl v), Pshdw (Ap s v)).
  Context (PInit : Pnv Init)
          (Pnv_bd : ∀ x v σ (IHv : Pvl v) (IHσ : Pnv σ), Pnv (nv_bd x v σ)).
  Context (Pvl_sh : ∀ s (IHs : Pshdw s), Pvl (vl_sh s))
          (Pvl_clos : ∀ x k σ (IHk : Ptr k) (IHσ : Pnv σ), Pvl (vl_clos x k σ)).
  Context (PStuck : PtrF Stuck)
          (PRet : ∀ v (IHv : Pvl v), PtrF (Ret v))
          (PStep : ∀ σ t (IHσ : Pnv σ) (IHt : PtrF t), PtrF (Step σ t)).

  Definition shdw_ind vl_ind :=
    fix go s : Pshdw s :=
      match s as s' return Pshdw s' with
      | Rd x => PRd x
      | Ap f v => PAp f v (go f) (vl_ind v)
      end.

  Definition nv_ind vl_ind :=
    fix go σ : Pnv σ :=
      match σ as σ' return Pnv σ' with
      | Init => PInit
      | nv_bd x v σ' => Pnv_bd x v σ' (vl_ind v) (go σ')
      end.

  Fixpoint vl_ind v : Pvl v :=
    match v as v' return Pvl v' with
    | vl_sh s => Pvl_sh s (shdw_ind vl_ind s)
    | vl_clos x t σ => Pvl_clos x t σ (tr_ind t) (nv_ind vl_ind σ)
    end.

  Fixpoint traceF_ind t : PtrF t :=
    match t as k return PtrF k with
    | Stuck => PStuck
    | Ret v => PRet v (vl_ind v)
    | Step σ t => PStep σ t (nv_ind vl_ind σ) (traceF_ind t)
    end.

  Lemma pre_val_ind :
    (∀ s, Pshdw s) ∧ (∀ σ, Pnv σ) ∧ (∀ v, Pvl v) ∧ (∀ t, PtrF t).
  Proof.
    pose proof (nv_ind vl_ind).
    pose proof (shdw_ind vl_ind).
    eauto using vl_ind, traceF_ind.
  Qed.
End ind.

Inductive term :=
  | Var (x : var)
  | Lam (x : var) (t : term)
  | App (fn arg : term)
.

Definition term_ind P
  (PVar : ∀ x, P (Var x))
  (PLam : ∀ x e (IHbody : P e), P (Lam x e))
  (PApp : ∀ fn arg (IHfn : P fn) (IHarg : P arg), P (App fn arg)) :=
  fix go t :=
    match t as t' return P t' with
    | Var x => PVar x
    | Lam x e => PLam x e (go e)
    | App fn arg => PApp fn arg (go fn) (go arg)
    end.

Definition ω := Lam "x" (App (Var "x") (Var "x")).
Definition ι := Lam "x" (Var "x").
Definition fst' := Lam "x" (Lam "y" (Var "x")).

(* Finite approximation, annotated with source term *)
Inductive trace := Tr (e : term) (k : nat → traceF trace).

Section trace_ind.
  Let Value := vl trace.
  Let Env := env trace.
  Let Shadow := shadow trace.
  Context (Pshdw : Shadow → Prop)
          (Pnv : Env → Prop)
          (Pvl : Value → Prop)
          (PtrF : traceF trace → Prop)
          (Ptr : trace → Prop).
  Context (PRd : ∀ x, Pshdw (Rd x))
          (PAp : ∀ s v (IHs : Pshdw s) (IHv : Pvl v), Pshdw (Ap s v)).
  Context (PInit : Pnv Init)
          (Pnv_bd : ∀ x v σ (IHv : Pvl v) (IHσ : Pnv σ), Pnv (nv_bd x v σ)).
  Context (Pvl_sh : ∀ s (IHs : Pshdw s), Pvl (vl_sh s))
          (Pvl_clos : ∀ x k σ (IHk : Ptr k) (IHσ : Pnv σ), Pvl (vl_clos x k σ)).
  Context (PStuck : PtrF Stuck)
          (PRet : ∀ v (IHv : Pvl v), PtrF (Ret v))
          (PStep : ∀ σ t (IHσ : Pnv σ) (IHt : PtrF t), PtrF (Step σ t)).
  Context (PTr : ∀ e t (IHt : ∀ n, PtrF (t n)), Ptr (Tr e t)).

  Fixpoint trace_ind (t : trace) :=
    let traceF_ind' := traceF_ind _ trace_ind _ _ _ _
      PRd PAp
      PInit Pnv_bd
      Pvl_sh Pvl_clos
      PStuck PRet PStep in
    match t with
    | Tr e t => PTr e t (fun n => traceF_ind' (t n))
    end.

  Lemma val_ind :
    (∀ s, Pshdw s) ∧ (∀ σ, Pnv σ) ∧ (∀ v, Pvl v) ∧ (∀ tF, PtrF tF) ∧ (∀ t, Ptr t).
  Proof.
    pose proof
      (pre_val_ind _ trace_ind _ _ _ _
        PRd PAp
        PInit Pnv_bd
        Pvl_sh Pvl_clos
        PStuck PRet PStep).
    intuition (auto using trace_ind).
  Qed.
End trace_ind.

Section rel.
  Definition rel_shdw {vl vl'}
    (rel_vl : vl → vl' → Prop) :=
    fix rel_s (s : shdw vl) (s' : shdw vl') : Prop :=
      match s with
      | Rd x =>
        match s' with
        | Rd x' => x = x'
        | _ => False
        end
      | Ap f v =>
        match s' with
        | Ap f' v' => rel_s f f' ∧ rel_vl v v'
        | _ => False
        end
      end.

  Definition rel_nv {vl vl'}
    (rel_vl : vl → vl' → Prop) :=
    fix rel_nv (σ : nv vl) (σ' : nv vl') : Prop :=
      match σ with
      | Init =>
        match σ' with
        | Init => True
        | _ => False
        end
      | nv_bd x v σ =>
        match σ' with
        | nv_bd x' v' σ' => x = x' ∧ rel_vl v v' ∧ rel_nv σ σ'
        | _ => False
        end
      end.

  Definition rel_vl {tr tr'}
    (rel_tr : tr → tr' → Prop) :=
    fix rel_v (v : vl tr) (v' : vl tr') :=
      match v with
      | vl_sh s =>
        match v' with
        | vl_sh s' => rel_shdw rel_v s s'
        | _ => False
        end
      | vl_clos x t σ =>
        match v' with
        | vl_clos x' t' σ' => x = x' ∧ rel_tr t t' ∧ rel_nv rel_v σ σ'
        | _ => False
        end
      end.

  (* partial order between finite approximations *)
  Definition rel_traceF {tr tr'}
    (rel_tr : tr → tr' → Prop) :=
    fix rel_tF (t : traceF tr) (t' : traceF tr') :=
      match t with
      | Stuck => True
      | Ret v =>
        match t' with
        | Ret v' => rel_vl rel_tr v v'
        | _ => False
        end
      | Step σ k =>
        match t' with
        | Step σ' k' => rel_nv (rel_vl rel_tr) σ σ' ∧ rel_tF k k'
        | _ => False
        end
      end.

  Definition rel_shadow {tr tr'} (r : tr → tr' → Prop) :=
    rel_shdw (rel_vl r)
  .
  Definition rel_env {tr tr'} (r : tr → tr' → Prop) :=
    rel_nv (rel_vl r)
  .

  Context {tr tr' : Type}
    (r r' : tr → tr' → Prop)
    (LEt : ∀ t t', r t t' → r' t t').

  Definition rel_shadow_monotone (s : shdw (vl tr)) :=
    ∀ s', rel_shadow r s s' → rel_shadow r' s s'
  .
  Definition rel_env_monotone (σ : nv (vl tr)) :=
    ∀ σ', rel_env r σ σ' → rel_env r' σ σ'
  .
  Definition rel_vl_monotone (v : vl tr) :=
    ∀ v', rel_vl r v v' → rel_vl r' v v'
  .
  Definition rel_traceF_monotone (t : traceF tr) :=
    ∀ t', rel_traceF r t t' → rel_traceF r' t t'
  .

  Lemma rel_monotone :
    (∀ s, rel_shadow_monotone s) ∧
    (∀ σ, rel_env_monotone σ) ∧
    (∀ v, rel_vl_monotone v) ∧
    (∀ t, rel_traceF_monotone t).
  Proof.
    apply (pre_val_ind _ (fun _ => I));
    cbv [rel_shadow_monotone rel_env_monotone rel_vl_monotone rel_traceF_monotone];
    cbv [rel_shadow rel_env];
    simpl; intros; auto;
    match goal with
    | _ : match ?x with _ => _ end |- _ =>
      destruct x; intuition auto
    end.
  Qed.
End rel.

Section wf.
  Definition wf_shdw {vl} (wf_vl : vl → Prop) :=
    fix wf (s : shdw vl) : Prop :=
      match s with
      | Rd _ => True
      | Ap f v => wf f ∧ wf_vl v
      end.

  Definition wf_nv {vl} (wf_vl : vl → Prop) :=
    fix wf (σ : nv vl) : Prop :=
      match σ with
      | Init => True
      | nv_bd _ v σ => wf_vl v ∧ wf σ
      end.

  Definition wf_vl {tr} (wf_tr : tr → Prop) :=
    fix wf (v : vl tr) :=
      match v with
      | vl_sh s => wf_shdw wf s
      | vl_clos x t σ => wf_tr t ∧ wf_nv wf σ
      end.

  (* partial order between finite approximations *)
  Definition wf_traceF {tr} (wf_tr : tr → Prop) :=
    fix wf (t : traceF tr) :=
      match t with
      | Stuck => True
      | Ret v => wf_vl wf_tr v
      | Step σ k => wf_nv (wf_vl wf_tr) σ ∧ wf k
      end.

  Definition wf_shadow {tr} (wf_tr : tr → Prop) :=
    wf_shdw (wf_vl wf_tr)
  .

  Definition wf_env {tr} (wf_tr : tr → Prop) :=
    wf_nv (wf_vl wf_tr)
  .
End wf.

Fixpoint le_trace (t t' : trace) :=
  match t with
  | Tr e k =>
    match t' with
    | Tr e' k' => e = e' ∧ ∀ n, ∃ m, rel_traceF le_trace (k n) (k' m)
    end
  end.

Lemma le_trace_refl :
  let le_trF := rel_traceF le_trace in
  let le_vl := rel_vl le_trace in
  let le_nv := rel_nv le_vl in
  let le_shdw := rel_shdw le_vl in
  (∀ s, le_shdw s s) ∧
  (∀ σ, le_nv σ σ) ∧
  (∀ v, le_vl v v) ∧
  (∀ t, le_trF t t) ∧
  (∀ t : trace, le_trace t t).
Proof. cbn zeta. apply val_ind; simpl; eauto. Qed.

Lemma le_trace_trans :
  let le_trF := rel_traceF le_trace in
  let le_vl := rel_vl le_trace in
  let le_nv := rel_nv le_vl in
  let le_shdw := rel_shdw le_vl in
  (∀ s',
    ∀ s s'', le_shdw s s' → le_shdw s' s'' → le_shdw s s'') ∧
  (∀ σ',
    ∀ σ σ'', le_nv σ σ' → le_nv σ' σ'' → le_nv σ σ'') ∧
  (∀ v',
    ∀ v v'', le_vl v v' → le_vl v' v'' → le_vl v v'') ∧
  (∀ tF',
    ∀ tF tF'', le_trF tF tF' → le_trF tF' tF'' → le_trF tF tF'') ∧
  (∀ t',
    ∀ t t'', le_trace t t' → le_trace t' t'' → le_trace t t'').
Proof.
  cbn zeta. apply val_ind; simpl; intros;
  match goal with
  | |- rel_shdw _ ?s ?s'' =>
    destruct s; simpl in *; intuition eauto;
    subst; destruct s''; intuition eauto
  | |- rel_nv _ ?σ ?σ'' =>
    destruct σ; simpl in *; intuition eauto;
    subst; destruct σ''; intuition eauto
  | |- rel_vl _ ?v ?v'' =>
    destruct v; simpl in *; intuition eauto;
    subst; destruct v''; intuition eauto
  | |- rel_traceF _ ?tF ?tF'' =>
    destruct tF; simpl in *; intuition eauto;
    subst; destruct tF''; intuition eauto
  | |- le_trace ?t ?t'' =>
    destruct t; simpl in *; intuition eauto;
    subst; destruct t''; intuition eauto
  end.
  match reverse goal with
  | H : _ |- _ => destruct (H n) as (m & ?)
  end.
  match goal with
  | H : _ |- _ => destruct (H m) as (? & ?)
  end.
  eauto.
Qed.

Section link.
  Context {trace : Type}.
  Context (link_trace : env trace → trace → (vl trace → traceF trace) → traceF trace).

  Definition rd x :=
    fix rd (σ : env trace) :=
      match σ with
      | Init => vl_sh (Rd x)
      | nv_bd x' v σ' => if x =? x' then v else rd σ'
      end.

  Definition ap f a k :=
    match f with
    | vl_sh f' => k (vl_sh (Ap f' a))
    | vl_clos x t σ => link_trace (nv_bd x a σ) t k
    end.

  Lemma rel_rd {r} x σ σ' (REL : rel_nv (rel_vl r) σ σ')
  : rel_vl r (rd x σ) (rd x σ').
  Proof.
    revert σ σ' REL.
    refine (fix go σ :=
      match σ with
      | Init => fun σ' =>
        match σ' with
        | Init => _
        | _ => _
        end
      | nv_bd x v σ => fun σ' =>
        match σ' with
        | nv_bd x' v' σ' => _
        | _ => _
        end
      end); simpl; try solve [destruct 1]; auto.
    intros (? & RELv & RELσ); subst.
    destruct (_ =? _); auto.
  Qed.

  Definition link_shdw link_value σ0 :=
    fix link (s : shadow trace) k :=
      match s with
      | Rd x => k (rd x σ0)
      | Ap s' v =>
        let k_s f :=
          let k_v a := ap f a k
          in link_value v k_v
        in link s' k_s
      end.

  Definition link_nv link_value (σ0 : env trace) :=
    fix link (σ : env trace) k : traceF trace :=
      match σ with
      | Init => k σ0
      | nv_bd x v σ' =>
        let k_v v' :=
          let k_σ σ'' := k (nv_bd x v' σ'')
          in link σ' k_σ
        in link_value v k_v
      end.

  Definition link_vl σ0 :=
    fix link (v : vl trace) k :=
      match v with
      | vl_sh s => link_shdw link σ0 s k
      | vl_clos x t σ =>
        let k_σ σ' := k (vl_clos x t σ')
        in link_nv link σ0 σ k_σ
      end.

  Definition link_tr σ0 :=
    fix link (t : traceF trace) k :=
      match t with
      | Stuck => Stuck
      | Ret v => link_vl σ0 v k
      | Step σ t' =>
        let k_σ σ' := Step σ' (link t' k) in
        link_nv (link_vl σ0) σ0 σ k_σ
      end.
End link.

Fixpoint link_traceF n :=
  match n with
  | 0 => fun _ _ _ => Stuck
  | S n' =>
    link_tr (fun σ0 '(Tr _ t') k => Step σ0 (link_traceF n' σ0 (t' n') k))
  end.

Definition link_trace n σ0 '(Tr _ t') k := Step σ0 (link_traceF n σ0 (t' n) k).

Definition link_value n := link_vl (link_trace n).

Definition link_env {T} link :=
  fun σ0 => link_nv (trace := T) (link_vl link σ0) σ0
.

Definition link_envA n := link_env (link_trace n).

Definition link_shadow {T} link :=
  fun σ0 => link_shdw (trace := T) link (link_vl link σ0) σ0
.

Definition link_shadowA n := link_shadow (link_trace n).

Fixpoint denote (t : term) k {struct t} : nat → traceF trace :=
  match t with
  | Var x =>
    let r := vl_sh (Rd x) in
    fun _ => k r
  | Lam x e =>
    let E := Tr e (denote e Ret) in
    let r := vl_clos x E Init in
    fun _ => k r
  | App fn arg => fun n =>
    let k_fn f :=
      let k_arg a := ap (link_trace n) f a k in
      denote arg k_arg n in
    denote fn k_fn n
  end.

Definition wf_trace t :=
  match t with
  | Tr e t' => t' = denote e Ret
  end.

Definition bind k :=
  fix bind_ (t : traceF trace) :=
    match t with
    | Stuck => Stuck
    | Ret v => k v
    | Step σ t' => Step σ (bind_ t')
    end.

Lemma bind_ext k k' (EXT : ∀ v, k v = k' v) :
  ∀ t, bind k t = bind k' t.
Proof.
  refine (fix go t :=
    match t with
    | Stuck => eq_refl
    | Ret v => EXT v
    | Step σ t' => f_equal (Step σ) (go t')
    end).
Qed.

Lemma bind_bind k k' :
  ∀ t, bind k' (bind k t) = bind (fun v => bind k' (k v)) t.
Proof.
  refine (fix go t :=
    match t with
    | Stuck => eq_refl
    | Ret v => eq_refl
    | Step σ t' => f_equal (Step σ) (go t')
    end).
Qed.

Definition link_shadow_ext {T} link s :=
  ∀ (k : _ → traceF T) k' σ0 (EXT : ∀ v, k v = k' v),
    link_shadow link σ0 s k = link_shadow link σ0 s k'
.
Definition link_env_ext {T} link σ :=
  ∀ (k : _ → traceF T) k' σ0 (EXT : ∀ v, k v = k' v),
    link_env link σ0 σ k = link_env link σ0 σ k'
.
Definition link_vl_ext {T} link v :=
  ∀ (k : _ → traceF T) k' σ0 (EXT : ∀ v, k v = k' v),
    link_vl link σ0 v k = link_vl link σ0 v k'
.
Definition link_tr_ext {T} link (t : traceF T) :=
  ∀ k k' σ0 (EXT : ∀ v, k v = k' v),
    link_tr link σ0 t k = link_tr link σ0 t k'
.
Definition link_trace_ext {T} (link : _ → _ → _ → traceF T) (t : T) :=
  ∀ (k : vl T → traceF T) k' (σ0 : env T) (EXT : ∀ v, k v = k' v),
    link σ0 t k = link σ0 t k'
.

Lemma pre_link_ext {T} link (LINK_EXT : ∀ t, @link_trace_ext T link t) :
  (∀ s, link_shadow_ext link s) ∧
  (∀ σ, link_env_ext link σ) ∧
  (∀ v, link_vl_ext link v) ∧
  (∀ t, link_tr_ext link t).
Proof.
  cbv [link_trace_ext] in *.
  apply (pre_val_ind _ (fun _ => I));
  cbv [link_shadow_ext link_env_ext link_vl_ext link_tr_ext];
  simpl; eauto.
  - intros. apply IHs. intros v'. apply IHv. destruct v'; eauto.
  - intros. apply IHσ. intros. f_equal. auto.
Qed.

Lemma link_ext n :
  ∀ t, link_trace_ext (link_trace n) t.
Proof.
  induction n; cbv [link_trace_ext];
  simpl; intros;
    match goal with t : trace |- _ => destruct t end;
    auto.
  simpl. f_equal.
  apply (pre_link_ext _ IHn); auto.
Qed.

Definition link_shadow_bind link s :=
  ∀ k k' σ0,
    bind k' (link_shadow link σ0 s k) =
    link_shadow link σ0 s (fun v' => bind k' (k v'))
.
Definition link_env_bind link σ :=
  ∀ k k' σ0,
    bind k' (link_env link σ0 σ k) =
    link_env link σ0 σ (fun v' => bind k' (k v'))
.
Definition link_vl_bind link v :=
  ∀ k k' σ0,
    bind k' (link_vl link σ0 v k) = link_vl link σ0 v (fun v' => bind k' (k v'))
.
Definition link_tr_bind link t :=
  ∀ k k' σ0,
    bind k' (link_tr link σ0 t k) = link_tr link σ0 t (fun v => bind k' (k v))
.
Definition link_trace_bind link (t : trace) :=
  ∀ k k' (σ0 : env trace),
    bind k' (link σ0 t k) = link σ0 t (fun v : vl trace => bind k' (k v))
.

Lemma pre_link_bind link
  (LINK_EXT : ∀ t, link_trace_ext link t)
  (LINK_BIND : ∀ t, link_trace_bind link t) :
  (∀ s, link_shadow_bind link s) ∧
  (∀ σ, link_env_bind link σ) ∧
  (∀ v, link_vl_bind link v) ∧
  (∀ t, link_tr_bind link t).
Proof.
  pose proof (pre_link_ext _ LINK_EXT) as (EXTs & EXTσ & EXTv & EXTt).
  apply (pre_val_ind _ (fun _ => I));
  cbv [link_shadow_bind link_env_bind link_vl_bind link_tr_bind];
  simpl; intros; eauto.
  - rewrite IHs. apply EXTs. intros v'.
    rewrite IHv. apply EXTv. destruct v'; auto.
    intros. apply LINK_BIND.
  - rewrite IHv. apply EXTv. intros.
    rewrite IHσ. auto.
  - unfold link_env in *. rewrite IHσ. apply EXTσ. intros.
    simpl. f_equal. auto.
Qed.

Lemma link_bind n :
  ∀ t, link_trace_bind (link_trace n) t.
Proof.
  induction n; simpl; destruct t as [e t'];
  cbv [link_trace_bind]; simpl; auto.
  intros. f_equal.
  apply (pre_link_bind _ (link_ext n) IHn).
Qed.

Lemma link_bind_Ret n σ t k :
  link_traceF n σ t k = bind k (link_traceF n σ t Ret).
Proof.
  destruct n; simpl; auto.
  destruct (pre_link_bind _ (link_ext n) (link_bind n)) as (_ & _ & _ & ->).
  auto.
Qed.

Lemma denote_ext e :
  ∀ k k' (EXT : ∀ v, k v = k' v) n, denote e k n = denote e k' n.
Proof.
  induction e; simpl; intros; auto.
  apply IHe1; intros.
  apply IHe2; intros. unfold ap.
  destruct v; auto. pose proof (link_ext n t k k').
  destruct t. auto.
Qed.

Lemma denote_bind e :
  ∀ k k' n, bind k' (denote e k n) = denote e (fun v => bind k' (k v)) n.
Proof.
  induction e; simpl; intros; f_equal; auto.
  rewrite IHe1. apply denote_ext. intros.
  rewrite IHe2. apply denote_ext. intros. unfold ap.
  destruct v; auto. pose proof (link_bind n t k k').
  destruct t; auto.
Qed.

Lemma denote_bind_Ret e :
  ∀ k n, denote e k n = bind k (denote e Ret n).
Proof.
  intros. rewrite denote_bind. apply denote_ext. reflexivity.
Qed.

(* traditional *)
Inductive value :=
  | value_clos (x : var) (e : term) (σ : list (var * value))
.

Definition rd' x :=
  fix read (σ : list (var * value)) :=
  match σ with
  | [] => None
  | (x', v) :: σ' =>
    if x =? x' then Some v else read σ'
  end.

Definition ev ev :=
  fix go t (k : _ → option value) :=
  match t with
  | Var x => fun σ =>
    match rd' x σ with
    | None => None
    | Some r => k r
    end
  | Lam x e => fun σ => k (value_clos x e σ)
  | App fn arg => fun σ =>
    let k_fn f :=
      let k_arg a :=
        match f with
        | value_clos x e σ' => ev e k ((x, a) :: σ')
        end in
      go arg k_arg σ in
    go fn k_fn σ
  end.

Lemma ev_ext e :
  ∀ eval
    (EVAL_EXT : ∀ t k k' (EXT : ∀ v, k v = k' v) σ,
      eval t k σ = eval t k' σ)
    k k' (EXT : ∀ v, k v = k' v) σ,
    ev eval e k σ = ev eval e k' σ.
Proof.
  induction e; simpl; intros; auto.
  { destruct (rd' _ _); auto. }
  apply IHe1; auto. intros.
  apply IHe2; auto. destruct v; auto.
Qed.

Lemma ev_bind e :
  ∀ eval
    (EVAL_EXT : ∀ t k k' (EXT : ∀ v, k v = k' v) σ,
      eval t k σ = eval t k' σ)
    (EVAL_BIND : ∀ t k k' σ,
      match eval t k σ with
      | Some v' => k' v'
      | None => None
      end =
      eval t (fun v => match k v with Some v' => k' v' | None => None end) σ)
    k k' σ,
    match ev eval e k σ with
    | Some v => k' v
    | None => None
    end =
    ev eval e (fun v => match k v with Some v' => k' v' | None => None end) σ.
Proof.
  induction e; simpl; intros; auto.
  { destruct (rd' _ _); auto. }
  rewrite IHe1 by auto. apply ev_ext; auto. intros.
  rewrite IHe2 by auto. apply ev_ext; auto. intros.
  destruct v; auto.
Qed.

Fixpoint eval n :=
  match n with
  | 0 => fun _ _ _ => None
  | S n' => ev (eval n')
  end.

Lemma eval_ext n :
  ∀ e k k' (EXT : ∀ v, k v = k' v) σ,
    eval n e k σ = eval n e k' σ.
Proof.
  induction n; simpl; auto using ev_ext.
Qed.

Lemma eval_bind n :
  ∀ e k k' σ,
    match eval n e k σ with
    | Some v => k' v
    | None => None
    end =
    eval n e (fun v => match k v with Some v' => k' v' | None => None end) σ.
Proof.
  induction n; simpl; auto using eval_ext, ev_bind.
Qed.

Lemma eval_bind_Some n :
  ∀ e k σ,
    eval n e k σ =
    match eval n e Some σ with
    | Some v => k v
    | None => None
    end.
Proof.
  intros. rewrite eval_bind. reflexivity.
Qed.

Definition lift_nv f :=
  fix go (σ : list (var * value)) : env trace :=
    match σ with
    | [] => Init
    | (x, v) :: σ' => nv_bd x (f v) (go σ')
    end.

Fixpoint lift_value v :=
  match v with
  | value_clos x e σ =>
    vl_clos x (Tr e (denote e Ret)) (lift_nv lift_value σ)
  end.

Definition lift_env := lift_nv lift_value.

Fixpoint dest {T} (t : traceF T) :=
  match t with
  | Stuck => None
  | Ret v => Some v
  | Step _ t' => dest t'
  end.

Definition Ret_env σ :=
  Ret (vl_clos "" (Tr (Var "") (fun _ => Stuck)) σ)
.

Definition link_shadow_dest link (s : shadow trace) :=
  ∀ k σ0,
    dest (link_shadow link σ0 s k) =
    match dest (link_shadow link σ0 s Ret) with
    | Some v => dest (k v)
    | None => None
    end.
Definition link_env_dest link (σ : env trace) :=
  ∀ k σ0,
    dest (link_env link σ0 σ k) =
    match dest (link_env link σ0 σ Ret_env) with
    | Some (vl_clos _ _ σ') => dest (k σ')
    | _ => None
    end.
Definition link_vl_dest link (v : vl trace) :=
  ∀ k σ0,
    dest (link_vl link σ0 v k) =
    match dest (link_vl link σ0 v Ret) with
    | Some v' => dest (k v')
    | None => None
    end.
Definition link_tr_dest link (t : traceF trace) :=
  ∀ k σ0,
    dest (link_tr link σ0 t k) =
    match dest (link_tr link σ0 t Ret) with
    | Some v => dest (k v)
    | None => None
    end.
Definition link_trace_dest link (t : trace) :=
  ∀ (k : vl trace → traceF trace) (σ0 : env trace),
    dest (link σ0 t k) =
    match dest (link σ0 t Ret) with
    | Some v => dest (k v)
    | None => None
    end.

Ltac des_ap :=
  match goal with
  | |- context [ap _ ?v _ _] => destruct v
  end.

Lemma pre_link_dest link (LINK_DEST : ∀ t, link_trace_dest link t) :
  (∀ s, link_shadow_dest link s) ∧
  (∀ σ, link_env_dest link σ) ∧
  (∀ v, link_vl_dest link v) ∧
  (∀ t, link_tr_dest link t).
Proof.
  apply (pre_val_ind _ (fun _ => I));
  cbv [link_shadow_dest link_env_dest link_vl_dest link_tr_dest];
  simpl; intros; eauto.
  - rewrite IHs. symmetry. rewrite IHs.
    destruct (dest (link_shadow _ _ _ _)); auto.
    rewrite IHv. symmetry. rewrite IHv.
    destruct (dest (link_vl _ _ _ _)); auto.
    des_ap; simpl; auto.
    apply LINK_DEST.
  - rewrite IHv. symmetry. rewrite IHv.
    destruct (dest (link_vl _ _ _ _)); auto.
    rewrite IHσ. symmetry. rewrite IHσ.
    destruct (dest (link_env _ _ _ _)); auto.
    match goal with |- context [match ?x with _ => _ end] => destruct x end;
    auto.
  - unfold link_env in *. rewrite IHσ. symmetry. rewrite IHσ.
    destruct (dest (link_nv _ _ _ _)); auto.
    destruct v; auto.
  - unfold link_env in *. rewrite IHσ. symmetry. rewrite IHσ.
    destruct (dest (link_nv _ _ _ _)); auto.
    destruct v; auto.
    simpl. symmetry. auto.
Qed.

Lemma link_dest n :
  ∀ t, link_trace_dest (link_trace n) t.
Proof.
  induction n; simpl; destruct t as [e t'];
  cbv [link_trace_dest]; simpl; auto.
  apply (pre_link_dest _ IHn).
Qed.

Definition link_shadow_link link (s : shadow trace) :=
  ∀ Σ0 σ0 k K
    (CONT : ∀ v, dest (link_tr link Σ0 (k v) Ret) = dest (link_vl link Σ0 v K)),
    match dest (link_env link Σ0 σ0 Ret_env) with
    | Some (vl_clos _ _ σ) =>
      dest (link_tr link Σ0 (link_shadow link σ0 s k) Ret) =
      dest (link_shadow link σ s K)
    | _ => True
    end.
Definition link_env_link link (σ : env trace) :=
  ∀ Σ0 σ0 k K
    (CONT : ∀ σ', dest (link_tr link Σ0 (k σ') Ret) = dest (link_env link Σ0 σ' K)),
    match dest (link_env link Σ0 σ0 Ret_env) with
    | Some (vl_clos _ _ σ') =>
      dest (link_tr link Σ0 (link_env link σ0 σ k) Ret) =
      dest (link_env link σ' σ K)
    | _ => True
    end.
Definition link_vl_link link (v : vl trace) :=
  ∀ Σ0 σ0 k K
    (CONT : ∀ v, dest (link_tr link Σ0 (k v) Ret) = dest (link_vl link Σ0 v K)),
    match dest (link_env link Σ0 σ0 Ret_env) with
    | Some (vl_clos _ _ σ) =>
      dest (link_tr link Σ0 (link_vl link σ0 v k) Ret) =
      dest (link_vl link σ v K)
    | _ => True
    end.
Definition link_tr_link link (t : traceF trace) :=
  ∀ Σ0 σ0 k K
    (CONT : ∀ v, dest (link_tr link Σ0 (k v) Ret) = dest (link_vl link Σ0 v K)),
    match dest (link_env link Σ0 σ0 Ret_env) with
    | Some (vl_clos _ _ σ) =>
      dest (link_tr link Σ0 (link_tr link σ0 t k) Ret) =
      dest (link_tr link σ t K)
    | _ => True
    end.
Definition link_trace_link link (t : trace) :=
  ∀ Σ0 σ0 k K
    (CONT : ∀ v, dest (link_tr link Σ0 (k v) Ret) = dest (link_vl link Σ0 v K)),
    dest (link_tr link Σ0 (link σ0 t k) Ret) =
    match dest (link_env link Σ0 σ0 Ret_env) with
    | Some (vl_clos _ _ σ) => dest (link σ t K)
    | _ => None
    end.

Lemma link_rd link (LINK_DEST : ∀ t, link_trace_dest link t) Σ0 :
  ∀ σ0 k x,
    match dest (link_env link Σ0 σ0 Ret_env) with
    | Some (vl_clos _ _ σ) =>
      dest (link_vl link Σ0 (rd x σ0) k) = dest (k (rd x σ))
    | _ => True
    end.
Proof.
  refine (fix go σ0 :=
    match σ0 with
    | Init => fun k x => eq_refl
    | nv_bd x' V Σ' => fun k x => _
    end).
  specialize (go Σ').
  simpl.
  pose proof (pre_link_dest _ LINK_DEST) as (RRs & RRσ & RRv & RRt).
  rewrite RRv. destruct (dest (link_vl _ _ _ _)) eqn:EQ; auto.
  rewrite RRσ. destruct (dest (link_env _ _ _ _)) as [v'|]; auto.
  destruct v'; auto. simpl.
  destruct (_ =? _); auto.
  rewrite RRv. rewrite EQ. reflexivity.
Qed.

Lemma pre_link_link link
  (LINK_DEST : ∀ t, link_trace_dest link t)
  (LINK_LINK : ∀ t, link_trace_link link t) :
  (∀ s, link_shadow_link link s) ∧
  (∀ σ, link_env_link link σ) ∧
  (∀ v, link_vl_link link v) ∧
  (∀ t, link_tr_link link t).
Proof.
  pose proof (pre_link_dest _ LINK_DEST) as (RRs & RRσ & RRv & RRt).
  apply (pre_val_ind _ (fun _ => I));
  cbv [link_shadow_link link_env_link link_vl_link link_tr_link] in *;
  simpl; intros; eauto.
  - specialize (link_rd link LINK_DEST Σ0 σ0 Ret x).
    destruct (dest (link_env _ _ _ _)) as [v'|]; auto.
    destruct v'; auto. intros RR.
    specialize (CONT (rd x σ0)).
    rewrite RRv, RR in CONT. rewrite CONT; auto.
  - specialize (IHs Σ0 σ0). specialize (IHv Σ0 σ0).
    destruct (dest (link_env _ _ _ _)) as [v'|] eqn:EQσ; auto.
    destruct v'; auto.
    erewrite IHs; eauto.
    intros f. erewrite IHv.
    { instantiate (1 := fun a => link_vl link Σ0 f (fun f => ap link f a K)).
      rewrite (RRv v). rewrite (RRv f).
      destruct (dest (link_vl _ _ v _)) eqn:EQv; try rewrite RRv;
      destruct (dest (link_vl _ _ f _)) eqn:EQf; simpl; auto;
      rewrite (RRv v), EQv; auto. }
    intros a. simpl. rewrite RRv.
    unfold ap. destruct f as [f'|x' t' σ']; simpl.
    { rewrite CONT. simpl.
      unfold link_shadow_dest, link_shadow in RRs. rewrite RRs.
      destruct (dest (link_shdw _ _ _ f' _)) eqn:EQf'. rewrite RRv.
      all: destruct (dest (link_vl _ _ _ _)); auto; rewrite RRs, EQf'; auto. }
    { specialize (LINK_LINK t' Σ0 (nv_bd x' a σ')).
      simpl in *. rewrite RRv in LINK_LINK.
      erewrite LINK_LINK; eauto.
      destruct (dest (link_vl _ _ _ _)); auto.
      rewrite RRσ. symmetry.
      cbv [link_env_dest link_env] in *. rewrite RRσ.
      destruct (dest (link_nv _ _ σ' Ret_env)) as [v'|]; auto.
      destruct v'; auto. }
  -
Abort.

Lemma ev_monotonicity : ∀ e k k' σ v f f'
  (K_MONO : ∀ v w, k v = Some w → k' v = Some w)
  (EVAL_MONO : ∀ e k k' σ v,
    (∀ v w, k v = Some w → k' v = Some w) →
    f e k σ = Some v → f' e k' σ = Some v)
  (EVAL : ev f e k σ = Some v),
  ev f' e k' σ = Some v.
Proof.
  induction e; simpl; auto.
  { intros. destruct (rd' x σ); auto. }
  intros.
  eapply IHe1; eauto. simpl.
  intros u w EVAL'.
  eapply IHe2; eauto. simpl.
  intros v' w'. destruct u. eauto.
Qed.

Lemma eval_monotonicity : ∀ m n (GE : m ≤ n) e k k' σ v
  (K_MONO : ∀ v w, k v = Some w → k' v = Some w)
  (EVAL : eval m e k σ = Some v),
  eval n e k' σ = Some v.
Proof.
  induction m; simpl; [congruence|].
  intros [|n]. lia.
  intros.
  eapply ev_monotonicity with (f := eval m) (f' := eval n); eauto.
  intros. eapply IHm; eauto. lia.
Qed.

