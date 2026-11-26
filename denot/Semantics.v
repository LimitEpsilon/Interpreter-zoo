(** * Linking and the denotational semantics

    This file defines the denotation of a term and the linking of an
    environment into a trace. [denote n e] is the trace of [e] at the fuel
    [n]. It is a structural recursion on [e] that takes no environment. Each
    free variable becomes a shadow, and linking resolves the shadows.

    ** Main definitions

    - [link_vl], [link_tr], [link_trace]: link an environment into a value,
      into the spine of a trace, and into a trace.
    - [linkb], [linkv]: link into a body and into a value, with fuel.
    - [call]: enter a body with an environment, behind a guard.
    - [denote], [den]: the denotation of a term.
    - [run]: the result of a term in an environment.

    ** Notes

    - Guards. When linking uses only a part of a resolved value, it keeps the
      whole value in a guard. The cases are a read of a module, a field of a
      constructor value, a branch of a match and the environment of a body. A
      later linking must then resolve each value that a call-by-value run
      computes.
    - Weak values. A leaf of a trace is a value, and a weak value is not
      always a value. Thus [link_wvl] takes the rest of the linking as a
      function of the linked weak value.
    - Recursive values. To link into a recursive value, [link_wvl] opens it
      with a fresh anchor, links, and closes it. It kills the anchor in the
      spine.
    - Fuel. The opened recursive value is not a structural part, so
      [link_wvl] takes its linking as the parameter [lk]. [linkv] gives [lk]
      by the same fuel as [linkb]. *)
From Stdlib Require Import Utf8 String Bool Arith List.
From Denot Require Import Syntax Anchor Domain.

Section link.
  Context (cl : nv → body → trace) (lk : nv → vl → trace).

  (** Apply the function [f] to [a]. A shadow gives a call shadow. A closure
      enters its body. *)
  Definition ap (f a : vl) : trace :=
    match f with
    | vl_sh s => Ret (vl_sh (Call s a))
    | vl_clos x b σ => cl (nv_bd x a σ) b
    | _ => Bot
    end.

  (** Read the variable [x] of the module [m]. A module that is a shadow
      gives a read shadow. *)
  Definition rd (x : var) (m : vl) : trace :=
    match m with
    | vl_exp σ =>
      match read x σ with Some v => Guard m (Ret v) | None => Bot end
    | vl_sh s => Ret (vl_sh (Read s x))
    | _ => Bot
    end.

  (** Take field [i] of the constructor value [m], when its name is [c]. A
      shadow gives a field shadow. *)
  Definition ds (c : cstr) (i : nat) (m : vl) : trace :=
    match m with
    | vl_sh s => Ret (vl_sh (Dstr s c i))
    | vl_cstr c' vs =>
      if String.eqb c c'
      then match vnth i vs with Some v => Guard m (Ret v) | None => Bot end
      else Bot
    | _ => Bot
    end.

  Context (σ0 : nv).

  (** Link [σ0] into a shadow, an environment, a weak value, a value or a
      list of values. Each leaf of [link_nv] is a module. Each leaf of
      [link_vls c] is a constructor value of [c]. [link_wvl w k] continues
      with [k] at the linked weak value. *)
  Fixpoint link_shdw (s : shdw) : trace :=
    match s with
    | Init => Ret (vl_exp σ0)
    | Read s' x => bind (rd x) (link_shdw s')
    | Call s' v => bind (fun f => bind (fun a => ap f a) (link_vl v)) (link_shdw s')
    | Dstr s' c i => bind (ds c i) (link_shdw s')
    end
  with link_nv (σ : nv) : trace :=
    match σ with
    | nv_mt => Ret (vl_exp nv_mt)
    | nv_sh s => bind (on_mod (fun σ' => Ret (vl_exp σ'))) (link_shdw s)
    | nv_bd x w σ' =>
      link_wvl w (fun w' =>
        bind (on_env (fun σ'' => Ret (vl_exp (nv_bd x w' σ'')))) (link_nv σ'))
    end
  with link_wvl (w : wvl) (k : wvl → trace) : trace :=
    match w with
    | wvl_v v => bind (fun v' => k (wvl_v v')) (link_vl v)
    | wvl_mu v =>
      (* Open with a fresh anchor, link, and close. Kill the anchor in the spine. *)
      let ℓ := fresh σ0 v in
      bind (fun v' => k (wvl_mu (close_vl 0 ℓ v')))
        (killg ℓ (lk σ0 (open_vl 0 ℓ v)))
    | wvl_an _ => k w
    end
  with link_vl (v : vl) : trace :=
    match v with
    | vl_exp σ => link_nv σ
    | vl_sh s => link_shdw s
    | vl_clos x b σ => bind (on_env (fun σ' => Ret (vl_clos x b σ'))) (link_nv σ)
    | vl_cstr c vs => link_vls c vs
    end
  with link_vls (c : cstr) (vs : vls) : trace :=
    match vs with
    | vnil => Ret (vl_cstr c vnil)
    | vcons v vs' =>
      bind (fun v' =>
        bind (on_cstr (fun c' vs'' => Ret (vl_cstr c' (vcons v' vs'')))) (link_vls c vs'))
        (link_vl v)
    end.

  (** Link [σ0] into the spine of a trace. The leaves stay. [link_sel c n]
      links into the branch for the constructor [c] with [n] fields. *)
  Fixpoint link_tr (t : trace) : trace :=
    match t with
    | Bot => Bot
    | Ret v => Ret v
    | Guard u t' => bind (fun u' => Guard u' (link_tr t')) (link_vl u)
    | Match s bs =>
      bind (fun m =>
        match m with
        | vl_sh s' => Match s' (link_brs bs)
        | vl_cstr c vs => Guard m (link_sel c (vlen vs) bs)
        | _ => Bot
        end) (link_shdw s)
    end
  with link_brs (bs : brs) : brs :=
    match bs with
    | bnil => bnil
    | bcons c n t bs' => bcons c n (link_tr t) (link_brs bs')
    end
  with link_sel (c : cstr) (n : nat) (bs : brs) : trace :=
    match bs with
    | bnil => Bot
    | bcons c' n' t bs' =>
      if String.eqb c c' && Nat.eqb n n' then link_tr t else link_sel c n bs'
    end.

  (** Link [σ0] into a trace, that is into the spine and then into the leaf. *)
  Definition link_trace (t : trace) : trace := bind link_vl (link_tr t).
End link.

(** ** Fuel *)

(** [linkb n σ b] links [σ] into the body [b] at the fuel [n]. [linkv n σ v]
    links [σ] into the value [v]. The fuel bounds the depth of calls and of
    recursive values. At the fuel 0 both give [Bot]. *)
Fixpoint linkb (n : nat) : nv → body → trace :=
  match n with
  | 0 => fun _ _ => Bot
  | S n' => fun σ b =>
    link_trace (fun σ' b' => Guard (vl_exp σ') (linkb n' σ' b')) (linkv n') σ (b n')
  end
with linkv (n : nat) : nv → vl → trace :=
  match n with
  | 0 => fun _ _ => Bot
  | S n' => fun σ v =>
    link_vl (fun σ' b' => Guard (vl_exp σ') (linkb n' σ' b')) (linkv n') σ v
  end.

(** Enter the body [b] with the environment [σ]. The guard keeps [σ]. *)
Definition call (n : nat) (σ : nv) (b : body) : trace :=
  Guard (vl_exp σ) (linkb n σ b).

(** At the fuel 0, [linkb] gives [Bot]. *)
Lemma linkb_0 σ b : linkb 0 σ b = Bot.
Proof. reflexivity. Qed.

(** One unit of fuel for [linkb]. *)
Lemma linkb_S n σ b : linkb (S n) σ b = link_trace (call n) (linkv n) σ (b n).
Proof. reflexivity. Qed.

(** At the fuel 0, [linkv] gives [Bot]. *)
Lemma linkv_0 σ v : linkv 0 σ v = Bot.
Proof. reflexivity. Qed.

(** One unit of fuel for [linkv]. *)
Lemma linkv_S n σ v : linkv (S n) σ v = link_vl (call n) (linkv n) σ v.
Proof. reflexivity. Qed.

(** The definition of [call]. *)
Lemma call_eq n σ b : call n σ b = Guard (vl_exp σ) (linkb n σ b).
Proof. reflexivity. Qed.

(** ** The denotation *)

(** The trace of a term at the fuel [n], relative to the unknown environment.
    [denote_list] is for the arguments of a constructor. [denote_sel] selects
    the branch of a constructor value. [denote_brs] gives the branches for a
    shadow. *)
Fixpoint denote (n : nat) (e : tm) {struct e} : trace :=
  match e with
  | Var x => Ret (vl_sh (Read Init x))
  | Fn x e' => Ret (vl_clos x (fun m => denote m e') (nv_sh Init))
  | App e1 e2 =>
    bind (fun f => bind (fun a => ap (call n) f a) (denote n e2)) (denote n e1)
  | Link e1 e2 =>
    bind (on_mod (fun σ => call n σ (fun m => denote m e2))) (denote n e1)
  | Mt => Ret (vl_exp nv_mt)
  | Bind x e1 e2 =>
    (* [e1] runs with [x] bound to the anchor 1. Then the anchor is closed. *)
    bind (fun v =>
      bind (on_mod (fun σ2 => Ret (vl_exp (nv_bd x (wvl_mu (close_vl 0 1 v)) σ2))))
        (call n (nv_bd x (wvl_mu (close_vl 0 1 v)) (nv_sh Init))
           (fun m => denote m e2)))
      (killg 1 (call n (nv_bd x (wvl_an (F 1)) (nv_sh Init)) (fun m => denote m e1)))
  | Cstr c es => denote_list n c es
  | Case e' bs =>
    bind (fun m =>
      match m with
      | vl_cstr c vs => denote_sel n c vs bs
      | vl_sh s => Match s (denote_brs n s bs)
      | _ => Bot
      end) (denote n e')
  end
with denote_list (n : nat) (c : cstr) (es : tms) {struct es} : trace :=
  match es with
  | tnil => Ret (vl_cstr c vnil)
  | tcons e es' =>
    bind (fun v =>
      bind (on_cstr (fun c' vs => Ret (vl_cstr c' (vcons v vs)))) (denote_list n c es'))
      (denote n e)
  end
with denote_sel (n : nat) (c : cstr) (vs : vls) (bs : branches) {struct bs} : trace :=
  match bs with
  | brnil => Bot
  | brcons c' xs e bs' =>
    if String.eqb c c' && Nat.eqb (vlen vs) (length xs)
    then call n (bindV xs vs (nv_sh Init)) (fun m => denote m e)
    else denote_sel n c vs bs'
  end
with denote_brs (n : nat) (s : shdw) (bs : branches) {struct bs} : brs :=
  match bs with
  | brnil => bnil
  | brcons c xs e bs' =>
    bcons c (length xs)
      (call n (bindD xs s c 0 (nv_sh Init)) (fun m => denote m e))
      (denote_brs n s bs')
  end.

(** The denotation of a term as a body. *)
Definition den (e : tm) : body := fun n => denote n e.

(** The result of the term [e] in the environment [σ] at the fuel [n]. *)
Definition run (n : nat) (σ : nv) (e : tm) : option vl := dest (linkb n σ (den e)).

Global Opaque linkb linkv call.
