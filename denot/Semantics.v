(** * Linking and the denotational semantics

    [denote n e] is the n-th finite approximation of the denotation of [e].
    It is computed by structural recursion on [e], knowing nothing about the
    environment: free variables become shadows.  Linking an environment into
    a trace resolves the shadows.

    Guard discipline: whenever part of a resolved value is discarded
    (projecting from a module, taking a field, selecting a branch, entering
    a body), the whole value is kept in a [Guard], so that a later link still
    has to resolve everything a call-by-value run would have computed. *)
From Stdlib Require Import Utf8 String Bool Arith List.
From Denot Require Import Syntax Domain.

Section link.
  (** [cl σ b]: run the body [b] under [σ].  Supplied later, by fuel. *)
  Context (cl : nv → body → trace).

  Definition ap (f a : vl) : trace :=
    match f with
    | vl_sh s => Ret (vl_sh (Call s a))
    | vl_clos x b σ => cl (nv_bd x a σ) b
    | _ => Bot
    end.

  Definition rd (x : var) (m : vl) : trace :=
    match m with
    | vl_exp σ =>
      match read x σ with Some v => Guard m (Ret v) | None => Bot end
    | vl_sh s => Ret (vl_sh (Read s x))
    | _ => Bot
    end.

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

  Fixpoint link_shdw (s : shdw) : trace :=
    match s with
    | Init => Ret (vl_exp σ0)
    | Read s' x => bind (rd x) (link_shdw s')
    | Call s' v => bind (fun f => bind (fun a => ap f a) (link_vl v)) (link_shdw s')
    | Dstr s' c i => bind (ds c i) (link_shdw s')
    end
  (* leaves of [link_nv] are always modules *)
  with link_nv (σ : nv) : trace :=
    match σ with
    | nv_mt => Ret (vl_exp nv_mt)
    | nv_sh s => bind (on_mod (fun σ' => Ret (vl_exp σ'))) (link_shdw s)
    | nv_bd x v σ' =>
      bind (fun v' =>
        bind (on_env (fun σ'' => Ret (vl_exp (nv_bd x v' σ'')))) (link_nv σ'))
        (link_vl v)
    end
  with link_vl (v : vl) : trace :=
    match v with
    | vl_exp σ => link_nv σ
    | vl_sh s => link_shdw s
    | vl_clos x b σ => bind (on_env (fun σ' => Ret (vl_clos x b σ'))) (link_nv σ)
    | vl_cstr c vs => link_vls c vs
    end
  (* leaves of [link_vls c] are always [vl_cstr c _] *)
  with link_vls (c : cstr) (vs : vls) : trace :=
    match vs with
    | vnil => Ret (vl_cstr c vnil)
    | vcons v vs' =>
      bind (fun v' =>
        bind (on_cstr (fun c' vs'' => Ret (vl_cstr c' (vcons v' vs'')))) (link_vls c vs'))
        (link_vl v)
    end.

  (** Link the spine of a trace; leaves are left as they are. *)
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

  Definition link_trace (t : trace) : trace := bind link_vl (link_tr t).
End link.

(** Link into a body, with fuel for nested calls. *)
Fixpoint linkb (n : nat) : nv → body → trace :=
  match n with
  | 0 => fun _ _ => Bot
  | S n' => fun σ b =>
    link_trace (fun σ' b' => Guard (vl_exp σ') (linkb n' σ' b')) σ (b n')
  end.

Definition call (n : nat) (σ : nv) (b : body) : trace :=
  Guard (vl_exp σ) (linkb n σ b).

Lemma linkb_0 σ b : linkb 0 σ b = Bot.
Proof. reflexivity. Qed.

Lemma linkb_S n σ b : linkb (S n) σ b = link_trace (call n) σ (b n).
Proof. reflexivity. Qed.

Lemma call_eq n σ b : call n σ b = Guard (vl_exp σ) (linkb n σ b).
Proof. reflexivity. Qed.

(** The denotation, relative to the unknown environment [Init]. *)
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
    bind (fun v =>
      bind (on_mod (fun σ2 => Ret (vl_exp (nv_bd x v σ2))))
        (call n (nv_bd x v (nv_sh Init)) (fun m => denote m e2)))
      (denote n e1)
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

Definition den (e : tm) : body := fun n => denote n e.

(** Running a program in an environment: link the environment in. *)
Definition run (n : nat) (σ : nv) (e : tm) : option vl := dest (linkb n σ (den e)).

(* From here on [linkb] and [call] are only unfolded through the three
   equations above. *)
Global Opaque linkb call.
