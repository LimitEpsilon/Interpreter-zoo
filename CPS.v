From Coq Require Import Numbers.DecimalString ZArith String.

Local Open Scope string_scope.

Definition string_of_int n :=
  NilEmpty.string_of_int (Pos.to_int n).

Definition int_of_string s :=
  match NilEmpty.int_of_string s with
  | None => None
  | Some n => Pos.of_int n
  end.

Inductive tm :=
  | Var (x : string)
  | Num (n : Z)
  | Add (l r : tm)
  | Pair (f s : tm)
  | Fst (p : tm)
  | Snd (p : tm)
  | Fn (x : string) (e : tm)
  | Fnr (f x : string) (e : tm)
  | Ifp (c p n : tm)
  | App (f a : tm)
  | Raise (r : tm)
  | Handle (r : tm) (x : string) (h : tm)
.

Fixpoint trans (t : tm) (k : (tm -> tm) * tm) :=
  match t with
  | Var x => (fst k) (Var x)
  | Num n => (fst k) (Num n)
  | Add m n =>
    let kM m :=
      let kN n := (fst k) (Add m n) in
      trans n (kN, snd k)
    in trans m (kM, snd k)
  | Pair f s =>
    let kF f :=
      let kS s := (fst k) (Pair f s) in
      trans s (kS, snd k)
    in trans f (kF, snd k)
  | Fst p =>
    let kP p := (fst k) (Fst p) in
    trans p (kP, snd k)
  | Snd p =>
    let kP p := (fst k) (Snd p) in
    trans p (kP, snd k)
  | Fn x m =>
    let kh := "$kh" in
    (fst k) (Fn x (Fn kh (trans' m (Fst (Var kh), Snd (Var kh)))))
  | Fnr f x m =>
    let kh := "$kh" in
    (fst k) (Fnr f x (Fn kh (trans' m (Fst (Var kh), Snd (Var kh)))))
  | Ifp c p n =>
    let kC c := Ifp c (trans p k) (trans n k)
    in trans c (kC, snd k)
  | App m n =>
    let kM m :=
      let kN n := App (App m n) (Pair (Fn "$k" ((fst k) (Var "$k"))) (snd k)) in
      trans n (kN, snd k)
    in trans m (kM, snd k)
  | Raise r => trans' r (snd k, snd k)
  | Handle r x h => trans r (fst k, Fn x (trans h k))
  end

with trans' (t : tm) (k : tm * tm) :=
  match t with
  | Var x => App (fst k) (Var x)
  | Num n => App (fst k) (Num n)
  | Add m n =>
    let kM m :=
      let kN n := App (fst k) (Add m n) in
      trans n (kN, snd k)
    in trans m (kM, snd k)
  | Pair f s =>
    let kF f :=
      let kS s := App (fst k) (Pair f s) in
      trans s (kS, snd k)
    in trans f (kF, snd k)
  | Fst p =>
    let kP p := App (fst k) (Fst p) in
    trans p (kP, snd k)
  | Snd p =>
    let kP p := App (fst k) (Snd p) in
    trans p (kP, snd k)
  | Fn x m =>
    let kh := "$kh" in
    App (fst k) (Fn x (Fn kh (trans' m (Fst (Var kh), Snd (Var kh)))))
  | Fnr f x m =>
    let kh := "$kh" in
    App (fst k) (Fnr f x (Fn kh (trans' m (Fst (Var kh), Snd (Var kh)))))
  | Ifp c p n =>
    let kC c := Ifp c (trans' p k) (trans' n k)
    in trans c (kC, snd k)
  | App m n =>
    let kM m :=
      let kN n := App (App m n) (Pair (fst k) (snd k)) in
      trans n (kN, snd k)
    in trans m (kM, snd k)
  | Raise r => trans' r (snd k, snd k)
  | Handle r x h => trans' r (fst k, Fn x (trans' h k))
  end.

Definition CPS (t : tm) := Fn "$kh" (trans' t (Fst (Var "$kh"), Snd (Var "$kh"))).

Local Coercion Var : string >-> tm.
Local Coercion Num : Z >-> tm.
Local Notation "'⟪' M '+' N '⟫'" := (Add M N) (at level 60, right associativity, only printing).
Local Notation "'⟪' M ',' N '⟫'" := (Pair M N) (at level 60, right associativity, only printing).
Local Notation "'⟪' M '•' '1' '⟫'" := (Fst M) (at level 60, right associativity, only printing).
Local Notation "'⟪' M '•' '2' '⟫'" := (Snd M) (at level 60, right associativity, only printing).
Local Notation "'⟪' 'λ' x e '⟫'" := (Fn x e) (at level 60, right associativity, only printing).
Local Notation "'⟪' 'μ' f x e '⟫'" := (Fnr f x e) (at level 60, right associativity, only printing).
Local Notation "'⟪' 'ifp' C 'then' P 'else' N '⟫'" := (Ifp C P N) (at level 60, right associativity, only printing).
Local Notation "'⟪' '@' M N '⟫'" := (App M N) (at level 60, right associativity, only printing).
Local Notation "'⟪' 'raise' R '⟫'" := (Raise R) (at level 60, right associativity, only printing).
Local Notation "'⟪' 'handle' R 'with' x '->' H '⟫'" := (Handle R x H) (at level 60, right associativity, only printing).

Definition test :=
  (App
    (Fnr "f" "x"
      (Ifp
        (Var "x")
        (App (Var "f") (Add (Var "x") (Num (-1))))
        (Num 0)))
    (Num 8))%Z
.

Definition test1 :=
  (App
    (Fnr "f" "x"
      (Ifp
        (Var "x")
        (Add (Var "x") (App (Var "f") (Add (Var "x") (Num (-1)))))
        (Num 0)))
    (Num 8))%Z
.

Definition test2 :=
  (App
    (Fn "x"
      (App
        (Fn "y"
          (Handle
            (Ifp
              (Var "y")
              (App
                (Fn "x"
                  (Raise (Num 7)))
                (Num 65))
              (Num 1))
            "a"
            (Add (Var "x") (Var "a"))))
        (Num 75)))
    (Num 85))%Z
.

Definition test3 :=
  (Handle
    (App
      (Fn "f"
        (App (Var "f") (Num 3)))
      (Fn "x"
        (Ifp
          (Var "x")
          (Raise (Num 10))
          (Var "x"))))
    "a"
    (Add (Var "a") (Var "a")))%Z
.

Compute CPS test.
Compute CPS test1.
Compute CPS test2.
Compute CPS test3.

Inductive val :=
  | Int (n : Z)
  | Clos (x : string) (e : tm) (σ : string -> option val)
  | Closr (f x : string) (e : tm) (σ : string -> option val)
  | Tuple (f s : val)
.

Inductive result :=
  | Error (msg : string)
  | Exn (v : val)
  | Val (v : val)
.

Inductive cont :=
  | Halt (r : result)
  | Continue (e : tm) (σ : string -> option val) (k : (val -> cont) * (val -> cont))
.

Fixpoint step (e : tm) (σ : string -> option val) (k : (val -> cont) * (val -> cont)) : cont :=
  match e with
  | Var x => match σ x with
    | None => Halt (Error (x ++ " is not bound."))
    | Some v => (fst k) v
    end
  | Num n => (fst k) (Int n)
  | Add l r =>
    let kl vl := match vl with
    | Int n1 =>
      let kr vr := match vr with
      | Int n2 => (fst k) (Int (n1 + n2))
      | _ => Halt (Error "Add tried on non-integer value.")
      end in step r σ (kr, snd k)
    | _ => Halt (Error "Add tried on non-integer value.")
    end in step l σ (kl, snd k)
  | Pair f s =>
    let kF f :=
      let kS s := (fst k) (Tuple f s) in
      step s σ (kS, snd k)
    in step f σ (kF, snd k)
  | Fst p =>
    let kp vp := match vp with
    | Tuple f s => (fst k) f
    | _ => Halt (Error "Fst tried on non-pair value.")
    end in step p σ (kp, snd k)
  | Snd p =>
    let kp vp := match vp with
    | Tuple f s => (fst k) s
    | _ => Halt (Error "Fst tried on non-pair value.")
    end in step p σ (kp, snd k)
  | Fn x e => (fst k) (Clos x e σ)
  | Fnr f x e => (fst k) (Closr f x e σ)
  | Ifp c p n =>
    let kp vp := match vp with
    | Int c =>
      if 0 <? c then step p σ k else step n σ k
    | _ => Halt (Error "Condition not integer.")
    end%Z in step c σ (kp, snd k)
  | App e1 e2 =>
    let k1 v1 := match v1 with
    | Clos x e σ1 =>
      let k2 v2 :=
        let σ' x' := if x =? x' then Some v2 else σ1 x'
        in Continue e σ' k
      in step e2 σ (k2, snd k)
    | Closr f x e σ1 =>
      let k2 v2 :=
        let σ' x' :=
          if x =? x' then Some v2
          else if f =? x' then Some v1
          else σ1 x'
        in Continue e σ' k
      in step e2 σ (k2, snd k)
    | _ => Halt (Error "Tried to apply a non-function.")
    end in step e1 σ (k1, snd k)
  | Raise r => step r σ (snd k, snd k)
  | Handle r x h =>
    let kh vh :=
      let σ' x' := if x =? x' then Some vh else σ x'
      in step h σ' k
    in step r σ (fst k, kh)
  end.

Fixpoint eval_cont e σ k (n : nat) :=
  match step e σ k with
  | Halt v => Halt v
  | Continue e' σ' k' =>
    match n with
    | O => Continue e' σ' k'
    | S n' => eval_cont e' σ' k' n'
    end
  end.

Definition eval e n := eval_cont e (fun _ => None) (fun v => Halt (Val v), fun v => Halt (Exn v)) n.
Definition eval_cps e n := eval (App (CPS e) (Pair (Fn "$x" (Var "$x")) (Fn "$x" (Raise (Var "$x"))))) n.

Compute eval test 9.
Compute eval test1 9.
Compute eval test2 9.
Compute eval test3 9.
Compute eval (Raise (Num 10))%Z 9.
Compute eval_cps test 20.
Compute eval_cps test1 28.
Compute eval_cps test2 9.
Compute eval_cps test3 9.
Compute eval_cps (Raise (Num 10))%Z 9.

