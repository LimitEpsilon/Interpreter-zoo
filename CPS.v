From Coq Require Import ZArith String.

Local Open Scope string_scope.

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

Fixpoint trans (t : tm) (κ : (tm -> tm) * tm) :=
  match t with
  | Var x => (fst κ) (Var x)
  | Num n => (fst κ) (Num n)
  | Add M N =>
    let κM m :=
      let κN n := (fst κ) (Add m n) in
      trans N (κN, snd κ)
    in trans M (κM, snd κ)
  | Pair f s =>
    let κF f :=
      let κS s := (fst κ) (Pair f s) in
      trans s (κS, snd κ)
    in trans f (κF, snd κ)
  | Fst P =>
    let κP p := (fst κ) (Fst p) in
    trans P (κP, snd κ)
  | Snd P =>
    let κP p := (fst κ) (Snd p) in
    trans P (κP, snd κ)
  | Fn x M => (fst κ) (Fn x (Fn "$kh" (trans' M (Fst (Var "$kh"), Snd (Var "$kh")))))
  | Fnr f x M => (fst κ) (Fnr f x (Fn "$kh" (trans' M (Fst (Var "$kh"), Snd (Var "$kh")))))
  | Ifp C P N =>
    let κC c := Ifp c (trans P κ) (trans N κ)
    in trans C (κC, snd κ)
  | App M N =>
    let κM m :=
      let κN n := App (App m n) (Pair (Fn "$k" ((fst κ) (Var "$k"))) (snd κ))in
      trans N (κN, snd κ)
    in trans M (κM, snd κ)
  | Raise R => trans' R (snd κ, snd κ)
  | Handle R x H => trans R (fst κ, Fn x (trans H κ))
  end

with trans' (t : tm) (k : tm * tm) :=
  match t with
  | Var x => App (fst k) (Var x)
  | Num n => App (fst k) (Num n)
  | Add M N =>
    let κM m :=
      let κN n := App (fst k) (Add m n) in
      trans N (κN, snd k)
    in trans M (κM, snd k)
  | Pair f s =>
    let κF f :=
      let κS s := App (fst k) (Pair f s) in
      trans s (κS, snd k)
    in trans f (κF, snd k)
  | Fst P =>
    let κP p := App (fst k) (Fst p) in
    trans P (κP, snd k)
  | Snd P =>
    let κP p := App (fst k) (Snd p) in
    trans P (κP, snd k)
  | Fn x M => App (fst k) (Fn x (Fn "$kh" (trans' M (Fst (Var "$kh"), Snd (Var "$kh")))))
  | Fnr f x M => App (fst k) (Fnr f x (Fn "$kh" (trans' M (Fst (Var "$kh"), Snd (Var "$kh")))))
  | Ifp C P N =>
    let κC c := Ifp c (trans' P k) (trans' N k)
    in trans C (κC, snd k)
  | App M N =>
    let κM m :=
      let κN n := App (App m n) (Pair (fst k) (snd k)) in
      trans N (κN, snd k)
    in trans M (κM, snd k)
  | Raise R => trans' R (snd k, snd k)
  | Handle R x H => trans' R (fst k, Fn x (trans' H k))
  end.

Definition CPS (t : tm) := Fn "$kh" (trans' t (Fst (Var "$kh"), Snd (Var "$kh"))).

Local Coercion Var : string >-> tm.

Local Coercion Num : Z >-> tm.

Local Notation "'⟪' M '+' N '⟫'" := (Add M N) (at level 60, right associativity).

Local Notation "'⟪' M ',' N '⟫'" := (Pair M N) (at level 60, right associativity).

Local Notation "'⟪' M '•' '1' '⟫'" := (Fst M) (at level 60, right associativity).

Local Notation "'⟪' M '•' '2' '⟫'" := (Snd M) (at level 60, right associativity).

Local Notation "'⟪' 'λ' x e '⟫'" := (Fn x e) (at level 60, right associativity).

Local Notation "'⟪' 'μ' f x e '⟫'" := (Fnr f x e) (at level 60, right associativity).

Local Notation "'⟪' 'ifp' C 'then' P 'else' N '⟫'" := (Ifp C P N) (at level 60, right associativity).

Local Notation "'⟪' '@' M N '⟫'" := (App M N) (at level 60, right associativity).

Local Notation "'⟪' 'raise' R '⟫'" := (Raise R) (at level 60, right associativity).

Local Notation "'⟪' 'handle' R 'with' x '->' H '⟫'" := (Handle R x H) (at level 60, right associativity).

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
    (Add (Var "a") (Var "a")))
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
  | Val (v : val)
.

Inductive dom :=
  | Halt (r : result)
  | Continue (e : tm) (σ : string -> option val) (k : (val -> dom) * (val -> dom))
.

Fixpoint step (e : tm) (σ : string -> option val) (k : (val -> dom) * (val -> dom)) : dom :=
  match e with
  | Var x => match σ x with None => Halt (Error (x ++ " is not bound")) | Some v => (fst k) v end
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

Definition eval e n := eval_cont e (fun _ => None) (fun v => Halt (Val v), fun v => Halt (Error "Uncaught exception")) n.
Definition eval_cps e n := eval (App (CPS e) (Pair (Fn "$x" (Var "$x")) (Fn "_" (Raise (Num 2024%Z))))) n.

Compute eval test 9.
Compute eval test1 9.
Compute eval test2 9.
Compute eval test3 9.
Compute eval_cps test 20.
Compute eval_cps test1 28.
Compute eval_cps test2 9.
Compute eval_cps test3 9.

