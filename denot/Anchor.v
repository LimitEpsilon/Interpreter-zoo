(** * Anchors

    This file defines anchors and the functions that change one anchor. An
    anchor is the placeholder for the value of a binding while the right side
    of the binding runs. [Domain.v] and [Reference.v] use these functions to
    open, close and rename the anchors of a value.

    ** Main definitions

    - [anc]: an anchor, that is an index [B i] or a name [F ℓ].
    - [fopen], [fclose], [fren]: what open, close and rename do to one anchor
      under [k] recursive values.
    - [kap]: the renaming that makes one name the dead anchor. *)
From Stdlib Require Import Utf8 Arith.

(** The name of a free anchor. The name 0 is the dead anchor. *)
Definition loc := nat.

(** An anchor. A recursive value around an index binds the index. A name is
    free. *)
Inductive anc :=
  | B (i : nat)     (* bound by recursive value number [i] around it *)
  | F (ℓ : loc).    (* free *)

(** Open one anchor. Under [k] recursive values, the index [k] becomes the
    name [ℓ]. *)
Definition fopen (ℓ : loc) (k : nat) (a : anc) : anc :=
  match a with B j => if Nat.eqb j k then F ℓ else a | F _ => a end.

(** Close one anchor. Under [k] recursive values, the name [ℓ] becomes the
    index [k]. *)
Definition fclose (ℓ : loc) (k : nat) (a : anc) : anc :=
  match a with F ℓ' => if Nat.eqb ℓ' ℓ then B k else a | B _ => a end.

(** Rename one anchor. Each name [ℓ] becomes the name [ξ ℓ]. *)
Definition fren (ξ : loc → loc) (_ : nat) (a : anc) : anc :=
  match a with F ℓ => F (ξ ℓ) | B _ => a end.

(** The renaming that takes the name [ℓ] to the dead anchor and keeps each
    other name. No function gives 0 as a fresh name, so nothing closes the
    dead anchor. *)
Definition kap (ℓ : loc) (x : loc) : loc := if Nat.eqb x ℓ then 0 else x.
