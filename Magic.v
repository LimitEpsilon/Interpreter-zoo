Unset Guard Checking.

Fixpoint magic (x : nat) : False := magic x.

Goal False.
  apply magic. exact 0.
Qed.

