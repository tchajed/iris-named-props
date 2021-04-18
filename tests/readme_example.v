From iris.proofmode Require Import tactics.
From iris_named_props Require Import named_props.

Section demo.
Context {PROP: bi} `{Haff: BiAffine PROP}.
Context (P Q: PROP).

Definition foo_rep :=
("HP" ∷ P ∗
 "HR" ∷ Q)%I.

Theorem foo_rep_read_P : foo_rep -∗ P.
Proof using Haff.
  iIntros "H".
  iNamed "H".
  (* at this point we have a context of

  "HP" : P
  "HR" : Q
  --------------------------------------∗
  P

  *)
  iExact "HP".
Qed.

End demo.
