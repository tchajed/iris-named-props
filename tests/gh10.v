From iris.proofmode Require Import tactics monpred.
From iris_named_props Require Import named_props.

Section bi.

Context {PROP: bi} {Haffine: BiAffine PROP}.

Definition foo : PROP. Admitted.
Global Instance foo_persis : Persistent foo. Proof. Admitted.

Lemma test : "#Hfoo" ∷ foo -∗ "#Hfoo" ∷ foo -∗ True.
Proof.
  iIntros "H0 H1".
  iNamed "H0".
  Fail iNamed "H1".
Abort.

End bi.
