From iris.proofmode Require Import proofmode.
From iris_named_props Require Import named_props.

Set Default Proof Using "All".
Section tests.
  Context {PROP: bi} {Haffine: BiAffine PROP}.
  Implicit Types (P Q R : PROP).

  Lemma demo_split_manual P Q R :
    "HP" ∷ P ∗
    "HQ" ∷ Q ∗
    "HP_to_R" ∷ (P -∗ R) -∗
    R ∗ Q.
  Proof.
    iNamed 1.
    iSplitL "HP HP_to_R".
    - iApply ("HP_to_R" with "HP").
    - iExact "HQ".
  Qed.

  Lemma demo_split_delay P Q R :
    "HP" ∷ P ∗
    "HQ" ∷ Q ∗
    "HP_to_R" ∷ (P -∗ R) -∗
    R ∗ Q.
  Proof.
    iNamed 1.
    iSplitDelay.
    - iSpecialize ("HP_to_R" with "HP").
      iFrame.
      Show.
      rewrite left_id. (* TODO: this is an annoyance *)
      iNamedAccu.
    - iNamed 1.
      Show.
      iExact "HQ".
  Qed.
End tests.
