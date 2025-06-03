From iris.proofmode Require Import tactics.
From iris_named_props Require Import custom_syntax.

Set Default Proof Using "All".
Section proof.
  Context {PROP: bi} {Haffine: BiAffine PROP}.
  Implicit Types (P Q R : PROP).
  Implicit Types (Ψ: nat -> PROP).
  Implicit Types (φ: Prop).

  Example test_name_named_1 P Q :
    ⊢ "H1" ∷ P -∗
      "H2" ∷ Q -∗
      P ∗ Q.
  Proof.
    iIntros "@ @".
    iSplitL "H1"; [ iExact "H1" | iExact "H2" ].
  Qed.

  Example test_pure_pattern_freshen φ φ' P :
    "%H" ∷ ⌜φ⌝ -∗
    "%H" ∷ ⌜φ'⌝ -∗
    P -∗
    ⌜φ ∧ φ'⌝ ∗ P.
  Proof.
    iIntros "@ @ $".
    iPureIntro; exact (conj H H0).
  Qed.

  Example test_destruct_named P Q :
    ⊢ "H1" ∷ P ∗
      "H2" ∷ P ∗
      "H3" ∷ Q ∗
      "H4" ∷ Q
      -∗
      P ∗ Q ∗ P ∗ Q.
  Proof.
    iIntros "@".
    iFrame.
  Qed.

  Example test_destruct_pat (foo: Prop) P Q :
    ⊢ "[%Hfoo HP]" ∷ (⌜foo⌝ ∗ P) ∗
      "HQ" ∷ Q ∗
      "HP2" ∷ P
      -∗
      ⌜foo⌝ ∗ P ∗ Q ∗ P.
  Proof.
    iIntros "@".
    iFrame "HP HQ HP2".
    iPureIntro; exact Hfoo.
  Qed.
End proof.
