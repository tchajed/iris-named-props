From iris.proofmode Require Import tactics monpred.
From iris_named_props Require Import named_props.

Set Default Proof Using "All".
Section tests.
  Context {PROP: bi} {Haffine: BiAffine PROP}.
  Implicit Types (P Q R : PROP).
  Implicit Types (Ψ: nat -> PROP).
  Implicit Types (φ: Prop).

  Example test_name_named_1 P Q :
    ⊢ named "H1" P -∗
      named "H2" Q -∗
      P ∗ Q.
  Proof.
    iIntros "? ?".
    iNamed.
    iSplitL "H1"; [ iExact "H1" | iExact "H2" ].
  Qed.

  Example test_name_named_2 P Q :
    ⊢ named "H1" P -∗
      named "H2" Q -∗
      P ∗ Q%I.
  Proof.
    iIntros "H₁ H₂".
    iNameHyp "H₁".
    iNameHyp "H₂".
    iSplitL "H1"; [ iExact "H1" | iExact "H2" ].
  Qed.

  Example test_pure_pattern_freshen φ φ' P :
    named "%H" ⌜φ⌝ -∗
    named "%H" ⌜φ'⌝ -∗
    P -∗
    ⌜φ ∧ φ'⌝ ∗ P.
  Proof.
    iIntros "H1 H2 $".
    iNameHyp "H1".
    iNameHyp "H2".
    iPureIntro; exact (conj H H0).
  Qed.

  Example test_destruct_named P Q :
    ⊢ named "H1" P ∗
      named "H2" Q ∗
      named "H3" P ∗
      named "H4" Q
      -∗
      P ∗ Q ∗ P ∗ Q.
  Proof.
    iIntros "H".
    iNamedDestruct "H".
    iFrame.
  Qed.

  Example test_destruct_pat (foo: Prop) P Q :
    ⊢ named "[%Hfoo HP]" (⌜foo⌝ ∗ P) ∗
      named "HQ" Q ∗
      named "HP2" P
      -∗
      ⌜foo⌝ ∗ P ∗ Q ∗ P.
  Proof.
    iIntros "H".
    iNamedDestruct "H".
    iFrame "HP HQ HP2".
    iPureIntro; exact Hfoo.
  Qed.

  Example test_frame_named P Q :
    ⊢ P -∗ Q -∗ named "HP" P ∗ named "HQ" Q.
  Proof.
    iIntros "HP HQ".
    iFrame "HQ HP".
  Qed.

  Example test_frame_named_sep P Q :
    ⊢ P -∗ Q -∗ named "HPQ" (P ∗ Q).
  Proof.
    iIntros "HP HQ".
    iFrame.
  Qed.

  Example test_exist_destruct Ψ Q :
    ⊢ (∃ x, named "HP" (Ψ x) ∗ named "HQ" Q) -∗ (∃ x, Ψ x) ∗ Q.
  Proof.
    iIntros "H".
    iNamed "H".
    iSplitL "HP"; [ iExists x | ]; iFrame.
  Qed.

  Definition rep_invariant Ψ Q : PROP :=
    (∃ x, named "HP" (Ψ x) ∗ named "HQ" Q)%I.

  Example test_exist_destruct_under_definition Ψ Q :
    ⊢ rep_invariant Ψ Q -∗ (∃ x, Ψ x) ∗ Q.
  Proof.
    iIntros "H".
    iNamed "H".
    iSplitL "HP"; [ iExists x | ]; iFrame.
  Qed.

  Example test_exist_destruct_no_naming Ψ Q :
    ⊢ (∃ x, Ψ x) -∗ (∃ x, Ψ x).
  Proof.
    iIntros "H".
    iNamed "H".
    iExists x; iFrame "H".
  Qed.

  Example test_multiple_exist_destruct Ψ Q :
    ⊢ (∃ x y z, Ψ (x + y + z)) -∗ (∃ x, Ψ x).
  Proof.
    iIntros "H".
    iNamed "H".
    iExists (x+y+z); iFrame "H".
  Qed.

  Example test_iNamed_destruct_pat φ P Q :
    ⊢ named "[%Hfoo HP]" (⌜φ⌝ ∗ P) ∗
      named "HQ" Q ∗
      named "HP2" P
      -∗
      ⌜φ⌝ ∗ P ∗ Q ∗ P.
  Proof.
    iIntros "H".
    iNamed "H".
    iFrame "HP HQ HP2".
    iPureIntro; exact Hfoo.
  Qed.

  Example test_named_into_pure φ Q :
    named "N" ⌜φ⌝ ∗ Q -∗ Q.
  Proof.
    iIntros "[%HP HQ]".
    iFrame.
  Qed.

  Example test_named_persistent P :
    named "#H" (□P) -∗ □P.
  Proof.
    iIntros "HP".
    iNamed "HP".
    iModIntro.
    iExact "H".
  Qed.

  Example test_named_persistent_same_name P :
    named "#H" (□P) -∗ □P.
  Proof.
    iIntros "H".
    iNamed "H".
    iModIntro.
    iExact "H".
  Qed.

  Example test_named_persistent_conjuncts P Q :
    named "#H" (□P) ∗ named "#HQ" (□ Q) -∗ □P ∗ Q.
  Proof.
    iIntros "H".
    iDestruct "H" as "[Htmp1 H]".
    iNamed "H".
    auto.
  Qed.

  Example test_named_persistent_context P Q :
    named "#H" (□P) ∗ named "#HQ" (□ Q) -∗ □P ∗ Q.
  Proof.
    iIntros "#HQ".
    iNamed "HQ".
    auto.
  Qed.

  Example test_named_already_persistent `{!Persistent P} Q :
    named "#H" P ∗ named "#HQ" (□ Q) -∗ □P ∗ Q.
  Proof.
    iIntros "H".
    iNamed "H".
    auto.
  Qed.

  Example test_named_last_not_named P Q :
    named "HP" P ∗ Q -∗ P ∗ Q.
  Proof.
    iIntros "HQ".
    iNamed "HQ".
    iSplitR "HQ"; iAssumption.
  Qed.

  Example test_named_from_pure φ Q :
    φ ->
    Q -∗ Q ∗ named "N" ⌜φ⌝.
  Proof.
    iIntros (HP) "HQ".
    iFrame.
    iPureIntro.
    done.
  Qed.

  Example test_named_not_found P :
    named "HP" P -∗ P.
  Proof.
    iIntros "HP".
    Fail iNamed "foo". (* hypothesis "foo" not found *)
    iNamed "HP".
    iExact "HP".
  Qed.

  Example test_exists Ψ :
    named "HP2" (∃ my_name, Ψ my_name) -∗
    named "HP" (∃ x, Ψ x).
  Proof.
    iIntros "?"; iNamed.
    iDeexHyp "HP2".
    iExists my_name; iFrame.
  Qed.

  Example test_exists_freshen x Ψ :
    named "HP" (Ψ x) -∗ named "HP2" (∃ x, Ψ x) -∗
    named "HP" (∃ x, Ψ x).
  Proof.
    iIntros "? ?"; iNamed.
    iDeexHyp "HP2".
    iExists x0; iFrame.
  Qed.

  Definition simple_rep P := "HP" ∷ P.

  (* TODO: this is a bug *)
  Example test_destruct_singleton_under_definition P :
    simple_rep P -∗ P.
  Proof.
    iIntros "H".
    iNamed "H".
    Fail iExact "HP".
  Abort.

  Example test_nested_destruct Ψ :
    ⊢ ("%wf" ∷ ⌜True⌝ ∗
    "*" ∷ ∃ y, "psi" ∷ Ψ y) -∗
    ∃ x, Ψ x.
  Proof.
    iNamed 1.
    iExists y; iExact "psi".
  Qed.

  Example test_nested_destruct_conjuncts Ψ :
    ("%wf" ∷ ⌜True⌝ ∗
    "*" ∷ ∃ y, "psi" ∷ Ψ y ∗ "psi2" ∷ Ψ (2+y)) -∗
    ∃ x, Ψ x.
  Proof.
    iNamed 1.
    iExists (2+y); iExact "psi2".
  Qed.

  Example test_nested_destruct_middle P Ψ :
    ("HP1" ∷ P ∗
      "*" ∷ (∃ y, "psi" ∷ Ψ y ∗ "psi2" ∷ Ψ (2+y)) ∗
      "HP2" ∷ P) -∗
    ∃ x, Ψ x ∗ P.
  Proof.
    iNamed 1.
    iExists (2+y); iFrame "psi2 HP2".
  Qed.

  Example test_frame_named_spatial P1 P2 :
    "H1" ∷ P1 ∗ "H2" ∷ P2 -∗
    "H1" ∷ P1 ∗ "H2" ∷ P2.
  Proof.
    iIntros "I". iNamed "I".
    iFrameNamed.
  Qed.

  Example test_frame_named_persistent P1 P2 :
    "#H1" ∷ □ P1 ∗ "H2" ∷ P2 -∗
    "#H1" ∷ □ P1 ∗ "H2" ∷ P2.
  Proof.
    iIntros "I".
    iNamed "I".
    iFrameNamed.
  Qed.

  Example test_frame_named_pure P1 P2 :
    "%Hwf" ∷ ⌜False⌝ ∗ "#H1" ∷ □ P1 ∗ "H2" ∷ P2 -∗
    "%Hwf" ∷ ⌜False⌝ ∗ "#H1" ∷ P1 ∗ "H2" ∷ P2.
  Proof.
    iIntros "I". iNamed "I".
    iFrameNamed.
  Qed.

  Example test_inamedaccu_serialize P1 P2 :
    P1 ∗
    P1 ∗ P2 ∗
    P2 ∗
    P1 ∗ P2 -∗
    P1 ∗ P1 ∗ P1 ∗ P2 ∗ P2 ∗ P2.
  Proof.
    iIntros "(H1&?&?&H2&?&?)".
    iApply bi.wand_elim_r.
    iSplitL.
    - iNamedAccu.
    - iNamed 1.
      (* should recover the same context (modulo renaming of anonymous
      hypotheses) *)
      iFrame.
  Qed.

  Check "test_monpred_named".
  Example test_monpred_named {I : biIndex} P1 (P2 : monPred I PROP) :
    "H1" ∷ ⎡P1⎤ ∗ "H2" ∷ P2 -∗ ⎡P1⎤ ∗ P2.
  Proof.
    iStartProof PROP.
    iIntros (i).
    Show.
    iNamed 1.
    iFrame "H1 H2".
  Qed.

  Check "test_suffix".
  Example test_suffix P φ :
    "H1" ∷ P ∗
    "H2" ∷ □ P ∗
    "H3" ∷ ⌜ φ ⌝ -∗
    P ∗ □ P ∗ ⌜ φ ⌝.
  Proof.
    iIntros "H".
    iNamedSuffix "H" "foo".
    Show.
    iFrame "∗#%".
  Qed.

End tests.
