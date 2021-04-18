# Named propsitions for Iris

[![CI](https://github.com/tchajed/iris-named-props/workflows/CI/badge.svg)](https://github.com/tchajed/iris-named-props/actions?query=workflow%3ACI)

Named propositions are an extension to the Iris Proof Mode (IPM) that allow you
to embed names for conjuncts within a definition and then use those names to
introduce or destruct the definition.

```coq
From iris.proofmode Require Import tactics.
From iris_named_props Require Import named_props.

Definition foo_rep :=
 ("HP" ∷ P ∗
  "HR" ∷ R)%I.

Theorem foo_rep_read_P :
  foo_rep -∗ P.
Proof.
 iIntros "H".
 iNamed "H".
 (* at this point we have a context of

 "HP" : P
 "HR" : R
 --------------------------------------∗
 P

 *)
 iExact "HP".
Qed.
```

Putting the names in the definition avoid repeating the same intro pattern and
is easier to change when the definition changes (for example, reordering and
adding new conjuncts will have minimal impact on proof scripts).
