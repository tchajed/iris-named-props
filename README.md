# Named propositions for Iris

[![CI](https://github.com/tchajed/iris-named-props/workflows/CI/badge.svg)](https://github.com/tchajed/iris-named-props/actions/workflows/build.yml?query=workflow%3ACI)

Named propositions are an extension to the Iris Proof Mode (IPM) that allow you
to embed names for conjuncts within a definition and then use those names to
introduce or destruct the definition. See the header comment in
[named_props.v](src/named_props.v) for a detailed explanation with the entire
API.

This library is compatible with the latest version of Iris and Coq 8.13+.

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

Putting the names in the definition avoids repeating the same intro patterns
over and over in a proof. Not repeating yourself makes things easier to change
when the definition changes - for example, reordering and adding new conjuncts
will have minimal impact on proof scripts.

The "names" in named propositions are not actually just names, but Iris intro
patterns; for example `"#H"`, `"%H"` (using Iris's recent support for Coq names
in intro patterns), and `"?"` are all potentially useful.

One application of this feature implemented in the library is a tactic
`iNamedAccu` which is like `iAccu` but remembers the names used. If you haven't
used `iAccu`, it solves a goal which is an evar with the conjunction of the
entire context (this kind of situation arises when you have a proof rule that
allows saving the entire context and then restoring it elsewhere). `iNamedAccu`
is just like `iAccu`, but it adds names to the conjuncts so that the result can
easily be restored with the same names later.

For an example of using `iNamedAccu`, see
[tests/split_delay.v](tests/split_delay.v). We implemented a simple tactic
`iSplitDelay` that puts all hypotheses on the left side but changes the goal
from `Q1 ∗ Q2` to `(Q1 ∗ ?rest) ∗ (?rest -∗ ?Q2)`. The result is that you can
prove `Q1` on the left, use `iNamedAccu` to fill `?rest` with the remaining
hypotheses, and then use `iNamed 1` in the second goal to get back all the
remaining hypotheses. The upshot is that you don't need to decide upfront how to
split the context.
