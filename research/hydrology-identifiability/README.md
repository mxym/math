# Exact identifiability frontier for a two-storage rainfall--runoff model

This is a new hydrology research direction. It studies a minimal two-storage
model exactly, rather than fitting a numerical predictor:

\[
 \dot x_1=p-(a+b)x_1+cx_2,\qquad
 \dot x_2=bx_1-cx_2,\qquad Q=ax_1,
\]
where (a,b,c>0), (p) is known rainfall input, (x_1,x_2) are storage
states, and (Q) is observed runoff.

## Results established in this research note

Writing (S=a+b+c) and (P=ac), eliminating the hidden states gives the
exact output equation

\[
 Q''+S Q'+P Q=a p'+Pp.
\]

For constant rainfall this becomes (Q''+SQ'+PQ=Pp). Therefore an unknown
initial storage experiment can see (S) and (P), but cannot in general
separate (a,b,c).

This is witnessed by the two physically admissible equilibrium models
\[
 (a,b,c)=(2,2,2),\qquad (a,b,c)=(1,1,4),\qquad p=Q=1.
\]
They have the same (S=6), (P=4), and produce the identical runoff curve
(Q(t)=1) with nonnegative constant storage states, although their parameters
and hidden storage are different.

Conversely, for a constant (p>0) and known zero initial storage, the first
three output derivatives recover all parameters:
\[
 a=Q'(0)/p,\quad B=a+b=-Q''(0)/Q'(0),\quad
 bc=Q'''(0)/Q'(0)-B^2,\quad b=B-a,\quad c=bc/b.
\]
The total storage satisfies the exact water-balance identity
\[
 (x_1+x_2)'=p-Q.
\]

The point is a model-design theorem: initial-state assumptions and input
experiments are part of identifiability. A single hydrograph cannot be used to
claim three separately identified physical rates without such assumptions.

## Status and next target

The identities and rational counterexample are checked by
`checks/exact.py`. The ODE/identifiability statements are currently written
mathematical proofs and are not yet Lean-certified. The high-value continuation
is to classify the equivalence group for threshold/ power-law outflows with
unknown initial state and finite-time integral observations, and to formalize
the linear theorem before making any stronger claim.

Relevant prior context includes the structural-identifiability literature for
conceptual rainfall--runoff models (e.g. DOI
`10.1029/WR021i004p00487`, DOI `10.1016/j.jhydrol.2014.11.040`) and recent
work on equifinality and hydrograph separation (DOI
`10.1016/j.jhydrol.2022.127816`). This note does not claim historical priority.

## Reproduction

```sh
python3 -B checks/exact.py
python3 -B -O checks/exact.py
```

The checker uses exact rational algebra only. It corroborates the displayed
identities and counterexample; it is not a substitute for the analytic proof.
