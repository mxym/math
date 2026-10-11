# Exact identifiability and equifinality in a two-storage rainfall–runoff model

This note develops an exact, model-specific result for the positive two-storage
linear rainfall–runoff system

\[
\dot x_1=p-(a+b)x_1+cx_2,\qquad
\dot x_2=bx_1-cx_2,\qquad Q=ax_1,
\]
with \(a,b,c>0\). Here \(p\) is a known rainfall input, \(x_1,x_2\) are
hidden storage states, and \(Q\) is the observed discharge.

## Established results

Adding the storage equations gives the exact balance law
\[
(x_1+x_2)'=p-Q.
\]
Eliminating the hidden states gives, pointwise for every sufficiently smooth
trajectory,
\[
Q''+(a+b+c)Q'+ac\,Q = a p' + ac\,p.
\]
Thus the scalar output equation sees the rates through
\(S=a+b+c\) and \(P=ac\), unless additional state information or forcing
experiments are supplied.

The rates \((2,2,2)\) and \((1,1,4)\) have the same \((S,P)=(6,4)\). For
constant rainfall \(p=1\), the nonnegative stationary states
\[
(1/2,1/2)\quad\text{and}\quad(1,1/4)
\]
respectively produce the identical discharge curve \(Q(t)=1\) for all time.
This is an exact physical equifinality certificate: the parameters and hidden
storage partition differ, while perfect continuous discharge observations agree.

The Lean development also proves the exact coefficient fibre
\[
b=S-a-P/a,\qquad c=P/a,
\]
and its converse: every positive choice of \(a\) for which the reconstructed
\(b,c\) remain positive gives the prescribed \((S,P)\). Thus the obstruction
is an explicit one-parameter family, not only the displayed pair.

Under the controlled intervention \(p(t)=p_0>0\) and known zero initial
storage, the first three output derivatives satisfy
\[
Q'(0)=ap_0,\quad Q''(0)=-a(a+b)p_0,\quad
Q'''(0)=a((a+b)^2+bc)p_0.
\]
Consequently
\[
a=\frac{Q'(0)}{p_0},\quad B=-\frac{Q''(0)}{Q'(0)},\quad
b=B-a,\quad c=\frac{Q'''(0)/Q'(0)-B^2}{b}.
\]
The three positive rates are therefore exactly recoverable in this controlled
zero-storage experiment. This is a structural theorem, not a claim about
statistical accuracy under noisy measurements.

The formalization also proves a stronger intervention statement: if two
constant-rainfall experiments begin from the same unknown storage state, and
the higher rainfall exceeds the lower one, subtracting their hydrograph jets
cancels the common initial state. The same three recovery formulas applied to
the difference hydrograph identify all rates. This makes the cancellation
mechanism explicit rather than assuming an empty catchment.

## Verification

The exact rational regression checker is `checks/exact.py` and passes both
normal and optimized Python execution. The Lean package in
`formalizations/hydrology-identifiability/` formalizes the pointwise jet
elimination identity, the stationary equifinality certificate, the exact
parameter-recovery formulas, the finite-storage recession obstruction, and the
parallel-reservoir moment identities. It deliberately does not hide an ODE
existence assumption: trajectories are represented by explicit pointwise
derivative jets, so every hypothesis used by the algebraic proof is visible.

The current result is intentionally limited to these finite linear models. It
does not claim a general identifiability theorem for all conceptual hydrology
models. A next target beyond the finite-mode certificates is a rigorous
equivalence classification for threshold or power-law outflows with unknown
initial storage and finite-time integral observations.

The package now also contains a finite-storage recession obstruction. If
\(S>0\) and \(P>0\), no nonzero exact power-law curve
\(Q(t)=C(\tau+t)^{-\alpha}\) can satisfy the homogeneous output equation for
all times. Substitution gives the quadratic residual
\[
\alpha(\alpha+1)-S\alpha(\tau+t)+P(\tau+t)^2.
\]
The Lean proof evaluates this residual at the three exact times \(0,1,2\), so
the obstruction is a finite algebraic certificate. It separates this finite
two-storage linear model from exact power-law recession tails without claiming
that empirical tails are exact or ruling out distributed or nonlinear models.

For two active parallel exponential reservoirs, let

[
m_j=w_1ell_1^j+w_2ell_2^jquad (j=0,1,2,3).
]

`Hydrology/Parallel.lean` proves the order-two recurrence

[
m_{j+2}=(ell_1+ell_2)m_{j+1}-ell_1ell_2m_jquad(j=0,1)
]

and the exact Hankel identity

[
m_0m_2-m_1^2=w_1w_2(ell_1-ell_2)^2.
]

Its uniqueness theorem says that a nonzero Hankel determinant makes the first
four moments determine (s=ell_1+ell_2) and (p=ell_1ell_2) uniquely; the
two rates are then the roots of (z^2-sz+p), up to order. This is a finite
model-order diagnostic, not a general identifiability theorem for distributed
or nonlinear catchments.

The same certificate is now proved for three parallel modes. For
(n_j=sum_{i=1}^3 w_iell_i^j), (0leq jleq5), the first three elementary
symmetric coefficients

[
e_1=ell_1+ell_2+ell_3,quad
e_2=ell_1ell_2+ell_1ell_3+ell_2ell_3,quad
e_3=ell_1ell_2ell_3
]

give (n_{j+3}=e_1n_{j+2}-e_2n_{j+1}+e_3n_j) for (j=0,1,2). The exact
three-by-three Hankel determinant is

[
w_1w_2w_3(ell_1-ell_2)^2(ell_1-ell_3)^2(ell_2-ell_3)^2.
]

Thus three positive-weight, pairwise-distinct modes have a strict order-three
certificate. The Lean module `Hydrology/Parallel3.lean` proves these identities
and the associated cubic root equations; the checker includes an exact example
whose determinant is (216). This is a finite parallel-reservoir result and
does not assert a universal theorem for spatially distributed catchments.

The finite-mode statement itself is now uniform. If

[
h_j=sum_{i=1}^k w_ilambda_i^j
]

and (A(z)=sum_{r=0}^d a_rz^r) vanishes at every (lambda_i), then

[
sum_{r=0}^d a_r h_{j+r}=0qquad	ext{for every }jge0.
]

`Hydrology/Generic.lean` proves this theorem for arbitrary finite (k,d) in
Lean. Its proof explicitly interchanges the two finite sums, factors
(lambda_i^j), and applies the annihilating equation term by term. This is
the exact finite-dimensional backbone behind all of the explicit recurrences
above; rate uniqueness and positivity require the additional Hankel or
Vandermonde hypotheses stated separately.

## Context

Relevant prior work includes Sorooshian–Gupta on conceptual-model calibration
([DOI](https://doi.org/10.1029/WR021i004p00487)), Shin et al. on structural
identifiability in hydrology ([DOI](https://doi.org/10.1016/j.jhydrol.2014.11.040)),
and Kirchner on catchment response functions
([DOI](https://doi.org/10.1029/2009WR008777)); related two-parallel-reservoir
approximations of power-law recession are discussed by Tashie et al.
([DOI](https://doi.org/10.1061/(ASCE)HE.1943-5584.0001518)). This repository
does not make a priority claim.

## Reproduce

```sh
python3 -B checks/exact.py
python3 -B -O checks/exact.py
cd formalizations/hydrology-identifiability
lake build Hydrology
```
