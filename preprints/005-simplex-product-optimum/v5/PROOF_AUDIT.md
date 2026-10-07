# Proof audit — entry 005 version 5

**Date:** 7 October 2026

**Claim audited:** among all balanced homogeneous simplex recursions
\[
K_{j+1}=(K_j^t)^{*t},
\qquad
t\ge2,
\]
with simplex seed dimension \(p\ge1\), the binary \(T_5\) recursion uniquely maximizes the asymptotic root rate.

## 1. Inherited inputs

Version 5 uses only the following mathematical inputs from earlier entry-005 versions:

- the exact product identity \(R(A\times B)=R(A)R(B)\);
- the product identity for \(a\);
- the join identities for \(R,a,Q\);
- the simplex values
  \[
  a(T_p)=1/(p+1),\qquad R(T_p)=(p+1)g(p);
  \]
- the already established \(T_5\) orbit tail mechanism, which is also rederived in the version-5 paper.

The global spectral nonattainment theorem from version 3 is contextual and is not needed for Theorem 1.1.

## 2. Recurrence audit

For
\[
P=(K_j)^t,
\]
the product formulas give
\[
\dim P=td_j,\qquad a(P)=a_j,\qquad R(P)=R_j^t.
\]
For the join of \(t\) copies of \(P\),
\[
Q(P^{*t})=Q(P)^t,\qquad
a(P^{*t})=a_j/t.
\]
Substitution gives
\[
R_{j+1}
=
t a_j^{t-1}
\frac{g(d_{j+1})}{g(td_j)^t}
R_j^{t^2}.
\]

**Audit check:** the exponent on \(R_j\) is \(t^2\), not \(t\), and the prefactor is \(t a_j^{t-1}\), not \(t/a_j\).

The dimension shift
\[
c=1/(t+1)
\]
is verified by
\[
t^2d+t-1+c=t^2(d+c).
\]

## 3. Robbins envelope audit

The proof uses
\[
\frac{e^n}{\sqrt{2\pi n}}e^{-1/(12n)}
<
g(n)
<
\frac{e^n}{\sqrt{2\pi n}}.
\]
For
\[
q=td,\qquad n=tq+t-1,
\]
the quotient contributes
\[
e^{t-1}(2\pi)^{(t-1)/2}
\frac{q^{t/2}}{\sqrt n}
e^{1/(12d)}.
\]
Since \(n>t^2d\),
\[
q^{t/2}/\sqrt n
<
t^{t/2-1}d^{(t-1)/2}.
\]
After multiplication by \(t a^{t-1}\), the power of \(t\) is \(t^{t/2}\).

**Audit check:** the Robbins correction is \(e^{1/(12d)}\), because
\[
t/(12q)=1/(12d).
\]
The final uniform replacement \(d\ge p\) is therefore valid.

The exact dimension identity gives
\[
a_j\sqrt{d_j}
<
\frac{\sqrt{p+c}}{p+1},
\]
so all \(j\)-dependence cancels in the balanced case.

## 4. Infinite-tail audit

The simpler logarithmic majorant is
\[
\log\Lambda_{t,p}
<
1+\frac{B_t(p)}{p+c}.
\]

For \(p\ge20\), the proof needs \(B_t''<0\). The universal comparison reduces to
\[
6p^3-19p^2-11p-1>0.
\]
It is positive at \(p=4\), and its derivative is positive and increasing from there.

For each integer \(2\le t\le19\), the checker certifies
\[
H_t(20)>0,
\qquad
B_t(20)/(20+c)<1/25.
\]
This is sufficient because
\[
H_t'=-(p+c)B_t''>0.
\]

For \(t\ge20\), the arity term is bounded using monotonicity of
\[
\log t/(t-1).
\]
The resulting one-variable majorant \(F(p)\) has \(F''<0\) for \(p\ge4\). The checker verifies
\[
H_F(9)>0
\]
and the required \(F(p)/p<6/125\) inequalities for \(1\le p\le9\).

**Audit check:** the monotonicity anchor is \(p=9\), not \(p=8\). The continuous derivative of \(F(p)/p\) is still positive at \(p=8\), even though the integer value at \(8\) exceeds that at \(9\).

## 5. Finite-core audit

The finite core contains exactly
\[
18\cdot19=342
\]
pairs.

The first envelope excludes 335. The remaining seven are exactly
\[
(2,p),\qquad1\le p\le7.
\]
The checker then performs three exact recurrence levels for
\[
p=1,2,3,4,6,7
\]
and applies the same infinite tail envelope. All six are below the logarithmic threshold \(131/125\).

No pruning, floating-point ordering, or heuristic search determines this list. Every comparison uses rational logarithm enclosures.

## 6. Winning lower bound

For \((t,p)=(2,5)\), the proof uses
\[
D_j>3.
\]
The central-binomial estimate is elementary and reproduced in the paper.

At level six,
\[
d_6=21845,\qquad3d_6+1=65536.
\]
The checker recomputes the exact rational \(R_6\) and verifies
\[
(14267/5000)^{65536}<3R_6^3.
\]
This proves
\[
\Lambda_{2,5}>14267/5000.
\]

Separately, the rational logarithm checker proves
\[
\log(14267/5000)>131/125.
\]
Thus every competitor is strictly below the winner.

## 7. Logarithm verifier

The checker scales every rational \(x>0\) to
\[
x=2^k y,\qquad1\le y<2,
\]
and applies the positive atanh series with the explicit remainder
\[
0<R_N\le
\frac{2z^{2N+1}}{(2N+1)(1-z^2)}.
\]
All endpoints are Fractions. The only transcendental constant needed beyond logarithms of rationals is \(\pi\), enclosed by
\[
333/106<\pi<355/113.
\]

There are no calls to floating point, numerical optimizers, random search, SAT/SMT solvers, or external libraries. Correctness conditions use explicit exceptions and therefore remain active under python -O.

## 8. Nonclaims

Version 5 does not establish optimality over independent product/join arities \(m,k\), periodic homogeneous schemes, arbitrary recursive trees, or all convex bodies.

A preliminary non-rigorous scan of small independent arities found no better orbit, but that observation is discovery-only and is deliberately excluded from the theorem.
