# Analytic proof supplement and exact formalization boundary

This supplement expands the analytic proof obligations in the mass-envelope
paper; it does not alter a frozen preprint or claim that the lower envelope has
already been formalized.

## 1. Actual density, tail, and truncated moments

Let
\[
 \phi(a)=(2\pi)^{-1/2}e^{-a^2/2},\qquad
 q(a)=\int_a^\infty\phi(x)\,dx.
\]
The Lean definitions are `standardDensity` and `gaussianTail`.
`gaussianTail_eq_probability` proves that this integral is the real value of
`gaussianReal 0 1 (Ioi a)`, rather than merely a function with postulated Gaussian
properties. Positivity of the density gives `0<q(a)<1`. The fundamental theorem
of calculus gives `q'=-phi`, and the improper-integral endpoint theorems give the
limits zero at positive infinity and one at negative infinity.

The inherited first-moment identity is
\[
 \int_a^\infty x\phi(x)\,dx=\phi(a).
\]
For the new second-moment identity, differentiate `x phi(x)` and use integrability
of this function and its derivative to prove its zero limit at positive infinity.
The fundamental theorem on the half-line then gives
\[
 \int_a^\infty x^2\phi(x)\,dx=q(a)+a\phi(a).
\]
No numerical quadrature, asymptotic approximation, or external variance formula
is an input to this argument.

## 2. Squared hazard: the principal analytic lemma

Set `H(a)=phi(a)/q(a)`. The integral of `(x-a)phi(x)` over the upper half-line is
nonnegative, so `H(a)≥a`. For every real `c`, expanding the actual nonnegative
integral of `(x-c)^2 phi(x)` gives
\[
 0\le q(a)+a\phi(a)-2c\phi(a)+c^2q(a).
\]
At `c=H(a)`, division by the proved positive number `q(a)` yields
\[
 H(a)(H(a)-a)\le1.
\]
Direct differentiation establishes
\[
 H'=H(H-a)\ge0,\qquad
 (H^2+2\log q)'=2H\{H(H-a)-1\}\le0.
\]
The mean-value theorem therefore gives, for any real `a≤b`,
\[
 0\le H(b)^2-H(a)^2\le2\log\frac{q(a)}{q(b)}.
\]
Strict monotonicity, continuity and the two endpoint limits of the actual tail
prove existence and uniqueness of `a_p` for every `0<p<1`. The Lean definition
`upperQuantile` chooses this proved unique threshold; it makes no inverse or
existence assumption. Substitution proves the complete probability-parameter
statement of Lemma 2. Strict positivity of the conditional variance is not needed
for this non-strict estimate and is not claimed.

## 3. Arbitrary measurable-set first moments

For an actual fractional label `0≤f≤1`, a unit vector `u` and real threshold `a`,
pointwise threshold comparison gives
\[
 f(x)(\langle u,x\rangle-a)
 \le1_{\{\langle u,x\rangle>a\}}(x)(\langle u,x\rangle-a).
\]
All integrability statements are supplied. The proved standard-Gaussian law of
the unit projection and the exact scalar half-line flux give
\[
 \langle u,b\rangle-am\le\phi(a)-a q(a),\quad
 b=\int xf(x)\,d\gamma_d(x),\quad m=\int f\,d\gamma_d.
\]
Choose `a=a_m`. If `b=0`, the desired profile bound is immediate; otherwise use
`u=b/||b||` to conclude `||b||≤phi(a_m)`.

`GaussianSets.lean` constructs the actual pair of indicator labels of `A` and
its complement. It proves that their first label has mass `gamma_d(A)` and
Bochner moment `integral_A x d gamma_d`. The bound thus applies to the original
measurable-set objects with no unproved relaxation bridge. Squaring and summing
proves the upper inequality for any finite measurable family of prescribed
interior masses, and hence for every such measurable partition.

## 4. Terminal-cell entropy bound without a conditional-Jensen interface

Fix a real threshold `a` and put `t=H(a)`. The elementary exponential tangent
inequality gives, on the half-line,
\[
 e^{tx}\ge e^{t^2}(1+tx-t^2).
\]
Outside the half-line the indicator of the right-hand side is zero and remains
at most `e^{tx}`. Integrating with respect to the actual `gaussianReal 0 1`, and
using `t q(a)=phi(a)`, proves
\[
 q(a)e^{t^2}\le\int_{\mathbb R}e^{tx}\,d\gamma_1(x)=e^{t^2/2}.
\]
The Gaussian exponential moment is a proved Mathlib theorem in the pinned
version. Taking logarithms yields `H(a)^2≤2 log(1/q(a))`, and substituting `a_p`
then multiplying by `p^2` proves equation (16b).

## 5. What this does not prove

These arguments close the analytic hazard/profile/terminal-cell obligations.
They do not construct the arbitrary-mass staircase partition, prove its complete
moment matrix or the ordered residual-entropy inequality, or establish the full
supremum/lower-envelope assembly. Those remain explicit mathematical
formalization tasks, not assumptions of a purported completed main theorem.
