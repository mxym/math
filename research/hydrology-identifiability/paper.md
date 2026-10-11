# Exact identifiability and equifinality in a two-storage rainfall–runoff model

## Abstract

We analyze a positive two-storage linear rainfall–runoff model at exact symbolic
precision. Eliminating the hidden storage variables yields a scalar output
identity whose coefficients depend on the three physical rates through only two
combinations. We give an explicit physically admissible equifinality certificate:
two distinct rate triples and distinct stationary storage partitions generate
exactly the same discharge for all time. We then prove that a controlled
constant-rainfall experiment with known zero initial storage recovers all three
rates from the first three output derivatives. The result separates structural
non-identifiability from numerical estimation and gives a concrete intervention
design principle.

## 1. Model and balance law

Let \(p:I\to\mathbb R\) be a rainfall input and let \(a,b,c>0\). Consider
\[
\dot x_1=p-(a+b)x_1+cx_2,\qquad
\dot x_2=bx_1-cx_2,\qquad Q=ax_1. \tag{1}
\]
The states \(x_1,x_2\) are hidden storage compartments and \(Q\) is the
observed discharge. Adding the first two equations gives
\[
\frac{d}{dt}(x_1+x_2)=p-Q. \tag{2}
\]
Thus the model has an exact water-balance law independent of any numerical
solver.

## 2. Elimination of the hidden states

Put
\[
B=a+b,\qquad S=a+b+c,\qquad P=ac.
\]
Differentiate \(Q=ax_1\), use (1), and differentiate once more. Substitution
of \(x_2\) and \(\dot x_2\) gives
\[
Q''+S Q'+P Q = a p'+Pp. \tag{3}
\]
The calculation is an identity in the model equations. In particular, for a
constant input \(p\), the scalar output law depends on the rate triple through
\(S\) and \(P\). This is an upper bound on what a single output equation can
identify; a constant hydrograph can contain still less information.

The Lean file `Hydrology/Basic.lean` formalizes (3) from explicit pointwise
first and second derivative equations. No existence, uniqueness, or numerical
approximation is silently used in that formal statement.

## 3. Exact physical equifinality

Consider
\[
\theta_A=(a,b,c)=(2,2,2),\qquad
\theta_B=(a,b,c)=(1,1,4).
\]
Both have \(S=6\) and \(P=4\). Take \(p(t)=1\). For \(\theta_A\), use the
constant state \((x_1,x_2)=(1/2,1/2)\); for \(\theta_B\), use
\((x_1,x_2)=(1,1/4)\). Direct substitution in (1) gives
\[
\dot x_1=\dot x_2=0,\qquad Q=1
\]
in both systems. The states are nonnegative, the parameters are positive, and
therefore both models produce exactly the same curve \(Q(t)=1\) for every time,
although their parameters and storage partitions differ.

This is a structural counterexample to unique physical calibration from one
unknown-initial-state discharge record. It is not a floating-point or finite
sampling artifact. The theorem `thetaA_thetaB_stationary_unit` in the Lean
package is an exact rational certificate of the two stationary systems.

More generally, fixing \(S,P\) and choosing \(a'>0\), one may set
\[
c'=P/a',\qquad b'=S-a'-c'. \tag{4}
\]
Whenever \(b'>0\), the eliminated output equation is unchanged. This describes
the algebraic equivalence fibre. A claim about a particular physical trajectory
still requires a nonnegative state reconstruction; the displayed stationary
example supplies that reconstruction explicitly.

The algebraic fibre is complete at the coefficient level. For every positive
triple, the Lean theorem `parameter_fibre_identity` proves
\[
b=S-a-P/a,\qquad c=P/a.
\]
Conversely, `fibreParams_totalRate` and `fibreParams_productRate` prove that
every positive choice of \(a\) for which these reconstructed rates are positive
has exactly the prescribed \((S,P)\). The two numerical triples are therefore
instances of a fully explicit one-parameter coefficient-equivalence family.

## 4. Exact recovery under a controlled initial state

Now assume \(p(t)=p_0>0\) is constant and \(x_1(0)=x_2(0)=0\). Directly from
(1),
\[
Q'(0)=ap_0,\qquad Q''(0)=-a(a+b)p_0,\qquad
Q'''(0)=a((a+b)^2+bc)p_0. \tag{5}
\]
Define \(B=-Q''(0)/Q'(0)\). Since all rates and \(p_0\) are positive,
\[
a=\frac{Q'(0)}{p_0},\qquad b=B-a,qquad
c=\frac{Q'''(0)/Q'(0)-B^2}{b}. \tag{6}
\]
The denominator \(b\) is nonzero by the model hypothesis. Therefore the map
from positive rate triples to the first three output derivatives is injective
under this intervention, and (6) is an explicit inverse.

`Hydrology/Recovery.lean` formalizes the three jet identities and proves the
inverse formulas with exact field arithmetic. The sample theorem uses the
rational triple \((2,2,2)\) and rainfall \(p_0=3\) as a regression case.

The same file proves an intervention variant that does not require observing
empty storage. Suppose two constant-rainfall experiments start from the same
unknown state, with \(p_{\rm hi}>p_{\rm lo}\). Subtracting the two output
hydrographs gives a difference trajectory with zero initial state. Its first
three jets satisfy (5) with \(p_0=p_{\rm hi}-p_{\rm lo}\), so the formulas (6)
recover \(a,b,c\) from the paired experiment. The cancellation is encoded in
the hypotheses of `PairedDifferenceJets`; it is not an informal appeal to
numerical fitting.

The word “recover” here means structural and exact identifiability. It does not
assert that noisy measurements permit stable numerical differentiation.

## 5. A finite-storage obstruction to exact power-law recession

The eliminated equation also gives a model-diagnostic theorem. Set rainfall to
zero and suppose, for contradiction, that a nonzero recession has the exact
form
\[
Q(t)=C(\tau+t)^{-\alpha},\qquad C\ne0.
\]
Direct differentiation gives
\[
Q'(t)=-\alpha C(\tau+t)^{-\alpha-1},\qquad
Q''(t)=\alpha(\alpha+1)C(\tau+t)^{-\alpha-2}.
\]
Substitution into \(Q''+S Q'+P Q=0\), followed by multiplication by the
nonzero factor \((\tau+t)^{\alpha+2}/C\), yields
\[
R(t)=\alpha(\alpha+1)-S\alpha(\tau+t)+P(\tau+t)^2=0. \tag{7}
\]
This is a quadratic polynomial with positive leading coefficient \(P\). It
cannot vanish at the three distinct times \(t=0,1,2\): subtracting the three
equations forces \(P=0\), a contradiction. The Lean theorem
`powerLawResidual_not_all_zero` is exactly this three-point argument, and
`nonzero_amplitude_powerLawResidual_not_all_zero` includes the amplitude.

Therefore a finite two-storage linear model cannot produce an exact power-law
recession over a full time interval. This is a structural model-selection
statement, not a fit to observational data. It does not rule out approximate
power laws, heterogeneous distributed linear systems, or nonlinear reservoirs.

## 6. A finite-order diagnostic for two parallel reservoirs

The previous obstruction concerns one finite two-storage realization. A useful
adjacent calculation concerns a pair of parallel recession modes. Let

\[
m_j=w_1\ell_1^j+w_2\ell_2^j,\qquad j=0,1,2,3,
\]

where the weights and rates are real. Since each rate satisfies
\(z^2-(\ell_1+\ell_2)z+\ell_1\ell_2=0\), the moments obey

\[
m_2=s m_1-pm_0,\qquad m_3=s m_2-pm_1,
\quad s=\ell_1+\ell_2,\quad p=\ell_1\ell_2. \tag{8}
\]

Direct expansion gives the Hankel identity

\[
m_0m_2-m_1^2=w_1w_2(\ell_1-\ell_2)^2. \tag{9}
\]

Thus, when both modes have nonzero weights and distinct rates, the determinant
in (9) is nonzero. More generally, the Lean theorem
`recurrence_coefficients_unique` proves that any two coefficient pairs
\((s,p)\) and \((s',p')\) satisfying the two recurrence equations for the same
four moments must coincide whenever this determinant is nonzero. The rates are
then recovered as the unordered roots of \(z^2-sz+p\). This supplies an exact
finite-order diagnostic for a two-mode approximation and identifies precisely
the degenerate cases: a zero weight or coincident rates collapse the Hankel
determinant.

The statement is algebraic and does not assume noisy observations, numerical
differentiation, or a general distributed-reservoir model. The independent
checker uses the exact example \((w_1,w_2,\ell_1,\ell_2)=(2,3,1,4)\), for which
the determinant is exactly \(54\).

## 7. The general finite-mode recurrence

The finite-mode mechanism does not depend on having two or three modes. Let

\[
h_j=\sum_{i=1}^k w_i\lambda_i^j
\]

and let \(A(z)=\sum_{r=0}^d a_rz^r\) satisfy \(A(\lambda_i)=0\) for every
mode. Then, for every \(j\ge0\),

\[
\sum_{r=0}^d a_r h_{j+r}=0. \tag{10}
\]

Indeed, expand the left side as a finite double sum, use
\(\lambda_i^{j+r}=\lambda_i^j\lambda_i^r\), interchange the finite sums, and
factor \(w_i\lambda_i^j\). The remaining inner sum is \(A(\lambda_i)=0\) for
each \(i\). This proof is fully formalized in `Hydrology/Generic.lean` for
arbitrary finite mode count and polynomial degree. It establishes the exact
finite-dimensional recurrence backbone, while uniqueness of rates still needs
nondegenerate Hankel/Vandermonde assumptions.

For a known collection of pairwise distinct rates, the weights are also exactly
identifiable. If two weight vectors give the same first \(k\) moments, their
difference lies in the kernel of the \(k\times k\) Vandermonde matrix. Its
Vandermonde determinant is nonzero, so the difference vanishes. The theorem
`finiteMoment_weights_unique` in `Hydrology/WeightIdentifiability.lean` formalizes
this step. It is deliberately a fixed-rate statement; identifying unknown rates
requires the additional Prony reconstruction argument.

The same nondegeneracy controls the linear Prony step. Let \(H_{ij}=M_{i+j}\)
for \(0\le i,j<k\). The finite moment Hankel matrix factors as a transposed
Vandermonde matrix, a diagonal weight matrix, and a Vandermonde matrix. Its
determinant is therefore the squared Vandermonde determinant multiplied by the
product of the weights. For nonzero weights and pairwise distinct rates this is
nonzero. The theorem `momentHankel_det_ne_zero` in `Hydrology/Prony.lean`
formalizes this factorization and `finite_spectrum_recurrence_unique` proves
that the first \(k\) recurrence equations have a unique coefficient vector.
This closes the linear coefficient-recovery part of Prony identification; matching
the roots of two unknown characteristic polynomials remains a separate step.
More precisely, `two_spectrum_recurrence_coefficients_equal` proves the transfer
statement needed to compare two competing nondegenerate \(k\)-mode models: if
their first \(2k\) moments agree and each model supplies an order-\(k\)
recurrence, the coefficient vectors are identical. Thus the remaining nonlinear
step is exactly root matching (including the permutation of distinct rates), not
another hidden linear-algebra assumption. This is the strongest fully
formalized unknown-rate statement in the current package.

### Finite-spectrum growth obstruction

The finite-mode recurrence has a second consequence under the physical positivity
assumptions. For nonnegative weights and nonnegative rates, write
\[
M_j=\sum_i w_i\lambda_i^j,
\]
and choose \(L\) with \(\lambda_i\le L\) for every active mode. Then
\[
0\le M_j,qquad M_{j+1}\le L M_j. \tag{11}
\]
The Lean theorem `finiteMoment_rate_bound` proves the second inequality exactly
for every finite index type and every \(j\); no numerical approximation is used.

This yields a general analytic no-go statement for **finite positive parallel
reservoirs**. If
\(Q(t)=\sum_i w_i e^{-\lambda_i t}\) with \(w_i>0\) and \(\lambda_i\ge0\),
then its alternating derivative moments are \(M_j=(-1)^jQ^{(j)}(0)\), and the
preceding bound gives \(M_{j+1}/M_j\le L\). For an exact positive shifted power
law \(Q(t)=C(\tau+t)^{-\alpha}\), direct differentiation gives
\[
\frac{(-1)^{j+1}Q^{(j+1)}(0)}{(-1)^jQ^{(j)}(0)}
=\frac{\alpha+j}{\tau},
\]
which is unbounded as \(j\to\infty\). Thus no finite positive parallel
reservoir mixture can equal a shifted power law on an interval. The derivative
formula and the unboundedness argument are now combined in the kernel-checked
discrete theorem `finite_spectrum_powerlaw_ratio_impossible` in
`Hydrology/PowerLawNoGo.lean`; the theorem assumes exactly the derivative-ratio
recurrence and derives a contradiction from the finite-spectrum bound. Connecting
that recurrence to the classical Gamma integral remains written calculus, while
the finite-dimensional no-go implication itself is fully formalized.
This statement does not cover signed modal coefficients, complex modes, or
nonlinear and spatially distributed models.
The same moments have a universal order-two Hankel identity. A finite double-sum
expansion gives
\[
M_0M_2-M_1^2
=\frac12\sum_{i,j}w_iw_j(\lambda_i-\lambda_j)^2. \tag{12}
\]
`Hydrology/Variance.lean` proves this identity for every finite index type,
proves nonnegativity for nonnegative weights, and proves strict positivity when
two positive-weight rates differ. Thus the order-two Hankel determinant is exactly
a weighted measure of rate heterogeneity; the two-mode formula (9) is its first
nontrivial special case. This is an algebraic certificate and does not use
numerical fitting or a presumed model order.

The same argument extends one step further without a numerical approximation.
For three parallel modes define

\[
n_j=\sum_{i=1}^3 w_i\ell_i^j,\qquad 0\le j\le5,
\]

and let \(e_1,e_2,e_3\) be the elementary symmetric functions of the three
rates. The formalized identities are

\[
n_{j+3}=e_1n_{j+2}-e_2n_{j+1}+e_3n_j\quad(j=0,1,2), \tag{13}
\]

and

\[
\det(n_{i+j})_{0\le i,j\le2}
=w_1w_2w_3(\ell_1-\ell_2)^2(\ell_1-\ell_3)^2(\ell_2-\ell_3)^2. \tag{14}
\]

The module `Hydrology/Parallel3.lean` also proves that each rate is a root of
the characteristic cubic. Consequently, positive weights and pairwise
distinct rates give a strict order-three Hankel certificate; zero weights or
coincident rates are exactly the algebraic degeneracies detected by (12). The
independent exact example uses
\((w_1,w_2,w_3,\ell_1,\ell_2,\ell_3)=(1,2,3,1,2,4)\),
for which the determinant is \(216\).

## 8. Exact continuum construction of a power-law tail

The finite-dimensional no-go theorem has a physically conservative extension after
replacing finitely many reservoirs by a continuum of rates. For \(\alpha>1\) and
\(\tau>0\), let independent reservoirs with decay rate \(\lambda>0\) have initial
**storage density**

\[
s_{\alpha,\tau}(\lambda)=\lambda^{\alpha-2}e^{-\tau\lambda}.
\]

A linear reservoir with rate \(\lambda\) satisfies
\(\dot x_\lambda=-\lambda x_\lambda\), and its discharge is \(\lambda x_\lambda\).
Therefore the aggregate discharge is

\[
Q(t)=\int_0^\infty \lambda s_{\alpha,\tau}(\lambda)e^{-\lambda t}\,d\lambda
=\int_0^\infty \lambda^{\alpha-1}e^{-(\tau+t)\lambda}\,d\lambda
=\Gamma(\alpha)(\tau+t)^{-\alpha}. \tag{15}
\]

Equation (15) is the standard Gamma-integral identity. The initial aggregate storage
is finite because
\[
\int_0^\infty s_{\alpha,\tau}(\lambda)\,d\lambda
=\Gamma(\alpha-1)\tau^{1-\alpha}<\infty.
\]
Thus a continuous rate spectrum gives an exact shifted power law with finite initial
storage, while every finite positive reservoir network is excluded by the
finite-dimensional obstruction above. This provides a concrete model-building
interpretation of the distinction between exponential mixtures and power-law
recession. The integral identity is written mathematics here; it is not claimed as
part of the current Lean package.

## 9. A local curvature diagnostic

The continuum construction gives an observable local protocol. For a shifted
power law \(Q(t)=C(\tau+t)^{-\alpha}\), direct differentiation yields

\[
I(t):=\frac{Q(t)Q''(t)}{Q'(t)^2}
=\frac{\alpha+1}{\alpha}=1+\frac1{\alpha},
\qquad
\alpha=\frac1{I(t)-1}. \tag{16}
\]

The local slope then gives

\[
\tau=\frac{-\alpha Q(t)}{Q'(t)}-t. \tag{17}
\]

The Lean theorem `powerLaw_alpha_recovery` proves the first inversion from the
algebraic identity \(I=(\alpha+1)/\alpha\), and
`powerLaw_shift_recovery` proves the second from
\(Q'(\tau+t)=-\alpha Q\), with the required nonzero denominators explicit.
The calculus substitution establishing these jet identities is written in the
paper; the inverse algebra is kernel checked.

For two positive parallel exponential modes, put
\(u_i(t)=w_i e^{-\lambda_i t}\). The Hankel identity becomes

\[
Q(t)Q''(t)-Q'(t)^2
=u_1(t)u_2(t)(\lambda_1-\lambda_2)^2. \tag{18}
\]

It is strict for distinct active rates, but after division by \(Q(t)^2\) it
vanishes asymptotically as the slower mode dominates. An exact power law has the
constant invariant \(I(t)>1\). This gives a structural diagnostic separating a
persistent power-law curvature from every finite two-rate recession; it is not a
statistical fitting claim.

## 10. Implications and limits



The two statements answer complementary model-design questions. With unknown
initial storage, the output equation has a genuine parameter symmetry and a
physical equifinality certificate. With a known empty initial state and a
controlled rainfall step, three derivatives remove that symmetry in this
three-parameter model. Initial-state assumptions and input design are therefore
part of the identifiability statement, rather than implementation details.

The result is deliberately model-specific. It does not claim a universal
identifiability theorem for conceptual hydrology, nor does it settle models with
thresholds, power-law reservoirs, spatial routing, or finite-time integral-only
observations. A natural next problem is to classify the corresponding
input/state equivalence classes in one of those nonlinear extensions.

## 11. Reproducibility and prior context

Run the exact rational checker with

```sh
python3 -B checks/exact.py
python3 -B -O checks/exact.py
```

The Lean package is built with Lean 4.34.1 and the pinned Mathlib revision:

```sh
cd formalizations/hydrology-identifiability
lake build Hydrology
```

Relevant prior context includes Sorooshian–Gupta, “The analysis of
conceptual-model calibration,” [Water Resources Research 21 (1985), DOI
10.1029/WR021i004p00487](https://doi.org/10.1029/WR021i004p00487); Shin et al.,
“Identifiability of hydrologic models,” [Journal of Hydrology (2015), DOI
10.1016/j.jhydrol.2014.11.040](https://doi.org/10.1016/j.jhydrol.2014.11.040);
and Kirchner, “Catchments as simple dynamical systems,” [Water Resources
Research (2009), DOI 10.1029/2009WR008777](https://doi.org/10.1029/2009WR008777).
Two-parallel-reservoir approximations of power-law recession are treated by
Tashie et al., [DOI 10.1061/(ASCE)HE.1943-5584.0001518](https://doi.org/10.1061/%28ASCE%29HE.1943-5584.0001518).
This note makes no historical priority claim.
