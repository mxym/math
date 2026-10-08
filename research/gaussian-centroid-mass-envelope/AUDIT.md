# Mathematical correctness and reproducibility audit

Status: **self-audit of full written argument**, not independent
human peer review or a formal Lean kernel proof.

## The exact quantifiers

Theorems 4 and 6 apply to *every* integer k>=2, every strictly
positive real vector p summing to 1, and every Gaussian dimension
d>=k-1. The upper bound is valid even when d<k-1.

The mass ratios may be arbitrarily large; no epsilon-away-from-zero
hypothesis is hidden. The lower construction is deterministic and
uses k-1 independent standard-normal coordinates. Its thresholds
are mathematical quantiles, uniquely defined by continuous
strict monotonicity of the Gaussian CDF.

The optimizer is a supremum over all measurable ordered
partitions, up to Gaussian-null boundaries. No convexity,
smoothness, conical, or simplex hypothesis is inserted.

## Independent line-by-line proof review

1. **Mass telescoping**: write S_i = sum_{j>=i} p_j and
   q_i=p_i/S_i. Then 1-q_i=S_(i+1)/S_i. The probability
   that the first i-1 coordinate cuts are survived is
   exactly S_i (not an approximation). The i-th cell has
   probability S_i*q_i=p_i, and the final cell has
   probability S_k=p_k.
2. **First-moment diagonal**: the exact identity
   integral_t^infty x*phi(x) dx=phi(t) is independent of
   previous-coordinate cuts. Hence b_(i,i)=p_i*h(q_i).
   The full off-diagonal moment formula in paper.md is
   independently derived by conditioning on Z_j<t_j.
3. **Global one-cell ceiling**: compare each arbitrary
   cell of mass q to a halfspace in its first-moment
   direction. The signed threshold integral is
   nonnegative pointwise. The q-mass constraint cancels
   the threshold terms exactly.
4. **Global hazard derivative**: q(t)=1-Phi(t), so
   d t / d log(1/q)=1/h. The variance identity
   Var(Z|Z>=t)=1-h(h-t)>0 and the strict conditional
   mean inequality h>t together imply
   0<d(h^2)/d log(1/q)<2 for *all* t in R,
   including negative threshold values.
5. **Order-sensitive weighted entropy**: descending p_i
   and ascending log(1/S_i) imply a nonpositive
   weighted covariance. The integral comparison
   p_i log(1/S_i) <= integral_(S_(i+1))^(S_i)
   log(1/s) ds is valid even for S_(k+1)=0
   (the improper integral is finite, equal to 1).
6. **Last-cell repair**: the earlier 3 Q estimate could
   be sharpened. Conditional Jensen applied to
   E exp(lambda Z)=exp(lambda^2/2) proves
   phi(t_q)^2 <=2 q^2 log(1/q).
   This is exactly the final i=k term of the same
   weighted residual-mass budget, giving **2 Q**,
   not 3 Q.
7. **Dimension**: the staircase construction
   uses exactly k-1 coordinates; tensoring with an
   independent centered Gaussian preserves both cell
   masses and the norm of each first moment.
8. **Quantile entropy bound**: the universal +/-17
   scalar estimate splits at q=1/10. When q<=1/10,
   Mills bounds, q(1)>1/10 and elementary logarithm
   inequalities give the stated two-sided bound
   with smaller constants. When q>1/10,
   the Gaussian density maximum and pi>3 give
   h(q)^2<17, while the entropy scalar lies in
   [0,5]. No numerical tail fit appears.
9. **Asymptotic quantifiers**: for arbitrary p_max->0,
   all log(1/p_i) >=log(1/p_max)->infinity.
   Thus both the log-log correction and the O(Q)
   remainder are uniformly lower-order relative to
   the leading weighted entropy. Comparable-mass
   specialization is separately justified.
10. **Noise stability**: orthonormal Hermite coefficients
    have nonnegative squared weights for rho>=0;
    the sum of their weights is 1 by Parseval.
    Degree zero is Q(p), degree one the first-moment
    objective. All higher degrees contribute between
    0 and rho^2(1-Q), giving the advertised bound
    without claiming equality or optimality.
11. **Collision-deficit concentration**: the sum of
    nonnegative one-cell deficits is at most 2Q
    for every qualifying near-optimal partition,
    and individual ceilings exceed
    p_i^2*log(1/p_max) when p_max<=exp(-40).

## Exact checker: scope and expected negatives

Run from this directory:

    python3 check_exact.py
    python3 check_exact.py --quick

The Python standard-library Fraction type tracks every
mass and survival product exactly. For logs of rational
positive numbers, the checker uses the atanh series
after powers-of-two argument reduction, with **outward
fixed-point integer rounding to denominator 10^90**
and an explicit positive geometric tail. The included
finite family contains equal, geometrically varying,
rationally weighted, high-contrast, and large
multi-level mass vectors.

The checker also constructs a genuinely *unsorted*
71-cell probability vector for which
sum p_i^2 log(1/S_i) >sum p_i^2.
The strict failure is certified by **rational interval
bounds for logs**. This tests that we have not
silently dropped the vital descending-order hypothesis.

**Important limitation:** the script verifies
finite rational instances of the algebraic and
transcendental integral comparison, not the universal
Gaussian calculus identities. Universal validity
depends on the written proofs, not an observed PASS.

## Remaining scholarly work

- Systematic comparison against prior Gaussian
  level-1 Fourier/Hermite entropy inequalities.
- Independent mathematical peer review and,
  if valuable, kernel-level formalization of
  the mass-entropy lemma and scalar hazard bound.
- Investigate the smallest possible universal additive
  coefficient in the all-mass envelope. Constant 2
  is proved here; global optimality is **not**.
- The exact fixed-k, k>=4, equal-mass Gaussian
  simplex extremal problem is **not** resolved.

For current manuscript scope, prior work and
limitations, see paper.md and LITERATURE.md.
