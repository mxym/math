# Independent analytic audit

**Proof standard:** written derivation plus replayable rational interval
cross-checks. Neither a Lean kernel formalization nor independent
human peer review has been completed. Historical priority is not claimed.

## Key mathematical checks

1. **Quantifiers:** Theorem A holds for all k>=2, d>=3,
   without optimizer attainment. Theorem B requires log k>=100
   and d>=L^2/log L. Theorem C is asymptotic for any *fixed*
   finite additive-error constant C>=0. The supremum may
   be approached by arbitrary measurable sets.
2. **Halfspace one-cell normalization:** a cell of mass 1/k
   has moment norm at most h_k/k. Since every squared norm
   is <=(h_k/k)*norm, the full objective is bounded by
   h_k/k times the sum of moment norms.
3. **Support score:** for any first-moment direction u_i,
   the expected maximum of <u_i,G> is at least
   sum_i||b_i||. This uses the given partition pointwise
   and needs no Laguerre, Voronoi or stationary assumption.
4. **Gamma ratio:** gamma log-convexity gives
   Gamma(z+1/2)^2<=z Gamma(z)^2 for z>0.
   The spherical marginal density constant is therefore
   bounded by sqrt((d-1)/(2pi)) for all d>=3.
5. **Spherical-cap tail:** derivative of
   (1-u^2)^((d-1)/2) equals
   -(d-1)u(1-u^2)^((d-3)/2). The integral bound
   has an indispensable prefactor 1/[a sqrt(2pi(d-1))].
   Dropping this factor would lose the -loglog correction
   and invalidate the quadratic dimension conclusion.
6. **Tail integration:** log of the cap union envelope has
   derivative at most -(d-1)a for u>=a.
   Therefore the integrated maximum tail is at most
   B(a)/[(d-1)a]; Gaussian radius and direction are
   independent, and E radius <=sqrt d by Jensen.
7. **Large-log threshold:** for L>=100,
   log L<=sqrt L and d>=L^2/log L>=10L.
   The chosen S lies in [L,3L] and strictly below d.
   The exact series inequality
   log(1-x)<=-x-x^2/2
   produces log beta <=-8+3+3/20+9/400<0.
   No numerical approximation enters this bound.
8. **Normal quantile:** for k>=e^100, the classical
   Mills inequalities give h_k^2 >=2L-log L-4.
   The strict constant log(16pi)<4 follows from
   pi<22/7, e>8/3, and a rational power comparison.
9. **Squared error identity:** the implication
   h_k(h_k-H)>=(h_k^2-H^2)/2 follows from
   (h_k-H)^2/2>=0 and holds even if H>h_k.
   This avoids any unjustified ordering of maxima.
10. **Dimension below the cap threshold:** lift a
    partition of dimension d<D0=ceil(L^2/logL)
    to dimension D0. Monotonicity of F_d then
    gives a defect at least log L-O(1),
    eventually incompatible with fixed C.
    Thus the final L^2/(C+16) bound applies
    without a circular d>=D0 assumption.
11. **Upper comparator:** the claimed discrepancy
    U_k-F_infty(k)<=2/k is inherited from the
    independently documented arbitrary-mass envelope;
    the proof in this note does *not* assume exact
    Standard Simplex optimality.
12. **Scope of improvement:** the result proves an
    Omega(log^2 k) *necessary* dimension. It does not
    construct an equal-mass code in that dimension.
    The best documented sufficient dimension in this
    programme remains O(log^3 k).

## Exact program controls

The checker carries normalizer pi, logarithms of integers
up to 10^1000, and log-log threshold terms as arbitrarily
large exact fractions with outward error intervals.
The arctanh positive series and Machin arctan alternating
series enclose every transcendental value used in the
12 illustrative cap-threshold comparisons.

Tested samples include dimensions
ceil(L^2/log L), twice that, and ten times that.
Each sample verifies the *actual* cap log upper
bound is strictly negative, in addition to the
universal algebra in the paper.

No binary floating-point operation, Gaussian numerical
integration or heuristic solver output is used to
certify a mathematical inequality.

The finite tests are supplementary; universal validity
rests on the written lemmas.
