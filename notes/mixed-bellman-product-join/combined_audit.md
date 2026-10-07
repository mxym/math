# Independent audit of the mixed quadratic/quartic upper theorem

**Audit outcome: PASS.** The three component proofs and their exact verifiers establish the proposed invariant for the complete point-generated product/join class:

\[
\log Q(K)\le P(D,H)
=\frac{49}{1000}D-\frac{87}{2000}\frac{H^2}{D}
-\frac{11}{2000}\frac{H^4}{D^3}.
\]

Consequently

\[
2.8534<\Gamma_{\mathcal C}\le e^{1049/1000}<2.855.
\]

The lower endpoint is the existing certified self-similar construction. The new contribution audited here is the upper invariant, not a new lower construction or a determination of the optimum. It concerns the point-generated recursive class only.

The assembled complete proof `proof.md` was additionally read in full after the component replays. Its constants, potential signs, matrix determinant, state hypotheses, certificate coverage, actual-constant comparison, and spectral consequence agree with the audited components. The parent rechecked the public baseline through commit `3360e7191cf564a46d09edcbfbd107c9178bd98f`, whose changes clarify the existing quadratic tail guards and leave its bound unchanged. No mathematical revision to the assembled proof was requested.

## Induction and asymptotic consequence

Put \(\alpha=87/2000\), \(\beta=11/2000\), and \(T=\alpha+\beta=49/1000\). The formal point has \(D=H=Q=1\), and hence \(P=0=\log Q\). For joins, weighted Jensen applied to \(u^2\) and \(u^4\) proves that their homogeneous perspective functions are subadditive. Their negative combination in \(P\), plus the additive term \(TD\), is superadditive. The join calculus therefore preserves the invariant.

For a Cartesian product of dimensions \(r,s\), the potential increment is exactly

\[
-T+\alpha\widehat G_2+\beta\widehat G_4,
\]

where \(\widehat G_p=H^p/(r+1)^{p-1}+J^p/(s+1)^{p-1}-(H')^p/(r+s+1)^{p-1}\), and \(H'\) is the weighted harmonic mean from the exact calculus. Bounding that harmonic mean by the arithmetic mean for the quadratic term and by the fourth-power mean for the quartic term gives the component proofs' concave relaxation. All bound directions are correct because both \(\alpha,\beta>0\).

The class state bounds \(2\le H\le D\) are justified: the interval starts with \(H=2\), joins add \(H\), products average \(a=1/H\), and the established lower bound on \(a\) gives \(H\le D\). Products with a formal point preserve the body. Thus structural induction covers every finite expression and its images under invertible affine maps on affine hulls. Rank-dropping maps are excluded.

The final potential gives \(\log\lambda\le P/D\le T\). The spectral reduction identifies the class rate as \(e\sup\lambda\), yielding \(\Gamma_{\mathcal C}\le e^{1+T}\). The large-dimension exact checker verifies the rational exponential comparison \(e^{1049/1000}<571/200=2.855\) by a positive Taylor sum and geometric upper tail.

## Finite rectangles

The proof `finite_proof.md` and verifier `check_finite.py` were read in full. The verifier independently replayed all 19,900 rectangles \(1\le r\le s\le199\), covering every real state in \([2,r+1]\times[2,s+1]\).

The relaxed quadratic form is positive definite. Independently expanding its matrix gives determinant

\[
\frac{rs(3(r+s)+2)}{(r+1)(r+s)^2(s+1)(r+s+1)}>0.
\]

The diagonal quartic coefficients are positive, so the quartic term is convex. The logarithm of the positive affine product variable is concave. Thus the violation function is globally strictly concave, and a rational supporting plane at any stored point bounds its whole rectangle. The rational gradients and the corner maximization formula in the checker are exact and have the correct factor dimensions.

The logarithm proof uses 20 positive atanh-series terms, an explicit geometric remainder, range reduction, and sign-correct interval multiplication by negative powers of two. Both dyadic endpoints are rounded outward by integer floor/ceiling operations. These operations preserve containment. The factorial-log identity, row-order checks, integer types, point-box membership, and complete coverage were all reviewed.

The independent replay is `independent_finite_replay.json`. All rectangles have a certified upper bound below \(-3/2000\). The largest upper bound is at \((5,5)\). Numerical point discovery is not a proof dependency.

## Imbalanced infinite tails

The proof `mixed_tail_proof.md`, arithmetic core, and checker were read in full. The exact substitution \(z=1/s\), \(h=H\), \(j=J/(s+1)\) turns \(1\le r<200,\ s\ge200\) into the fixed compact interval \(0\le z\le1/200\) and box \([2,r+1]\times[0,1]\). Both quadratic and quartic cancellation identities were independently verified by general symbolic expansion: their differences are identically zero.

The logarithm bound is valid. Writing the Stirling remainder as \(\delta_k\), Robbins' bounds and \(n\ge s+1\) imply \(\delta_n<\delta_s\), because \(1/(12n)<1/(12s+1)\). Thus

\[
C<g(r)e^{-r}\sqrt{1+r/s}.
\]

Combining this with the normalized product variable gives exactly the constant logarithm and the \(-\tfrac12\log(1+rz)\) term in the checker. Its interval upper endpoint has the correct sign.

For each compact cell, Young's inequality gives the verified uniform quadratic remainder

\[
q_2(\Delta h,\Delta j)\ge
\frac{a_-}{2}(\Delta h)^2+
\left(c_--\frac{\max(b_-^2,b_+^2)}{2a_-}\right)(\Delta j)^2.
\]

Both coefficients are required positive. Concavity of the logarithm and convexity of the quartic give a supporting bound with this stronger negative quadratic remainder. The checker maximizes the two resulting box parabolas exactly. For negative displacements it uses the lower gradient endpoint; for positive displacements it uses the upper endpoint. This is the correct interval support rule.

The 28-term logarithm intervals, their geometric remainder, decimal outward rounding, interval powers, signed reciprocals, and multiplication bounds were reviewed. Every cell checks a whole continuum of \(z,h,j\). After checking each cell, the verifier sorts intervals and requires exact adjacency from 0 to \(1/200\) for each of the 199 small dimensions, preventing both gaps and overlaps.

An independent optimized-Python replay passed all **15,568 cells**, with maximum dyadic depth **7** and uniform upper margin below **\(-1/100000000\)**. Its record is `independent_tail_replay_optimized.json`. The certificate SHA-256 is

```text
3d19c41c656b952b4e649f1f9fb0ea2ff3a14c6c26086b91e8c7a780fba4cb94
```

The initial checker run used an earlier, overstrong reporting target \(-10^{-7}\); all cells and coverage passed before that target failed. The final target \(-10^{-8}\) is strictly certified by the completed replay. This is a corrected reporting endpoint, not a relaxation to an uncertified sign.

## Both dimensions large

The proof `mixed_large_dimensions.md` was independently read. Its exact nonnegative-square identity for the quadratic reduction was verified by general symbolic expansion. The diagonal quartic coefficients are positive, so dropping that quartic term increases the violation. Maximizing the remaining scalar concave function gives the correct criterion

\[
C^2/k<2\alpha\exp(1-2T).
\]

The factorial estimate, factor of two, and rational ceiling \(1615/7536\) are correct for \(r,s\ge160\). The exact Machin lower bound on \(\pi\), positive degree-10 exponential lower sum, and final exponential upper comparison all passed in ordinary and optimized Python.

These three regions cover every positive dimension pair: if both dimensions are below 200 the finite certificate applies; if the smaller is below 200 and the larger is at least 200 the compact-tail certificate applies; if both are at least 200 the analytic large-dimension lemma applies. Its stronger cutoff 160 merely adds overlap.

## Comparison and limits

The already public quadratic theorem uses \(\alpha_*=(11/85)\log(189/128)\) and ceiling \(e^{1+\alpha_*}\). The new ceiling is strictly smaller by an exact analytic comparison:

\[
\alpha_*>
\frac{11}{85}\frac{2(189/128-1)}{189/128+1}
=\frac{1342}{26945}
>\frac{49}{1000}=T.
\]

The last difference is \(21695/26945000>0\). This compares the actual prior ceiling, not only its displayed decimal rounding.

No material mathematical gap was found. This audit is model conducted; it is not external peer review or proof-assistant formalization. The theorem does not identify the optimum, does not improve the limiting lower construction, and does not apply to arbitrary starting convex bodies.
