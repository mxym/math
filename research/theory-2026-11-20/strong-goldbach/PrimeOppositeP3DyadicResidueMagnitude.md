# Dyadic residue audit: radical two does not remove the moving phase or the known spectral magnitude losses

Written follow-up, 2026-11-24, to the [signed middle Poisson work](PrimeOppositeP3JointSOrthogonality.md). This gives a quantitative obstruction to dropping the true archimedean reciprocity factor and an audit of candidate primary dispersion estimates. It is not a negative theorem against new dyadic-specific cancellation.

## The actual archimedean factor is not close to 1 even in mean square

In the switched block for the actual source primes \(p\asymp H=\sqrt N\), take \(N=2^k\), \(q\asymp Q=N^{.20}\) a true prime, \(s\asymp S=N^{.068}\) a true squarefree product of two distinct odd primes near angular size .034, and \(R=N^{.27}\). These exponents are inside the previously isolated .06 target strip (\(.27+3(.20)+1.8(.068)=.9924<1\)) and outside the current paid first term. Keep the exact original Poisson h-scale \(A_0=RQS/H=N^{.038}\), and any integer \(0<|h|\asymp A_0\). For \(r\asymp R\) on literal units, reciprocity gives
\[
 e\!\left(\frac{hN\overline r}{qs}\right)
 =e\!\left(-\frac{hN\overline{qs}}r\right)
  e\!\left(\frac{hN}{qsr}\right).
\]
The last archimedean phase cannot be replaced by 1, even at density one or in a mean-square sense. More precisely for the unit set \(\mathcal U=\{R<r\le2R:(r,2qs)=1\}\),
\[
 \frac1{|\mathcal U|}\sum_{r\in\mathcal U}
     \left|e(hN/(qsr))-1\right|^2=2+o(1),
 \tag{1}
\]
uniformly at the indicated dyadic scales. This is an unweighted unit mean-square for the residual phase in isolation, not a statement about its correlation with the other modular phase or the true Selberg coefficients.

Indeed \(f(r)=hN/(qsr)\) has \(|f''(r)|\asymp\lambda=N^{-.04}\) uniformly on the interval: the phase value scale is \(N^{.5}\), and \(R^2=N^{.54}\). On a Möbius multiple \(r=dm\), \(d\mid2qs\), the actual interval length is \(O(R/d)\) and the derivative scale is \(d^2\lambda\). The elementary second-derivative estimate, or trivial counting if \(d^2\lambda>1\), bounds the multiple sum by
\[
 O\left(R\sqrt\lambda+(d\sqrt\lambda)^{-1}\right).
\]
The bound also dominates endpoint floor terms. Exact divisor inclusion-exclusion over \(d\mid2qs\) thus gives total size
\[
 \ll \tau(2qs)\,[R\sqrt\lambda+\lambda^{-1/2}]
    =N^{.25+o(1)}.
\]
Here \(\tau(2qs)=N^{o(1)}\) (indeed bounded in the chosen actual two-factor sector). Meanwhile \(|\mathcal U|=(1/2+o(1))R\), directly from the three large odd prime factors and the parity constraint. Expansion of the square and division by this unit count proves (1). More generally the same argument works for supported odd squarefree \(s\) with \(\varphi(2qs)/(2qs)\ge(\log N)^{-C}\). This calculation does not forbid keeping that phase and proving a new oscillatory bound for its *product* with the exact modular reciprocal phase.

Also there is no common small integer representative of the true target residue on a positive share of the prime marks. For every \(a\ne N\) with \(|a|\le N^{1-\epsilon}\), all actual \(q\asymp N^{.20}\) for which \(a\equiv N\pmod q\) divide the same nonzero integer \(N-a\), whose magnitude is \(O(N)\). There are at most \(O(1)\) such prime marks, by multiplying them. It is therefore not legitimate to replace \(N\) by one small representative on a positive proportion of these genuine \(q\). Taking representatives separately for each modulus is an entirely different uniformity requirement.

## What the primary sources actually control

* [Lichtman, arXiv:2309.08522, Lemma 4.6](https://arxiv.org/html/2309.08522v1#S4) explicitly uses \(|a|<x^{1+\epsilon}\) in replacing a reciprocal phase by its Bézout-transformed modulo-1 part without the last archimedean fraction. The proof writes that last factor with numerator \(ah\), and the approximation error is bounded in terms of the numerical ratio \(|a|/x\), independently of \(\operatorname{rad}(a)\). At the present prime source scale \(x\asymp\sqrt N\) one has \(a=N\asymp x^2\). The displayed auxiliary simplification and hence Proposition 5.2 cannot be applied by treating a power of 2 as a small residue. Equation (1) separately checks the analogous reciprocity factor in the team's exact actual switched model, not merely the stated hypothesis of someone else's theorem.
* [Lichtman, Theorems 10.1–10.2, formulas (10.3)–(10.4), and (10.13)](https://arxiv.org/html/2309.08522v1#S10) exhibit separately the supported-divisor sum \(n''\mid a^\infty\), the full-number factors \((a n'')^\theta\) and \(aMN\), and the full archimedean Kuznetsov parameter \(X=CS\sqrt R/(4\pi\sqrt{aMN})\) in the author's notation. Putting \(a=2^k\) limits the sum to powers of 2, but does not change the factor \(a^\theta\) even in the \(n''=1\) summand (when that summand has nonzero coefficient norm), nor the Bessel-argument scale. The theorem does not license simply replacing \(a\) by 2 in any of these independent appearances. No claim here is made that every application of the quoted spectral bound fails, or that an additional Hecke/spectral averaging argument for powers of 2 is impossible.
* [Pascadi, arXiv:2505.00653, Theorem 1.3](https://arxiv.org/html/2505.00653#S1) proves the larger exponents \(5/8\) and \(3/5\) for its specified factorable weights with the implied constant depending on the fixed residue \(a\). It does not assert uniformity for the growing sequence \(a=2^k\asymp x^2\), nor by itself that the actual marked \(q\) and switched factors satisfy its weight hypotheses. A bound with a residue-dependent constant cannot be specialized to a growing residue merely because the residue has one prime factor.

The surviving viable analytic alternatives must either retain the full reciprocal archimedean phase and bound it jointly, genuinely obtain a first-moment theorem for this lacunary growing residue, or exploit the exact dyadic input in a different spectral arrangement. The above points neither estimate the joint archimedean/modular correlation nor prove a P3 gain.