# Upper half of the quadratic comparison; what a standard switch does not give

Use the normalization, weights W₂,W₃, and notation of QuadraticLowDegreeReduction.md. Along even targets the two unconditional estimates are

    .86868 ≤ liminf (R/4+W₂+W₃)/(NS)
           ≤ limsup (R/4+W₂+W₃)/(NS) < 1.266.                              (1)

In particular the genuinely proved upper for the **low sum** (W₂+W₃)/(NS) is <1.266 in limsup, since R≥0. It is **not** the required <.86868 (with a strict margin) and does not assert the conditional 11%-above-reference hypothesis.

For squarefree m with three factors and ordered normalized logs a≤b≤c, the weight is explicitly

    Q₃(a,b,c) = 2ab − ½(a+b−c)₊².                                          (2)

If c≥a+b, the two smallest factors exhaust the quadratic differences and yield 2ab. Otherwise set v=(a+b−c)/2 in [0,a]; reflect the difference for the pair a,b at v, subtract the shift by c, and obtain 2ab−2v². This is the positive ternary box-spline contribution, not log P⁻(m).

For (1), Q vanishes at every even rank k≥4 and Q≤0 at k=5. For odd k≥7, the *combined signed reference* Σ I_k(Q) is nonnegative: by (4) and radial integration in the quadratic note its integrand is the alternating series starting at z⁷/7!, with z=2 arctan(t/2)∈[0,π], and the term magnitudes decrease. All signs concern the reference only; the actual upper-sieve transfer is applied to the nonnegative negative parts. It gives

    limsup (actual negative mass of odd k≥7)/(NS)
       ≤ 4 Σ I_k((−Q)₊) ≤ 2 Σ I_k(|Q|) ≤ 2A < .12296.

The full five-factor negative part of the reference is exactly −I₅(Q). Substitute t=2tan v, T=π/2 into (4)'s Laplace integral as in the quadratic note. Twice integrating by parts gives

    ∫₀^∞ arctan(t/2)⁵dt/t³ = −T⁵/8 + (5/2)∫₀^T v³cot v dv.
    ∫₀^T v³cot v dv = T³log 2−(9/8)Tζ(3).

For the latter insert the L² cosine series of log sin v into −3∫₀^T v²log sin v dv. With coefficient (2/π)2⁵/5!=8/(15π), one obtains

    −I₅(Q) = −π⁴/480 + π²log(2)/6 − 3ζ(3)/4 < .035704.

The elementary rational certificate check_quadratic_upper.py reproduces the bound using the cosine-free constant enclosures from check_six.py (Machin formula, log 2 power series, integral-test tails). Hence the full actual negative mass is at most (4·.035704+.12296)NS in limsup. By the unconditional total quadratic mean this proves the upper side of (1); the lower side was already proved in the quadratic note.

**Arithmetic scope, not a further error estimate.** [Wu, *Chen's double sieve, Goldbach's conjecture and the twin prime problem*, Lemma 2.6, p. 222](https://www.impan.pl/shop/publication/transaction/download/product/82961), as restated in [Li–Liu, Lemma 3.5](https://arxiv.org/html/2606.05224v2), allows a large residue |a|≤X for a dyadic bilinear sequence α_m β_n with X=MN; β_n obeys the stated uniform Siegel–Walfisz condition also with coprimality restrictions and vanishes when n has a prime factor below exp((log log n)²). Its modulus weight is well-factorable of order one, with level X^{5(1−ν)/9−ε} for ε≤ν=log N/log X≤1/10 (here N is a dyadic factor scale, not the Goldbach target). The stronger range subdivisions in Wu's preceding lemma / Li–Liu's Lemma 3.4 assume |a|≤(log X)^A; the fixed-residue 3/5 upper-sieve estimate in Li–Liu Lemma 3.3 has dependence on a. These are progression discrepancies under the given weights, not estimates for the prime condition N−∏p_i prime in a whole factor box. An upper sieve at any ordinary distribution exponent θ≤1 still has the linear-sieve constant 2/θ≥2 when used on its own; even the ideal factor 2 applied separately to both positive reference weights gives 2(.5+log2−π²/24)>.86868. This observation is a limitation of that direct upper-majorant argument, not a theorem ruling out a new coupled or parity-sensitive argument using actual primes.
