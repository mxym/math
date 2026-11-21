# A stability barrier for signed pointwise major-arc witnesses

This is a deterministic uncertainty estimate for **one specific strategy** for the binary Goldbach problem. It does not use artificial prime sequences, assume GRH, or rule out actual minor-arc phase cancellation. We use the normalized circle and e(x)=exp(2πix).

## Finite-window lemma

For any finite complex measure μ on the circle with μ̂(0)=1, an integer H≥1, and a union E of at most J≥1 arcs of normalized total length m, write
$$
 B=\sum_{1\le |j|\le H}|\widehat\mu(j)|,\qquad D=1+B.
$$
There are absolute constants c,C>0 such that if m≤1/(16D) and H≥CJD, then
$$
 |\mu|(\mathbb T\setminus E)+C\exp(-cH/(JD))\,|\mu|(E)\ge 3/4.                 \tag{1}
$$
More precisely, with δ>0 such that m+2Jδ≤1/(4D), the exponential factor can be replaced by C exp(−cHδ) if Hδ≥C. Thus the numerical 3/4 can be replaced by any fixed number below 1 with corresponding constants. No sign or absolute continuity of μ is needed.

**Proof.** Let F be the δ-neighborhood of E and let G be the indicator of its complement. Its mean is at least 1−|F|, and every nonconstant Fourier coefficient has modulus at most |F|. Put s=ceil(4/δ), k=floor(H/(s−1)), and use the nonnegative, unit-mass trigonometric kernel
$$
 K(t)=Z^{-1}\left|s^{-1}\sum_{j=0}^{s-1} e(jt)\right|^{2k}.
$$
It has degree at most H. For |t|≤c₀/(s√k), rotate the terms about the middle phase and bound the real part below by 1−C₀s²t². Thus Z≥c₁/(s√k). At circular distance ||t||≥δ the absolute Dirichlet average is at most (2s||t||)⁻¹, so
$$
 \int_{\|t\|\ge\delta}K(t)\,dt
 \le C s\sqrt{k}\,\frac{2\delta}{2k-1}(2s\delta)^{-2k}
 \le C e^{-ck}.
$$
Here 4≤sδ≤5 (δ≤1). When Hδ is sufficiently large, k≥cHδ. The polynomial P=G*K has 0≤P≤1, mean at least 1−|F|, nonconstant coefficients of modulus ≤|F|, and on E is ≤Ce⁻ᶜᴴδ because E lies distance at least δ (up to endpoints) from the support of G. Since P has degree H, the real part of its μ-integral is at least 1−|F|(1+B)≥3/4. Taking absolute values separately on E and its complement proves the δ-version. For the stated version use δ=1/(16JD).

## Consequence for weighted prime convolution

For sufficiently large even N choose a fixed nonnegative nonzero smooth weight f compactly supported in (0,1), positive near 1/2. Define S(α)=Σ_p (log p)f(p/N)e(pα) and let r(m) be the coefficients of S². The prime 2 is outside the support, all odd coefficients vanish, and all even coefficients are nonnegative. Write I(s)=∫f(u)f(s−u)du and set M(m)=N I(m/N)·𝔖(m) on the positive even integers (zero elsewhere). This is the ordinary full-circle Hardy–Littlewood pole **model**, not an estimate of r(m) term by term.

Consider any finite measure λ_N with mass 1. Use the sign convention ω(h)=∫e(2hα)dλ_N(α), and require real ω(h)≤0 for every h≠0 where I((N+2h)/N)>0. A nonzero prime contribution implies this last strict inequality. Integrate e(−Nα)S(α)² against λ_N. Its value then is
$$
 r(N)+\sum_{h\ne0}\omega(h)r(N+2h)\le r(N).
$$
Suppose that the **model comparison at that same target is strictly positive**, i.e. M(N)+Σ_{h≠0}ω(h)M(N+2h)>0. For some constant η>0 depending only on f, I(1+2h/N) is bounded below by a positive constant throughout |h|≤ηN. The Euler product gives an absolute positive lower bound on 𝔖(m) for every even m, while 𝔖(N)≪log log(3N): factor off the convergent twin-prime product and use (p−1)/(p−2)=[p/(p−1)]·[1+1/(p(p−2))] for odd p|N and the standard totient bound. Thus for H=floor(ηN),
$$
 \sum_{1\le |h|\le H}|\omega(h)|\ll_f \log\log(3N).                     \tag{2}
$$
Upper bounds are not needed for the off-target model values.

Let M_R be the union of arcs of radii at most 2R/(qN) about all reduced fractions a/q with q≤R; its length is O(R²/N), number of components O(R²). Apply (1) to μ, the pushforward of λ_N by α↦2α mod 1, and E=2M_R, with the same bounds up to constants. Its nonzero moments in the window satisfy (2), and |μ|≤(doubling)_*|λ_N|. The bound
$$
 |\lambda_N|(\mathbb T\setminus\mathfrak M_R)
 + C_f\exp\big(-c_f N/(R^2\log\log(3N))\big)\,\|\lambda_N\|_{TV}\;\ge\;3/4             \tag{3}
$$
follows for R≤N^(1/2−ε) and all sufficiently large N, for every fixed ε>0. In this step the exponential term is deliberately charged to the ENTIRE norm, since the inverse image of the doubled major arcs can also include points outside M_R. A slightly sharper bound charges just those two half-circle translates. In particular even a signed multiplier, allowed to depend on N and with polynomial total variation, retains order-one absolute mass on the true minor arcs. A fortiori a measure entirely on the major arcs with the two certificate properties has exponentially large norm on this scale. Equation (3) is about the multiplier, not about the actual integral weighted by S²: concentration at small values of S or cancellation in its phase remains possible.

Algebraic existence is very different. In any nonempty arc and for any finite integer H there **is** a finite signed, even measure (on the arc and its reflected arc if necessary) with zeroth moment 1 and all moments through H zero: use any H+1 distinct cosine values in a subarc, and interpolate the constant Fourier coefficient on the basis 1, cos(2πα),…,cos(2πHα) by real Vandermonde inversion, symmetrizing the atoms. Increasing H to include every even coefficient in the live convolution model gives exact target extraction supported on a small symmetric major arc. Inequality (3) explains why finite-dimensional interpolation alone cannot be combined with polynomial-precision bounds via absolute errors. For general (asymmetric) supports without symmetrization one may instead use complex exponential Vandermonde interpolation.

## Relation to published estimates and scope

Bhowmik–Grimmelt, [arXiv:2607.27282v2, §7](https://arxiv.org/html/2607.27282v2#S7), smooth the rational major arcs in an averaged explicit formula. Althöfer–Chen–Perelli–Pintz, [arXiv:2611.09386v1, (4.2)–(4.4)](https://arxiv.org/html/2611.09386v1#S4), use a sum over exceptional polynomial values and a restriction-moment bound, not a lower-bounding multiplier at a single index; their Theorem A is the externally supplied 7/8 zero-free claim. Neither result is contradicted here. [Pintz–Althöfer](https://arxiv.org/html/2610.15559v1) likewise counts exceptions. A flat frequency passband such as [the elementary comparison](https://github.com/mxym/math/blob/main/research/theory-2026-11-20/strong-goldbach/FlatPassbandMajorArcs.md) does not have all the off-target sign guarantees stipulated above. The present construction is related to classical Fourier extrapolation/uncertainty (e.g. [Donoho, 1992](https://doi.org/10.1137/0523074)); it gives a self-contained finite-window barrier tailored to the actual positive local singular-series model. No claim that general Fourier extrapolation is new is being made. We neither approximate each prime coefficient by its model nor conclude anything about the truth of Goldbach.

[Bhattacharjee v1, §13](https://www.researchgate.net/publication/405207567_Goldbach_Representations) identifies leakage from neighboring positive count coefficients when the Fejér-smoothed count is positive. Here the off-target weights are already nonpositive; the conclusion is instead on the absolute variation of the signed frequency measure outside the rational arcs. [Bahboui v1](https://www.preprints.org/manuscript/202610.2486) likewise leaves a distinct fixed-target arithmetic barrier. The comparison is limited to these stated results.
