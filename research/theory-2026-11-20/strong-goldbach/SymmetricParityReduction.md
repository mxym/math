# The symmetric center and a one-sided rough parity residual

Set L=log N, ε>0 fixed, η=3/2−√2. For any fixed 0<δ<1 and 0<κ<η(1−δ), write y=exp(L^δ) and K(m)=Σ_{k|m} μ(k)min(0,log(k/√m)). For every sufficiently large even N one has unconditionally

    R(N)/2 = N S(N) + Σ_{m<N, P⁻(m)>y, μ(m)=1} Λ(N−m) K(m)
                    + O_{δ,κ}(N/L^κ).                                 (1)

Here R counts ordered prime pairs with their log weights. The m=1 term is zero. The displayed sum may be negative of main-term size; (1) by itself is not a Goldbach lower bound. For **two** distinct prime factors, K(m)=−log P⁻(m); for **four**, K(m)≥0 and is an explicit interval-overlap length. Thus the only negative contributions in (1) are from rough semiprimes and possibly rough even Ω≥6. Every squarefree composite of odd Ω drops out exactly.

## 1. Rigorous change from fixed to pointwise center

Use U_A(m)=Σ_{d|m,d≤A} μ(d)log(A/d). Choose a fixed large D and A=√N/L^D as in GlobalRoughLocalization.md so the known ordinary BV theorem evaluates the small side Σ Λ(N−m)μ²(m)U_A(m)=NS(N)+O(N/L²); proper powers can be replaced by prime weights throughout at N^(1/2+o(1)). One may choose D larger than 20. All terms m<A²=N/L^(2D) cost O(N/L^(2D−3)) even after changing the center: use Σ_{m≤x}τ(m)≪x log(2x) and two log weights. For m≥A²,

    U_{√m}(m)−U_A(m)
      = ∫_{log A}^{(log m)/2} [Σ_{d|m,d≤A} μ(d)
                               +Σ_{d|m,A<d≤exp(v)} μ(d)] dv.          (2)

The integral length is at most Dℓ, ℓ=log L. The second term contributes O(N/L^κ) under the prime weight and μ²(m) by InteriorMobiusPrimitive.md, applied uniformly in v and then integrated; the extra condition m≥exp(2v) is a bounded complement-only mask.

For transparency, the first term uses an **ordinary unsigned-prime progression replacement**, not an unproved Möbius-twisted estimate. For any prefix p≤x<N, the small side without its log divisor weight satisfies

    Σ_{p≤x} (log p) μ²(N−p) Σ_{d|N−p,d≤A} μ(d)
       = x A(N) Σ_{d≤A,(d,N)=1} μ(d)g_N(d)/φ(d)+O(N/L²),
                                                                         (3)

uniformly in x, by the same elementary b² expansion as CenteredDivisorSwitch.md §§1–2, with B=L². Details of differences: on the discarded z=b²h>AB², the available h ratio ≤4^(j+1) supplies O(j+1) for Σ1/φ(h) without a log, no bigger than the previous O((j+1)²); actual nonnegative prefix counts are at most their full-interval counts in the Brun–Titchmarsh majorant. The term b>N^c only decreases. After ordinary BV on z≤AB², with x in its standard prefix maximum, extend the Euler model back to all b using the same positive tail. For reduced classes the prime-power correction summed over b,d is N^(1/2+o(1)); nonreduced actual prime classes contribute N^o(1) as before. The unweighted d sum in (3) is superlog-small by the Abel/partial-summation deduction from Huang–Li Lemma 2 in CenteredDivisorSwitch.md; A(N) there is the squarefree product, not the cutoff A. Since each integrand for m≥exp(2v) is a prime prefix (an endpoint rounding costs at most N^o(1)), (3) contributes O(Nℓ/L²) to (2). We have therefore unconditionally evaluated the **symmetric** small side:

    Σ_{m<N} Λ(N−m)μ²(m)U_{√m}(m) = NS(N)+O(N/L^κ).                    (4)

## 2. Odd parity vanishes locally and the symmetric rough filter applies

For m>1 squarefree, the divisor identity and complementation at √m give exactly

    Λ(m)=U_{√m}(m)+μ(m)K(m),                 K(m)=−U_{√m}(m).

The second equality follows directly from the definitions. Thus when μ(m)=−1 we have K(m)=−Λ(m)/2: zero for composite m, and −(log m)/2 for primes. If μ(m)=1 and m>1, then Λ(m)=0 but its small side and its large side need not vanish separately.

The proof of GlobalRoughLocalization.md as iterated in RoughLayerIteration.md §1 allows θ=(log m)/2 and discards P⁻(m)≤y in the signed large side with L¹ cost O(N/L^κ); small m was already bounded trivially. For prime m≤y one could also estimate its total log weight directly by N^o(1). The contribution of μ(m)=−1 to the large side is exactly R/2, after the negligible proper prime powers of n=N−m. Summing the exact identity, using (4), and bringing R/2 to the left proves (1).

## 3. Exact signs at two and four prime factors

Let m have 2s≥2 distinct prime factors r_i and a_i=(log r_i)/2. Since Σ_{d|m}μ(d)log(d/√m)=0, K(m)=−½Σ μ(d)|log(d/√m)|. The classical integral for |x| and elementary finite factorization give

    K(m) = [(-1)^s 2^(2s)/π] ∫₀^∞ ∏_{i=1}^{2s} sin(a_i t) dt/t².

Indeed Σ μ(d) exp(it log(d/√m))=∏(e^(−ia_it)−e^(ia_it)). For two factors, direct divisor enumeration (or the sine integral) gives −2min(a₁,a₂)=−log P⁻(m). For four, the identity

    ∫_{|a−b|}^{a+b} sin(tx) dx = 2sin(at)sin(bt)/t

and sine-transform Plancherel give

    K(m)=2 · length([|a₁−a₂|,a₁+a₂] ∩ [|a₃−a₄|,a₃+a₄]) ≥0.

No sign assertion is made for arbitrary larger even Ω. Therefore a sufficient genuinely one-sided bound is that, with a fixed positive margin on the NS(N) scale, the total of Λ(N−m)log P⁻(m) over y-rough semiprimes plus the total of Λ(N−m)max(−K(m),0) over y-rough even Ω≥6 be smaller than NS(N). This discards positive terms, including all four-factor weights; the bound is not established and may be stronger than necessary. Keeping the positive four-factor contribution on the other side gives a weaker target directly from (1).
