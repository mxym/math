# Centering the divisor switch: an O(N/B) pointwise tail

**Scope.** This note improves the **same-scale** logarithmic overlap in the Huang–Li conditional estimate. Its new estimate of the discarded arithmetic sum is **unconditional for each target**, and uses real primes. Neither the ordinary distribution estimate beyond its known ranges nor its Möbius-twisted counterpart is proved here. Source numbering refers to [Huang–Li v2](https://arxiv.org/html/2005.03811v2). Denote by L=log N, θ∈(0,1) fixed and α=N^θ. The paper's EH(Q), EH_μ(Q') mean its prefix-uniform distribution assertions, with arbitrarily large fixed logarithmic savings, at the indicated ranges. Use the same S(N), D(N) as in SharpPointwiseSquarefreeMargin.md.

**Theorem.** For B≥2 growing at most as a fixed power of L, assume EH(αB²) and EH_μ(N/α). For each fixed A>0 the *ordered log-weighted prime-pair count* R(N) satisfies

    R(N)=S(N)[N−T(N)] + O_θ(N/B) + O_{θ,A}(N/L^A),                 (1)
    T(N)=Σ_{n<N} Λ(n) μ(N−n).

Constants in the arbitrarily logarithmically small error may also depend on the fixed upper power for B and the implicit constants in the assumed distribution estimates. The constant in O_θ(N/B) is independent of B,N and of those conjectural constants. Thus B=L h(N), with h→∞ arbitrarily slowly and polylog-bounded, yields R(N)≥(exp(γ)−o(1)) N/L for every sufficiently large even N under these hypotheses. In particular EH(N^θ L^(2+ε)) and EH_μ(N^(1−θ)) suffice for any fixed ε>0, rather than the L^(12+ε) ordinary modulus factor in their Corollary 1. Mere eventual positivity needs only B=C_θ L for a sufficiently large constant. This is an improvement to the **same-scale modulus/precision tradeoff**, not a logically weaker global ordinary EH conjecture. In fact global prefix-uniform EH(x^θ) with arbitrarily large log savings already implies its estimate at q≤N^θ L^C for any fixed C: apply it at x=N L^((C+1)/θ) and increase the requested savings exponent by more than (C+1)/θ. This change of scale does not work for the twisted hypothesis (the sequence itself depends on N), nor does it turn the classical Bombieri–Vinogradov theorem into exact-endpoint EH(√N). The point here is the proved O(N/B) actual-prime tail and the corresponding inputs needed *at this N*. No power improvement or unconditional prime-pair lower bound is claimed.

## 1. Recenter before making the cut

For m>1, Λ(m)=Σ_{d|m}μ(d)log(α/d); this adds log α times the zero sum of μ over the divisors. For m=1 there is an artificial log α term and we remove it at cost O(L²). Insert μ²(m) and split d≤α from d>α. Using the log prime weight ϑ(n)=(log n)1_{n prime} on the first side and Λ on the second side changes the original count by at most N^(1/2+o(1)): there are O(sqrt(N)L) proper prime powers available on either side, each relevant truncated divisor sum is O(τ(m)L), and τ(m)=N^o(1) uniformly for 1≤m≤N. Write the resulting two pieces as S1 and S2.

For S1, expand μ²(m)=Σ_{b²|m}μ(b). All nonzero b,d are squarefree. Put g=(b,d), h=d/g; then g|b, (h,b)=1, [b²,d]=b²h=:z, and μ(d)=μ(g)μ(h). Every term is an actual-prime progression sum Θ(z)=Σ_{p<N,p≡N mod z}log p. Terms having (z,N)>1 contribute at most N^o(1) in total: such a prime divides N, and for each p|N the numbers of eligible d and b divide-counts are bounded by τ(N−p)². We henceforth retain only coprime moduli. The model for Θ(z) is N/φ(z).

**Truncation lemma.** In S1, discard the terms with **z>αB²**. The absolute sum after discarding their Möbius signs is O_θ(N/B)+O_θ(N^(1−c)L^5) for c=(1−θ)/4. This also holds, with just O(N/B), for the analogous sum replacing Θ(z) by N/φ(z) and taking all b≥1 in that model.

**Proof.** On the discarded region we necessarily have

    b>B,       g≤(b/B)²,       α B²/b² < h ≤ α/g,
    0≤log(α/(gh)) ≤ 2 log(b/B).                                     (2)

For b≤N^c, z≤b²α≤N^((1+θ)/2). The classical Brun–Titchmarsh inequality therefore gives Θ(z)≪_θ N/φ(z), uniformly for the reduced class. Thus this part is bounded by the model with positive terms. The model uses φ(z)=bφ(b)φ(h). Divide b into 2^j B<b≤2^(j+1)B, writing H=2^j B. Then g≤4^(j+1). For each such g,b the admissible h have endpoint ratio ≤4^(j+1) (even when the lower endpoint is <1), so

    Σ_{admissible h} log(α/(gh))/φ(h) ≪ (j+1)².

This follows by dyadic subdivision, since Σ_{u<h≤2u}1/φ(h)≪1 for u≥1; if the lower endpoint is <1, begin at 1 and include h=1. The dyadic bound follows from Σ_{n≤x} n/φ(n)≪x, itself immediate by expanding n/φ(n)=Σ_{r|n} μ²(r)/φ(r) and summing Σ_r 1/(rφ(r))<∞.

For each g, among squarefree b divisible by g, write b=gv, (g,v)=1. The dyadic estimate just given also implies

    Σ_{H<b≤2H,g|b,squarefree} 1/(bφ(b))
       ≤ [1/(gφ(g))] Σ_{H/g<v≤2H/g}1/(vφ(v)) ≪ 1/(Hφ(g)).

For H/g<1/2 there is no term; for 1/2≤H/g<1 the sole possibility v=1 obeys the same bound. Finally Σ_{g≤4^(j+1)}1/φ(g)≪j+1. Hence the jth contribution to the positive model is O(N(j+1)^3/(2^j B)). Summing proves O(N/B) for *all* b in the model and for b≤N^c in the actual sum.

For actual b>N^c we have z<N whenever Θ(z)≠0, since N−p is a positive multiple of z. Thus Θ(z)≤2NL/z. Ignore (2), take h≤α, g|b, and bound the centered log by L. This part is at most

    2NL² Σ_{b>N^c} τ(b)/b² · Σ_{h≤α}1/h ≪_θ N^(1−c)L^4,

using the elementary divisor mean bound. This finishes the lemma. The savings come from (2); bounding the centered weight by L near the boundary, or truncating in b alone, loses them.

## 2. Completing the small-divisor part

For the retained z≤αB² the EH(αB²) assumption supplies the usual weighted progression replacement with arbitrary log saving. Details: group by z, with absolute coefficient at most L τ₃(z) (as in Huang–Li §3.1). Use their weighted Cauchy–Schwarz estimate from (16), restricted to these moduli: for (z,N)=1 the progression error is ≪NL/z in this polylog-extended range, and Σ_{z≤N}τ₃(z)²/z≪L^9. Thus a power saving of arbitrary fixed order in the unweighted *sum of absolute errors* gives the same with this coefficient after increasing the requested log exponent. One may use the Λ-progression version of EH directly: the total increase on the retained arithmetic side when replacing θ by Λ is O(N^(1/2+o(1))) by counting divisors for each proper prime power as in §1. The noncoprime classes are still omitted. Endpoint p<N instead of ≤N is harmless here for even N; or apply the maximal form and absorb the O(1/φ(z)) differences summed with the divisor weights.

After replacement, use the **model** half of the truncation lemma to extend back to all b with (bd,N)=1, with error O(N/B). The full model is

    N A(N) Σ_{d≤α,(d,N)=1} μ(d)g_N(d) log(α/d)/φ(d),
    g_N(d)=∏_{p|d}(p−1)²/(p²−p−1)    for (d,N)=1.

Indeed this is the Euler factorization of the b-sum in Huang–Li Lemma 3; at p∤Nd the factor is 1−1/[p(p−1)], and at p|d it is 1−1/p after factoring out 1/φ(d), giving g_N. For avoidance of ambiguity, at p|d the local factor is **1−1/p** because φ(p)/[pφ(p)]=1/p.

Their Lemma 2 gives Σ_{d≤R} c_N(d)log(1/d)=S(N)/A(N)+O_θ(exp(−c_θ sqrt(log R))) for R≥N^θ, with c_N(d)=1_{(d,N)=1} μ(d)g_N(d)/φ(d). The term newly added by centering, (log α)Σ_{d≤α}c_N(d), is also super-logarithmically small. To verify this, for fixed N first note the unweighted series converges by partial summation from that lemma. Its Abel value is zero: the Euler product for Σ c_N(d)d^(−s) has a simple zero at s=0, as in the proof of their Lemma 2 (a nonzero analytic factor times 1/ζ(1+s)). Abel continuity then gives Σ_{d≥1}c_N(d)=0. Partial summation on the tail α<d≤R, subtracting the constant limit S/A of the log-weighted sums, followed by R→∞, gives |Σ_{d>α}c_N(d)|≪_θ exp(−c'_θ sqrt(L))/log α. These estimates prove

    S1 = NS(N)+O_θ(N/B)+O_{θ,A}(N/L^A).                             (3)

## 3. Complementary part with the triangular endpoint retained

Put ρ(n)=Λ(n)μ(N−n). Divisor complement on squarefree m=N−n gives exactly

    S2 = Σ_{k<N/α} μ(k) Σ_{n<N−αk, n≡N mod k}
                         ρ(n) log(αk/(N−n)).

This retains the moving upper bound n<N−αk, dropped in the last printed line of Huang–Li v2 (18). It is the direct equivalent of k<(N−n)/α; dropping it as a formal equality is not justified. At equality the centered logarithm is zero, so rounding endpoints does not change the sum. For (k,N)>1, n must be a prime power of a divisor of N; summing its τ(N−n) possible k gives N^o(1). For the remaining k, the bounded-variation log weight on this prefix has supremum and total variation ≤L. Partial summation plus EH_μ(N/α) therefore replaces the progression sum by 1/φ(k) times the full ρ-prefix with *the identical endpoint and logarithmic weight*, with aggregate error O_A(N/L^A).

Reverse the resulting finite sums. The factor multiplying ρ(n) is

    −Σ_{k<R,(k,N)=1} μ(k)log(R/k)/φ(k),       R=(N−n)/α.

For N−n≥N^((1+θ)/2) we have R≥N^((1−θ)/2); Huang–Li Lemma 1 gives this factor as −S(N)+O_θ(exp(−c_θ sqrt(L))). The strict/weak endpoint difference vanishes due to log(R/k). For the shorter segment the factor is O(L²) trivially (empty if R≤1), and the total cost of using −S(N) instead is O_θ(N^((1+θ)/2)L³). Thus S2=−S(N)T(N)+O_{θ,A}(N/L^A). Together with (3) this proves (1). This repair uses the maximal endpoint in their *stated* twisted hypothesis, not a stronger conjecture. Related parallel formal work [TamakoHe/GoldbachResearch](https://github.com/TamakoHe/GoldbachResearch) also retains exact cutoff endpoints and identifies unresolved twisted errors; we do not claim priority for noticing that dependence.

## Remaining barrier

The O(N/B) tail lemma is unconditional for all large even targets; the distribution replacement in §2 and especially §3 is not. Combined with the pointwise squarefree margin, the result quantifies how much room a proof of those remaining errors actually needs. It neither supplies cancellation for the twisted progression discrepancies nor proves an all-even Goldbach theorem.

**Prior work on the moving endpoint.** [Ramón Moya's 14 August 2026 preprint](https://doi.org/10.5281/zenodo.21939906) had already identified the missing moving endpoint in Huang–Li (18), given a finite counterexample to the printed equality, and repaired the argument under the original prefix-uniform hypothesis. The different result here is the centered arithmetic tail estimate, not that correction.
