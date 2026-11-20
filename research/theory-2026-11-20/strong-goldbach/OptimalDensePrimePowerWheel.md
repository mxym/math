# An optimal-size even prime-power mask losing arbitrarily little local Goldbach mass

**Status.** This gives a prime-only version of the positivity test motivated by [Li–Liu](https://mrc.sdu.edu.cn/english/info/1018/1514.htm), not a Goldbach proof or an estimate of the missing prime correlation.

Fix any δ in (0,1) and ε>0. For every sufficiently large even N, put L=log N. One can effectively construct a squarefree modulus W and a 0–1 mask M on its residue classes such that:

- log W ≍_{δ,ε} √L; M is even, is supported on units, and excludes every actual proper prime power p^j≤N.
- Write B_W(N) for the number of residues a mod W with both a,N−a units. Then the mask retains at least (1−δ)B_W(N) choices, uniformly in N, including targets divisible by one or more of the test primes.
- The multiplicative Fourier expansion M=Σ_ψ c_ψψ involves only even Dirichlet characters, with Σ|c_ψ|≤exp(ε√L) for all sufficiently large N.
- Conversely any nonempty periodic unit mask rejecting all proper prime powers ≤N must have log W≫√L, regardless of its target dependence, parity or retained mass. This proof assumes exclusion on all of [1,N]. See the [central-window addendum](CentralWindowWheelObstruction.md) for the matching lower bound even when the mask is required to work only in one central interval of length at least `N exp(−D sqrt(log N))`.

There is also an optional signed lower-count variant using only O(√L/log L) total one-factor Fourier cost, with an explicit finite high-power correction (§5).

## 1. A product of nonpower *blocks* for low exponents

Choose a fixed integer d≥2 depending on δ, and fixed C₀≥3 depending also on ε. Put K=ceil(C₀√L). Choose a prime t in [2(14+dK),4(14+dK)] by Bertrand. For each prime exponent k≤K choose d test primes ℓ_{k,i}, i=1,…,d. To make these distinct, assign distinct integers j_{k,i} in [14,13+dK] and choose the least prime in the following CRT class:
    ℓ_{k,i}≡j_{k,i} mod t;
    ℓ_{k,i}≡1 mod k for k odd, and ℓ_{2,i}≡1 mod 4.
All CRT classes are reduced, t>K, and j_{k,i}>13 implies ℓ_{k,i}>13 (any smaller prime would equal its least residue mod t). The ℓ_{k,i} are distinct by their residues. [Linnik's theorem](https://arxiv.org/abs/0906.2749) gives ℓ_{k,i}≤K^{O_d(1)} with an effective upper bound. For odd k the prime is at least k+1. Hence
    W=2 ∏_{k≤K,k prime} W_k,    W_k=∏_{i=1}^d ℓ_{k,i},
    dΣ_{3≤k≤K,k prime}log k ≤ log W ≪_d π(K)log K.
Thus log W ≍_d K. At 2 use the unit indicator. In the unit group modulo W_k, let H_k be the subgroup consisting of classes which are kth powers at **all d** test primes. Retain the complement of H_k within the units, and multiply the block masks to obtain M₀. Since −1 is a kth power at every tested prime (automatic for odd k, and ensured by ℓ≡1 mod 4 for k=2), each block mask and M₀ are even. If an exponent j≥2 has a prime divisor k≤K, an integer-base power b^j is either a nonunit or is in H_k, hence is rejected. This is simultaneous exclusion for composite exponents too.

At a test prime ℓ define b_ℓ(N)=ℓ−ν_ℓ(N), where ν_ℓ(N)=1 if ℓ|N and 2 otherwise. This is the exact ordinary count of units a,N−a mod ℓ. It includes b₂=1 at every even target. In block k the count of locally admissible unit pairs is B_k=∏_{i=1}^d b_{ℓ_{k,i}}. The subgroup has cardinality
    |H_k|=k^(−d) ∏_{i=1}^d (ℓ_{k,i}−1).
At most |H_k| residues are lost by each argument's restriction, even if N is divisible by test primes. The relative loss is therefore bounded by
    2|H_k|/B_k
      = 2k^(−d)∏_{i=1}^d (ℓ_{k,i}−1)/(ℓ_{k,i}−ν_{ℓ_{k,i}})
      ≤ 2(13/(12k))^d.
The factor for a test prime dividing N is one, not (ℓ−1)/(ℓ−2). Since
    Σ_{k≥2, k prime} 2(13/(12k))^d
      ≤ 2(13/24)^d [1+2/(d−1)],
choose d so this is <δ/2. CRT and the elementary product lower bound Π(1−u_i)≥1−Σu_i give
    A₀:= #{a mod W: M₀(a)M₀(N−a)=1} ≥ (1−δ/2) B_W,
    B_W:= ∏_{ℓ|W} b_ℓ(N).
In particular A₀≫W/(log K)^2: the latter lower bound on B_W follows by comparison of b_ℓ/ℓ with 1−2/ℓ at the odd primes, Mertens, and the bound K^{O_d(1)} for all test primes. The prime 2 costs 1/2. Using several tests per exponent instead of rejecting a kth power at any one test is what improves the local retention from a diminishing factor to an arbitrarily large fixed fraction.

## 2. High powers and singular-series normalization

Enumerate the residues of all integer-base powers b^j≤N with b≥2 and j>K and their negatives. Let E consist only of those listed residues still retained by M₀. This choice guarantees M=M₀−1_E is a nonnegative 0–1 mask. It is even and is supported on units. All proper prime powers are rejected. The number of deleted classes is bounded by
    |E| ≤ 2 floor(log₂ N) N^(1/(K+1))
         ≤ exp((C₀^(−1)+o(1))√L).
Since W≥exp(d K/2) for large K, at most 2|E| pair residues are lost and 2|E|=o(B_W). Thus A_W, the final number of allowed pair residues, is ≥(1−δ)B_W for all large even N. The pair set is reflection-invariant because the two copies of M are the same.

All counts are effective without enumerating residues modulo the whole wheel. Compute A₀ by multiplying the finite block counts; each block has size K^{O_d(1)}. Set e_N=#{a∈E:M₀(N−a)=1} and d_N=#{a∈E:N−a∈E}; then A_W=A₀−2e_N+d_N. The finite high-power list needs no knowledge about prime bases. The ordinary local normalized prime-product mass at a prime ℓ is b_ℓ/[ℓ(1−1/ℓ)^2]. For the grouped wheel the adjusted local singular prediction is exactly
    S_W(N)=S(N) A_W/B_W ≥ (1−δ) S(N).
This exact combinatorial normalization does not assert that the prime count has its predicted size. After the finite high-power deletion the mask need not factor across W_k, so the adjustment is the single ratio A_W/B_W.

## 3. Even character expansion and exact prime-only projection

On units of W_k the indicator of H_k is the average of the k^d characters of the quotient, extended by zero to nonunits. The block complement has coefficient ℓ¹ norm 2(1−k^(−d))≤2. Since −1 belongs to H_k, all those characters are even. Therefore the full product M₀ has ℓ¹ cost at most 2^π(K). The even indicator 1_E has squared coefficient ℓ² norm |E|/φ(W) by Parseval and hence ℓ¹ cost ≤√|E| by Cauchy–Schwarz. Consequently the one-argument expansion M=Σ_ψ c_ψψ obeys
    Σ|c_ψ|≤2^π(K)+√|E|≤exp((1/(2C₀)+o(1))√L).
Take C₀ large enough in terms of ε. A direct product expansion at two arguments costs at most the square of this bound.

For real f,g smoothly supported in a fixed (a,1−a)⊂(0,1), define
    P_{χ,f}^M = N^(−1/2) Σ_n Λ(n)χ(n)M(n)f(n/N),
    D_M(f,g) = N^(−1) Σ_{(n,N)=1} Λ(n)^2 M(n)^2 f(n/N)g(n/N).
The exact odd-character projection is
    D_M(f,g) − [2/φ(N)]Σ_{χ mod N, χ odd} P_{χ,f}^M overline(P_{χ,g}^M)
      = N^(−1) Σ_{p+q=N; p,q distinct primes}
                           (log p)(log q) M(p)M(q)f(p/N)g(q/N).
On the support, equality or reflection modulo N forces n=m or n+m=N, respectively. The mask removes every proper power up to N. The omitted equal-prime case N=2p already provides a Goldbach representation. Thus strictly positive value of the left at f=g≥0 certifies an actual prime pair with **zero** prime-power contamination, even at the scale of a single pair. The restricted test is sufficient but not necessary because real prime pairs may lie in excluded classes.

The character expansion P_{χ,f}^M=Σ_ψ c_ψ P_{χψ,f} is exact with products induced to lcm(N,W), including overlaps of test primes with N. Since χ is odd and each ψ even, no product is principal. Its analytic use would require information about the zeros for these products and the mixed character moments, still averaging χ modulo N, not lcm(N,W). This is not the original T_lcm, and neither the subpower modulus nor the Fourier bound alone estimates the discrepancy required for Goldbach.

## 4. Matching lower bound for periodic exclusion of actual powers

Let an arbitrary nonempty unit mask modulo W reject every p^j≤N with prime base p and exponent j≥2. The mask may depend on N. Fix an accepted reduced class a. Linnik gives a bound CW^A on the least prime in any reduced class mod W, with effective absolute C,A. Set T=floor(log N/log(CW^A)). If some prime k≤T does not divide φ(W), exponentiation by k is a bijection on the unit group. The kth root of a therefore contains a prime p≤CW^A. Then p^k≤N lies in the accepted class, contradiction. Hence every prime k≤T divides φ(W) and
    log W≥log φ(W)≥Σ_{k≤T,k prime} log k.
For large T this is ≫T by Chebyshev, giving (log W)^2≫log N after handling the additive log C and floor. For bounded T, log W≫log N directly from the formula for T for all sufficiently large N. Bounded W is in particular impossible eventually. This proves the same order log W≈√log N for exact periodic elimination of actual powers up to N, without hypotheses of evenness or local-density preservation.

For comparison, the **usual** unfiltered higher-power correction already has normalized weighted size O(log N/√N): the squares carry total von Mangoldt weight θ(√N)≪√N, all higher exponents contribute O(N^(1/3)log N), and the unique partner costs at most log N. This is even o(Li–Liu's R error scale), but remains much bigger than a single pair. The wheel is targeted at the latter regime.

## 5. Optional signed lower count with only polynomial Fourier cost

For applications that can use a lower count instead of an exact positive mask, an elementary alternative avoids the product Fourier cost. Let U be the indicator of units modulo W and let H_k(n) here mean membership in the block subgroup. On n+m=N use the real signed weight
    L_*(n,m)=U(n)U(m) [1−Σ_{k≤K, k prime}(H_k(n)+H_k(m))].
For any pair with at least one *low-power* argument, i.e. a prime power p^j with j≥2 divisible by a prime k≤K, the weight is ≤0. For both arguments prime the weight is always ≤1. The same union estimate on the unit pair residues shows its total signed local mass is ≥(1−δ/2)B_W, so its local normalization is again at least (1−δ/2)S(N).

To avoid all other prime powers **exactly**, subtract the contribution to the von Mangoldt-weighted count with L_* from the finite set of ordered pairs n+m=N for which either argument is a proper prime power with some exponent j>K (use a union, not counting a pair twice). Their set can be enumerated from the high-power list; to compute each correction one determines Λ of the unique complement by exact integer roots and primality tests. Put smooth nonnegative cutoffs on both arguments throughout. If implementing the statistic by the odd-character projection of §3, restrict both the projected count and this correction to (nm,N)=1; the excluded equal-prime case is already a representation. After this subtraction all still-present prime-power-contaminated terms are nonpositive, and genuine-prime terms are bounded above by their true weights. Therefore this signed statistic is a rigorous **lower bound** for the true-prime pair count. The subtraction need not be approximated by a larger error; in normalized log weights it is at most N^(−1+o(1)) but need not be ignored in a microscopic sign test.

Each argument function U or U·1_{H_k} is an even-character expansion of ℓ¹ norm one. Write the signed projected expression linearly in pairs of arguments:
    U⊗U − Σ_k [(U1_{H_k})⊗U + U⊗(U1_{H_k})].
The total coefficient ℓ¹ cost in this expansion is at most 1+2π(K)=O_{δ,ε}(√L/log L), not exponential. Unlike M this is not a nonnegative prime-only mask and may undershoot even an existing true pair; the assertion is only that a strictly positive corrected lower count certifies genuine primes. No positive lower bound for that count is obtained here.

Run `python3 -O check_dense_wheel.py` for a full finite differential test of the block and deletion counts, including targets divisible by test primes. The asymptotic conclusions use the analytic argument above.

For an exponentially shrinking loss rather than fixed δ, see the [sharp size–retention tradeoff](DenseWheelPrecisionBarrier.md).
