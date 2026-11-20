# Sharp size–retention tradeoff for exact periodic prime-power exclusion

**Status.** This is a quantitative barrier to decreasing the lost mass of a nonnegative periodic mask, with matching constructions. It uses the distribution of actual primes in short progressions. It neither supplies nor obstructs a pointwise prime–prime correlation estimate, and it does not apply to the separate signed statistic with explicit high-power subtraction.

Fix 0<α<1/2, D>0, and 0<b<1. For large even N put L=log N, E=Lᵇ and δ=exp(−E). Consider an interval I=(U,V] contained in [αN,(1−α)N] with |I|≥N exp(−D√L). Let M be a 0–1 mask supported on units modulo W. Denote by B_W the number of classes a mod W with a,N−a both units, and A_W the number for which M(a)M(N−a)=1. Suppose B_W>0, A_W≥(1−δ)B_W, and M rejects every actual proper prime power pʲ in I. Then
    log W ≫_{α,D} max(√L, √(LE/log L)).
Conversely, there is an explicitly constructible even 0–1 mask as above which rejects all proper prime powers up to N, retains (1−δ) of the local unit-pair mass at every even target N, and has
    log W ≪_b √(LE/log L).
In particular this order of log W is optimal for the stated shrinking δ. Lower and upper constants are effective. The lower proof below gives the same estimate for arbitrary 0<E=log(1/δ)≤L log L; beyond that it gives the case distinction in §2.

## 1. An entire power image is forced to be rejected

Let q=2W, P=log q, and Γ=log(V/|I|). By the argument of [CentralWindowWheelObstruction.md](CentralWindowWheelObstruction.md) (using [Thorner–Zaman, Theorem 1.1](https://arxiv.org/pdf/2108.10878v2)), for every prime
    k ≤ T=floor(c L/(P+Γ+log L))
with fixed sufficiently small effective c, every unit class modulo q contains a prime in (U^(1/k),V^(1/k)]. Therefore *every* member of the image H_k={uᵏ:u unit mod W} has a representative pᵏ∈I. Indeed, lift any root u modulo W to a reduced class modulo q. Exact rejection of the actual powers thus implies M(a)=0 on all of H_k. The same short-progression argument gives P≫_{α,D}√L from nonemptiness alone.

## 2. Small pair loss forces many copies in the totient

For an odd prime k≤T write W as a product of exact prime powers ℓʳ. CRT gives a local ratio for the fraction of admissible unit pairs with first argument in H_k. If k does not divide φ(ℓʳ), the k-th power map is onto, and the ratio is one. The other local factors are:

- If ℓ=k and r≥2, the image of the map on the cyclic group of units mod kʳ has index k. The image reduces onto every nonzero class mod k and the fibers of this reduction have equal size. The condition that N−a be a unit depends only on the reduction mod k. The resulting ratio is exactly 1/k.
- If ℓ≡1 mod k, then ℓ≥2k+1, since ℓ and k are odd and ℓ=1+mk requires m even. The image mod ℓ has (ℓ−1)/k≥2 classes. All of their lifts are in the image mod ℓʳ, since raising to the k-th power bijects the kernel of reduction. At most one of the image classes is excluded by N−a being a nonunit. Thus if ℓ∤N the ratio is at least [(ℓ−1)/k−1]/(ℓ−2)≥1/(2k). If ℓ|N it is exactly 1/k. The prime 2 contributes no restriction for odd k.

Put s_k=#{ℓʳ∥W : k divides φ(ℓʳ)}. Since any admissible residue whose first entry is in H_k is lost, CRT gives
    δ ≥ (2k)^(−s_k) ≥ (2k)^(−v_k(φ(W))).
Hence v_k(φ(W)) log k ≥ E log k/log(2k) ≥ (log 3/log 6)E. Summing over odd primes k≤T yields
    P ≥ log φ(W) ≫ E π(T)                (T sufficiently large).
Since Γ≤D√L and P≫_{α,D}√L, the denominator in T is O_{α,D}(P); for large T, T≫_{α,D}L/P. Chebyshev then gives P²≫_{α,D}EL/log L. If T is bounded, the denominator is ≫L, so P≫L. In the stated range E=Lᵇ the desired bound is automatic in this case. For arbitrary E more generally one should retain the inequality P≫Eπ(T) for large T and the bound P≫L when T is bounded; there is no universal bound beyond L from these arguments. Since P→∞, replacing P by log W does not change the assertions.

The loss lower bound here does not use the exceptional delicate square block k=2. If the modulus contains 3 and N≡1 mod 3, there are no admissible unit pairs whose first entry is a square modulo 3. Odd prime k avoid that case through ℓ≥2k+1.

## 3. Matching upper construction

Adapt the simultaneous power-block construction in [OptimalDensePrimePowerWheel.md](OptimalDensePrimePowerWheel.md). For large fixed C>0, set
    K=ceil(C √(L log L/E)),
    d_k=ceil((E+2log k+log 20)/log(12k/13))      (prime k≤K).
At each exponent use d_k distinct test primes ℓ>13 with ℓ≡1 mod k (ℓ≡1 mod 4 at k=2), all tests globally distinct. As in the companion note, choose one auxiliary prime t>max(K,13+Σd_k) of comparable size and assign every test a distinct reduced residue from 14 through 13+Σd_k modulo t. CRT and [Linnik](https://arxiv.org/abs/0906.2749) give each test prime ≤L^{O_b(1)}, since K and Σd_k are polynomially bounded in L. Define W as twice the product of all tests and reject the simultaneous k-th power subgroup at each exponent. Its two-coordinate local loss is bounded by
    2(13/(12k))^{d_k} ≤ δ/(10k²).
The sum over k is <δ/4. No assumption on the residue of N at the test primes was used.

Here log K ≍_b log L. The lower estimate
    log W ≥ Σ_{3≤k≤K, prime}d_k log k ≫ Eπ(K) ≫ E K/log K
uses ℓ≥k+1. For the upper estimate, d_k≪1+E/log k and splitting k at √K gives
    Σ_{k≤K, prime}d_k ≪ π(K)+ E √K + Eπ(K)/log K
                       ≪ E K/(log K)².
Consequently log W≪_b (E K/log²K)log L ≪_b C√(LE/log L). The lower bound on log W is ≥c_b C√(LE/log L) for large N with c_b independent of the fixed C.

As before, delete any still-accepted residues (and negatives) of all integer-base powers with exponent j>K. Their total is at most exp(L/(K+1)+O(log L)). Mertens and the polynomial bound for the individual test primes imply B_W≫_b W/(log L)². Choose C large enough so log W−L/(K+1)≫_b√(LE/log L). Since E=o(√(LE/log L)), the pair loss from this last deletion, at most twice the number of deleted classes, is <δ B_W/2. This proves the required retention, exact exclusion and evenness. The squarefree product depends on N only through its scale choices; the last finite deletion may depend on the exact integer N.

For context, the linear signed variant of the companion note still has even-character coefficient ℓ¹ cost 1+2π(K) before its exact high-power correction, despite the increasing d_k. But the signed lower test is not a 0–1 mask and need not be close to the actual prime count merely because its local mass is close. This tradeoff controls a modular operation, not the unresolved signed statistic on genuine primes.
