# The three real-power regimes of critical beta-splitting subtree sizes

In the discrete critical beta-splitting tree T_n on n leaves, let N_n(m) be the number of fringe clades with m leaves and S_n(p)=Σ_{m=2}^n N_n(m)m^p. The root counts; leaves do not. The same statistic appears in [Aldous–Janson II, v3 §6.2, Open Problem 16, (76)–(78)](https://arxiv.org/html/2303.02529v3#S6.SS2). We consider real fixed powers; this is not an analysis of complex powers, fluctuations in the first two regimes, or exponents varying with n. All logarithms are natural.

**Theorem.** In the common exchangeable fragmentation and iid label coupling of this tree family, for every fixed 1≤q<∞ the following limits hold in L^q:
```
p<1:   S_n(p)/n             → Σ_{m≥2} a(m)m^{p−1},
p=1:   S_n(1)/(n log² n)    → 1/[2ζ(2)],
p>1:   S_n(p)/(n^p log n)   → J_p=∫₀^∞ Σ_i P_i(t)^p dt .
```
Here a(m)=H_{m−1}/[ζ(2)(m−1)], H_j=Σ_{k=1}^j 1/k, and (P_i(t)) are the frequencies of the interval fragments at time t. For p>1 the limit is nonconstant. Write ν(dx)=dx/[2x(1−x)] on (0,1) and
```
κ(p)=∫(1−x^p−(1−x)^p)ν(dx) = ψ(p)+γ .
```
Then E J_p=1/κ(p) and
```
Var J_p = ∫ (1−x^p−(1−x)^p)^2 ν(dx) / [κ(p)^2 κ(2p)] > 0 .
```
The limiting law and its continuum moments are **classical**: it has Bertoin's self-similar fragmentation-area law of index 1−p, with the indicated binary dislocation measure. The main step here is the passage from the sampled *discrete unweighted genealogy* to that continuum area at all supercritical real powers. At p=2 the limit has mean 1 and variance 2/11; thus the leading expectation in (78) is correct, but the normalized sum is not asymptotically deterministic. The means in (76),(77) are already consequences of earlier results.

### Known inputs and model

At size m an ordered root split into (i,m−i) has probability m/[2H_{m−1}i(m−i)]. The subtrees are conditionally independent with their respective size laws. The tagged leaf's ancestral sizes form the strictly decreasing chain with transition 1/[(m−i)H_{m−1}] to i<m. Its probability a(n,m) of visiting m satisfies E N_n(m)=na(n,m)/m and a(n,m)→a(m) as above. See [Aldous–Janson–Li](https://doi.org/10.1214/24-ECP645) and [Aldous–Janson II, (51), Theorem 18](https://arxiv.org/html/2303.02529v3#S4.SS1). We also use Var N_n(m)=O_m(n) from [Brandenberger–Chin–Mossel, Corollary 1.4](https://arxiv.org/html/2505.24821v3#S1.SS2).

The exchangeable homogeneous fragmentation with binary dislocation measure ν (symmetric oriented representation) embeds T_n: sample an infinite iid sequence of uniform labels in the unit interval independently of the fragment process. At each time, two sampled labels are in the same block when they fall in the same interval fragment. Restricting to the first n labels gives a finite process with discrete genealogy T_n, and **conditional on this finite tree**, the lifetimes τ_v of all its nonsingleton clades v are independent exponentials of respective rates H_{|v|−1}. This is the Aldous–Janson coupling [III](https://arxiv.org/abs/2412.09655); see also [Ma, §1.2, Lemma 2.1](https://arxiv.org/html/2609.14329v2#S2), who already uses the independent rate-rescaled exponentials to compare continuous and discrete path lengths. The continuum frequencies sum to one at each fixed time a.s. A pair of distinct labels remains in the same block at time t with probability e^(−t), by the two-label restriction with rate H_1=1.

### Subcritical and critical powers

For a uniform tagged leaf U and size bin [M,2M), M≥2, let V_M be its number of ancestral sizes in the bin. From any s∈[M,2M), the conditional probability to move to one of 1,…,M−1 is at least (M−1)/(2M H_{2M})≥1/(4H_{2M}). The decreasing chain cannot return; therefore ||V_M||_q≤C_q H_{2M}, uniformly in n, by geometric tails (zero if the bin is skipped).

Given T_n, averaging over U counts each m-clade with probability m/n. Thus the omitted part of S_n(p)/n for m≥M is the conditional mean of Σ_{tagged sizes m≥M} m^{p−1}. For p<1, the contraction of conditional expectation in L^q and the triangle inequality bound its L^q norm by
```
C_q Σ_{d≥0} (2^d M)^{p−1} H_{2^{d+1}M} = O_{q,p}(M^{p−1}(1+log M)) .
```
This tends to zero independently of n. For each fixed m, N_n(m)/n is bounded and converges to a(m)/m in L² by its mean and variance; hence it converges in every finite L^q. The deterministic tail Σ_{m≥M}a(m)m^{p−1} is finite and vanishes. Finite truncation proves the first assertion. BCM already give the subcritical mean by the unnumbered weighted occupation implication following their (1.7), with weight m^{p−1}.

For p=1 the normalized S_n(1)/n is the conditional expectation of the edge-depth of U, given T_n. The mean and variance of the edge-depth from [Aldous–Pittel Thm 1.2](https://doi.org/10.1214/24-AAP2112) give convergence in L² after division by log²n, to 1/[2ζ(2)]. The tagged edge-depth is bounded by the maximum edge-depth; [Ma's Thm 1.1](https://arxiv.org/html/2609.14329v2#S1) bounds all finite moments of the latter divided by log²n. Interpolation and conditional Jensen give the stated L^q result. The left-side random statistic is precisely the sample-average edge-depth; [Svihla–Lladser Thm 2.1](https://doi.org/10.1007/s11538-026-01655-x) already gives a sharper variance expansion at p=1.

### Supercritical powers: a clock-weighted integral

Fix p>1. Write m_B(t) for the number of the first n labels in a present block B. Set
```
Z_n(t)=Σ_{B:m_B≥2}(m_B/n)^p ,
Y_n(t)=Σ_{B:m_B≥2}(m_B/n)^p H_{m_B−1}/log n ,
Z(t)=Σ_i P_i(t)^p,              A_n=∫₀^∞ Y_n(t) dt .
```
For n≥2, H_{m−1}/log n≤C uniformly. For a uniform tagged sampled label conditionally on the empirical blocks, let M be the size of its block at time t, and put r=min(p−1,1)>0. As M/n≤1, on M≥2 we have
```
(M/n)^{p−1} ≤ (M/n)^r ≤ 2^r ((M−1)/(n−1))^r .
```
Size biasing, Jensen's inequality, and the two-label survival probability yield
```
E Z_n(t) ≤ 2^r E[((M−1)/(n−1))^r] ≤ 2^r exp(−rt) .
```
Since Z_n≤1, ||Y_n(t)||_q ≤ C 2^{r/q} exp(−rt/q). This is integrable over all t and independent of n.

For fixed t, conditional on the interval partition, empirical masses converge a.s. to true masses on every interval and in ℓ¹; for the latter, truncate to finitely many intervals of total mass ≥1−ε, and use convergence of their empirical total. Intervals of positive mass have m_B/n→P_B>0, and H_{m_B−1}/log n→1. Since the omitted p-power sum is bounded by the omitted empirical mass times a fixed constant, this also proves Y_n(t)→Z(t) a.s., and in every L^q by boundedness. In particular the limit obeys the same integrable time envelope in L^q. Minkowski's integral inequality and dominated convergence now give A_n→J_p in L^q for every finite q, and all moments used below exist.

On the finite tree,
```
A_n = (1/log n) Σ_{v internal} (|v|/n)^p H_{|v|−1} τ_v .
```
Given T_n, the last rate times lifetime variables are iid mean-one exponentials. Thus, with B_n=S_n(p)/(n^p log n),
```
E[A_n|T_n]=B_n,        Var(A_n|T_n)=Σ_v (|v|/n)^{2p}/log²n ≤ B_n/log n.
```
Consequently ||A_n−B_n||_2²≤E A_n/log n→0. The L^R norms of B_n are bounded for every finite R by conditional Jensen and the corresponding bounds on A_n. Interpolating the difference between L² and any higher L^R gives convergence of A_n−B_n to zero in each L^q. This proves the supercritical assertion under the stated canonical coupling.

### The limit law

For the same homogeneous fragmentation, [Bertoin, *The area of a self-similar fragmentation*, ALEA 9 (2012), §3.4, p.64](https://alea.impa.br/articles/v9/09-02.pdf) identifies the integral of the sum of block frequencies to power 1−α with the area in the self-similar fragmentation of negative index α. This applies with α=1−p: no erosion, binary conservative dislocations and finite ∫min(x,1−x)ν(dx). His Lemma 3.1 and Corollary 2.2 characterize the law by its moments and give all moment recursions. There is no claim of a new area distribution or of new continuum moment identities.

For completeness the first two moments in that corollary give
```
κ(p) E J_p=1,
κ(2p) E J_p²=2E J_p + [∫2x^p(1−x)^p ν(dx)] (E J_p)² .
```
The symmetric full interval ν is identical for symmetric integrands to the ordered maximum-child measure dx/[x(1−x)] on [1/2,1). For κ(p) use
```
1−x^p−(1−x)^p=x(1−x^{p−1})+(1−x)(1−(1−x)^{p−1}),
```
so κ(p)=∫₀¹(1−x^{p−1})/(1−x) dx=ψ(p)+γ. Subtracting the square of the mean gives the displayed variance, since the combined integrand of 2κ(p)−κ(2p)+∫2x^p(1−x)^p ν(dx) equals (1−x^p−(1−x)^p)^2. This is positive away from the endpoints and integrable. For p=2, κ(2)=1, κ(4)=11/6 and the squared-integrand integral is 1/3, giving 2/11.
