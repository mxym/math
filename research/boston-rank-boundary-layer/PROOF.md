# The joint law of the last rank and the centered average rank in truthful Boston assignment

There are n students, n one-seat schools and complete strict school rankings drawn independently and uniformly by the students. School priorities can be arbitrary fixed strict orders, or random independently of these preferences. In round r of ordinary (naive) Boston/immediate acceptance (IA), every unmatched student applies to the school ranked r, including schools already full. Each school that is still free and receives bids makes one irrevocable assignment according to its priority. Let W_n be the worst (largest) assigned rank and B_n the realized average assigned rank.

[Pritchard and Wilson, Stochastic Systems 13 (2023), §8.2](https://doi.org/10.1287/stsy.2022.0104) conjectured that the expected worst rank for naive Boston grows linearly. Their separate conjecture on a strictly smaller leading mean-rank coefficient than serial dictatorship was **already answered in the negative** by [Ortega, arXiv:2607.24970v2, Theorem 1 and §5.1](https://arxiv.org/html/2607.24970v2), including the adaptive variant. The present results concern the actual terminal-rank distribution and the *additive*, rather than multiplicative, scale of the ordinary IA rank. No extension of these second-order formulas to adaptive Boston, deferred acceptance, non-unit capacities or strategic reports is asserted.

**Theorem.** Let V_k, k≥1, be independent Beta(k²,1) variables, A_k=∏_{j≥k}V_j, and H_n=Σ_{k≤n}1/k. Then, jointly in law and in all mixed moments of total degree at most two,
```
 (W_n/n, B_n−H_n) → (1−A_1, Z),
 Z = Σ_{k≥1} [k A_{k+1}(1−V_k)−1/k]    (convergence in L²).
```
Both marginals are nonconstant. In particular
```
 E W_n/n → 1−π/sinh(π),
 E B_n = H_n−C+o(1),     C=Σ_{k≥1} (1−∏_{j≥k} j²/(1+j²))/k > 1 .
```
The second formula gives a strictly positive limiting additive improvement C−1 over the expected average rank of serial dictatorship, even though the leading coefficients coincide. The result concerns random student preferences, not the welfare of each individual student with fixed priority.

### 1. The finite occupancy chain and a finite bound

Write K_r for the number of unmatched students (also unassigned schools) after r completed rounds, K_0=n. Conditional on the entire revealed history, if K_r=k>0 and D=n−r, the next bid of each of the k active students is uniform among that student's D uninspected schools, independently across students. All k free schools occur in each uninspected list: a prior bid to one of them would have caused it to fill. These statements follow by deferred decisions on the independent random permutations; revealing priorities does not change them. In other words each of k independent draws hits any specified free school with probability 1/D and a dummy category with probability 1−k/D. The number X of distinct free schools hit determines K_{r+1}=k−X. This Markov transition depends only on k,D, not on the priority profile, even though individual winners can depend on it. The entire history of aggregate ranks, including (W_n,B_n), is determined by these decrements. W_n is the last round, and B_n=(1/n)Σ_{r=0}^{n−1}K_r.

The conditional probability to complete in this next round is k!/D^k≤1/D, since 1≤k≤D. Thus P(W_n>r)≥(n−r)/n for 0≤r≤n, by multiplication of the conditional survival bound. In particular (n+1)/2≤E W_n≤n. This already answers the order part of the worst-rank question. For the boundary-layer analysis note also
```
 E[K_{r+1}|K_r=k]=k(1−1/D)^k≤k exp(−k/n)≤k/(1+k/n).
```
The last expression is concave in k, giving by Jensen and induction
```
 E K_r ≤ n/(r+1) .                                                  (1)
```

### 2. The final fixed-k transitions

Consider a round boundary with K=k fixed and D list positions remaining, D→∞. Let L be the number of rounds from now through and including the first round with a new assignment. For 0≤a≤D,
```
 P(L>a | k,D)=[binom(D−a,k)/binom(D,k)]^k,
```
where the numerator vanishes when D−a<k. Indeed on the event of no success, all k students simply expose their next a positions and each must avoid all k free schools. It follows that (D−L)/D→V_k in law; the harmless one-round shift at an integer threshold does not affect the limit. Its limiting CDF is u^{k²}, 0≤u≤1. In particular the residual horizon D−L tends to infinity in probability. The probability that this success round makes two or more assignments tends to zero: conditional on its start with D' residual positions and on success now, the required probability is at most binom(k,2)(k/D')² divided by P(success now)≥k/D' (just use the first bidder). The starting count D'=D−L+1 tends to infinity in probability. This yields a bound tending to zero also after averaging (truncate it by 1).

By the Markov property, restarting after the success round gives joint convergence of successive residual fractions from any fixed k down to 1 to independent V_k,…,V_1, with all those decrements single w.h.p. Formally induct on k: the one-step kernel has the displayed limit for *any* deterministic sequence D→∞ and therefore uniformly for integer D above any diverging cutoff; use D−L→∞ in probability and condition on the first transition to obtain asymptotic independence. This works with a random starting D→∞ in probability, conditional on the observed entrance state.

We must justify entrance from n rather than a fixed k. Fix 0<ε<1/2, then a positive integer K. Up to time floor(εn), once the count crosses K from above it **visits K at a round boundary** with probability tending to one on the event that a crossing to ≤K occurs (in the absolute sense that the failure event has probability o(1)). Indeed cut at G=ceil(log² n). If the current k≥G, the number unfilled after this round has conditional mean at least k/4 for large n, since k≤D, D≥2 and (1−1/D)^D≥1/4. It is a function of k independent bids changing by at most one on replacing one bid (removing one and adding one changes the number of distinct free schools hit by at most one). Bounded differences imply P(K_{r+1}<k/8|history)≤exp(−c k) for an absolute c>0. A union bound over n rounds excludes a jump from k≥G straight to ≤K. If K<k<G the probability of hitting two or more free schools in one round is at most binom(k,2)(k/D)²≤C G⁴/n². A second union bound shows that none of these small-count rounds makes a multiple decrement in the early interval w.h.p. Finally by (1),
```
 P(K_{floor(εn)}>K)≤1/(ε K).
```
Therefore, except with probability ≤1/(εK)+o_n(1), the process enters K at a round boundary with starting residual fraction D/n between 1−ε and 1.

For k≤n let T_{n,k} be the completed round number in which the chronological k-to-(k−1) **distinct new school claim** occurs; multiple k may have the same T if a round makes several assignments. Then T_{n,1}=W_n. For any fixed J the above shows
```
 ((n−T_{n,k})/n)_{1≤k≤J}  ⇒  (A_k)_{1≤k≤J}.                     (2)
```
To see the two-limit passage, take K>J and ε=K^{-1/2}<1/2, then n→∞. When K is hit early, replacing its initial residual fraction by 1 changes every coordinate by at most ε. The fixed-K argument gives coordinates ∏_{j=k}^{K}V_j in the limit, with an exceptional event of probability at most K^{-1/2}+o_n(1); equivalently apply this comparison to bounded Lipschitz test functions. Now send K→∞. Indeed −log V_j has mean 1/j², so all tail products A_k exist a.s., are positive, and A_k→1 a.s. The same estimates ensure, for each fixed J, that the late decrements from J+1 down to 1 take place in separate rounds w.h.p. with the transition from J+1 itself entered singly: apply the fixed-K construction then let K→∞.

### 3. From the last ranks to the average: a uniform L² tail

We use Ortega's §3.1 device: expose the active bids within each round in some fixed order, but decide allocation by actual school priorities only after the round. Call the first bid to an as-yet unclaimed free school a success. Just before a bid, let k be the number still unclaimed, d the number of complete previous rounds. Its conditional success probability is p=k/(n−d): the bidder has exactly n−d uninspected positions, including every unclaimed free school. No probes remain after the last success, since the final round started with as many bidders as free schools and needs all of them to hit distinct free schools. There are at most n² probes. For each stage k=1,…,n there is exactly one success, in round T_{n,k}; let P_{n,k} count *all* probes during which k are unclaimed. Thus B_n=Σ P_{n,k}/n. This stage accounting does not assert that the first claimant is awarded that school.

For any set I of stages, the sum over its probes of (1−indicator(success)/p)/n is a sum of martingale differences. Indicators of the current stage are predictable; after completion pad with zeros. The expected square of the sum is at most
```
 (1/n²) E Σ_{probes in I} 1/p
 = (1/n²) E Σ_{successes in I} 1/p² ≤ Σ_{k∈I} 1/k² .             (3)
```
The sum itself equals Σ_{k∈I}[P_{n,k}/n−(n−T_{n,k}+1)/(nk)]. The remaining difference from Σ_{k∈I}(P_{n,k}/n−1/k) is minus Σ_{k∈I}(T_{n,k}−1)/(nk). For d_k=T_{n,k}−1, the tail P(d_k≥r)≤P(K_r≥k)≤min(1,n/[k(r+1)]) by (1): if the kth stage has not ended after r rounds, there must still be ≥k free schools. Hence E(d_k/n)²≤2/k by the discrete tail sum for d_k², using (2r−1)/(r+1)≤2 for r≥1. Together with (3) and Minkowski, uniformly in n and I⊂{k:k>K},
```
 ||Σ_{k∈I}(P_{n,k}/n−1/k)||₂ ≤ (Σ_{k>K}1/k²)^{1/2}+√2 Σ_{k>K} k^{−3/2}
                                    ≤ C₀/√K.                      (4)
```

For fixed k we have P_{n,k}/n⇒k(A_{k+1}−A_k), jointly in any finite list and with W_n/n, by (2). In fact if the transitions through the neighboring stages occur singly in distinct rounds, the full intervening rounds use k bids each. The partial first and last rounds differ from counting k(T_{n,k}−T_{n,k+1}) probes by at most 2(k+1) provided the kth stage is entered from a round starting at k+1. This proviso holds w.h.p. as established following (2). Always P_{n,k}/n≤k+1: at most n probes in the round in which stage k is entered and at most k per later round. Fixed finite lists are thus bounded and their moments converge.

Applying (4) first to K<k≤K' and passing n→∞ proves that the limit series defining Z is Cauchy in L². Then (4) on the full tail, finite-dimensional convergence with moments, and L² truncation yield the stated joint weak convergence and convergence of moments through degree two. For the latter use Cauchy–Schwarz to compare second moments of truncated and full variables, with their L² norms uniformly bounded; W_n/n and its limit are bounded by 1. Both limiting coordinates are nonconstant: condition on all independent V_j with j≥2. V_1 is uniform and appears in 1−A_1 and in the k=1 term A_2(1−V_1)−1 of Z with nonzero coefficient.

### 4. Exact constants

Write a_k=E A_k=∏_{j≥k} j²/(1+j²). Euler's classical product for sinh gives a_1=π/sinh π. Independence gives E[k A_{k+1}(1−V_k)]=k a_{k+1}/(k²+1)=a_k/k, whence the formula for C; convergence follows also from 1−a_k≤Σ_{j≥k}1/(1+j²)=O(1/k). It is strictly greater than 1: a_2=2a_1, a_3=5a_1/2, so the first three nonnegative terms sum to 11/6−17a_1/6>1 because a_1<5/17. The latter inequality follows already from the finite rational product ∏_{j=1}^{20}j²/(1+j²)<5/17. Serial dictatorship has expected average rank ((n+1)/n)H_n−1 (the remaining schools are uniform for each chooser, independently of that chooser's preference order). Its expected rank minus that of ordinary Boston tends to C−1>0.

These conclusions concern original rank, not a cardinal-utility score. Fixed-rank limiting shares, equilibrium welfare and first-order equivalence are different questions. In particular the mean-rank leading-coefficient conjecture is not claimed as newly resolved here.
