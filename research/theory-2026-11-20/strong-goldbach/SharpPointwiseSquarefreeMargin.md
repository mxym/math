# The sharp pointwise squarefree margin in the Huang–Li Goldbach reduction

**Result.** For even N→∞ put L=log N and let γ be Euler's constant. Define

    A(N)=∏_{p∤N}(1−1/[p(p−1)]),  D(N)=1−A(N),
    S(N)=2 C₂ ∏_{p|N,p>2}(p−1)/(p−2),   C₂=∏_{p>2}(1−1/(p−1)²).

Then, **unconditionally**,

    liminf L log L · D(N) = 1,
    liminf L · S(N) D(N) = exp(γ).                                  (1)

Both limiting constants are realized along the even primorials. This is a pointwise worst-case statement, not a typical-N estimate. It gives a sharp uniform margin for actual shifted primes:

    liminf [L² log L / N] # { primes p<N : N−p is not squarefree } = 1. (2)

Restricting p to αN<p≤βN for any fixed 0<α<β<1 changes the right-hand side to β−α. In particular it applies in the central Goldbach interval. These are *prime plus a non-squarefree integer* counts, not prime plus prime.

For [Huang–Li v2, Theorem 1 and Corollary 1](https://arxiv.org/pdf/2005.03811), (1) reduces the ordinary-distribution logarithmic buffer in their conditional corollary from exponent 12+ε to 10+ε, with the same unproved Möbius-twisted distribution hypothesis. No positive level of the latter is established here. The endpoint with an unspecified O(N/log N) error does not follow just by this computation. No historical priority is claimed.

## Extremal Euler products

Let a_p=1/[p(p−1)]. If N has k distinct prime divisors and p_k is the kth prime (starting with 2), then N is at least the kth primorial P_k. Removing the k largest local losses −log(1−a_p) gives the greatest possible product A(N) (including p=2 among those removed). Therefore

    D(N) ≥ 1−∏_{p>p_k}(1−a_p).

PNT and partial summation give Σ_{p>x}a_p ∼ 1/(x log x). For example Σ_{p>x}p^(−2)=−π(x)/x² + 2∫_x^∞ π(t)t^(−3)dt ∼ 1/(x log x); replacing by a_p costs O(1/x²). As the tail tends to zero, its product deficit is asymptotic to its sum. Also log P_k=θ(p_k)∼p_k. Along sequences with k→∞ we have p_k≤(1+o(1))L, giving D(N)≥(1−o(1))/(L log L). For bounded k, D(N) is bounded below by a positive constant. Equality asymptotically holds on P_k, giving the first claim.

For the second claim, put z=L/log L. It suffices to treat any sequence along which L S(N)D(N) remains bounded. Since S≥2C₂ we have D=O(1/L), whence

    Σ_{p∤N} a_p ≤ −log(1−D) ≪ 1/L,
    Σ_{2<p≤z,p∤N} 1/p ≤ z Σ_{p∤N} a_p ≪ 1/log L.

The contribution of the missing factors (p−1)/(p−2) up to z is consequently exp(O(1/log L))=1+o(1). In particular

    S(N) ≥ (1−o(1)) 2C₂ ∏_{2<p≤z}(p−1)/(p−2) ∼ exp(γ) log z ∼ exp(γ) log L.

Here the finite local product is exactly (∏_{p≤z}(1−1/p)^(-1))·(∏_{p>z}(1−1/(p−1)^2)), giving the displayed constant by Mertens' third theorem. The first claim now gives liminf L S D≥exp(γ). On P_k take z=p_k in the exact finite-product identity and use D(P_k)∼1/(p_k log p_k) and L∼p_k, giving sharpness.

## From the local loss to actual prime counts

For an interval I⊂[1,N−1] let |I| denote its integer length. Uniformly in even N and I, for any fixed B>0,

    Σ_{n∈I} Λ(n) μ²(N−n) = |I| A(N) + O_B(N/L^B).                  (3)

This is the standard unconditional shifted-squarefree estimate underlying [Huang–Li, §3.3, (23)–(28)](https://arxiv.org/pdf/2005.03811), for which the following polylogarithmic cutoff also suffices. Expand μ²(m)=Σ_{d²|m} μ(d). Truncate d at T=L^(B+4). Summing trivially for d>T costs O(L Σ_{T<d≤sqrt N}(N/d²+1))=O(NL/T+sqrt(N)L). At (d,N)>1 the only possible nonzero Λ(n) comes from n a prime power of a prime dividing d; the total for this fixed d is at most ω(d)L. At (d,N)=1 the Siegel–Walfisz theorem at modulus d²≤L^(2B+8) gives |I|/φ(d²) plus O_B(N/L^(2B+10)), uniformly in the two endpoints. To justify the uniform endpoint formulation one may use the maximal Siegel–Walfisz theorem or apply its usual version for endpoints ≥N/L^(2B+12) (their logarithms are comparable to L), and bound smaller endpoints trivially. The cutoff has O(T) terms so all these errors are admissible. Finally the sum of μ(d)/φ(d²) over (d,N)=1 is A(N) and its absolute tail is O(log(2T)/T), by d/φ(d)≪log(2d). This proves (3). All constants need not be effective.

By the prime number theorem on intervals at this absolute error scale, and the negligible proper-prime-power weight O(sqrt(N)L²), (3) gives

    Σ_{p∈I} (log p) (1−μ²(N−p)) = |I| D(N)+O_B(N/L^B).             (4)

For fixed central proportional intervals, log p = (1+O(1/L))L. As ND(N) ≫ N/(L log L), choose B>2 to obtain, uniformly along even targets, a count asymptotic to (β−α)ND(N)/L. For the full interval, p≤N/L^5 costs at most N/L^5 in the unweighted count and negligible weighted mass; above that cutoff log p=(1+o(1))L uniformly. This proves (2), with sharpness on the primorial subsequence.

The genuine signed sum T(N)=Σ_{n<N} Λ(n)μ(N−n) consequently obeys the unconditional **one-sided** estimate

    S(N)(N−T(N)) ≥ [exp(γ)−o(1)] N/L.                               (5)

Indeed μ≤μ², so (3) implies N−T(N)≥ND(N)−O_B(N/L^B), and S(N)≪log log N (by comparison with the primorial having the same number of prime divisors). We do *not* claim sharpness in (5): cancellation from negative Möbius values can increase the genuine signed gap. Sharpness was proved only for the squarefree comparison in (1), (2) and (4).

## Exactly what remains conditional

Huang–Li Theorem 1, for fixed A>0 and θ∈(0,1), assumes their EH(N^θ L^(2A+8)) and EH_μ(N^(1−θ)), and gives the weighted prime-pair count r̃(N)≥N S(N)D(N)−O_{A,θ}(N/L^A). Insert A=1+ε/2. By (1) the magnitude of that error is little-o of the uniform main lower bound, and therefore

    EH(N^θ L^(10+ε)) and EH_μ(N^(1−θ))
       ⇒ r̃(N) ≥ [exp(γ)−o(1)] N/log N

for all sufficiently large even N. This is a refinement of the **same-scale modulus bookkeeping**, not a logically weaker global ordinary EH assumption: with the source’s maximum over prefixes and arbitrary log savings one can apply ordinary EH(x^θ) at x=N(log N)^((C+1)/θ) and increase the requested savings exponent to recover its estimate through q≤N^θ(log N)^C for any fixed C. This rescaling does not apply to the twisted sequence whose shift is N. The stated result is not a power improvement in the levels or a deduction from ordinary EH or GRH alone. In particular the primary unresolved term is the error of their relation (22), not the local minimum just computed. A one-sided uniform lower bound on the error in (22) better than −(exp(γ)−η)N/L for some fixed η>0 would already suffice for existence; deriving that bound unconditionally is a different problem.
