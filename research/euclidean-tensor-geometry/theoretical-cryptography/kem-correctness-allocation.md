# How key reuse allocates honest KEM mismatch risk

A one-execution failure probability does not describe how failures cluster when a key is reused. This note gives an exact allocation law. With fixed total traffic and exchangeable per-key failure rates, more concentrated reuse raises **every convex cost of the number of honest mismatches**, yet lowers the chance of observing any mismatch. The law requires neither independent per-key rates nor a specific KEM. This is a correctness result, not an IND-CCA claim or a recommendation about security-driven key rotation.

## Experiment

Use a single KEM parameter set. Fix a nonadaptive allocation n=(n₁,…,nₖ) of T honest sessions to K key pairs before any key or outcome is observed. Given the key pairs (and any common random modeling state), each session starts with fresh independent randomness. Its outcome is 1 exactly when the two shared keys differ; explicit failure, if the KEM has one, counts as a mismatch. Exclude implementation faults and failures of random generation. Let Pᵢ∈[0,1] be the conditional mismatch probability of key i. We assume P=(P₁,…,Pₖ) is exchangeable, meaning invariant in law under permutations. For example, independently generated keys under a common fixed specification, with no key selection, suffice. Conditional on P the key counts are independent Bin(nᵢ,Pᵢ) variables: conditional on the underlying state the independent Bernoulli laws depend on it only through P. Write Yₙ for their sum.

This extends the honest single-execution experiment of [NIST SP 800-227, Definition 2](https://doi.org/10.6028/NIST.SP.800-227). In [FIPS 203, §3.3 and Table 1](https://doi.org/10.6028/NIST.FIPS.203), the ML-KEM rate is taken over both key-generation and encapsulation randomness, under a heuristic ideal-function assumption. In our notation it is a single-execution mean, not a uniform bound on Pᵢ. We derive no new numerical value for ML-KEM. If an ideal random function is shared, one may condition on it to state the model, or work with exchangeable P directly; no unconditional independence of Pᵢ is required for the main theorem.

## Theorem: an exact transfer identity

Starting with loads (a,b) on two keys, where a≥b≥1, let n⁺ be the allocation obtained by replacing them with (a+1,b−1). Let p and q denote their random rates and let W be the count from the other keys. Write Δ²φ(s)=φ(s+2)−2φ(s+1)+φ(s). For j=0,…,a−b define Vⱼ, conditional on P, to have the law of W plus four independent binomial counts of parameters (b−1,p), (b−1,q), (j,p), and (a−b−j,q), also independent of W conditional on P. Then

    E φ(Yₙ₊) − E φ(Yₙ)
      = ½ E[(p−q)² Σⱼ E[Δ²φ(Vⱼ) | P]].                       (1)

In particular Yₙ≤cx Yₙ₊: the means are equal and the displayed difference is nonnegative for every convex φ. For a test with strictly positive discrete second differences the inequality is strict if Pr(p≠q)>0. Randomness of each individual Pᵢ alone is not enough for strictness; the rates could all be equal within each realization.

**Proof.** Couple the change by letting one independent Bernoulli coin switch from q to p, with a coins of rate p and b−1 of rate q kept fixed. Conditional on P, the expectation difference is (p−q) times the expected first difference Δφ applied to their count plus W. Exchangeability under swapping the two rates, leaving the remaining P coordinates fixed, allows averaging this expression with its swapped form. The resulting bracket subtracts the expectation with a coins of rate q and b−1 of rate p from the expectation with a coins of rate p and b−1 of rate q. Both share b−1 coins of each rate; the remaining a−b+1 coins have rate p in the first term and q in the second. Change those remaining coins one by one from q to p. Each change contributes (p−q) E[Δ²φ(Vⱼ)|P]. The outside multiplier is (p−q)/2, which proves (1).

### Implications

- For two load vectors with the same sum and number of coordinates (zero loads are allowed), if n' majorizes n in the standard sense of sorted prefix sums, then Yₙ≤cx Yₙ′. Integral majorization is generated, up to permutations, by unit transfers from a smaller coordinate to a larger one. Equivalently, from the larger load vector one can repeatedly transfer a unit from a surplus to a deficit while maintaining the target prefix-sum inequalities, choosing the deficit no later than the next prefix-sum return to zero. Re-sort after each step; sorting only increases prefix sums, and each step strictly decreases the sum of squares. The source and target of each balancing transfer differ by at least two, since the target vector is sorted and the source exceeds its target while the deficit lies below its target. Thus near-equal loads minimize convex costs, and putting all traffic on one key maximizes them. In particular this applies to every stop-loss cost φ(x)=(x−h)₊, and to the number of pairs of mismatches φ(x)=x(x−1)/2.
- Conversely, φ(x)=min(x,1) is concave and equals the indicator of at least one mismatch on nonnegative integers. Thus equalizing loads **maximizes** the probability of at least one mismatch under this model. This does not order every raw count tail. For example, with two independent rates that each equal 0 or 1 with probability 1/2, loads (2,2) yield Pr(Y≥2)=3/4 but (3,1) yields 1/2.
- For the pair-count cost, the exact increase in a transfer is (a−b+1) E[(p−q)²]/2. It is also exactly half the increase in variance, since the mean is unchanged. With i.i.d. rates of mean μ and variance σ², Var(Yₙ)=T μ(1−μ)+2σ² Σᵢ binom(nᵢ,2), as also follows by summing the pairwise covariances.
- The formula works after averaging a common environmental state or with other exchangeable dependence. It makes no claim for adaptive scheduling, selection of keys by their observed reliability, per-session shared randomness, or a mix of nonexchangeable key populations.

## Sharp mean-only bounds for independent rates

For this paragraph assume independent identically distributed rates with mean μ and a common upper bound b>0 (b=1 is always valid). Let Wᵢ be independent with Pr(Wᵢ=b)=μ/b and Pr(Wᵢ=0)=1−μ/b. Then

    Bin(T, μ)  ≤cx  Yₙ  ≤cx  Σᵢ Bin(nᵢ,Wᵢ),

with the binomials independent conditional on W on the right. For each convex φ, the conditional test expectation given a per-key rate t has nonnegative second derivative: for a binomial of size N the derivative is N(N−1) times the expected discrete second difference against Bin(N−2,t), plus the unchanged sum from the other keys inside the test. For N<2 the expectation is affine or constant. Jensen gives the lower envelope by replacing one rate at a time by μ; the chord between 0 and b gives the upper envelope by replacing it by Wᵢ. Independent rates permit iterating both replacements. The extremes are attained by the constant and two-point rate laws in the abstract model. This establishes sharpness given only μ and b, not attainability by any specific scheme.

For b=1 it follows that, with m nonempty keys,

    1 − (1−μ)^m  ≤  Pr(Yₙ≥1)  ≤  1 − (1−μ)^T.

The lower extreme clusters all failures of each key into a single fate; the upper extreme has no key-to-key heterogeneity. An average correctness number alone cannot distinguish the two. With exchangeable but dependent rates, use the transfer identity, not these independent-rate envelopes.

## Relation to prior work and arithmetic check

[Glabush–Hövelmanns–Stebila, On the Multi-target Security of Post-Quantum Key Encapsulation Mechanisms](https://doi.org/10.62056/a63zl83y6) uses multi-user correctness terms in adversarial reductions; the experiment here measures counts of honest mismatches under a fixed allocation instead. [Barbosa et al., Formally Verified Correctness Bounds for Lattice-Based Cryptography](https://eprint.iacr.org/2025/1562) studies correctness bounds for a single experiment, including the precision of heuristic approximations for ML-KEM. The separate mean-only envelope above is an application of the classical shape preservation of [Bernstein-type operators](https://doi.org/10.1239/aap/1029955144); the contribution here is the exact squared-rate-difference law (1) for transferring uses between exchangeable keys and its risk implications. The preliminary literature check did not identify the same transfer formulation; this is not an absolute priority claim.

For φ(s)=zˢ, equation (1) is a generating-polynomial identity with right-hand side ½(z−1)² E[(p−q)² Σⱼ E[z^Vⱼ | P]].

The [exact toy verifier](verify-kem-correctness-allocation.js) checks the polynomial form of (1) for 11,090 load and rate-orbit configurations and 84,880 stop-loss inequalities using integer arithmetic. It enumerates only synthetic distributions on {0,1/4,1/2,3/4,1}. It contains no KEM implementation, cryptographic data, or deployment assumptions beyond the probability model.
