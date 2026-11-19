# Known observation laws: the Hellinger separation determines the information rate

There are n≥2 arms and one uniform planted index. Conditional on it, successive requested observations are independent, with a known probability law U at the planted location and a known common law V elsewhere. The two laws can be arbitrary probability distributions on the same standard Borel observation space: no moments, densities with respect to Lebesgue measure, or mutual absolute continuity are required. There need not be a numerical reward or an ordering by means. One pull returns one sample at one chosen arm. Define I*(t) as in the main note, with an expected pull budget t≥0 under the uniform planted model and a transcript including its length. Put
    
    η = H²(U,V) = ∫(√dU−√dV)² ∈ [0,2].

**Theorem.** With absolute constants, simultaneously for all these laws, all n and all t,
    
    (log n)/64 · min{1,tη/n} ≤ I*(t) ≤ 112(log n) · min{1,tη/n}.

At η=0 every history is independent of the secret. Otherwise this is an order characterization, not an exact leading constant. It treats one planted location, not general bandits, arbitrary priors or unknown observation laws.

## Converse

Use P_i,M,P_{ij},T,N_j from [the Bernoulli proof](PROOF.md), now with U as the planted law. Take the seeded finite experiment padded to m, retaining the independent seed as a common initial coordinate. The one-sided sequential Hellinger inequality of Foster–Han–Qian–Rakhlin [Lemma F.2](https://papers.nips.cc/paper_files/paper/2024/file/4b6908c6695009dd84846e273d6c2607-Paper-Conference.pdf) bounds the squared Hellinger distance of two trajectory laws by 7 times the expected sum of their one-step conditional squared Hellinger distances, **expectation under the first law**. Multiplying all their distances by two changes nothing. Our conditional discrepancy between P_i and P_{ij} is η exactly on the steps where j is drawn, and zero otherwise. Actions and stop decisions agree as conditional functions on the same seeded prefix; after stopping both kernels put mass one on the cemetery outcome. Thus, including possibly singular U and V,
    
    H²(P_i,P_{ij}) ≤ 7η E_i N_j.

The two-planted bridge, triangle inequality and ordered-pair average in the main proof now give (1/n²)∑_{i,j}H²(P_i,P_j)≤28ηt/n. The same bounded-density comparison and limiting argument give I*(t)≤min{log n,28(2+log n)ηt/n}. Since log n≥log 2>2/3, this implies the stated upper bound.

## Achievability

Use a single-elimination tournament, a classical noisy search/PAC idea. The elementary likelihood comparison below adapts it to arbitrary known laws. Pad the bracket to M=2^{ceil(log₂n)}≤2n, using empty slots as byes. Only matches of two actual arms require any observations; fix the bracket and deterministic tie breaking. In round ℓ=1,2,…, draw bℓ=ceil((ℓ+4)/η) fresh samples from each of the two contestants. Compare the likelihood of U^bℓ⊗V^bℓ to that of V^bℓ⊗U^bℓ under the common dominating measure (U+V)^{⊗2bℓ}. Advance the contestant declared planted. A match between two ordinary arms is allowed to return either; even if both likelihoods vanish on such observations the tie convention defines its winner.

If the planted contestant has survived to a round, then conditional on the past and on the planted label, the other contestant, if present, uses V, and future draws are fresh. For two hypotheses with densities f,g, each type of error of the likelihood comparison is bounded by ∫√fg: on the specific error set, the true density is no larger than the competing one. Tensorization gives the per-match bound
    
    (∫√dU dV)^{2bℓ}=(1−η/2)^{2bℓ} ≤ exp(−bℓη) ≤ exp(−ℓ−4).

The chance that the planted arm ever loses is at most ∑_{ℓ≥1}exp(−ℓ−4)≤1/16 (use e>2). Since η≤2, bℓ≤(ℓ+6)/η. There are at most M/2^ℓ matches at level ℓ. Hence the entire tournament budget is bounded deterministically by
    
    (2M/η)∑_{ℓ≥1}(ℓ+6)/2^ℓ = 16M/η ≤ 32n/η.

The transcript gives an estimate with error e₀≤1/16. By Fano its information is at least (1−e₀)log n−h(e₀), where h is binary entropy. For x≤1/16, monotonicity and h(x)≤x log(e/x) give h(x)≤(1+4log2)/16≤(3/8)log2, so even at n=2 this gives at least (1/2)log n.

Run the tournament with independent probability min{1,tη/(32n)}, and otherwise stop before taking any samples. The active branch always makes at least one pull since n≥2, so the branch is visible from the raw transcript; the active strategy itself is deterministic. The budget holds and the mutual information is at least half this active probability times log n. This proves the lower bound. ∎

For the symmetric Bernoulli laws of the main problem, η=2(1−√(1−Δ²)) lies between Δ² and 2Δ². Thus this extension also gives matching orders uniformly to Δ=1. The short Bernoulli converse does not rely on the general sequential Hellinger theorem.
