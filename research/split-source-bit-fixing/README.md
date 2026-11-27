# Consistent bit-fixing decomposition for two split random-oracle sources

Let H be a uniformly random function [N]² → [M]. Two sources use independent private randomness and receive H, each returning one coordinate and bounded classical leakage. Assume that each coordinate has average optimal guessing probability at most δ even with the full function and both leakages. An observer gets the leakage and the value of H at the two returned coordinates, not the coordinates themselves, and may make q adaptive classical oracle queries.

There is a consistent bit-fixing family, built from the sources and the fixing budget P before knowing q or the observer. If the observer is instead given the resampled oracle and the value of that oracle at the same returned coordinates, the change in acceptance probability is at most

    min{1, 3σ' q/P + 18 sqrt(σ' (q+1) δ)},

where σ' = σ₁ + σ₂ + 2 log₂ N. A resampled oracle fixes at most P entries of the original function and is uniformly random and independent elsewhere, conditional on the selected fixed set. The result answers the finite monolithic model of [AICR c/0010](https://aicr.info/c/0010/), including all query and range sizes and the order of its quantifiers. The one-point domain is handled exactly.

The proof also gives a direct bound of 10 sqrt(σ'(q+1)δ) on replacing the challenge value by a uniform independent output **without** changing the original oracle. Two ideas bridge the previous partial results: a reweighted random restriction of adaptive query transcripts, and an average hit bound that uses the product of posterior point probabilities. The remaining density decomposition is existing machinery, proved here for the specific model.

The result concerns uniform finite oracle tables and classical queries. It does not prove independent per-source decompositions, non-monolithic hash analogues or a security judgment about a concrete implementation.

Run sh replay.sh with Python 3 and a POSIX shell. Both exact checkers validate finite cases and proof identities; the theorem is analytic.
