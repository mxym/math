# Exact worst-case round-by-round soundness under independent repetition

Consider a finite public-coin proof with r verifier challenges and a round-by-round certificate with per-round errors p_1,…,p_r. We give the sharp worst-case error guarantee for m independent parallel copies under all-accept verification: an exact minimax over nonincreasing integer cutoffs, or equivalently a backward dynamic program of binomial tails. The result allows joint adaptive prover messages and arbitrary changes of the original certificate's labels after a coordinate first leaves its doomed set.

The count-and-threshold method itself is prior work (Athamnah–Ron-Zewi–Rothblum, Appendix B). The contribution here is exact optimization and sharpness against *all* certificates, not just count-based ones. A finite verifier with ignored prover messages realizes the optimum for dyadic error profiles.

This settles the literal uniform bound in Remark 3 of Bitan et al., ePrint 2025/2152, negatively: six copies of a two-challenge proof of exact base error 1/8 have exact repeated error 389/131072, greater than 1/512. Its ordinary soundness is 15/64 and completeness is perfect. The failure persists at vanishing base error when the repetition parameter grows with its bit precision. For fixed repetition and round counts the claimed bound is true for sufficiently small base error, and the stated power is always the correct small-error order with parameter-dependent constants. At fixed base error, the exact limiting two-challenge exponent shows an exponential discrepancy as repetitions grow.

This is an information-theoretic bound for ordinary interactive proof certificates. The extremizer is a standalone finite random experiment, not a real-system test. We make no claim about a specific approximate sum-check protocol, its Fiat–Shamir transform, or its implementation.

Run `sh replay.sh | diff -u RESULTS.txt -` with Python 3. The first script uses exact rational binomial dynamic programming. The second explicitly checks finite trees, all subsets of selected intermediate layers, and adaptive joint message choices without importing the first.
