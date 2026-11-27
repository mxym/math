# Exact uniform-prior target-distribution semantic security

This note gives the exact single-ciphertext optimum for all fixed Boolean
predicates of a uniform N-message source and a uniform k-element independent key.
The optimum is a finite hypergeometric mean, attained by sampling distinct
ciphertext entries. For perfect correctness this sharpens the order estimate in
Su–Cheng–Wang, ePrint 2026/1899, Corollary 1. We separately define and solve the
extension allowing average decoding error. The same optimizer meets the required
correctness probability for every message and key pair.

Three consequences are an odd/even zero-gain frontier, an exact deletion
recurrence at perfect correctness, and the exact universal worst-prior constant
at a fixed number of keys. An appendix gives a finite LP for arbitrary finite
priors and predicate classes, not a closed formula or efficient algorithm in
that setting.

This is a target-dependent, one-ciphertext, information-theoretic result.
Zero predicate prediction gain need not mean the ciphertext and message are
independent. No short ciphertext, bounded fair-coin budget, source-oblivious
cipher, chosen-plaintext security, or key-reuse guarantee is asserted.

Run `sh replay.sh` with Python 3 and GNU-compatible sha256sum. PROOF.md is
self-contained; the two exact rational checkers are finite independent tests,
not substitutes for the proof. SOURCES.md distinguishes the prior Fano
extremizer and support-constrained channel results from the present application.
