# Shared randomness for conditional disclosure by equality

In classical conditional disclosure of secrets (CDS), Alice holds a secret and the referee should learn it exactly when Alice's and Bob's labels agree. Bob does not know the secret. In this model, for n-bit labels and ℓ-bit secrets, the exact minimum number of fixed fair shared bits for perfect correctness and perfect privacy is

    ℓ + max(n, ℓ)    for n, ℓ ≥ 1.

The converse allows arbitrary finite message alphabets and unlimited independent private randomness. It combines a support-size bound and a separate Shannon-entropy bound valid even for nonuniform shared resources. The matching construction uses pairwise-independent field masks and sends exactly ℓ bits from each sender.

For a one-bit secret, a different converse gives an explicit support lower bound varying with privacy error. Together with Hasegawa–Mataraarachchi's known constant-gap bound and a standard almost-pairwise-independent mask construction, this pins down the order of the shared randomness for every privacy error bounded away from the vacuous regime. The new claim concerns equality; it does not resolve the robust inner-product CDS problem.

See [PROOF.md](PROOF.md) and [SOURCES.md](SOURCES.md). Run `sh replay.sh` to verify all file hashes and reproduce the two finite checkers. The proofs are not limited to the checked finite instances.
