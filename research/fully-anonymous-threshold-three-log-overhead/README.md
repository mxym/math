# Logarithmic overhead for perfect fully anonymous 3-threshold sharing

For every n ≥ 4 and every L ≥ 1, setting m = ceil(log2 n), there is an explicit perfect fully anonymous 3-out-of-n sharing scheme for L-bit secrets with exactly

    M = m ceil(L/m) + 10m ≤ L + 11m − 1

bits per share. Every pair of honest shares is exactly independent uniform on the full share alphabet, for every fixed secret. Every honest triple recovers the secret from the share values alone, in any order, with zero error, even when values repeat. Setup is deterministic polynomial-time public preprocessing; the dealer runs in expected polynomial time with fair bits; reconstruction is deterministic polynomial time.

The new auxiliary scheme shares two field elements at once. A ratio of three distinct shares identifies a projective orbit; when an honest triple has a duplicate, the line of the nonzero difference identifies the secret. Exact directional reweighting fills the diagonal probability while preserving the full pair law. Feeding this auxiliary into the direction-space compiler of Ren–Yu changes its threshold-three overhead from quadratic-logarithmic to logarithmic. The known anonymous-reconstruction lower bound is logarithmic here, so the order matches, not the leading constant.

This does not claim new existence of perfect 3-threshold FASS (Con–Li–Mazor already resolved that), nor a new bound for t ≥ 4 or robustness to mixing dealers. See SOURCES.md and PROOF.md. Run `./replay.sh` (Python 3.10+); finite exact checks supplement the proofs.
