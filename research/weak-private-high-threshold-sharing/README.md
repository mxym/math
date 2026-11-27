# Weakly private (n−1)-out-of-n sharing with O(log log n) bits

A one-bit secret can be shared among n labelled parties so that every n−1 shares reconstruct it exactly, every n−2 shares satisfy the pointwise weak-privacy ratio, and each share has O(log log n) bits. The guarantee can be any fixed p<1, or p≥1−O(1/log n) with the same share-size order. This answers the high-threshold question in Beimel–Ishai–Kushilevitz–Li, ePrint 2025/1978, with positive and quantitatively stronger privacy than merely p>0.

The share vectors have one additive parity constraint. A deterministic polynomial-time construction gives a different Boolean table for each party; summing those tables on the share symbols colors each two-coordinate completion fiber almost evenly. A bounded fair-coin sampler preserves the pointwise ratios up to explicit rounding factors. There is no public per-execution share, rejection loop or probability of incorrect reconstruction.

For arbitrary schemes, a separate converse bounds the reciprocal alphabet sizes in terms of p. At p=1 it recovers the known perfect-privacy lower bound, explaining why this is not a construction for perfect privacy. At fixed p<1 it does not rule out constant alphabets.

Run sh replay.sh with Python 3 and a POSIX shell. The analytic proof is in [PROOF.md](PROOF.md), with exact source and scope in [SOURCES.md](SOURCES.md). Two exact checkers validate the construction and converse on finite cases.
