# Sharp exterior norm prefactor and singular sectors for complementary Hamming balls

Das–Dimitrov already give the radial Krawtchouk ensemble's exact large-deviation rate, and Bernard–Crampé–Vinet already give the corresponding chopped correlation matrix and Terwilliger blocks. This note does not claim either ingredient as new.

For two fixed positive radii strictly outside the complementary-ball concentration circle, we get the leading `n^(-1/2)` norm prefactor, with the lattice floors kept inside the exponential. Each reversed spin-defect block has a geometric rank-one limit after normalization. The radial block is eventually the unique maximizing sector, and for any fixed J the leading J+1 distinct singular values are eventually furnished in order by sectors 0 through J, with their exact multiplicities.

A closed-form optimization of the one-qubit exponential tilt also supplies a finite-n bound with the sharp exponential rate and no polynomial loss. This refines the two-ball case in [Beigi–Tomamichel, Lemma 12](https://arxiv.org/html/2611.05943v1#A1). It is not a statement about arbitrary spatial supports, a full monogamy-game exponent, a protocol, or critical/interior scaling.

See [the proof](PROOF.md) and [the primary-source comparison](SOURCES.md). Run `bash replay.sh` with Python 3 and sha256sum. One verifier compares direct Walsh Gram trace powers and integer spin blocks, and independently enumerates exact small projection-DPP gap events. The other uses the integer polynomial recurrence and numerical Rayleigh/Frobenius bounds for the large-block comparisons; its printed endpoints are rounded. The analytical result does not depend on those numerical checks.
