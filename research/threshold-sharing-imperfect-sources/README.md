# One-bit overhead for threshold sharing without extraction

For every threshold $2\le t\le n$ and sufficiently large binary field $\mathbb F_{2^b}$, one dealer draw from an explicit class of flat, imperfect sources suffices to share a $b$-bit secret with perfect privacy and perfect reconstruction. Each party gets one field symbol and one bit. The dealer-key label uses exactly $(t-1)b+\lceil\log_2 C\rceil$ bits, where $C=C(n,t)$ is an explicit odd integer. The best deterministic one-bit extractor for this source class has worst-case total variation distance exactly $1/(2C)$.

The qualitative all-threshold separation is already implied by combining Aggarwal's unanimous construction with the distribution design of Aggarwal–Chung–Obremski–Ribeiro. That route hands each new participant a tuple of old shares. The result here is a direct one-symbol-plus-one-bit construction for the intermediate thresholds $3\le t<n$, with the stated key length and error. The formulas recover Aggarwal's threshold-two and unanimous endpoint constructions. The appendix of the proof also gives the sharp integer share-width requirement and a label count optimum confined to the stated local multiplicity template.

- [Proof and model](PROOF.md)
- [Sources, comparison, and scope](SOURCES.md)
- [Deterministic replay output](RESULTS.txt)

Run `bash replay.sh` with Python 3. The checkers cover exact multiplicities and source-switch combinatorics, and independently enumerate finite-field sharing, authorized decoding, and all-source privacy at selected parameters. They do not replace the all-parameter proof.

This is ordinary information-theoretic threshold sharing from a specified source class. It makes no claim about leakage resilience, non-malleability, adaptive share corruption, an implementable randomness source, or any deployed system.
