# Weak random-erasure recovery for Reed–Muller codes

**Conjecture 16 of Błasiok, Lou, Rosen and Sudan (arXiv:2604.04188v2) holds.** There are absolute constants \(\gamma>0\) and \(\zeta\ge1\) such that a binary Reed–Muller code of blocklength \(M\) and rate at most \(1-\varepsilon\), with \(M^{-\gamma}<\varepsilon<1/2\), recovers an independent random erasure pattern at rate \(\eta\le\varepsilon^\zeta\) with probability \(1-O(M^{-3})\). The same statement holds for any binary linear code with a doubly transitive coordinate-permutation group.

The proof combines the classical erasure EXIT area identity with the small-bias version of the Friedgut–Kalai threshold bound. It uses the area deficit to locate a point below the transition even as the rate tends to one, then integrates the threshold bound down to a power of the deficit. The error guarantee is for recovery of the **whole** codeword, not just one coordinate.

[Proof](PROOF.md) · [Source map](SOURCES.md) · [Exact replay output](RESULTS.txt)

This resolves the weak power-of-deficit statement, not Conjecture 14 on a polynomial additive gap to capacity. No claim is made about the source's other problems. Replay the two supporting checks with <code>sh replay.sh | diff -u RESULTS.txt -</code>.
