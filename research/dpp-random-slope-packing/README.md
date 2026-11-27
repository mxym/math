# Large-field dot-product proofs by modular slope packing

For every Boolean circuit of size \(S\) and \(0<\varepsilon<1\), there
is a perfectly complete promise dot-product proof with soundness at most
\(\varepsilon\) and proof length \(O(S\log(2S/\varepsilon))\) over every
prime field of order
\[
P\ \ge\ C\, S^6\log^3(2S/\varepsilon)/\varepsilon^6
\]
for a universal constant \(C\). Soundness covers every fixed alleged
proof over \(\mathbb F_P\) for each false **Boolean** input. There is a
single linear query to the concatenated input and proof, followed by
efficient membership testing of the verifier's accepting set.

This gives the pair \((a,b)=(6,6)\) in the question of reducing the
\(S\)-exponent in Bitansky–Harsha–Ishai–Rothblum–Wu, Theorem 1.3
([author manuscript](https://www.cs.utexas.edu/~dwu4/papers/DPP.pdf);
[AICR c/0070](https://aicr.info/c/0070/)). The two-query proof and the
bounded embedding are from that paper. The change is at the packing
step: sample a slope throughout the target field, allow ambiguity on a
small fraction of slopes, and count the lattice fiber in deterministic
time polynomial in \(\log P\), using the Euclidean algorithm. No
random-walk estimate or new underlying two-query proof is used.

The result answers the named improvement inequality relative to the
stated Theorem 1.3. It does not claim an optimal exponent, strong or
reusable soundness for this instantiation, soundness outside the
Boolean promise, or an improvement to a deployed argument system.
The TCC 2026 *Dot-Product Proofs of Powers* chapter is a relevant
follow-up; only its public preview was available for checking. No
priority over that chapter or final literature status for c/0070
is asserted; see [SOURCES.md](SOURCES.md).

- [PROOF.md](PROOF.md): black-box packing lemma, deterministic decoder,
  and exact parameter substitution.
- [SOURCES.md](SOURCES.md): source theorem anchors and prior work.
- [RESULTS.txt](RESULTS.txt): two verification passes, including
  independent modular-inverse reference checks.

Replay with Python 3.8+ and no external dependencies:
`sh replay.sh | diff -u RESULTS.txt -`.
