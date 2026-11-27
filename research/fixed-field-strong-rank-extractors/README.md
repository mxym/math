# Fixed-field exact-output rank extractors: strong loss and the uniform benchmark

A weak extractor counts how many restrictions lose rank. A strong extractor counts how many ranks they lose in total. For any fixed prime-power field and all test dimensions `1 ≤ r ≤ k`, the [earlier weak construction at its pinned commit](https://github.com/mxym/math/tree/d0ba6f9a1d42bf94b915506f320cefe5e6490729/research/fixed-field-weak-rank-extractors) already has mean loss below 1145/1344 in the binary case and below 25/[24(q−1)] over larger fields. The output dimension equals the test dimension.

A tunable variant approximates both the mean loss and injectivity probability of a uniform square matrix, to any prescribed additive accuracy, on **every** test subspace. Its size is linear in the ambient dimension and singly exponential in the test dimension for fixed field and accuracy. This is not a claim about the full rank distribution. Filtering for globally surjective seeds preserves the one-sided guarantees, not necessarily the two-sided approximation.

[Proof, parameters and minimax reference](PROOF.md) · [Sources and limits of the claim](SOURCES.md) · [Finite checks](RESULTS.txt)

Run `sh replay.sh | diff -u RESULTS.txt -` (Python 3, standard library). Guo–Raj–Shangguan–Zhang §7 item 5 asks for a weak extractor; the strong and tunable versions are strengthenings, not additional problems posed there. The separately frozen weak package has not been modified.
