# Consecutive sum-freedom forces flat breaking

[Open Problem 3 of Rodríguez-Aldama, Šehović, Pasalic and Kudin](https://arxiv.org/html/2609.22394v3#S3.SS2) asks whether a binary vectorial function that is both \(k\)-th- and \((k-1)\)-st-order sum-free must break every \(k\)-flat, for \(k>3\). **Yes.** The argument holds for every \(k\ge3\) and arbitrary input and output dimensions. In fact, the image of each \(k\)-flat has affine span of dimension at least \(k+1\).

The proof records the sums on pairs of complementary hyperplanes as a linear map. Modulo the nonzero sum on the whole flat, that map is injective if every hyperplane sum is nonzero. The same map identifies exactly how zero-sum hyperplanes can occur when the local image span is smaller; a construction attains the resulting count bound on surjective flat images.

[Proof](PROOF.md) · [Sources and scope](SOURCES.md) · [Replay output](RESULTS.txt)

This is a finite-geometry result for arbitrary functions on binary vector spaces, not a statement about the security of a construction. It does not use APNness or any assumption that a function is a permutation. To replay the two checks, run <code>sh replay.sh | diff -u RESULTS.txt -</code>.
