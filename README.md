# Unbounded distance for Chow graphical codes under subdivision

Let \(G_t\) be the simple graph obtained from \(K_4\) by replacing every edge with a path of \(3^t\) edges, with disjoint new internal vertices. For every integer \(t\ge 0\), Chow's edge-indexed symplectic matroid \(\mathcal S(G_t)\) has an explicit isotropic representation over the **same field** \(\mathbb F_8\), giving a stabilizer code with exact parameters
\[
[[\,6\cdot 3^t,\ 2,\ 2^{t+1}\,]]_8 .
\]
This answers the unbounded-distance clause of [Ganguly, arXiv:2611.27300v2, §VI, Open Problem 1](https://arxiv.org/html/2611.27300v2#S6) affirmatively, even for subdivisions of a single 3-connected simple graph. It does not characterize the full characteristic-two rate–distance region or establish optimality of the distances among all representations.

The ordinary stabilizer concatenation step is standard. The extra issue is compatibility with **every** admissible set of the signed graph matroid. The proof uses a ported representation of Chow's four-cycle. A partially chosen path contributes independent columns; a fully chosen path contributes two local pivots and the outer edge column selected by the path's star parity. The same port interface ensures that every nonzero local logical label costs exactly two sites. This gives independent upper and lower distance arguments at every iteration.

[Proof](PROOF.md) · [Sources and scope](SOURCES.md) · [Recorded output](RESULTS.txt)

Run the two exact standard-library Python 3 checks with the manifest verification:

    sh replay.sh | diff -u RESULTS.txt -

The first check directly tests signed subgraphs against the constructed matrices and scans supported normalizer quotient ranks. The second uses independently enumerated module words, different generators for the same concatenated row space, an exact grouped census of **all** size-16 admissible sets at \(t=1\), and literal error syndromes. Finite checks supplement the proof, not the other way around.
