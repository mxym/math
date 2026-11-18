# Symmetries of the single-deletion incidence relation

Which relabelings of the input words and the output words preserve the information “the output can be obtained by deleting exactly one letter”? Even if both labelings are unknown, all multiplicities are hidden, and words of no other lengths are observed, the relation determines almost all of the labeling.

**Theorem.** For an alphabet of size q≥2 and input length n≥3, the two permutations must be induced by the same alphabet permutation, optionally followed by reversal of every word. Thus the group is S_q × C₂. For n=2, after an alphabet permutation, the mixed inputs ab and ba may be swapped independently for each unordered letter pair: the group is (C₂)^{q choose 2} ⋊ S_q. At n=1 it is S_q. In binary the group therefore has four elements for every n≥2.

The proof uses no probabilities or same-length substitution edges. Degree identifies constant words, the induced distances recover letter counts, and a path pins the orientation for inputs with a single exceptional symbol. Reconstruction from neighboring gaps then determines the binary action. Pair projections and consistency on triples give the general alphabet case. The original deletion-ball hypergraph and the fixed-length Levenshtein distance are classical.

A **separate corollary** answers the nondegenerate binary channel symmetry question preceding Pernice's Allerton 2022 Conjecture IV.3, hence the conjectured orbit bound of four. The all-length conclusion is a short application of Erdős–Sziklai–Torney's 2001 classification of the full word poset, **not** a new word-poset classification. The fixed-length all-output model is also distinguished from the one-deletion relation. None of the results computes capacity, identifies equal-entropy inputs, classifies the isolated confusability graph, or treats an arbitrary number of deletions.

- [Single-deletion incidence proof and boundary cases](PROOF.md)
- [Pernice's all-length group and the fixed-length full-support statement](FULL-CHANNEL.md)
- [Prior work and limits of the repository/literature search](SOURCES.md)
- [Independent internal mathematical review](REVIEW.md)
- [Recorded exact finite checks](CHECKS.txt)

Run `python -B -O verify.py` and `python -B -O independent.py` in this directory; both use only the standard library. The finite checks supplement, but do not replace, the proof.

AI-assisted research with an independent internal AI review. Not externally peer-reviewed; no priority claim.
