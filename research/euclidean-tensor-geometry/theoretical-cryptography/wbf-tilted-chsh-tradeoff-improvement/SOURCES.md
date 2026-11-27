# Sources and comparison scope

1. Lewis Wooltorton, Peter Brown, Omar Fawzi, *Chain rules for
   conditional entropies in quantum cryptography: limitations and
   improvements*, [arXiv:2605.29787v1](https://arxiv.org/html/2605.29787v1)
   (28 May 2026, v1 only as checked on 27 November 2026).
   Equation (31) is the partially optimized entropy. Definition
   5.1 is the new-side-information condition, and Definition 5.2 /
   Equation (34) are the common-instrument infrequent-sampling model.
   Corollary 5.3 and Equation (35), including the immediately preceding
   unoptimized objective, are the precise mathematical comparison in
   this note, with the common class of allowed tensor-separated behaviors;
   the fixed-channel form and its optional enlargement are separated in
   Appendix C.6, Equations (85)–(87) and the preceding paragraph.
   We use the usual KL support convention (finite only if the
   first distribution is supported on the second). Section 5.2 points to settings with unequal conditional
   entropies and reports a heuristic investigation for \(I_{3322}\);
   Section 6's final two paragraphs ask which protocols benefit from
   the new EAT. We address that application question by a tilted-CHSH
   example with a uniform gap after the indicated infima, not merely
   at one strategy. We do not address their general Question 1 or
   Section 6's separate question comparing families of strategies.

2. Amir Arqand, Thomas A. Hahn, Ernest Y.-Z. Tan, *Generalized Rényi
   entropy accumulation theorem and generalized quantum probability
   estimation*, [Phys. Rev. X 15, 041013 (2025)](https://doi.org/10.1103/pgrn-mz9j),
   [arXiv:2405.05912v4](https://arxiv.org/abs/2405.05912v4).
   WBF Section 5.2 cites journal Equation (93). The corresponding
   simplified infrequent-sampling formula in the accessible arXiv v4
   is Equation (101), with its applicable special case and a discussion
   of DI uses immediately following in Section 5.2.1. Its Equation (93)
   instead relates Rényi order parameters. We compare the two
   generation-only objectives **as displayed by WBF**. Our claim is
   only the two displayed objectives in WBF's controlled comparison,
   not dominance over every use or variant of this theorem.

3. Cédric Bamps and Stefano Pironio, *Sum-of-squares decompositions for
   a family of Clauser-Horne-Shimony-Holt-like inequalities and their
   application to self-testing*, [Phys. Rev. A 91, 052111 (2015)](https://doi.org/10.1103/PhysRevA.91.052111),
   [arXiv:1504.06960](https://arxiv.org/abs/1504.06960), notably their tilted
   CHSH operator, ideal qubit state and robust self-test. These ingredients
   are known; we give elementary Pauli-block estimates tailored to two
   outcome probabilities. Rajat Colbeck's CHSH-type randomness
   motivation and random input sampling methods themselves are not
   new here. For prior single-round and random-basis analysis see Peter
   Brown, Hamza Fawzi and Omar Fawzi, [*Computing conditional entropies for
   quantum correlations*](https://doi.org/10.1038/s41467-020-20018-1)
   and Pavel Sekatski et al., [*Device-independent quantum key
   distribution with random key basis*](https://doi.org/10.1038/s41467-021-23147-3).
   These do not compare the two WBF infrequent-sampling objectives.

4. Salman Beigi, [*Sandwiched Rényi divergence satisfies data processing
   inequality*](https://arxiv.org/abs/1306.5920), Theorems 6 and 7,
   for data processing and order monotonicity. The computation (9)
   uses only standard pretty-good measurement algebra, included
   explicitly in the proof. No originality claim for Jensen's
   inequality, the Bell-state identification, PGM, or Pinsker.

Bounded prior-art check, 27 November 2026: original v1 section text
including the LaTeX subscript label for \(I_{3322}\); queried the exact
arXiv number and author-title with “tilted CHSH”, “partially optimized”,
“spot-checking”, “strict” and “entropy accumulation”, and checked the
closely related literature above and indexed TrureTuring matches.
No matching arbitrary-dimension strict separation of these two
optimized objectives for an accepted-frequency region was found.
This is a bounded search, not a priority assertion. All interpretation
is within the two fixed theoretical security bounds and the standard
separated-device model.
