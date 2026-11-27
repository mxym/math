# Primary sources and scope

- **Question:** Gautam Chandrasekaran, Jesse Goodman and David
  Zuckerman, [Quadratic Extractors](https://arxiv.org/html/2611.07266v1),
  §11 first structural question. The source proposes decomposing a
  high-min-entropy degree-d source into high-entropy degree-(d-1)
  sources or high (d-1)-st-derivative-entropy sources. Its quadratic
  antecedents are Theorem 3.7 / §5.1 (injective generation) and
  Theorem 5.1 / §5.2 (general, with smoothing). The present theorem
  addresses the affine-restriction formulation for every fixed d
  with exact decomposition for injective generators and bounded TV
  loss in general. Independent direction tuples are necessary over
  F_2, because dependent ones give identically zero higher
  directional derivatives. The complementary §11 questions about
  rank combiners and f(X+Y), and the transfer to a new disperser
  using Appendix A, are not claimed here. Other identifiers:
  [ePrint 2026/2775](https://eprint.iacr.org/2026/2775),
  [ECCC TR26-303](https://eccc.weizmann.ac.il/report/2026/303/).
- **Main external theorem and attribution:** Luka Milićević,
  [Low-codimensional Subvarieties Inside Dense Multilinear Varieties](https://arxiv.org/html/2512.14529v1),
  §1 Definition and Theorem 2, proved using Lemmas 3–5 and Claim 6.
  The theorem is stated over prime fields; it includes F_2, with the
  same arity constant irrespective of ambient block dimensions.
  The defining equations are scalar multilinear forms that may use
  only a subset of the coordinate blocks. The codimension is an
  upper bound on their number. A variety of density c contains
  a subvariety of this kind given by at most K_d(log2(1/c)+1)
  forms over F_2. The published proceedings citation is EuroComb
  2025, pp. 904–909, confirmed on the
  [author's publication list](https://www.mi.sanu.ac.rs/~luka.milicevic/papers.html).
  In our application the set T=0 is the intersection of the scalar
  coordinate zero sets of T; thus it is exactly a variety in the
  source's sense, not merely a dense set of low-rank tuples.
  The quoted theorem is not itself new here. We give an explicitly
  quantified binary exposition in §6 of our proof.
- **Neighbouring rank work:** Luka Milićević
  [arXiv:1902.09830v2](https://arxiv.org/abs/1902.09830v2), Oliver
  Janzer [arXiv:1902.11207](https://arxiv.org/abs/1902.11207),
  Guy Moshkovitz and Daniel G. Zhu
  [arXiv:2211.05780v2](https://arxiv.org/abs/2211.05780v2), and
  Qiyuan Chen and Ke Ye [arXiv:2611.30721v1](https://arxiv.org/html/2611.30721v1)
  concern partition rank versus analytic rank. Chen–Ye's Theorem 1.1
  states the linear comparison even over small fields, and cites
  Milićević's dense-variety theorem in its proof. The present
  deduction does not rely on Chen–Ye or on any rank comparison;
  the density of the vector zero set alone suffices.
- **Source restrictions:** Eshan Chattopadhyay, Jesse Goodman and
  Mohit Gurumukhani,
  [Extractors for Polynomial Sources over F_2](https://arxiv.org/html/2309.11019),
  §4.1 Theorem 4.1, gives a different near-entropy-preserving input
  reduction. Our collision argument loses more input bits and
  gives exact injectivity in the much smaller retained pieces.
  Cohen–Tal [arXiv:1404.0654](https://arxiv.org/abs/1404.0654) and
  Haramaty–Shpilka [arXiv:0908.2853](https://arxiv.org/abs/0908.2853)
  are structural neighbours on low-degree polynomial restrictions
  and biased scalar polynomials, not the present dichotomy for
  arbitrarily many output coordinates.
- **Earlier companion:** [Elementary cubic-source decomposition](https://github.com/mxym/math/blob/696d29df8042572dec4988809b315fe1aa6df596/research/cubic-source-decomposition/PROOF.md).
  It uses Chang's large-spectrum estimate and even convolution, has
  an explicit dimension threshold O(m^4/log m), and does not use
  the higher-arity dense-variety theorem. It is kept as a separate
  proof and not replaced by the present supplement.

The checked literature did not yield the same all-degrees
affine-restriction dichotomy or its matching entropy exponent.
The check was bounded to these primary texts and targeted queries
on CGZ, derivative entropy, and multilinear varieties, not a
worldwide priority claim. The lower bound in §5 concerns affine
restrictions of a given generator, not arbitrary reparametrisations.
The statements here are about finite-field randomness-source
structure and do not assert a vulnerability or any deployed scheme
property.
