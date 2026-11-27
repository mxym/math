# Sources and scope

- **Direct problem:** Gautam Chandrasekaran, Jesse Goodman and David
  Zuckerman, [Quadratic Extractors](https://arxiv.org/html/2611.07266v1),
  §11 first structural question, with §5.1 (Theorem 3.7 in §3.4)
  and §5.2 (Theorem 5.1) as the quadratic precedents. The authors ask
  about decomposing degree-d sources into lower-degree high-entropy
  sources or high (d−1)-st-derivative-entropy sources. We obtain the
  stated quantitative d=3 result for linearly independent pairs of
  directions, exact for injective generators and approximate for
  arbitrary high-min-entropy cubic sources. Repeated directions would
  make the condition impossible in characteristic two. The separate
  §11 directions on tensor analogues of rank combiners and extraction
  from f(X+Y) are not resolved here. No improved disperser is claimed
  from Appendix A without a further argument. The paper is also
  listed as [ePrint 2026/2775](https://eprint.iacr.org/2026/2775) and
  [ECCC TR26-303](https://eccc.weizmann.ac.il/report/2026/303/);
  section numbers above are pinned to the arXiv text.
- **Additive input, with proof included:** Mei-Chu Chang,
  [A Polynomial Bound in Freiman's Theorem](https://math.ucr.edu/~mcc/paper/111%20Freiman.pdf),
  and Russell Impagliazzo, Cristopher Moore, Alexander Russell,
  [An Entropic Proof of Chang's Inequality](https://arxiv.org/abs/1205.0263),
  give the underlying spectral dimension bound. We combine the
  elementary entropy proof with even convolution to get a subspace
  in a variable-length iterated sumset, and use this for a trilinear
  rank construction. The elementary Fourier and entropy estimates
  are not claimed as new. The fixed-fourfold Bogolyubov–Ruzsa lemma
  (Sanders [arXiv:1011.0107](https://arxiv.org/abs/1011.0107);
  binary formulation in Ben-Sasson–Lovett–Ron-Zewi, Theorem 5.1 of
  [ECCC TR12-135 rev. 2](https://eccc.weizmann.ac.il/report/2012/135/revision/2/download/))
  gives a weaker alternative dimension scale in this argument.
  The fixed-fold polynomial Bogolyubov conjecture is not needed.
- **Polynomial-source input reduction:** Eshan Chattopadhyay, Jesse
  Goodman and Mohit Gurumukhani,
  [Extractors for Polynomial Sources over F_2](https://arxiv.org/html/2309.11019),
  §4.1 Theorem 4.1; see also Lemma 4.14 and Lemma 4.18 in
  *Quadratic Extractors*. These treat conditioned input restrictions
  while retaining (possibly smooth) min-entropy. Here the collision
  calculation only needs injectivity of much smaller restrictions
  after dropping a controlled fraction of cosets; it does not give
  an improvement of their near-entropy-preserving input reduction.
- **Structural neighbours:** Elad Haramaty and Amir Shpilka,
  [On the Structure of Cubic and Quartic Polynomials](https://arxiv.org/abs/0908.2853),
  uses rank of derivatives to study biased scalar polynomials.
  Gil Cohen and Avishay Tal,
  [Two Structural Results for Low Degree Polynomials and Applications](https://arxiv.org/abs/1404.0654),
  study affine partitions and subspaces for low-degree polynomials.
  The new low-rank iteration uses a vector-valued alternating
  trilinear map and does not assume a single biased scalar polynomial
  or enough equations to force all coordinates to be constant.
  Arnab Bhattacharyya et al.,
  [Average Bias and Polynomial Sources](https://arxiv.org/abs/1905.11612),
  is a Fourier/entropy theorem for quadratic sources, a different
  notion than the simultaneous second-direction ranks here.

A bounded search of the cited primary papers, arXiv/ECCC and
TrureTuring for the source identifier, the exact issue, and cubic
derivative-entropy/affine-restriction dichotomies located no direct
duplicate. This is not a claim of exhaustive worldwide priority.
The constructive-sounding choice of subspaces in the proof asserts
existence, not an efficient algorithm for finding them. This is a
finite-field randomness-source theorem, not an assertion about a
deployed scheme or about recovering any secret.
