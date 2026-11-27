# Primary sources and comparison

- Zeyu Guo, Roshan Raj, Chong Shangguan, and Zihan Zhang,
  [*Explicit Rank Extractors and Subspace Designs via Function Fields,
  with Applications to Strong Blocking Sets*, arXiv:2604.13431v2](https://arxiv.org/html/2604.13431v2#S7).
  Section 7 item 5 asks for a fixed-field, weak exact-output-rank
  construction with \(1-L/n\ge2^{-o(r)}\). Section 1 counts indices,
  distinguishes the weak guarantee from aggregate rank loss, and
  defines explicitness in footnote 1 as polynomial in the dimension,
  field and output-size parameters. Section 5.1 and the general case
  of §5.3 give the comparison via determinant multilinearity;
  Appendix A is non-explicit. Item 5 does not set an upper bound on
  \(n\). Here \(n\) is exponential in \(r\), linear in \(k\), not
  asserted polynomial in \(k,r\). Section 6.2 uses the same small-bias
  subspace-indicator lemma for strong blocking sets, not a distribution
  of rank-preserving matrices.
- Akhil Jalan and Dana Moshkovitz, [*Near-Optimal Cayley Expanders for
  Abelian Groups*, arXiv:2105.01149v1](https://arxiv.org/pdf/2105.01149v1),
  Theorem 1.1 and §3.4. Their Cayley character eigenvalue bound gives
  small bias on labelled generators. Their Proposition 4.5 already
  uses small bias to estimate the single test that a linear map kills
  a random vector; we do not claim the character estimate as new.
  The binary alternative is Amnon Ta-Shma, [*Explicit, Almost Optimal,
  Epsilon-Balanced Codes*](https://www.cs.tau.ac.il/~amnon/Papers/T.STOC17.pdf).
- Victor Shoup, [*New Algorithms for Finding Irreducible Polynomials
  over Finite Fields*](https://www.shoup.net/papers/detirred.pdf),
  *Mathematics of Computation* 54 (1990), 435–447, gives deterministic
  polynomial time at fixed characteristic. The Moore nonsingularity
  argument is proved directly in this note. Moore evaluation of
  linearized polynomials is classical, as in E. M. Gabidulin,
  [*Theory of Codes with Maximum Rank Distance*](https://www.mathnet.ru/eng/ppi967).
- Michael Forbes and Venkatesan Guruswami, [*Dimension Expanders via
  Rank Condensers*, ECCC TR14-162](https://eccc.weizmann.ac.il/report/2014/162/),
  Proposition 8.5: the indicated extension-to-base-field reduction
  increases output dimension. Venkatesan Guruswami, Chaoping Xing, and
  Chen Yuan, [*Subspace Designs Based on Algebraic Function Fields*](https://arxiv.org/abs/1704.05992),
  Theorems 1.2 and 4.2: the former imposes a codimension gap; in the
  latter setting the codimension allowance \(rt\) equal to the test rank
  \(s\) forces \(r=1\) and \(t=s\) in their notation. Its stated bound
  then does not give a constant exact-rank success fraction at fixed
  field and growing test rank.
- Gil Cohen, Dean Doron, and Noam Goldgraber, [*Algebraic-Geometric
  Parvaresh–Vardy Subspace Designs and Rank Condensers*,
  arXiv:2609.32834v2](https://arxiv.org/html/2609.32834v2#S4.SS3),
  Corollaries 4.7–4.9: the arbitrary-field aggregate-defect bound does
  not imply a constant probability of defect zero for growing \(r\);
  their exact-output lossless corollary requires \(q>r/\delta\).
  Rohan Goyal, Venkatesan Guruswami, and Jun-Ting Hsieh,
  [*Explicit Constant-Alphabet Subspace Design Codes*](https://arxiv.org/abs/2604.15218),
  Theorem 1.1, controls average kernel intersection using a coordinate
  alphabet whose dimension over \(\mathbb F_q\) can be much larger than
  the test rank.
- Joshua Cook and Dana Moshkovitz, [*Time and Space Efficient
  Deterministic Decoders*, ECCC TR24-110](https://eccc.weizmann.ac.il/report/2024/110/),
  §7.3 of the original report, use small bias to construct line and
  affine-subspace samplers for density estimation. Their conclusion
  does not control the full-rank frequency of maps to the exact test
  dimension.

Searches covered exact-output finite-field rank extraction, small bias
on matrices, subspace design and sampler constructions, and
limited-independence rank tests. The cited work contains the construction
ingredients and related guarantees; the search found no matching stated
constant-success result in this fixed-field growing-rank comparison.
This is not a priority claim. The key calculation is to approximate
low-dimensional kernel events and retain the rank-two contributions
to the binary third-order correction. Applying small bias directly
to the \(rk\) matrix entries also proves the same probability bound
with an extra factor \(r\) in the size estimate before simplification;
the linearized representation needs at most \(3k\) coordinates.
