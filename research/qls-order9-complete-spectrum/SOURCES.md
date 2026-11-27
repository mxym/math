# Primary sources and input provenance

* Yuyuan Zhang, Mingzhen Lv and Haitao Cao, [*On the possible
  cardinalities of quantum Latin squares*, arXiv:2607.19969v2](https://arxiv.org/html/2607.19969v2#S5).
  Section 5, Table 6 lists the order-nine unsettled cases
  34, 60–62, 65–71, 73, 74. The other attainable values used in
  the final spectrum are the values reported in the same row.
  Theorem 1.1(1) states the general \(n+1\) impossibility;
  Theorem 1.2 does not cover order nine.
* Pekka H. J. Lampio, Patric R. J. Östergård and Ferenc Szöllősi,
  [*Orderly generation of Butson Hadamard matrices*, Math. Comp. 89 (2020), 313–331](https://doi.org/10.1090/mcom/3453),
  [arXiv:1707.02287](https://arxiv.org/abs/1707.02287).
  Use their [official Aalto monomial-equivalence catalog](https://wiki.aalto.fi/spaces/Butson/pages/120482304/Matrices%2Bup%2Bto%2Bmonomial%2Bequivalence),
  row \(n=9\), column \(q=6\), linked [BH-9-6.txt v1 attachment](https://wiki.aalto.fi/download/attachments/120482261/BH-9-6.txt?api=v2&modificationDate=1499265159731&version=1).
  The 17 records are used in file order with 1-based indices.
  Each is a six-character literal header BH1996 followed by 81
  exponents 0–5 in row-major order. Canonicalize line endings to LF
  and include a final LF: 1496 canonical ASCII bytes,
  SHA-256 e6b0c65c17700e3d9a5141b5ba74e025cbbde9d39809a25b89c98ef1083ff5a7.
  This hash is for record-normalized bytes, not a claim about
  transport line endings. The public checked input is not redistributed.
  No new complex Hadamard matrix or classification is claimed.
* David J. Reutter and Jamie Vicary, [*Biunitary constructions in
  quantum information*, Higher Structures 3(1), 109–154 (2019)](https://doi.org/10.21136/HS.2019.04),
  Corollary 3.2.1, equation (41) and Figure 7(a) already give the
  two-Hadamard formula with the first factor transposed in indexing.
  Zhipeng Xu, [*New Cardinalities for Quantum Latin Squares of Order Six*,
  arXiv:2607.11800v3](https://arxiv.org/html/2607.11800v3), Proposition 1,
  uses the mixed Schur product directly and uses exact exponent
  signatures and row-permuted factors in Sections 7–9. We credit both.
* John J. Benedetto, Robert L. Benedetto and Joseph T. Woodworth,
  [*Optimal Ambiguity Functions and Weil's Exponential Sum Bound*, arXiv:1107.1887](https://arxiv.org/abs/1107.1887),
  Section 2, records the three-valued Björck quadratic-character
  construction over prime fields \(p\equiv1\bmod4\). Our
  nine-element-field instance uses the corresponding phase and is
  verified directly without assuming the prime-field statement
  covers nonprime field sizes.
* Aishwarya P. Das and Durgesh Kumar,
  [*A Quantum Latin Square of Order Six with Cardinality 29*, arXiv:2608.12607](https://arxiv.org/abs/2608.12607),
  uses a punctured square and an orthogonal diagonal summand for
  an order-six result. The block splice here is verified from its
  explicit row/column ingredients; only its stated order-nine
  applications are claimed new. It is also related to the
  incomplete-square and direct-sum themes in the preceding sources.
* Lin Huang and Yang Li,
  [*The Existence of Diagonal Quantum Latin Squares with Maximum
  Cardinality*, arXiv:2606.27758](https://arxiv.org/abs/2606.27758),
  and Yuyuan Zhang and Haitao Cao,
  [*Resolvable quantum Latin squares with maximal cardinality*, arXiv:2608.29201](https://arxiv.org/abs/2608.29201),
  concern maximum-cardinality designs with special additional
  conditions. These problems are distinct from the intermediate
  order-nine cardinalities here.

A bounded public search on 2026-11-27 checked the current source versions
and searched the Zhang–Lv–Cao title/identifier, “order nine”, “order 9”,
“quantum Latin square” and the missing cardinality values. No prior
publication of the thirteen witnesses or a full order-nine intermediate
spectrum surfaced. This is not a priority guarantee. We do not claim
anything about unresolved order-seven or order-eleven values.
