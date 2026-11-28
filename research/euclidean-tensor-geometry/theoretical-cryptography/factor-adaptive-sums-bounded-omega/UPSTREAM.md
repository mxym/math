# Upstream sources and exact scope

This is an original source-location and scope note. It does not reproduce
source text.

1. Joseph M. Shunia, *Deterministic integer factorization from abundance
   decisions*, arXiv:2611.34242v1 (25 November 2026).
   - Fixed PDF: https://arxiv.org/pdf/2611.34242v1
   - Lemma 3.2 gives high-power normalization/totient recovery.
   - Theorem 3.1 uses \(2\lceil\log_2n\rceil\) consecutive high-power
     divisor sums for unrestricted deterministic factorization.
   - Section 3 points out the cyclic-resultant formulation.
   - It does not give the fixed-\(K\), instance-adaptive
     theorem proved here.

2. Lluis Eriksson, *Sharp Normalization Exponents, a 19x
   Rescaled-Vandermonde Contraction, Linear-Exponent Bounded-omega(n)
   Factoring, and Resolution of the c=1 Endpoint for Abundance-Oracle
   Factorization*, AIRR ARR-2026-1ZVBB45HG78WNVDH, v1 (27 November 2026).
   - Canonical PDF:
     https://airr.science/papers/ARR-2026-1ZVBB45HG78WNVDH/ARR-2026-1ZVBB45HG78WNVDH-v1.pdf
   - PDF SHA-256:
     \`c1bcf55a9afe5ac894558ee686acc4fabe430991031ce56c696e5bbe28c7f6d1\`.
   - Theorem 1(a) gives the sufficient normalization threshold used here.
   - Theorem 2(a) gives \(2K\) consecutive sums for
     \(\omega(n)\le K\), allowing arbitrary multiplicities.
   - It does not state the present instance-adaptive sparse result.

3. The frozen neighboring package
   \`factor-kminus2-sums-bounded-omega\`.
   - It proves that \(K-2\) predetermined sparse sums suffice for every
     \(\omega(n)\le K\) input with arbitrary multiplicities.
   - The present proof adds the normalized-totient equation to the same
     product-projective system. This removes one more boundary slot in every
     nonuniform or multiblock case and yields an exact sufficient budget for
     each structural split; the maximal uniform case retains the old
     \(K-2\) budget.
   - The proof here is self-contained; the neighboring package is cited as
     the frozen antecedent, not used as a mutable runtime dependency.

4. Bartosz Żrałek, *A deterministic version of Pollard's p-1 algorithm*,
   arXiv:0707.4102v5 (12 May 2009).
   - Fixed PDF: https://arxiv.org/pdf/0707.4102v5
   - Section 6, printed/PDF page 14, discusses Landau's equal-order split
     using totient-oracle information.
   - That is a prior structural ingredient, not the sparse divisor-sum
     theorem or the boundary argument here.

5. Christopher J. Hillar, *Cyclic Resultants*, Journal of Symbolic
   Computation 39 (2005), 653--669; arXiv:math/0401220v3.
   - https://arxiv.org/pdf/math/0401220v3
   - This studies equality and reconstruction from cyclic-resultant
     sequences, not the bounded-\(\omega\) product-projective fiber here.

6. Christopher J. Hillar and Lionel Levine, *Polynomial recurrences and
   cyclic resultants*, Proceedings of the AMS 135 (2007), 1607--1618;
   arXiv:math/0411414v4.
   - https://arxiv.org/pdf/math/0411414v4
   - This gives generic finite-initial-segment results, not the explicit
     arbitrary-multiplicity exceptional classification proved here.

7. Matthias Aschenbrenner, *Ideal Membership in Polynomial Rings over the
   Integers*, Journal of the AMS 17 (2004), 407--441;
   arXiv:math/0305172.
   - https://arxiv.org/pdf/math/0305172
   - Section 6, especially (6.1), supplies a standard fixed-dimensional
     field-case cofactor-degree bound for the deterministic elimination
     step.

No matching statement was found in this source and repository search. That
negative search is not an absolute priority claim. The positive theorem is
an exact-oracle result; the displayed positive-dimensional fibers are
only obstacles to this algebraic system, not an information-theoretic or integer lower
bound.
