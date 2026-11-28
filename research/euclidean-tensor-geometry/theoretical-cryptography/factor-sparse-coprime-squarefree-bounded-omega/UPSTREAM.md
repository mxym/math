# Upstream sources and scope comparison

This file identifies the sources used to delimit the result.  It is an
original location/scope note; it does not reproduce any source text.

1. Joseph M. Shunia, *Deterministic integer factorization from abundance
   decisions*, arXiv:2611.34242v1 (25 November 2026).
   - PDF: https://arxiv.org/pdf/2611.34242v1
   - Lemma 3.2 gives totient recovery by a high-power divisor sum.
   - Theorem 3.1 and Algorithm 2 reconstruct general factorizations from
     \(O(\log n)\) consecutive power sums.
   - Section 3 records the cyclic-resultant viewpoint.
   - Theorem 1.2 supplies the abundance-to-exact-comparison reduction.

2. Lluis Eriksson, *Sharp Normalization Exponents, a 19x
   Rescaled-Vandermonde Contraction, Linear-Exponent Bounded-omega(n)
   Factoring, and Resolution of the c=1 Endpoint for Abundance-Oracle
   Factorization*, AIRR ARR-2026-1ZVBB45HG78WNVDH, v1 (27 November 2026).
   - Fixed PDF:
     https://airr.science/papers/ARR-2026-1ZVBB45HG78WNVDH/versions/v1/ARR-2026-1ZVBB45HG78WNVDH-v1.pdf
   - Canonical PDF SHA-256 recorded by AIRR:
     `c1bcf55a9afe5ac894558ee686acc4fabe430991031ce56c696e5bbe28c7f6d1`.
   - Theorem 1(a) sharpens normalization to
     \(J\ge\max(2,\lceil\log_2 n\rceil)\).
   - Theorem 2(a) uses \(2K\) consecutive divisor sums for bounded
     \(\omega(n)\le K\), allowing arbitrary multiplicities.
   - The present result uses fewer, sparse, pairwise-coprime indices but
     assumes squarefreeness.

3. Christopher J. Hillar, *Cyclic Resultants*, Journal of Symbolic
   Computation 39 (2005), 653--669; arXiv:math/0401220v3.
   - https://arxiv.org/pdf/math/0401220v3
   - This characterizes equality of full cyclic-resultant sequences and
     gives reconstruction methods; it does not state the present
     fixed-endpoint, \(K-2\)-index finite-fiber theorem.

4. Christopher J. Hillar and Lionel Levine, *Polynomial recurrences and
   cyclic resultants*, Proceedings of the AMS 135 (2007), 1607--1618;
   arXiv:math/0411414v4.
   - https://arxiv.org/pdf/math/0411414v4
   - This gives finite initial-segment bounds for generic monic
     polynomials (and discusses the \(d+1\) conjectural scale), not the
     pairwise-coprime sparse-index construction here.

5. Eric Bach, Gary L. Miller, and Jeffrey Shallit, *Sums of divisors,
   perfect numbers and factoring*, SIAM Journal on Computing 15 (1986),
   1143--1154.
   - https://www.cs.cmu.edu/~glmiller/Publications/Papers/BMS86.pdf
   - A single ordinary divisor sum supports randomized polynomial-time
     factoring.  That is a different algorithmic model from this
     deterministic fixed-\(K\) squarefree result.

No source located in this search states the exact theorem proved here.
That negative search is not an absolute priority claim.
