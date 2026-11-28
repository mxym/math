# Upstream sources and exact scope

This is an original source-location and scope note. It does not reproduce
source text.

1. Bartosz Żrałek, *A deterministic version of Pollard's p-1 algorithm*,
   arXiv:0707.4102v5 (12 May 2009).
   - Fixed PDF: https://arxiv.org/pdf/0707.4102v5
   - Section 6, printed page 14 (PDF page 14), especially the paragraph
     at extracted lines 1355--1385:
     - integers \(p^\alpha q^\beta\) are deterministically factorable from
       \(n,\varphi(n)\);
     - Landau's equal-order decomposition uses at most
       \(\omega(n)-2\) totient calls, including \(\varphi(n)\);
     - the paper explicitly states that
       \(p^\alpha q^\beta r^\gamma\) with exponents not all equal is
       deterministically factorable from the single value \(\varphi(n)\)
       in \(O((\log n)^3)\).
   - These are prior results, not contributions of this package.

2. Joseph M. Shunia, *Deterministic integer factorization from abundance
   decisions*, arXiv:2611.34242v1 (25 November 2026).
   - Fixed PDF: https://arxiv.org/pdf/2611.34242v1
   - Lemma 3.2 recovers the totient from a high-power divisor sum.
   - Theorem 3.1 uses \(2\lceil\log_2 n\rceil\) consecutive divisor sums
     for general deterministic factorization.
   - Theorem 1.2 converts abundance decisions into exact divisor-sum
     comparisons.
   - The squarefree cyclic-resultant identity is noted after Theorem 3.1.

3. Lluis Eriksson, *Sharp Normalization Exponents, a 19x
   Rescaled-Vandermonde Contraction, Linear-Exponent Bounded-omega(n)
   Factoring, and Resolution of the c=1 Endpoint for Abundance-Oracle
   Factorization*, AIRR ARR-2026-1ZVBB45HG78WNVDH, v1 (27 November 2026).
   - Fixed PDF:
     https://airr.science/papers/ARR-2026-1ZVBB45HG78WNVDH/versions/v1/ARR-2026-1ZVBB45HG78WNVDH-v1.pdf
   - Canonical PDF SHA-256:
     c1bcf55a9afe5ac894558ee686acc4fabe430991031ce56c696e5bbe28c7f6d1
   - Theorem 1(a) gives the normalization threshold
     \(J\ge\max(2,\lceil\log_2 n\rceil)\).
   - Theorem 2(a) gives a general bounded-\(\omega(n)\) method with
     \(2K\) consecutive divisor sums and arbitrary multiplicities; for
     \(K=3\), that sufficient bound is six sums.
   - It does not state the one-sum all-multiplicity triprime corollary.

4. Eric Bach, Gary L. Miller, and Jeffrey Shallit, *Sums of divisors,
   perfect numbers and factoring*, SIAM Journal on Computing 15 (1986),
   1143--1154.
   - https://www.cs.cmu.edu/~glmiller/Publications/Papers/BMS86.pdf
   - One ordinary divisor sum supports randomized polynomial-time
     factoring. This is a different model and proof.

5. François Morain, Guénaël Renault, and Benjamin Smith,
   *Deterministic factoring with oracles*, Applicable Algebra in
   Engineering, Communication and Computing 34 (2023), 423--443;
   arXiv:1802.08444v2.
   - https://arxiv.org/pdf/1802.08444v2
   - This studies deterministic factoring from \(\varphi(n)\) or
     \(\sigma(n)\) under size restrictions and does not state the present
     one-high-power-sum, all-multiplicity \(\omega(n)\le3\) theorem.

No matching statement was found in this source search. That negative search
is not an absolute priority claim.
