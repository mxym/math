# Upstream sources and exact scope

This is an original source-location and scope note. It does not reproduce
source text.

1. Joseph M. Shunia, *Deterministic integer factorization from abundance
   decisions*, arXiv:2611.34242v1 (25 November 2026).
   - Fixed PDF: https://arxiv.org/pdf/2611.34242v1
   - Lemma 3.2 gives high-power normalization/totient recovery.
   - Theorem 3.1 reconstructs unrestricted factorizations from
     \(2\lceil\log_2 n\rceil\) consecutive high-power divisor sums.
   - Section 3 notes the cyclic-resultant viewpoint.
   - It does not state a fixed-\(K\), \(K-2\)-query,
     arbitrary-multiplicity theorem.

2. Lluis Eriksson, *Sharp Normalization Exponents, a 19x
   Rescaled-Vandermonde Contraction, Linear-Exponent Bounded-omega(n)
   Factoring, and Resolution of the c=1 Endpoint for Abundance-Oracle
   Factorization*, AIRR ARR-2026-1ZVBB45HG78WNVDH, v1 (27 November 2026).
   - Fixed PDF:
     https://airr.science/papers/ARR-2026-1ZVBB45HG78WNVDH/ARR-2026-1ZVBB45HG78WNVDH-v1.pdf
   - Canonical PDF SHA-256:
     \`c1bcf55a9afe5ac894558ee686acc4fabe430991031ce56c696e5bbe28c7f6d1\`.
   - Theorem 1(a) gives the sharp normalization threshold
     \(J\ge\max(2,\lceil\log_2n\rceil)\).
   - Theorem 2(a) gives \(2K\) consecutive sums for
     \(\omega(n)\le K\), allowing arbitrary multiplicities.
   - The present theorem uses \(K-2\) sparse predetermined sums for the
     same bounded-\(\omega\), arbitrary-multiplicity input class.

3. The neighboring package
   \`factor-sparse-coprime-squarefree-bounded-omega\` in this repository.
   - It proves a \(K-2\)-query theorem under squarefreeness by a single
     projective coefficient-space argument.
   - The present proof removes squarefreeness. It first extracts known
     equal-exponent blocks from \(n,\varphi(n)\), represents the unknown
     complement by prime variables, and uses a product-projective
     boundary budget.

4. The neighboring packages
   \`factor-one-sum-three-prime-powers\` and
   \`factor-two-sums-four-prime-powers\`.
   - They prove the arbitrary-multiplicity cases \(K=3\) and \(K=4\)
     by explicit low-dimensional eliminants.
   - They are strict special cases of the theorem here and supply useful
     independent checks, but the product-projective proof is uniform in
     every fixed \(K\ge3\).

5. Christopher J. Hillar, *Cyclic Resultants*, Journal of Symbolic
   Computation 39 (2005), 653--669; arXiv:math/0401220v3.
   - https://arxiv.org/pdf/math/0401220v3
   - This studies equality and reconstruction from cyclic-resultant
     sequences, not the blockwise sparse finite-fiber theorem here.

6. Christopher J. Hillar and Lionel Levine, *Polynomial recurrences and
   cyclic resultants*, Proceedings of the AMS 135 (2007), 1607--1618;
   arXiv:math/0411414v4.
   - https://arxiv.org/pdf/math/0411414v4
   - This gives finite initial-segment results for generic monic
     polynomials, not the arbitrary-multiplicity \(K-2\) construction.

7. Bartosz Żrałek, *A deterministic version of Pollard's p-1 algorithm*,
   arXiv:0707.4102v5 (12 May 2009).
   - Fixed PDF: https://arxiv.org/pdf/0707.4102v5
   - Section 6, printed/PDF page 14, cites Landau's equal-order
     factorization using at most \(\omega(n)-2\) totient-oracle calls,
     including \(\varphi(n)\), and states the single-totient
     nonuniform three-prime-power case.
   - The elementary \(R,U,V\) split used here is compatible with that
     prior analysis, but no additional totient query is made.

8. François Morain, Guénaël Renault, and Benjamin Smith,
   *Deterministic factoring with oracles*, Applicable Algebra in
   Engineering, Communication and Computing 34(4) (2023), 663--690;
   arXiv:1802.08444v2.
   - https://arxiv.org/pdf/1802.08444v2
   - Section 6.3 gives every squarefree three-prime integer from the two
     different ordinary values \(\varphi(N)\) and \(\sigma(N)\).
   - It does not give the theorem here.

9. Eric Bach, Gary L. Miller, and Jeffrey Shallit, *Sums of divisors,
   perfect numbers and factoring*, SIAM Journal on Computing 15 (1986),
   1143--1154.
   - https://www.cs.cmu.edu/~glmiller/Publications/Papers/BMS86.pdf
   - A single ordinary divisor sum supports randomized polynomial-time
     factoring, a different algorithmic model.

10. Matthias Aschenbrenner, *Ideal Membership in Polynomial Rings over
    the Integers*, Journal of the AMS 17 (2004), 407--441;
    arXiv:math/0305172.
    - https://arxiv.org/pdf/math/0305172
    - Section 6, especially (6.1), records a fixed-dimensional
      field-case effective Nullstellensatz/cofactor degree bound used
      only for the deterministic elimination complexity.

No matching statement was found in this source and repository search. That
negative search is not an absolute priority claim.
