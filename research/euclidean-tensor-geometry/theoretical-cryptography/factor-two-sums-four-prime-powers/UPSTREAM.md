# Upstream sources and exact scope

This is an original source-location and scope note. It does not reproduce
source text.

1. Bartosz Żrałek, *A deterministic version of Pollard's p-1 algorithm*,
   arXiv:0707.4102v5 (12 May 2009).
   - Fixed PDF: https://arxiv.org/pdf/0707.4102v5
   - Section 6, printed/PDF page 14:
     - \(p^\alpha q^\beta\) is deterministically factorable from
       \(n,\varphi(n)\);
     - Landau's equal-order decomposition uses at most
       \(\omega(n)-2\) totient-oracle calls, including \(\varphi(n)\);
     - the paper explicitly states that a three-prime-power integer with
       exponents not all equal is deterministically factorable from the
       single value \(\varphi(n)\).
   - Those are prior ingredients, not contributions of this package.
   - They do not state the two-divisor-sum, all-multiplicity
     \(\omega(n)\le4\) theorem or the \(2+2\) eliminant here.

2. Susan Landau, *Some remarks on computing the square parts of integers*,
   Information and Computation 78 (1988), 246--253,
   DOI: 10.1016/0890-5401(88)90026-3.
   - This is the equal-order/square-parts oracle antecedent cited by
     Żrałek. The present package gives the elementary split it actually
     uses and does not claim Landau's oracle result as new.

3. Joseph M. Shunia, *Deterministic integer factorization from abundance
   decisions*, arXiv:2611.34242v1 (25 November 2026).
   - Fixed PDF: https://arxiv.org/pdf/2611.34242v1
   - Lemma 3.2 gives high-power normalization/totient recovery.
   - Theorem 3.1 uses \(2\lceil\log_2n\rceil\) consecutive divisor sums
     for unrestricted deterministic factorization.
   - Section 3 notes the cyclic-resultant viewpoint.
   - It does not state a two-sum arbitrary-multiplicity
     \(\omega(n)\le4\) theorem.

4. Lluis Eriksson, *Sharp Normalization Exponents, a 19x
   Rescaled-Vandermonde Contraction, Linear-Exponent Bounded-omega(n)
   Factoring, and Resolution of the c=1 Endpoint for Abundance-Oracle
   Factorization*, AIRR ARR-2026-1ZVBB45HG78WNVDH, v1 (27 November 2026).
   - Fixed PDF:
     https://airr.science/papers/ARR-2026-1ZVBB45HG78WNVDH/versions/v1/ARR-2026-1ZVBB45HG78WNVDH-v1.pdf
   - Canonical PDF SHA-256:
     \`c1bcf55a9afe5ac894558ee686acc4fabe430991031ce56c696e5bbe28c7f6d1\`.
   - Theorem 1(a) gives the sharp normalization threshold
     \(J\ge\max(2,\lceil\log_2n\rceil)\).
   - Theorem 2(a) gives \(2K\) consecutive sums for bounded
     \(\omega(n)\le K\), with arbitrary multiplicities; at \(K=4\) this
     is eight sums.
   - It does not state the present two-sum result.

5. Christopher J. Hillar, *Cyclic Resultants*, Journal of Symbolic
   Computation 39 (2005), 653--669; arXiv:math/0401220v3.
   - https://arxiv.org/pdf/math/0401220v3
   - This studies equality and reconstruction from cyclic-resultant
     sequences, not the present fixed-endpoint two-index quartet theorem.

6. Christopher J. Hillar and Lionel Levine, *Polynomial recurrences and
   cyclic resultants*, Proceedings of the AMS 135 (2007), 1607--1618;
   arXiv:math/0411414v4.
   - https://arxiv.org/pdf/math/0411414v4
   - This gives finite initial-segment results for generic monic
     polynomials, not the present multiplicity split or \(2+2\) eliminant.

7. Eric Bach, Gary L. Miller, and Jeffrey Shallit, *Sums of divisors,
   perfect numbers and factoring*, SIAM Journal on Computing 15 (1986),
   1143--1154.
   - https://www.cs.cmu.edu/~glmiller/Publications/Papers/BMS86.pdf
   - One ordinary divisor sum supports randomized polynomial-time
     factoring. This differs from the deterministic bounded-\(\omega\)
     result here.

8. François Morain, Guénaël Renault, and Benjamin Smith,
   *Deterministic factoring with oracles*, Applicable Algebra in
   Engineering, Communication and Computing 34 (2023), 423--443;
   arXiv:1802.08444v2.
   - https://arxiv.org/pdf/1802.08444v2
   - Section 6.3 gives deterministic factorization of every squarefree
     three-prime integer from the two different ordinary-oracle values
     \(\varphi(N)\) and \(\sigma(N)\). Its size hypotheses occur in other
     results. It does not give the theorem here.

No matching statement was found in this source search. That negative search
is not an absolute priority claim.
