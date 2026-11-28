# Upstream sources and exact scope

This is an original source-location and scope note. It does not reproduce
source text.

1. The frozen neighboring package
   \`factor-adaptive-sums-bounded-omega\`, commit
   \`594f5784a3f3947b021d5a43eb9d4dcb9cafb07e\`.
   - It proves the structure-dependent sufficient query budget
     \(B=\max(1,k-g-1)\) when \(h=0\) and
     \(B=\max(1,k-g-2)\) when \(h>0\).
   - Its only class that can attain \(K-2\) is the maximal single-block
     uniform input treated here.
   - The present result adds two exact arithmetic peels that save the final
     query on explicit subfamilies of that class. It also proves that those
     two peels are not complete.

2. Joseph M. Shunia, *Deterministic integer factorization from abundance
   decisions*, arXiv:2611.34242v1 (25 November 2026).
   - Fixed PDF: https://arxiv.org/pdf/2611.34242v1
   - Lemma 3.2 gives high-power normalization/totient recovery.
   - Theorem 3.1 uses \(2\lceil\log_2n\rceil\) consecutive high-power
     divisor sums for unrestricted deterministic factorization.
   - Equation (3.4) defines a normalized defect \(\xi_J\) which, on the
     uniform input here, is exactly
     \((u^m-\varphi(u)S)/u^m\). That statistic is therefore prior.
   - Lemmas 3.3--3.4 use a gap condition and Hankel reconstruction from
     \(2\ell\) consecutive normalized samples; even \(\ell=1\) uses two
     values. The new work here is the one-value exact ceiling-root
     sufficient test, the proper-gcd artificial split, and the explicit
     families where both shortcuts fail.

3. Lluis Eriksson, *Sharp Normalization Exponents, a 19x
   Rescaled-Vandermonde Contraction, Linear-Exponent Bounded-omega(n)
   Factoring, and Resolution of the c=1 Endpoint for Abundance-Oracle
   Factorization*, AIRR ARR-2026-1ZVBB45HG78WNVDH, v1 (27 November 2026).
   - Canonical PDF:
     https://airr.science/papers/ARR-2026-1ZVBB45HG78WNVDH/ARR-2026-1ZVBB45HG78WNVDH-v1.pdf
   - PDF SHA-256:
     \`c1bcf55a9afe5ac894558ee686acc4fabe430991031ce56c696e5bbe28c7f6d1\`.
   - Theorems 1(a) and 2(a) give normalization and a \(2K\)-sum
     arbitrary-multiplicity bounded-\(\omega\) result.
   - The same normalized defect is used there, but the paper does not state
     the one-value exact ceiling-root test, proper-gcd artificial split, or
     double-failure family proved here.

4. Christopher J. Hillar, *Cyclic Resultants*, Journal of Symbolic
   Computation 39 (2005), 653--669; arXiv:math/0401220v3.
   - https://arxiv.org/pdf/math/0401220v3
   - This studies equality and reconstruction of cyclic-resultant
     sequences, not the exact integer threshold or the dense-prime
     obstruction family here.

5. Christopher J. Hillar and Lionel Levine, *Polynomial recurrences and
   cyclic resultants*, Proceedings of the AMS 135 (2007), 1607--1618;
   arXiv:math/0411414v4.
   - https://arxiv.org/pdf/math/0411414v4
   - Its generic finite-initial-segment results do not imply either
     arithmetic peeling criterion.

6. Bartosz Żrałek, *A deterministic version of Pollard's p-1 algorithm*,
   arXiv:0707.4102v5 (12 May 2009).
   - Fixed PDF: https://arxiv.org/pdf/0707.4102v5
   - Section 6 discusses equal-order factoring with totient-oracle
     information. The present statistic and prime-gap criterion are not
     stated there.

No matching statement was found in this source and repository search. That
negative search is not an absolute priority claim. The positive result is
relative to exact divisor-sum values. The infinite-family proposition limits
only the two displayed peels and is not a factoring or oracle lower bound.
