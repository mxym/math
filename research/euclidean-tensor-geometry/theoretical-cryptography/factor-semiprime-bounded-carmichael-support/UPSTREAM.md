# Prior art and corrected scope

## Dominating prior result

Jacek Pomykala and Maciej Radziejewski,
*Integer factoring and compositeness witnesses*,
Journal of Mathematical Cryptology 14 (2020), 346--358,
DOI https://doi.org/10.1515/jmc-2019-0023,
author PDF:
https://nutmic2019.imj-prg.fr/confpapers/FactoringWitnesses.pdf

Section 6, pp. 15--16, introduces the oracle Dec Mul Phi, which returns
the prime factorization of a multiple
\(D=O(\exp((\log n)^{M'}))\) of \(\varphi(n)\). Lines following
Theorem 6.1 state explicitly that, for \(n=pq\), every instance is
solvable by Algorithm A3 under Dec Mul Phi.

The support input here gives exactly such data. Put
\[
 E=\prod_{\substack{r\in\mathcal S\\r\le N}}
 r^{\lfloor\log_rN\rfloor}.
\]
The prime supports of \(\varphi(N)\) and \(\lambda(N)\) are equal,
and \(\varphi(N)\le N\), so \(\varphi(N)\mid E\). The
factorization of \(E\) is explicit and
\(\log E\le|\mathcal S|\log N\), polynomial in the stated advice
length. False-positive support primes only enlarge the multiple.

Therefore the fixed-cardinality restriction of the local enumeration
proof is unnecessary for polynomial time. The earlier version of this
file missed this direct prior result. No novelty claim remains.

## Local proof source

Clemens Adelmann and Arne Winterhof,
*Interpolation of Functions Related to the Integer Factoring Problem*,
in Coding and Cryptography, LNCS 3969 (2006), 144--154,
DOI https://doi.org/10.1007/11779360_12.

Their Proposition 2 gives the exact-\(\lambda\) reconstruction used by
the retained enumeration proof. That proof is valid, but it is weaker
than the Dec Mul Phi route above.
