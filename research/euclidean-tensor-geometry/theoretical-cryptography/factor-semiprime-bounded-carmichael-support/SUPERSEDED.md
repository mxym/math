# Supersession note

Date: 2026-11-28

The local support-vector enumeration and Adelmann--Winterhof
reconstruction are mathematically valid. They do not provide a new
polynomial semiprime class.

For complete support advice,
\[
 E=\prod_{r\in\mathcal S,r\le N}
 r^{\lfloor\log_rN\rfloor}
\]
is an explicitly factored multiple of \(\varphi(N)\): the prime
supports of \(\varphi(N)\) and \(\lambda(N)\) coincide, and every
prime-power divisor of \(\varphi(N)\le N\) is covered by the exponent
cap in \(E\).

Pomykala--Radziejewski, Section 6, pp. 15--16, defines Dec Mul Phi and
states after Theorem 6.1 that every semiprime \(n=pq\) is solvable by
Algorithm A3 with this input. Its complexity is polynomial when
\(\log E\) is polynomial in the advice length, as it is here.

Thus this directory is retained only as a weaker independent derivation.
It must not be released or cited as a new fixed-support result.
