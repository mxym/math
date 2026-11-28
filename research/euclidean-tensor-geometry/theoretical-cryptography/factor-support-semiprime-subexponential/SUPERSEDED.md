# Supersession note

This directory is retained to preserve the exact historical proof and
checker. Its stated deterministic
\[
 \exp((\sqrt2+o(1))\sqrt{\log N\log\log N})
\]
semiprime bound is correct, but it is superseded in its own advice
model.

## Input conversion

Let S contain the complete prime support of λ(N), with false positives
allowed, and put
\[
 E=\prod_{r\in S,\ r\le N}r^{\lfloor\log_rN\rfloor}.
\]
For every prime power p^a exactly dividing N,
\[
 \varphi(p^a)=p^{a-1}(p-1)\mid E.
\]
The support inclusion follows from supp φ(N)=supp λ(N), while each
r-adic exponent is at most floor(log_r N). Therefore φ(N) divides E.
The complete factorization of E is part of the construction and
log E≤|S| log N.

## Stronger prior consequences

Pomykała--Radziejewski, Section 6 (printed pp. 15--16), take as input a
completely factored polynomial-size multiple of φ(N). Their text after
Theorem 6.1 explicitly covers all semiprimes through Algorithm A3.
Substituting E above gives deterministic polynomial time for exactly the
present semiprime support-advice promise.

Źrałek, arXiv:0707.4102v5, Theorem 8.1 and Lemmas 8.3--8.5 (printed
pp. 18--20), gives a deterministic L_N[1/3,1+o(1)] method. The proof
needs a factored exponent multiple for order stripping, not equality
with φ(N). Repeated prime powers are harmless because p^a divides N
with a≥2 implies p divides λ(N), so those primes are exposed by the
support list before the squarefree phase.

Accordingly this package is not a release candidate and should not be
cited as closing a prior open problem. Its original files remain
available only for provenance and comparison.
