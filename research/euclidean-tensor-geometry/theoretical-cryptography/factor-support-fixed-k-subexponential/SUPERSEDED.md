# Supersession note

Date: 2026-11-28

The \(L_N[1/2]\)-type fixed-\(K\) theorem in this directory is a
correct weaker proof. It is not the best consequence of the advice.

Complete Carmichael support yields an explicitly factored multiple
\(E\) of \(\varphi(N)\). After stripping repeated-prime factors,
scan bases through \((\log d)^{K+2}\) in each recursive squarefree
block. A gcd or Fermat--Euclid witness splits the block. If none appears,
the exact orders modulo every prime factor agree. Their least common
multiple \(A\) is computable from \(E\).

The Konyagin--Pomerance smooth-number bound gives
\(A^k\ge\Psi(d,(\log d)^{K+2})>d^{1-1/(K+2)}\) for
\(k=\omega(d)\le K\). Therefore Zralek Lemmas 8.4--8.5 apply and
recover all factors in deterministic polynomial time for fixed \(K\).
Hittmeir--Pomykala 2020 records the same bounded-\(\omega\)
polynomial regime for decomposed totient input.

The directory is retained only for provenance and must not be released
or cited as a new best bound.
