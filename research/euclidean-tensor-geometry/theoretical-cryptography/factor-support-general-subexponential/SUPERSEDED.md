# Supersession and exact proof mapping

Date: 2026-11-28

## Decision

The \(L_N[2/3,1]\) theorem in this directory remains a correct weaker
algorithm, but it is superseded by an earlier \(L_N[1/3,1+o(1)]\)
argument after a direct input-model adaptation. This package is retained
for provenance and must not be released or cited as a new best bound.

## Earlier theorem

Bartosz Zralek, *A deterministic version of Pollard's p-1 algorithm*,
Mathematics of Computation 79 (2010), 513--533,
DOI https://doi.org/10.1090/S0025-5718-09-02262-5,
arXiv:0707.4102v5.

Use the v5 numbering:

* p. 18, Theorem 8.1: a completely factored \(\varphi(n)\) gives a
  deterministic \(L_n[1/3,1+o(1)]\) complete factorization;
* pp. 18--19, Lemma 8.3: for many prime factors, a common computable
  \(A=\operatorname{lcm}_{b\in B}\operatorname{ord}_d(b)\) makes the
  least prime factor \(p=1+mA\) with subexponentially bounded \(m\);
* p. 19, Lemmas 8.4--8.5: for few prime factors, a base-\(A\)
  polynomial reconstructs all shifted factors;
* p. 20: \((\alpha,\beta,\gamma)=(2/3,1/3,1/2)\) gives exponent
  parameter \(1/3\).

## Why complete Carmichael support is sufficient

From the verified prime list \(\mathcal S\), form
\[
 E=\prod_{\substack{r\in\mathcal S\\r\le N}}
 r^{\lfloor\log_rN\rfloor}.
\]
Then \(\lambda(N)\mid E\), the factorization of \(E\) is explicit,
and \(\log E\le |\mathcal S|\log N\).

For every recursive divisor \(d\mid N\) and every unit \(b\bmod d\),
\(\operatorname{ord}_d(b)\mid E\). Starting from \(E\), remove a
prime factor \(r\) whenever
\(b^{E/r}\equiv1\pmod d\), repeating with the current exponent.
This computes the exact, fully factored order in time polynomial in the
ordinary input/advice length. The same order-factor tests compute every
Fermat--Euclid witness used in Zralek's proof. If no witness splits the
current divisor, the orders modulo all of its prime factors agree, so
the common \(A\) in Lemmas 8.3--8.5 is available exactly.

Before this recursion, divide from \(N\) the full power of every
\(r\in\mathcal S\). Any surviving repeated prime power \(p^a\),
\(a\ge2\), would force
\(p\mid\lambda(p^a)\mid\lambda(N)\), contradicting that stripping.
The residual is therefore squarefree; stripped factors are already
known. False-positive support primes merely enlarge \(E\) and are
removed during exact-order computation.

Consequently the earlier proof gives
\[
 L_N[1/3,1+o(1)]\operatorname{poly}(B),
 \qquad
 B=\log N+|\mathcal S|+\sum_{r\in\mathcal S}\log r.
\]
This is a corollary obtained by inspecting the proof, not the literal
input statement of Theorem 8.1.

## Related explicit common-order statement

Pomykala--Radziejewski, *Integer factoring and compositeness witnesses*,
Lemma 4.4 and equations (4.4)--(4.5), pp. 11--12,
https://nutmic2019.imj-prg.fr/confpapers/FactoringWitnesses.pdf,
independently exposes the same equal-order and smooth-subgroup
mechanism.

No claim is made that this support-advice corollary is new.
