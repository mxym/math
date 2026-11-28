# Deterministic semiprime factoring with bounded Carmichael support

> **Prior-art correction, 2026-11-28.**  The enumeration theorem below
> remains correct, but its fixed-support polynomial consequence is
> strictly superseded.  Pomykala--Radziejewski, *Integer factoring and
> compositeness witnesses*, Section 6, pp. 15--16, explicitly proves that
> every squarefree semiprime is deterministically factorable from a
> completely factored multiple of \(\varphi(N)\).  Complete Carmichael
> support constructs such a multiple \(E\), because
> \(\operatorname{supp}\varphi(N)=\operatorname{supp}\lambda(N)\)
> and the exponent caps in \(E\) dominate every valuation of
> \(\varphi(N)\).  Hence semiprimes are polynomial-time factorable
> under the advice here **without a fixed-cardinality promise**.
> This directory is superseded and is not a release candidate. See
> [SUPERSEDED.md](SUPERSEDED.md).

## Local statement retained for provenance

Let \(N=pq\) be the product of two distinct primes. Let
\(\mathcal S\) be a finite list of distinct genuine primes satisfying
\[
 \operatorname{supp}(\lambda(N))\subseteq\mathcal S, \tag{1}
\]
with false positives allowed. Define
\[
 C(N,\mathcal S)=
 \prod_{\substack{r\in\mathcal S\\r\le N}}
 \left(1+\lfloor\log_rN\rfloor\right). \tag{2}
\]
The proof in this directory factors \(N\) in
\[
 C(N,\mathcal S)\operatorname{poly}
 \left(\log N+|\mathcal S|+\sum_{r\in\mathcal S}\log r\right).
 \tag{3}
\]
This is valid but weaker than the prior polynomial-time route above.

## Local method

Enumerate all support-compatible candidates
\[
 m=\prod_{r\in\mathcal S,\ r\le N}r^{e_r},
 \qquad 0\le e_r\le\lfloor\log_rN\rfloor.
\]
The true \(m=\lambda(N)\) occurs. Adelmann--Winterhof Proposition 2
then reconstructs the two factors from the true candidate.

The support list is advice and is not computed from \(N\). No concrete
modulus, key, implementation, or security claim is involved.

## Reproduction

    bash replay.sh
    sha256sum -c SHA256SUMS
