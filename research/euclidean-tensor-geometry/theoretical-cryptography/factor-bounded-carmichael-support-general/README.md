# General deterministic factoring with bounded Carmichael support

## Status: verified prior-art corollary

The statement below is mathematically correct and has passed an
author-independent paper audit. It is **not an independent new factoring
theorem**. It is the support-advice parameterization of established
factored-exponent / inverse-totient enumeration methods. In particular,
Cameron--Preece give the prime-power classification for all
\(\lambda(n)\mid E\), and Alekseyev explicitly enumerates \(d\mid E\)
and tests \(d+1\) for primality in the analogous inverse-\(\varphi\)
procedure. See [PRIOR_ART.md](PRIOR_ART.md).

## Statement

Let \(N\ge2\), and let \(\mathcal S\) be a finite list of distinct
genuine primes satisfying
\[
 \operatorname{supp}(\lambda(N))\subseteq\mathcal S,
\]
with false positives allowed. Define
\[
 C(N,\mathcal S)=
 \prod_{\substack{r\in\mathcal S\\r\le N}}
 \left(1+\lfloor\log_rN\rfloor\right).
\]
Then \(N\) can be completely factored deterministically in
\[
 C(N,\mathcal S)\operatorname{poly}
 \left(\log N+|\mathcal S|+\sum_{r\in\mathcal S}\log r\right)
\]
bit operations.

Consequently, for every fixed \(k\), instances with
\(|\mathcal S|\le k\) are polynomial-time factorable because
\[
 C(N,\mathcal S)\le(1+\log_2N)^k.
\]
No bound on the number or multiplicities of the prime factors of an
individual promised input is needed.

## Established enumeration specialized to the advice

Form the completely factored multiple
\[
 E=\prod_{r\in\mathcal S,\ r\le N}r^{\lfloor\log_rN\rfloor}.
\]
Enumerate all \(d\mid E\) with \(d<N\). For each, test \(d+1\) for
primality and divisibility into the current cofactor of \(N\), removing
the full prime power when it divides. There are
\(\tau(E)=C(N,\mathcal S)\) candidates.

Every odd prime \(p\mid N\) appears because
\(p-1\mid\lambda(N)\mid E\); \(p=2\) is the case \(d=1\).

The complete-support promise is advice and is not computed from \(N\).
The fixed-\(k\) statement does not assert that a family with arbitrarily
many distinct prime factors exists for every fixed support set. This
package is not a release or DOI candidate.

## Reproduction

    bash replay.sh
    sha256sum -c SHA256SUMS
