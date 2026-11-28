# General deterministic factoring with bounded Carmichael support

## Statement

Let \(N\ge2\), and let \(\mathcal S\) be a finite list of distinct
genuine primes satisfying
\[
 \operatorname{supp}(\lambda(N))\subseteq\mathcal S, \tag{1}
\]
with false positives allowed. Define
\[
 C(N,\mathcal S)=
 \prod_{\substack{r\in\mathcal S\\r\le N}}
 \left(1+\lfloor\log_rN\rfloor\right). \tag{2}
\]
Then \(N\) can be completely factored deterministically in
\[
 C(N,\mathcal S)\operatorname{poly}
 \left(\log N+|\mathcal S|+\sum_{r\in\mathcal S}\log r\right) \tag{3}
\]
bit operations.

Consequently, for every fixed \(k\), the entire class with
\(|\mathcal S|\le k\) is deterministically polynomial-time factorable:
\[
 C(N,\mathcal S)\le(1+\log_2N)^k. \tag{4}
\]

This holds for arbitrary numbers of prime factors and arbitrary
multiplicities. The complete-support promise is extra advice and is not
computed from \(N\).

## Algorithm

Enumerate all exponent vectors
\[
 0\le e_r\le\lfloor\log_rN\rfloor
\]
and the corresponding integers
\[
 d=\prod_{r\in\mathcal S,\ r\le N}r^{e_r}\le N-1. \tag{5}
\]
For each \(d\), test \(d+1\) for primality and divisibility into the
current cofactor; when it divides, remove its full power.

Every prime \(p\mid N\) is found because
\[
 p-1\mid\lambda(p^a)\mid\lambda(N)
\]
for odd \(p\), while \(p=2\) corresponds to \(d=1\). Hence \(p-1\) is
one of the enumerated \(\mathcal S\)-smooth integers.

## Reproduction

    bash replay.sh
    sha256sum -c SHA256SUMS
