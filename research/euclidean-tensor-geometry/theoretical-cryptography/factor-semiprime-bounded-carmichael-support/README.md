# Deterministic semiprime factoring with bounded Carmichael support

## Statement

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
There is an unconditional deterministic algorithm that factors \(N\)
in
\[
 C(N,\mathcal S)\operatorname{poly}
 \left(\log N+|\mathcal S|+\sum_{r\in\mathcal S}\log r\right) \tag{3}
\]
bit operations.

In particular, if \(|\mathcal S|\le k\) for a fixed constant \(k\),
then the running time is polynomial in the advised input length, since
\[
 C(N,\mathcal S)\le(1+\log_2N)^k. \tag{4}
\]

The support list is extra advice and is not computed from \(N\). The
result is for semiprimes; it is not a general polynomial-time factoring
algorithm.

## Method

Enumerate all support-compatible candidates
\[
 m=\prod_{r\in\mathcal S,\ r\le N}r^{e_r},
 \qquad 0\le e_r\le\lfloor\log_rN\rfloor. \tag{5}
\]
The true \(m=\lambda(N)\) occurs.

For each candidate put \(\Delta=\lfloor N/m\rfloor\). Adelmann and
Winterhof's exact-\(\lambda\) reconstruction implies that for the true
candidate either \(\Delta\) is a prime factor, or
\[
 \varphi(N)=\Delta m.
\]
In the second case \(p+q=N+1-\Delta m\), so an exact discriminant test
recovers the two roots. Every output is verified by primality and
product checks.

## Reproduction

    bash replay.sh
    sha256sum -c SHA256SUMS
