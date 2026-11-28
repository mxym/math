# Fixed-\(K\) factoring from Carmichael prime-support advice

> **Prior-art correction, 2026-11-28.**  The subexponential theorem in
> this directory remains correct but is strictly superseded.  The
> common-order and base-\(A\) reconstruction machinery of Zralek 2010,
> Lemmas 8.4--8.5, together with the standard polylogarithmic
> smooth-number generating set, gives deterministic polynomial time for
> every fixed upper bound \(K\) once a factored exponent multiple is
> available. Complete support advice synthesizes that multiple.
> Hittmeir--Pomykala 2020 also explicitly records polynomial
> deterministic factorization for bounded \(\omega(N)\) with the
> decomposed-totient input. Therefore this directory is superseded, not
> a release candidate, and makes no priority claim. See
> [SUPERSEDED.md](SUPERSEDED.md).

## Local theorem retained for provenance

Fix \(K\ge2\). Let \(N\) have at most \(K\) distinct prime divisors.
Let \(\mathcal S\) contain every prime divisor of \(\lambda(N)\),
with false positives allowed. The local proof gives
\[
 \exp\!\left(
   \bigl(\sqrt{2(K-1)}+o(1)\bigr)
   \sqrt{\log N\,\log\log N}\right)
 \operatorname{poly}_K(B),
\]
where
\[
 B=\log N+|\mathcal S|+\sum_{r\in\mathcal S}\log r.
\]
This bound is valid but weaker than deterministic
\(\operatorname{poly}_K(B)\) from the earlier machinery.

## Local method

The retained proof scans a subexponential base range, bounds the reduced
ratios of shifted primes, and enumerates those ratios for monotone
polynomial reconstruction. The stronger route instead computes a common
order \(A\) from polylogarithmically many bases and applies base-\(A\)
digit-polynomial reconstruction.

The support is advice and is not inferred from \(N\). No concrete
modulus, key, implementation, or security claim is involved.

## Reproduction

```sh
./replay.sh
```
