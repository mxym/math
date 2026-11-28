# General \(L_N[2/3,1]\) factoring from Carmichael support advice

> **Prior-art correction, 2026-11-28.**  The theorem proved in this
> directory remains a valid weaker construction, but it is not the
> strongest known consequence of the stated advice.  Zralek,
> *A deterministic version of Pollard's p-1 algorithm*, Theorem 8.1 and
> Lemmas 8.3--8.5, already proves an \(L_N[1/3,1+o(1)]\) deterministic
> algorithm from a completely factored exponent source.  The proof only
> uses that source to compute exact orders and Fermat--Euclid witnesses.
> Complete support advice synthesizes such a factored multiple
> \(E\) of \(\lambda(N)\), so the same proof applies after the elementary
> repeated-prime preprocessing.  Therefore this directory is
> **superseded, not a release candidate, and makes no priority claim**.
> See [SUPERSEDED.md](SUPERSEDED.md) for the exact mapping.

## Status

Superseded research-branch theorem. The proof and deterministic finite
checker remain available as an independently derived weaker route. This
directory must not be cited as the best support-advised complexity bound
or archived as a new result.

## Theorem proved here

Let \(N\ge2\). The auxiliary input is a finite list \(\mathcal S\) of
distinct primes satisfying
\[
 r\mid\lambda(N)\Longrightarrow r\in\mathcal S. \tag{1}
\]
False positives are allowed. The value of \(\lambda(N)\) and its prime
exponents are not supplied.

The proof in this directory gives an unconditional deterministic
algorithm that completely factors \(N\) in
\[
 \exp\!\left((1+o(1))
   (\log N)^{2/3}(\log\log N)^{1/3}\right)
 \operatorname{poly}(B), \tag{2}
\]
where
\[
 B=\log N+|\mathcal S|+\sum_{r\in\mathcal S}\log r. \tag{3}
\]
This is weaker than the \(L_N[1/3,1+o(1)]\operatorname{poly}(B)\)
consequence of Zralek's proof explained in SUPERSEDED.md.

The local construction first uses Pollard--Strassen small-divisor
detection to reduce the number of surviving primes, then applies a
smooth-subgroup base scan, and finally reconstructs each unresolved
block from bounded pairwise ratios of shifted primes.

## Exact scope

The list entries must be verified primes and (1) must contain **every**
true prime divisor of \(\lambda(N)\). The algorithm does not infer that
list from \(N\), does not factor an unfactored Carmichael value, and
does not give an unadvised deterministic subexponential factoring
algorithm. A very large false-positive list is charged through
\(\operatorname{poly}(B)\).

Arbitrary prime multiplicities and an unbounded number of distinct prime
factors are allowed. No concrete modulus, key, implementation, or
security claim is involved.

## Reproduction

```sh
./replay.sh
```
