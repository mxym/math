# Deterministic factoring from Carmichael prime-support advice

## Status: valid but superseded by a stronger prior-art adaptation

The power-time theorem retained in this directory is mathematically
correct and has passed an author-independent paper audit. It is not a
release candidate. The same advice admits the strictly stronger bound
\[
 \exp\!\left((1+o(1))
   \sqrt{\log P_{\mathcal S}(N)\,
         \log\log P_{\mathcal S}(N)}\right)
 \operatorname{poly}(B),
\]
where \(B=\log N+|\mathcal S|+\sum_{r\in\mathcal S}\log r\).
This follows by applying the subgroup/smooth-number argument of
Źrałek's Lemma 8.3 to the factored exponent synthesized from the support
list. See [SUPERSEDED.md](SUPERSEDED.md). It is a proof adaptation of
prior work, not a new complexity claim.

## Retained weaker theorem

Let \(N\ge2\). The auxiliary input is a finite list \(\mathcal S\) of
distinct primes such that
\[
  r\mid\lambda(N)\quad\Longrightarrow\quad r\in\mathcal S,
\]
with false positives allowed. No value or prime exponents of
\(\lambda(N)\) are supplied.

Put
\[
 E_{\mathcal S}(N)=
 \prod_{\substack{r\in\mathcal S\\r\le N}}
 r^{\lfloor\log_r N\rfloor}
\]
and
\[
 P_{\mathcal S}(N)=
 \max\bigl(\{p:p\mid N,\ p\notin\mathcal S\}\cup\{1\}\bigr).
\]
For every fixed \(\varepsilon>0\), the retained Burgess-character
argument completely factors \(N\) deterministically in
\[
 P_{\mathcal S}(N)^{1/(4\sqrt e)+\varepsilon}
 \operatorname{poly}_{\varepsilon}(B)
\]
bit operations.

The support advice synthesizes a completely factored polynomial-length
multiple of \(\lambda(N)\). Multiplicities are not needed. The original
proof and checker remain for provenance and exact verification of this
weaker route.

## Scope

The support list is advice and is not computed from \(N\). Neither bound
is an ordinary unadvised factoring algorithm. No concrete modulus, key,
implementation, or security conclusion is involved.

## Reproduction

    ./replay.sh
    sha256sum -c SHA256SUMS
