# One-fifth composition for deterministic known-exponent factoring

Let \(N>1\). Suppose an even positive integer \(E\) is supplied with
\[
 \lambda(N)\mid E,\qquad \log E=(\log N)^{O(1)}.
\]
The prime factorization of \(E\) is **not** part of the input. Put
\[
 X=\min\{N,E\}.
\]

> **Theorem.** The complete prime-power factorization of \(N\) can be
> recovered deterministically in
> \[
> X^{1/5+o(1)}
> \operatorname{poly}(\log N+\log E)
> \]
> bit operations.

A more explicit two-term form is
\[
 \mathcal H(X)
 + (X+1)^{1/(4\sqrt e)+\eta}
   \operatorname{poly}_{\eta}(\log N+\log E), \tag{1}
\]
for any fixed
\(0<\eta<1/5-1/(4\sqrt e)\), where the established
Harvey--Hittmeir bound is
\[
 \mathcal H(Y)=
 O\!\left(
 \frac{Y^{1/5}\log^{16/5}Y}{(\log\log Y)^{3/5}}
 \right)
\]
for sufficiently large \(Y\).

The algorithm chooses the smaller integer. If \(N\le E\), apply the
general deterministic Harvey--Hittmeir algorithm directly to \(N\).
If \(E<N\), apply it to \(E\), then feed the resulting complete
factorization of \(E\) to the factored-advice character-chain theorem.
That theorem costs only
\((E+1)^{1/(4\sqrt e)+\eta}\) up to polynomial factors, which is below
the one-fifth value exponent.

Consequently, if \(E=N^{\tau+o(1)}\), then the exponent in \(N\) is
\[
 \frac{\min\{1,\tau\}}5+o(1). \tag{2}
\]

This is a deterministic arithmetic-advice result, not an ordinary
sub-one-fifth algorithm: obtaining a suitable \(E\) remains outside the
theorem. It concerns no concrete modulus or deployed system. No
absolute priority claim is made for the composition.

See [PROOF.md](PROOF.md), [UPSTREAM.md](UPSTREAM.md), and
[RESULTS.txt](RESULTS.txt).
