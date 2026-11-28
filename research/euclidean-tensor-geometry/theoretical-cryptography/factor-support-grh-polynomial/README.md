# GRH-conditional polynomial factoring from Carmichael support

## Statement

Assume the generalized Riemann hypothesis for Dirichlet \(L\)-functions.
Let \(N\ge 2\), and let \(\mathcal S\) be a finite list of distinct
**genuine primes** satisfying the promise
\[
  \operatorname{supp}(\lambda(N))\subseteq\mathcal S. \tag{1}
\]
False positives in \(\mathcal S\) are allowed. The value of
\(\lambda(N)\), its prime-power exponents, and the factorization of \(N\)
are not supplied.

There is a deterministic algorithm that completely factors \(N\) in
time polynomial in
\[
 B=\log N+|\mathcal S|+\sum_{r\in\mathcal S}\log r. \tag{2}
\]

The support promise is advice: it is not inferred from \(N\). In
particular this is a conditional, advised-input reduction, not an
unconditional polynomial-time algorithm for ordinary integer
factorization.

## Idea

The support synthesizes a factored exponent multiple
\[
 E=\prod_{r\in\mathcal S,\ r\le N}r^{\lfloor\log_rN\rfloor},
 \qquad \lambda(N)\mid E.
\]
After listed primes are divided out, the residual is squarefree.
For each ordinary integer base
\[
 2\le u\le 2(\log N)^2,
\]
saturation handles non-coprime bases, while the factored \(E\)-chains
\[
 \gcd(u^{E/r^j}-1,D)
\]
refine every current block \(D\).

For two distinct residual primes \(p,q\), one of the reduced quotients
of \(p-1\) and \(q-1\) is nontrivial. Bach's GRH bound supplies a base
\(u\le2(\log p)^2\) outside the corresponding proper subgroup of
\(\mathbb F_p^\times\). The support chain then detects the order
valuation that differs between \(p\) and \(q\). Hence every pair is
separated and every terminal block is a single prime.

## Reproduction

    bash replay.sh
    sha256sum -c SHA256SUMS

The checker validates the finite group/order-chain reduction, support
supersets, complete refinement on finite cases, and repeated-prime
stripping. It does not verify GRH or replace Bach's analytic theorem.
