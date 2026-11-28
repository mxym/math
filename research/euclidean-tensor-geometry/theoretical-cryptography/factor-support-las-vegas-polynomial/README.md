# Las Vegas polynomial factoring from Carmichael support advice

## Statement

Let \(N\ge2\), and let \(\mathcal S\) be a finite list of distinct
genuine primes with
\[
 \operatorname{supp}(\lambda(N))\subseteq\mathcal S. \tag{1}
\]
False positives are allowed. The value and exponents of \(\lambda(N)\)
are not given.

There is an unconditional Las Vegas algorithm that completely factors
\(N\) in expected time polynomial in
\[
 B=\log N+|\mathcal S|+\sum_{r\in\mathcal S}\log r. \tag{2}
\]
It always returns a correct factorization; randomness affects only the
running time.

The complete-support promise is extra advice and is not inferred from
\(N\). Thus this does not give a polynomial-time algorithm for ordinary
unadvised integer factorization.

## Construction

Build the factored exponent multiple
\[
 E=\prod_{r\in\mathcal S,\ r\le N}r^{\lfloor\log_rN\rfloor},
 \qquad \lambda(N)\mid E.
\]
Divide every listed prime completely out of \(N\); the residual is
squarefree. On each composite residual block, sample a uniform residue
\(a\). A proper \(\gcd(a,M)\) splits immediately. Otherwise write
\(E=2^st\), follow
\[
 a^t,\ a^{2t},\ldots,a^{2^st}=1\pmod M,
\]
and take a gcd from the last square root before \(1\). Conditional on
\(a\) being a unit, one trial splits every squarefree composite block
with probability at least \(1/2\). Recursion therefore has expected
polynomial cost.

## Reproduction

    bash replay.sh
    sha256sum -c SHA256SUMS

The checker validates exponent synthesis, the exact CRT collision
probability, exhaustive finite splitting trials, false-positive advice,
and repeated-prime stripping.
