# Prior work and exact comparison

## Numeric totient oracle

François Morain, Guénaël Renault, and Benjamin Smith,
“Deterministic factoring with oracles,”
*Applicable Algebra in Engineering, Communication and Computing*
34(4) (2023), 663–690.
DOI: https://doi.org/10.1007/s00200-021-00521-8
Preprint: https://arxiv.org/abs/1802.08444

Their Theorems 5.4, 5.6, 5.9, and 5.10 give deterministic
polynomial-time sufficient regions based on relative prime sizes.
The uniform point
\((\alpha_1,\ldots,\alpha_k)=(1/k,\ldots,1/k)\) is outside those strict
sufficient regions for every fixed \(k\ge3\). The present theorem enters
a thin additive neighborhood of that point; it does not solve all
equal-bitlength inputs.

## Stronger input in other work

Markus Hittmeir and Jacek Pomykała,
“Deterministic Integer Factorization with Oracles for Euler's Totient
Function,” *Fundamenta Informaticae* 172(1) (2020), 39–51.
DOI: https://doi.org/10.3233/FI-2020-1891

Their principal deterministic results use the prime-power decomposition
of \(\varphi(N)\), a stronger input than the single numeric value used
here. Those results and the present additive-cluster theorem are not
interchangeable.

## Polynomial factorization

A. K. Lenstra, H. W. Lenstra, Jr., and L. Lovász,
“Factoring polynomials with rational coefficients,”
*Mathematische Annalen* 261 (1982), 515–534.
The fixed-degree polynomial factorization invoked in the verifier step
is a standard consequence of this work.

## Related repository result

For \(k=2\), Morain--Renault--Smith Lemma 5.2 already gives exact
quadratic recovery with no clustering assumption.

The sibling directory
`factor-clustered-triprime-totient/` gives a sharper result for
\(k=3\): one close adjacent pair can suffice even if all three primes
are not in one short interval. The present two-point coefficient method unifies that elementary
mechanism for every fixed \(k\), but its new scope is recorded only for
fixed \(k\ge4\).


## Classical route to the same uniform threshold

Henry Cohn and Nadia Heninger,
“Ideal Forms of Coppersmith's Theorem and Guruswami--Sudan List
Decoding,” *Innovations in Computer Science* (2011), 298–308; expanded
version dated 2013, arXiv:1008.1284v2.
https://arxiv.org/pdf/1008.1284v2

Their Theorem 1.1 states the Coppersmith--Howgrave-Graham--May
unknown-divisor small-root theorem, including the endpoint
\(|w|\le M^{\beta^2/d}\). For the present balanced fixed-\(k\) cluster,
either \(\gcd(N,\varphi(N))\) already splits \(N\), or CRT modulo
\(M=N\varphi(N)\) combines a common integer center modulo \(N\) and that
center minus one modulo \(\varphi(N)\). Each shift to a factor \(p\) is
then a root of a monic linear polynomial modulo the unknown divisor
\(p(p-1)\mid M\). The theorem, with a polylogarithmic number of adjacent
center blocks, already gives the polynomial-time threshold
\(H\le N^{2/k^2}\operatorname{polylog}N\).

Thus the uniform exponent is not claimed as new. The present package's
independent content is the explicit two-consecutive-value
finite-difference tree and its full parameterized running-time bound.

## Search and claim policy

Searches covered numeric-\(\varphi\) oracle factoring, balanced
multi-prime inputs, fixed-\(\omega\) results, and the MRS and
Hittmeir–Pomykała source chains. No source matching this two-consecutive-
value finite-difference theorem was found. The search is not exhaustive,
so no first-proof or priority claim is made. An author-independent paper audit checked the integer pivot, exact tail
bounds, complete search tree, final coefficient recovery, and scope.
No global priority claim is made.
