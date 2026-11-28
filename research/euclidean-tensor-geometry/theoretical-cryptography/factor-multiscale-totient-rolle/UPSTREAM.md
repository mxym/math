# Prior work and exact comparison

This is an original source-location and scope note. It does not
reproduce source text.

## Numeric totient and sum-of-divisors oracles

François Morain, Guénaël Renault, and Benjamin Smith,
“Deterministic factoring with oracles,”
*Applicable Algebra in Engineering, Communication and Computing*
34(4) (2023), 663–690.
DOI: https://doi.org/10.1007/s00200-021-00521-8
Preprint: https://arxiv.org/abs/1802.08444

Their results give deterministic polynomial-time regions described by
relative prime sizes and lattice/approximate-common-divisor conditions.
For three factors, Theorem 1.2 lists the exact published regions. The
balanced point is outside them. No multiscale consecutive-root profile
like \(W_m\), nor the shell in this package, was found there. This is a
comparison of scopes, not a priority claim.

## Stronger oracle input

Markus Hittmeir and Jacek Pomykała,
“Deterministic Integer Factorization with Oracles for Euler's Totient
Function,” *Fundamenta Informaticae* 172(1) (2020), 39–51.
DOI: https://doi.org/10.3233/FI-2020-1891

Their main deterministic results use the prime-power decomposition of
\(\varphi(N)\), stronger information than the one numeric value used
here.

## Polynomial factorization

A. K. Lenstra, H. W. Lenstra, Jr., and L. Lovász,
“Factoring polynomials with rational coefficients,”
*Mathematische Annalen* 261 (1982), 515–534.

This supplies the standard deterministic polynomial factorization step
after the coefficient tree has produced a candidate.

## Repository precursors

The sibling package **factor-clustered-triprime-totient** gives the
one-level adjacent-gap case for three factors. The sibling package
**factor-fixed-omega-clustered-totient** gives the all-in-one-window
corollary
\(\prod_j(1+O_k(H^{j+2}/u^2))\).
The present result replaces \(H^{j}\) at every level by an actual
product of distances to roots outside a level-specific short block.
Its shell therefore has \(H\asymp u\) and is not covered by that earlier
short-window promise.

Searches covered numeric-totient oracle factoring, balanced and close
multi-prime inputs, fixed-\(\omega\) results, and the source chains
above. No matching theorem was found. The search is not exhaustive, so
no first-proof, priority, optimality, or lower-bound claim is made.

A separate author-independent audit checked the coefficient
parameterization, repeated Rolle centers, derivative profile, unknown
radius scheduling, fixed-degree bit complexity, rich-cell shell count,
label multiplicity, and gcd exclusion.
