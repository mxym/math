# Prior work and exact comparison

This is an original source-location and scope note. It does not
reproduce source text.

## The classical small-root theorem

Henry Cohn and Nadia Heninger,
“Ideal Forms of Coppersmith's Theorem and Guruswami--Sudan List
Decoding,” *Innovations in Computer Science* (2011), 298–308; expanded
version dated 2013, arXiv:1008.1284v2.
https://arxiv.org/pdf/1008.1284v2

Their Theorem 1.1 states the monic unknown-divisor theorem:
for degree \(d\), all \(|w|\le M^{\beta^2/d}\) with
\(\gcd(f(w),M)\ge M^\beta\) are found in time polynomial in
\(\log M\) and \(d\). It explicitly includes the closed endpoint and
attributes the result to Coppersmith, Howgrave-Graham, and May.

The CRT recovery in this package is a direct application of that
classical theorem. The new step claimed here is only the derivation,
from one exact numeric totient value, of a sufficiently accurate
unknown center for the separated factor.

## Numeric totient oracle factoring

François Morain, Guénaël Renault, and Benjamin Smith,
“Deterministic factoring with oracles,”
*Applicable Algebra in Engineering, Communication and Computing*
34(4) (2023), 663–690.
DOI: https://doi.org/10.1007/s00200-021-00521-8
Preprint: https://arxiv.org/abs/1802.08444v2

Their Theorem 4.2 is a related-divisor small-root prototype.
Theorems 5.4, 5.5, 5.6, and 5.9 give deterministic sufficient regions
in terms of relative prime sizes. At the balanced limit
\(\alpha_i\to1/k\), the hypotheses of Theorems 5.5 and 5.6 fail, and
Theorem 5.9's threshold is not met. The present additive one-outlier
cluster therefore lies outside those stated sufficient regions.

## Repository precursors

The sibling package **factor-fixed-omega-clustered-totient** records the
classical all-factors-in-one-short-window threshold and an elementary
two-point coefficient proof. The sibling package
**factor-multiscale-totient-rolle** uses repeated Rolle centers to cover
a broader multiscale family. Neither allows a \(k-1\) cluster as wide as
\(X^{2/(k-1)}\) with one factor a macroscopic distance away.

Searches covered numeric-totient oracle factoring, balanced and close
multi-prime inputs, one-outlier and two-cluster variants, and the source
chains above. No matching unknown-outlier localization theorem was
found. The search is not exhaustive, so no first-proof, priority,
optimality, density, or lower-bound claim is made.

A separate author-independent audit checked the two real branches,
Jensen error, derivative integration, gcd peeling, bitlength-dependent
small-root parameters, remaining-cluster recovery, shell count, and
the exact prior-work scopes.
