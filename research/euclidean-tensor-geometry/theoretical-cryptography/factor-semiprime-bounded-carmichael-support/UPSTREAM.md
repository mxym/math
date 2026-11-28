# Prior art and scope

The exact-\(\lambda\) semiprime reconstruction used here is Proposition
2 of:

Clemens Adelmann and Arne Winterhof,
**“Interpolation of Functions Related to the Integer Factoring
Problem,”** in *Coding and Cryptography*, LNCS 3969 (2006), pp. 144–154,
DOI [10.1007/11779360_12](https://doi.org/10.1007/11779360_12).

That proposition shows that for \(N=pq\), with
\(\Delta=\lfloor N/\lambda(N)\rfloor\), either \(\Delta\) is a factor
or the factors are roots of a quadratic determined by
\(\Delta\lambda(N)\).

The present note adds a parameterized support-to-value reduction:
enumerating all exponent vectors compatible with a support superset
guarantees that the exact \(\lambda(N)\) candidate is tested. This gives
the explicit complexity (2), and deterministic polynomial time when
the advice cardinality is fixed.

## Distinctions

* The exact value of \(\lambda(N)\) is not input.
* Every true support prime must occur in \(\mathcal S\); false positives
  are allowed by giving them exponent zero.
* Polynomial time is claimed only for fixed support cardinality. The
  general bound is the explicit product (2).
* The theorem is for a product of two distinct primes, with even and
  square cases handled directly.
* No claim of absolute historical priority is made.
