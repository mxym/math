# Support-advised semiprime factoring: retained weaker route

## Status: superseded by prior-art adaptations

The theorem proved in this directory is mathematically valid, but it is
**not the best known consequence of the stated advice** and must not be
reported as a new complexity bound.

Complete prime-support advice for λ(N) gives the completely factored
integer
\[
 E_{\mathcal S}(N)=\prod_{\substack{r\in\mathcal S\\r\le N}}
 r^{\lfloor\log_r N\rfloor}.
\]
For every prime power dividing N, its Euler factor divides this integer,
so φ(N) divides E. Its binary length is polynomial in the advised input
length.

Pomykała--Radziejewski, Section 6, formulate deterministic factoring
from a completely factored polynomial-size multiple of φ(N)
(Dec Mul Φ) and explicitly state that their Algorithm A3 handles every
semiprime N=pq in polynomial time in that model. Thus the support-only
semiprime promise here already has a deterministic polynomial-time
solution by a direct input adaptation of that prior result. See
[SUPERSEDED.md](SUPERSEDED.md) for the exact mapping.

The original proof and checker are retained for provenance. They prove
the following weaker historical statement:
\[
 \exp\!\left((\sqrt2+o(1))
       \sqrt{\log N\,\log\log N}\right)
 \operatorname{poly}\!\left(
   \log N+|\mathcal S|+\sum_{r\in\mathcal S}\log r\right).
\]
No release or DOI should be made from this package.

## Scope

The support list is advice; it is not computed from N. No ordinary
unadvised factoring claim, concrete modulus, key, implementation, or
security conclusion is made.

## Reproduction of the retained proof

    ./replay.sh
    sha256sum -c SHA256SUMS
