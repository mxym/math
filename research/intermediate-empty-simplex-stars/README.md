# Maximum stars of empty simplices: the intermediate degrees

For independent uniform points in a fixed convex body in dimension \(d\), fix \(k\) sample vertices and count the empty \(d\)-simplices containing them. Maximize this count over all choices of the \(k\) vertices. For every \(2\le k\le d-1\) its expectation has order
\[
 \boxed{\Theta_{K,d,k}\big(n^{d-k+\min\{1,\,k/(d-k+2)\}}\big).}
\]
For instance, the largest star of empty tetrahedra through a common edge in three dimensions has expected size of order \(n^{5/3}\), rather than order \(n\). For \(2k\ge d+2\) the maximum reaches, in expectation and up to constant factors, the order of *all* completions of a base. This is a statement about the **maximum**, not the degree of a prescribed base or the total number of empty simplices.

- [Lower bound](PROOF.md): with positive probability the sample contains a base flat enough to support an unusually large star. A split into two label pools keeps the selection and emptiness estimates valid.
- [Matching upper bound](UPPER.md): conditional completion-volume tails and moments, including overlapping completion sets, control the maximum. This supplies the unsaturated upper bound intentionally not asserted in the lower-bound note alone.
- [Sources and precise comparison](SOURCES.md): the exponent proposed in Conjecture 1.6 of Reitzner–Temesvari's preprint is too small at every intermediate degree. Neither endpoint \(k=1,d\) is a counterexample here. No leading constant or limiting distribution is claimed.
- [Internal review of lower bound](REVIEW.md) and [internal review of upper bound](UPPER-REVIEW.md). The proof is analytic. The optional finite bookkeeping check, `python3 -B -O check.py`, is not a verification of the probabilistic theorem.

AI-assisted research draft; internally audited, not externally peer-reviewed. No claim of publication priority.
