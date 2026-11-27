# The six-dimensional point-transitive kissing number is 72

In a kissing configuration, equal balls touch a central ball without overlapping. This archive proves that at most 72 balls can do so in six dimensions if the orthogonal symmetry group of their centers can carry any one center to any other. The known 72-point E6 configuration attains the bound. The theorem does not assume a lattice or antipodal pairs, and it does not settle the unrestricted six-dimensional kissing number.

[Tomar's unrestricted upper bound of 76](https://www.mefyi.com/papers/kissing-numbers-five-seven/) leaves the four possible excess sizes 73 through 76. We exclude these by orbit counts, real rotation representations, and exact continuous coverage of the remaining phase domains. The proof also records a separate, partial observation in seven dimensions; no seven-dimensional exact result is asserted here.

- [Proof](KissingSixVertexTransitive.md)
- Run `python3 verify-kissing-six-vertex-transitive.py` for the main reproducible certificate.
- Run `python3 verify-independent.py` for the separately implemented audit. Both use only the Python standard library.
- Run `sha256sum -c SHA256SUMS` to verify the archive payload.

Research source: [1ca84c4](https://github.com/mxym/math/commit/1ca84c46b0f2d75d8b1566aab466b5c6d935b6a6).
