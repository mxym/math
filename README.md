# Fuglede's conjecture over F_17^3

Version 1.0.0. This snapshot gives an exact computer-assisted proof that a nonempty subset of the three-dimensional vector space over the field of 17 elements is spectral if and only if it tiles by translations.

- [Theorem and proof map](proof/FugledeF17Theorem.md)
- [Final cardinality 34 proof](proof/FugledeF17Size34Final.md)
- [Degree-ten census transcript](proof/verify-fuglede-f17-size34-six-directions-decic-transcript.txt)

Run `sha256sum -c SHA256SUMS` from the archive root. Individual proof notes identify the corresponding verifiers. The scripts and sources require Node.js or a C++17 compiler and use exact integer and field arithmetic.

For the final size-34 checks, run `bash replay-size34.sh quick` for the lift and incidence certificates and the cap-four profile catalogue, or `bash replay-size34.sh` to additionally repeat the degree-ten census and compare all eight disjoint intervals with the transcript. Full replay is substantially slower. Earlier reductions and other sizes have separate verifier instructions in their proof notes.

This proof is specific to F_17^3, not the Euclidean Fuglede conjecture. The snapshot includes only the theorem, its transitive proof dependencies, and the exact verifiers from [the reviewed research commit](https://github.com/mxym/math/tree/2d5d1cd7dae9b7365db42256a13c7f944e2c625d/research/euclidean-tensor-geometry).
