# Fuglede's conjecture over F_13^3

Version 1.0.0. This archive contains the complete proof for the three-dimensional vector space over the field of 13 elements, together with exact, dependency-free JavaScript verifiers.

- Read the [theorem and proof map](proof/FugledeF13Theorem.md).
- Start the last cardinality at [size 26](proof/FugledeF13Size26Final.md).
- Check the files with `sha256sum -c SHA256SUMS` from the archive root.
- Run an individual verifier with `node proof/verify-fuglede-f13-size26-five-uniform.js`. Run all with `for f in proof/verify-fuglede-f13-*.js; do node "$f" || exit; done`. Some enumerations take longer than others.

The result is specific to F_13^3. This snapshot contains the Fuglede proof and verifier files from [the reviewed research commit](https://github.com/mxym/math/tree/785a52b5cd0e414c0950b8632d4a9824b07e9352/research/euclidean-tensor-geometry), not unrelated projects in the repository. Citations and proof dependencies are in the theorem index.
