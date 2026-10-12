For every integer k >= 2, we prove the sharp equal-mass Gaussian first-moment inequality: the squared cell-moment sum is at most (E max_{i<=k} Z_i)^2/(k-1), for independent standard normals. In dimension d >= k-1, equality holds precisely for central regular simplex winning cones extended cylindrically. The bound includes measurable and fractional partitions; it is strict below dimension k-1 without a claim of the sharp low-dimensional value.

The complete six-page proof settles the equal-mass subcase of Heilman 2019 Conjecture 1.16 for every cell count, and his full four-cell dimension-three Conjecture 3 from 2014. It derives a global covariance comparison and exact nonnegative deficit integral from Gaussian flux, the published Milman–Neeman multi-bubble perimeter theorem, weighted Cauchy–Schwarz and a radial differential inequality.

## Frozen proof and verification files

This immutable release binds Git commit `ebfd90558439afca21babeb7b77c8d8837ea745f`. All proof and verification files are committed in that tree:

- [Six-page PDF](https://github.com/mxym/math/blob/ebfd90558439afca21babeb7b77c8d8837ea745f/research/gaussian-balanced-simplex-all-k/paper.pdf), SHA-256 `f50e07e08e1c9a676b7c5511dcb5a88c4dd18c8b867dcbf5169f62b24bf08872`.
- [Complete editable mathematical proof](https://github.com/mxym/math/blob/ebfd90558439afca21babeb7b77c8d8837ea745f/research/gaussian-balanced-simplex-all-k/paper.md), SHA-256 `8416f741398ceb4207edcc3ff31964883ae14044698043bf17a75d66c1dec832`.
- [Package and reproduction instructions](https://github.com/mxym/math/blob/ebfd90558439afca21babeb7b77c8d8837ea745f/research/gaussian-balanced-simplex-all-k/README.md).
- [All-file manifest](https://github.com/mxym/math/blob/ebfd90558439afca21babeb7b77c8d8837ea745f/research/gaussian-balanced-simplex-all-k/MANIFEST.json) and [SHA-256 checksums](https://github.com/mxym/math/blob/ebfd90558439afca21babeb7b77c8d8837ea745f/research/gaussian-balanced-simplex-all-k/SHA256SUMS).
- [Partial Lean proofs and replay instructions](https://github.com/mxym/math/blob/ebfd90558439afca21babeb7b77c8d8837ea745f/research/gaussian-balanced-simplex-all-k/formal/README.md), [recorded result](https://github.com/mxym/math/blob/ebfd90558439afca21babeb7b77c8d8837ea745f/research/gaussian-balanced-simplex-all-k/results/lean.json).
- [Internal proof reviews](https://github.com/mxym/math/blob/ebfd90558439afca21babeb7b77c8d8837ea745f/research/gaussian-balanced-simplex-all-k/review) and [literature-status comparison](https://github.com/mxym/math/blob/ebfd90558439afca21babeb7b77c8d8837ea745f/research/gaussian-balanced-simplex-all-k/LITERATURE_STATUS.md).

Use the source-code archives generated for this locked tag to obtain the repository, then run the package verifier. The actual Git archive of the frozen package passed integrity checks and fresh partial Lean replay: eight algebra/abstract-real-analysis exports, 18,013 used declarations replayed in an initially empty kernel at trust level zero, and a deliberately false control rejected.

There are no separately uploaded release attachments: the managed connection authenticated ordinary Git/API access but returned HTTP 401 at the upload host. The entire package, including the PDF and logs, is therefore disclosed through the immutable tag and fixed-commit links above.

The Gaussian analytic endpoint and the imported geometric theorem are not fully Lean-formalized. Two archived reviews are internal model reviews, not external human peer review. The source screen found no equivalent all-k result in the checked sources; it is limited and establishes no worldwide priority claim. This release does not prove positive-correlation noise stability or the arbitrary-mass Euclidean statement.
