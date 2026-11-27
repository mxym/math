# Classification of spectral non-tiles in ternary four-space

A nonempty subset of F₃⁴ is spectral if and only if it tiles by translation or is an affine image of the known six-point configuration {0,e₁,e₂,e₃,e₄,−(e₁+e₂+e₃+e₄)}. There is one affine class of spectral non-tiles, comprising 2,729,376 subsets, and the possible spectral cardinalities are exactly 1, 3, 6, 9, 27 and 81.

The known six-point counterexample is not claimed here as new. [Fan–Zhang](https://arxiv.org/html/2408.12901), Corollary 1.11(3), previously proved that translational tiles are spectral. [Harada–Lam–Munemasa–Tonchev](https://doi.org/10.37236/443) previously classified the 85 classes of order-18 generalized Hadamard matrices over the cyclic group of order 3; this archive instead excludes spectra of size 18 specifically in F₃⁴ and classifies the non-tiling spectral subsets of that space. It is not a classification for other primes or dimensions.

- [Proof](FactorFugledeF3FourClassification.md)
- Run `node verify_factor_fuglede_f3_four_classification.js` for the main exact enumeration.
- Run `python3 verify_fuglede_f3_four_independent_numpy.py` with Python ≥3.10 and NumPy for the independent exact replay of the size-18 exclusion.
- Run `sha256sum -c SHA256SUMS` to verify archive bytes.

Research source: [1409827](https://github.com/mxym/math/commit/1409827aa945f40d6ba98803ac91c5854f0d9767).
