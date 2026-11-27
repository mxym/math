# Extreme singular values of dyadic cyclotomic Gaussian matrices

For each fixed rectangular module shape, this archive studies the maximum, over archimedean embeddings of a dyadic cyclotomic field, of the operator norm of a random matrix with independent discrete Gaussian coefficients. With the centering and normalization in the proof, the squared maximum has a standard Gumbel limit in the supercritical variance regime. In the critical regime the limit is a mixture with random intensity. For scalar matrices it is a standard Gumbel plus an independent normal variable of mean −1/(4c) and variance 1/c, where c is the limiting variance count divided by the square of the logarithm.

- [Proof](dyadic-spectral-extreme.md), including both limiting distributions and exact hypotheses.
- Reproduce the finite identities with `python3 verify-dyadic-spectral-extreme.py` (see the proof for the mathematical limits).
- Verify bytes with `sha256sum -c SHA256SUMS`.

This is a statistical theorem, not a result about complete cryptographic reductions, computational hardness, deployed parameters, or varying matrix shape. [Davis–Mikosch](https://pure.rug.nl/ws/portalfiles/portal/72126009/euclid.aop.1022677270.pdf) treat the classical scalar fixed-distribution Fourier maximum. [Lin–Wang–Zhuang–Wang](https://pure.tudelft.nl/ws/portalfiles/portal/186654080/1-s2.0-S0304397524001683-main.pdf) motivate the spectral budget in abstract Gaussian decomposition.

Research source: [e013add](https://github.com/mxym/math/commit/e013add67914aab9ac7e0ff2f37cf79016fcd75e).
