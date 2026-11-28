# Exact Gaussian Approximation for Products of Arbitrarily Many Gaussian Matrices

For independent real iid Gaussian matrices, the total variation limit of the normalized full matrix product is governed by the accumulated inverse internal widths, even when the chain length grows without a bound.

With both end dimensions increasing and rho = p q times the sum of the inverse inner widths, the exact limiting total variation profile is 2 Phi(gamma/4) minus 1 when rho tends to gamma. If one end dimension stays fixed and the other grows, a different chi-square crossing profile applies. There is no claim for two fixed end dimensions. See [the proof](deep-gaussian-matrix-products.md), including the comparison to [Li and Woodruff](https://arxiv.org/abs/2108.09887) and [Hanin and Nica](https://arxiv.org/abs/1812.05994).

Pinned source commit: `ce27771d64413f2d5f408727c24bf73e394da1e7`. Run `bash replay.sh` for the finite exact checks.
