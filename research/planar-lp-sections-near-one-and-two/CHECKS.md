# Reproducing the finite checks

From this directory, using Python 3 without optimization:

```sh
python3 verify.py
python3 independent.py
```

Both commands use only the standard library and exact rational arithmetic. The first checks Fourier normalization and 435 symmetrized residue-class Hessian computations, including the self-conjugate angular mode for even dimensions. The second reconstructs the Fejér auxiliary-polynomial identities independently at four rational Poisson radii, as well as the moment identity and positivity of finite convexity differences.

For an optional numerical illustration with `mpmath` installed, run `python3 independent.py --areas`. It evaluates two nonregular competitors against the regular frame in dimension four, at five exponents. These are illustrations only: the proof neither assumes the samples lie in the unspecified neighborhoods nor extrapolates from them. The optional quadrature and a truncated Fourier sum give matching second-order coefficients within the script's stated tolerance. See [CHECKS.txt](CHECKS.txt) for the recorded output.

The general statements (compactness, localization of all minimizers, uniqueness, differentiability across the moving cusps, and strict curvature for every fixed dimension) are analytic: see [the near-two proof](PROOF.md), [the near-one proof](NEAR-ONE.md), and [the separate internal audit](REVIEW.md). No floating-point comparison is used to certify them.
