# Verification and review

Run `python3 verify.py` with [mpmath](https://mpmath.org/) and compare the results with [CHECKS.txt](CHECKS.txt). To check file integrity run `sha256sum -c SHA256SUMS` from this directory.

1. The script checks the scalar Bregman comparison in 7,560 exact rational signed instances. Rational powers in the test family are evaluated as integer powers of rationals. It also checks the stronger same-sign Young bound.
2. It checks the scalar finite-list ingredient in 19,440 nondecreasing integer lists, covering lengths two through ten for entries between −3 and 3.
3. It evaluates the cyclic ratio at eight exponents (including a noninteger), from 256 to 100,000,000, using 83 decimal digits. It checks the derivative signs at the bisection endpoints, compares the stationary ratio with a separately computed ratio of coordinate norms, samples the full compact parameter interval, and reports the scaled remainders. These are descriptive numerical checks, not uniform estimates or interval certificates.

A separate internal AI-assisted review checked the two-sided signed scalar inequalities, spectral lifting and variational transfer, extension to arbitrary finite lists, localization of all maximizing parameters, eventual strict concavity of the level function, and the three-term expansion. It also checked the large-exponent diagonal variational premise against Esa’s pinned source. The review identified no gap in the stated results. The proofs, not the finite tests, support the universal claims. No unaffiliated external review is represented, and the prior Lean development does not certify this note.
