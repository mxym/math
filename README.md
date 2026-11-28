# The Exact Mahler Minimum in the Uniform Mod-Three Reciprocal Class

Among monic reciprocal integer polynomials of positive even degree, with constant coefficient 1, every inner coefficient congruent to 2 modulo 3, and no root of unity, the Mahler measure is minimized uniquely by x^4-x^3-x^2-x+1. Its measure lies strictly between 1.7220 and 1.7221; every other polynomial in this class has measure greater than 1.724. The result places no bound on degree, coefficient height, or reducibility and does not concern unrestricted Lehmer.

The condition is **no root of unity**, not “no root on the unit circle”: roots of modulus one which are not roots of unity are allowed, and the minimizer has such roots.

- [Main proof](FactorLehmerExactModThreeMinimum.md): the reciprocal three-circle inequality proves the higher-degree result for every even degree at least twelve; direct/resultant checks handle degrees two, four and six.
- [Finite low-degree proof](FactorLehmerSmallModThreeMinima.md): the exact degree-eight and degree-ten certificates needed by the main theorem. The linked proof also contains a separate degree-fourteen calculation, which is not a dependency of the main result.
- [Independent checker](verify_factor_lehmer_mod_three_independent.py): a separate moment-and-root-power audit at threshold 1.724 for degrees two, four, six, eight and ten; only the specified quartic survives. It uses no Schur tests, exterior powers, floating-point root finding or coefficient-height cutoff. Run it with Python assertions enabled.
- [Slice manifest](SLICE.json) records the pinned research sources and normal-mode commands. [Release metadata](release-metadata.json) is supplied for the planned publication; presence of this file is not a release or DOI registration.

Run `bash replay.sh` (Python 3 and `sha256sum`, standard library only). It verifies the manifest and runs all three checkers in normal Python mode.
