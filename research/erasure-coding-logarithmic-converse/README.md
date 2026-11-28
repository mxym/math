# Logarithmic remainders for fixed-error erasure coding

For a fixed erasure probability 0 < p < 1/2 and fixed input dimension d ≥ 2, we prove an O(log n) converse remainder in the Gaussian expansion for unassisted private and quantum communication over n uses. The logarithmic code size is measured in bits. This answers the O(log n) remainder part of Wilde, arXiv:2611.32395v1, Appendix D.5. With Wilde's existing lower bounds, the expansion has a two-sided O(log n) remainder.

The result covers entanglement transmission, entanglement generation, and the optimized, maximal-message, and actual-environment-marginal joint private criteria. The first four retain the normal quantile at ε; the actual-marginal criterion retains the quantile at 1−√(1−ε). Neither the third-order coefficient nor the necessity of maximal-message expurgation is determined.

The proof keeps Wilde's quantum overlap and fidelity reductions. It builds signed averaging matrices directly on the erasure-count layer, then varies the polynomial degree with the distance from the Singleton threshold before taking the binomial expectation. Johnson and Kneser spectra and the Chebyshev inequalities used in the proof are classical.

See PROOF.md for the theorem and SOURCES.md for the exact source and prior-art scope. The standard-library replay checks small slices by exact rational enumeration and independently tests the scalar filter and threshold summation. The checks are not needed by the proof.

```sh
bash replay.sh
```
