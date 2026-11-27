# Zero adjoints and a near-bent degree counterexample

Two explicit quadratic almost perfect nonlinear maps have a nonzero input where their exclude parity adjoint is zero. A self-generated ten-variable finite-field map already suffices. A seven-variable polynomial, derived from a cited public classification, provides a smaller odd-dimensional example.

The ten-variable example also refutes Proposition 6.4 of [Carlet–Thornburgh, arXiv:2608.23888v2](https://arxiv.org/html/2608.23888v2): on the indicated input hyperplane, the near-bent component indicator has Boolean degree **8, not 9**. The correct universal criterion in the proposition's setting is degree \(n-1\) if and only if the adjoint value at the hyperplane normal is nonzero. The proof identifies the vector of hyperplane parities and repairs the use of nonvanishing in the separate Gold calculation.

This does not dispute existence of the adjoint or the paper's proof of Gorodilova's conjecture. It does not resolve Open Problem 5.7 on inverse-component degrees.

## Replay

Run `sh replay.sh` from this directory with Python 3.10 or later. There are no dependencies beyond the standard library and no download requirement. The two programs separately certify derivative structure, adjoint zeros and the near-bent degree. See [PROOF.md](PROOF.md) for the all-parameter argument, [RESULTS.txt](RESULTS.txt) for the expected log and [SOURCES.md](SOURCES.md) for exact primary-source locations and an optional upstream data check.
