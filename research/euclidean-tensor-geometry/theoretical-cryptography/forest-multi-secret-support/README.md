# Exact source-support classification on every forest

This directory gives a complete answer for graph-CMSS on a forest.

Let G be a finite simple forest and D a nonempty binary domain. A vertex is active when its coordinate is nonconstant on D. An edge uv is a pair edge when x_u XOR x_v is constant on D, and an active vertex is pair-covered when it touches a pair edge. Call vertices of degree at most one terminal.

Then the minimum source support is exactly:

- 1, if every active vertex is pair-covered;
- 2, if every active terminal vertex is pair-covered but some active vertex is not;
- infinity, if some active terminal vertex is not pair-covered.

The source may have arbitrary positive weights and the edge alphabets may be arbitrary finite sets. Thus the infinity case rules out every finite-randomness scheme, not only linear or uniform schemes.

The proof combines a direct leaf obstruction with a self-contained fair-bit construction on the non-pair-edge forest. Marszalik's general deterministic and one-bit characterizations are the main antecedents; the contribution here is the exact all-support forest classification, including feasibility.

Run:

    bash replay.sh

This is an information-theoretic graph theorem. It does not analyze a deployed protocol or cryptographic implementation.
