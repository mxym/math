# Scope, literature screen and proof provenance

The research branch began from main 8353cff72 and rechecked origin/main
310c7e311 before this direction. Existing all-unweighted graph Lean results,
the complete weighted triangle source and actual absence of AGENTS.md were
checked. Frozen proof packages were not changed.

Primary screening read Pant--Singh, arXiv:2604.24192v2 (18 September 2026),
Theorems 3.1, 4.3, 5.3, 5.4 and the hereditary-closure appendix. Its
bipartite theorem already covers arbitrary weights at the matrix level;
the cycle/cactus graph proofs use the unweighted Laplacian. Those completed
inputs and the repository's weighted triangle were excluded as new targets.
Motzkin--Straus's original 1965 paper was consulted and its needed clique-two
proof is included. The result uses published Lieb as an explicitly disclosed
ordinary-mathematical input. Searches cannot establish historical priority.

Actual weighted-Laplacian experiments suggested testing a stronger matching
upper bound. They did not prove it. The universal odd-cycle proof instead
came from a direct independent-neighbor-choice model: empty mutual matching
probability equals the two oriented whole-cycle probabilities, and comparing
one matching with the intersection of two independent matchings bounds the
actual two matching partition functions. Singular determinant cancellation
and a classical triangle-free spectral estimate close the proof for every
odd length at least five and every conductance ratio.

The companion standard-library code computes actual Laplacian permanents
and probabilities exactly. Its 24 cycle and 1402 principal/diagonal cases
are auxiliary diagnostics, not extrapolation to all sizes. The all-size
proof is the manuscript. Both final Windows and WSL runs bind the actual
source hashes, use the same checker, and are not independent human refereeing.
No Lean formalization, old-log revalidation, Release or DOI is asserted here.

The all-weighted-graph problem remains open in this package. A five-vertex
defect expansion had negative coefficients, so a naive coefficientwise
argument was rejected; this is not an original-matrix counterexample.
The derived universal squared-edge matching-polytope condition alone also
does not close the quantitative permanent comparison. No hypothetical or
numerical bridge is a premise of the cycle/block theorem.

Research, discovery computation and writing used OpenAI AI assistants.
No external funding or external human peer review. Original material is
copyright 2026 Yongxian Zhang, all rights reserved; third-party rights preserved.
