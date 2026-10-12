# Sources and scope

Checked on 8 October 2026.

1. Priyanshu Pant and Ranveer Singh, *Structural Classes for Chollet's Permanent Conjecture*, arXiv:2604.24192v2, revised 18 September 2026. [Version history](https://arxiv.org/abs/2604.24192), [full latest manuscript](https://arxiv.org/html/2604.24192v2).
   - Section 2 specifies that its graphs are simple and defines their ordinary Laplacians.
   - Section 6 expressly asks both whether the self-Chollet inequality holds for every graph Laplacian and whether the stronger degree-product inequality holds.
   - Lemma 1 states Lieb's block permanent inequality. Theorem 4.3 and Appendix A establish hereditary strong closure under one-point sums. Theorem 5.3 handles cycles. These results are credited in the proof; the closure and cycle arguments needed here are also supplied in full.

2. Jack Edmonds, *Maximum matching and a polyhedron with 0,1-vertices*, Journal of Research of the National Bureau of Standards B 69B (1965), 125–130. [Original paper](https://nvlpubs.nist.gov/nistpubs/jres/69B/jresv69Bn1-2p125_A1b.pdf), [DOI](https://doi.org/10.6028/jres.069B.013).
   - The full matching polytope includes nonnegativity, vertex constraints, and constraints for every odd vertex set. The proof checks all three families, not merely the fractional degree constraints.

3. Elliott H. Lieb, *Proofs of some conjectures on permanents*, Journal of Mathematics and Mechanics 16 (1966), 127–134. [DOI](https://doi.org/10.1512/iumj.1967.16.16008).
   - Only the established non-strict block-product lower bound for Hermitian positive semidefinite matrices is used. No unresolved permanental-dominance statement or equality characterization is assumed.

The checked arXiv version history lists v2 as the latest version. Searches of subsequent public work and the current OpenAI mathematics catalogue did not locate an earlier full solution of these all-graph questions. This is a record of the sources checked, not a guarantee of originality or priority.

The theorem's quantifiers are all finite simple unweighted undirected graphs, including disconnected graphs and isolated vertices, and all principal submatrices. Degrees remain the degrees in the original graph when taking a principal submatrix. The empty-matrix permanent is 1. No claim is made for arbitrary positive edge weights, loops, multigraphs, or arbitrary Hermitian positive semidefinite matrices.
