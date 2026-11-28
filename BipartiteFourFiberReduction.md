# The at-most-five-orbit reduction in the bipartition-preserving case

The main paper refers to the prior general [five-orbit theorem and sharpness archive](https://github.com/mxym/math/releases/tag/erdos-gyarfas-abelian-five-orbit-threshold-v1.0.0). This short explanation gives a smaller dependency for the particular bipartition-preserving class here, using just one of the already published four-orbit voltage certificates. It does not add a separate theorem claim.

Assume there are no simple cycles of lengths 4, 8 or 16. As in the main paper, three matchings between a pair would give a short cycle, and doubled pairs must be disjoint because the two steps in a shared layer give a square or an eight-cycle. If one side of the quotient has only one layer, the layers on the other side have degree at most two. If one side has two layers and the other has at least three, each layer on the larger side requires a double to reach degree three; disjointness allows at most two such doubles.

Thus, if there are at most five layers, the only case left is a two-plus-two quotient. Every row and column has both entries positive and exactly one double, so, up to column exchange, its matching multiplicity matrix is
\[
                         \begin{pmatrix}1&2\\2&1\end{pmatrix}.
\]
This is the old \(\texttt{0000012210}\) template of the [four-orbit theorem](https://github.com/mxym/math/blob/b335081a1fc3f41d393c78851f4a2b2c87fcac16/research/euclidean-tensor-geometry/theoretical-cryptography/FactorErdosGyarfasAbelianFourOrbits.md). The [included extraction and replay](verify_erdos_gyarfas_bipartite_four_corner.py) uses the exact previously stored 17-state table. Use left fibers 0,1 and right fibers 2,3, with tree matchings \(02,03,12\) labeled zero. The second \(03\), second \(12\), and the single \(13\) have independent formal voltage coordinates. The first two nonzero constraints are precisely distinctness of the doubled matchings.

The integer relation-lattice verification is identical in soundness to the main paper. Every admissible evaluation has all relations at the current node. A prescribed word closes; if it repeats a lifted vertex there is a same-fiber difference that vanishes in the evaluation. The extended relation lattice is either another checked state, or makes the shift of one of the doubled matchings zero, contradicting simplicity. Each child increases the lattice and the explicit finite table covers all such choices, so a short cycle must occur. Both the local proof and the full previously available theorem justify the six-layer reduction.
