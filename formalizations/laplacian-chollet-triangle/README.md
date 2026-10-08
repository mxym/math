# Nonbipartite base case: exact weighted triangle strong Chollet inequality in Lean

**Status:** Proved by Lean 4.34.1, including an exact polynomial identity for arbitrary real weights. This is an additive, unconditional nonbipartite finite-dimensional result. It does **not** prove the strong Chollet inequality for all finite graphs.

The single source file [Triangle.lean](Triangle.lean) imports official Mathlib and proves the literal sum-over-permutations formula for the permanent of **every 3-by-3 real matrix**. It then defines the actual weighted triangle Laplacian
\[
L=\begin{pmatrix}
x+y&-x&-y\\
-x&x+z&-z\\
-y&-z&y+z
\end{pmatrix}.
\]

The central Lean result \`Chollet.triangle_laplacian_exact\` is valid without assumptions on real weights:

\[
\operatorname{per}(L)\,(x+y)(x+z)(y+z)
-\operatorname{per}(L\circ L)
=2(xy+xz+yz)(x^2y^2+x^2z^2+y^2z^2).
\]

Consequently, \`Chollet.triangle_laplacian_strong\` proves the required inequality for **all nonnegative real edge weights x,y,z**, including zero weights and singular Laplacians. The strict weighted complete-triangle case is included. The proof uses the genuine Mathlib \`Matrix.permanent\`, not a hard-coded symbolic surrogate for permanent; the six-permutation reduction itself is proved from the library definition.

## Verification record

The source was compiled successfully in an isolated Ubuntu 22.04 WSL environment using:

- Lean 4.34.1, compiler SHA \`5045d0056413266e57c625dcd7c365b10e377c52\`.
- Mathlib pinned to \`d13f23b723b8a846827a245b89c10fc7d3f11612\`.

The real Mathlib module cache was obtained from its matching official version. The Lean compiler returned **exit code 0**, and the included \`#print axioms\` checks showed exactly \`[propext, Classical.choice, Quot.sound]\` for each of the three public declarations \`permanent_three_formula\`, \`triangle_laplacian_exact\`, and \`triangle_laplacian_strong\`. No custom axiom, \`sorry\`, \`admit\`, or \`native_decide\` is used. This is source-compilation and axiom-report evidence, not an independently rerun empty-kernel replay or a rebuilt Mathlib supply chain.

## Scope and integration

The shared [strong Chollet all-graph written proof](../../notes/laplacian-chollet-general/source/proof.txt) treats cycles, noncycle 2-connected blocks, and block gluing. The [preceding complete bipartite-subgraph Lean proof](../laplacian-chollet-bipartite/README.md) covers every finite bipartite graph and every principal submatrix of its genuine Mathlib Laplacian. The present theorem **adds a nonbipartite complete-triangle matrix case and allows arbitrary nonnegative real edge weights**, with an exact slack formula.

A full Lean theorem over **all** finite simple graphs remains unproved, notably the imported Lieb and Edmonds theorems, odd cycles of unbounded length, noncycle 2-connected block estimates, and block assembly. The written all-graph theorem's mathematical scope must not be attributed to this Lean package.

This is a formal component of the existing project's all-graph proof, not a priority assertion, independent human peer review, or a formalization of the unrestricted Hermitian-PSD Chollet conjecture.


## Additional original-graph correspondence theorem

The supplementary [K3.lean](K3.lean) closes the actual finite graph instance, rather than leaving the triangle as only a weighted matrix model:

**Chollet.complete_three_graph_full_laplacian_strong** proves the strong Chollet inequality for the full matrix \`(⊤ : SimpleGraph (Fin 3)).lapMatrix ℝ\`, with exactly the Mathlib graph degree product \`∏ i : Fin 3, ((⊤ : SimpleGraph (Fin 3)).degree i : ℝ)\`. Its preparatory kernel-checked theorem \`top3_laplacian_eq\` establishes equality with \`triangleL 1 1 1\`, including all three diagonal degrees and all three undirected edges.

This module was freshly compiled with pinned Lean 4.34.1 and exact Mathlib version, exit code zero. Both the public main theorem and the actual-graph matrix-identity proof depend only on \`[propext, Classical.choice, Quot.sound]\`. This is a **genuine nonbipartite graph case**, but it currently covers the full three-vertex matrix only; the full all-graph quantifier over arbitrary graphs and all principal subsets is not claimed. The separate [induced-bipartite principal-submatrix theorem](../laplacian-chollet-bipartite/src/Induced.lean) handles every principal subset with bipartite induced support, including proper subsets of the triangle.


## Closed literal all-principal target for the actual three-cycle

The additional [Reindex.lean](Reindex.lean) proves a general theorem: conjugate/reindex **any** finite square real matrix along an equivalence of index types and its Mathlib permanent is exactly unchanged. This lemma is proved directly from the permutation-sum definition, with no reindexing axiom.

[K3AllSubsets.lean](K3AllSubsets.lean) upgrades the earlier full-matrix case to the **literal shared all-subsets proposition**:

\`\`\`lean
Chollet.complete_three_graph_strongChollet :
  Chollet.StrongChollet (⊤ : SimpleGraph (Fin 3))
\`\`\`

Thus for the actual three-cycle, every principal submatrix—including empty and full—and the original graph degree product are covered. The proof invokes the previously proved arbitrary-ambient-graph bipartite-induced principal theorem for proper subsets; the full subset is handled by the exact weighted-triangle algebra and the newly proved permanent-reindexing equivalence. This closes the complete strong-Chollet target on one genuinely nonbipartite graph.

The source was **compiled by Lean 4.34.1 with exit code zero**, and \`#print axioms\` reported only \`propext\`, \`Classical.choice\`, \`Quot.sound\` for both \`complete_three_graph_strongChollet\` and \`proper_induced_bipartite_fin_three\`. For reproduction, compile the earlier bipartite package's \`Nonnegative.lean\`, \`Signed.lean\`, \`Target.lean\`, \`Induced.lean\`, then this package's \`Triangle.lean\`, \`Reindex.lean\`, \`K3.lean\`, \`K3AllSubsets.lean\` with the exact pinned toolchain and appropriate local LEAN_PATH. The former files are referenced, not copied or independently reauthored.

**Important:** The statement about the complete 3-cycle is not a theorem for arbitrary simple graphs. The analytic and combinatorial all-graph bridges remain missing in Lean; no nonbipartite universal theorem has been silently substituted.


## Complete three-vertex classification (all simple graphs, all principal subsets)

[AllFinThree.lean](AllFinThree.lean) further proves

\`\`\`lean
Chollet.strongChollet_fin_three
    (G : SimpleGraph (Fin 3)) [DecidableRel G.Adj] :
    Chollet.StrongChollet G
\`\`\`

This is an **unconditional theorem for every labeled simple graph on three vertices**, with the complete all-subsets inequality and original graph degrees. The proof shows that omitting any of the three possible edges gives an explicit two-coloring, hence invokes the previously proved all-bipartite graph theorem. If all three edges are present, the graph is the complete triangle, so it applies the verified all-principal theorem in K3AllSubsets. This includes disconnected graphs, isolated vertices, the empty principal matrix, and the full nonbipartite triangle.

AllFinThree.lean was compiled by the pinned Lean 4.34.1 toolchain **with exit code 0**, and the included axiom audit printed only \`[propext, Classical.choice, Quot.sound]\` for \`Chollet.strongChollet_fin_three\`. The source uses neither custom axioms nor admitted proofs. For reproducibility, also compile the bipartite package's \`GraphMain.lean\` and this package's \`K3AllSubsets.lean\` before AllFinThree.lean.

This finite three-vertex classification does **not** close the unrestricted arbitrary-order graph theorem, whose noncycle block/matching and cycle/block-gluing arguments still lack full Lean formalization.

## New uniform local theorem for arbitrary large graphs (Lean proved)

The additional source modules [TriangleDiagonal.lean](TriangleDiagonal.lean), [TriangleStieltjes.lean](TriangleStieltjes.lean), [DegreePair.lean](DegreePair.lean), [GraphTriple.lean](GraphTriple.lean) and [GraphTripleSubset.lean](GraphTripleSubset.lean) establish two new universal statements.

**Every real symmetric 3x3 diagonally dominant Z-matrix** of the form

    [a -x -y; -x b -z; -y -z c]

with nonnegative edge weights x,y,z and diagonal dominance a>=x+y, b>=x+z, c>=y+z satisfies

    permanent(A hadamard A) <= permanent(A) * a*b*c.

The proof uses a general diagonal-increment identity: increasing any one diagonal entry by an arbitrary nonnegative real preserves the strength inequality under the other two entries' elementary degree bounds. It does not enumerate graph parameters or approximate reals.

More substantially, **the actual Laplacian of EVERY finite simple graph**, regardless of ambient size and containing any number of odd cycles elsewhere, satisfies the strong Chollet inequality on **every principal subset S of size at most three**, with the degrees taken from the ORIGINAL ambient graph. The public theorem is:

    Chollet.strong_chollet_principal_card_le_three

Its cardinality-three core is:

    Chollet.strong_chollet_principal_card_three

GraphTriple.lean checks that the genuine Mathlib graph Laplacian on three distinct vertices is exactly the Stieltjes matrix, and DegreePair.lean proves, inside Lean, that adjacency indicators of two distinct candidate neighbors never exceed the original graph degree. GraphTripleSubset.lean transports this result through an explicitly constructed type equivalence from Fin 3 to the three-element subset; it combines it with the previous induced-bipartite theorem for subsets of size zero through two.

**Verification:** both TriangleDiagonal.lean and TriangleStieltjes.lean were compiled using pinned Lean 4.34.1 and Mathlib revision d13f23b723b8a846827a245b89c10fc7d3f11612, exit code zero. Both GraphTriple.lean and GraphTripleSubset.lean were likewise compiled successfully from source. Lean axiom audits for strong_chollet_stieltjes_three, strong_chollet_principal_card_three and strong_chollet_principal_card_le_three list only propext, Classical.choice and Quot.sound. No sorry, admitted lemma, or custom axiom is used.

This is an infinite ambient-graph theorem but a uniformly bounded principal-rank result. It **does not prove** the unrestricted all-graph theorem for principal subsets of four or more vertices; the missing noncycle-block/matching and block-gluing arguments remain explicit.
