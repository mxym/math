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
