# Strong Chollet graph Laplacian: precise Lean status

**As of 2026-10-08: no full Lean proof of the arbitrary finite simple graph theorem has been completed or claimed.** The complete ordinary mathematical proof is [here](../notes/laplacian-chollet-general/source/proof.txt).

## Formal theorem already closed

The general target is defined in [Target.lean](laplacian-chollet-bipartite/src/Target.lean) as \`Chollet.StrongChollet G\`, using the actual Mathlib graph Laplacian and every principal vertex subset S, with degrees from the original graph.

Actual Lean 4.34.1 builds with pinned Mathlib SHA \`d13f23b723b8a846827a245b89c10fc7d3f11612\` completed successfully for:

1. \`Chollet.nonnegative_permanent_hadamard_bound\`: all finite-index entrywise-nonnegative real matrices satisfying the 2-by-2 diagonal bounds.
2. \`Chollet.sign_switch_permanent_hadamard_bound\`: all finite matrices whose entries can be switched nonnegative by diagonal signs.
3. \`Chollet.strongChollet_of_isBipartite\`: the **literal all-principal target** for every finite simple bipartite graph.
4. \`Chollet.strong_chollet_principal_of_induced_bipartite\`: for **every** ambient finite graph G, regardless of bipartiteness, and every S for which the induced graph on S is bipartite, the literal original-degree principal inequality holds.
5. \`Chollet.permanent_three_formula\`: the actual six-term permanent of any 3x3 real matrix derived by Lean from the official permanent definition.
6. \`Chollet.triangle_laplacian_exact\`: the exact identity for weighted triangle matrices, with the explicit nonnegative factored slack for edge weights x,y,z≥0.
7. \`Chollet.permanent_reindex_equiv\`: the permanent of any finite real square matrix is unchanged under a simultaneous equivalence of its index type.
8. \`Chollet.complete_three_graph_strongChollet\`: the original full target for the actual nonbipartite complete 3-vertex graph, on every principal vertex subset.
9. \`Chollet.strongChollet_fin_three\`: the original full target for **every** finite simple graph on \`Fin 3\`, including all principal submatrices and any isolated vertices.

All statements above have compiled with exit code 0. The \`#print axioms\` audits for their final theorem roots report only \`propext\`, \`Classical.choice\`, and \`Quot.sound\`; no source contains \`sorry\`, \`admit\`, \`native_decide\`, or custom mathematical axioms. This status reports source recompilation and Lean's axiom reports, **not** a separately executed empty-trust kernel replay of the entire source closure. The pinned official Mathlib compiled cache was reused; Mathlib itself was not independently rebuilt from zero.

## Public files and source ownership

- [Bipartite, arbitrary-induction and general target package](laplacian-chollet-bipartite/README.md)
- [Triangle, K3 all subsets, and all 3-vertex simple graphs](laplacian-chollet-triangle/README.md)
- [Written general graph proof and independent ordinary mathematical review](../notes/laplacian-chollet-general/README.md)

The triangle package imports earlier source modules by name from the bipartite package. Reproduce its combined development with one coherent LEAN_PATH and pinned dependencies; do not confuse a build from historical local objects with a completely fresh independent replay.

## The exact all-graph gap

None of the above implies the main statement \`∀ V, ∀ G : SimpleGraph V, Chollet.StrongChollet G\`. The proof of that statement still requires substantial Lean work:

- The proof of the full odd cycle classes \`C_n\` for all odd n≥5 and their principal submatrices.
- A general proof of the Lieb PSD block permanent inequality, including singular PSD matrices, or another **proved** substitute supplying the required matching-block lower bound.
- A complete formal counterpart of Edmonds' matching-polytope/blossom theorem (or a suitable direct special-purpose rounding result) needed for all 2-vertex-connected noncycle blocks.
- The graph degree/odd-subset deficiency estimate, its logarithmic directed-cycle permanent upper bound and its matching lower bound.
- Hereditary closure under one-point graph-block gluing, including degenerate/isolated cases.
- An independent fresh source rebuild, axiom audit and empty-environment, trust-zero kernel replay on the finally completed theorem and its exact dependency closure.

No missing theorem is silently postulated as an axiom or a hypothesis equivalent to the all-graph conclusion. A green build of the finite-dimensional pieces is not a complete proof of the global main theorem. No human peer-review, absolute publication novelty or authorship priority is claimed.
