# Lean formalization: bipartite sector of the strong Chollet graph theorem

**Verification status: the full bipartite sector is proved in Lean; the theorem for ALL simple graphs is NOT yet formalized.**

The full written all-graph argument is in [the research note](../../notes/laplacian-chollet-general/README.md). This new Lean package proves an independently useful universal graph subclass and does not claim the missing nonbipartite proof.

## Literal theorem

**Chollet.strongChollet_of_isBipartite** proves, for EVERY finite simple bipartite graph G and EVERY vertex subset S (including the empty subset),

\[
\operatorname{per}(L_G[S]\circ L_G[S])
\leq \operatorname{per}(L_G[S])\prod_{v\in S}\deg_G(v).
\]

The theorem's conclusion is the precise shared Lean predicate **Chollet.StrongChollet G** from Target.lean. It uses the actual Mathlib **SimpleGraph.lapMatrix**, actual **Matrix.permanent**, and vertex degrees in the original graph G, not the induced graph. No hypothesis requires connectivity, positive degrees, a bound on the number of vertices, or an invertible Laplacian.

## Compiled source chain (src/)

- **Nonnegative.lean** proves the all-orders permanent inequality for every entrywise nonnegative real matrix A satisfying the diagonal pairwise bounds (A i j)^2 <= A i i * A j j. Its proof compares every nonnegative permutation monomial term-by-term with the diagonal product, then sums over all permutations.
- **Signed.lean** proves that multiplying rows and columns by the same diagonal signs s_i with s_i^2=1 leaves the permanent, Hadamard square and diagonal unchanged. It transfers the result to sign-switchable matrices.
- **Bipartite.lean** derives all needed pairwise estimates for the actual graph Laplacian, proves positivity after switching by a bipartite sign coloring, and uses Mathlib's graph bipartition theorem. Its intermediate proof works simultaneously on every principal submatrix.
- **Target.lean** defines the exact stronger arbitrary-graph goal as a proposition; it does not assert the goal is proved.
- **GraphMain.lean** closes the bipartite instance of that SAME target proposition and invokes the axiom audit.

The final theorem and two supporting permanent inequalities were rebuilt by Lean 4.34.1 with exit status 0. The axiom query for the final graph theorem reports only **propext**, **Classical.choice**, and **Quot.sound**. There is no sorry, admit, native_decide, unsafe proof, or custom mathematical axiom.

## Reproduction

The official pinned toolchain is Lean **4.34.1** (compiler SHA 5045d0056413266e57c625dcd7c365b10e377c52) with Mathlib SHA **d13f23b723b8a846827a245b89c10fc7d3f11612**. Provision pinned Mathlib and its dependencies and work in an isolated directory accessible to the configured LEAN_PATH. Compile, in order:

1. Nonnegative.lean (creating Nonnegative.olean)
2. Signed.lean (creating Signed.olean)
3. Target.lean (creating Target.olean)
4. Bipartite.lean (creating Bipartite.olean)
5. GraphMain.lean

The source compiler completed all five mathematical units. The GraphMain.lean file runs the #print axioms command on the final graph theorem. **No independent empty-environment kernel replay or full Mathlib source rebuild is claimed**; source compilation and Lean axiom reporting have their usual, narrower verification meanings.

## What remains

The complete ALL-graph theorem requires separate Lean proofs of Lieb's PSD block permanent inequality, Edmonds' matching-polytope characterization, the logarithmic directed-cycle upper bound, the 2-connected noncycle matching feasibility, odd cycle cases and closure under graph blocks and one-point sums. The written mathematical proof provides these steps but they are not silently converted into formal premises. The unrestricted Hermitian positive-semidefinite Chollet conjecture is a still broader problem and is not asserted.

**Publication boundary:** This is a formally compiled graph subclass of the repository's existing result, not a full formalization of the all-graph statement, a historical novelty certificate or human peer review.
