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


## Additional Lean-checked theorem: arbitrary ambient graph with bipartite induced subset

The new [Induced.lean](src/Induced.lean) strengthens the scope beyond globally bipartite graphs:

For **every** finite simple graph G, whether or not G is bipartite, and every vertex subset S such that the actual induced graph G.induce S is bipartite, the original-degree principal Laplacian satisfies

\[
\operatorname{per}(L_G[S]\circ L_G[S])
\le \operatorname{per}(L_G[S])\prod_{v\in S}\deg_G(v).
\]

This is the exact theorem **Chollet.strong_chollet_principal_of_induced_bipartite**. The original diagonal entries are not changed to the induced graph's degrees. The source builds the required local ±1 sign switch on the subtype of S directly from Mathlib's induced-graph bipartition and checks every diagonal/offdiagonal inequality for the genuine G.lapMatrix. It proves the theorem from the previously published sign-switch permanent lemma, with no assumed external inequality.

It compiled using Lean 4.34.1 and pinned Mathlib d13f23b723b8a846827a245b89c10fc7d3f11612. The #print axioms result is exactly [propext, Classical.choice, Quot.sound], with compiler exit 0 (three deprecation warnings only). This is source compilation and a standard axiom report, not an independent empty-kernel replay. This extension applies in particular to all proper principal submatrices of a triangle and more generally to all S inducing forests, even when the original G contains odd cycles elsewhere.

Reproduce it after compiling Nonnegative.lean and Signed.lean and extending LEAN_PATH by their compiled objects: compile src/Induced.lean with the same pinned Lean/Mathlib environment.

The **full all-graph theorem remains open in Lean**. In particular this proof does not treat principal submatrices whose induced support itself contains odd cycles, except for separate explicitly verified cases such as the [weighted 3-cycle identity](../laplacian-chollet-triangle/README.md).

## Two new all-orders algebraic steps toward block gluing

The addition [BlockClosureAlgebra.lean](src/BlockClosureAlgebra.lean) formalizes two universal quantified polynomial inequalities used in Section 5 of the written full-graph proof.

**diagonal_increment_algebra**: if Q <= a*h*P, T <= h*R and a*R <= P, with a,h,t nonnegative, then
`Q+(2*a*t+t^2)*T <= h*(a+t)*(P+t*R)`. This is the exact algebraic statement required when a diagonal is increased by t, provided that the separate permanent-update formulas and Lieb singleton pivot inequality have been proved.

**one_point_sum_algebra**: under the corresponding two-block strong-minor and singleton-pivot inequalities and explicit nonnegativity conditions, the exact one-point-sum squared-permanent upper expression `Q1*T2 + T1*Q2 + 2*a1*a2*T1*T2` is dominated by `h1*h2*(a1+a2)*(P1*R2+R1*P2)`. This handles arbitrary real parameters and includes zero diagonals.

Both statements compile using pinned Lean 4.34.1 and Mathlib. Their `#print axioms` listings contain only `propext`, `Classical.choice`, and `Quot.sound`; there are no admitted proofs. **The statements are algebraic lemmas with precisely stated premises, not purported proofs that the full matrix permanent satisfies those premises.** In particular the permanent gluing identities and Lieb's PSD singleton inequality remain unformalized, so the arbitrary-graph strong Chollet theorem remains out of reach in the current Lean package.


## Exact matrix-level permanent update and diagonal-stability theorem

Three additional source modules extend the original graph proof to a fully general real-matrix algebraic step, with all missing assumptions explicit.

1. [PermanentDiagonal.lean](src/PermanentDiagonal.lean) proves, for arbitrary finite-index square real matrices A and arbitrary t, the exact linear dependence of \`Matrix.permanent\` on a single diagonal entry. Its coefficient is a sum over permutations fixing that vertex; this identity is proved from the Mathlib permutation-sum definition.
2. [CofactorOption.lean](src/CofactorOption.lean) proves that the fixed-vertex coefficient, when the distinguished vertex is \`Option.none\`, equals **the permanent of the genuine principal deletion**. The proof uses Mathlib's exact permutation decomposition of \`Option α\`, not an external certificate.
3. [PermanentDiagonalMinor.lean](src/PermanentDiagonalMinor.lean) combines this with [Reindex.lean](../laplacian-chollet-triangle/Reindex.lean) to prove the universally quantified exact identity for any square real matrix and any distinguished index:

   \[
   \operatorname{per}(A+tE_{vv})
   =\operatorname{per}(A)+t\operatorname{per}(A[V\setminus\{v\}]).
   \]

   No assumption of PSD, symmetry, nonnegativity or nonzero diagonal entries is imposed.
4. [PermanentDiagonalStability.lean](src/PermanentDiagonalStability.lean) upgrades the previously published scalar closure lemma to the **literal Mathlib matrix permanent**. The theorem \`Chollet.strongChollet_diagonalBump_of_pivot\` states that the strong inequality for a matrix and its genuine principal deletion, plus nonnegative diagonal entries and the explicit *singleton permanent pivot inequality* \(\operatorname{per}(A)\ge A_{vv}\operatorname{per}(A[V\setminus\{v\}])\), implies that increasing \(A_{vv}\) by any \(t\ge0\) preserves strong Chollet on that matrix. It proves the exact squared-matrix update \((A+tE_{vv})\circ(A+tE_{vv})=(A\circ A)+(2A_{vv}t+t^2)E_{vv}\) and the updated diagonal-product formula inside Lean.

All four source files were actually compiled with pinned Lean 4.34.1 and Mathlib commit \`d13f23b723b8a846827a245b89c10fc7d3f11612\`. The final statements \`permanent_diagonalBump_principal\` and \`strongChollet_diagonalBump_of_pivot\` passed \`#print axioms\` with only \`propext\`, \`Classical.choice\`, and \`Quot.sound\`; no source uses \`sorry\`, admitted proofs, or custom axioms.

**Important open dependency:** the singleton pivot bound is not asserted for all PSD matrices here. It is an explicit theorem hypothesis. Likewise, the universal one-point graph block permanent identities are NOT claimed completed. The overall all-finite-graphs strong Chollet theorem remains unformalized.

## New: general real PSD matrix permanent nonnegativity

The following four Lean modules establish the entire unrestricted ALL-ORDER REAL PSD permanent-positivity theorem (NOT the stronger Lieb PSD block-permanent bound):

- [OrbitGramPositivity.lean](src/OrbitGramPositivity.lean): a positive sum-of-squares identity for correlations along arbitrary finite group actions on finite sets.
- [GramPermanentNonnegative.lean](src/GramPermanentNonnegative.lean): nonnegativity of the genuine Matrix.permanent of the Gram matrix of any finite real rectangular array, using official permutation sums and the orbit lemma.
- [PSDRealGramFactor.lean](src/PSDRealGramFactor.lean): every finite real PSD matrix, INCLUDING SINGULAR matrices, has an actual real Gram factorization, proved using the real Hermitian spectral theorem and nonnegative eigenvalue square roots in Mathlib.
- [PSDRealPermanentNonnegative.lean](src/PSDRealPermanentNonnegative.lean): combines the previous two sources to prove Chollet.posSemidef_permanent_nonneg for every finite-dimensional real PSD matrix, without an entrywise sign restriction.

All four sources successfully compiled on Lean 4.34.1 with Mathlib SHA d13f23b723b8a846827a245b89c10fc7d3f11612. The main source theorem axiom audit lists ONLY propext, Classical.choice and Quot.sound. No sorry, admit, native_decide or custom axioms.

This proves general PSD permanent NONNEGATIVITY, not Lieb's stronger PSD BLOCK comparison. Lieb's block bound, the graph noncycle matching inequalities and the odd-cycle identification remain essential missing Lean dependencies for unrestricted graph strong Chollet.
