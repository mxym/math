# Odd-cycle sector: exact all-length recurrence inequality in Lean

**Verification status: the infinite scalar monomer–dimer inequality is kernel-checked. The identification with the actual Mathlib cycle-graph Laplacian permanent is NOT proved here, and the arbitrary-graph strong Chollet theorem remains unformalized.**

The source [CycleMatchingBounds.lean](CycleMatchingBounds.lean) defines \`pathMatchingWeight d n\` by the two-step recurrence

\[
P_0(d)=1,\quad P_1(d)=d,\quad P_{n+2}(d)=dP_{n+1}(d)+P_n(d),
\]

and defines \`cycleMatchingWeight d n = P_n(d)+P_{n-2}(d)\`. It then proves *in Lean, for every natural n*:

\[
P_n(4)\le 2^nP_n(2).
\]

More strongly, for every \(n\ge3\), \`pathMatchingWeight_strict_gap\` and \`cycleMatchingWeight_strict_gap\` establish

\[
P_n(4)+2^{n+1}+2 \le 2^nP_n(2),\qquad
C_n(4)+2^{n+1}+2\le 2^n C_n(2),
\]

where \(C_n(d)=P_n(d)+P_{n-2}(d)\). (The displayed \(n\ge3\) variable corresponds to the file's \`n+3\`.)

This is exactly the **integer arithmetic inequality** needed if the expected cycle permanent formulas are independently proved:

\[
\operatorname{per}(L(C_n))=C_n(2)+2(-1)^n,\qquad
\operatorname{per}(L(C_n)\circ L(C_n))=C_n(4)+2,\quad n\ge3.
\]

For odd \(n\), the first formula reads \(C_n(2)-2\), and the proved scalar bound directly implies \( \operatorname{per}(L\circ L)\le 2^n\operatorname{per}(L)\). For even \(n\), the diagonal cycle term is positive and the same bound is more than sufficient.

**CRITICAL OPEN BRIDGE:** The two displayed identities involving the **actual** \`SimpleGraph.cycleGraph n\` and Mathlib's \`Matrix.permanent\` are conventional combinatorial expansions, but they are not Lean theorems in this package. In particular, neither a closed all-odd-cycle Lean theorem nor the arbitrary-graph Lean theorem may be inferred from the file.

The proof of the arithmetic inequalities is a real infinite induction on natural \(n\), using only two-step recurrence arithmetic, not a finite parameter sweep or \`native_decide\`. Lean 4.34.1 with Mathlib commit \`d13f23b723b8a846827a245b89c10fc7d3f11612\` compiled this source with exit code zero. All three theorem-root \`#print axioms\` outputs are precisely \`[propext, Quot.sound]\`; no unproved mathematical axioms or \`sorry\` are present.

Next priority is a **kernel-checked bijection/classification** of nonzero permutation terms of the cycle-graph Laplacian, proving the two permanent identities for all \(n\ge3\). That will yield an unconditional infinite odd-cycle result and remove one of the main all-graph gaps.

This source complements the independently checked [bipartite, one-point-sum and three-point-principal sectors](../LAPLACIAN_CHOLLET_LEAN_STATUS.md).


## Actual graph-theoretic Lean theorem for the five-cycle

**In addition to the all-length scalar recurrence, the first odd cycle beyond the triangle is now FULLY proved in Lean**, including all principal submatrices of the genuine Mathlib graph:

\`\`\`lean
Chollet.cycleFive_all_principal_strongChollet :
  Chollet.StrongChollet (SimpleGraph.cycleGraph 5)
\`\`\`

There is **no** assumption that a principal subset is bipartite or that the graph is otherwise decomposable. The full size-five matrix is genuinely nonbipartite, and all its proper induced subgraphs are checked separately. The source files are:

- [CycleGraphMatrix.lean](CycleGraphMatrix.lean): proved, in all graph sizes \(n\ge3\), that the actual \`SimpleGraph.cycleGraph (n+3)\` has degree two and Laplacian entries 2 on the diagonal and −1 on adjacent vertices.
- [CycleFiveInt.lean](CycleFiveInt.lean): proved **by Lean's exact integer reduction** that the permanent of the actual 5-cycle integer Laplacian equals 80 and that of its entrywise square equals 1366. No numerical solver, floating point or unchecked external certificate was used.
- [CycleFiveReal.lean](CycleFiveReal.lean): first proves integer-to-real cast preserves every finite matrix permanent and the library's Laplacian construction, then transfers the two exact integer values to the original real graph Laplacian. The strong inequality follows from the actual degree product \(2^5=32\): \(1366\le80\cdot32=2560\).
- [CycleFiveAll.lean](CycleFiveAll.lean): constructs an exact explicit two-coloring of the induced graph after any one of the five vertices is deleted, proves every *proper* principal set is bipartite, and uses the established [induced-bipartite principal-submatrix theorem](../laplacian-chollet-bipartite/src/Induced.lean). For the *entire* vertex set, it reindexes the genuine five-by-five graph Laplacian using the earlier proved arbitrary-equivalence invariant of the permanent. This closes the exact \`StrongChollet\` target on every one of the 32 subsets.

**Verification:** With Lean 4.34.1 and Mathlib SHA \`d13f23b723b8a846827a245b89c10fc7d3f11612\`, \`CycleFiveInt.lean\`, \`CycleFiveReal.lean\`, and \`CycleFiveAll.lean\` all compiled with exit code zero. The final \`#print axioms\` for \`cycleFive_all_principal_strongChollet\` reports only \`[propext, Classical.choice, Quot.sound]\`. These are genuine kernel-checkable proofs; there is no \`sorry\`, \`admit\`, \`native_decide\` or custom mathematical axiom.

**Still open:** The all-length scalar cycle inequalities above are proved, and the actual graph equivalence is proved at \(C_5\), but the all-\(n\) **permanent-to-matching recurrence identification** is not yet a Lean theorem. Hence the all-odd-cycle case, arbitrary biconnected noncycle blocks, Edmonds/Lieb inputs, and full arbitrary-graph strong Chollet theorem remain unformalized. This package must not be used as evidence they are complete.
