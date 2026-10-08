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
