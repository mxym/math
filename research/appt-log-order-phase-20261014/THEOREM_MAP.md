# Logarithmic spectral comparison and sharp pole transition: proof obligations

Prepared before the manuscripts, 14 October 2026. A continuation of the same
APPT entropy direction, with no additional major-conjecture count.

| Statement | Necessary bridge | Input and verification scope |
| --- | --- | --- |
| L1: every integer D≥15 and real α>1 has outer power maximum max_j (j3^α+D−j)/(D+2j)^α | Known complete outer vertex list. Size-biased log measures, strict entropy-mean gaps and a full stop-loss comparison exclude every T and uniform vertex, including the two missed first indices. | New ordinary real-power argument. Prior Tran vertices, purity index and entropy facts credited; the needed elementary entropy bounds and comparisons are written out. |
| L2: actual qubit–qudit, n≥8, every real α>1, exact Rényi minimum and every equality state | Actual all-unitary construction (I+2P)/(D+2rank P), Johnston's disclosed APPT=ASEP theorem and physical necessity. | Reuses explicit physical bridges from POWER_ENVELOPE; no extrapolation to arbitrary m≥3 or small-n intermediate orders. |
| L3: explicit maximizing integer ranks at every α>1 | Exact derivative, positivity of 3^α−1−2α and clipped floor/ceiling. | Ordinary finite optimization; α=1 limit is known von Neumann entropy, not newly counted. |
| C1: for every D≥8 a unique tau_D>2 solves the rank-two/rank-one moment crossing | Full real-order ratio derivative, strict convexity on (0,1), its single positive-order peak after1, and exact positivity at2. | Mathematical proof of uniqueness, not a numerical root scan. |
| C2: actual qubit–qudit n≥4, the pole is optimal exactly when α≥tau_D for all α>0 | Actual rank-two projection beats it below tau_D, including α=1 separately; old α≥2 outer theorem proves sufficiency and all critical equality states. | Complete phase criterion for this family, not a formula for every subcritical minimum. |
| C3: all dimension pairs D≥8, pole optimal at α≥tau_D; uniqueness at the critical point when m≥3 | Only outer equality spectra are rank-one/rank-two plateaus. A rational actual 3⊗3 negative control excludes the rank-two plateau for all m≥3. Pole is ASEP by the credited white-noise endpoint. | Does not assume general APPT=ASEP. For odd D or m≥3 below the cutoff, no necessity or exact partition-specific transition is asserted. |
| C4: sharp worst-partition transition constant and expansion | Crossing identity, exponentially small correction, and the expansion of 2atanh[1/(D+3)]. Quibit actual competitors make the universal bound sharp along even D. | tau_D=(log2)(D+3)/2−(log2)/[6(D+3)]+O(D^−3); no finite numerical fit substitutes for the proof. |

Inherited ordinary inputs are explicitly linked to the finite high-order
packet. Its 558-line review remains bound to its original four files; it
does not review the new manuscripts. No Lean module, build, axiom, audit root
or prior audit coverage is added. An independent fresh internal read will be
recorded for the new version. Supporting finite rational certificates and
evaluated real-order examples are separate from the general proofs.
