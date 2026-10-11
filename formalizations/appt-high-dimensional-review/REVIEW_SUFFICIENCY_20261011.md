# Independent review checkpoint: physical sufficiency

This review addresses the all-unitary sufficiency and projection-attainment side of the working APPT arguments. It does not assert full formal verification of their unrestricted purity/entropy asymptotics.

## Mathematical argument checked

For each local diagonal coordinate use its rank-one coordinate matrix E_ii. For distinct i,j, use S_ij=E_ij+E_ji and K_ij=E_ij-E_ji. Their lifted congruences act on the original complex bipartite matrix. Direct entrywise expansion gives

    2 PT(P)+(m-1)I = 2 sum_i congruence(P,E_ii)
        +(1/2) sum_(i!=j) [congruence(P,S_ij)+congruence(I-P,K_ij)].

The sum on the right is over ordered distinct pairs; counting each unordered pair twice explains the one-half coefficient. No real-symmetry assumption on P is used in the identity. If 0<=P<=I, every summand is PSD. Unitary conjugation preserves those two inequalities, proving the physical APPT condition for (m-1)I+2P.

For a Hermitian idempotent P with trace k, exact multiplication and trace show the normalized state has the recorded purity. Every integer rank is realized by a coordinate subset, constructed in Lean rather than supplied as an assumed projector. The broad-plateau rank is implemented as the exact integer ceiling ((m-1)n+1)/2.

For sharpness, P_-= (I-F)/2 is the genuine antisymmetric orthogonal projection, where F swaps the two factors. Its partial transpose is controlled by PT(F)=|Omega><Omega|. The expectation of PT(cI+2P_-) at the unnormalized maximally entangled vector is m(c+1-m), negative for c<m-1. The wrong-constant regression additionally proves trace one and positivity of (I+P_-)/22 in 4x4 dimensions.

## Verification boundary

The four new modules are BlockContraction, PositiveMap, ProjectionState and SharpContraction. The audited existential theorem uses the original APPT.Quantum.IsDensity, AbsolutelyPPT and purity definitions. Local replay used a trust-zero empty kernel, 40,214 declarations, 34 roots, and only propext, Classical.choice and Quot.sound. The forged-proof control changes only the proof of exists_broad_plateau, not its statement.

These results do not prove APPT membership of the three-level counterexample with its extra spike. That requires a stronger joint projection/spike estimate; the new contraction bound alone is insufficient. Nor do they prove the exact rectangular upper bound, full maximizer classification, graph compactness limits, entropy extrema or rigidity. These gaps remain explicit.

Source transfer required extra care after an incomplete auxiliary checkout and a network failure. No incomplete Git index or unrelated deletions were committed. Each of the 34 final inputs was compared with the already audited WSL source digest before committing in a clean VPS worktree. Source transport and whitespace warnings do not replace a mathematical or kernel check. Independent CI is recorded separately when completed.
