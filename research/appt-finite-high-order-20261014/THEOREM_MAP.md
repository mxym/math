# Exact finite APPT power extrema: proof obligations

Prepared before the manuscripts on 14 October 2026. This continues the same
APPT entropy programme; it does not count as a separate major conjecture.

| Statement | Bridge on the actual mathematical object | Input and verification boundary |
| --- | --- | --- |
| P1: for every integer D≥8 and real α≥2, the outer spectral polytope power maximum is max_j (j3^α+D−j)/(D+2j)^α | Complete vertex list; size-biased convex comparison excludes all other vertex families. Retain the nonphysical D=8, α=2 rank-six exception in the outer equality statement. | Tran 2609.18568v1 Lemma 2.1 and the known purity comparison in Theorem 2.2 are credited. Needed elementary comparisons are written out. Ordinary proof only. |
| P2: actual 2⊗n, n≥4, APPT and ASEP exact Rényi minimum for every real α≥2, with all equality states | Actual all-unitary PPT of (I+2P)/(D+2rank P); exclude the singular outer exception by the rank-two physical inequality; use Johnston's qubit–qudit APPT=ASEP theorem for ASEP. | Johnston 1309.2006 Theorem 1 is a disclosed published external input. No analogous APPT=ASEP assumption for m≥3. |
| P3: explicit optimal integer ranks and unique rank-one phase for D≥8, α≥D/2+1 | Differentiate the finite real-rank formula; compare only the clipped floor and ceiling of its unique critical point. Strict convexity excludes mixtures of equality vertices. | New ordinary real-power argument; α=2 reproduces known purity, not newly solved purity. |
| H1: every actual m⊗n, D≥6, α≥D/2+1 has exact rank-one spike Rényi minimum and full equality classification | P1/P3 for D≥8; rigorous D=6 vertex comparisons; actual attainment by an absolutely separable pole in every bipartite dimension. | D=6 is proved separately, not inferred from the D≥8 theorem. Pole separability is a credited known endpoint with an explicit finite product decomposition supplied here. |
| H2: actual 2⊗2, α≥24, has the same unique pole spectrum | Necessary physical rank-two determinant inequality controls the three tail deviations when the top eigenvalue approaches its cap; a separate far-from-cap real-power bound is strict. | The linear outer relaxation alone is insufficient. Both regions and equality at the cap are proved on actual densities. The constant 24 is sufficient, not optimal. |
| H3: a dimension-only eventual-pole cutoff must have order D | Actual qubit rank-two projection competes with the pole at α=cD; its moment ratio tends to 2 exp(−2c). | Actual APPT/ASEP competitors, not arbitrary outer spectra. This establishes order Θ(D) together with H1, not a sharp universal transition constant. |

The existing rank-two necessary inequality in
`../appt-growing-renyi/EXACT_SMALL_ORDER.md` is inherited and rederived in
the new manuscript. No older Lean log proves the new real-power extrema.
No Lean source, root list, axiom, build, or audit is added or expanded.
Finite exact/numeric diagnostics will check formulas and negative controls;
they will not substitute for the continuous-order proofs above.

The literature record will distinguish prior vertices, purity, von Neumann
entropy and white-noise separability from this continuation. A bounded search
does not certify historical priority or absence of all earlier work. The
general finite minimum below the displayed bands for m≥3, the small-qubit
intermediate-order minimum, and complete formalization remain outside scope.
