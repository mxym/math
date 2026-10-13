# Rectangular APPT equality classification

## Exact scope

For all integers m>=3 and n>=m^3-m-2, D=mn and t=ceil((m-1)n/2), the previously verified maximum is [D(m-1)^2+4mt]/[D(m-1)+2t]^2. The new source classifies all maximizing actual complex APPT density matrices, not just a selected spectral family. The unique decreasing maximizing spectrum is (m+1 repeated t times, m-1 repeated D-t times)/[D(m-1)+2t]. Equivalently the complete set of maximizers is one global-unitary orbit of the explicitly defined matrix roundedPlateauMatrix.

`appt_rectangular_isGreatest_iff_unitary` is the final physical statement. It assumes only the dimensions/cutoff and that the actual input matrix is a density matrix. Its left side uses the original all-global-unitary APPT predicate and IsGreatest of the actual purity-value set. Its right side asserts unitary conjugacy to the fixed representative; APPT and maximum attainment on that side are conclusions, not supplied assumptions. `density_appt_rectangular_maximizer_iff` records the equivalent exact ordered-spectrum statement.

## Closed equality dependencies

1. `cutEdgePurity_lt_of_short` preserves the exact convex quadratic chord after the rational change of variable. When the zero-support endpoint 1/L is strictly below the optimum, every genuinely shortened-support crossing is strictly inferior, including zero cut coefficients. Denominator signs are established.
2. `full_prefix_edge_maximizer` excludes early and late prefixes using the strict branch comparison. The remaining full-support middle edge attains the bound only at the uniquely optimal integer ceiling rank, including odd parity.
3. `ordered_rectangular_cut_unique_spectrum` supplies every boundary premise of the earlier general cut-simplex equality theorem. It does not assume a low-level spectral ansatz or that every maximizer is a vertex. The convex unique-boundary sublevel proof handles all arbitrary convex combinations.
4. `full_middle_crossing_spectrum` identifies the entire vector, not merely its squared norm. Exact coordinate formulas include the ceiling threshold and normalization.
5. `density_appt_rectangular_spectrum` constructs the physical spectral cut and canonical index bounds internally. The quantum trace-square identity connects the original matrix objective to the ordered spectrum.
6. `roundedPlateauMatrix_properties` proves the fixed representative is an actual APPT density at the optimum. It derives its diagonal form from an independently established attaining state and the proved spectrum necessity. The proof dependency is acyclic: exact maximum/attainment precede equality classification. Unitary spectral decomposition and the verified physical conjugation lemmas then prove both directions of the orbit equivalence.

## Controls and verification boundaries

The even 4x58 and odd 4x59 tests verify both sides of the multiplicity boundary. A wrong odd-case floor spectrum is rejected exactly. The fixed 4x58 representative is checked as an actual density/APPT state with purity 2/435. Existing 10x38 physical counterexamples still reject removal of the dimension cutoff. The added audit roots cover all new lemmas, the ordered-spectrum equivalence and the final actual IsGreatest/unitary-orbit classification. Extra unchanged-type proof corruption controls target the spectrum equivalence and arbitrary-spectrum cut equality.

The five new modules compiled individually and then passed a full fresh WSL build and trust-zero replay. Independent run 38241340424, exact source e1f7774e267a5a15bc56d19d2301b4c5111cb8a6, passed all five stages: 2891 Lake tasks, 42729 declarations, 268 roots, and 104 source-bound inputs. All 15 exact-type proof-corruption controls passed. Original evidence is retained in verification/ci-e1f7774e/. Earlier maximum-only evidence retains its own source binding.

The cutoff is sufficient, not claimed minimal. This classification is finite-dimensional in the stated rectangular region; it is not the dimension-varying rigidity theorem, a multiscale graph compactness result, a matching growing-dimension lower bound, or a full entropy theorem. No new preprint or immutable Release is created, and original quantum definitions and toolchain pins remain unchanged.
