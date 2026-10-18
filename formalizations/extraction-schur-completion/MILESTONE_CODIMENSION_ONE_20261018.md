# Actual codimension-one Haar moments

Status: BUILD_ONLY. This is a separate continuation scope; no old audit scope is changed.

SchurCompletion/CodimensionOneMoments.lean proves the actual rank-one Haar average of every genuine density, derives all genuine unitary-entry power moments from it, and then proves an exact finite binomial-sum formula for latHaarAverage (s+1) s k. It includes blocklength zero and the singular rank-zero expression; the physical density interpretation requires s>0. No Schur spectrum, classification, concentration or moment law is supplied as a hypothesis.

The actual endpoint is ExtractionSchur.flatHaarAverage_codimension_one_purity. It is an exact finite purity formula, not yet a sharp asymptotic, a support-rank formula or a general-rank completion. General intermediate-rank Young/multiplicity classification, sharp support dimension, reciprocal-moment asymptotics and their target-uniform physical minimax connection remain open.

The retained CLI WIP was first compiled unchanged before extension. All sources and build outputs are D-backed, with the prescribed shared-cache lock wrapper. Ordinary compilation is not an independent empty-kernel audit.

## Sharp purity continuation

CodimensionOneAsymptotic.lean proves the exact algebraic main-minus-tail identity, bounds each of the s tail terms by a polynomial times a geometric sequence, and obtains the actual endpoint

latHaarAverage_codimension_one_purity_scaled_limit: for every fixed s>0, s^k k^s Tr(Ω²) tends to s^s s!, with D=s+1.

latHaarAverage_codimension_one_purity_isEquivalent gives the corresponding sharp asymptotic equivalence. 
ankBudget_codimension_one_sharp_lower gives the actual support rank a matching leading lower bound from Cauchy-Schwarz. The sharp rank upper bound, and hence even this codimension-one rank-times-purity limit, remain separate obligations. General rank 1<s<D-1 is still open.

## Complete codimension-one double moments

The matching rank upper bound is now internally proved. `WordStraightening.lean` conjugates the actual column cutoff to arbitrary selected positions, derives literal coordinate determinant relations, and uses strict lexicographic descent to prove that restriction to words avoiding the complete descending D-letter pattern is injective on the actual rank-budget space. `WordPatternCount.lean` constructs a recursive word bijection and counts these words exactly by the finite sum ∑_{j=0}^s choose(k,j) s^(k-j). No RSK, Young decomposition, straightening, or dimension certificate is assumed.

`CodimensionOneRank.lean` proves the sum's leading asymptotic and squeezes the actual rank against the actual purity lower bound. For every fixed s>0 and D=s+1:

- `rankBudget_codimension_one_rank_scaled_limit`: r/(s^k k^s) → 1/(s^s s!).
- `rankBudget_codimension_one_rank_isEquivalent`: r ~ s^k k^s/(s^s s!).
- `flatHaarAverage_codimension_one_purity_isEquivalent`: Tr(Ω²) ~ s^s s!/(s^k k^s).
- `rankBudget_codimension_one_rank_times_purity_limit`: r Tr(Ω²) → 1.

These are genuine actual-matrix theorems with no target-equivalent hypotheses. This closes the manuscript's sharp double moments on the codimension-one subfamily only. General 1<s<D-1 and the physical target-uniform minimax connection are not claimed complete. Status remains BUILD_ONLY until independent replay/audit.
