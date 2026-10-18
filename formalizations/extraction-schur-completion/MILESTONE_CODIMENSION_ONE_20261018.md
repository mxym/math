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
