import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def base02 : SparsePolynomial.Poly := [([nat_lit 0], Int.negSucc (nat_lit 3)), ([nat_lit 1], Int.negSucc (nat_lit 11)), ([nat_lit 2], Int.negSucc (nat_lit 15)), ([nat_lit 3], Int.negSucc (nat_lit 15)), ([nat_lit 4], Int.negSucc (nat_lit 15)), ([nat_lit 5], Int.negSucc (nat_lit 15)), ([nat_lit 6], Int.negSucc (nat_lit 15)), ([nat_lit 7], Int.negSucc (nat_lit 15)), ([nat_lit 8], Int.negSucc (nat_lit 15)), ([nat_lit 9], Int.negSucc (nat_lit 7)), ([nat_lit 10], Int.negSucc (nat_lit 3)), ([nat_lit 11], Int.ofNat (nat_lit 4)), ([nat_lit 12], Int.ofNat (nat_lit 6)), ([nat_lit 13], Int.ofNat (nat_lit 10)), ([nat_lit 14], Int.ofNat (nat_lit 18))]
theorem eval_base02 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) base02 = quadA (outer g) ![2,1,2] := by
  norm_num [base02, SparsePolynomial.eval, SparsePolynomial.mon, gapValues, spectrum, quadA, matA, outer, Matrix.mulVec, dotProduct, Fin.sum_univ_succ]
  <;> ring
theorem base02_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) base02 := by
  rw [eval_base02]
  exact quadA_nonneg (outer g) hA ![2,1,2]

end APPT.Finite15
