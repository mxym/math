import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Pair3 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11], Int.negSucc (nat_lit 1)), ([nat_lit 1, nat_lit 12], Int.negSucc (nat_lit 1)), ([nat_lit 1, nat_lit 13], Int.negSucc (nat_lit 1)), ([nat_lit 1, nat_lit 14], Int.negSucc (nat_lit 1)), ([nat_lit 2, nat_lit 11], Int.negSucc (nat_lit 1)), ([nat_lit 2, nat_lit 12], Int.negSucc (nat_lit 1)), ([nat_lit 2, nat_lit 13], Int.negSucc (nat_lit 1)), ([nat_lit 2, nat_lit 14], Int.negSucc (nat_lit 1)), ([nat_lit 3, nat_lit 11], Int.negSucc (nat_lit 1)), ([nat_lit 3, nat_lit 12], Int.negSucc (nat_lit 1)), ([nat_lit 3, nat_lit 13], Int.negSucc (nat_lit 1)), ([nat_lit 3, nat_lit 14], Int.negSucc (nat_lit 1)), ([nat_lit 4, nat_lit 11], Int.negSucc (nat_lit 1)), ([nat_lit 4, nat_lit 12], Int.negSucc (nat_lit 1)), ([nat_lit 4, nat_lit 13], Int.negSucc (nat_lit 1)), ([nat_lit 4, nat_lit 14], Int.negSucc (nat_lit 1)), ([nat_lit 5, nat_lit 11], Int.negSucc (nat_lit 1)), ([nat_lit 5, nat_lit 12], Int.negSucc (nat_lit 1)), ([nat_lit 5, nat_lit 13], Int.negSucc (nat_lit 1)), ([nat_lit 5, nat_lit 14], Int.negSucc (nat_lit 1)), ([nat_lit 6, nat_lit 11], Int.negSucc (nat_lit 1)), ([nat_lit 6, nat_lit 12], Int.negSucc (nat_lit 1)), ([nat_lit 6, nat_lit 13], Int.negSucc (nat_lit 1)), ([nat_lit 6, nat_lit 14], Int.negSucc (nat_lit 1)), ([nat_lit 7, nat_lit 11], Int.negSucc (nat_lit 1)), ([nat_lit 7, nat_lit 12], Int.negSucc (nat_lit 1)), ([nat_lit 7, nat_lit 13], Int.negSucc (nat_lit 1)), ([nat_lit 7, nat_lit 14], Int.negSucc (nat_lit 1)), ([nat_lit 8, nat_lit 11], Int.negSucc (nat_lit 1)), ([nat_lit 8, nat_lit 12], Int.negSucc (nat_lit 1)), ([nat_lit 8, nat_lit 13], Int.negSucc (nat_lit 1)), ([nat_lit 8, nat_lit 14], Int.negSucc (nat_lit 1)), ([nat_lit 9, nat_lit 11], Int.negSucc (nat_lit 1)), ([nat_lit 9, nat_lit 12], Int.negSucc (nat_lit 1)), ([nat_lit 9, nat_lit 13], Int.negSucc (nat_lit 1)), ([nat_lit 9, nat_lit 14], Int.negSucc (nat_lit 1)), ([nat_lit 10, nat_lit 11], Int.negSucc (nat_lit 1)), ([nat_lit 10, nat_lit 12], Int.negSucc (nat_lit 1)), ([nat_lit 10, nat_lit 13], Int.negSucc (nat_lit 1)), ([nat_lit 10, nat_lit 14], Int.negSucc (nat_lit 1)), ([nat_lit 11, nat_lit 11], Int.negSucc (nat_lit 1)), ([nat_lit 11, nat_lit 12], Int.negSucc (nat_lit 1)), ([nat_lit 11, nat_lit 13], Int.negSucc (nat_lit 1)), ([nat_lit 11, nat_lit 14], Int.negSucc (nat_lit 1))]
theorem det04Pair3_data : det04Pair3 = SparsePolynomial.trim (SparsePolynomial.mul entryB11 entryB20) := by decide +kernel
theorem eval_det04Pair3 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) det04Pair3 = matB (outer g) 1 1 * matB (outer g) 2 0 := by
  rw [det04Pair3_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB11, eval_entryB20]

end APPT.Finite15
