import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det00Pair4 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3], Int.negSucc (nat_lit 1)), ([nat_lit 0, nat_lit 4], Int.negSucc (nat_lit 1)), ([nat_lit 0, nat_lit 5], Int.negSucc (nat_lit 1)), ([nat_lit 0, nat_lit 6], Int.negSucc (nat_lit 1)), ([nat_lit 0, nat_lit 7], Int.negSucc (nat_lit 1)), ([nat_lit 0, nat_lit 8], Int.negSucc (nat_lit 1)), ([nat_lit 1, nat_lit 3], Int.negSucc (nat_lit 1)), ([nat_lit 1, nat_lit 4], Int.negSucc (nat_lit 1)), ([nat_lit 1, nat_lit 5], Int.negSucc (nat_lit 1)), ([nat_lit 1, nat_lit 6], Int.negSucc (nat_lit 1)), ([nat_lit 1, nat_lit 7], Int.negSucc (nat_lit 1)), ([nat_lit 1, nat_lit 8], Int.negSucc (nat_lit 1)), ([nat_lit 2, nat_lit 3], Int.negSucc (nat_lit 1)), ([nat_lit 2, nat_lit 4], Int.negSucc (nat_lit 1)), ([nat_lit 2, nat_lit 5], Int.negSucc (nat_lit 1)), ([nat_lit 2, nat_lit 6], Int.negSucc (nat_lit 1)), ([nat_lit 2, nat_lit 7], Int.negSucc (nat_lit 1)), ([nat_lit 2, nat_lit 8], Int.negSucc (nat_lit 1)), ([nat_lit 3, nat_lit 3], Int.negSucc (nat_lit 1)), ([nat_lit 3, nat_lit 4], Int.negSucc (nat_lit 3)), ([nat_lit 3, nat_lit 5], Int.negSucc (nat_lit 3)), ([nat_lit 3, nat_lit 6], Int.negSucc (nat_lit 3)), ([nat_lit 3, nat_lit 7], Int.negSucc (nat_lit 1)), ([nat_lit 3, nat_lit 8], Int.negSucc (nat_lit 1)), ([nat_lit 4, nat_lit 4], Int.negSucc (nat_lit 1)), ([nat_lit 4, nat_lit 5], Int.negSucc (nat_lit 3)), ([nat_lit 4, nat_lit 6], Int.negSucc (nat_lit 3)), ([nat_lit 4, nat_lit 7], Int.negSucc (nat_lit 1)), ([nat_lit 4, nat_lit 8], Int.negSucc (nat_lit 1)), ([nat_lit 5, nat_lit 5], Int.negSucc (nat_lit 1)), ([nat_lit 5, nat_lit 6], Int.negSucc (nat_lit 3)), ([nat_lit 5, nat_lit 7], Int.negSucc (nat_lit 1)), ([nat_lit 5, nat_lit 8], Int.negSucc (nat_lit 1)), ([nat_lit 6, nat_lit 6], Int.negSucc (nat_lit 1)), ([nat_lit 6, nat_lit 7], Int.negSucc (nat_lit 1)), ([nat_lit 6, nat_lit 8], Int.negSucc (nat_lit 1))]
theorem det00Pair4_data : det00Pair4 = SparsePolynomial.trim (SparsePolynomial.mul entryA10 entryA22) := by decide +kernel
theorem eval_det00Pair4 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair4 = matA (outer g) 1 0 * matA (outer g) 2 2 := by
  rw [det00Pair4_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA10, eval_entryA22]

end APPT.Finite9
