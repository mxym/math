import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det00Pair3 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6], Int.negSucc (nat_lit 1)), ([nat_lit 1, nat_lit 7], Int.negSucc (nat_lit 1)), ([nat_lit 1, nat_lit 8], Int.negSucc (nat_lit 1)), ([nat_lit 2, nat_lit 6], Int.negSucc (nat_lit 1)), ([nat_lit 2, nat_lit 7], Int.negSucc (nat_lit 1)), ([nat_lit 2, nat_lit 8], Int.negSucc (nat_lit 1)), ([nat_lit 3, nat_lit 6], Int.negSucc (nat_lit 1)), ([nat_lit 3, nat_lit 7], Int.negSucc (nat_lit 1)), ([nat_lit 3, nat_lit 8], Int.negSucc (nat_lit 1)), ([nat_lit 4, nat_lit 6], Int.negSucc (nat_lit 1)), ([nat_lit 4, nat_lit 7], Int.negSucc (nat_lit 1)), ([nat_lit 4, nat_lit 8], Int.negSucc (nat_lit 1))]
theorem det00Pair3_data : det00Pair3 = SparsePolynomial.trim (SparsePolynomial.mul entryA11 entryA20) := by decide +kernel
theorem eval_det00Pair3 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair3 = matA (outer g) 1 1 * matA (outer g) 2 0 := by
  rw [det00Pair3_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA11, eval_entryA20]

end APPT.Finite9
