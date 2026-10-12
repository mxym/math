import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det03Pair2 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2], Int.ofNat (nat_lit 1)), ([nat_lit 0, nat_lit 3], Int.ofNat (nat_lit 1)), ([nat_lit 1, nat_lit 2], Int.ofNat (nat_lit 1)), ([nat_lit 1, nat_lit 3], Int.ofNat (nat_lit 1)), ([nat_lit 2, nat_lit 2], Int.ofNat (nat_lit 1)), ([nat_lit 2, nat_lit 3], Int.ofNat (nat_lit 2)), ([nat_lit 2, nat_lit 4], Int.ofNat (nat_lit 1)), ([nat_lit 2, nat_lit 5], Int.ofNat (nat_lit 1)), ([nat_lit 2, nat_lit 6], Int.ofNat (nat_lit 1)), ([nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1)), ([nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1)), ([nat_lit 3, nat_lit 5], Int.ofNat (nat_lit 1)), ([nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem det03Pair2_data : det03Pair2 = SparsePolynomial.trim (SparsePolynomial.mul entryB10 entryB21) := by decide +kernel
theorem eval_det03Pair2 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) det03Pair2 = matB (outer g) 1 0 * matB (outer g) 2 1 := by
  rw [det03Pair2_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB10, eval_entryB21]

end APPT.Finite9
