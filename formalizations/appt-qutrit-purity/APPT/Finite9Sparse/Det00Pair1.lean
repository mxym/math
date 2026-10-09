import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det00Pair1 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2], Int.ofNat (nat_lit 1)), ([nat_lit 1, nat_lit 3], Int.ofNat (nat_lit 1)), ([nat_lit 2, nat_lit 2], Int.ofNat (nat_lit 1)), ([nat_lit 2, nat_lit 3], Int.ofNat (nat_lit 2)), ([nat_lit 2, nat_lit 4], Int.ofNat (nat_lit 1)), ([nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1)), ([nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem det00Pair1_data : det00Pair1 = SparsePolynomial.trim (SparsePolynomial.mul entryA12 entryA20) := by decide +kernel
theorem eval_det00Pair1 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair1 = matA (outer g) 1 2 * matA (outer g) 2 0 := by
  rw [det00Pair1_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA12, eval_entryA20]

end APPT.Finite9
