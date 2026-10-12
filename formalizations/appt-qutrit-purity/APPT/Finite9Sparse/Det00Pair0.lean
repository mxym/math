import APPT.Finite9Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det00Pair0 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 4)), ([nat_lit 3, nat_lit 7], Int.ofNat (nat_lit 4)), ([nat_lit 3, nat_lit 8], Int.ofNat (nat_lit 4)), ([nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 4)), ([nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 4)), ([nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 4)), ([nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 4)), ([nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 4)), ([nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 4)), ([nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 4)), ([nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 8)), ([nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 8)), ([nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 4)), ([nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 8)), ([nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 4))]
theorem det00Pair0_data : det00Pair0 = SparsePolynomial.trim (SparsePolynomial.mul entryA11 entryA22) := by decide +kernel
theorem eval_det00Pair0 (g : Fin 9 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair0 = matA (outer g) 1 1 * matA (outer g) 2 2 := by
  rw [det00Pair0_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA11, eval_entryA22]

end APPT.Finite9
