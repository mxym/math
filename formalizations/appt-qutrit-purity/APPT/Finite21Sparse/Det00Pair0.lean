import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def det00Pair0 : SparsePolynomial.Poly := [([nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 4)), ([nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 4)), ([nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 4)), ([nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 4)), ([nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 4)), ([nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 4)), ([nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 4)), ([nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 4)), ([nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 4)), ([nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 4)), ([nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 8)), ([nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 8)), ([nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 4)), ([nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 8)), ([nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 4))]
theorem det00Pair0_data : det00Pair0 = SparsePolynomial.trim (SparsePolynomial.mul entryA11 entryA22) := by decide +kernel
theorem eval_det00Pair0 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) det00Pair0 = matA (outer g) 1 1 * matA (outer g) 2 2 := by
  rw [det00Pair0_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryA11, eval_entryA22]

end APPT.Finite21
