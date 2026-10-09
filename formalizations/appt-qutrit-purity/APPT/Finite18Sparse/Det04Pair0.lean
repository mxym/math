import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det04Pair0 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 4)), ([nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 4)), ([nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 4)), ([nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 4)), ([nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 4)), ([nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 4)), ([nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 4)), ([nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 4)), ([nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 4)), ([nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 8)), ([nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 8)), ([nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 8)), ([nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 4)), ([nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 8)), ([nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 8)), ([nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 4)), ([nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 8)), ([nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 4))]
theorem det04Pair0_data : det04Pair0 = SparsePolynomial.trim (SparsePolynomial.mul entryB11 entryB22) := by decide +kernel
theorem eval_det04Pair0 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) det04Pair0 = matB (outer g) 1 1 * matB (outer g) 2 2 := by
  rw [det04Pair0_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB11, eval_entryB22]

end APPT.Finite18
