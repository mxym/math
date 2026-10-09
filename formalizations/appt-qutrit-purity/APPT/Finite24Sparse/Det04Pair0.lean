import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def det04Pair0 : SparsePolynomial.Poly := [([nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 4)), ([nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 4)), ([nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 4)), ([nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 4)), ([nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 4)), ([nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 4)), ([nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 4)), ([nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 4)), ([nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 4)), ([nat_lit 20, nat_lit 21], Int.ofNat (nat_lit 8)), ([nat_lit 20, nat_lit 22], Int.ofNat (nat_lit 8)), ([nat_lit 20, nat_lit 23], Int.ofNat (nat_lit 8)), ([nat_lit 21, nat_lit 21], Int.ofNat (nat_lit 4)), ([nat_lit 21, nat_lit 22], Int.ofNat (nat_lit 8)), ([nat_lit 21, nat_lit 23], Int.ofNat (nat_lit 8)), ([nat_lit 22, nat_lit 22], Int.ofNat (nat_lit 4)), ([nat_lit 22, nat_lit 23], Int.ofNat (nat_lit 8)), ([nat_lit 23, nat_lit 23], Int.ofNat (nat_lit 4))]
theorem det04Pair0_data : det04Pair0 = SparsePolynomial.trim (SparsePolynomial.mul entryB11 entryB22) := by decide +kernel
theorem eval_det04Pair0 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) det04Pair0 = matB (outer g) 1 1 * matB (outer g) 2 2 := by
  rw [det04Pair0_data, SparsePolynomial.eval_trim, SparsePolynomial.eval_mul, eval_entryB11, eval_entryB22]

end APPT.Finite24
