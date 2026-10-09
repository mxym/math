import APPT.Finite9Sparse.det00Term0Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite9
open SparsePolynomial

def det00Term0Coeffs : CoefficientMerge.Poly := [(nat_lit 305, Int.ofNat (nat_lit 8)), (nat_lit 314, Int.ofNat (nat_lit 8)), (nat_lit 323, Int.ofNat (nat_lit 8)), (nat_lit 386, Int.ofNat (nat_lit 8)), (nat_lit 395, Int.ofNat (nat_lit 8)), (nat_lit 404, Int.ofNat (nat_lit 8)), (nat_lit 467, Int.ofNat (nat_lit 8)), (nat_lit 476, Int.ofNat (nat_lit 8)), (nat_lit 485, Int.ofNat (nat_lit 8)), (nat_lit 548, Int.ofNat (nat_lit 8)), (nat_lit 557, Int.ofNat (nat_lit 16)), (nat_lit 566, Int.ofNat (nat_lit 16)), (nat_lit 638, Int.ofNat (nat_lit 8)), (nat_lit 647, Int.ofNat (nat_lit 16)), (nat_lit 728, Int.ofNat (nat_lit 8))]
theorem det00Term0Coeffs_data : det00Term0Coeffs = CoefficientMerge.trim det00Term0Row00 := by decide +kernel
theorem eval_det00Term0Coeffs (g : Fin 9 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 9) det00Term0Coeffs = SparsePolynomial.eval (gapValues g) entryA00 * SparsePolynomial.eval (gapValues g) det00Pair0 := by
  rw [det00Term0Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det00Term0Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det00Pair0 = v
  simp only [entryA00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite9
