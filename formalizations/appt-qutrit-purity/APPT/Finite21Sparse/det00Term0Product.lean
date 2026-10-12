import APPT.Finite21Sparse.det00Term0Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def det00Term0Coeffs : CoefficientMerge.Poly := [(nat_lit 7013, Int.ofNat (nat_lit 8)), (nat_lit 7034, Int.ofNat (nat_lit 8)), (nat_lit 7055, Int.ofNat (nat_lit 8)), (nat_lit 7454, Int.ofNat (nat_lit 8)), (nat_lit 7475, Int.ofNat (nat_lit 8)), (nat_lit 7496, Int.ofNat (nat_lit 8)), (nat_lit 7895, Int.ofNat (nat_lit 8)), (nat_lit 7916, Int.ofNat (nat_lit 8)), (nat_lit 7937, Int.ofNat (nat_lit 8)), (nat_lit 8336, Int.ofNat (nat_lit 8)), (nat_lit 8357, Int.ofNat (nat_lit 16)), (nat_lit 8378, Int.ofNat (nat_lit 16)), (nat_lit 8798, Int.ofNat (nat_lit 8)), (nat_lit 8819, Int.ofNat (nat_lit 16)), (nat_lit 9260, Int.ofNat (nat_lit 8))]
theorem det00Term0Coeffs_data : det00Term0Coeffs = CoefficientMerge.trim det00Term0Row00 := by decide +kernel
theorem eval_det00Term0Coeffs (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det00Term0Coeffs = SparsePolynomial.eval (gapValues g) entryA00 * SparsePolynomial.eval (gapValues g) det00Pair0 := by
  rw [det00Term0Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det00Term0Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det00Pair0 = v
  simp only [entryA00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite21
