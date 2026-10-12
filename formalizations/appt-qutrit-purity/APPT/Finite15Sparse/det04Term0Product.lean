import APPT.Finite15Sparse.det04Term0Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Term0Coeffs : CoefficientMerge.Poly := [(nat_lit 2204, Int.ofNat (nat_lit 8)), (nat_lit 2219, Int.ofNat (nat_lit 8)), (nat_lit 2234, Int.ofNat (nat_lit 8)), (nat_lit 2249, Int.ofNat (nat_lit 8)), (nat_lit 2429, Int.ofNat (nat_lit 8)), (nat_lit 2444, Int.ofNat (nat_lit 8)), (nat_lit 2459, Int.ofNat (nat_lit 8)), (nat_lit 2474, Int.ofNat (nat_lit 8)), (nat_lit 2654, Int.ofNat (nat_lit 8)), (nat_lit 2669, Int.ofNat (nat_lit 16)), (nat_lit 2684, Int.ofNat (nat_lit 16)), (nat_lit 2699, Int.ofNat (nat_lit 16)), (nat_lit 2894, Int.ofNat (nat_lit 8)), (nat_lit 2909, Int.ofNat (nat_lit 16)), (nat_lit 2924, Int.ofNat (nat_lit 16)), (nat_lit 3134, Int.ofNat (nat_lit 8)), (nat_lit 3149, Int.ofNat (nat_lit 16)), (nat_lit 3374, Int.ofNat (nat_lit 8))]
theorem det04Term0Coeffs_data : det04Term0Coeffs = CoefficientMerge.trim det04Term0Row00 := by decide +kernel
theorem eval_det04Term0Coeffs (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term0Coeffs = SparsePolynomial.eval (gapValues g) entryB00 * SparsePolynomial.eval (gapValues g) det04Pair0 := by
  rw [det04Term0Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det04Term0Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det04Pair0 = v
  simp only [entryB00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite15
