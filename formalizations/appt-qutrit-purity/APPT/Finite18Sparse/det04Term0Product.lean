import APPT.Finite18Sparse.det04Term0Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def det04Term0Coeffs : CoefficientMerge.Poly := [(nat_lit 4157, Int.ofNat (nat_lit 8)), (nat_lit 4175, Int.ofNat (nat_lit 8)), (nat_lit 4193, Int.ofNat (nat_lit 8)), (nat_lit 4211, Int.ofNat (nat_lit 8)), (nat_lit 4481, Int.ofNat (nat_lit 8)), (nat_lit 4499, Int.ofNat (nat_lit 8)), (nat_lit 4517, Int.ofNat (nat_lit 8)), (nat_lit 4535, Int.ofNat (nat_lit 8)), (nat_lit 4805, Int.ofNat (nat_lit 8)), (nat_lit 4823, Int.ofNat (nat_lit 16)), (nat_lit 4841, Int.ofNat (nat_lit 16)), (nat_lit 4859, Int.ofNat (nat_lit 16)), (nat_lit 5147, Int.ofNat (nat_lit 8)), (nat_lit 5165, Int.ofNat (nat_lit 16)), (nat_lit 5183, Int.ofNat (nat_lit 16)), (nat_lit 5489, Int.ofNat (nat_lit 8)), (nat_lit 5507, Int.ofNat (nat_lit 16)), (nat_lit 5831, Int.ofNat (nat_lit 8))]
theorem det04Term0Coeffs_data : det04Term0Coeffs = CoefficientMerge.trim det04Term0Row00 := by decide +kernel
theorem eval_det04Term0Coeffs (g : Fin 18 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) det04Term0Coeffs = SparsePolynomial.eval (gapValues g) entryB00 * SparsePolynomial.eval (gapValues g) det04Pair0 := by
  rw [det04Term0Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det04Term0Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det04Pair0 = v
  simp only [entryB00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite18
