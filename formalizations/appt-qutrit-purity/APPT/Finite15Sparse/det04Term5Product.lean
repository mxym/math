import APPT.Finite15Sparse.det04Term5Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det04Term5Coeffs : CoefficientMerge.Poly := [(nat_lit 494, Int.ofNat (nat_lit 2)), (nat_lit 509, Int.ofNat (nat_lit 4)), (nat_lit 524, Int.ofNat (nat_lit 4)), (nat_lit 539, Int.ofNat (nat_lit 4)), (nat_lit 554, Int.ofNat (nat_lit 4)), (nat_lit 569, Int.ofNat (nat_lit 4)), (nat_lit 584, Int.ofNat (nat_lit 4)), (nat_lit 599, Int.ofNat (nat_lit 4)), (nat_lit 734, Int.ofNat (nat_lit 2)), (nat_lit 749, Int.ofNat (nat_lit 4)), (nat_lit 764, Int.ofNat (nat_lit 4)), (nat_lit 779, Int.ofNat (nat_lit 4)), (nat_lit 794, Int.ofNat (nat_lit 4)), (nat_lit 809, Int.ofNat (nat_lit 4)), (nat_lit 824, Int.ofNat (nat_lit 4)), (nat_lit 974, Int.ofNat (nat_lit 2)), (nat_lit 989, Int.ofNat (nat_lit 4)), (nat_lit 1004, Int.ofNat (nat_lit 4)), (nat_lit 1019, Int.ofNat (nat_lit 4)), (nat_lit 1034, Int.ofNat (nat_lit 4)), (nat_lit 1049, Int.ofNat (nat_lit 4)), (nat_lit 1214, Int.ofNat (nat_lit 2)), (nat_lit 1229, Int.ofNat (nat_lit 4)), (nat_lit 1244, Int.ofNat (nat_lit 4)), (nat_lit 1259, Int.ofNat (nat_lit 4)), (nat_lit 1274, Int.ofNat (nat_lit 4)), (nat_lit 1454, Int.ofNat (nat_lit 2)), (nat_lit 1469, Int.ofNat (nat_lit 4)), (nat_lit 1484, Int.ofNat (nat_lit 4)), (nat_lit 1499, Int.ofNat (nat_lit 4)), (nat_lit 1694, Int.ofNat (nat_lit 2)), (nat_lit 1709, Int.ofNat (nat_lit 4)), (nat_lit 1724, Int.ofNat (nat_lit 4)), (nat_lit 1934, Int.ofNat (nat_lit 2)), (nat_lit 1949, Int.ofNat (nat_lit 4)), (nat_lit 2174, Int.ofNat (nat_lit 2))]
theorem det04Term5Coeffs_data : det04Term5Coeffs = CoefficientMerge.trim det04Term5Row00 := by decide +kernel
theorem eval_det04Term5Coeffs (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det04Term5Coeffs = SparsePolynomial.eval (gapValues g) entryB00 * SparsePolynomial.eval (gapValues g) det04Pair5 := by
  rw [det04Term5Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det04Term5Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det04Pair5 = v
  simp only [entryB00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite15
