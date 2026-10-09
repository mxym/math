import APPT.Finite12Sparse.det03Term5Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det03Term5Coeffs : CoefficientMerge.Poly := [(nat_lit 323, Int.ofNat (nat_lit 2)), (nat_lit 335, Int.ofNat (nat_lit 4)), (nat_lit 347, Int.ofNat (nat_lit 4)), (nat_lit 359, Int.ofNat (nat_lit 4)), (nat_lit 371, Int.ofNat (nat_lit 4)), (nat_lit 479, Int.ofNat (nat_lit 2)), (nat_lit 491, Int.ofNat (nat_lit 4)), (nat_lit 503, Int.ofNat (nat_lit 4)), (nat_lit 515, Int.ofNat (nat_lit 4)), (nat_lit 635, Int.ofNat (nat_lit 2)), (nat_lit 647, Int.ofNat (nat_lit 4)), (nat_lit 659, Int.ofNat (nat_lit 4)), (nat_lit 791, Int.ofNat (nat_lit 2)), (nat_lit 803, Int.ofNat (nat_lit 4)), (nat_lit 947, Int.ofNat (nat_lit 2))]
theorem det03Term5Coeffs_data : det03Term5Coeffs = CoefficientMerge.trim det03Term5Row00 := by decide +kernel
theorem eval_det03Term5Coeffs (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term5Coeffs = SparsePolynomial.eval (gapValues g) entryB00 * SparsePolynomial.eval (gapValues g) det03Pair5 := by
  rw [det03Term5Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det03Term5Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det03Pair5 = v
  simp only [entryB00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite12
