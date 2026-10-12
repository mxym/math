import APPT.Finite12Sparse.det03Term0Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det03Term0Coeffs : CoefficientMerge.Poly := [(nat_lit 971, Int.ofNat (nat_lit 8)), (nat_lit 983, Int.ofNat (nat_lit 8)), (nat_lit 995, Int.ofNat (nat_lit 8)), (nat_lit 1007, Int.ofNat (nat_lit 8)), (nat_lit 1115, Int.ofNat (nat_lit 8)), (nat_lit 1127, Int.ofNat (nat_lit 8)), (nat_lit 1139, Int.ofNat (nat_lit 8)), (nat_lit 1151, Int.ofNat (nat_lit 8)), (nat_lit 1259, Int.ofNat (nat_lit 8)), (nat_lit 1271, Int.ofNat (nat_lit 16)), (nat_lit 1283, Int.ofNat (nat_lit 16)), (nat_lit 1295, Int.ofNat (nat_lit 16)), (nat_lit 1415, Int.ofNat (nat_lit 8)), (nat_lit 1427, Int.ofNat (nat_lit 16)), (nat_lit 1439, Int.ofNat (nat_lit 16)), (nat_lit 1571, Int.ofNat (nat_lit 8)), (nat_lit 1583, Int.ofNat (nat_lit 16)), (nat_lit 1727, Int.ofNat (nat_lit 8))]
theorem det03Term0Coeffs_data : det03Term0Coeffs = CoefficientMerge.trim det03Term0Row00 := by decide +kernel
theorem eval_det03Term0Coeffs (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det03Term0Coeffs = SparsePolynomial.eval (gapValues g) entryB00 * SparsePolynomial.eval (gapValues g) det03Pair0 := by
  rw [det03Term0Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det03Term0Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det03Pair0 = v
  simp only [entryB00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite12
