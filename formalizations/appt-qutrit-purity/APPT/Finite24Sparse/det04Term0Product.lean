import APPT.Finite24Sparse.det04Term0Rows00
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def det04Term0Coeffs : CoefficientMerge.Poly := [(nat_lit 10871, Int.ofNat (nat_lit 8)), (nat_lit 10895, Int.ofNat (nat_lit 8)), (nat_lit 10919, Int.ofNat (nat_lit 8)), (nat_lit 10943, Int.ofNat (nat_lit 8)), (nat_lit 11447, Int.ofNat (nat_lit 8)), (nat_lit 11471, Int.ofNat (nat_lit 8)), (nat_lit 11495, Int.ofNat (nat_lit 8)), (nat_lit 11519, Int.ofNat (nat_lit 8)), (nat_lit 12023, Int.ofNat (nat_lit 8)), (nat_lit 12047, Int.ofNat (nat_lit 16)), (nat_lit 12071, Int.ofNat (nat_lit 16)), (nat_lit 12095, Int.ofNat (nat_lit 16)), (nat_lit 12623, Int.ofNat (nat_lit 8)), (nat_lit 12647, Int.ofNat (nat_lit 16)), (nat_lit 12671, Int.ofNat (nat_lit 16)), (nat_lit 13223, Int.ofNat (nat_lit 8)), (nat_lit 13247, Int.ofNat (nat_lit 16)), (nat_lit 13823, Int.ofNat (nat_lit 8))]
theorem det04Term0Coeffs_data : det04Term0Coeffs = CoefficientMerge.trim det04Term0Row00 := by decide +kernel
theorem eval_det04Term0Coeffs (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term0Coeffs = SparsePolynomial.eval (gapValues g) entryB00 * SparsePolynomial.eval (gapValues g) det04Pair0 := by
  rw [det04Term0Coeffs_data, CoefficientMerge.eval_trim]
  simp only [CoefficientMerge.eval_fastMerge, eval_det04Term0Row00]
  generalize hq : SparsePolynomial.eval (gapValues g) det04Pair0 = v
  simp only [entryB00, SparsePolynomial.eval]
  push_cast
  ring

end APPT.Finite24
