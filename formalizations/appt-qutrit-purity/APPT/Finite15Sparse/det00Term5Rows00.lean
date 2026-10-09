import APPT.Finite15Sparse.Det00Pair5
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def det00Term5Row00 : CoefficientMerge.Poly := [(494, 2), (509, 4), (524, 4), (539, 4), (554, 4), (569, 4), (584, 4), (599, 4), (734, 2), (749, 4), (764, 4), (779, 4), (794, 4), (809, 4), (824, 4), (974, 2), (989, 4), (1004, 4), (1019, 4), (1034, 4), (1049, 4), (1214, 2), (1229, 4), (1244, 4), (1259, 4), (1274, 4), (1454, 2), (1469, 4), (1484, 4), (1499, 4), (1694, 2), (1709, 4), (1724, 4), (1934, 2), (1949, 4), (2174, 2)]
theorem det00Term5Row00_decode : SparsePolynomial.decodeCubic 15 det00Term5Row00 = SparsePolynomial.monoTimes [14] (2 : Int) det00Pair5 := by decide +kernel
theorem eval_det00Term5Row00 (g : Fin 15 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) det00Term5Row00 = (2 : ℝ)*SparsePolynomial.mon (gapValues g) [14]*SparsePolynomial.eval (gapValues g) det00Pair5 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term5Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite15
