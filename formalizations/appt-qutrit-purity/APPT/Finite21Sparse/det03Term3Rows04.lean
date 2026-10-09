import APPT.Finite21Sparse.Det03Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def det03Term3Row16 : CoefficientMerge.Poly := [(815, 2), (816, 2), (817, 2), (818, 2), (1256, 2), (1257, 2), (1258, 2), (1259, 2), (1697, 2), (1698, 2), (1699, 2), (1700, 2), (2138, 2), (2139, 2), (2140, 2), (2141, 2), (2579, 2), (2580, 2), (2581, 2), (2582, 2), (3020, 2), (3021, 2), (3022, 2), (3023, 2), (3461, 2), (3462, 2), (3463, 2), (3464, 2), (3902, 2), (3903, 2), (3904, 2), (3905, 2), (4343, 2), (4344, 2), (4345, 2), (4346, 2), (4784, 2), (4785, 2), (4786, 2), (4787, 2), (5225, 2), (5226, 2), (5227, 2), (5228, 2), (5666, 2), (5667, 2), (5668, 2), (5669, 2), (6107, 2), (6108, 2), (6109, 2), (6110, 2), (6548, 2), (6549, 2), (6550, 2), (6551, 2), (6989, 2), (6990, 2), (6991, 2), (6992, 2), (7430, 2), (7431, 2), (7432, 2), (7433, 2), (7871, 2), (7872, 2), (7873, 2), (7874, 2)]
theorem det03Term3Row16_decode : SparsePolynomial.decodeCubic 21 det03Term3Row16 = SparsePolynomial.monoTimes [17] (-1 : Int) det03Pair3 := by decide +kernel
theorem eval_det03Term3Row16 (g : Fin 21 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) det03Term3Row16 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [17]*SparsePolynomial.eval (gapValues g) det03Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det03Term3Row16_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite21
