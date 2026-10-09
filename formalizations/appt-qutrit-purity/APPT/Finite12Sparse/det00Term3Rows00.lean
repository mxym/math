import APPT.Finite12Sparse.Det00Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Term3Row00 : CoefficientMerge.Poly := [(165, 2), (166, 2), (167, 2), (177, 2), (178, 2), (179, 2), (189, 2), (190, 2), (191, 2), (201, 2), (202, 2), (203, 2), (213, 2), (214, 2), (215, 2), (225, 2), (226, 2), (227, 2), (237, 2), (238, 2), (239, 2)]
theorem det00Term3Row00_decode : SparsePolynomial.decodeCubic 12 det00Term3Row00 = SparsePolynomial.monoTimes [1] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row00 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term3Row00 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [1]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row00_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row01 : CoefficientMerge.Poly := [(177, 2), (178, 2), (179, 2), (321, 2), (322, 2), (323, 2), (333, 2), (334, 2), (335, 2), (345, 2), (346, 2), (347, 2), (357, 2), (358, 2), (359, 2), (369, 2), (370, 2), (371, 2), (381, 2), (382, 2), (383, 2)]
theorem det00Term3Row01_decode : SparsePolynomial.decodeCubic 12 det00Term3Row01 = SparsePolynomial.monoTimes [2] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row01 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term3Row01 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [2]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row01_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row02 : CoefficientMerge.Poly := [(189, 2), (190, 2), (191, 2), (333, 2), (334, 2), (335, 2), (477, 2), (478, 2), (479, 2), (489, 2), (490, 2), (491, 2), (501, 2), (502, 2), (503, 2), (513, 2), (514, 2), (515, 2), (525, 2), (526, 2), (527, 2)]
theorem det00Term3Row02_decode : SparsePolynomial.decodeCubic 12 det00Term3Row02 = SparsePolynomial.monoTimes [3] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row02 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term3Row02 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [3]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row02_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term3Row03 : CoefficientMerge.Poly := [(201, 2), (202, 2), (203, 2), (345, 2), (346, 2), (347, 2), (489, 2), (490, 2), (491, 2), (633, 2), (634, 2), (635, 2), (645, 2), (646, 2), (647, 2), (657, 2), (658, 2), (659, 2), (669, 2), (670, 2), (671, 2)]
theorem det00Term3Row03_decode : SparsePolynomial.decodeCubic 12 det00Term3Row03 = SparsePolynomial.monoTimes [4] (-1 : Int) det00Pair3 := by decide +kernel
theorem eval_det00Term3Row03 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term3Row03 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det00Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term3Row03_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
