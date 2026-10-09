import APPT.Finite12Sparse.Det00Pair1
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def det00Term1Row04 : CoefficientMerge.Poly := [(172, -1), (184, -1), (196, -1), (197, -1), (198, -1), (316, -1), (328, -2), (340, -2), (341, -2), (342, -2), (343, -1), (472, -1), (484, -2), (485, -2), (486, -2), (487, -1), (628, -1), (629, -2), (630, -2), (631, -1), (641, -1), (642, -2), (643, -1), (654, -1), (655, -1)]
theorem det00Term1Row04_decode : SparsePolynomial.decodeCubic 12 det00Term1Row04 = SparsePolynomial.monoTimes [4] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row04 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term1Row04 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [4]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row04_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row05 : CoefficientMerge.Poly := [(173, -1), (185, -1), (197, -1), (209, -1), (210, -1), (317, -1), (329, -2), (341, -2), (353, -2), (354, -2), (355, -1), (473, -1), (485, -2), (497, -2), (498, -2), (499, -1), (629, -1), (641, -2), (642, -2), (643, -1), (785, -1), (786, -2), (787, -1), (798, -1), (799, -1)]
theorem det00Term1Row05_decode : SparsePolynomial.decodeCubic 12 det00Term1Row05 = SparsePolynomial.monoTimes [5] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row05 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term1Row05 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [5]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row05_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row06 : CoefficientMerge.Poly := [(174, -1), (186, -1), (198, -1), (210, -1), (222, -1), (318, -1), (330, -2), (342, -2), (354, -2), (366, -2), (367, -1), (474, -1), (486, -2), (498, -2), (510, -2), (511, -1), (630, -1), (642, -2), (654, -2), (655, -1), (786, -1), (798, -2), (799, -1), (942, -1), (943, -1)]
theorem det00Term1Row06_decode : SparsePolynomial.decodeCubic 12 det00Term1Row06 = SparsePolynomial.monoTimes [6] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row06 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term1Row06 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [6]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row06_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det00Term1Row07 : CoefficientMerge.Poly := [(175, -1), (187, -1), (199, -1), (211, -1), (223, -1), (319, -1), (331, -2), (343, -2), (355, -2), (367, -2), (379, -1), (475, -1), (487, -2), (499, -2), (511, -2), (523, -1), (631, -1), (643, -2), (655, -2), (667, -1), (787, -1), (799, -2), (811, -1), (943, -1), (955, -1)]
theorem det00Term1Row07_decode : SparsePolynomial.decodeCubic 12 det00Term1Row07 = SparsePolynomial.monoTimes [7] (-1 : Int) det00Pair1 := by decide +kernel
theorem eval_det00Term1Row07 (g : Fin 12 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) det00Term1Row07 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [7]*SparsePolynomial.eval (gapValues g) det00Pair1 := by
  rw [← SparsePolynomial.eval_decodeCubic, det00Term1Row07_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite12
