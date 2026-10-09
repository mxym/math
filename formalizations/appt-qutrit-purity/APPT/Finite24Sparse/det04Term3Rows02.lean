import APPT.Finite24Sparse.Det04Pair3
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def det04Term3Row08 : CoefficientMerge.Poly := [(812, 2), (813, 2), (814, 2), (815, 2), (1388, 2), (1389, 2), (1390, 2), (1391, 2), (1964, 2), (1965, 2), (1966, 2), (1967, 2), (2540, 2), (2541, 2), (2542, 2), (2543, 2), (3116, 2), (3117, 2), (3118, 2), (3119, 2), (3692, 2), (3693, 2), (3694, 2), (3695, 2), (4268, 2), (4269, 2), (4270, 2), (4271, 2), (4844, 2), (4845, 2), (4846, 2), (4847, 2), (5420, 2), (5421, 2), (5422, 2), (5423, 2), (5444, 2), (5445, 2), (5446, 2), (5447, 2), (5468, 2), (5469, 2), (5470, 2), (5471, 2), (5492, 2), (5493, 2), (5494, 2), (5495, 2), (5516, 2), (5517, 2), (5518, 2), (5519, 2), (5540, 2), (5541, 2), (5542, 2), (5543, 2), (5564, 2), (5565, 2), (5566, 2), (5567, 2), (5588, 2), (5589, 2), (5590, 2), (5591, 2), (5612, 2), (5613, 2), (5614, 2), (5615, 2), (5636, 2), (5637, 2), (5638, 2), (5639, 2), (5660, 2), (5661, 2), (5662, 2), (5663, 2), (5684, 2), (5685, 2), (5686, 2), (5687, 2)]
theorem det04Term3Row08_decode : SparsePolynomial.decodeCubic 24 det04Term3Row08 = SparsePolynomial.monoTimes [9] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row08 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row08 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [9]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row08_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row09 : CoefficientMerge.Poly := [(836, 2), (837, 2), (838, 2), (839, 2), (1412, 2), (1413, 2), (1414, 2), (1415, 2), (1988, 2), (1989, 2), (1990, 2), (1991, 2), (2564, 2), (2565, 2), (2566, 2), (2567, 2), (3140, 2), (3141, 2), (3142, 2), (3143, 2), (3716, 2), (3717, 2), (3718, 2), (3719, 2), (4292, 2), (4293, 2), (4294, 2), (4295, 2), (4868, 2), (4869, 2), (4870, 2), (4871, 2), (5444, 2), (5445, 2), (5446, 2), (5447, 2), (6020, 2), (6021, 2), (6022, 2), (6023, 2), (6044, 2), (6045, 2), (6046, 2), (6047, 2), (6068, 2), (6069, 2), (6070, 2), (6071, 2), (6092, 2), (6093, 2), (6094, 2), (6095, 2), (6116, 2), (6117, 2), (6118, 2), (6119, 2), (6140, 2), (6141, 2), (6142, 2), (6143, 2), (6164, 2), (6165, 2), (6166, 2), (6167, 2), (6188, 2), (6189, 2), (6190, 2), (6191, 2), (6212, 2), (6213, 2), (6214, 2), (6215, 2), (6236, 2), (6237, 2), (6238, 2), (6239, 2), (6260, 2), (6261, 2), (6262, 2), (6263, 2)]
theorem det04Term3Row09_decode : SparsePolynomial.decodeCubic 24 det04Term3Row09 = SparsePolynomial.monoTimes [10] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row09 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row09 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [10]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row09_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row10 : CoefficientMerge.Poly := [(860, 2), (861, 2), (862, 2), (863, 2), (1436, 2), (1437, 2), (1438, 2), (1439, 2), (2012, 2), (2013, 2), (2014, 2), (2015, 2), (2588, 2), (2589, 2), (2590, 2), (2591, 2), (3164, 2), (3165, 2), (3166, 2), (3167, 2), (3740, 2), (3741, 2), (3742, 2), (3743, 2), (4316, 2), (4317, 2), (4318, 2), (4319, 2), (4892, 2), (4893, 2), (4894, 2), (4895, 2), (5468, 2), (5469, 2), (5470, 2), (5471, 2), (6044, 2), (6045, 2), (6046, 2), (6047, 2), (6620, 2), (6621, 2), (6622, 2), (6623, 2), (6644, 2), (6645, 2), (6646, 2), (6647, 2), (6668, 2), (6669, 2), (6670, 2), (6671, 2), (6692, 2), (6693, 2), (6694, 2), (6695, 2), (6716, 2), (6717, 2), (6718, 2), (6719, 2), (6740, 2), (6741, 2), (6742, 2), (6743, 2), (6764, 2), (6765, 2), (6766, 2), (6767, 2), (6788, 2), (6789, 2), (6790, 2), (6791, 2), (6812, 2), (6813, 2), (6814, 2), (6815, 2), (6836, 2), (6837, 2), (6838, 2), (6839, 2)]
theorem det04Term3Row10_decode : SparsePolynomial.decodeCubic 24 det04Term3Row10 = SparsePolynomial.monoTimes [11] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row10 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row10 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [11]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row10_decode, SparsePolynomial.eval_monoTimes]
  norm_num
def det04Term3Row11 : CoefficientMerge.Poly := [(884, 2), (885, 2), (886, 2), (887, 2), (1460, 2), (1461, 2), (1462, 2), (1463, 2), (2036, 2), (2037, 2), (2038, 2), (2039, 2), (2612, 2), (2613, 2), (2614, 2), (2615, 2), (3188, 2), (3189, 2), (3190, 2), (3191, 2), (3764, 2), (3765, 2), (3766, 2), (3767, 2), (4340, 2), (4341, 2), (4342, 2), (4343, 2), (4916, 2), (4917, 2), (4918, 2), (4919, 2), (5492, 2), (5493, 2), (5494, 2), (5495, 2), (6068, 2), (6069, 2), (6070, 2), (6071, 2), (6644, 2), (6645, 2), (6646, 2), (6647, 2), (7220, 2), (7221, 2), (7222, 2), (7223, 2), (7244, 2), (7245, 2), (7246, 2), (7247, 2), (7268, 2), (7269, 2), (7270, 2), (7271, 2), (7292, 2), (7293, 2), (7294, 2), (7295, 2), (7316, 2), (7317, 2), (7318, 2), (7319, 2), (7340, 2), (7341, 2), (7342, 2), (7343, 2), (7364, 2), (7365, 2), (7366, 2), (7367, 2), (7388, 2), (7389, 2), (7390, 2), (7391, 2), (7412, 2), (7413, 2), (7414, 2), (7415, 2)]
theorem det04Term3Row11_decode : SparsePolynomial.decodeCubic 24 det04Term3Row11 = SparsePolynomial.monoTimes [12] (-1 : Int) det04Pair3 := by decide +kernel
theorem eval_det04Term3Row11 (g : Fin 24 → ℝ) : CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) det04Term3Row11 = (-1 : ℝ)*SparsePolynomial.mon (gapValues g) [12]*SparsePolynomial.eval (gapValues g) det04Pair3 := by
  rw [← SparsePolynomial.eval_decodeCubic, det04Term3Row11_decode, SparsePolynomial.eval_monoTimes]
  norm_num

end APPT.Finite24
