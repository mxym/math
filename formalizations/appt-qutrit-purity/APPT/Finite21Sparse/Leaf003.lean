import APPT.Finite21Sparse.Base06
import APPT.Finite21Sparse.Base07
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0096 : SparsePolynomial.Poly := [([0,9,20], -4), ([1,9,20], -8), ([2,9,20], -16), ([3,9,20], -16), ([4,9,20], -16), ([5,9,20], -16), ([6,9,20], -16), ([7,9,20], -16), ([8,9,20], -16), ([9,9,20], -16), ([9,10,20], -16), ([9,11,20], -16), ([9,12,20], -16), ([9,13,20], -16), ([9,14,20], -16), ([9,15,20], -8), ([9,17,20], 8), ([9,18,20], 12), ([9,19,20], 16), ([9,20,20], 18)]
theorem atom0096_data : atom0096 = SparsePolynomial.monoTimes [9,20] 1 base06 := by decide +kernel
theorem eval_atom0096 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0096 = (quadB (outer g) ![1,2,2] * g 9 * g 20) := by
  rw [atom0096_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0096_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1251556516350 : Int) atom0096) := by
  rw [SparsePolynomial.eval_scale, eval_atom0096]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 9 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0096Coded : CoefficientMerge.Poly := [(209, -4), (650, -8), (1091, -16), (1532, -16), (1973, -16), (2414, -16), (2855, -16), (3296, -16), (3737, -16), (4178, -16), (4199, -16), (4220, -16), (4241, -16), (4262, -16), (4283, -16), (4304, -8), (4346, 8), (4367, 12), (4388, 16), (4409, 18)]
theorem atom0096Coded_decode : atom0096 = SparsePolynomial.decodeCubic 21 atom0096Coded := by decide +kernel
theorem atom0096Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1251556516350 : Int) atom0096Coded) := by
  have h := atom0096_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0096Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0097 : SparsePolynomial.Poly := [([0,10,11], -4), ([1,10,11], -8), ([2,10,11], -16), ([3,10,11], -16), ([4,10,11], -16), ([5,10,11], -16), ([6,10,11], -16), ([7,10,11], -16), ([8,10,11], -16), ([9,10,11], -16), ([10,10,11], -16), ([10,11,11], -16), ([10,11,12], -16), ([10,11,13], -16), ([10,11,14], -16), ([10,11,15], -8), ([10,11,17], 8), ([10,11,18], 12), ([10,11,19], 16), ([10,11,20], 18)]
theorem atom0097_data : atom0097 = SparsePolynomial.monoTimes [10,11] 1 base06 := by decide +kernel
theorem eval_atom0097 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0097 = (quadB (outer g) ![1,2,2] * g 10 * g 11) := by
  rw [atom0097_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0097_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (417466889280 : Int) atom0097) := by
  rw [SparsePolynomial.eval_scale, eval_atom0097]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0097Coded : CoefficientMerge.Poly := [(221, -4), (662, -8), (1103, -16), (1544, -16), (1985, -16), (2426, -16), (2867, -16), (3308, -16), (3749, -16), (4190, -16), (4631, -16), (4652, -16), (4653, -16), (4654, -16), (4655, -16), (4656, -8), (4658, 8), (4659, 12), (4660, 16), (4661, 18)]
theorem atom0097Coded_decode : atom0097 = SparsePolynomial.decodeCubic 21 atom0097Coded := by decide +kernel
theorem atom0097Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (417466889280 : Int) atom0097Coded) := by
  have h := atom0097_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0097Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0098 : SparsePolynomial.Poly := [([0,10,12], -4), ([1,10,12], -8), ([2,10,12], -16), ([3,10,12], -16), ([4,10,12], -16), ([5,10,12], -16), ([6,10,12], -16), ([7,10,12], -16), ([8,10,12], -16), ([9,10,12], -16), ([10,10,12], -16), ([10,11,12], -16), ([10,12,12], -16), ([10,12,13], -16), ([10,12,14], -16), ([10,12,15], -8), ([10,12,17], 8), ([10,12,18], 12), ([10,12,19], 16), ([10,12,20], 18)]
theorem atom0098_data : atom0098 = SparsePolynomial.monoTimes [10,12] 1 base06 := by decide +kernel
theorem eval_atom0098 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0098 = (quadB (outer g) ![1,2,2] * g 10 * g 12) := by
  rw [atom0098_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0098_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (906380102880 : Int) atom0098) := by
  rw [SparsePolynomial.eval_scale, eval_atom0098]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0098Coded : CoefficientMerge.Poly := [(222, -4), (663, -8), (1104, -16), (1545, -16), (1986, -16), (2427, -16), (2868, -16), (3309, -16), (3750, -16), (4191, -16), (4632, -16), (4653, -16), (4674, -16), (4675, -16), (4676, -16), (4677, -8), (4679, 8), (4680, 12), (4681, 16), (4682, 18)]
theorem atom0098Coded_decode : atom0098 = SparsePolynomial.decodeCubic 21 atom0098Coded := by decide +kernel
theorem atom0098Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (906380102880 : Int) atom0098Coded) := by
  have h := atom0098_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0098Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0099 : SparsePolynomial.Poly := [([0,10,13], -4), ([1,10,13], -8), ([2,10,13], -16), ([3,10,13], -16), ([4,10,13], -16), ([5,10,13], -16), ([6,10,13], -16), ([7,10,13], -16), ([8,10,13], -16), ([9,10,13], -16), ([10,10,13], -16), ([10,11,13], -16), ([10,12,13], -16), ([10,13,13], -16), ([10,13,14], -16), ([10,13,15], -8), ([10,13,17], 8), ([10,13,18], 12), ([10,13,19], 16), ([10,13,20], 18)]
theorem atom0099_data : atom0099 = SparsePolynomial.monoTimes [10,13] 1 base06 := by decide +kernel
theorem eval_atom0099 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0099 = (quadB (outer g) ![1,2,2] * g 10 * g 13) := by
  rw [atom0099_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0099_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (644978048400 : Int) atom0099) := by
  rw [SparsePolynomial.eval_scale, eval_atom0099]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0099Coded : CoefficientMerge.Poly := [(223, -4), (664, -8), (1105, -16), (1546, -16), (1987, -16), (2428, -16), (2869, -16), (3310, -16), (3751, -16), (4192, -16), (4633, -16), (4654, -16), (4675, -16), (4696, -16), (4697, -16), (4698, -8), (4700, 8), (4701, 12), (4702, 16), (4703, 18)]
theorem atom0099Coded_decode : atom0099 = SparsePolynomial.decodeCubic 21 atom0099Coded := by decide +kernel
theorem atom0099Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (644978048400 : Int) atom0099Coded) := by
  have h := atom0099_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0099Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0100 : SparsePolynomial.Poly := [([0,10,14], -4), ([1,10,14], -8), ([2,10,14], -16), ([3,10,14], -16), ([4,10,14], -16), ([5,10,14], -16), ([6,10,14], -16), ([7,10,14], -16), ([8,10,14], -16), ([9,10,14], -16), ([10,10,14], -16), ([10,11,14], -16), ([10,12,14], -16), ([10,13,14], -16), ([10,14,14], -16), ([10,14,15], -8), ([10,14,17], 8), ([10,14,18], 12), ([10,14,19], 16), ([10,14,20], 18)]
theorem atom0100_data : atom0100 = SparsePolynomial.monoTimes [10,14] 1 base06 := by decide +kernel
theorem eval_atom0100 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0100 = (quadB (outer g) ![1,2,2] * g 10 * g 14) := by
  rw [atom0100_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0100_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (317707009200 : Int) atom0100) := by
  rw [SparsePolynomial.eval_scale, eval_atom0100]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0100Coded : CoefficientMerge.Poly := [(224, -4), (665, -8), (1106, -16), (1547, -16), (1988, -16), (2429, -16), (2870, -16), (3311, -16), (3752, -16), (4193, -16), (4634, -16), (4655, -16), (4676, -16), (4697, -16), (4718, -16), (4719, -8), (4721, 8), (4722, 12), (4723, 16), (4724, 18)]
theorem atom0100Coded_decode : atom0100 = SparsePolynomial.decodeCubic 21 atom0100Coded := by decide +kernel
theorem atom0100Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (317707009200 : Int) atom0100Coded) := by
  have h := atom0100_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0100Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0101 : SparsePolynomial.Poly := [([0,10,16], -4), ([1,10,16], -8), ([2,10,16], -16), ([3,10,16], -16), ([4,10,16], -16), ([5,10,16], -16), ([6,10,16], -16), ([7,10,16], -16), ([8,10,16], -16), ([9,10,16], -16), ([10,10,16], -16), ([10,11,16], -16), ([10,12,16], -16), ([10,13,16], -16), ([10,14,16], -16), ([10,15,16], -8), ([10,16,17], 8), ([10,16,18], 12), ([10,16,19], 16), ([10,16,20], 18)]
theorem atom0101_data : atom0101 = SparsePolynomial.monoTimes [10,16] 1 base06 := by decide +kernel
theorem eval_atom0101 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0101 = (quadB (outer g) ![1,2,2] * g 10 * g 16) := by
  rw [atom0101_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0101_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (241725824550 : Int) atom0101) := by
  rw [SparsePolynomial.eval_scale, eval_atom0101]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0101Coded : CoefficientMerge.Poly := [(226, -4), (667, -8), (1108, -16), (1549, -16), (1990, -16), (2431, -16), (2872, -16), (3313, -16), (3754, -16), (4195, -16), (4636, -16), (4657, -16), (4678, -16), (4699, -16), (4720, -16), (4741, -8), (4763, 8), (4764, 12), (4765, 16), (4766, 18)]
theorem atom0101Coded_decode : atom0101 = SparsePolynomial.decodeCubic 21 atom0101Coded := by decide +kernel
theorem atom0101Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (241725824550 : Int) atom0101Coded) := by
  have h := atom0101_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0101Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0102 : SparsePolynomial.Poly := [([0,10,18], -4), ([1,10,18], -8), ([2,10,18], -16), ([3,10,18], -16), ([4,10,18], -16), ([5,10,18], -16), ([6,10,18], -16), ([7,10,18], -16), ([8,10,18], -16), ([9,10,18], -16), ([10,10,18], -16), ([10,11,18], -16), ([10,12,18], -16), ([10,13,18], -16), ([10,14,18], -16), ([10,15,18], -8), ([10,17,18], 8), ([10,18,18], 12), ([10,18,19], 16), ([10,18,20], 18)]
theorem atom0102_data : atom0102 = SparsePolynomial.monoTimes [10,18] 1 base06 := by decide +kernel
theorem eval_atom0102 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0102 = (quadB (outer g) ![1,2,2] * g 10 * g 18) := by
  rw [atom0102_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0102_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (229660045650 : Int) atom0102) := by
  rw [SparsePolynomial.eval_scale, eval_atom0102]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 18) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0102Coded : CoefficientMerge.Poly := [(228, -4), (669, -8), (1110, -16), (1551, -16), (1992, -16), (2433, -16), (2874, -16), (3315, -16), (3756, -16), (4197, -16), (4638, -16), (4659, -16), (4680, -16), (4701, -16), (4722, -16), (4743, -8), (4785, 8), (4806, 12), (4807, 16), (4808, 18)]
theorem atom0102Coded_decode : atom0102 = SparsePolynomial.decodeCubic 21 atom0102Coded := by decide +kernel
theorem atom0102Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (229660045650 : Int) atom0102Coded) := by
  have h := atom0102_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0102Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0103 : SparsePolynomial.Poly := [([0,10,19], -4), ([1,10,19], -8), ([2,10,19], -16), ([3,10,19], -16), ([4,10,19], -16), ([5,10,19], -16), ([6,10,19], -16), ([7,10,19], -16), ([8,10,19], -16), ([9,10,19], -16), ([10,10,19], -16), ([10,11,19], -16), ([10,12,19], -16), ([10,13,19], -16), ([10,14,19], -16), ([10,15,19], -8), ([10,17,19], 8), ([10,18,19], 12), ([10,19,19], 16), ([10,19,20], 18)]
theorem atom0103_data : atom0103 = SparsePolynomial.monoTimes [10,19] 1 base06 := by decide +kernel
theorem eval_atom0103 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0103 = (quadB (outer g) ![1,2,2] * g 10 * g 19) := by
  rw [atom0103_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0103_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1443556935450 : Int) atom0103) := by
  rw [SparsePolynomial.eval_scale, eval_atom0103]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0103Coded : CoefficientMerge.Poly := [(229, -4), (670, -8), (1111, -16), (1552, -16), (1993, -16), (2434, -16), (2875, -16), (3316, -16), (3757, -16), (4198, -16), (4639, -16), (4660, -16), (4681, -16), (4702, -16), (4723, -16), (4744, -8), (4786, 8), (4807, 12), (4828, 16), (4829, 18)]
theorem atom0103Coded_decode : atom0103 = SparsePolynomial.decodeCubic 21 atom0103Coded := by decide +kernel
theorem atom0103Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1443556935450 : Int) atom0103Coded) := by
  have h := atom0103_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0103Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0104 : SparsePolynomial.Poly := [([0,10,20], -4), ([1,10,20], -8), ([2,10,20], -16), ([3,10,20], -16), ([4,10,20], -16), ([5,10,20], -16), ([6,10,20], -16), ([7,10,20], -16), ([8,10,20], -16), ([9,10,20], -16), ([10,10,20], -16), ([10,11,20], -16), ([10,12,20], -16), ([10,13,20], -16), ([10,14,20], -16), ([10,15,20], -8), ([10,17,20], 8), ([10,18,20], 12), ([10,19,20], 16), ([10,20,20], 18)]
theorem atom0104_data : atom0104 = SparsePolynomial.monoTimes [10,20] 1 base06 := by decide +kernel
theorem eval_atom0104 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0104 = (quadB (outer g) ![1,2,2] * g 10 * g 20) := by
  rw [atom0104_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0104_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (997540913250 : Int) atom0104) := by
  rw [SparsePolynomial.eval_scale, eval_atom0104]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 10 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0104Coded : CoefficientMerge.Poly := [(230, -4), (671, -8), (1112, -16), (1553, -16), (1994, -16), (2435, -16), (2876, -16), (3317, -16), (3758, -16), (4199, -16), (4640, -16), (4661, -16), (4682, -16), (4703, -16), (4724, -16), (4745, -8), (4787, 8), (4808, 12), (4829, 16), (4850, 18)]
theorem atom0104Coded_decode : atom0104 = SparsePolynomial.decodeCubic 21 atom0104Coded := by decide +kernel
theorem atom0104Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (997540913250 : Int) atom0104Coded) := by
  have h := atom0104_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0104Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0105 : SparsePolynomial.Poly := [([0,11,12], -4), ([1,11,12], -8), ([2,11,12], -16), ([3,11,12], -16), ([4,11,12], -16), ([5,11,12], -16), ([6,11,12], -16), ([7,11,12], -16), ([8,11,12], -16), ([9,11,12], -16), ([10,11,12], -16), ([11,11,12], -16), ([11,12,12], -16), ([11,12,13], -16), ([11,12,14], -16), ([11,12,15], -8), ([11,12,17], 8), ([11,12,18], 12), ([11,12,19], 16), ([11,12,20], 18)]
theorem atom0105_data : atom0105 = SparsePolynomial.monoTimes [11,12] 1 base06 := by decide +kernel
theorem eval_atom0105 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0105 = (quadB (outer g) ![1,2,2] * g 11 * g 12) := by
  rw [atom0105_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0105_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (390768144480 : Int) atom0105) := by
  rw [SparsePolynomial.eval_scale, eval_atom0105]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0105Coded : CoefficientMerge.Poly := [(243, -4), (684, -8), (1125, -16), (1566, -16), (2007, -16), (2448, -16), (2889, -16), (3330, -16), (3771, -16), (4212, -16), (4653, -16), (5094, -16), (5115, -16), (5116, -16), (5117, -16), (5118, -8), (5120, 8), (5121, 12), (5122, 16), (5123, 18)]
theorem atom0105Coded_decode : atom0105 = SparsePolynomial.decodeCubic 21 atom0105Coded := by decide +kernel
theorem atom0105Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (390768144480 : Int) atom0105Coded) := by
  have h := atom0105_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0105Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0106 : SparsePolynomial.Poly := [([0,11,13], -4), ([1,11,13], -8), ([2,11,13], -16), ([3,11,13], -16), ([4,11,13], -16), ([5,11,13], -16), ([6,11,13], -16), ([7,11,13], -16), ([8,11,13], -16), ([9,11,13], -16), ([10,11,13], -16), ([11,11,13], -16), ([11,12,13], -16), ([11,13,13], -16), ([11,13,14], -16), ([11,13,15], -8), ([11,13,17], 8), ([11,13,18], 12), ([11,13,19], 16), ([11,13,20], 18)]
theorem atom0106_data : atom0106 = SparsePolynomial.monoTimes [11,13] 1 base06 := by decide +kernel
theorem eval_atom0106 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0106 = (quadB (outer g) ![1,2,2] * g 11 * g 13) := by
  rw [atom0106_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0106_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (821585116800 : Int) atom0106) := by
  rw [SparsePolynomial.eval_scale, eval_atom0106]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0106Coded : CoefficientMerge.Poly := [(244, -4), (685, -8), (1126, -16), (1567, -16), (2008, -16), (2449, -16), (2890, -16), (3331, -16), (3772, -16), (4213, -16), (4654, -16), (5095, -16), (5116, -16), (5137, -16), (5138, -16), (5139, -8), (5141, 8), (5142, 12), (5143, 16), (5144, 18)]
theorem atom0106Coded_decode : atom0106 = SparsePolynomial.decodeCubic 21 atom0106Coded := by decide +kernel
theorem atom0106Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (821585116800 : Int) atom0106Coded) := by
  have h := atom0106_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0106Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0107 : SparsePolynomial.Poly := [([0,11,14], -4), ([1,11,14], -8), ([2,11,14], -16), ([3,11,14], -16), ([4,11,14], -16), ([5,11,14], -16), ([6,11,14], -16), ([7,11,14], -16), ([8,11,14], -16), ([9,11,14], -16), ([10,11,14], -16), ([11,11,14], -16), ([11,12,14], -16), ([11,13,14], -16), ([11,14,14], -16), ([11,14,15], -8), ([11,14,17], 8), ([11,14,18], 12), ([11,14,19], 16), ([11,14,20], 18)]
theorem atom0107_data : atom0107 = SparsePolynomial.monoTimes [11,14] 1 base06 := by decide +kernel
theorem eval_atom0107 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0107 = (quadB (outer g) ![1,2,2] * g 11 * g 14) := by
  rw [atom0107_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0107_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (405398800800 : Int) atom0107) := by
  rw [SparsePolynomial.eval_scale, eval_atom0107]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0107Coded : CoefficientMerge.Poly := [(245, -4), (686, -8), (1127, -16), (1568, -16), (2009, -16), (2450, -16), (2891, -16), (3332, -16), (3773, -16), (4214, -16), (4655, -16), (5096, -16), (5117, -16), (5138, -16), (5159, -16), (5160, -8), (5162, 8), (5163, 12), (5164, 16), (5165, 18)]
theorem atom0107Coded_decode : atom0107 = SparsePolynomial.decodeCubic 21 atom0107Coded := by decide +kernel
theorem atom0107Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (405398800800 : Int) atom0107Coded) := by
  have h := atom0107_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0107Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0108 : SparsePolynomial.Poly := [([0,11,16], -4), ([1,11,16], -8), ([2,11,16], -16), ([3,11,16], -16), ([4,11,16], -16), ([5,11,16], -16), ([6,11,16], -16), ([7,11,16], -16), ([8,11,16], -16), ([9,11,16], -16), ([10,11,16], -16), ([11,11,16], -16), ([11,12,16], -16), ([11,13,16], -16), ([11,14,16], -16), ([11,15,16], -8), ([11,16,17], 8), ([11,16,18], 12), ([11,16,19], 16), ([11,16,20], 18)]
theorem atom0108_data : atom0108 = SparsePolynomial.monoTimes [11,16] 1 base06 := by decide +kernel
theorem eval_atom0108 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0108 = (quadB (outer g) ![1,2,2] * g 11 * g 16) := by
  rw [atom0108_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0108_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (164356819200 : Int) atom0108) := by
  rw [SparsePolynomial.eval_scale, eval_atom0108]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0108Coded : CoefficientMerge.Poly := [(247, -4), (688, -8), (1129, -16), (1570, -16), (2011, -16), (2452, -16), (2893, -16), (3334, -16), (3775, -16), (4216, -16), (4657, -16), (5098, -16), (5119, -16), (5140, -16), (5161, -16), (5182, -8), (5204, 8), (5205, 12), (5206, 16), (5207, 18)]
theorem atom0108Coded_decode : atom0108 = SparsePolynomial.decodeCubic 21 atom0108Coded := by decide +kernel
theorem atom0108Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (164356819200 : Int) atom0108Coded) := by
  have h := atom0108_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0108Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0109 : SparsePolynomial.Poly := [([0,11,19], -4), ([1,11,19], -8), ([2,11,19], -16), ([3,11,19], -16), ([4,11,19], -16), ([5,11,19], -16), ([6,11,19], -16), ([7,11,19], -16), ([8,11,19], -16), ([9,11,19], -16), ([10,11,19], -16), ([11,11,19], -16), ([11,12,19], -16), ([11,13,19], -16), ([11,14,19], -16), ([11,15,19], -8), ([11,17,19], 8), ([11,18,19], 12), ([11,19,19], 16), ([11,19,20], 18)]
theorem atom0109_data : atom0109 = SparsePolynomial.monoTimes [11,19] 1 base06 := by decide +kernel
theorem eval_atom0109 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0109 = (quadB (outer g) ![1,2,2] * g 11 * g 19) := by
  rw [atom0109_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0109_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1156414996800 : Int) atom0109) := by
  rw [SparsePolynomial.eval_scale, eval_atom0109]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0109Coded : CoefficientMerge.Poly := [(250, -4), (691, -8), (1132, -16), (1573, -16), (2014, -16), (2455, -16), (2896, -16), (3337, -16), (3778, -16), (4219, -16), (4660, -16), (5101, -16), (5122, -16), (5143, -16), (5164, -16), (5185, -8), (5227, 8), (5248, 12), (5269, 16), (5270, 18)]
theorem atom0109Coded_decode : atom0109 = SparsePolynomial.decodeCubic 21 atom0109Coded := by decide +kernel
theorem atom0109Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1156414996800 : Int) atom0109Coded) := by
  have h := atom0109_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0109Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0110 : SparsePolynomial.Poly := [([0,11,20], -4), ([1,11,20], -8), ([2,11,20], -16), ([3,11,20], -16), ([4,11,20], -16), ([5,11,20], -16), ([6,11,20], -16), ([7,11,20], -16), ([8,11,20], -16), ([9,11,20], -16), ([10,11,20], -16), ([11,11,20], -16), ([11,12,20], -16), ([11,13,20], -16), ([11,14,20], -16), ([11,15,20], -8), ([11,17,20], 8), ([11,18,20], 12), ([11,19,20], 16), ([11,20,20], 18)]
theorem atom0110_data : atom0110 = SparsePolynomial.monoTimes [11,20] 1 base06 := by decide +kernel
theorem eval_atom0110 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0110 = (quadB (outer g) ![1,2,2] * g 11 * g 20) := by
  rw [atom0110_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0110_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (638510040000 : Int) atom0110) := by
  rw [SparsePolynomial.eval_scale, eval_atom0110]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 11 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0110Coded : CoefficientMerge.Poly := [(251, -4), (692, -8), (1133, -16), (1574, -16), (2015, -16), (2456, -16), (2897, -16), (3338, -16), (3779, -16), (4220, -16), (4661, -16), (5102, -16), (5123, -16), (5144, -16), (5165, -16), (5186, -8), (5228, 8), (5249, 12), (5270, 16), (5291, 18)]
theorem atom0110Coded_decode : atom0110 = SparsePolynomial.decodeCubic 21 atom0110Coded := by decide +kernel
theorem atom0110Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (638510040000 : Int) atom0110Coded) := by
  have h := atom0110_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0110Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0111 : SparsePolynomial.Poly := [([0,12,13], -4), ([1,12,13], -8), ([2,12,13], -16), ([3,12,13], -16), ([4,12,13], -16), ([5,12,13], -16), ([6,12,13], -16), ([7,12,13], -16), ([8,12,13], -16), ([9,12,13], -16), ([10,12,13], -16), ([11,12,13], -16), ([12,12,13], -16), ([12,13,13], -16), ([12,13,14], -16), ([12,13,15], -8), ([12,13,17], 8), ([12,13,18], 12), ([12,13,19], 16), ([12,13,20], 18)]
theorem atom0111_data : atom0111 = SparsePolynomial.monoTimes [12,13] 1 base06 := by decide +kernel
theorem eval_atom0111 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0111 = (quadB (outer g) ![1,2,2] * g 12 * g 13) := by
  rw [atom0111_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0111_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (330801340800 : Int) atom0111) := by
  rw [SparsePolynomial.eval_scale, eval_atom0111]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0111Coded : CoefficientMerge.Poly := [(265, -4), (706, -8), (1147, -16), (1588, -16), (2029, -16), (2470, -16), (2911, -16), (3352, -16), (3793, -16), (4234, -16), (4675, -16), (5116, -16), (5557, -16), (5578, -16), (5579, -16), (5580, -8), (5582, 8), (5583, 12), (5584, 16), (5585, 18)]
theorem atom0111Coded_decode : atom0111 = SparsePolynomial.decodeCubic 21 atom0111Coded := by decide +kernel
theorem atom0111Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (330801340800 : Int) atom0111Coded) := by
  have h := atom0111_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0111Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0112 : SparsePolynomial.Poly := [([0,12,14], -4), ([1,12,14], -8), ([2,12,14], -16), ([3,12,14], -16), ([4,12,14], -16), ([5,12,14], -16), ([6,12,14], -16), ([7,12,14], -16), ([8,12,14], -16), ([9,12,14], -16), ([10,12,14], -16), ([11,12,14], -16), ([12,12,14], -16), ([12,13,14], -16), ([12,14,14], -16), ([12,14,15], -8), ([12,14,17], 8), ([12,14,18], 12), ([12,14,19], 16), ([12,14,20], 18)]
theorem atom0112_data : atom0112 = SparsePolynomial.monoTimes [12,14] 1 base06 := by decide +kernel
theorem eval_atom0112 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0112 = (quadB (outer g) ![1,2,2] * g 12 * g 14) := by
  rw [atom0112_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0112_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (650421156000 : Int) atom0112) := by
  rw [SparsePolynomial.eval_scale, eval_atom0112]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0112Coded : CoefficientMerge.Poly := [(266, -4), (707, -8), (1148, -16), (1589, -16), (2030, -16), (2471, -16), (2912, -16), (3353, -16), (3794, -16), (4235, -16), (4676, -16), (5117, -16), (5558, -16), (5579, -16), (5600, -16), (5601, -8), (5603, 8), (5604, 12), (5605, 16), (5606, 18)]
theorem atom0112Coded_decode : atom0112 = SparsePolynomial.decodeCubic 21 atom0112Coded := by decide +kernel
theorem atom0112Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (650421156000 : Int) atom0112Coded) := by
  have h := atom0112_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0112Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0113 : SparsePolynomial.Poly := [([0,12,16], -4), ([1,12,16], -8), ([2,12,16], -16), ([3,12,16], -16), ([4,12,16], -16), ([5,12,16], -16), ([6,12,16], -16), ([7,12,16], -16), ([8,12,16], -16), ([9,12,16], -16), ([10,12,16], -16), ([11,12,16], -16), ([12,12,16], -16), ([12,13,16], -16), ([12,14,16], -16), ([12,15,16], -8), ([12,16,17], 8), ([12,16,18], 12), ([12,16,19], 16), ([12,16,20], 18)]
theorem atom0113_data : atom0113 = SparsePolynomial.monoTimes [12,16] 1 base06 := by decide +kernel
theorem eval_atom0113 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0113 = (quadB (outer g) ![1,2,2] * g 12 * g 16) := by
  rw [atom0113_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0113_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (271117319200 : Int) atom0113) := by
  rw [SparsePolynomial.eval_scale, eval_atom0113]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0113Coded : CoefficientMerge.Poly := [(268, -4), (709, -8), (1150, -16), (1591, -16), (2032, -16), (2473, -16), (2914, -16), (3355, -16), (3796, -16), (4237, -16), (4678, -16), (5119, -16), (5560, -16), (5581, -16), (5602, -16), (5623, -8), (5645, 8), (5646, 12), (5647, 16), (5648, 18)]
theorem atom0113Coded_decode : atom0113 = SparsePolynomial.decodeCubic 21 atom0113Coded := by decide +kernel
theorem atom0113Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (271117319200 : Int) atom0113Coded) := by
  have h := atom0113_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0113Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0114 : SparsePolynomial.Poly := [([0,12,19], -4), ([1,12,19], -8), ([2,12,19], -16), ([3,12,19], -16), ([4,12,19], -16), ([5,12,19], -16), ([6,12,19], -16), ([7,12,19], -16), ([8,12,19], -16), ([9,12,19], -16), ([10,12,19], -16), ([11,12,19], -16), ([12,12,19], -16), ([12,13,19], -16), ([12,14,19], -16), ([12,15,19], -8), ([12,17,19], 8), ([12,18,19], 12), ([12,19,19], 16), ([12,19,20], 18)]
theorem atom0114_data : atom0114 = SparsePolynomial.monoTimes [12,19] 1 base06 := by decide +kernel
theorem eval_atom0114 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0114 = (quadB (outer g) ![1,2,2] * g 12 * g 19) := by
  rw [atom0114_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0114_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (808085588800 : Int) atom0114) := by
  rw [SparsePolynomial.eval_scale, eval_atom0114]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0114Coded : CoefficientMerge.Poly := [(271, -4), (712, -8), (1153, -16), (1594, -16), (2035, -16), (2476, -16), (2917, -16), (3358, -16), (3799, -16), (4240, -16), (4681, -16), (5122, -16), (5563, -16), (5584, -16), (5605, -16), (5626, -8), (5668, 8), (5689, 12), (5710, 16), (5711, 18)]
theorem atom0114Coded_decode : atom0114 = SparsePolynomial.decodeCubic 21 atom0114Coded := by decide +kernel
theorem atom0114Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (808085588800 : Int) atom0114Coded) := by
  have h := atom0114_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0114Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0115 : SparsePolynomial.Poly := [([0,12,20], -4), ([1,12,20], -8), ([2,12,20], -16), ([3,12,20], -16), ([4,12,20], -16), ([5,12,20], -16), ([6,12,20], -16), ([7,12,20], -16), ([8,12,20], -16), ([9,12,20], -16), ([10,12,20], -16), ([11,12,20], -16), ([12,12,20], -16), ([12,13,20], -16), ([12,14,20], -16), ([12,15,20], -8), ([12,17,20], 8), ([12,18,20], 12), ([12,19,20], 16), ([12,20,20], 18)]
theorem atom0115_data : atom0115 = SparsePolynomial.monoTimes [12,20] 1 base06 := by decide +kernel
theorem eval_atom0115 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0115 = (quadB (outer g) ![1,2,2] * g 12 * g 20) := by
  rw [atom0115_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0115_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (224744637600 : Int) atom0115) := by
  rw [SparsePolynomial.eval_scale, eval_atom0115]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 12 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0115Coded : CoefficientMerge.Poly := [(272, -4), (713, -8), (1154, -16), (1595, -16), (2036, -16), (2477, -16), (2918, -16), (3359, -16), (3800, -16), (4241, -16), (4682, -16), (5123, -16), (5564, -16), (5585, -16), (5606, -16), (5627, -8), (5669, 8), (5690, 12), (5711, 16), (5732, 18)]
theorem atom0115Coded_decode : atom0115 = SparsePolynomial.decodeCubic 21 atom0115Coded := by decide +kernel
theorem atom0115Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (224744637600 : Int) atom0115Coded) := by
  have h := atom0115_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0115Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0116 : SparsePolynomial.Poly := [([0,13,15], -4), ([1,13,15], -8), ([2,13,15], -16), ([3,13,15], -16), ([4,13,15], -16), ([5,13,15], -16), ([6,13,15], -16), ([7,13,15], -16), ([8,13,15], -16), ([9,13,15], -16), ([10,13,15], -16), ([11,13,15], -16), ([12,13,15], -16), ([13,13,15], -16), ([13,14,15], -16), ([13,15,15], -8), ([13,15,17], 8), ([13,15,18], 12), ([13,15,19], 16), ([13,15,20], 18)]
theorem atom0116_data : atom0116 = SparsePolynomial.monoTimes [13,15] 1 base06 := by decide +kernel
theorem eval_atom0116 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0116 = (quadB (outer g) ![1,2,2] * g 13 * g 15) := by
  rw [atom0116_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0116_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49939337700 : Int) atom0116) := by
  rw [SparsePolynomial.eval_scale, eval_atom0116]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0116Coded : CoefficientMerge.Poly := [(288, -4), (729, -8), (1170, -16), (1611, -16), (2052, -16), (2493, -16), (2934, -16), (3375, -16), (3816, -16), (4257, -16), (4698, -16), (5139, -16), (5580, -16), (6021, -16), (6042, -16), (6063, -8), (6065, 8), (6066, 12), (6067, 16), (6068, 18)]
theorem atom0116Coded_decode : atom0116 = SparsePolynomial.decodeCubic 21 atom0116Coded := by decide +kernel
theorem atom0116Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49939337700 : Int) atom0116Coded) := by
  have h := atom0116_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0116Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0117 : SparsePolynomial.Poly := [([0,13,16], -4), ([1,13,16], -8), ([2,13,16], -16), ([3,13,16], -16), ([4,13,16], -16), ([5,13,16], -16), ([6,13,16], -16), ([7,13,16], -16), ([8,13,16], -16), ([9,13,16], -16), ([10,13,16], -16), ([11,13,16], -16), ([12,13,16], -16), ([13,13,16], -16), ([13,14,16], -16), ([13,15,16], -8), ([13,16,17], 8), ([13,16,18], 12), ([13,16,19], 16), ([13,16,20], 18)]
theorem atom0117_data : atom0117 = SparsePolynomial.monoTimes [13,16] 1 base06 := by decide +kernel
theorem eval_atom0117 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0117 = (quadB (outer g) ![1,2,2] * g 13 * g 16) := by
  rw [atom0117_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0117_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (194120325900 : Int) atom0117) := by
  rw [SparsePolynomial.eval_scale, eval_atom0117]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0117Coded : CoefficientMerge.Poly := [(289, -4), (730, -8), (1171, -16), (1612, -16), (2053, -16), (2494, -16), (2935, -16), (3376, -16), (3817, -16), (4258, -16), (4699, -16), (5140, -16), (5581, -16), (6022, -16), (6043, -16), (6064, -8), (6086, 8), (6087, 12), (6088, 16), (6089, 18)]
theorem atom0117Coded_decode : atom0117 = SparsePolynomial.decodeCubic 21 atom0117Coded := by decide +kernel
theorem atom0117Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (194120325900 : Int) atom0117Coded) := by
  have h := atom0117_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0117Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0118 : SparsePolynomial.Poly := [([0,13,19], -4), ([1,13,19], -8), ([2,13,19], -16), ([3,13,19], -16), ([4,13,19], -16), ([5,13,19], -16), ([6,13,19], -16), ([7,13,19], -16), ([8,13,19], -16), ([9,13,19], -16), ([10,13,19], -16), ([11,13,19], -16), ([12,13,19], -16), ([13,13,19], -16), ([13,14,19], -16), ([13,15,19], -8), ([13,17,19], 8), ([13,18,19], 12), ([13,19,19], 16), ([13,19,20], 18)]
theorem atom0118_data : atom0118 = SparsePolynomial.monoTimes [13,19] 1 base06 := by decide +kernel
theorem eval_atom0118 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0118 = (quadB (outer g) ![1,2,2] * g 13 * g 19) := by
  rw [atom0118_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0118_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (292376711700 : Int) atom0118) := by
  rw [SparsePolynomial.eval_scale, eval_atom0118]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 13 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0118Coded : CoefficientMerge.Poly := [(292, -4), (733, -8), (1174, -16), (1615, -16), (2056, -16), (2497, -16), (2938, -16), (3379, -16), (3820, -16), (4261, -16), (4702, -16), (5143, -16), (5584, -16), (6025, -16), (6046, -16), (6067, -8), (6109, 8), (6130, 12), (6151, 16), (6152, 18)]
theorem atom0118Coded_decode : atom0118 = SparsePolynomial.decodeCubic 21 atom0118Coded := by decide +kernel
theorem atom0118Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (292376711700 : Int) atom0118Coded) := by
  have h := atom0118_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0118Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0119 : SparsePolynomial.Poly := [([0,14,15], -4), ([1,14,15], -8), ([2,14,15], -16), ([3,14,15], -16), ([4,14,15], -16), ([5,14,15], -16), ([6,14,15], -16), ([7,14,15], -16), ([8,14,15], -16), ([9,14,15], -16), ([10,14,15], -16), ([11,14,15], -16), ([12,14,15], -16), ([13,14,15], -16), ([14,14,15], -16), ([14,15,15], -8), ([14,15,17], 8), ([14,15,18], 12), ([14,15,19], 16), ([14,15,20], 18)]
theorem atom0119_data : atom0119 = SparsePolynomial.monoTimes [14,15] 1 base06 := by decide +kernel
theorem eval_atom0119 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0119 = (quadB (outer g) ![1,2,2] * g 14 * g 15) := by
  rw [atom0119_data, SparsePolynomial.eval_monoTimes, eval_base06]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0119_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10631174400 : Int) atom0119) := by
  rw [SparsePolynomial.eval_scale, eval_atom0119]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hb := base06_nonneg g hg hA hB
  rw [eval_base06] at hb
  have ht : 0 ≤ (quadB (outer g) ![1,2,2] * g 14 * g 15) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0119Coded : CoefficientMerge.Poly := [(309, -4), (750, -8), (1191, -16), (1632, -16), (2073, -16), (2514, -16), (2955, -16), (3396, -16), (3837, -16), (4278, -16), (4719, -16), (5160, -16), (5601, -16), (6042, -16), (6483, -16), (6504, -8), (6506, 8), (6507, 12), (6508, 16), (6509, 18)]
theorem atom0119Coded_decode : atom0119 = SparsePolynomial.decodeCubic 21 atom0119Coded := by decide +kernel
theorem atom0119Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10631174400 : Int) atom0119Coded) := by
  have h := atom0119_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0119Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0120 : SparsePolynomial.Poly := [([0,0,1], -8), ([0,1,1], -12), ([0,1,2], -16), ([0,1,3], -16), ([0,1,4], -16), ([0,1,5], -16), ([0,1,6], -16), ([0,1,7], -16), ([0,1,8], -16), ([0,1,9], -16), ([0,1,10], -16), ([0,1,11], -16), ([0,1,12], -16), ([0,1,13], -16), ([0,1,14], -16), ([0,1,15], -14), ([0,1,16], -10), ([0,1,17], -2), ([0,1,18], 2), ([0,1,19], 10), ([0,1,20], 18)]
theorem atom0120_data : atom0120 = SparsePolynomial.monoTimes [0,1] 1 base07 := by decide +kernel
theorem eval_atom0120 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0120 = (quadB (outer g) ![2,2,1] * g 0 * g 1) := by
  rw [atom0120_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0120_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (113801889600 : Int) atom0120) := by
  rw [SparsePolynomial.eval_scale, eval_atom0120]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0120Coded : CoefficientMerge.Poly := [(1, -8), (22, -12), (23, -16), (24, -16), (25, -16), (26, -16), (27, -16), (28, -16), (29, -16), (30, -16), (31, -16), (32, -16), (33, -16), (34, -16), (35, -16), (36, -14), (37, -10), (38, -2), (39, 2), (40, 10), (41, 18)]
theorem atom0120Coded_decode : atom0120 = SparsePolynomial.decodeCubic 21 atom0120Coded := by decide +kernel
theorem atom0120Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (113801889600 : Int) atom0120Coded) := by
  have h := atom0120_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0120Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0121 : SparsePolynomial.Poly := [([0,0,2], -8), ([0,1,2], -12), ([0,2,2], -16), ([0,2,3], -16), ([0,2,4], -16), ([0,2,5], -16), ([0,2,6], -16), ([0,2,7], -16), ([0,2,8], -16), ([0,2,9], -16), ([0,2,10], -16), ([0,2,11], -16), ([0,2,12], -16), ([0,2,13], -16), ([0,2,14], -16), ([0,2,15], -14), ([0,2,16], -10), ([0,2,17], -2), ([0,2,18], 2), ([0,2,19], 10), ([0,2,20], 18)]
theorem atom0121_data : atom0121 = SparsePolynomial.monoTimes [0,2] 1 base07 := by decide +kernel
theorem eval_atom0121 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0121 = (quadB (outer g) ![2,2,1] * g 0 * g 2) := by
  rw [atom0121_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0121_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (167199379200 : Int) atom0121) := by
  rw [SparsePolynomial.eval_scale, eval_atom0121]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 2) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0121Coded : CoefficientMerge.Poly := [(2, -8), (23, -12), (44, -16), (45, -16), (46, -16), (47, -16), (48, -16), (49, -16), (50, -16), (51, -16), (52, -16), (53, -16), (54, -16), (55, -16), (56, -16), (57, -14), (58, -10), (59, -2), (60, 2), (61, 10), (62, 18)]
theorem atom0121Coded_decode : atom0121 = SparsePolynomial.decodeCubic 21 atom0121Coded := by decide +kernel
theorem atom0121Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (167199379200 : Int) atom0121Coded) := by
  have h := atom0121_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0121Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0122 : SparsePolynomial.Poly := [([0,0,3], -8), ([0,1,3], -12), ([0,2,3], -16), ([0,3,3], -16), ([0,3,4], -16), ([0,3,5], -16), ([0,3,6], -16), ([0,3,7], -16), ([0,3,8], -16), ([0,3,9], -16), ([0,3,10], -16), ([0,3,11], -16), ([0,3,12], -16), ([0,3,13], -16), ([0,3,14], -16), ([0,3,15], -14), ([0,3,16], -10), ([0,3,17], -2), ([0,3,18], 2), ([0,3,19], 10), ([0,3,20], 18)]
theorem atom0122_data : atom0122 = SparsePolynomial.monoTimes [0,3] 1 base07 := by decide +kernel
theorem eval_atom0122 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0122 = (quadB (outer g) ![2,2,1] * g 0 * g 3) := by
  rw [atom0122_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0122_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (220596868800 : Int) atom0122) := by
  rw [SparsePolynomial.eval_scale, eval_atom0122]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 3) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0122Coded : CoefficientMerge.Poly := [(3, -8), (24, -12), (45, -16), (66, -16), (67, -16), (68, -16), (69, -16), (70, -16), (71, -16), (72, -16), (73, -16), (74, -16), (75, -16), (76, -16), (77, -16), (78, -14), (79, -10), (80, -2), (81, 2), (82, 10), (83, 18)]
theorem atom0122Coded_decode : atom0122 = SparsePolynomial.decodeCubic 21 atom0122Coded := by decide +kernel
theorem atom0122Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (220596868800 : Int) atom0122Coded) := by
  have h := atom0122_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0122Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0123 : SparsePolynomial.Poly := [([0,0,4], -8), ([0,1,4], -12), ([0,2,4], -16), ([0,3,4], -16), ([0,4,4], -16), ([0,4,5], -16), ([0,4,6], -16), ([0,4,7], -16), ([0,4,8], -16), ([0,4,9], -16), ([0,4,10], -16), ([0,4,11], -16), ([0,4,12], -16), ([0,4,13], -16), ([0,4,14], -16), ([0,4,15], -14), ([0,4,16], -10), ([0,4,17], -2), ([0,4,18], 2), ([0,4,19], 10), ([0,4,20], 18)]
theorem atom0123_data : atom0123 = SparsePolynomial.monoTimes [0,4] 1 base07 := by decide +kernel
theorem eval_atom0123 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0123 = (quadB (outer g) ![2,2,1] * g 0 * g 4) := by
  rw [atom0123_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0123_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (273994358400 : Int) atom0123) := by
  rw [SparsePolynomial.eval_scale, eval_atom0123]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0123Coded : CoefficientMerge.Poly := [(4, -8), (25, -12), (46, -16), (67, -16), (88, -16), (89, -16), (90, -16), (91, -16), (92, -16), (93, -16), (94, -16), (95, -16), (96, -16), (97, -16), (98, -16), (99, -14), (100, -10), (101, -2), (102, 2), (103, 10), (104, 18)]
theorem atom0123Coded_decode : atom0123 = SparsePolynomial.decodeCubic 21 atom0123Coded := by decide +kernel
theorem atom0123Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (273994358400 : Int) atom0123Coded) := by
  have h := atom0123_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0123Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0124 : SparsePolynomial.Poly := [([0,0,5], -8), ([0,1,5], -12), ([0,2,5], -16), ([0,3,5], -16), ([0,4,5], -16), ([0,5,5], -16), ([0,5,6], -16), ([0,5,7], -16), ([0,5,8], -16), ([0,5,9], -16), ([0,5,10], -16), ([0,5,11], -16), ([0,5,12], -16), ([0,5,13], -16), ([0,5,14], -16), ([0,5,15], -14), ([0,5,16], -10), ([0,5,17], -2), ([0,5,18], 2), ([0,5,19], 10), ([0,5,20], 18)]
theorem atom0124_data : atom0124 = SparsePolynomial.monoTimes [0,5] 1 base07 := by decide +kernel
theorem eval_atom0124 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0124 = (quadB (outer g) ![2,2,1] * g 0 * g 5) := by
  rw [atom0124_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0124_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140969602656 : Int) atom0124) := by
  rw [SparsePolynomial.eval_scale, eval_atom0124]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0124Coded : CoefficientMerge.Poly := [(5, -8), (26, -12), (47, -16), (68, -16), (89, -16), (110, -16), (111, -16), (112, -16), (113, -16), (114, -16), (115, -16), (116, -16), (117, -16), (118, -16), (119, -16), (120, -14), (121, -10), (122, -2), (123, 2), (124, 10), (125, 18)]
theorem atom0124Coded_decode : atom0124 = SparsePolynomial.decodeCubic 21 atom0124Coded := by decide +kernel
theorem atom0124Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (140969602656 : Int) atom0124Coded) := by
  have h := atom0124_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0124Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0125 : SparsePolynomial.Poly := [([0,0,6], -8), ([0,1,6], -12), ([0,2,6], -16), ([0,3,6], -16), ([0,4,6], -16), ([0,5,6], -16), ([0,6,6], -16), ([0,6,7], -16), ([0,6,8], -16), ([0,6,9], -16), ([0,6,10], -16), ([0,6,11], -16), ([0,6,12], -16), ([0,6,13], -16), ([0,6,14], -16), ([0,6,15], -14), ([0,6,16], -10), ([0,6,17], -2), ([0,6,18], 2), ([0,6,19], 10), ([0,6,20], 18)]
theorem atom0125_data : atom0125 = SparsePolynomial.monoTimes [0,6] 1 base07 := by decide +kernel
theorem eval_atom0125 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0125 = (quadB (outer g) ![2,2,1] * g 0 * g 6) := by
  rw [atom0125_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0125_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (137701468800 : Int) atom0125) := by
  rw [SparsePolynomial.eval_scale, eval_atom0125]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0125Coded : CoefficientMerge.Poly := [(6, -8), (27, -12), (48, -16), (69, -16), (90, -16), (111, -16), (132, -16), (133, -16), (134, -16), (135, -16), (136, -16), (137, -16), (138, -16), (139, -16), (140, -16), (141, -14), (142, -10), (143, -2), (144, 2), (145, 10), (146, 18)]
theorem atom0125Coded_decode : atom0125 = SparsePolynomial.decodeCubic 21 atom0125Coded := by decide +kernel
theorem atom0125Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (137701468800 : Int) atom0125Coded) := by
  have h := atom0125_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0125Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0126 : SparsePolynomial.Poly := [([0,0,7], -8), ([0,1,7], -12), ([0,2,7], -16), ([0,3,7], -16), ([0,4,7], -16), ([0,5,7], -16), ([0,6,7], -16), ([0,7,7], -16), ([0,7,8], -16), ([0,7,9], -16), ([0,7,10], -16), ([0,7,11], -16), ([0,7,12], -16), ([0,7,13], -16), ([0,7,14], -16), ([0,7,15], -14), ([0,7,16], -10), ([0,7,17], -2), ([0,7,18], 2), ([0,7,19], 10), ([0,7,20], 18)]
theorem atom0126_data : atom0126 = SparsePolynomial.monoTimes [0,7] 1 base07 := by decide +kernel
theorem eval_atom0126 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0126 = (quadB (outer g) ![2,2,1] * g 0 * g 7) := by
  rw [atom0126_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0126_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9374417712 : Int) atom0126) := by
  rw [SparsePolynomial.eval_scale, eval_atom0126]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0126Coded : CoefficientMerge.Poly := [(7, -8), (28, -12), (49, -16), (70, -16), (91, -16), (112, -16), (133, -16), (154, -16), (155, -16), (156, -16), (157, -16), (158, -16), (159, -16), (160, -16), (161, -16), (162, -14), (163, -10), (164, -2), (165, 2), (166, 10), (167, 18)]
theorem atom0126Coded_decode : atom0126 = SparsePolynomial.decodeCubic 21 atom0126Coded := by decide +kernel
theorem atom0126Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9374417712 : Int) atom0126Coded) := by
  have h := atom0126_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0126Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0127 : SparsePolynomial.Poly := [([0,0,11], -8), ([0,1,11], -12), ([0,2,11], -16), ([0,3,11], -16), ([0,4,11], -16), ([0,5,11], -16), ([0,6,11], -16), ([0,7,11], -16), ([0,8,11], -16), ([0,9,11], -16), ([0,10,11], -16), ([0,11,11], -16), ([0,11,12], -16), ([0,11,13], -16), ([0,11,14], -16), ([0,11,15], -14), ([0,11,16], -10), ([0,11,17], -2), ([0,11,18], 2), ([0,11,19], 10), ([0,11,20], 18)]
theorem atom0127_data : atom0127 = SparsePolynomial.monoTimes [0,11] 1 base07 := by decide +kernel
theorem eval_atom0127 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0127 = (quadB (outer g) ![2,2,1] * g 0 * g 11) := by
  rw [atom0127_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0127_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38990448000 : Int) atom0127) := by
  rw [SparsePolynomial.eval_scale, eval_atom0127]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0127Coded : CoefficientMerge.Poly := [(11, -8), (32, -12), (53, -16), (74, -16), (95, -16), (116, -16), (137, -16), (158, -16), (179, -16), (200, -16), (221, -16), (242, -16), (243, -16), (244, -16), (245, -16), (246, -14), (247, -10), (248, -2), (249, 2), (250, 10), (251, 18)]
theorem atom0127Coded_decode : atom0127 = SparsePolynomial.decodeCubic 21 atom0127Coded := by decide +kernel
theorem atom0127Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38990448000 : Int) atom0127Coded) := by
  have h := atom0127_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0127Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0128 : SparsePolynomial.Poly := [([0,0,12], -8), ([0,1,12], -12), ([0,2,12], -16), ([0,3,12], -16), ([0,4,12], -16), ([0,5,12], -16), ([0,6,12], -16), ([0,7,12], -16), ([0,8,12], -16), ([0,9,12], -16), ([0,10,12], -16), ([0,11,12], -16), ([0,12,12], -16), ([0,12,13], -16), ([0,12,14], -16), ([0,12,15], -14), ([0,12,16], -10), ([0,12,17], -2), ([0,12,18], 2), ([0,12,19], 10), ([0,12,20], 18)]
theorem atom0128_data : atom0128 = SparsePolynomial.monoTimes [0,12] 1 base07 := by decide +kernel
theorem eval_atom0128 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0128 = (quadB (outer g) ![2,2,1] * g 0 * g 12) := by
  rw [atom0128_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0128_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (334175038400 : Int) atom0128) := by
  rw [SparsePolynomial.eval_scale, eval_atom0128]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0128Coded : CoefficientMerge.Poly := [(12, -8), (33, -12), (54, -16), (75, -16), (96, -16), (117, -16), (138, -16), (159, -16), (180, -16), (201, -16), (222, -16), (243, -16), (264, -16), (265, -16), (266, -16), (267, -14), (268, -10), (269, -2), (270, 2), (271, 10), (272, 18)]
theorem atom0128Coded_decode : atom0128 = SparsePolynomial.decodeCubic 21 atom0128Coded := by decide +kernel
theorem atom0128Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (334175038400 : Int) atom0128Coded) := by
  have h := atom0128_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0128Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0129 : SparsePolynomial.Poly := [([0,0,13], -8), ([0,1,13], -12), ([0,2,13], -16), ([0,3,13], -16), ([0,4,13], -16), ([0,5,13], -16), ([0,6,13], -16), ([0,7,13], -16), ([0,8,13], -16), ([0,9,13], -16), ([0,10,13], -16), ([0,11,13], -16), ([0,12,13], -16), ([0,13,13], -16), ([0,13,14], -16), ([0,13,15], -14), ([0,13,16], -10), ([0,13,17], -2), ([0,13,18], 2), ([0,13,19], 10), ([0,13,20], 18)]
theorem atom0129_data : atom0129 = SparsePolynomial.monoTimes [0,13] 1 base07 := by decide +kernel
theorem eval_atom0129 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0129 = (quadB (outer g) ![2,2,1] * g 0 * g 13) := by
  rw [atom0129_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0129_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (411474772800 : Int) atom0129) := by
  rw [SparsePolynomial.eval_scale, eval_atom0129]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0129Coded : CoefficientMerge.Poly := [(13, -8), (34, -12), (55, -16), (76, -16), (97, -16), (118, -16), (139, -16), (160, -16), (181, -16), (202, -16), (223, -16), (244, -16), (265, -16), (286, -16), (287, -16), (288, -14), (289, -10), (290, -2), (291, 2), (292, 10), (293, 18)]
theorem atom0129Coded_decode : atom0129 = SparsePolynomial.decodeCubic 21 atom0129Coded := by decide +kernel
theorem atom0129Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (411474772800 : Int) atom0129Coded) := by
  have h := atom0129_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0129Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0130 : SparsePolynomial.Poly := [([0,0,14], -8), ([0,1,14], -12), ([0,2,14], -16), ([0,3,14], -16), ([0,4,14], -16), ([0,5,14], -16), ([0,6,14], -16), ([0,7,14], -16), ([0,8,14], -16), ([0,9,14], -16), ([0,10,14], -16), ([0,11,14], -16), ([0,12,14], -16), ([0,13,14], -16), ([0,14,14], -16), ([0,14,15], -14), ([0,14,16], -10), ([0,14,17], -2), ([0,14,18], 2), ([0,14,19], 10), ([0,14,20], 18)]
theorem atom0130_data : atom0130 = SparsePolynomial.monoTimes [0,14] 1 base07 := by decide +kernel
theorem eval_atom0130 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0130 = (quadB (outer g) ![2,2,1] * g 0 * g 14) := by
  rw [atom0130_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0130_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (379098014400 : Int) atom0130) := by
  rw [SparsePolynomial.eval_scale, eval_atom0130]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0130Coded : CoefficientMerge.Poly := [(14, -8), (35, -12), (56, -16), (77, -16), (98, -16), (119, -16), (140, -16), (161, -16), (182, -16), (203, -16), (224, -16), (245, -16), (266, -16), (287, -16), (308, -16), (309, -14), (310, -10), (311, -2), (312, 2), (313, 10), (314, 18)]
theorem atom0130Coded_decode : atom0130 = SparsePolynomial.decodeCubic 21 atom0130Coded := by decide +kernel
theorem atom0130Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (379098014400 : Int) atom0130Coded) := by
  have h := atom0130_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0130Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0131 : SparsePolynomial.Poly := [([0,0,19], -8), ([0,1,19], -12), ([0,2,19], -16), ([0,3,19], -16), ([0,4,19], -16), ([0,5,19], -16), ([0,6,19], -16), ([0,7,19], -16), ([0,8,19], -16), ([0,9,19], -16), ([0,10,19], -16), ([0,11,19], -16), ([0,12,19], -16), ([0,13,19], -16), ([0,14,19], -16), ([0,15,19], -14), ([0,16,19], -10), ([0,17,19], -2), ([0,18,19], 2), ([0,19,19], 10), ([0,19,20], 18)]
theorem atom0131_data : atom0131 = SparsePolynomial.monoTimes [0,19] 1 base07 := by decide +kernel
theorem eval_atom0131 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0131 = (quadB (outer g) ![2,2,1] * g 0 * g 19) := by
  rw [atom0131_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0131_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (130231886400 : Int) atom0131) := by
  rw [SparsePolynomial.eval_scale, eval_atom0131]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg19 : 0 ≤ g 19 := hg 19
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 0 * g 19) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0131Coded : CoefficientMerge.Poly := [(19, -8), (40, -12), (61, -16), (82, -16), (103, -16), (124, -16), (145, -16), (166, -16), (187, -16), (208, -16), (229, -16), (250, -16), (271, -16), (292, -16), (313, -16), (334, -14), (355, -10), (376, -2), (397, 2), (418, 10), (419, 18)]
theorem atom0131Coded_decode : atom0131 = SparsePolynomial.decodeCubic 21 atom0131Coded := by decide +kernel
theorem atom0131Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (130231886400 : Int) atom0131Coded) := by
  have h := atom0131_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0131Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0132 : SparsePolynomial.Poly := [([0,1,1], -8), ([1,1,1], -12), ([1,1,2], -16), ([1,1,3], -16), ([1,1,4], -16), ([1,1,5], -16), ([1,1,6], -16), ([1,1,7], -16), ([1,1,8], -16), ([1,1,9], -16), ([1,1,10], -16), ([1,1,11], -16), ([1,1,12], -16), ([1,1,13], -16), ([1,1,14], -16), ([1,1,15], -14), ([1,1,16], -10), ([1,1,17], -2), ([1,1,18], 2), ([1,1,19], 10), ([1,1,20], 18)]
theorem atom0132_data : atom0132 = SparsePolynomial.monoTimes [1,1] 1 base07 := by decide +kernel
theorem eval_atom0132 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0132 = (quadB (outer g) ![2,2,1] * g 1 * g 1) := by
  rw [atom0132_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0132_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (151735852800 : Int) atom0132) := by
  rw [SparsePolynomial.eval_scale, eval_atom0132]
  have hg1 : 0 ≤ g 1 := hg 1
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 1) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0132Coded : CoefficientMerge.Poly := [(22, -8), (463, -12), (464, -16), (465, -16), (466, -16), (467, -16), (468, -16), (469, -16), (470, -16), (471, -16), (472, -16), (473, -16), (474, -16), (475, -16), (476, -16), (477, -14), (478, -10), (479, -2), (480, 2), (481, 10), (482, 18)]
theorem atom0132Coded_decode : atom0132 = SparsePolynomial.decodeCubic 21 atom0132Coded := by decide +kernel
theorem atom0132Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (151735852800 : Int) atom0132Coded) := by
  have h := atom0132_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0132Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0133 : SparsePolynomial.Poly := [([0,1,20], -8), ([1,1,20], -12), ([1,2,20], -16), ([1,3,20], -16), ([1,4,20], -16), ([1,5,20], -16), ([1,6,20], -16), ([1,7,20], -16), ([1,8,20], -16), ([1,9,20], -16), ([1,10,20], -16), ([1,11,20], -16), ([1,12,20], -16), ([1,13,20], -16), ([1,14,20], -16), ([1,15,20], -14), ([1,16,20], -10), ([1,17,20], -2), ([1,18,20], 2), ([1,19,20], 10), ([1,20,20], 18)]
theorem atom0133_data : atom0133 = SparsePolynomial.monoTimes [1,20] 1 base07 := by decide +kernel
theorem eval_atom0133 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0133 = (quadB (outer g) ![2,2,1] * g 1 * g 20) := by
  rw [atom0133_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0133_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (159185728800 : Int) atom0133) := by
  rw [SparsePolynomial.eval_scale, eval_atom0133]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 1 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0133Coded : CoefficientMerge.Poly := [(41, -8), (482, -12), (503, -16), (524, -16), (545, -16), (566, -16), (587, -16), (608, -16), (629, -16), (650, -16), (671, -16), (692, -16), (713, -16), (734, -16), (755, -16), (776, -14), (797, -10), (818, -2), (839, 2), (860, 10), (881, 18)]
theorem atom0133Coded_decode : atom0133 = SparsePolynomial.decodeCubic 21 atom0133Coded := by decide +kernel
theorem atom0133Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (159185728800 : Int) atom0133Coded) := by
  have h := atom0133_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0133Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0134 : SparsePolynomial.Poly := [([0,2,20], -8), ([1,2,20], -12), ([2,2,20], -16), ([2,3,20], -16), ([2,4,20], -16), ([2,5,20], -16), ([2,6,20], -16), ([2,7,20], -16), ([2,8,20], -16), ([2,9,20], -16), ([2,10,20], -16), ([2,11,20], -16), ([2,12,20], -16), ([2,13,20], -16), ([2,14,20], -16), ([2,15,20], -14), ([2,16,20], -10), ([2,17,20], -2), ([2,18,20], 2), ([2,19,20], 10), ([2,20,20], 18)]
theorem atom0134_data : atom0134 = SparsePolynomial.monoTimes [2,20] 1 base07 := by decide +kernel
theorem eval_atom0134 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0134 = (quadB (outer g) ![2,2,1] * g 2 * g 20) := by
  rw [atom0134_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0134_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (188220110400 : Int) atom0134) := by
  rw [SparsePolynomial.eval_scale, eval_atom0134]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg20 : 0 ≤ g 20 := hg 20
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 2 * g 20) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0134Coded : CoefficientMerge.Poly := [(62, -8), (503, -12), (944, -16), (965, -16), (986, -16), (1007, -16), (1028, -16), (1049, -16), (1070, -16), (1091, -16), (1112, -16), (1133, -16), (1154, -16), (1175, -16), (1196, -16), (1217, -14), (1238, -10), (1259, -2), (1280, 2), (1301, 10), (1322, 18)]
theorem atom0134Coded_decode : atom0134 = SparsePolynomial.decodeCubic 21 atom0134Coded := by decide +kernel
theorem atom0134Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (188220110400 : Int) atom0134Coded) := by
  have h := atom0134_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0134Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0135 : SparsePolynomial.Poly := [([0,4,4], -8), ([1,4,4], -12), ([2,4,4], -16), ([3,4,4], -16), ([4,4,4], -16), ([4,4,5], -16), ([4,4,6], -16), ([4,4,7], -16), ([4,4,8], -16), ([4,4,9], -16), ([4,4,10], -16), ([4,4,11], -16), ([4,4,12], -16), ([4,4,13], -16), ([4,4,14], -16), ([4,4,15], -14), ([4,4,16], -10), ([4,4,17], -2), ([4,4,18], 2), ([4,4,19], 10), ([4,4,20], 18)]
theorem atom0135_data : atom0135 = SparsePolynomial.monoTimes [4,4] 1 base07 := by decide +kernel
theorem eval_atom0135 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0135 = (quadB (outer g) ![2,2,1] * g 4 * g 4) := by
  rw [atom0135_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0135_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32234743800 : Int) atom0135) := by
  rw [SparsePolynomial.eval_scale, eval_atom0135]
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 4 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0135Coded : CoefficientMerge.Poly := [(88, -8), (529, -12), (970, -16), (1411, -16), (1852, -16), (1853, -16), (1854, -16), (1855, -16), (1856, -16), (1857, -16), (1858, -16), (1859, -16), (1860, -16), (1861, -16), (1862, -16), (1863, -14), (1864, -10), (1865, -2), (1866, 2), (1867, 10), (1868, 18)]
theorem atom0135Coded_decode : atom0135 = SparsePolynomial.decodeCubic 21 atom0135Coded := by decide +kernel
theorem atom0135Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32234743800 : Int) atom0135Coded) := by
  have h := atom0135_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0135Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0136 : SparsePolynomial.Poly := [([0,5,5], -8), ([1,5,5], -12), ([2,5,5], -16), ([3,5,5], -16), ([4,5,5], -16), ([5,5,5], -16), ([5,5,6], -16), ([5,5,7], -16), ([5,5,8], -16), ([5,5,9], -16), ([5,5,10], -16), ([5,5,11], -16), ([5,5,12], -16), ([5,5,13], -16), ([5,5,14], -16), ([5,5,15], -14), ([5,5,16], -10), ([5,5,17], -2), ([5,5,18], 2), ([5,5,19], 10), ([5,5,20], 18)]
theorem atom0136_data : atom0136 = SparsePolynomial.monoTimes [5,5] 1 base07 := by decide +kernel
theorem eval_atom0136 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0136 = (quadB (outer g) ![2,2,1] * g 5 * g 5) := by
  rw [atom0136_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0136_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68482848960 : Int) atom0136) := by
  rw [SparsePolynomial.eval_scale, eval_atom0136]
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 5 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0136Coded : CoefficientMerge.Poly := [(110, -8), (551, -12), (992, -16), (1433, -16), (1874, -16), (2315, -16), (2316, -16), (2317, -16), (2318, -16), (2319, -16), (2320, -16), (2321, -16), (2322, -16), (2323, -16), (2324, -16), (2325, -14), (2326, -10), (2327, -2), (2328, 2), (2329, 10), (2330, 18)]
theorem atom0136Coded_decode : atom0136 = SparsePolynomial.decodeCubic 21 atom0136Coded := by decide +kernel
theorem atom0136Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (68482848960 : Int) atom0136Coded) := by
  have h := atom0136_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0136Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0137 : SparsePolynomial.Poly := [([0,5,6], -8), ([1,5,6], -12), ([2,5,6], -16), ([3,5,6], -16), ([4,5,6], -16), ([5,5,6], -16), ([5,6,6], -16), ([5,6,7], -16), ([5,6,8], -16), ([5,6,9], -16), ([5,6,10], -16), ([5,6,11], -16), ([5,6,12], -16), ([5,6,13], -16), ([5,6,14], -16), ([5,6,15], -14), ([5,6,16], -10), ([5,6,17], -2), ([5,6,18], 2), ([5,6,19], 10), ([5,6,20], 18)]
theorem atom0137_data : atom0137 = SparsePolynomial.monoTimes [5,6] 1 base07 := by decide +kernel
theorem eval_atom0137 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0137 = (quadB (outer g) ![2,2,1] * g 5 * g 6) := by
  rw [atom0137_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0137_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34806427776 : Int) atom0137) := by
  rw [SparsePolynomial.eval_scale, eval_atom0137]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 5 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0137Coded : CoefficientMerge.Poly := [(111, -8), (552, -12), (993, -16), (1434, -16), (1875, -16), (2316, -16), (2337, -16), (2338, -16), (2339, -16), (2340, -16), (2341, -16), (2342, -16), (2343, -16), (2344, -16), (2345, -16), (2346, -14), (2347, -10), (2348, -2), (2349, 2), (2350, 10), (2351, 18)]
theorem atom0137Coded_decode : atom0137 = SparsePolynomial.decodeCubic 21 atom0137Coded := by decide +kernel
theorem atom0137Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34806427776 : Int) atom0137Coded) := by
  have h := atom0137_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0137Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0138 : SparsePolynomial.Poly := [([0,6,7], -8), ([1,6,7], -12), ([2,6,7], -16), ([3,6,7], -16), ([4,6,7], -16), ([5,6,7], -16), ([6,6,7], -16), ([6,7,7], -16), ([6,7,8], -16), ([6,7,9], -16), ([6,7,10], -16), ([6,7,11], -16), ([6,7,12], -16), ([6,7,13], -16), ([6,7,14], -16), ([6,7,15], -14), ([6,7,16], -10), ([6,7,17], -2), ([6,7,18], 2), ([6,7,19], 10), ([6,7,20], 18)]
theorem atom0138_data : atom0138 = SparsePolynomial.monoTimes [6,7] 1 base07 := by decide +kernel
theorem eval_atom0138 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0138 = (quadB (outer g) ![2,2,1] * g 6 * g 7) := by
  rw [atom0138_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0138_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (278634473856 : Int) atom0138) := by
  rw [SparsePolynomial.eval_scale, eval_atom0138]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 6 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0138Coded : CoefficientMerge.Poly := [(133, -8), (574, -12), (1015, -16), (1456, -16), (1897, -16), (2338, -16), (2779, -16), (2800, -16), (2801, -16), (2802, -16), (2803, -16), (2804, -16), (2805, -16), (2806, -16), (2807, -16), (2808, -14), (2809, -10), (2810, -2), (2811, 2), (2812, 10), (2813, 18)]
theorem atom0138Coded_decode : atom0138 = SparsePolynomial.decodeCubic 21 atom0138Coded := by decide +kernel
theorem atom0138Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (278634473856 : Int) atom0138Coded) := by
  have h := atom0138_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0138Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0139 : SparsePolynomial.Poly := [([0,7,7], -8), ([1,7,7], -12), ([2,7,7], -16), ([3,7,7], -16), ([4,7,7], -16), ([5,7,7], -16), ([6,7,7], -16), ([7,7,7], -16), ([7,7,8], -16), ([7,7,9], -16), ([7,7,10], -16), ([7,7,11], -16), ([7,7,12], -16), ([7,7,13], -16), ([7,7,14], -16), ([7,7,15], -14), ([7,7,16], -10), ([7,7,17], -2), ([7,7,18], 2), ([7,7,19], 10), ([7,7,20], 18)]
theorem atom0139_data : atom0139 = SparsePolynomial.monoTimes [7,7] 1 base07 := by decide +kernel
theorem eval_atom0139 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0139 = (quadB (outer g) ![2,2,1] * g 7 * g 7) := by
  rw [atom0139_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0139_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (231712335936 : Int) atom0139) := by
  rw [SparsePolynomial.eval_scale, eval_atom0139]
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 7 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0139Coded : CoefficientMerge.Poly := [(154, -8), (595, -12), (1036, -16), (1477, -16), (1918, -16), (2359, -16), (2800, -16), (3241, -16), (3242, -16), (3243, -16), (3244, -16), (3245, -16), (3246, -16), (3247, -16), (3248, -16), (3249, -14), (3250, -10), (3251, -2), (3252, 2), (3253, 10), (3254, 18)]
theorem atom0139Coded_decode : atom0139 = SparsePolynomial.decodeCubic 21 atom0139Coded := by decide +kernel
theorem atom0139Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (231712335936 : Int) atom0139Coded) := by
  have h := atom0139_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0139Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0140 : SparsePolynomial.Poly := [([0,7,8], -8), ([1,7,8], -12), ([2,7,8], -16), ([3,7,8], -16), ([4,7,8], -16), ([5,7,8], -16), ([6,7,8], -16), ([7,7,8], -16), ([7,8,8], -16), ([7,8,9], -16), ([7,8,10], -16), ([7,8,11], -16), ([7,8,12], -16), ([7,8,13], -16), ([7,8,14], -16), ([7,8,15], -14), ([7,8,16], -10), ([7,8,17], -2), ([7,8,18], 2), ([7,8,19], 10), ([7,8,20], 18)]
theorem atom0140_data : atom0140 = SparsePolynomial.monoTimes [7,8] 1 base07 := by decide +kernel
theorem eval_atom0140 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0140 = (quadB (outer g) ![2,2,1] * g 7 * g 8) := by
  rw [atom0140_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0140_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (335369083176 : Int) atom0140) := by
  rw [SparsePolynomial.eval_scale, eval_atom0140]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 7 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0140Coded : CoefficientMerge.Poly := [(155, -8), (596, -12), (1037, -16), (1478, -16), (1919, -16), (2360, -16), (2801, -16), (3242, -16), (3263, -16), (3264, -16), (3265, -16), (3266, -16), (3267, -16), (3268, -16), (3269, -16), (3270, -14), (3271, -10), (3272, -2), (3273, 2), (3274, 10), (3275, 18)]
theorem atom0140Coded_decode : atom0140 = SparsePolynomial.decodeCubic 21 atom0140Coded := by decide +kernel
theorem atom0140Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (335369083176 : Int) atom0140Coded) := by
  have h := atom0140_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0140Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0141 : SparsePolynomial.Poly := [([0,8,8], -8), ([1,8,8], -12), ([2,8,8], -16), ([3,8,8], -16), ([4,8,8], -16), ([5,8,8], -16), ([6,8,8], -16), ([7,8,8], -16), ([8,8,8], -16), ([8,8,9], -16), ([8,8,10], -16), ([8,8,11], -16), ([8,8,12], -16), ([8,8,13], -16), ([8,8,14], -16), ([8,8,15], -14), ([8,8,16], -10), ([8,8,17], -2), ([8,8,18], 2), ([8,8,19], 10), ([8,8,20], 18)]
theorem atom0141_data : atom0141 = SparsePolynomial.monoTimes [8,8] 1 base07 := by decide +kernel
theorem eval_atom0141 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0141 = (quadB (outer g) ![2,2,1] * g 8 * g 8) := by
  rw [atom0141_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0141_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (380934243900 : Int) atom0141) := by
  rw [SparsePolynomial.eval_scale, eval_atom0141]
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 8 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0141Coded : CoefficientMerge.Poly := [(176, -8), (617, -12), (1058, -16), (1499, -16), (1940, -16), (2381, -16), (2822, -16), (3263, -16), (3704, -16), (3705, -16), (3706, -16), (3707, -16), (3708, -16), (3709, -16), (3710, -16), (3711, -14), (3712, -10), (3713, -2), (3714, 2), (3715, 10), (3716, 18)]
theorem atom0141Coded_decode : atom0141 = SparsePolynomial.decodeCubic 21 atom0141Coded := by decide +kernel
theorem atom0141Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (380934243900 : Int) atom0141Coded) := by
  have h := atom0141_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0141Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0142 : SparsePolynomial.Poly := [([0,8,9], -8), ([1,8,9], -12), ([2,8,9], -16), ([3,8,9], -16), ([4,8,9], -16), ([5,8,9], -16), ([6,8,9], -16), ([7,8,9], -16), ([8,8,9], -16), ([8,9,9], -16), ([8,9,10], -16), ([8,9,11], -16), ([8,9,12], -16), ([8,9,13], -16), ([8,9,14], -16), ([8,9,15], -14), ([8,9,16], -10), ([8,9,17], -2), ([8,9,18], 2), ([8,9,19], 10), ([8,9,20], 18)]
theorem atom0142_data : atom0142 = SparsePolynomial.monoTimes [8,9] 1 base07 := by decide +kernel
theorem eval_atom0142 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0142 = (quadB (outer g) ![2,2,1] * g 8 * g 9) := by
  rw [atom0142_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0142_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (488307156120 : Int) atom0142) := by
  rw [SparsePolynomial.eval_scale, eval_atom0142]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 8 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0142Coded : CoefficientMerge.Poly := [(177, -8), (618, -12), (1059, -16), (1500, -16), (1941, -16), (2382, -16), (2823, -16), (3264, -16), (3705, -16), (3726, -16), (3727, -16), (3728, -16), (3729, -16), (3730, -16), (3731, -16), (3732, -14), (3733, -10), (3734, -2), (3735, 2), (3736, 10), (3737, 18)]
theorem atom0142Coded_decode : atom0142 = SparsePolynomial.decodeCubic 21 atom0142Coded := by decide +kernel
theorem atom0142Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (488307156120 : Int) atom0142Coded) := by
  have h := atom0142_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0142Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0143 : SparsePolynomial.Poly := [([0,9,9], -8), ([1,9,9], -12), ([2,9,9], -16), ([3,9,9], -16), ([4,9,9], -16), ([5,9,9], -16), ([6,9,9], -16), ([7,9,9], -16), ([8,9,9], -16), ([9,9,9], -16), ([9,9,10], -16), ([9,9,11], -16), ([9,9,12], -16), ([9,9,13], -16), ([9,9,14], -16), ([9,9,15], -14), ([9,9,16], -10), ([9,9,17], -2), ([9,9,18], 2), ([9,9,19], 10), ([9,9,20], 18)]
theorem atom0143_data : atom0143 = SparsePolynomial.monoTimes [9,9] 1 base07 := by decide +kernel
theorem eval_atom0143 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0143 = (quadB (outer g) ![2,2,1] * g 9 * g 9) := by
  rw [atom0143_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0143_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (697449337200 : Int) atom0143) := by
  rw [SparsePolynomial.eval_scale, eval_atom0143]
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 9 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0143Coded : CoefficientMerge.Poly := [(198, -8), (639, -12), (1080, -16), (1521, -16), (1962, -16), (2403, -16), (2844, -16), (3285, -16), (3726, -16), (4167, -16), (4168, -16), (4169, -16), (4170, -16), (4171, -16), (4172, -16), (4173, -14), (4174, -10), (4175, -2), (4176, 2), (4177, 10), (4178, 18)]
theorem atom0143Coded_decode : atom0143 = SparsePolynomial.decodeCubic 21 atom0143Coded := by decide +kernel
theorem atom0143Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (697449337200 : Int) atom0143Coded) := by
  have h := atom0143_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0143Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0144 : SparsePolynomial.Poly := [([0,9,10], -8), ([1,9,10], -12), ([2,9,10], -16), ([3,9,10], -16), ([4,9,10], -16), ([5,9,10], -16), ([6,9,10], -16), ([7,9,10], -16), ([8,9,10], -16), ([9,9,10], -16), ([9,10,10], -16), ([9,10,11], -16), ([9,10,12], -16), ([9,10,13], -16), ([9,10,14], -16), ([9,10,15], -14), ([9,10,16], -10), ([9,10,17], -2), ([9,10,18], 2), ([9,10,19], 10), ([9,10,20], 18)]
theorem atom0144_data : atom0144 = SparsePolynomial.monoTimes [9,10] 1 base07 := by decide +kernel
theorem eval_atom0144 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0144 = (quadB (outer g) ![2,2,1] * g 9 * g 10) := by
  rw [atom0144_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0144_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (611260312320 : Int) atom0144) := by
  rw [SparsePolynomial.eval_scale, eval_atom0144]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 9 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0144Coded : CoefficientMerge.Poly := [(199, -8), (640, -12), (1081, -16), (1522, -16), (1963, -16), (2404, -16), (2845, -16), (3286, -16), (3727, -16), (4168, -16), (4189, -16), (4190, -16), (4191, -16), (4192, -16), (4193, -16), (4194, -14), (4195, -10), (4196, -2), (4197, 2), (4198, 10), (4199, 18)]
theorem atom0144Coded_decode : atom0144 = SparsePolynomial.decodeCubic 21 atom0144Coded := by decide +kernel
theorem atom0144Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (611260312320 : Int) atom0144Coded) := by
  have h := atom0144_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0144Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0145 : SparsePolynomial.Poly := [([0,10,10], -8), ([1,10,10], -12), ([2,10,10], -16), ([3,10,10], -16), ([4,10,10], -16), ([5,10,10], -16), ([6,10,10], -16), ([7,10,10], -16), ([8,10,10], -16), ([9,10,10], -16), ([10,10,10], -16), ([10,10,11], -16), ([10,10,12], -16), ([10,10,13], -16), ([10,10,14], -16), ([10,10,15], -14), ([10,10,16], -10), ([10,10,17], -2), ([10,10,18], 2), ([10,10,19], 10), ([10,10,20], 18)]
theorem atom0145_data : atom0145 = SparsePolynomial.monoTimes [10,10] 1 base07 := by decide +kernel
theorem eval_atom0145 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0145 = (quadB (outer g) ![2,2,1] * g 10 * g 10) := by
  rw [atom0145_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0145_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (742269402000 : Int) atom0145) := by
  rw [SparsePolynomial.eval_scale, eval_atom0145]
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 10 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0145Coded : CoefficientMerge.Poly := [(220, -8), (661, -12), (1102, -16), (1543, -16), (1984, -16), (2425, -16), (2866, -16), (3307, -16), (3748, -16), (4189, -16), (4630, -16), (4631, -16), (4632, -16), (4633, -16), (4634, -16), (4635, -14), (4636, -10), (4637, -2), (4638, 2), (4639, 10), (4640, 18)]
theorem atom0145Coded_decode : atom0145 = SparsePolynomial.decodeCubic 21 atom0145Coded := by decide +kernel
theorem atom0145Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (742269402000 : Int) atom0145Coded) := by
  have h := atom0145_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0145Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0146 : SparsePolynomial.Poly := [([0,10,11], -8), ([1,10,11], -12), ([2,10,11], -16), ([3,10,11], -16), ([4,10,11], -16), ([5,10,11], -16), ([6,10,11], -16), ([7,10,11], -16), ([8,10,11], -16), ([9,10,11], -16), ([10,10,11], -16), ([10,11,11], -16), ([10,11,12], -16), ([10,11,13], -16), ([10,11,14], -16), ([10,11,15], -14), ([10,11,16], -10), ([10,11,17], -2), ([10,11,18], 2), ([10,11,19], 10), ([10,11,20], 18)]
theorem atom0146_data : atom0146 = SparsePolynomial.monoTimes [10,11] 1 base07 := by decide +kernel
theorem eval_atom0146 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0146 = (quadB (outer g) ![2,2,1] * g 10 * g 11) := by
  rw [atom0146_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0146_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (690133061520 : Int) atom0146) := by
  rw [SparsePolynomial.eval_scale, eval_atom0146]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 10 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0146Coded : CoefficientMerge.Poly := [(221, -8), (662, -12), (1103, -16), (1544, -16), (1985, -16), (2426, -16), (2867, -16), (3308, -16), (3749, -16), (4190, -16), (4631, -16), (4652, -16), (4653, -16), (4654, -16), (4655, -16), (4656, -14), (4657, -10), (4658, -2), (4659, 2), (4660, 10), (4661, 18)]
theorem atom0146Coded_decode : atom0146 = SparsePolynomial.decodeCubic 21 atom0146Coded := by decide +kernel
theorem atom0146Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (690133061520 : Int) atom0146Coded) := by
  have h := atom0146_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0146Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0147 : SparsePolynomial.Poly := [([0,10,12], -8), ([1,10,12], -12), ([2,10,12], -16), ([3,10,12], -16), ([4,10,12], -16), ([5,10,12], -16), ([6,10,12], -16), ([7,10,12], -16), ([8,10,12], -16), ([9,10,12], -16), ([10,10,12], -16), ([10,11,12], -16), ([10,12,12], -16), ([10,12,13], -16), ([10,12,14], -16), ([10,12,15], -14), ([10,12,16], -10), ([10,12,17], -2), ([10,12,18], 2), ([10,12,19], 10), ([10,12,20], 18)]
theorem atom0147_data : atom0147 = SparsePolynomial.monoTimes [10,12] 1 base07 := by decide +kernel
theorem eval_atom0147 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0147 = (quadB (outer g) ![2,2,1] * g 10 * g 12) := by
  rw [atom0147_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0147_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11030738320 : Int) atom0147) := by
  rw [SparsePolynomial.eval_scale, eval_atom0147]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 10 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0147Coded : CoefficientMerge.Poly := [(222, -8), (663, -12), (1104, -16), (1545, -16), (1986, -16), (2427, -16), (2868, -16), (3309, -16), (3750, -16), (4191, -16), (4632, -16), (4653, -16), (4674, -16), (4675, -16), (4676, -16), (4677, -14), (4678, -10), (4679, -2), (4680, 2), (4681, 10), (4682, 18)]
theorem atom0147Coded_decode : atom0147 = SparsePolynomial.decodeCubic 21 atom0147Coded := by decide +kernel
theorem atom0147Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11030738320 : Int) atom0147Coded) := by
  have h := atom0147_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0147Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0148 : SparsePolynomial.Poly := [([0,11,11], -8), ([1,11,11], -12), ([2,11,11], -16), ([3,11,11], -16), ([4,11,11], -16), ([5,11,11], -16), ([6,11,11], -16), ([7,11,11], -16), ([8,11,11], -16), ([9,11,11], -16), ([10,11,11], -16), ([11,11,11], -16), ([11,11,12], -16), ([11,11,13], -16), ([11,11,14], -16), ([11,11,15], -14), ([11,11,16], -10), ([11,11,17], -2), ([11,11,18], 2), ([11,11,19], 10), ([11,11,20], 18)]
theorem atom0148_data : atom0148 = SparsePolynomial.monoTimes [11,11] 1 base07 := by decide +kernel
theorem eval_atom0148 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0148 = (quadB (outer g) ![2,2,1] * g 11 * g 11) := by
  rw [atom0148_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0148_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (776322086400 : Int) atom0148) := by
  rw [SparsePolynomial.eval_scale, eval_atom0148]
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0148Coded : CoefficientMerge.Poly := [(242, -8), (683, -12), (1124, -16), (1565, -16), (2006, -16), (2447, -16), (2888, -16), (3329, -16), (3770, -16), (4211, -16), (4652, -16), (5093, -16), (5094, -16), (5095, -16), (5096, -16), (5097, -14), (5098, -10), (5099, -2), (5100, 2), (5101, 10), (5102, 18)]
theorem atom0148Coded_decode : atom0148 = SparsePolynomial.decodeCubic 21 atom0148Coded := by decide +kernel
theorem atom0148Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (776322086400 : Int) atom0148Coded) := by
  have h := atom0148_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0148Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0149 : SparsePolynomial.Poly := [([0,11,12], -8), ([1,11,12], -12), ([2,11,12], -16), ([3,11,12], -16), ([4,11,12], -16), ([5,11,12], -16), ([6,11,12], -16), ([7,11,12], -16), ([8,11,12], -16), ([9,11,12], -16), ([10,11,12], -16), ([11,11,12], -16), ([11,12,12], -16), ([11,12,13], -16), ([11,12,14], -16), ([11,12,15], -14), ([11,12,16], -10), ([11,12,17], -2), ([11,12,18], 2), ([11,12,19], 10), ([11,12,20], 18)]
theorem atom0149_data : atom0149 = SparsePolynomial.monoTimes [11,12] 1 base07 := by decide +kernel
theorem eval_atom0149 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0149 = (quadB (outer g) ![2,2,1] * g 11 * g 12) := by
  rw [atom0149_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0149_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (792165041920 : Int) atom0149) := by
  rw [SparsePolynomial.eval_scale, eval_atom0149]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0149Coded : CoefficientMerge.Poly := [(243, -8), (684, -12), (1125, -16), (1566, -16), (2007, -16), (2448, -16), (2889, -16), (3330, -16), (3771, -16), (4212, -16), (4653, -16), (5094, -16), (5115, -16), (5116, -16), (5117, -16), (5118, -14), (5119, -10), (5120, -2), (5121, 2), (5122, 10), (5123, 18)]
theorem atom0149Coded_decode : atom0149 = SparsePolynomial.decodeCubic 21 atom0149Coded := by decide +kernel
theorem atom0149Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (792165041920 : Int) atom0149Coded) := by
  have h := atom0149_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0149Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0150 : SparsePolynomial.Poly := [([0,12,12], -8), ([1,12,12], -12), ([2,12,12], -16), ([3,12,12], -16), ([4,12,12], -16), ([5,12,12], -16), ([6,12,12], -16), ([7,12,12], -16), ([8,12,12], -16), ([9,12,12], -16), ([10,12,12], -16), ([11,12,12], -16), ([12,12,12], -16), ([12,12,13], -16), ([12,12,14], -16), ([12,12,15], -14), ([12,12,16], -10), ([12,12,17], -2), ([12,12,18], 2), ([12,12,19], 10), ([12,12,20], 18)]
theorem atom0150_data : atom0150 = SparsePolynomial.monoTimes [12,12] 1 base07 := by decide +kernel
theorem eval_atom0150 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0150 = (quadB (outer g) ![2,2,1] * g 12 * g 12) := by
  rw [atom0150_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0150_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (844301382400 : Int) atom0150) := by
  rw [SparsePolynomial.eval_scale, eval_atom0150]
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 12 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0150Coded : CoefficientMerge.Poly := [(264, -8), (705, -12), (1146, -16), (1587, -16), (2028, -16), (2469, -16), (2910, -16), (3351, -16), (3792, -16), (4233, -16), (4674, -16), (5115, -16), (5556, -16), (5557, -16), (5558, -16), (5559, -14), (5560, -10), (5561, -2), (5562, 2), (5563, 10), (5564, 18)]
theorem atom0150Coded_decode : atom0150 = SparsePolynomial.decodeCubic 21 atom0150Coded := by decide +kernel
theorem atom0150Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (844301382400 : Int) atom0150Coded) := by
  have h := atom0150_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0150Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0151 : SparsePolynomial.Poly := [([0,12,13], -8), ([1,12,13], -12), ([2,12,13], -16), ([3,12,13], -16), ([4,12,13], -16), ([5,12,13], -16), ([6,12,13], -16), ([7,12,13], -16), ([8,12,13], -16), ([9,12,13], -16), ([10,12,13], -16), ([11,12,13], -16), ([12,12,13], -16), ([12,13,13], -16), ([12,13,14], -16), ([12,13,15], -14), ([12,13,16], -10), ([12,13,17], -2), ([12,13,18], 2), ([12,13,19], 10), ([12,13,20], 18)]
theorem atom0151_data : atom0151 = SparsePolynomial.monoTimes [12,13] 1 base07 := by decide +kernel
theorem eval_atom0151 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0151 = (quadB (outer g) ![2,2,1] * g 12 * g 13) := by
  rw [atom0151_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0151_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (870328967200 : Int) atom0151) := by
  rw [SparsePolynomial.eval_scale, eval_atom0151]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 12 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0151Coded : CoefficientMerge.Poly := [(265, -8), (706, -12), (1147, -16), (1588, -16), (2029, -16), (2470, -16), (2911, -16), (3352, -16), (3793, -16), (4234, -16), (4675, -16), (5116, -16), (5557, -16), (5578, -16), (5579, -16), (5580, -14), (5581, -10), (5582, -2), (5583, 2), (5584, 10), (5585, 18)]
theorem atom0151Coded_decode : atom0151 = SparsePolynomial.decodeCubic 21 atom0151Coded := by decide +kernel
theorem atom0151Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (870328967200 : Int) atom0151Coded) := by
  have h := atom0151_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0151Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0152 : SparsePolynomial.Poly := [([0,12,14], -8), ([1,12,14], -12), ([2,12,14], -16), ([3,12,14], -16), ([4,12,14], -16), ([5,12,14], -16), ([6,12,14], -16), ([7,12,14], -16), ([8,12,14], -16), ([9,12,14], -16), ([10,12,14], -16), ([11,12,14], -16), ([12,12,14], -16), ([12,13,14], -16), ([12,14,14], -16), ([12,14,15], -14), ([12,14,16], -10), ([12,14,17], -2), ([12,14,18], 2), ([12,14,19], 10), ([12,14,20], 18)]
theorem atom0152_data : atom0152 = SparsePolynomial.monoTimes [12,14] 1 base07 := by decide +kernel
theorem eval_atom0152 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0152 = (quadB (outer g) ![2,2,1] * g 12 * g 14) := by
  rw [atom0152_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0152_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35097193600 : Int) atom0152) := by
  rw [SparsePolynomial.eval_scale, eval_atom0152]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 12 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0152Coded : CoefficientMerge.Poly := [(266, -8), (707, -12), (1148, -16), (1589, -16), (2030, -16), (2471, -16), (2912, -16), (3353, -16), (3794, -16), (4235, -16), (4676, -16), (5117, -16), (5558, -16), (5579, -16), (5600, -16), (5601, -14), (5602, -10), (5603, -2), (5604, 2), (5605, 10), (5606, 18)]
theorem atom0152Coded_decode : atom0152 = SparsePolynomial.decodeCubic 21 atom0152Coded := by decide +kernel
theorem atom0152Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35097193600 : Int) atom0152Coded) := by
  have h := atom0152_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0152Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0153 : SparsePolynomial.Poly := [([0,13,13], -8), ([1,13,13], -12), ([2,13,13], -16), ([3,13,13], -16), ([4,13,13], -16), ([5,13,13], -16), ([6,13,13], -16), ([7,13,13], -16), ([8,13,13], -16), ([9,13,13], -16), ([10,13,13], -16), ([11,13,13], -16), ([12,13,13], -16), ([13,13,13], -16), ([13,13,14], -16), ([13,13,15], -14), ([13,13,16], -10), ([13,13,17], -2), ([13,13,18], 2), ([13,13,19], 10), ([13,13,20], 18)]
theorem atom0153_data : atom0153 = SparsePolynomial.monoTimes [13,13] 1 base07 := by decide +kernel
theorem eval_atom0153 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0153 = (quadB (outer g) ![2,2,1] * g 13 * g 13) := by
  rw [atom0153_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0153_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (776300090400 : Int) atom0153) := by
  rw [SparsePolynomial.eval_scale, eval_atom0153]
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 13 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0153Coded : CoefficientMerge.Poly := [(286, -8), (727, -12), (1168, -16), (1609, -16), (2050, -16), (2491, -16), (2932, -16), (3373, -16), (3814, -16), (4255, -16), (4696, -16), (5137, -16), (5578, -16), (6019, -16), (6020, -16), (6021, -14), (6022, -10), (6023, -2), (6024, 2), (6025, 10), (6026, 18)]
theorem atom0153Coded_decode : atom0153 = SparsePolynomial.decodeCubic 21 atom0153Coded := by decide +kernel
theorem atom0153Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (776300090400 : Int) atom0153Coded) := by
  have h := atom0153_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0153Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0154 : SparsePolynomial.Poly := [([0,13,14], -8), ([1,13,14], -12), ([2,13,14], -16), ([3,13,14], -16), ([4,13,14], -16), ([5,13,14], -16), ([6,13,14], -16), ([7,13,14], -16), ([8,13,14], -16), ([9,13,14], -16), ([10,13,14], -16), ([11,13,14], -16), ([12,13,14], -16), ([13,13,14], -16), ([13,14,14], -16), ([13,14,15], -14), ([13,14,16], -10), ([13,14,17], -2), ([13,14,18], 2), ([13,14,19], 10), ([13,14,20], 18)]
theorem atom0154_data : atom0154 = SparsePolynomial.monoTimes [13,14] 1 base07 := by decide +kernel
theorem eval_atom0154 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0154 = (quadB (outer g) ![2,2,1] * g 13 * g 14) := by
  rw [atom0154_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0154_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (853893856800 : Int) atom0154) := by
  rw [SparsePolynomial.eval_scale, eval_atom0154]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 13 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0154Coded : CoefficientMerge.Poly := [(287, -8), (728, -12), (1169, -16), (1610, -16), (2051, -16), (2492, -16), (2933, -16), (3374, -16), (3815, -16), (4256, -16), (4697, -16), (5138, -16), (5579, -16), (6020, -16), (6041, -16), (6042, -14), (6043, -10), (6044, -2), (6045, 2), (6046, 10), (6047, 18)]
theorem atom0154Coded_decode : atom0154 = SparsePolynomial.decodeCubic 21 atom0154Coded := by decide +kernel
theorem atom0154Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (853893856800 : Int) atom0154Coded) := by
  have h := atom0154_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0154Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0155 : SparsePolynomial.Poly := [([0,14,14], -8), ([1,14,14], -12), ([2,14,14], -16), ([3,14,14], -16), ([4,14,14], -16), ([5,14,14], -16), ([6,14,14], -16), ([7,14,14], -16), ([8,14,14], -16), ([9,14,14], -16), ([10,14,14], -16), ([11,14,14], -16), ([12,14,14], -16), ([13,14,14], -16), ([14,14,14], -16), ([14,14,15], -14), ([14,14,16], -10), ([14,14,17], -2), ([14,14,18], 2), ([14,14,19], 10), ([14,14,20], 18)]
theorem atom0155_data : atom0155 = SparsePolynomial.monoTimes [14,14] 1 base07 := by decide +kernel
theorem eval_atom0155 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0155 = (quadB (outer g) ![2,2,1] * g 14 * g 14) := by
  rw [atom0155_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0155_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (638836934400 : Int) atom0155) := by
  rw [SparsePolynomial.eval_scale, eval_atom0155]
  have hg14 : 0 ≤ g 14 := hg 14
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 14 * g 14) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0155Coded : CoefficientMerge.Poly := [(308, -8), (749, -12), (1190, -16), (1631, -16), (2072, -16), (2513, -16), (2954, -16), (3395, -16), (3836, -16), (4277, -16), (4718, -16), (5159, -16), (5600, -16), (6041, -16), (6482, -16), (6483, -14), (6484, -10), (6485, -2), (6486, 2), (6487, 10), (6488, 18)]
theorem atom0155Coded_decode : atom0155 = SparsePolynomial.decodeCubic 21 atom0155Coded := by decide +kernel
theorem atom0155Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (638836934400 : Int) atom0155Coded) := by
  have h := atom0155_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0155Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0156 : SparsePolynomial.Poly := [([0,16,16], -8), ([1,16,16], -12), ([2,16,16], -16), ([3,16,16], -16), ([4,16,16], -16), ([5,16,16], -16), ([6,16,16], -16), ([7,16,16], -16), ([8,16,16], -16), ([9,16,16], -16), ([10,16,16], -16), ([11,16,16], -16), ([12,16,16], -16), ([13,16,16], -16), ([14,16,16], -16), ([15,16,16], -14), ([16,16,16], -10), ([16,16,17], -2), ([16,16,18], 2), ([16,16,19], 10), ([16,16,20], 18)]
theorem atom0156_data : atom0156 = SparsePolynomial.monoTimes [16,16] 1 base07 := by decide +kernel
theorem eval_atom0156 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0156 = (quadB (outer g) ![2,2,1] * g 16 * g 16) := by
  rw [atom0156_data, SparsePolynomial.eval_monoTimes, eval_base07]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0156_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153088911360 : Int) atom0156) := by
  rw [SparsePolynomial.eval_scale, eval_atom0156]
  have hg16 : 0 ≤ g 16 := hg 16
  have hb := base07_nonneg g hg hA hB
  rw [eval_base07] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 16 * g 16) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0156Coded : CoefficientMerge.Poly := [(352, -8), (793, -12), (1234, -16), (1675, -16), (2116, -16), (2557, -16), (2998, -16), (3439, -16), (3880, -16), (4321, -16), (4762, -16), (5203, -16), (5644, -16), (6085, -16), (6526, -16), (6967, -14), (7408, -10), (7409, -2), (7410, 2), (7411, 10), (7412, 18)]
theorem atom0156Coded_decode : atom0156 = SparsePolynomial.decodeCubic 21 atom0156Coded := by decide +kernel
theorem atom0156Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (153088911360 : Int) atom0156Coded) := by
  have h := atom0156_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0156Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0157 : SparsePolynomial.Poly := [([0,0,15], 1)]
theorem eval_atom0157 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0157 = ((g 0) * (g 0) * (g 15)) := by
  norm_num [atom0157, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0157_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1633334976000 : Int) atom0157) := by
  rw [SparsePolynomial.eval_scale, eval_atom0157]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 0) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0157Coded : CoefficientMerge.Poly := [(15, 1)]
theorem atom0157Coded_decode : atom0157 = SparsePolynomial.decodeCubic 21 atom0157Coded := by decide +kernel
theorem atom0157Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1633334976000 : Int) atom0157Coded) := by
  have h := atom0157_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0157Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0158 : SparsePolynomial.Poly := [([0,0,16], 1)]
theorem eval_atom0158 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0158 = ((g 0) * (g 0) * (g 16)) := by
  norm_num [atom0158, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0158_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1206155059200 : Int) atom0158) := by
  rw [SparsePolynomial.eval_scale, eval_atom0158]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 0) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0158Coded : CoefficientMerge.Poly := [(16, 1)]
theorem atom0158Coded_decode : atom0158 = SparsePolynomial.decodeCubic 21 atom0158Coded := by decide +kernel
theorem atom0158Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1206155059200 : Int) atom0158Coded) := by
  have h := atom0158_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0158Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0159 : SparsePolynomial.Poly := [([0,0,17], 1)]
theorem eval_atom0159 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0159 = ((g 0) * (g 0) * (g 17)) := by
  norm_num [atom0159, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0159_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (778975142400 : Int) atom0159) := by
  rw [SparsePolynomial.eval_scale, eval_atom0159]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 0) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0159Coded : CoefficientMerge.Poly := [(17, 1)]
theorem atom0159Coded_decode : atom0159 = SparsePolynomial.decodeCubic 21 atom0159Coded := by decide +kernel
theorem atom0159Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (778975142400 : Int) atom0159Coded) := by
  have h := atom0159_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0159Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0160 : SparsePolynomial.Poly := [([0,0,18], 1)]
theorem eval_atom0160 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0160 = ((g 0) * (g 0) * (g 18)) := by
  norm_num [atom0160, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0160_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (351795225600 : Int) atom0160) := by
  rw [SparsePolynomial.eval_scale, eval_atom0160]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 0) * (g 0) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0160Coded : CoefficientMerge.Poly := [(18, 1)]
theorem atom0160Coded_decode : atom0160 = SparsePolynomial.decodeCubic 21 atom0160Coded := by decide +kernel
theorem atom0160Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (351795225600 : Int) atom0160Coded) := by
  have h := atom0160_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0160Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0161 : SparsePolynomial.Poly := [([0,1,1], 1)]
theorem eval_atom0161 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0161 = ((g 0) * (g 1) * (g 1)) := by
  norm_num [atom0161, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0161_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (331499347200 : Int) atom0161) := by
  rw [SparsePolynomial.eval_scale, eval_atom0161]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have ht : 0 ≤ ((g 0) * (g 1) * (g 1)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0161Coded : CoefficientMerge.Poly := [(22, 1)]
theorem atom0161Coded_decode : atom0161 = SparsePolynomial.decodeCubic 21 atom0161Coded := by decide +kernel
theorem atom0161Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (331499347200 : Int) atom0161Coded) := by
  have h := atom0161_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0161Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0162 : SparsePolynomial.Poly := [([0,1,2], 1)]
theorem eval_atom0162 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0162 = ((g 0) * (g 1) * (g 2)) := by
  norm_num [atom0162, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0162_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7169277427200 : Int) atom0162) := by
  rw [SparsePolynomial.eval_scale, eval_atom0162]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0162Coded : CoefficientMerge.Poly := [(23, 1)]
theorem atom0162Coded_decode : atom0162 = SparsePolynomial.decodeCubic 21 atom0162Coded := by decide +kernel
theorem atom0162Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7169277427200 : Int) atom0162Coded) := by
  have h := atom0162_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0162Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0163 : SparsePolynomial.Poly := [([0,1,3], 1)]
theorem eval_atom0163 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0163 = ((g 0) * (g 1) * (g 3)) := by
  norm_num [atom0163, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0163_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7123853318400 : Int) atom0163) := by
  rw [SparsePolynomial.eval_scale, eval_atom0163]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0163Coded : CoefficientMerge.Poly := [(24, 1)]
theorem atom0163Coded_decode : atom0163 = SparsePolynomial.decodeCubic 21 atom0163Coded := by decide +kernel
theorem atom0163Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7123853318400 : Int) atom0163Coded) := by
  have h := atom0163_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0163Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0164 : SparsePolynomial.Poly := [([0,1,4], 1)]
theorem eval_atom0164 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0164 = ((g 0) * (g 1) * (g 4)) := by
  norm_num [atom0164, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0164_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7078429209600 : Int) atom0164) := by
  rw [SparsePolynomial.eval_scale, eval_atom0164]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0164Coded : CoefficientMerge.Poly := [(25, 1)]
theorem atom0164Coded_decode : atom0164 = SparsePolynomial.decodeCubic 21 atom0164Coded := by decide +kernel
theorem atom0164Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7078429209600 : Int) atom0164Coded) := by
  have h := atom0164_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0164Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0165 : SparsePolynomial.Poly := [([0,1,5], 1)]
theorem eval_atom0165 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0165 = ((g 0) * (g 1) * (g 5)) := by
  norm_num [atom0165, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0165_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7778694082176 : Int) atom0165) := by
  rw [SparsePolynomial.eval_scale, eval_atom0165]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0165Coded : CoefficientMerge.Poly := [(26, 1)]
theorem atom0165Coded_decode : atom0165 = SparsePolynomial.decodeCubic 21 atom0165Coded := by decide +kernel
theorem atom0165Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7778694082176 : Int) atom0165Coded) := by
  have h := atom0165_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0165Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0166 : SparsePolynomial.Poly := [([0,1,6], 1)]
theorem eval_atom0166 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0166 = ((g 0) * (g 1) * (g 6)) := by
  norm_num [atom0166, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0166_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7959932467200 : Int) atom0166) := by
  rw [SparsePolynomial.eval_scale, eval_atom0166]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0166Coded : CoefficientMerge.Poly := [(27, 1)]
theorem atom0166Coded_decode : atom0166 = SparsePolynomial.decodeCubic 21 atom0166Coded := by decide +kernel
theorem atom0166Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7959932467200 : Int) atom0166Coded) := by
  have h := atom0166_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0166Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0167 : SparsePolynomial.Poly := [([0,1,7], 1)]
theorem eval_atom0167 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0167 = ((g 0) * (g 1) * (g 7)) := by
  norm_num [atom0167, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0167_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8641406521152 : Int) atom0167) := by
  rw [SparsePolynomial.eval_scale, eval_atom0167]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 1) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0167Coded : CoefficientMerge.Poly := [(28, 1)]
theorem atom0167Coded_decode : atom0167 = SparsePolynomial.decodeCubic 21 atom0167Coded := by decide +kernel
theorem atom0167Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8641406521152 : Int) atom0167Coded) := by
  have h := atom0167_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0167Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0168 : SparsePolynomial.Poly := [([0,1,8], 1)]
theorem eval_atom0168 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0168 = ((g 0) * (g 1) * (g 8)) := by
  norm_num [atom0168, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0168_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8847070041600 : Int) atom0168) := by
  rw [SparsePolynomial.eval_scale, eval_atom0168]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 1) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0168Coded : CoefficientMerge.Poly := [(29, 1)]
theorem atom0168Coded_decode : atom0168 = SparsePolynomial.decodeCubic 21 atom0168Coded := by decide +kernel
theorem atom0168Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8847070041600 : Int) atom0168Coded) := by
  have h := atom0168_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0168Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0169 : SparsePolynomial.Poly := [([0,1,9], 1)]
theorem eval_atom0169 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0169 = ((g 0) * (g 1) * (g 9)) := by
  norm_num [atom0169, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0169_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9015235891200 : Int) atom0169) := by
  rw [SparsePolynomial.eval_scale, eval_atom0169]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 1) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0169Coded : CoefficientMerge.Poly := [(30, 1)]
theorem atom0169Coded_decode : atom0169 = SparsePolynomial.decodeCubic 21 atom0169Coded := by decide +kernel
theorem atom0169Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9015235891200 : Int) atom0169Coded) := by
  have h := atom0169_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0169Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0170 : SparsePolynomial.Poly := [([0,1,10], 1)]
theorem eval_atom0170 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0170 = ((g 0) * (g 1) * (g 10)) := by
  norm_num [atom0170, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0170_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9183401740800 : Int) atom0170) := by
  rw [SparsePolynomial.eval_scale, eval_atom0170]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 1) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0170Coded : CoefficientMerge.Poly := [(31, 1)]
theorem atom0170Coded_decode : atom0170 = SparsePolynomial.decodeCubic 21 atom0170Coded := by decide +kernel
theorem atom0170Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9183401740800 : Int) atom0170Coded) := by
  have h := atom0170_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0170Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0171 : SparsePolynomial.Poly := [([0,1,11], 1)]
theorem eval_atom0171 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0171 = ((g 0) * (g 1) * (g 11)) := by
  norm_num [atom0171, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0171_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9195605798400 : Int) atom0171) := by
  rw [SparsePolynomial.eval_scale, eval_atom0171]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 1) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0171Coded : CoefficientMerge.Poly := [(32, 1)]
theorem atom0171Coded_decode : atom0171 = SparsePolynomial.decodeCubic 21 atom0171Coded := by decide +kernel
theorem atom0171Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9195605798400 : Int) atom0171Coded) := by
  have h := atom0171_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0171Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0172 : SparsePolynomial.Poly := [([0,1,12], 1)]
theorem eval_atom0172 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0172 = ((g 0) * (g 1) * (g 12)) := by
  norm_num [atom0172, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0172_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8183033286400 : Int) atom0172) := by
  rw [SparsePolynomial.eval_scale, eval_atom0172]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 1) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0172Coded : CoefficientMerge.Poly := [(33, 1)]
theorem atom0172Coded_decode : atom0172 = SparsePolynomial.decodeCubic 21 atom0172Coded := by decide +kernel
theorem atom0172Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8183033286400 : Int) atom0172Coded) := by
  have h := atom0172_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0172Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0173 : SparsePolynomial.Poly := [([0,1,13], 1)]
theorem eval_atom0173 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0173 = ((g 0) * (g 1) * (g 13)) := by
  norm_num [atom0173, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0173_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8042000198400 : Int) atom0173) := by
  rw [SparsePolynomial.eval_scale, eval_atom0173]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 1) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0173Coded : CoefficientMerge.Poly := [(34, 1)]
theorem atom0173Coded_decode : atom0173 = SparsePolynomial.decodeCubic 21 atom0173Coded := by decide +kernel
theorem atom0173Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8042000198400 : Int) atom0173Coded) := by
  have h := atom0173_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0173Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0174 : SparsePolynomial.Poly := [([0,1,14], 1)]
theorem eval_atom0174 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0174 = ((g 0) * (g 1) * (g 14)) := by
  norm_num [atom0174, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0174_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8339673081600 : Int) atom0174) := by
  rw [SparsePolynomial.eval_scale, eval_atom0174]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 1) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0174Coded : CoefficientMerge.Poly := [(35, 1)]
theorem atom0174Coded_decode : atom0174 = SparsePolynomial.decodeCubic 21 atom0174Coded := by decide +kernel
theorem atom0174Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8339673081600 : Int) atom0174Coded) := by
  have h := atom0174_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0174Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0175 : SparsePolynomial.Poly := [([0,1,15], 1)]
theorem eval_atom0175 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0175 = ((g 0) * (g 1) * (g 15)) := by
  norm_num [atom0175, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0175_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13063297161600 : Int) atom0175) := by
  rw [SparsePolynomial.eval_scale, eval_atom0175]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 1) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0175Coded : CoefficientMerge.Poly := [(36, 1)]
theorem atom0175Coded_decode : atom0175 = SparsePolynomial.decodeCubic 21 atom0175Coded := by decide +kernel
theorem atom0175Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13063297161600 : Int) atom0175Coded) := by
  have h := atom0175_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0175Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block003 : CoefficientMerge.Poly := [(1, -910415116800), (2, -1337595033600), (3, -1764774950400), (4, -2191954867200), (5, -1127756821248), (6, -1101611750400), (7, -74995341696), (11, -311923584000), (12, -2673400307200), (13, -3291798182400), (14, -3032784115200), (15, 1633334976000), (16, 1206155059200), (17, 778975142400), (18, 351795225600), (19, -1041855091200), (22, -2248010150400), (23, 3342054643200), (24, 2655860659200), (25, 1969666675200), (26, 4266228616704), (27, 4486684608000), (28, 6708083275008), (29, 7026239808000), (30, 7194405657600), (31, 7362571507200), (32, 6906890188800), (33, 2352102592000), (34, 1283472691200), (35, 1969666675200), (36, 11470070707200), (37, -1138018896000), (38, -227603779200), (39, 227603779200), (40, -424763740800), (41, 774948182400), (44, -2675190067200), (45, -6204739968000), (46, -7059099801600), (47, -4930703709696), (48, -4878413568000), (49, -2825180750592), (50, -2675190067200), (51, -2675190067200), (52, -2675190067200), (53, -3299037235200), (54, -8021990681600), (55, -9258786432000), (56, -8740758297600), (57, -2340791308800), (58, -1671993792000), (59, -334398758400), (60, 334398758400), (61, -411716390400), (62, 1503827942400), (66, -3529549900800), (67, -7913459635200), (68, -5785063543296), (69, -5732773401600), (70, -3679540584192), (71, -3529549900800), (72, -3529549900800), (73, -3529549900800), (74, -4153397068800), (75, -8876350515200), (76, -10113146265600), (77, -9595118131200), (78, -3088356163200), (79, -2205968688000), (80, -441193737600), (81, 441193737600), (82, 122258505600), (83, 3970743638400), (88, -4641787684800), (89, -6639423376896), (90, -6587133235200), (91, -4533900417792), (92, -4383909734400), (93, -4383909734400), (94, -4383909734400), (95, -5007756902400), (96, -9730710348800), (97, -10967506099200), (98, -10449477964800), (99, -3835921017600), (100, -2739943584000), (101, -547988716800), (102, 547988716800), (103, 656233401600), (104, 4931898451200), (110, -2803376434176), (111, -4737188565504), (112, -2405504325888), (113, -2255513642496), (114, -2255513642496), (115, -2255513642496), (116, -2879360810496), (117, -7602314256896), (118, -8839110007296), (119, -8321081872896), (120, -1973574437184), (121, -1409696026560), (122, -281939205312), (123, 281939205312), (124, -674014155840), (125, 2537452847808), (132, -2203223500800), (133, -4582289975040), (134, -2203223500800), (135, -2203223500800), (136, -2203223500800), (137, -2827070668800), (138, -7550024115200), (139, -8786819865600), (140, -8268791731200), (141, -1927820563200), (142, -1377014688000), (143, -275402937600), (144, 275402937600), (145, -706695494400), (146, 2478626438400), (154, -2003689370880), (155, -2832943348800), (156, -149990683392), (157, -149990683392), (158, -773837851392), (159, -5496791297792), (160, -6733587048192), (161, -6215558913792), (162, -131241847968), (163, -93744177120), (164, -18748835424), (165, 18748835424), (166, -1989966005280), (167, 168739518816), (176, -3047473951200), (177, -3906457248960), (179, -623847168000), (180, -5346800614400), (181, -6583596364800), (182, -6065568230400), (187, -2083710182400), (198, -5579594697600), (199, -4890082498560), (200, -623847168000), (201, -5346800614400), (202, -6583596364800), (203, -6065568230400), (208, -2083710182400), (209, -5006226065400), (220, -5938155216000), (221, -7814779217280), (222, -9060566932480), (223, -9163508558400), (224, -7336396267200), (226, -966903298200), (228, -918640182600), (229, -7857937924200), (230, -3990163653000), (242, -6834423859200), (243, -13871040695680), (244, -10493784000000), (245, -8311010601600), (246, -545866272000), (247, -1047331756800), (248, -77980896000), (249, 77980896000), (250, -6319465689600), (251, -1852212096000), (264, -12101211673600), (265, -20216234080000), (266, -14294831017600), (267, -4678450537600), (268, -4426219660800), (269, -668350076800), (270, 668350076800), (271, -1974302153600), (272, 5116172140800), (286, -12793997088000), (287, -19480315449600), (288, -5960404170000), (289, -4891229031600), (290, -822949545600), (291, 822949545600), (292, 861530698800), (293, 7406545910400), (308, -11176263705600), (309, -5349896899200), (310, -3790980144000), (311, -758196028800), (312, 758196028800), (313, 1707269961600), (314, 6823764259200), (334, -1823246409600), (352, -1224711290880), (355, -1302318864000), (376, -260463772800), (397, 260463772800), (418, 1302318864000), (419, 2344173955200), (463, -1820830233600), (464, -2427773644800), (465, -2427773644800), (466, -2427773644800), (467, -2427773644800), (468, -2427773644800), (469, -2427773644800), (470, -2427773644800), (471, -2427773644800), (472, -2427773644800), (473, -2427773644800), (474, -2427773644800), (475, -2427773644800), (476, -2427773644800), (477, -2124301939200), (478, -1517358528000), (479, -303471705600), (480, 303471705600), (481, 1517358528000), (482, 821016604800), (503, -4805612985600), (524, -2546971660800), (529, -386816925600), (545, -2546971660800), (551, -821794187520), (552, -417677133312), (566, -2546971660800), (574, -3343613686272), (587, -2546971660800), (595, -2780548031232), (596, -4024428998112), (608, -2546971660800), (617, -4571210926800), (618, -5859685873440), (629, -2546971660800), (639, -8369392046400), (640, -7335123747840), (650, -12559423791600), (661, -8907232824000), (662, -11621331852480), (663, -7383409682880), (664, -5159824387200), (665, -2541656073600), (667, -1933806596400), (669, -1837280365200), (670, -11548455483600), (671, -10527298966800), (683, -9315865036800), (684, -12632125658880), (685, -6572680934400), (686, -3243190406400), (688, -1314854553600), (691, -9251319974400), (692, -7655051980800), (705, -10131616588800), (706, -13090358332800), (707, -5624535571200), (709, -2168938553600), (712, -6464684710400), (713, -4344928761600), (727, -9315601084800), (728, -10246726281600), (729, -399514701600), (730, -1552962607200), (733, -2339013693600), (734, -2546971660800), (749, -7666043212800), (750, -85049395200), (755, -2546971660800), (776, -2228600203200), (793, -1837066936320), (797, -1591857288000), (818, -318371457600), (839, 318371457600), (860, 1591857288000), (881, 2865343118400), (944, -3011521766400), (965, -3011521766400), (970, -515755900800), (986, -3011521766400), (992, -1095725583360), (993, -556902844416), (1007, -3011521766400), (1015, -4458151581696), (1028, -3011521766400), (1036, -3707397374976), (1037, -5365905330816), (1049, -3011521766400), (1058, -6094947902400), (1059, -7812914497920), (1070, -3011521766400), (1080, -11159189395200), (1081, -9780164997120), (1091, -23036426028000), (1102, -11876310432000), (1103, -17721599212800), (1104, -14678573459200), (1105, -10319648774400), (1106, -5083312147200), (1108, -3867613192800), (1110, -3674560730400), (1111, -23096910967200), (1112, -18972176378400), (1124, -12421153382400), (1125, -18926930982400), (1126, -13145361868800), (1127, -6486380812800), (1129, -2629709107200), (1132, -18502639948800), (1133, -13227682406400), (1146, -13508822118400), (1147, -19218084928000), (1148, -10968293593600), (1150, -4337877107200), (1153, -12929369420800), (1154, -6607435968000), (1168, -12420801446400), (1169, -13662301708800), (1170, -799029403200), (1171, -3105925214400), (1174, -4678027387200), (1175, -3011521766400), (1190, -10221390950400), (1191, -170098790400), (1196, -3011521766400), (1217, -2635081545600), (1234, -2449422581760), (1238, -1882201104000), (1259, -376440220800), (1280, 376440220800), (1301, 1882201104000), (1322, 3387961987200), (1411, -515755900800), (1433, -1095725583360), (1434, -556902844416), (1456, -4458151581696), (1477, -3707397374976), (1478, -5365905330816), (1499, -6094947902400), (1500, -7812914497920), (1521, -11159189395200), (1522, -9780164997120), (1532, -20024904261600), (1543, -11876310432000), (1544, -17721599212800), (1545, -14678573459200), (1546, -10319648774400), (1547, -5083312147200), (1549, -3867613192800), (1551, -3674560730400), (1552, -23096910967200), (1553, -15960654612000), (1565, -12421153382400), (1566, -18926930982400), (1567, -13145361868800), (1568, -6486380812800), (1570, -2629709107200), (1573, -18502639948800), (1574, -10216160640000), (1587, -13508822118400), (1588, -19218084928000), (1589, -10968293593600), (1591, -4337877107200), (1594, -12929369420800), (1595, -3595914201600), (1609, -12420801446400), (1610, -13662301708800), (1611, -799029403200), (1612, -3105925214400), (1615, -4678027387200), (1631, -10221390950400), (1632, -170098790400), (1675, -2449422581760), (1852, -515755900800), (1853, -515755900800), (1854, -515755900800), (1855, -515755900800), (1856, -515755900800), (1857, -515755900800), (1858, -515755900800), (1859, -515755900800), (1860, -515755900800), (1861, -515755900800), (1862, -515755900800), (1863, -451286413200), (1864, -322347438000), (1865, -64469487600), (1866, 64469487600), (1867, 322347438000), (1868, 580225388400), (1874, -1095725583360), (1875, -556902844416), (1897, -4458151581696), (1918, -3707397374976), (1919, -5365905330816), (1940, -6094947902400), (1941, -7812914497920), (1962, -11159189395200), (1963, -9780164997120), (1973, -20024904261600), (1984, -11876310432000), (1985, -17721599212800), (1986, -14678573459200), (1987, -10319648774400), (1988, -5083312147200), (1990, -3867613192800), (1992, -3674560730400), (1993, -23096910967200), (1994, -15960654612000), (2006, -12421153382400), (2007, -18926930982400), (2008, -13145361868800), (2009, -6486380812800), (2011, -2629709107200), (2014, -18502639948800), (2015, -10216160640000), (2028, -13508822118400), (2029, -19218084928000), (2030, -10968293593600), (2032, -4337877107200), (2035, -12929369420800), (2036, -3595914201600), (2050, -12420801446400), (2051, -13662301708800), (2052, -799029403200), (2053, -3105925214400), (2056, -4678027387200), (2072, -10221390950400), (2073, -170098790400), (2116, -2449422581760), (2315, -1095725583360), (2316, -1652628427776), (2317, -1095725583360), (2318, -1095725583360), (2319, -1095725583360), (2320, -1095725583360), (2321, -1095725583360), (2322, -1095725583360), (2323, -1095725583360), (2324, -1095725583360), (2325, -958759885440), (2326, -684828489600), (2327, -136965697920), (2328, 136965697920), (2329, 684828489600), (2330, 1232691281280), (2337, -556902844416), (2338, -5015054426112), (2339, -556902844416), (2340, -556902844416), (2341, -556902844416), (2342, -556902844416), (2343, -556902844416), (2344, -556902844416), (2345, -556902844416), (2346, -487289988864), (2347, -348064277760), (2348, -69612855552), (2349, 69612855552), (2350, 348064277760), (2351, 626515699968), (2359, -3707397374976), (2360, -5365905330816), (2381, -6094947902400), (2382, -7812914497920), (2403, -11159189395200), (2404, -9780164997120), (2414, -20024904261600), (2425, -11876310432000), (2426, -17721599212800), (2427, -14678573459200), (2428, -10319648774400), (2429, -5083312147200), (2431, -3867613192800), (2433, -3674560730400), (2434, -23096910967200), (2435, -15960654612000), (2447, -12421153382400), (2448, -18926930982400), (2449, -13145361868800), (2450, -6486380812800), (2452, -2629709107200), (2455, -18502639948800), (2456, -10216160640000), (2469, -13508822118400), (2470, -19218084928000), (2471, -10968293593600), (2473, -4337877107200), (2476, -12929369420800), (2477, -3595914201600), (2491, -12420801446400), (2492, -13662301708800), (2493, -799029403200), (2494, -3105925214400), (2497, -4678027387200), (2513, -10221390950400), (2514, -170098790400), (2557, -2449422581760), (2779, -4458151581696), (2800, -8165548956672), (2801, -9824056912512), (2802, -4458151581696), (2803, -4458151581696), (2804, -4458151581696), (2805, -4458151581696), (2806, -4458151581696), (2807, -4458151581696), (2808, -3900882633984), (2809, -2786344738560), (2810, -557268947712), (2811, 557268947712), (2812, 2786344738560), (2813, 5015420529408), (2822, -6094947902400), (2823, -7812914497920), (2844, -11159189395200), (2845, -9780164997120), (2855, -20024904261600), (2866, -11876310432000), (2867, -17721599212800), (2868, -14678573459200), (2869, -10319648774400), (2870, -5083312147200), (2872, -3867613192800), (2874, -3674560730400), (2875, -23096910967200), (2876, -15960654612000), (2888, -12421153382400), (2889, -18926930982400), (2890, -13145361868800), (2891, -6486380812800), (2893, -2629709107200), (2896, -18502639948800), (2897, -10216160640000), (2910, -13508822118400), (2911, -19218084928000), (2912, -10968293593600), (2914, -4337877107200), (2917, -12929369420800), (2918, -3595914201600), (2932, -12420801446400), (2933, -13662301708800), (2934, -799029403200), (2935, -3105925214400), (2938, -4678027387200), (2954, -10221390950400), (2955, -170098790400), (2998, -2449422581760), (3241, -3707397374976), (3242, -9073302705792), (3243, -3707397374976), (3244, -3707397374976), (3245, -3707397374976), (3246, -3707397374976), (3247, -3707397374976), (3248, -3707397374976), (3249, -3243972703104), (3250, -2317123359360), (3251, -463424671872), (3252, 463424671872), (3253, 2317123359360), (3254, 4170822046848), (3263, -11460853233216), (3264, -13178819828736), (3265, -5365905330816), (3266, -5365905330816), (3267, -5365905330816), (3268, -5365905330816), (3269, -5365905330816), (3270, -4695167164464), (3271, -3353690831760), (3272, -670738166352), (3273, 670738166352), (3274, 3353690831760), (3275, 6036643497168), (3285, -11159189395200), (3286, -9780164997120), (3296, -20024904261600), (3307, -11876310432000), (3308, -17721599212800), (3309, -14678573459200), (3310, -10319648774400), (3311, -5083312147200), (3313, -3867613192800), (3315, -3674560730400), (3316, -23096910967200), (3317, -15960654612000), (3329, -12421153382400), (3330, -18926930982400), (3331, -13145361868800), (3332, -6486380812800), (3334, -2629709107200), (3337, -18502639948800), (3338, -10216160640000), (3351, -13508822118400), (3352, -19218084928000), (3353, -10968293593600), (3355, -4337877107200), (3358, -12929369420800), (3359, -3595914201600), (3373, -12420801446400), (3374, -13662301708800), (3375, -799029403200), (3376, -3105925214400), (3379, -4678027387200), (3395, -10221390950400), (3396, -170098790400), (3439, -2449422581760), (3704, -6094947902400), (3705, -13907862400320), (3706, -6094947902400), (3707, -6094947902400), (3708, -6094947902400), (3709, -6094947902400), (3710, -6094947902400), (3711, -5333079414600), (3712, -3809342439000), (3713, -761868487800), (3714, 761868487800), (3715, 3809342439000), (3716, 6856816390200), (3726, -18972103893120), (3727, -17593079495040), (3728, -7812914497920), (3729, -7812914497920), (3730, -7812914497920), (3731, -7812914497920), (3732, -6836300185680), (3733, -4883071561200), (3734, -976614312240), (3735, 976614312240), (3736, 4883071561200), (3737, -11235375451440), (3748, -11876310432000), (3749, -17721599212800), (3750, -14678573459200), (3751, -10319648774400), (3752, -5083312147200), (3754, -3867613192800), (3756, -3674560730400), (3757, -23096910967200), (3758, -15960654612000), (3770, -12421153382400), (3771, -18926930982400), (3772, -13145361868800), (3773, -6486380812800), (3775, -2629709107200), (3778, -18502639948800), (3779, -10216160640000), (3792, -13508822118400), (3793, -19218084928000), (3794, -10968293593600), (3796, -4337877107200), (3799, -12929369420800), (3800, -3595914201600), (3814, -12420801446400), (3815, -13662301708800), (3816, -799029403200), (3817, -3105925214400), (3820, -4678027387200), (3836, -10221390950400), (3837, -170098790400), (3880, -2449422581760), (4167, -11159189395200), (4168, -20939354392320), (4169, -11159189395200), (4170, -11159189395200), (4171, -11159189395200), (4172, -11159189395200), (4173, -9764290720800), (4174, -6974493372000), (4175, -1394898674400), (4176, 1394898674400), (4177, 6974493372000), (4178, -7470816192000), (4189, -21656475429120), (4190, -27501764209920), (4191, -24458738456320), (4192, -20099813771520), (4193, -14863477144320), (4194, -8557644372480), (4195, -9980216316000), (4196, -1222520624640), (4197, -2452040105760), (4198, -16984307844000), (4199, -24982873251840), (4211, -12421153382400), (4212, -18926930982400), (4213, -13145361868800), (4214, -6486380812800), (4216, -2629709107200), (4219, -18502639948800), (4220, -30241064901600), (4233, -13508822118400), (4234, -19218084928000), (4235, -10968293593600), (4237, -4337877107200), (4240, -12929369420800), (4241, -23620818463200), (4255, -12420801446400), (4256, -13662301708800), (4257, -799029403200), (4258, -3105925214400), (4261, -4678027387200), (4262, -20024904261600), (4277, -10221390950400), (4278, -170098790400), (4283, -20024904261600), (4304, -10012452130800), (4321, -2449422581760), (4346, 10012452130800), (4367, 15018678196200), (4388, 20024904261600), (4409, 22528017294300), (4630, -11876310432000), (4631, -29597909644800), (4632, -26554883891200), (4633, -22195959206400), (4634, -16959622579200), (4635, -10391771628000), (4636, -11290307212800), (4637, -1484538804000), (4638, -2190021926400), (4639, -15674216947200), (4640, -2599805376000), (4652, -30142752595200), (4653, -51327103654400), (4654, -41186609856000), (4655, -29291292172800), (4656, -13001597975520), (4657, -13398652915200), (4658, 1959468991200), (4659, 2715308064000), (4660, -28018750072320), (4661, -6240016137600), (4674, -28187395577600), (4675, -44216307161600), (4676, -30730179200000), (4677, -7405471159520), (4678, -8315797683200), (4679, 7228979346400), (4680, 7224061980800), (4681, -21413891358720), (4682, -3043173672000), (4696, -22740450220800), (4697, -29065262630400), (4698, -5958853790400), (4699, -6973538407200), (4700, 5159824387200), (4701, 4065175850400), (4702, -17455289580000), (4703, -4351049740800), (4718, -15304703097600), (4719, -2711754864000), (4720, -3867613192800), (4721, 2541656073600), (4722, 137923380000), (4723, -18013598820000), (4724, -10241928446400), (4741, -1933806596400), (4743, -1837280365200), (4744, -11548455483600), (4745, -7980327306000), (4762, -2449422581760), (4763, 1933806596400), (4764, 2900709894600), (4765, 3867613192800), (4766, 4351064841900), (4785, 1837280365200), (4786, 11548455483600), (4787, 7980327306000), (4806, 2755920547800), (4807, 20997243955800), (4808, 16104371780700), (4828, 23096910967200), (4829, 41944679450100), (4850, 17955736438500), (5093, -12421153382400), (5094, -31348084364800), (5095, -25566515251200), (5096, -18907534195200), (5097, -10868509209600), (5098, -10392929971200), (5099, -1552644172800), (5100, 1552644172800), (5101, -10739419084800), (5102, 3757636915200), (5115, -32435753100800), (5116, -51290377779200), (5117, -36381605388800), (5118, -14216455742720), (5119, -14889236633600), (5120, 1541815072000), (5121, 6273547817600), (5122, -17258068638720), (5123, 7480722513600), (5137, -25566163315200), (5138, -33294044390400), (5139, -7371710337600), (5140, -5735634321600), (5141, 6572680934400), (5142, 9859021401600), (5143, -10035305467200), (5144, 4572371462400), (5159, -16707771763200), (5160, -3413289196800), (5161, -2629709107200), (5162, 3243190406400), (5163, 4864785609600), (5164, -12016259136000), (5165, -2918982225600), (5182, -1314854553600), (5185, -9251319974400), (5186, -5108080320000), (5203, -2449422581760), (5204, 1314854553600), (5205, 1972281830400), (5206, 2629709107200), (5207, 2958422745600), (5227, 9251319974400), (5228, 5108080320000), (5248, 13876979961600), (5249, 7662120480000), (5269, 18502639948800), (5270, 31031630582400), (5291, 11493180720000), (5556, -13508822118400), (5557, -32726907046400), (5558, -24477115712000), (5559, -11820219353600), (5560, -12780890931200), (5561, -1688602764800), (5562, 1688602764800), (5563, -4486355596800), (5564, 11601510681600), (5578, -31638886374400), (5579, -43848680230400), (5580, -15630045670400), (5581, -16147091993600), (5582, 905752792000), (5583, 5710274024000), (5584, -3611285683200), (5585, 18024431342400), (5600, -21189684544000), (5601, -5864828748800), (5602, -4688849043200), (5603, 5133174860800), (5604, 7875248259200), (5605, -2171658988800), (5606, 8743416091200), (5623, -2168938553600), (5626, -6464684710400), (5627, -1797957100800), (5644, -2449422581760), (5645, 2168938553600), (5646, 3253407830400), (5647, 4337877107200), (5648, 4880111745600), (5668, 6464684710400), (5669, 1797957100800), (5689, 9697027065600), (5690, 2696935651200), (5710, 12929369420800), (5711, 18141454800000), (5732, 4045403476800), (6019, -12420801446400), (6020, -26083103155200), (6021, -11667230668800), (6022, -10868926118400), (6023, -1552600180800), (6024, 1552600180800), (6025, 3084973516800), (6026, 13973401627200), (6041, -23883692659200), (6042, -12923642188800), (6043, -11644863782400), (6044, -1707787713600), (6045, 1707787713600), (6046, 3860911180800), (6047, 15370089422400), (6063, -399514701600), (6064, -1552962607200), (6065, 399514701600), (6066, 599272052400), (6067, -1539984290400), (6068, 898908078600), (6085, -2449422581760), (6086, 1552962607200), (6087, 2329443910800), (6088, 3105925214400), (6089, 3494165866200), (6109, 2339013693600), (6130, 3508520540400), (6151, 4678027387200), (6152, 5262780810600), (6482, -10221390950400), (6483, -9113815872000), (6484, -6388369344000), (6485, -1277673868800), (6486, 1277673868800), (6487, 6388369344000), (6488, 11499064819200), (6504, -85049395200), (6506, 85049395200), (6507, 127574092800), (6508, 170098790400), (6509, 191361139200), (6526, -2449422581760), (6967, -2143244759040), (7408, -1530889113600), (7409, -306177822720), (7410, 306177822720), (7411, 1530889113600), (7412, 2755600404480)]
theorem block003_data : block003 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1251556516350 : Int) atom0096Coded) (CoefficientMerge.scale (417466889280 : Int) atom0097Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (906380102880 : Int) atom0098Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (644978048400 : Int) atom0099Coded) (CoefficientMerge.scale (317707009200 : Int) atom0100Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (241725824550 : Int) atom0101Coded) (CoefficientMerge.scale (229660045650 : Int) atom0102Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1443556935450 : Int) atom0103Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (997540913250 : Int) atom0104Coded) (CoefficientMerge.scale (390768144480 : Int) atom0105Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (821585116800 : Int) atom0106Coded) (CoefficientMerge.scale (405398800800 : Int) atom0107Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164356819200 : Int) atom0108Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1156414996800 : Int) atom0109Coded) (CoefficientMerge.scale (638510040000 : Int) atom0110Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (330801340800 : Int) atom0111Coded) (CoefficientMerge.scale (650421156000 : Int) atom0112Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (271117319200 : Int) atom0113Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (808085588800 : Int) atom0114Coded) (CoefficientMerge.scale (224744637600 : Int) atom0115Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49939337700 : Int) atom0116Coded) (CoefficientMerge.scale (194120325900 : Int) atom0117Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (292376711700 : Int) atom0118Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10631174400 : Int) atom0119Coded) (CoefficientMerge.scale (113801889600 : Int) atom0120Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (167199379200 : Int) atom0121Coded) (CoefficientMerge.scale (220596868800 : Int) atom0122Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (273994358400 : Int) atom0123Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140969602656 : Int) atom0124Coded) (CoefficientMerge.scale (137701468800 : Int) atom0125Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9374417712 : Int) atom0126Coded) (CoefficientMerge.scale (38990448000 : Int) atom0127Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (334175038400 : Int) atom0128Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411474772800 : Int) atom0129Coded) (CoefficientMerge.scale (379098014400 : Int) atom0130Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (130231886400 : Int) atom0131Coded) (CoefficientMerge.scale (151735852800 : Int) atom0132Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (159185728800 : Int) atom0133Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (188220110400 : Int) atom0134Coded) (CoefficientMerge.scale (32234743800 : Int) atom0135Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68482848960 : Int) atom0136Coded) (CoefficientMerge.scale (34806427776 : Int) atom0137Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (278634473856 : Int) atom0138Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (231712335936 : Int) atom0139Coded) (CoefficientMerge.scale (335369083176 : Int) atom0140Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (380934243900 : Int) atom0141Coded) (CoefficientMerge.scale (488307156120 : Int) atom0142Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (697449337200 : Int) atom0143Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (611260312320 : Int) atom0144Coded) (CoefficientMerge.scale (742269402000 : Int) atom0145Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (690133061520 : Int) atom0146Coded) (CoefficientMerge.scale (11030738320 : Int) atom0147Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (776322086400 : Int) atom0148Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (792165041920 : Int) atom0149Coded) (CoefficientMerge.scale (844301382400 : Int) atom0150Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (870328967200 : Int) atom0151Coded) (CoefficientMerge.scale (35097193600 : Int) atom0152Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (776300090400 : Int) atom0153Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (853893856800 : Int) atom0154Coded) (CoefficientMerge.scale (638836934400 : Int) atom0155Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153088911360 : Int) atom0156Coded) (CoefficientMerge.scale (1633334976000 : Int) atom0157Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1206155059200 : Int) atom0158Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (778975142400 : Int) atom0159Coded) (CoefficientMerge.scale (351795225600 : Int) atom0160Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (331499347200 : Int) atom0161Coded) (CoefficientMerge.scale (7169277427200 : Int) atom0162Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7123853318400 : Int) atom0163Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7078429209600 : Int) atom0164Coded) (CoefficientMerge.scale (7778694082176 : Int) atom0165Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7959932467200 : Int) atom0166Coded) (CoefficientMerge.scale (8641406521152 : Int) atom0167Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8847070041600 : Int) atom0168Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9015235891200 : Int) atom0169Coded) (CoefficientMerge.scale (9183401740800 : Int) atom0170Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9195605798400 : Int) atom0171Coded) (CoefficientMerge.scale (8183033286400 : Int) atom0172Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8042000198400 : Int) atom0173Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8339673081600 : Int) atom0174Coded) (CoefficientMerge.scale (13063297161600 : Int) atom0175Coded)))))))) := by decide +kernel
theorem block003_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block003 := by
  rw [block003_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0096Coded_nonneg g hg hA hB) (atom0097Coded_nonneg g hg hA hB)) (add_nonneg (atom0098Coded_nonneg g hg hA hB) (add_nonneg (atom0099Coded_nonneg g hg hA hB) (atom0100Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0101Coded_nonneg g hg hA hB) (atom0102Coded_nonneg g hg hA hB)) (add_nonneg (atom0103Coded_nonneg g hg hA hB) (add_nonneg (atom0104Coded_nonneg g hg hA hB) (atom0105Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0106Coded_nonneg g hg hA hB) (atom0107Coded_nonneg g hg hA hB)) (add_nonneg (atom0108Coded_nonneg g hg hA hB) (add_nonneg (atom0109Coded_nonneg g hg hA hB) (atom0110Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0111Coded_nonneg g hg hA hB) (atom0112Coded_nonneg g hg hA hB)) (add_nonneg (atom0113Coded_nonneg g hg hA hB) (add_nonneg (atom0114Coded_nonneg g hg hA hB) (atom0115Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0116Coded_nonneg g hg hA hB) (atom0117Coded_nonneg g hg hA hB)) (add_nonneg (atom0118Coded_nonneg g hg hA hB) (add_nonneg (atom0119Coded_nonneg g hg hA hB) (atom0120Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0121Coded_nonneg g hg hA hB) (atom0122Coded_nonneg g hg hA hB)) (add_nonneg (atom0123Coded_nonneg g hg hA hB) (add_nonneg (atom0124Coded_nonneg g hg hA hB) (atom0125Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0126Coded_nonneg g hg hA hB) (atom0127Coded_nonneg g hg hA hB)) (add_nonneg (atom0128Coded_nonneg g hg hA hB) (add_nonneg (atom0129Coded_nonneg g hg hA hB) (atom0130Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0131Coded_nonneg g hg hA hB) (atom0132Coded_nonneg g hg hA hB)) (add_nonneg (atom0133Coded_nonneg g hg hA hB) (add_nonneg (atom0134Coded_nonneg g hg hA hB) (atom0135Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0136Coded_nonneg g hg hA hB) (atom0137Coded_nonneg g hg hA hB)) (add_nonneg (atom0138Coded_nonneg g hg hA hB) (add_nonneg (atom0139Coded_nonneg g hg hA hB) (atom0140Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0141Coded_nonneg g hg hA hB) (atom0142Coded_nonneg g hg hA hB)) (add_nonneg (atom0143Coded_nonneg g hg hA hB) (add_nonneg (atom0144Coded_nonneg g hg hA hB) (atom0145Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0146Coded_nonneg g hg hA hB) (atom0147Coded_nonneg g hg hA hB)) (add_nonneg (atom0148Coded_nonneg g hg hA hB) (add_nonneg (atom0149Coded_nonneg g hg hA hB) (atom0150Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0151Coded_nonneg g hg hA hB) (atom0152Coded_nonneg g hg hA hB)) (add_nonneg (atom0153Coded_nonneg g hg hA hB) (add_nonneg (atom0154Coded_nonneg g hg hA hB) (atom0155Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0156Coded_nonneg g hg hA hB) (atom0157Coded_nonneg g hg hA hB)) (add_nonneg (atom0158Coded_nonneg g hg hA hB) (add_nonneg (atom0159Coded_nonneg g hg hA hB) (atom0160Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0161Coded_nonneg g hg hA hB) (atom0162Coded_nonneg g hg hA hB)) (add_nonneg (atom0163Coded_nonneg g hg hA hB) (add_nonneg (atom0164Coded_nonneg g hg hA hB) (atom0165Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0166Coded_nonneg g hg hA hB) (atom0167Coded_nonneg g hg hA hB)) (add_nonneg (atom0168Coded_nonneg g hg hA hB) (add_nonneg (atom0169Coded_nonneg g hg hA hB) (atom0170Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0171Coded_nonneg g hg hA hB) (atom0172Coded_nonneg g hg hA hB)) (add_nonneg (atom0173Coded_nonneg g hg hA hB) (add_nonneg (atom0174Coded_nonneg g hg hA hB) (atom0175Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
