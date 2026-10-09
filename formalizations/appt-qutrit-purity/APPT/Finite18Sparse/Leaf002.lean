import APPT.Finite18Sparse.Base08
import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0095 : SparsePolynomial.Poly := [([0,2,17], -8), ([1,2,17], -12), ([2,2,17], -16), ([2,3,17], -16), ([2,4,17], -16), ([2,5,17], -16), ([2,6,17], -16), ([2,7,17], -16), ([2,8,17], -16), ([2,9,17], -16), ([2,10,17], -16), ([2,11,17], -16), ([2,12,17], -14), ([2,13,17], -10), ([2,14,17], -2), ([2,15,17], 2), ([2,16,17], 10), ([2,17,17], 18)]
theorem atom0095_data : atom0095 = SparsePolynomial.monoTimes [2,17] 1 base08 := by decide +kernel
theorem eval_atom0095 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0095 = (quadB (outer g) ![2,2,1] * g 2 * g 17) := by
  rw [atom0095_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0095_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38808000 : Int) atom0095) := by
  rw [SparsePolynomial.eval_scale, eval_atom0095]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 2 * g 17) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0095Coded : CoefficientMerge.Poly := [(53, -8), (377, -12), (701, -16), (719, -16), (737, -16), (755, -16), (773, -16), (791, -16), (809, -16), (827, -16), (845, -16), (863, -16), (881, -14), (899, -10), (917, -2), (935, 2), (953, 10), (971, 18)]
theorem atom0095Coded_decode : atom0095 = SparsePolynomial.decodeCubic 18 atom0095Coded := by decide +kernel
theorem atom0095Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (38808000 : Int) atom0095Coded) := by
  have h := atom0095_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0095Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0096 : SparsePolynomial.Poly := [([0,4,4], -8), ([1,4,4], -12), ([2,4,4], -16), ([3,4,4], -16), ([4,4,4], -16), ([4,4,5], -16), ([4,4,6], -16), ([4,4,7], -16), ([4,4,8], -16), ([4,4,9], -16), ([4,4,10], -16), ([4,4,11], -16), ([4,4,12], -14), ([4,4,13], -10), ([4,4,14], -2), ([4,4,15], 2), ([4,4,16], 10), ([4,4,17], 18)]
theorem atom0096_data : atom0096 = SparsePolynomial.monoTimes [4,4] 1 base08 := by decide +kernel
theorem eval_atom0096 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0096 = (quadB (outer g) ![2,2,1] * g 4 * g 4) := by
  rw [atom0096_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0096_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77518560 : Int) atom0096) := by
  rw [SparsePolynomial.eval_scale, eval_atom0096]
  have hg4 : 0 ≤ g 4 := hg 4
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 4 * g 4) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0096Coded : CoefficientMerge.Poly := [(76, -8), (400, -12), (724, -16), (1048, -16), (1372, -16), (1373, -16), (1374, -16), (1375, -16), (1376, -16), (1377, -16), (1378, -16), (1379, -16), (1380, -14), (1381, -10), (1382, -2), (1383, 2), (1384, 10), (1385, 18)]
theorem atom0096Coded_decode : atom0096 = SparsePolynomial.decodeCubic 18 atom0096Coded := by decide +kernel
theorem atom0096Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (77518560 : Int) atom0096Coded) := by
  have h := atom0096_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0096Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0097 : SparsePolynomial.Poly := [([0,4,5], -8), ([1,4,5], -12), ([2,4,5], -16), ([3,4,5], -16), ([4,4,5], -16), ([4,5,5], -16), ([4,5,6], -16), ([4,5,7], -16), ([4,5,8], -16), ([4,5,9], -16), ([4,5,10], -16), ([4,5,11], -16), ([4,5,12], -14), ([4,5,13], -10), ([4,5,14], -2), ([4,5,15], 2), ([4,5,16], 10), ([4,5,17], 18)]
theorem atom0097_data : atom0097 = SparsePolynomial.monoTimes [4,5] 1 base08 := by decide +kernel
theorem eval_atom0097 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0097 = (quadB (outer g) ![2,2,1] * g 4 * g 5) := by
  rw [atom0097_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0097_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8654952 : Int) atom0097) := by
  rw [SparsePolynomial.eval_scale, eval_atom0097]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 4 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0097Coded : CoefficientMerge.Poly := [(77, -8), (401, -12), (725, -16), (1049, -16), (1373, -16), (1391, -16), (1392, -16), (1393, -16), (1394, -16), (1395, -16), (1396, -16), (1397, -16), (1398, -14), (1399, -10), (1400, -2), (1401, 2), (1402, 10), (1403, 18)]
theorem atom0097Coded_decode : atom0097 = SparsePolynomial.decodeCubic 18 atom0097Coded := by decide +kernel
theorem atom0097Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8654952 : Int) atom0097Coded) := by
  have h := atom0097_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0097Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0098 : SparsePolynomial.Poly := [([0,5,5], -8), ([1,5,5], -12), ([2,5,5], -16), ([3,5,5], -16), ([4,5,5], -16), ([5,5,5], -16), ([5,5,6], -16), ([5,5,7], -16), ([5,5,8], -16), ([5,5,9], -16), ([5,5,10], -16), ([5,5,11], -16), ([5,5,12], -14), ([5,5,13], -10), ([5,5,14], -2), ([5,5,15], 2), ([5,5,16], 10), ([5,5,17], 18)]
theorem atom0098_data : atom0098 = SparsePolynomial.monoTimes [5,5] 1 base08 := by decide +kernel
theorem eval_atom0098 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0098 = (quadB (outer g) ![2,2,1] * g 5 * g 5) := by
  rw [atom0098_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0098_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74370240 : Int) atom0098) := by
  rw [SparsePolynomial.eval_scale, eval_atom0098]
  have hg5 : 0 ≤ g 5 := hg 5
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 5 * g 5) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0098Coded : CoefficientMerge.Poly := [(95, -8), (419, -12), (743, -16), (1067, -16), (1391, -16), (1715, -16), (1716, -16), (1717, -16), (1718, -16), (1719, -16), (1720, -16), (1721, -16), (1722, -14), (1723, -10), (1724, -2), (1725, 2), (1726, 10), (1727, 18)]
theorem atom0098Coded_decode : atom0098 = SparsePolynomial.decodeCubic 18 atom0098Coded := by decide +kernel
theorem atom0098Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (74370240 : Int) atom0098Coded) := by
  have h := atom0098_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0098Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0099 : SparsePolynomial.Poly := [([0,5,6], -8), ([1,5,6], -12), ([2,5,6], -16), ([3,5,6], -16), ([4,5,6], -16), ([5,5,6], -16), ([5,6,6], -16), ([5,6,7], -16), ([5,6,8], -16), ([5,6,9], -16), ([5,6,10], -16), ([5,6,11], -16), ([5,6,12], -14), ([5,6,13], -10), ([5,6,14], -2), ([5,6,15], 2), ([5,6,16], 10), ([5,6,17], 18)]
theorem atom0099_data : atom0099 = SparsePolynomial.monoTimes [5,6] 1 base08 := by decide +kernel
theorem eval_atom0099 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0099 = (quadB (outer g) ![2,2,1] * g 5 * g 6) := by
  rw [atom0099_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0099_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47881872 : Int) atom0099) := by
  rw [SparsePolynomial.eval_scale, eval_atom0099]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 5 * g 6) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0099Coded : CoefficientMerge.Poly := [(96, -8), (420, -12), (744, -16), (1068, -16), (1392, -16), (1716, -16), (1734, -16), (1735, -16), (1736, -16), (1737, -16), (1738, -16), (1739, -16), (1740, -14), (1741, -10), (1742, -2), (1743, 2), (1744, 10), (1745, 18)]
theorem atom0099Coded_decode : atom0099 = SparsePolynomial.decodeCubic 18 atom0099Coded := by decide +kernel
theorem atom0099Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (47881872 : Int) atom0099Coded) := by
  have h := atom0099_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0099Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0100 : SparsePolynomial.Poly := [([0,6,7], -8), ([1,6,7], -12), ([2,6,7], -16), ([3,6,7], -16), ([4,6,7], -16), ([5,6,7], -16), ([6,6,7], -16), ([6,7,7], -16), ([6,7,8], -16), ([6,7,9], -16), ([6,7,10], -16), ([6,7,11], -16), ([6,7,12], -14), ([6,7,13], -10), ([6,7,14], -2), ([6,7,15], 2), ([6,7,16], 10), ([6,7,17], 18)]
theorem atom0100_data : atom0100 = SparsePolynomial.monoTimes [6,7] 1 base08 := by decide +kernel
theorem eval_atom0100 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0100 = (quadB (outer g) ![2,2,1] * g 6 * g 7) := by
  rw [atom0100_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0100_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91894392 : Int) atom0100) := by
  rw [SparsePolynomial.eval_scale, eval_atom0100]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 6 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0100Coded : CoefficientMerge.Poly := [(115, -8), (439, -12), (763, -16), (1087, -16), (1411, -16), (1735, -16), (2059, -16), (2077, -16), (2078, -16), (2079, -16), (2080, -16), (2081, -16), (2082, -14), (2083, -10), (2084, -2), (2085, 2), (2086, 10), (2087, 18)]
theorem atom0100Coded_decode : atom0100 = SparsePolynomial.decodeCubic 18 atom0100Coded := by decide +kernel
theorem atom0100Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (91894392 : Int) atom0100Coded) := by
  have h := atom0100_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0100Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0101 : SparsePolynomial.Poly := [([0,7,7], -8), ([1,7,7], -12), ([2,7,7], -16), ([3,7,7], -16), ([4,7,7], -16), ([5,7,7], -16), ([6,7,7], -16), ([7,7,7], -16), ([7,7,8], -16), ([7,7,9], -16), ([7,7,10], -16), ([7,7,11], -16), ([7,7,12], -14), ([7,7,13], -10), ([7,7,14], -2), ([7,7,15], 2), ([7,7,16], 10), ([7,7,17], 18)]
theorem atom0101_data : atom0101 = SparsePolynomial.monoTimes [7,7] 1 base08 := by decide +kernel
theorem eval_atom0101 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0101 = (quadB (outer g) ![2,2,1] * g 7 * g 7) := by
  rw [atom0101_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0101_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8139420 : Int) atom0101) := by
  rw [SparsePolynomial.eval_scale, eval_atom0101]
  have hg7 : 0 ≤ g 7 := hg 7
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 7 * g 7) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0101Coded : CoefficientMerge.Poly := [(133, -8), (457, -12), (781, -16), (1105, -16), (1429, -16), (1753, -16), (2077, -16), (2401, -16), (2402, -16), (2403, -16), (2404, -16), (2405, -16), (2406, -14), (2407, -10), (2408, -2), (2409, 2), (2410, 10), (2411, 18)]
theorem atom0101Coded_decode : atom0101 = SparsePolynomial.decodeCubic 18 atom0101Coded := by decide +kernel
theorem atom0101Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8139420 : Int) atom0101Coded) := by
  have h := atom0101_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0101Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0102 : SparsePolynomial.Poly := [([0,7,8], -8), ([1,7,8], -12), ([2,7,8], -16), ([3,7,8], -16), ([4,7,8], -16), ([5,7,8], -16), ([6,7,8], -16), ([7,7,8], -16), ([7,8,8], -16), ([7,8,9], -16), ([7,8,10], -16), ([7,8,11], -16), ([7,8,12], -14), ([7,8,13], -10), ([7,8,14], -2), ([7,8,15], 2), ([7,8,16], 10), ([7,8,17], 18)]
theorem atom0102_data : atom0102 = SparsePolynomial.monoTimes [7,8] 1 base08 := by decide +kernel
theorem eval_atom0102 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0102 = (quadB (outer g) ![2,2,1] * g 7 * g 8) := by
  rw [atom0102_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0102_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108513552 : Int) atom0102) := by
  rw [SparsePolynomial.eval_scale, eval_atom0102]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 7 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0102Coded : CoefficientMerge.Poly := [(134, -8), (458, -12), (782, -16), (1106, -16), (1430, -16), (1754, -16), (2078, -16), (2402, -16), (2420, -16), (2421, -16), (2422, -16), (2423, -16), (2424, -14), (2425, -10), (2426, -2), (2427, 2), (2428, 10), (2429, 18)]
theorem atom0102Coded_decode : atom0102 = SparsePolynomial.decodeCubic 18 atom0102Coded := by decide +kernel
theorem atom0102Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (108513552 : Int) atom0102Coded) := by
  have h := atom0102_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0102Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0103 : SparsePolynomial.Poly := [([0,8,8], -8), ([1,8,8], -12), ([2,8,8], -16), ([3,8,8], -16), ([4,8,8], -16), ([5,8,8], -16), ([6,8,8], -16), ([7,8,8], -16), ([8,8,8], -16), ([8,8,9], -16), ([8,8,10], -16), ([8,8,11], -16), ([8,8,12], -14), ([8,8,13], -10), ([8,8,14], -2), ([8,8,15], 2), ([8,8,16], 10), ([8,8,17], 18)]
theorem atom0103_data : atom0103 = SparsePolynomial.monoTimes [8,8] 1 base08 := by decide +kernel
theorem eval_atom0103 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0103 = (quadB (outer g) ![2,2,1] * g 8 * g 8) := by
  rw [atom0103_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0103_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83536500 : Int) atom0103) := by
  rw [SparsePolynomial.eval_scale, eval_atom0103]
  have hg8 : 0 ≤ g 8 := hg 8
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 8 * g 8) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0103Coded : CoefficientMerge.Poly := [(152, -8), (476, -12), (800, -16), (1124, -16), (1448, -16), (1772, -16), (2096, -16), (2420, -16), (2744, -16), (2745, -16), (2746, -16), (2747, -16), (2748, -14), (2749, -10), (2750, -2), (2751, 2), (2752, 10), (2753, 18)]
theorem atom0103Coded_decode : atom0103 = SparsePolynomial.decodeCubic 18 atom0103Coded := by decide +kernel
theorem atom0103Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (83536500 : Int) atom0103Coded) := by
  have h := atom0103_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0103Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0104 : SparsePolynomial.Poly := [([0,8,9], -8), ([1,8,9], -12), ([2,8,9], -16), ([3,8,9], -16), ([4,8,9], -16), ([5,8,9], -16), ([6,8,9], -16), ([7,8,9], -16), ([8,8,9], -16), ([8,9,9], -16), ([8,9,10], -16), ([8,9,11], -16), ([8,9,12], -14), ([8,9,13], -10), ([8,9,14], -2), ([8,9,15], 2), ([8,9,16], 10), ([8,9,17], 18)]
theorem atom0104_data : atom0104 = SparsePolynomial.monoTimes [8,9] 1 base08 := by decide +kernel
theorem eval_atom0104 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0104 = (quadB (outer g) ![2,2,1] * g 8 * g 9) := by
  rw [atom0104_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0104_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (188493600 : Int) atom0104) := by
  rw [SparsePolynomial.eval_scale, eval_atom0104]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 8 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0104Coded : CoefficientMerge.Poly := [(153, -8), (477, -12), (801, -16), (1125, -16), (1449, -16), (1773, -16), (2097, -16), (2421, -16), (2745, -16), (2763, -16), (2764, -16), (2765, -16), (2766, -14), (2767, -10), (2768, -2), (2769, 2), (2770, 10), (2771, 18)]
theorem atom0104Coded_decode : atom0104 = SparsePolynomial.decodeCubic 18 atom0104Coded := by decide +kernel
theorem atom0104Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (188493600 : Int) atom0104Coded) := by
  have h := atom0104_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0104Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0105 : SparsePolynomial.Poly := [([0,8,10], -8), ([1,8,10], -12), ([2,8,10], -16), ([3,8,10], -16), ([4,8,10], -16), ([5,8,10], -16), ([6,8,10], -16), ([7,8,10], -16), ([8,8,10], -16), ([8,9,10], -16), ([8,10,10], -16), ([8,10,11], -16), ([8,10,12], -14), ([8,10,13], -10), ([8,10,14], -2), ([8,10,15], 2), ([8,10,16], 10), ([8,10,17], 18)]
theorem atom0105_data : atom0105 = SparsePolynomial.monoTimes [8,10] 1 base08 := by decide +kernel
theorem eval_atom0105 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0105 = (quadB (outer g) ![2,2,1] * g 8 * g 10) := by
  rw [atom0105_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0105_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10726368 : Int) atom0105) := by
  rw [SparsePolynomial.eval_scale, eval_atom0105]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 8 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0105Coded : CoefficientMerge.Poly := [(154, -8), (478, -12), (802, -16), (1126, -16), (1450, -16), (1774, -16), (2098, -16), (2422, -16), (2746, -16), (2764, -16), (2782, -16), (2783, -16), (2784, -14), (2785, -10), (2786, -2), (2787, 2), (2788, 10), (2789, 18)]
theorem atom0105Coded_decode : atom0105 = SparsePolynomial.decodeCubic 18 atom0105Coded := by decide +kernel
theorem atom0105Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10726368 : Int) atom0105Coded) := by
  have h := atom0105_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0105Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0106 : SparsePolynomial.Poly := [([0,9,9], -8), ([1,9,9], -12), ([2,9,9], -16), ([3,9,9], -16), ([4,9,9], -16), ([5,9,9], -16), ([6,9,9], -16), ([7,9,9], -16), ([8,9,9], -16), ([9,9,9], -16), ([9,9,10], -16), ([9,9,11], -16), ([9,9,12], -14), ([9,9,13], -10), ([9,9,14], -2), ([9,9,15], 2), ([9,9,16], 10), ([9,9,17], 18)]
theorem atom0106_data : atom0106 = SparsePolynomial.monoTimes [9,9] 1 base08 := by decide +kernel
theorem eval_atom0106 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0106 = (quadB (outer g) ![2,2,1] * g 9 * g 9) := by
  rw [atom0106_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0106_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175867680 : Int) atom0106) := by
  rw [SparsePolynomial.eval_scale, eval_atom0106]
  have hg9 : 0 ≤ g 9 := hg 9
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 9 * g 9) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0106Coded : CoefficientMerge.Poly := [(171, -8), (495, -12), (819, -16), (1143, -16), (1467, -16), (1791, -16), (2115, -16), (2439, -16), (2763, -16), (3087, -16), (3088, -16), (3089, -16), (3090, -14), (3091, -10), (3092, -2), (3093, 2), (3094, 10), (3095, 18)]
theorem atom0106Coded_decode : atom0106 = SparsePolynomial.decodeCubic 18 atom0106Coded := by decide +kernel
theorem atom0106Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (175867680 : Int) atom0106Coded) := by
  have h := atom0106_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0106Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0107 : SparsePolynomial.Poly := [([0,9,10], -8), ([1,9,10], -12), ([2,9,10], -16), ([3,9,10], -16), ([4,9,10], -16), ([5,9,10], -16), ([6,9,10], -16), ([7,9,10], -16), ([8,9,10], -16), ([9,9,10], -16), ([9,10,10], -16), ([9,10,11], -16), ([9,10,12], -14), ([9,10,13], -10), ([9,10,14], -2), ([9,10,15], 2), ([9,10,16], 10), ([9,10,17], 18)]
theorem atom0107_data : atom0107 = SparsePolynomial.monoTimes [9,10] 1 base08 := by decide +kernel
theorem eval_atom0107 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0107 = (quadB (outer g) ![2,2,1] * g 9 * g 10) := by
  rw [atom0107_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0107_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (203546880 : Int) atom0107) := by
  rw [SparsePolynomial.eval_scale, eval_atom0107]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 9 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0107Coded : CoefficientMerge.Poly := [(172, -8), (496, -12), (820, -16), (1144, -16), (1468, -16), (1792, -16), (2116, -16), (2440, -16), (2764, -16), (3088, -16), (3106, -16), (3107, -16), (3108, -14), (3109, -10), (3110, -2), (3111, 2), (3112, 10), (3113, 18)]
theorem atom0107Coded_decode : atom0107 = SparsePolynomial.decodeCubic 18 atom0107Coded := by decide +kernel
theorem atom0107Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (203546880 : Int) atom0107Coded) := by
  have h := atom0107_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0107Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0108 : SparsePolynomial.Poly := [([0,9,11], -8), ([1,9,11], -12), ([2,9,11], -16), ([3,9,11], -16), ([4,9,11], -16), ([5,9,11], -16), ([6,9,11], -16), ([7,9,11], -16), ([8,9,11], -16), ([9,9,11], -16), ([9,10,11], -16), ([9,11,11], -16), ([9,11,12], -14), ([9,11,13], -10), ([9,11,14], -2), ([9,11,15], 2), ([9,11,16], 10), ([9,11,17], 18)]
theorem atom0108_data : atom0108 = SparsePolynomial.monoTimes [9,11] 1 base08 := by decide +kernel
theorem eval_atom0108 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0108 = (quadB (outer g) ![2,2,1] * g 9 * g 11) := by
  rw [atom0108_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0108_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46651680 : Int) atom0108) := by
  rw [SparsePolynomial.eval_scale, eval_atom0108]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 9 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0108Coded : CoefficientMerge.Poly := [(173, -8), (497, -12), (821, -16), (1145, -16), (1469, -16), (1793, -16), (2117, -16), (2441, -16), (2765, -16), (3089, -16), (3107, -16), (3125, -16), (3126, -14), (3127, -10), (3128, -2), (3129, 2), (3130, 10), (3131, 18)]
theorem atom0108Coded_decode : atom0108 = SparsePolynomial.decodeCubic 18 atom0108Coded := by decide +kernel
theorem atom0108Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (46651680 : Int) atom0108Coded) := by
  have h := atom0108_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0108Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0109 : SparsePolynomial.Poly := [([0,10,10], -8), ([1,10,10], -12), ([2,10,10], -16), ([3,10,10], -16), ([4,10,10], -16), ([5,10,10], -16), ([6,10,10], -16), ([7,10,10], -16), ([8,10,10], -16), ([9,10,10], -16), ([10,10,10], -16), ([10,10,11], -16), ([10,10,12], -14), ([10,10,13], -10), ([10,10,14], -2), ([10,10,15], 2), ([10,10,16], 10), ([10,10,17], 18)]
theorem atom0109_data : atom0109 = SparsePolynomial.monoTimes [10,10] 1 base08 := by decide +kernel
theorem eval_atom0109 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0109 = (quadB (outer g) ![2,2,1] * g 10 * g 10) := by
  rw [atom0109_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0109_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (170358240 : Int) atom0109) := by
  rw [SparsePolynomial.eval_scale, eval_atom0109]
  have hg10 : 0 ≤ g 10 := hg 10
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 10 * g 10) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0109Coded : CoefficientMerge.Poly := [(190, -8), (514, -12), (838, -16), (1162, -16), (1486, -16), (1810, -16), (2134, -16), (2458, -16), (2782, -16), (3106, -16), (3430, -16), (3431, -16), (3432, -14), (3433, -10), (3434, -2), (3435, 2), (3436, 10), (3437, 18)]
theorem atom0109Coded_decode : atom0109 = SparsePolynomial.decodeCubic 18 atom0109Coded := by decide +kernel
theorem atom0109Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (170358240 : Int) atom0109Coded) := by
  have h := atom0109_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0109Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0110 : SparsePolynomial.Poly := [([0,10,11], -8), ([1,10,11], -12), ([2,10,11], -16), ([3,10,11], -16), ([4,10,11], -16), ([5,10,11], -16), ([6,10,11], -16), ([7,10,11], -16), ([8,10,11], -16), ([9,10,11], -16), ([10,10,11], -16), ([10,11,11], -16), ([10,11,12], -14), ([10,11,13], -10), ([10,11,14], -2), ([10,11,15], 2), ([10,11,16], 10), ([10,11,17], 18)]
theorem atom0110_data : atom0110 = SparsePolynomial.monoTimes [10,11] 1 base08 := by decide +kernel
theorem eval_atom0110 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0110 = (quadB (outer g) ![2,2,1] * g 10 * g 11) := by
  rw [atom0110_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0110_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (221921760 : Int) atom0110) := by
  rw [SparsePolynomial.eval_scale, eval_atom0110]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 10 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0110Coded : CoefficientMerge.Poly := [(191, -8), (515, -12), (839, -16), (1163, -16), (1487, -16), (1811, -16), (2135, -16), (2459, -16), (2783, -16), (3107, -16), (3431, -16), (3449, -16), (3450, -14), (3451, -10), (3452, -2), (3453, 2), (3454, 10), (3455, 18)]
theorem atom0110Coded_decode : atom0110 = SparsePolynomial.decodeCubic 18 atom0110Coded := by decide +kernel
theorem atom0110Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (221921760 : Int) atom0110Coded) := by
  have h := atom0110_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0110Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0111 : SparsePolynomial.Poly := [([0,11,11], -8), ([1,11,11], -12), ([2,11,11], -16), ([3,11,11], -16), ([4,11,11], -16), ([5,11,11], -16), ([6,11,11], -16), ([7,11,11], -16), ([8,11,11], -16), ([9,11,11], -16), ([10,11,11], -16), ([11,11,11], -16), ([11,11,12], -14), ([11,11,13], -10), ([11,11,14], -2), ([11,11,15], 2), ([11,11,16], 10), ([11,11,17], 18)]
theorem atom0111_data : atom0111 = SparsePolynomial.monoTimes [11,11] 1 base08 := by decide +kernel
theorem eval_atom0111 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0111 = (quadB (outer g) ![2,2,1] * g 11 * g 11) := by
  rw [atom0111_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0111_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (166440960 : Int) atom0111) := by
  rw [SparsePolynomial.eval_scale, eval_atom0111]
  have hg11 : 0 ≤ g 11 := hg 11
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 11) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0111Coded : CoefficientMerge.Poly := [(209, -8), (533, -12), (857, -16), (1181, -16), (1505, -16), (1829, -16), (2153, -16), (2477, -16), (2801, -16), (3125, -16), (3449, -16), (3773, -16), (3774, -14), (3775, -10), (3776, -2), (3777, 2), (3778, 10), (3779, 18)]
theorem atom0111Coded_decode : atom0111 = SparsePolynomial.decodeCubic 18 atom0111Coded := by decide +kernel
theorem atom0111Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (166440960 : Int) atom0111Coded) := by
  have h := atom0111_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0111Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0112 : SparsePolynomial.Poly := [([0,11,12], -8), ([1,11,12], -12), ([2,11,12], -16), ([3,11,12], -16), ([4,11,12], -16), ([5,11,12], -16), ([6,11,12], -16), ([7,11,12], -16), ([8,11,12], -16), ([9,11,12], -16), ([10,11,12], -16), ([11,11,12], -16), ([11,12,12], -14), ([11,12,13], -10), ([11,12,14], -2), ([11,12,15], 2), ([11,12,16], 10), ([11,12,17], 18)]
theorem atom0112_data : atom0112 = SparsePolynomial.monoTimes [11,12] 1 base08 := by decide +kernel
theorem eval_atom0112 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0112 = (quadB (outer g) ![2,2,1] * g 11 * g 12) := by
  rw [atom0112_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0112_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16773120 : Int) atom0112) := by
  rw [SparsePolynomial.eval_scale, eval_atom0112]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 11 * g 12) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0112Coded : CoefficientMerge.Poly := [(210, -8), (534, -12), (858, -16), (1182, -16), (1506, -16), (1830, -16), (2154, -16), (2478, -16), (2802, -16), (3126, -16), (3450, -16), (3774, -16), (3792, -14), (3793, -10), (3794, -2), (3795, 2), (3796, 10), (3797, 18)]
theorem atom0112Coded_decode : atom0112 = SparsePolynomial.decodeCubic 18 atom0112Coded := by decide +kernel
theorem atom0112Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (16773120 : Int) atom0112Coded) := by
  have h := atom0112_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0112Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0113 : SparsePolynomial.Poly := [([0,13,13], -8), ([1,13,13], -12), ([2,13,13], -16), ([3,13,13], -16), ([4,13,13], -16), ([5,13,13], -16), ([6,13,13], -16), ([7,13,13], -16), ([8,13,13], -16), ([9,13,13], -16), ([10,13,13], -16), ([11,13,13], -16), ([12,13,13], -14), ([13,13,13], -10), ([13,13,14], -2), ([13,13,15], 2), ([13,13,16], 10), ([13,13,17], 18)]
theorem atom0113_data : atom0113 = SparsePolynomial.monoTimes [13,13] 1 base08 := by decide +kernel
theorem eval_atom0113 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0113 = (quadB (outer g) ![2,2,1] * g 13 * g 13) := by
  rw [atom0113_data, SparsePolynomial.eval_monoTimes, eval_base08]
  norm_num [SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0113_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49932288 : Int) atom0113) := by
  rw [SparsePolynomial.eval_scale, eval_atom0113]
  have hg13 : 0 ≤ g 13 := hg 13
  have hb := base08_nonneg g hg hA hB
  rw [eval_base08] at hb
  have ht : 0 ≤ (quadB (outer g) ![2,2,1] * g 13 * g 13) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0113Coded : CoefficientMerge.Poly := [(247, -8), (571, -12), (895, -16), (1219, -16), (1543, -16), (1867, -16), (2191, -16), (2515, -16), (2839, -16), (3163, -16), (3487, -16), (3811, -16), (4135, -14), (4459, -10), (4460, -2), (4461, 2), (4462, 10), (4463, 18)]
theorem atom0113Coded_decode : atom0113 = SparsePolynomial.decodeCubic 18 atom0113Coded := by decide +kernel
theorem atom0113Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (49932288 : Int) atom0113Coded) := by
  have h := atom0113_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0113Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0114 : SparsePolynomial.Poly := [([0,0,12], 1)]
theorem eval_atom0114 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0114 = ((g 0) * (g 0) * (g 12)) := by
  norm_num [atom0114, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0114_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (409651200 : Int) atom0114) := by
  rw [SparsePolynomial.eval_scale, eval_atom0114]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 0) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0114Coded : CoefficientMerge.Poly := [(12, 1)]
theorem atom0114Coded_decode : atom0114 = SparsePolynomial.decodeCubic 18 atom0114Coded := by decide +kernel
theorem atom0114Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (409651200 : Int) atom0114Coded) := by
  have h := atom0114_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0114Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0115 : SparsePolynomial.Poly := [([0,0,13], 1)]
theorem eval_atom0115 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0115 = ((g 0) * (g 0) * (g 13)) := by
  norm_num [atom0115, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0115_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (305786880 : Int) atom0115) := by
  rw [SparsePolynomial.eval_scale, eval_atom0115]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 0) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0115Coded : CoefficientMerge.Poly := [(13, 1)]
theorem atom0115Coded_decode : atom0115 = SparsePolynomial.decodeCubic 18 atom0115Coded := by decide +kernel
theorem atom0115Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (305786880 : Int) atom0115Coded) := by
  have h := atom0115_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0115Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0116 : SparsePolynomial.Poly := [([0,0,14], 1)]
theorem eval_atom0116 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0116 = ((g 0) * (g 0) * (g 14)) := by
  norm_num [atom0116, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0116_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (201922560 : Int) atom0116) := by
  rw [SparsePolynomial.eval_scale, eval_atom0116]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 0) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0116Coded : CoefficientMerge.Poly := [(14, 1)]
theorem atom0116Coded_decode : atom0116 = SparsePolynomial.decodeCubic 18 atom0116Coded := by decide +kernel
theorem atom0116Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (201922560 : Int) atom0116Coded) := by
  have h := atom0116_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0116Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0117 : SparsePolynomial.Poly := [([0,0,15], 1)]
theorem eval_atom0117 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0117 = ((g 0) * (g 0) * (g 15)) := by
  norm_num [atom0117, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0117_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98058240 : Int) atom0117) := by
  rw [SparsePolynomial.eval_scale, eval_atom0117]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 0) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0117Coded : CoefficientMerge.Poly := [(15, 1)]
theorem atom0117Coded_decode : atom0117 = SparsePolynomial.decodeCubic 18 atom0117Coded := by decide +kernel
theorem atom0117Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (98058240 : Int) atom0117Coded) := by
  have h := atom0117_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0117Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0118 : SparsePolynomial.Poly := [([0,1,1], 1)]
theorem eval_atom0118 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0118 = ((g 0) * (g 1) * (g 1)) := by
  norm_num [atom0118, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0118_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (248236800 : Int) atom0118) := by
  rw [SparsePolynomial.eval_scale, eval_atom0118]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have ht : 0 ≤ ((g 0) * (g 1) * (g 1)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0118Coded : CoefficientMerge.Poly := [(19, 1)]
theorem atom0118Coded_decode : atom0118 = SparsePolynomial.decodeCubic 18 atom0118Coded := by decide +kernel
theorem atom0118Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (248236800 : Int) atom0118Coded) := by
  have h := atom0118_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0118Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0119 : SparsePolynomial.Poly := [([0,1,2], 1)]
theorem eval_atom0119 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0119 = ((g 0) * (g 1) * (g 2)) := by
  norm_num [atom0119, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0119_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1455068160 : Int) atom0119) := by
  rw [SparsePolynomial.eval_scale, eval_atom0119]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0119Coded : CoefficientMerge.Poly := [(20, 1)]
theorem atom0119Coded_decode : atom0119 = SparsePolynomial.decodeCubic 18 atom0119Coded := by decide +kernel
theorem atom0119Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1455068160 : Int) atom0119Coded) := by
  have h := atom0119_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0119Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0120 : SparsePolynomial.Poly := [([0,1,3], 1)]
theorem eval_atom0120 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0120 = ((g 0) * (g 1) * (g 3)) := by
  norm_num [atom0120, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0120_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1453455360 : Int) atom0120) := by
  rw [SparsePolynomial.eval_scale, eval_atom0120]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0120Coded : CoefficientMerge.Poly := [(21, 1)]
theorem atom0120Coded_decode : atom0120 = SparsePolynomial.decodeCubic 18 atom0120Coded := by decide +kernel
theorem atom0120Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1453455360 : Int) atom0120Coded) := by
  have h := atom0120_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0120Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0121 : SparsePolynomial.Poly := [([0,1,4], 1)]
theorem eval_atom0121 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0121 = ((g 0) * (g 1) * (g 4)) := by
  norm_num [atom0121, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0121_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1451842560 : Int) atom0121) := by
  rw [SparsePolynomial.eval_scale, eval_atom0121]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0121Coded : CoefficientMerge.Poly := [(22, 1)]
theorem atom0121Coded_decode : atom0121 = SparsePolynomial.decodeCubic 18 atom0121Coded := by decide +kernel
theorem atom0121Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1451842560 : Int) atom0121Coded) := by
  have h := atom0121_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0121Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0122 : SparsePolynomial.Poly := [([0,1,5], 1)]
theorem eval_atom0122 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0122 = ((g 0) * (g 1) * (g 5)) := by
  norm_num [atom0122, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0122_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1450229760 : Int) atom0122) := by
  rw [SparsePolynomial.eval_scale, eval_atom0122]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0122Coded : CoefficientMerge.Poly := [(23, 1)]
theorem atom0122Coded_decode : atom0122 = SparsePolynomial.decodeCubic 18 atom0122Coded := by decide +kernel
theorem atom0122Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1450229760 : Int) atom0122Coded) := by
  have h := atom0122_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0122Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0123 : SparsePolynomial.Poly := [([0,1,6], 1)]
theorem eval_atom0123 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0123 = ((g 0) * (g 1) * (g 6)) := by
  norm_num [atom0123, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0123_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1448616960 : Int) atom0123) := by
  rw [SparsePolynomial.eval_scale, eval_atom0123]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0123Coded : CoefficientMerge.Poly := [(24, 1)]
theorem atom0123Coded_decode : atom0123 = SparsePolynomial.decodeCubic 18 atom0123Coded := by decide +kernel
theorem atom0123Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1448616960 : Int) atom0123Coded) := by
  have h := atom0123_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0123Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0124 : SparsePolynomial.Poly := [([0,1,7], 1)]
theorem eval_atom0124 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0124 = ((g 0) * (g 1) * (g 7)) := by
  norm_num [atom0124, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0124_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1447004160 : Int) atom0124) := by
  rw [SparsePolynomial.eval_scale, eval_atom0124]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 1) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0124Coded : CoefficientMerge.Poly := [(25, 1)]
theorem atom0124Coded_decode : atom0124 = SparsePolynomial.decodeCubic 18 atom0124Coded := by decide +kernel
theorem atom0124Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1447004160 : Int) atom0124Coded) := by
  have h := atom0124_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0124Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0125 : SparsePolynomial.Poly := [([0,1,8], 1)]
theorem eval_atom0125 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0125 = ((g 0) * (g 1) * (g 8)) := by
  norm_num [atom0125, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0125_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1471008000 : Int) atom0125) := by
  rw [SparsePolynomial.eval_scale, eval_atom0125]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 1) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0125Coded : CoefficientMerge.Poly := [(26, 1)]
theorem atom0125Coded_decode : atom0125 = SparsePolynomial.decodeCubic 18 atom0125Coded := by decide +kernel
theorem atom0125Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1471008000 : Int) atom0125Coded) := by
  have h := atom0125_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0125Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0126 : SparsePolynomial.Poly := [([0,1,9], 1)]
theorem eval_atom0126 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0126 = ((g 0) * (g 1) * (g 9)) := by
  norm_num [atom0126, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0126_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1464879360 : Int) atom0126) := by
  rw [SparsePolynomial.eval_scale, eval_atom0126]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 1) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0126Coded : CoefficientMerge.Poly := [(27, 1)]
theorem atom0126Coded_decode : atom0126 = SparsePolynomial.decodeCubic 18 atom0126Coded := by decide +kernel
theorem atom0126Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1464879360 : Int) atom0126Coded) := by
  have h := atom0126_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0126Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0127 : SparsePolynomial.Poly := [([0,1,10], 1)]
theorem eval_atom0127 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0127 = ((g 0) * (g 1) * (g 10)) := by
  norm_num [atom0127, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0127_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1471330560 : Int) atom0127) := by
  rw [SparsePolynomial.eval_scale, eval_atom0127]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 1) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0127Coded : CoefficientMerge.Poly := [(28, 1)]
theorem atom0127Coded_decode : atom0127 = SparsePolynomial.decodeCubic 18 atom0127Coded := by decide +kernel
theorem atom0127Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1471330560 : Int) atom0127Coded) := by
  have h := atom0127_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0127Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0128 : SparsePolynomial.Poly := [([0,1,11], 1)]
theorem eval_atom0128 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0128 = ((g 0) * (g 1) * (g 11)) := by
  norm_num [atom0128, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0128_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1512465920 : Int) atom0128) := by
  rw [SparsePolynomial.eval_scale, eval_atom0128]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 1) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0128Coded : CoefficientMerge.Poly := [(29, 1)]
theorem atom0128Coded_decode : atom0128 = SparsePolynomial.decodeCubic 18 atom0128Coded := by decide +kernel
theorem atom0128Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1512465920 : Int) atom0128Coded) := by
  have h := atom0128_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0128Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0129 : SparsePolynomial.Poly := [([0,1,12], 1)]
theorem eval_atom0129 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0129 = ((g 0) * (g 1) * (g 12)) := by
  norm_num [atom0129, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0129_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2885621760 : Int) atom0129) := by
  rw [SparsePolynomial.eval_scale, eval_atom0129]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 1) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0129Coded : CoefficientMerge.Poly := [(30, 1)]
theorem atom0129Coded_decode : atom0129 = SparsePolynomial.decodeCubic 18 atom0129Coded := by decide +kernel
theorem atom0129Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2885621760 : Int) atom0129Coded) := by
  have h := atom0129_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0129Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0130 : SparsePolynomial.Poly := [([0,1,13], 1)]
theorem eval_atom0130 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0130 = ((g 0) * (g 1) * (g 13)) := by
  norm_num [atom0130, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0130_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1132241600 : Int) atom0130) := by
  rw [SparsePolynomial.eval_scale, eval_atom0130]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 1) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0130Coded : CoefficientMerge.Poly := [(31, 1)]
theorem atom0130Coded_decode : atom0130 = SparsePolynomial.decodeCubic 18 atom0130Coded := by decide +kernel
theorem atom0130Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1132241600 : Int) atom0130Coded) := by
  have h := atom0130_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0130Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0131 : SparsePolynomial.Poly := [([0,1,14], 1)]
theorem eval_atom0131 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0131 = ((g 0) * (g 1) * (g 14)) := by
  norm_num [atom0131, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0131_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (457390080 : Int) atom0131) := by
  rw [SparsePolynomial.eval_scale, eval_atom0131]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 1) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0131Coded : CoefficientMerge.Poly := [(32, 1)]
theorem atom0131Coded_decode : atom0131 = SparsePolynomial.decodeCubic 18 atom0131Coded := by decide +kernel
theorem atom0131Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (457390080 : Int) atom0131Coded) := by
  have h := atom0131_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0131Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0132 : SparsePolynomial.Poly := [([0,1,15], 1)]
theorem eval_atom0132 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0132 = ((g 0) * (g 1) * (g 15)) := by
  norm_num [atom0132, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0132_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (225565760 : Int) atom0132) := by
  rw [SparsePolynomial.eval_scale, eval_atom0132]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 1) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0132Coded : CoefficientMerge.Poly := [(33, 1)]
theorem atom0132Coded_decode : atom0132 = SparsePolynomial.decodeCubic 18 atom0132Coded := by decide +kernel
theorem atom0132Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (225565760 : Int) atom0132Coded) := by
  have h := atom0132_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0132Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0133 : SparsePolynomial.Poly := [([0,1,16], 1)]
theorem eval_atom0133 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0133 = ((g 0) * (g 1) * (g 16)) := by
  norm_num [atom0133, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0133_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (180255040 : Int) atom0133) := by
  rw [SparsePolynomial.eval_scale, eval_atom0133]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 1) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0133Coded : CoefficientMerge.Poly := [(34, 1)]
theorem atom0133Coded_decode : atom0133 = SparsePolynomial.decodeCubic 18 atom0133Coded := by decide +kernel
theorem atom0133Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (180255040 : Int) atom0133Coded) := by
  have h := atom0133_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0133Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0134 : SparsePolynomial.Poly := [([0,2,2], 1)]
theorem eval_atom0134 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0134 = ((g 0) * (g 2) * (g 2)) := by
  norm_num [atom0134, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0134_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1619251200 : Int) atom0134) := by
  rw [SparsePolynomial.eval_scale, eval_atom0134]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0134Coded : CoefficientMerge.Poly := [(38, 1)]
theorem atom0134Coded_decode : atom0134 = SparsePolynomial.decodeCubic 18 atom0134Coded := by decide +kernel
theorem atom0134Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1619251200 : Int) atom0134Coded) := by
  have h := atom0134_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0134Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0135 : SparsePolynomial.Poly := [([0,2,3], 1)]
theorem eval_atom0135 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0135 = ((g 0) * (g 2) * (g 3)) := by
  norm_num [atom0135, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0135_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3339141120 : Int) atom0135) := by
  rw [SparsePolynomial.eval_scale, eval_atom0135]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0135Coded : CoefficientMerge.Poly := [(39, 1)]
theorem atom0135Coded_decode : atom0135 = SparsePolynomial.decodeCubic 18 atom0135Coded := by decide +kernel
theorem atom0135Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3339141120 : Int) atom0135Coded) := by
  have h := atom0135_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0135Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0136 : SparsePolynomial.Poly := [([0,2,4], 1)]
theorem eval_atom0136 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0136 = ((g 0) * (g 2) * (g 4)) := by
  norm_num [atom0136, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0136_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3439779840 : Int) atom0136) := by
  rw [SparsePolynomial.eval_scale, eval_atom0136]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0136Coded : CoefficientMerge.Poly := [(40, 1)]
theorem atom0136Coded_decode : atom0136 = SparsePolynomial.decodeCubic 18 atom0136Coded := by decide +kernel
theorem atom0136Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3439779840 : Int) atom0136Coded) := by
  have h := atom0136_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0136Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0137 : SparsePolynomial.Poly := [([0,2,5], 1)]
theorem eval_atom0137 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0137 = ((g 0) * (g 2) * (g 5)) := by
  norm_num [atom0137, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0137_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3540418560 : Int) atom0137) := by
  rw [SparsePolynomial.eval_scale, eval_atom0137]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0137Coded : CoefficientMerge.Poly := [(41, 1)]
theorem atom0137Coded_decode : atom0137 = SparsePolynomial.decodeCubic 18 atom0137Coded := by decide +kernel
theorem atom0137Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3540418560 : Int) atom0137Coded) := by
  have h := atom0137_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0137Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0138 : SparsePolynomial.Poly := [([0,2,6], 1)]
theorem eval_atom0138 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0138 = ((g 0) * (g 2) * (g 6)) := by
  norm_num [atom0138, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0138_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3641057280 : Int) atom0138) := by
  rw [SparsePolynomial.eval_scale, eval_atom0138]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0138Coded : CoefficientMerge.Poly := [(42, 1)]
theorem atom0138Coded_decode : atom0138 = SparsePolynomial.decodeCubic 18 atom0138Coded := by decide +kernel
theorem atom0138Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3641057280 : Int) atom0138Coded) := by
  have h := atom0138_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0138Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0139 : SparsePolynomial.Poly := [([0,2,7], 1)]
theorem eval_atom0139 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0139 = ((g 0) * (g 2) * (g 7)) := by
  norm_num [atom0139, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0139_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3741696000 : Int) atom0139) := by
  rw [SparsePolynomial.eval_scale, eval_atom0139]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0139Coded : CoefficientMerge.Poly := [(43, 1)]
theorem atom0139Coded_decode : atom0139 = SparsePolynomial.decodeCubic 18 atom0139Coded := by decide +kernel
theorem atom0139Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3741696000 : Int) atom0139Coded) := by
  have h := atom0139_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0139Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0140 : SparsePolynomial.Poly := [([0,2,8], 1)]
theorem eval_atom0140 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0140 = ((g 0) * (g 2) * (g 8)) := by
  norm_num [atom0140, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0140_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3842334720 : Int) atom0140) := by
  rw [SparsePolynomial.eval_scale, eval_atom0140]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0140Coded : CoefficientMerge.Poly := [(44, 1)]
theorem atom0140Coded_decode : atom0140 = SparsePolynomial.decodeCubic 18 atom0140Coded := by decide +kernel
theorem atom0140Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3842334720 : Int) atom0140Coded) := by
  have h := atom0140_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0140Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0141 : SparsePolynomial.Poly := [([0,2,9], 1)]
theorem eval_atom0141 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0141 = ((g 0) * (g 2) * (g 9)) := by
  norm_num [atom0141, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0141_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3942973440 : Int) atom0141) := by
  rw [SparsePolynomial.eval_scale, eval_atom0141]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0141Coded : CoefficientMerge.Poly := [(45, 1)]
theorem atom0141Coded_decode : atom0141 = SparsePolynomial.decodeCubic 18 atom0141Coded := by decide +kernel
theorem atom0141Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3942973440 : Int) atom0141Coded) := by
  have h := atom0141_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0141Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0142 : SparsePolynomial.Poly := [([0,2,10], 1)]
theorem eval_atom0142 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0142 = ((g 0) * (g 2) * (g 10)) := by
  norm_num [atom0142, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0142_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4043612160 : Int) atom0142) := by
  rw [SparsePolynomial.eval_scale, eval_atom0142]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0142Coded : CoefficientMerge.Poly := [(46, 1)]
theorem atom0142Coded_decode : atom0142 = SparsePolynomial.decodeCubic 18 atom0142Coded := by decide +kernel
theorem atom0142Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4043612160 : Int) atom0142Coded) := by
  have h := atom0142_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0142Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0143 : SparsePolynomial.Poly := [([0,2,11], 1)]
theorem eval_atom0143 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0143 = ((g 0) * (g 2) * (g 11)) := by
  norm_num [atom0143, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0143_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4144250880 : Int) atom0143) := by
  rw [SparsePolynomial.eval_scale, eval_atom0143]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0143Coded : CoefficientMerge.Poly := [(47, 1)]
theorem atom0143Coded_decode : atom0143 = SparsePolynomial.decodeCubic 18 atom0143Coded := by decide +kernel
theorem atom0143Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4144250880 : Int) atom0143Coded) := by
  have h := atom0143_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0143Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0144 : SparsePolynomial.Poly := [([0,2,12], 1)]
theorem eval_atom0144 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0144 = ((g 0) * (g 2) * (g 12)) := by
  norm_num [atom0144, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0144_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4982100480 : Int) atom0144) := by
  rw [SparsePolynomial.eval_scale, eval_atom0144]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0144Coded : CoefficientMerge.Poly := [(48, 1)]
theorem atom0144Coded_decode : atom0144 = SparsePolynomial.decodeCubic 18 atom0144Coded := by decide +kernel
theorem atom0144Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4982100480 : Int) atom0144Coded) := by
  have h := atom0144_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0144Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0145 : SparsePolynomial.Poly := [([0,2,13], 1)]
theorem eval_atom0145 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0145 = ((g 0) * (g 2) * (g 13)) := by
  norm_num [atom0145, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0145_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2934167040 : Int) atom0145) := by
  rw [SparsePolynomial.eval_scale, eval_atom0145]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0145Coded : CoefficientMerge.Poly := [(49, 1)]
theorem atom0145Coded_decode : atom0145 = SparsePolynomial.decodeCubic 18 atom0145Coded := by decide +kernel
theorem atom0145Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2934167040 : Int) atom0145Coded) := by
  have h := atom0145_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0145Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0146 : SparsePolynomial.Poly := [([0,2,14], 1)]
theorem eval_atom0146 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0146 = ((g 0) * (g 2) * (g 14)) := by
  norm_num [atom0146, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0146_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2444907240 : Int) atom0146) := by
  rw [SparsePolynomial.eval_scale, eval_atom0146]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0146Coded : CoefficientMerge.Poly := [(50, 1)]
theorem atom0146Coded_decode : atom0146 = SparsePolynomial.decodeCubic 18 atom0146Coded := by decide +kernel
theorem atom0146Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2444907240 : Int) atom0146Coded) := by
  have h := atom0146_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0146Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0147 : SparsePolynomial.Poly := [([0,2,15], 1)]
theorem eval_atom0147 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0147 = ((g 0) * (g 2) * (g 15)) := by
  norm_num [atom0147, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0147_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (450777600 : Int) atom0147) := by
  rw [SparsePolynomial.eval_scale, eval_atom0147]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 2) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0147Coded : CoefficientMerge.Poly := [(51, 1)]
theorem atom0147Coded_decode : atom0147 = SparsePolynomial.decodeCubic 18 atom0147Coded := by decide +kernel
theorem atom0147Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (450777600 : Int) atom0147Coded) := by
  have h := atom0147_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0147Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0148 : SparsePolynomial.Poly := [([0,2,16], 1)]
theorem eval_atom0148 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0148 = ((g 0) * (g 2) * (g 16)) := by
  norm_num [atom0148, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0148_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (643184640 : Int) atom0148) := by
  rw [SparsePolynomial.eval_scale, eval_atom0148]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 2) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0148Coded : CoefficientMerge.Poly := [(52, 1)]
theorem atom0148Coded_decode : atom0148 = SparsePolynomial.decodeCubic 18 atom0148Coded := by decide +kernel
theorem atom0148Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (643184640 : Int) atom0148Coded) := by
  have h := atom0148_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0148Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0149 : SparsePolynomial.Poly := [([0,3,3], 1)]
theorem eval_atom0149 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0149 = ((g 0) * (g 3) * (g 3)) := by
  norm_num [atom0149, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0149_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1616025600 : Int) atom0149) := by
  rw [SparsePolynomial.eval_scale, eval_atom0149]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0149Coded : CoefficientMerge.Poly := [(57, 1)]
theorem atom0149Coded_decode : atom0149 = SparsePolynomial.decodeCubic 18 atom0149Coded := by decide +kernel
theorem atom0149Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1616025600 : Int) atom0149Coded) := by
  have h := atom0149_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0149Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0150 : SparsePolynomial.Poly := [([0,3,4], 1)]
theorem eval_atom0150 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0150 = ((g 0) * (g 3) * (g 4)) := by
  norm_num [atom0150, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0150_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3383009280 : Int) atom0150) := by
  rw [SparsePolynomial.eval_scale, eval_atom0150]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0150Coded : CoefficientMerge.Poly := [(58, 1)]
theorem atom0150Coded_decode : atom0150 = SparsePolynomial.decodeCubic 18 atom0150Coded := by decide +kernel
theorem atom0150Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3383009280 : Int) atom0150Coded) := by
  have h := atom0150_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0150Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0151 : SparsePolynomial.Poly := [([0,3,5], 1)]
theorem eval_atom0151 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0151 = ((g 0) * (g 3) * (g 5)) := by
  norm_num [atom0151, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0151_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3533967360 : Int) atom0151) := by
  rw [SparsePolynomial.eval_scale, eval_atom0151]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0151Coded : CoefficientMerge.Poly := [(59, 1)]
theorem atom0151Coded_decode : atom0151 = SparsePolynomial.decodeCubic 18 atom0151Coded := by decide +kernel
theorem atom0151Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3533967360 : Int) atom0151Coded) := by
  have h := atom0151_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0151Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0152 : SparsePolynomial.Poly := [([0,3,6], 1)]
theorem eval_atom0152 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0152 = ((g 0) * (g 3) * (g 6)) := by
  norm_num [atom0152, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0152_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3684925440 : Int) atom0152) := by
  rw [SparsePolynomial.eval_scale, eval_atom0152]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0152Coded : CoefficientMerge.Poly := [(60, 1)]
theorem atom0152Coded_decode : atom0152 = SparsePolynomial.decodeCubic 18 atom0152Coded := by decide +kernel
theorem atom0152Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3684925440 : Int) atom0152Coded) := by
  have h := atom0152_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0152Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0153 : SparsePolynomial.Poly := [([0,3,7], 1)]
theorem eval_atom0153 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0153 = ((g 0) * (g 3) * (g 7)) := by
  norm_num [atom0153, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0153_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3835883520 : Int) atom0153) := by
  rw [SparsePolynomial.eval_scale, eval_atom0153]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0153Coded : CoefficientMerge.Poly := [(61, 1)]
theorem atom0153Coded_decode : atom0153 = SparsePolynomial.decodeCubic 18 atom0153Coded := by decide +kernel
theorem atom0153Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3835883520 : Int) atom0153Coded) := by
  have h := atom0153_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0153Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0154 : SparsePolynomial.Poly := [([0,3,8], 1)]
theorem eval_atom0154 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0154 = ((g 0) * (g 3) * (g 8)) := by
  norm_num [atom0154, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0154_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3986841600 : Int) atom0154) := by
  rw [SparsePolynomial.eval_scale, eval_atom0154]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0154Coded : CoefficientMerge.Poly := [(62, 1)]
theorem atom0154Coded_decode : atom0154 = SparsePolynomial.decodeCubic 18 atom0154Coded := by decide +kernel
theorem atom0154Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3986841600 : Int) atom0154Coded) := by
  have h := atom0154_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0154Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0155 : SparsePolynomial.Poly := [([0,3,9], 1)]
theorem eval_atom0155 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0155 = ((g 0) * (g 3) * (g 9)) := by
  norm_num [atom0155, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0155_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4137799680 : Int) atom0155) := by
  rw [SparsePolynomial.eval_scale, eval_atom0155]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0155Coded : CoefficientMerge.Poly := [(63, 1)]
theorem atom0155Coded_decode : atom0155 = SparsePolynomial.decodeCubic 18 atom0155Coded := by decide +kernel
theorem atom0155Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4137799680 : Int) atom0155Coded) := by
  have h := atom0155_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0155Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0156 : SparsePolynomial.Poly := [([0,3,10], 1)]
theorem eval_atom0156 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0156 = ((g 0) * (g 3) * (g 10)) := by
  norm_num [atom0156, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0156_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4288757760 : Int) atom0156) := by
  rw [SparsePolynomial.eval_scale, eval_atom0156]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0156Coded : CoefficientMerge.Poly := [(64, 1)]
theorem atom0156Coded_decode : atom0156 = SparsePolynomial.decodeCubic 18 atom0156Coded := by decide +kernel
theorem atom0156Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4288757760 : Int) atom0156Coded) := by
  have h := atom0156_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0156Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0157 : SparsePolynomial.Poly := [([0,3,11], 1)]
theorem eval_atom0157 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0157 = ((g 0) * (g 3) * (g 11)) := by
  norm_num [atom0157, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0157_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4480035840 : Int) atom0157) := by
  rw [SparsePolynomial.eval_scale, eval_atom0157]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0157Coded : CoefficientMerge.Poly := [(65, 1)]
theorem atom0157Coded_decode : atom0157 = SparsePolynomial.decodeCubic 18 atom0157Coded := by decide +kernel
theorem atom0157Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4480035840 : Int) atom0157Coded) := by
  have h := atom0157_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0157Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0158 : SparsePolynomial.Poly := [([0,3,12], 1)]
theorem eval_atom0158 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0158 = ((g 0) * (g 3) * (g 12)) := by
  norm_num [atom0158, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0158_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5301918720 : Int) atom0158) := by
  rw [SparsePolynomial.eval_scale, eval_atom0158]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0158Coded : CoefficientMerge.Poly := [(66, 1)]
theorem atom0158Coded_decode : atom0158 = SparsePolynomial.decodeCubic 18 atom0158Coded := by decide +kernel
theorem atom0158Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5301918720 : Int) atom0158Coded) := by
  have h := atom0158_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0158Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0159 : SparsePolynomial.Poly := [([0,3,13], 1)]
theorem eval_atom0159 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0159 = ((g 0) * (g 3) * (g 13)) := by
  norm_num [atom0159, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0159_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3349463040 : Int) atom0159) := by
  rw [SparsePolynomial.eval_scale, eval_atom0159]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0159Coded : CoefficientMerge.Poly := [(67, 1)]
theorem atom0159Coded_decode : atom0159 = SparsePolynomial.decodeCubic 18 atom0159Coded := by decide +kernel
theorem atom0159Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3349463040 : Int) atom0159Coded) := by
  have h := atom0159_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0159Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0160 : SparsePolynomial.Poly := [([0,3,14], 1)]
theorem eval_atom0160 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0160 = ((g 0) * (g 3) * (g 14)) := by
  norm_num [atom0160, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0160_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2709567720 : Int) atom0160) := by
  rw [SparsePolynomial.eval_scale, eval_atom0160]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0160Coded : CoefficientMerge.Poly := [(68, 1)]
theorem atom0160Coded_decode : atom0160 = SparsePolynomial.decodeCubic 18 atom0160Coded := by decide +kernel
theorem atom0160Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2709567720 : Int) atom0160Coded) := by
  have h := atom0160_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0160Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0161 : SparsePolynomial.Poly := [([0,3,15], 1)]
theorem eval_atom0161 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0161 = ((g 0) * (g 3) * (g 15)) := by
  norm_num [atom0161, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0161_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (867686400 : Int) atom0161) := by
  rw [SparsePolynomial.eval_scale, eval_atom0161]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 0) * (g 3) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0161Coded : CoefficientMerge.Poly := [(69, 1)]
theorem atom0161Coded_decode : atom0161 = SparsePolynomial.decodeCubic 18 atom0161Coded := by decide +kernel
theorem atom0161Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (867686400 : Int) atom0161Coded) := by
  have h := atom0161_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0161Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0162 : SparsePolynomial.Poly := [([0,3,16], 1)]
theorem eval_atom0162 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0162 = ((g 0) * (g 3) * (g 16)) := by
  norm_num [atom0162, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0162_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1104122880 : Int) atom0162) := by
  rw [SparsePolynomial.eval_scale, eval_atom0162]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 0) * (g 3) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0162Coded : CoefficientMerge.Poly := [(70, 1)]
theorem atom0162Coded_decode : atom0162 = SparsePolynomial.decodeCubic 18 atom0162Coded := by decide +kernel
theorem atom0162Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1104122880 : Int) atom0162Coded) := by
  have h := atom0162_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0162Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0163 : SparsePolynomial.Poly := [([0,3,17], 1)]
theorem eval_atom0163 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0163 = ((g 0) * (g 3) * (g 17)) := by
  norm_num [atom0163, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0163_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56125440 : Int) atom0163) := by
  rw [SparsePolynomial.eval_scale, eval_atom0163]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 0) * (g 3) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0163Coded : CoefficientMerge.Poly := [(71, 1)]
theorem atom0163Coded_decode : atom0163 = SparsePolynomial.decodeCubic 18 atom0163Coded := by decide +kernel
theorem atom0163Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (56125440 : Int) atom0163Coded) := by
  have h := atom0163_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0163Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0164 : SparsePolynomial.Poly := [([0,4,4], 1)]
theorem eval_atom0164 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0164 = ((g 0) * (g 4) * (g 4)) := by
  norm_num [atom0164, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0164_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2283267840 : Int) atom0164) := by
  rw [SparsePolynomial.eval_scale, eval_atom0164]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0164Coded : CoefficientMerge.Poly := [(76, 1)]
theorem atom0164Coded_decode : atom0164 = SparsePolynomial.decodeCubic 18 atom0164Coded := by decide +kernel
theorem atom0164Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2283267840 : Int) atom0164Coded) := by
  have h := atom0164_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0164Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0165 : SparsePolynomial.Poly := [([0,4,5], 1)]
theorem eval_atom0165 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0165 = ((g 0) * (g 4) * (g 5)) := by
  norm_num [atom0165, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0165_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3957442368 : Int) atom0165) := by
  rw [SparsePolynomial.eval_scale, eval_atom0165]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0165Coded : CoefficientMerge.Poly := [(77, 1)]
theorem atom0165Coded_decode : atom0165 = SparsePolynomial.decodeCubic 18 atom0165Coded := by decide +kernel
theorem atom0165Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3957442368 : Int) atom0165Coded) := by
  have h := atom0165_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0165Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0166 : SparsePolynomial.Poly := [([0,4,6], 1)]
theorem eval_atom0166 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0166 = ((g 0) * (g 4) * (g 6)) := by
  norm_num [atom0166, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0166_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3881051040 : Int) atom0166) := by
  rw [SparsePolynomial.eval_scale, eval_atom0166]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0166Coded : CoefficientMerge.Poly := [(78, 1)]
theorem atom0166Coded_decode : atom0166 = SparsePolynomial.decodeCubic 18 atom0166Coded := by decide +kernel
theorem atom0166Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3881051040 : Int) atom0166Coded) := by
  have h := atom0166_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0166Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0167 : SparsePolynomial.Poly := [([0,4,7], 1)]
theorem eval_atom0167 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0167 = ((g 0) * (g 4) * (g 7)) := by
  norm_num [atom0167, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0167_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3958523520 : Int) atom0167) := by
  rw [SparsePolynomial.eval_scale, eval_atom0167]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0167Coded : CoefficientMerge.Poly := [(79, 1)]
theorem atom0167Coded_decode : atom0167 = SparsePolynomial.decodeCubic 18 atom0167Coded := by decide +kernel
theorem atom0167Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3958523520 : Int) atom0167Coded) := by
  have h := atom0167_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0167Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0168 : SparsePolynomial.Poly := [([0,4,8], 1)]
theorem eval_atom0168 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0168 = ((g 0) * (g 4) * (g 8)) := by
  norm_num [atom0168, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0168_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4131348480 : Int) atom0168) := by
  rw [SparsePolynomial.eval_scale, eval_atom0168]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0168Coded : CoefficientMerge.Poly := [(80, 1)]
theorem atom0168Coded_decode : atom0168 = SparsePolynomial.decodeCubic 18 atom0168Coded := by decide +kernel
theorem atom0168Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4131348480 : Int) atom0168Coded) := by
  have h := atom0168_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0168Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0169 : SparsePolynomial.Poly := [([0,4,9], 1)]
theorem eval_atom0169 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0169 = ((g 0) * (g 4) * (g 9)) := by
  norm_num [atom0169, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0169_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4332625920 : Int) atom0169) := by
  rw [SparsePolynomial.eval_scale, eval_atom0169]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0169Coded : CoefficientMerge.Poly := [(81, 1)]
theorem atom0169Coded_decode : atom0169 = SparsePolynomial.decodeCubic 18 atom0169Coded := by decide +kernel
theorem atom0169Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4332625920 : Int) atom0169Coded) := by
  have h := atom0169_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0169Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0170 : SparsePolynomial.Poly := [([0,4,10], 1)]
theorem eval_atom0170 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0170 = ((g 0) * (g 4) * (g 10)) := by
  norm_num [atom0170, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0170_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4533903360 : Int) atom0170) := by
  rw [SparsePolynomial.eval_scale, eval_atom0170]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0170Coded : CoefficientMerge.Poly := [(82, 1)]
theorem atom0170Coded_decode : atom0170 = SparsePolynomial.decodeCubic 18 atom0170Coded := by decide +kernel
theorem atom0170Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4533903360 : Int) atom0170Coded) := by
  have h := atom0170_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0170Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0171 : SparsePolynomial.Poly := [([0,4,11], 1)]
theorem eval_atom0171 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0171 = ((g 0) * (g 4) * (g 11)) := by
  norm_num [atom0171, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0171_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4753795200 : Int) atom0171) := by
  rw [SparsePolynomial.eval_scale, eval_atom0171]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0171Coded : CoefficientMerge.Poly := [(83, 1)]
theorem atom0171Coded_decode : atom0171 = SparsePolynomial.decodeCubic 18 atom0171Coded := by decide +kernel
theorem atom0171Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4753795200 : Int) atom0171Coded) := by
  have h := atom0171_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0171Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0172 : SparsePolynomial.Poly := [([0,4,12], 1)]
theorem eval_atom0172 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0172 = ((g 0) * (g 4) * (g 12)) := by
  norm_num [atom0172, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0172_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5621736960 : Int) atom0172) := by
  rw [SparsePolynomial.eval_scale, eval_atom0172]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0172Coded : CoefficientMerge.Poly := [(84, 1)]
theorem atom0172Coded_decode : atom0172 = SparsePolynomial.decodeCubic 18 atom0172Coded := by decide +kernel
theorem atom0172Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5621736960 : Int) atom0172Coded) := by
  have h := atom0172_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0172Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0173 : SparsePolynomial.Poly := [([0,4,13], 1)]
theorem eval_atom0173 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0173 = ((g 0) * (g 4) * (g 13)) := by
  norm_num [atom0173, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0173_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3713534160 : Int) atom0173) := by
  rw [SparsePolynomial.eval_scale, eval_atom0173]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0173Coded : CoefficientMerge.Poly := [(85, 1)]
theorem atom0173Coded_decode : atom0173 = SparsePolynomial.decodeCubic 18 atom0173Coded := by decide +kernel
theorem atom0173Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3713534160 : Int) atom0173Coded) := by
  have h := atom0173_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0173Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0174 : SparsePolynomial.Poly := [([0,4,14], 1)]
theorem eval_atom0174 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0174 = ((g 0) * (g 4) * (g 14)) := by
  norm_num [atom0174, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0174_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2974228200 : Int) atom0174) := by
  rw [SparsePolynomial.eval_scale, eval_atom0174]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0174Coded : CoefficientMerge.Poly := [(86, 1)]
theorem atom0174Coded_decode : atom0174 = SparsePolynomial.decodeCubic 18 atom0174Coded := by decide +kernel
theorem atom0174Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2974228200 : Int) atom0174Coded) := by
  have h := atom0174_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0174Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block002 : CoefficientMerge.Poly := [(12, 409651200), (13, 305786880), (14, 201922560), (15, 98058240), (19, 248236800), (20, 1455068160), (21, 1453455360), (22, 1451842560), (23, 1450229760), (24, 1448616960), (25, 1447004160), (26, 1471008000), (27, 1464879360), (28, 1471330560), (29, 1512465920), (30, 2885621760), (31, 1132241600), (32, 457390080), (33, 225565760), (34, 180255040), (38, 1619251200), (39, 3339141120), (40, 3439779840), (41, 3540418560), (42, 3641057280), (43, 3741696000), (44, 3842334720), (45, 3942973440), (46, 4043612160), (47, 4144250880), (48, 4982100480), (49, 2934167040), (50, 2444907240), (51, 450777600), (52, 643184640), (53, -310464000), (57, 1616025600), (58, 3383009280), (59, 3533967360), (60, 3684925440), (61, 3835883520), (62, 3986841600), (63, 4137799680), (64, 4288757760), (65, 4480035840), (66, 5301918720), (67, 3349463040), (68, 2709567720), (69, 867686400), (70, 1104122880), (71, 56125440), (76, 1663119360), (77, 3888202752), (78, 3881051040), (79, 3958523520), (80, 4131348480), (81, 4332625920), (82, 4533903360), (83, 4753795200), (84, 5621736960), (85, 3713534160), (86, 2974228200), (95, -594961920), (96, -383054976), (115, -735155136), (133, -65115360), (134, -868108416), (152, -668292000), (153, -1507948800), (154, -85810944), (171, -1406941440), (172, -1628375040), (173, -373213440), (190, -1362865920), (191, -1775374080), (209, -1331527680), (210, -134184960), (247, -399458304), (377, -465696000), (400, -930222720), (401, -103859424), (419, -892442880), (420, -574582464), (439, -1102732704), (457, -97673040), (458, -1302162624), (476, -1002438000), (477, -2261923200), (478, -128716416), (495, -2110412160), (496, -2442562560), (497, -559820160), (514, -2044298880), (515, -2663061120), (533, -1997291520), (534, -201277440), (571, -599187456), (701, -620928000), (719, -620928000), (724, -1240296960), (725, -138479232), (737, -620928000), (743, -1189923840), (744, -766109952), (755, -620928000), (763, -1470310272), (773, -620928000), (781, -130230720), (782, -1736216832), (791, -620928000), (800, -1336584000), (801, -3015897600), (802, -171621888), (809, -620928000), (819, -2813882880), (820, -3256750080), (821, -746426880), (827, -620928000), (838, -2725731840), (839, -3550748160), (845, -620928000), (857, -2663055360), (858, -268369920), (863, -620928000), (881, -543312000), (895, -798916608), (899, -388080000), (917, -77616000), (935, 77616000), (953, 388080000), (971, 698544000), (1048, -1240296960), (1049, -138479232), (1067, -1189923840), (1068, -766109952), (1087, -1470310272), (1105, -130230720), (1106, -1736216832), (1124, -1336584000), (1125, -3015897600), (1126, -171621888), (1143, -2813882880), (1144, -3256750080), (1145, -746426880), (1162, -2725731840), (1163, -3550748160), (1181, -2663055360), (1182, -268369920), (1219, -798916608), (1372, -1240296960), (1373, -1378776192), (1374, -1240296960), (1375, -1240296960), (1376, -1240296960), (1377, -1240296960), (1378, -1240296960), (1379, -1240296960), (1380, -1085259840), (1381, -775185600), (1382, -155037120), (1383, 155037120), (1384, 775185600), (1385, 1395334080), (1391, -1328403072), (1392, -904589184), (1393, -138479232), (1394, -138479232), (1395, -138479232), (1396, -138479232), (1397, -138479232), (1398, -121169328), (1399, -86549520), (1400, -17309904), (1401, 17309904), (1402, 86549520), (1403, 155789136), (1411, -1470310272), (1429, -130230720), (1430, -1736216832), (1448, -1336584000), (1449, -3015897600), (1450, -171621888), (1467, -2813882880), (1468, -3256750080), (1469, -746426880), (1486, -2725731840), (1487, -3550748160), (1505, -2663055360), (1506, -268369920), (1543, -798916608), (1715, -1189923840), (1716, -1956033792), (1717, -1189923840), (1718, -1189923840), (1719, -1189923840), (1720, -1189923840), (1721, -1189923840), (1722, -1041183360), (1723, -743702400), (1724, -148740480), (1725, 148740480), (1726, 743702400), (1727, 1338664320), (1734, -766109952), (1735, -2236420224), (1736, -766109952), (1737, -766109952), (1738, -766109952), (1739, -766109952), (1740, -670346208), (1741, -478818720), (1742, -95763744), (1743, 95763744), (1744, 478818720), (1745, 861873696), (1753, -130230720), (1754, -1736216832), (1772, -1336584000), (1773, -3015897600), (1774, -171621888), (1791, -2813882880), (1792, -3256750080), (1793, -746426880), (1810, -2725731840), (1811, -3550748160), (1829, -2663055360), (1830, -268369920), (1867, -798916608), (2059, -1470310272), (2077, -1600540992), (2078, -3206527104), (2079, -1470310272), (2080, -1470310272), (2081, -1470310272), (2082, -1286521488), (2083, -918943920), (2084, -183788784), (2085, 183788784), (2086, 918943920), (2087, 1654099056), (2096, -1336584000), (2097, -3015897600), (2098, -171621888), (2115, -2813882880), (2116, -3256750080), (2117, -746426880), (2134, -2725731840), (2135, -3550748160), (2153, -2663055360), (2154, -268369920), (2191, -798916608), (2401, -130230720), (2402, -1866447552), (2403, -130230720), (2404, -130230720), (2405, -130230720), (2406, -113951880), (2407, -81394200), (2408, -16278840), (2409, 16278840), (2410, 81394200), (2411, 146509560), (2420, -3072800832), (2421, -4752114432), (2422, -1907838720), (2423, -1736216832), (2424, -1519189728), (2425, -1085135520), (2426, -217027104), (2427, 217027104), (2428, 1085135520), (2429, 1953243936), (2439, -2813882880), (2440, -3256750080), (2441, -746426880), (2458, -2725731840), (2459, -3550748160), (2477, -2663055360), (2478, -268369920), (2515, -798916608), (2744, -1336584000), (2745, -4352481600), (2746, -1508205888), (2747, -1336584000), (2748, -1169511000), (2749, -835365000), (2750, -167073000), (2751, 167073000), (2752, 835365000), (2753, 1503657000), (2763, -5829780480), (2764, -6444269568), (2765, -3762324480), (2766, -2638910400), (2767, -1884936000), (2768, -376987200), (2769, 376987200), (2770, 1884936000), (2771, 3392884800), (2782, -2897353728), (2783, -3722370048), (2784, -150169152), (2785, -107263680), (2786, -21452736), (2787, 21452736), (2788, 107263680), (2789, 193074624), (2801, -2663055360), (2802, -268369920), (2839, -798916608), (3087, -2813882880), (3088, -6070632960), (3089, -3560309760), (3090, -2462147520), (3091, -1758676800), (3092, -351735360), (3093, 351735360), (3094, 1758676800), (3095, 3165618240), (3106, -5982481920), (3107, -7553925120), (3108, -2849656320), (3109, -2035468800), (3110, -407093760), (3111, 407093760), (3112, 2035468800), (3113, 3663843840), (3125, -3409482240), (3126, -921493440), (3127, -466516800), (3128, -93303360), (3129, 93303360), (3130, 466516800), (3131, 839730240), (3163, -798916608), (3430, -2725731840), (3431, -6276480000), (3432, -2385015360), (3433, -1703582400), (3434, -340716480), (3435, 340716480), (3436, 1703582400), (3437, 3066448320), (3449, -6213803520), (3450, -3375274560), (3451, -2219217600), (3452, -443843520), (3453, 443843520), (3454, 2219217600), (3455, 3994591680), (3487, -798916608), (3773, -2663055360), (3774, -2598543360), (3775, -1664409600), (3776, -332881920), (3777, 332881920), (3778, 1664409600), (3779, 2995937280), (3792, -234823680), (3793, -167731200), (3794, -33546240), (3795, 33546240), (3796, 167731200), (3797, 301916160), (3811, -798916608), (4135, -699052032), (4459, -499322880), (4460, -99864576), (4461, 99864576), (4462, 499322880), (4463, 898781184)]
theorem block002_data : block002 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38808000 : Int) atom0095Coded) (CoefficientMerge.scale (77518560 : Int) atom0096Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8654952 : Int) atom0097Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74370240 : Int) atom0098Coded) (CoefficientMerge.scale (47881872 : Int) atom0099Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (91894392 : Int) atom0100Coded) (CoefficientMerge.scale (8139420 : Int) atom0101Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (108513552 : Int) atom0102Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83536500 : Int) atom0103Coded) (CoefficientMerge.scale (188493600 : Int) atom0104Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10726368 : Int) atom0105Coded) (CoefficientMerge.scale (175867680 : Int) atom0106Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (203546880 : Int) atom0107Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46651680 : Int) atom0108Coded) (CoefficientMerge.scale (170358240 : Int) atom0109Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (221921760 : Int) atom0110Coded) (CoefficientMerge.scale (166440960 : Int) atom0111Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16773120 : Int) atom0112Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49932288 : Int) atom0113Coded) (CoefficientMerge.scale (409651200 : Int) atom0114Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (305786880 : Int) atom0115Coded) (CoefficientMerge.scale (201922560 : Int) atom0116Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98058240 : Int) atom0117Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (248236800 : Int) atom0118Coded) (CoefficientMerge.scale (1455068160 : Int) atom0119Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1453455360 : Int) atom0120Coded) (CoefficientMerge.scale (1451842560 : Int) atom0121Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1450229760 : Int) atom0122Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1448616960 : Int) atom0123Coded) (CoefficientMerge.scale (1447004160 : Int) atom0124Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1471008000 : Int) atom0125Coded) (CoefficientMerge.scale (1464879360 : Int) atom0126Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1471330560 : Int) atom0127Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1512465920 : Int) atom0128Coded) (CoefficientMerge.scale (2885621760 : Int) atom0129Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1132241600 : Int) atom0130Coded) (CoefficientMerge.scale (457390080 : Int) atom0131Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (225565760 : Int) atom0132Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (180255040 : Int) atom0133Coded) (CoefficientMerge.scale (1619251200 : Int) atom0134Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3339141120 : Int) atom0135Coded) (CoefficientMerge.scale (3439779840 : Int) atom0136Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3540418560 : Int) atom0137Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3641057280 : Int) atom0138Coded) (CoefficientMerge.scale (3741696000 : Int) atom0139Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3842334720 : Int) atom0140Coded) (CoefficientMerge.scale (3942973440 : Int) atom0141Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4043612160 : Int) atom0142Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4144250880 : Int) atom0143Coded) (CoefficientMerge.scale (4982100480 : Int) atom0144Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2934167040 : Int) atom0145Coded) (CoefficientMerge.scale (2444907240 : Int) atom0146Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (450777600 : Int) atom0147Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (643184640 : Int) atom0148Coded) (CoefficientMerge.scale (1616025600 : Int) atom0149Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3383009280 : Int) atom0150Coded) (CoefficientMerge.scale (3533967360 : Int) atom0151Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3684925440 : Int) atom0152Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3835883520 : Int) atom0153Coded) (CoefficientMerge.scale (3986841600 : Int) atom0154Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4137799680 : Int) atom0155Coded) (CoefficientMerge.scale (4288757760 : Int) atom0156Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4480035840 : Int) atom0157Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5301918720 : Int) atom0158Coded) (CoefficientMerge.scale (3349463040 : Int) atom0159Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2709567720 : Int) atom0160Coded) (CoefficientMerge.scale (867686400 : Int) atom0161Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1104122880 : Int) atom0162Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56125440 : Int) atom0163Coded) (CoefficientMerge.scale (2283267840 : Int) atom0164Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3957442368 : Int) atom0165Coded) (CoefficientMerge.scale (3881051040 : Int) atom0166Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3958523520 : Int) atom0167Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4131348480 : Int) atom0168Coded) (CoefficientMerge.scale (4332625920 : Int) atom0169Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4533903360 : Int) atom0170Coded) (CoefficientMerge.scale (4753795200 : Int) atom0171Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5621736960 : Int) atom0172Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3713534160 : Int) atom0173Coded) (CoefficientMerge.scale (2974228200 : Int) atom0174Coded)))))))) := by decide +kernel
theorem block002_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) block002 := by
  rw [block002_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0095Coded_nonneg g hg hA hB) (atom0096Coded_nonneg g hg hA hB)) (add_nonneg (atom0097Coded_nonneg g hg hA hB) (add_nonneg (atom0098Coded_nonneg g hg hA hB) (atom0099Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0100Coded_nonneg g hg hA hB) (atom0101Coded_nonneg g hg hA hB)) (add_nonneg (atom0102Coded_nonneg g hg hA hB) (add_nonneg (atom0103Coded_nonneg g hg hA hB) (atom0104Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0105Coded_nonneg g hg hA hB) (atom0106Coded_nonneg g hg hA hB)) (add_nonneg (atom0107Coded_nonneg g hg hA hB) (add_nonneg (atom0108Coded_nonneg g hg hA hB) (atom0109Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0110Coded_nonneg g hg hA hB) (atom0111Coded_nonneg g hg hA hB)) (add_nonneg (atom0112Coded_nonneg g hg hA hB) (add_nonneg (atom0113Coded_nonneg g hg hA hB) (atom0114Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0115Coded_nonneg g hg hA hB) (atom0116Coded_nonneg g hg hA hB)) (add_nonneg (atom0117Coded_nonneg g hg hA hB) (add_nonneg (atom0118Coded_nonneg g hg hA hB) (atom0119Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0120Coded_nonneg g hg hA hB) (atom0121Coded_nonneg g hg hA hB)) (add_nonneg (atom0122Coded_nonneg g hg hA hB) (add_nonneg (atom0123Coded_nonneg g hg hA hB) (atom0124Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0125Coded_nonneg g hg hA hB) (atom0126Coded_nonneg g hg hA hB)) (add_nonneg (atom0127Coded_nonneg g hg hA hB) (add_nonneg (atom0128Coded_nonneg g hg hA hB) (atom0129Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0130Coded_nonneg g hg hA hB) (atom0131Coded_nonneg g hg hA hB)) (add_nonneg (atom0132Coded_nonneg g hg hA hB) (add_nonneg (atom0133Coded_nonneg g hg hA hB) (atom0134Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0135Coded_nonneg g hg hA hB) (atom0136Coded_nonneg g hg hA hB)) (add_nonneg (atom0137Coded_nonneg g hg hA hB) (add_nonneg (atom0138Coded_nonneg g hg hA hB) (atom0139Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0140Coded_nonneg g hg hA hB) (atom0141Coded_nonneg g hg hA hB)) (add_nonneg (atom0142Coded_nonneg g hg hA hB) (add_nonneg (atom0143Coded_nonneg g hg hA hB) (atom0144Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0145Coded_nonneg g hg hA hB) (atom0146Coded_nonneg g hg hA hB)) (add_nonneg (atom0147Coded_nonneg g hg hA hB) (add_nonneg (atom0148Coded_nonneg g hg hA hB) (atom0149Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0150Coded_nonneg g hg hA hB) (atom0151Coded_nonneg g hg hA hB)) (add_nonneg (atom0152Coded_nonneg g hg hA hB) (add_nonneg (atom0153Coded_nonneg g hg hA hB) (atom0154Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0155Coded_nonneg g hg hA hB) (atom0156Coded_nonneg g hg hA hB)) (add_nonneg (atom0157Coded_nonneg g hg hA hB) (add_nonneg (atom0158Coded_nonneg g hg hA hB) (atom0159Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0160Coded_nonneg g hg hA hB) (atom0161Coded_nonneg g hg hA hB)) (add_nonneg (atom0162Coded_nonneg g hg hA hB) (add_nonneg (atom0163Coded_nonneg g hg hA hB) (atom0164Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0165Coded_nonneg g hg hA hB) (atom0166Coded_nonneg g hg hA hB)) (add_nonneg (atom0167Coded_nonneg g hg hA hB) (add_nonneg (atom0168Coded_nonneg g hg hA hB) (atom0169Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0170Coded_nonneg g hg hA hB) (atom0171Coded_nonneg g hg hA hB)) (add_nonneg (atom0172Coded_nonneg g hg hA hB) (add_nonneg (atom0173Coded_nonneg g hg hA hB) (atom0174Coded_nonneg g hg hA hB))))))))

end APPT.Finite18
