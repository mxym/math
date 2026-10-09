import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0896 : SparsePolynomial.Poly := [([3,13,18], 1)]
theorem eval_atom0896 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0896 = ((g 3) * (g 13) * (g 18)) := by
  norm_num [atom0896, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0896_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47411171942400 : Int) atom0896) := by
  rw [SparsePolynomial.eval_scale, eval_atom0896]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0896Coded : CoefficientMerge.Poly := [(1614, 1)]
theorem atom0896Coded_decode : atom0896 = SparsePolynomial.decodeCubic 21 atom0896Coded := by decide +kernel
theorem atom0896Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47411171942400 : Int) atom0896Coded) := by
  have h := atom0896_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0896Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0897 : SparsePolynomial.Poly := [([3,13,19], 1)]
theorem eval_atom0897 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0897 = ((g 3) * (g 13) * (g 19)) := by
  norm_num [atom0897, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0897_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44102287944000 : Int) atom0897) := by
  rw [SparsePolynomial.eval_scale, eval_atom0897]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0897Coded : CoefficientMerge.Poly := [(1615, 1)]
theorem atom0897Coded_decode : atom0897 = SparsePolynomial.decodeCubic 21 atom0897Coded := by decide +kernel
theorem atom0897Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44102287944000 : Int) atom0897Coded) := by
  have h := atom0897_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0897Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0898 : SparsePolynomial.Poly := [([3,13,20], 1)]
theorem eval_atom0898 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0898 = ((g 3) * (g 13) * (g 20)) := by
  norm_num [atom0898, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0898_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53975438899200 : Int) atom0898) := by
  rw [SparsePolynomial.eval_scale, eval_atom0898]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0898Coded : CoefficientMerge.Poly := [(1616, 1)]
theorem atom0898Coded_decode : atom0898 = SparsePolynomial.decodeCubic 21 atom0898Coded := by decide +kernel
theorem atom0898Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53975438899200 : Int) atom0898Coded) := by
  have h := atom0898_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0898Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0899 : SparsePolynomial.Poly := [([3,14,14], 1)]
theorem eval_atom0899 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0899 = ((g 3) * (g 14) * (g 14)) := by
  norm_num [atom0899, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0899_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26303458406400 : Int) atom0899) := by
  rw [SparsePolynomial.eval_scale, eval_atom0899]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0899Coded : CoefficientMerge.Poly := [(1631, 1)]
theorem atom0899Coded_decode : atom0899 = SparsePolynomial.decodeCubic 21 atom0899Coded := by decide +kernel
theorem atom0899Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26303458406400 : Int) atom0899Coded) := by
  have h := atom0899_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0899Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0900 : SparsePolynomial.Poly := [([3,14,15], 1)]
theorem eval_atom0900 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0900 = ((g 3) * (g 14) * (g 15)) := by
  norm_num [atom0900, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0900_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48520679961600 : Int) atom0900) := by
  rw [SparsePolynomial.eval_scale, eval_atom0900]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0900Coded : CoefficientMerge.Poly := [(1632, 1)]
theorem atom0900Coded_decode : atom0900 = SparsePolynomial.decodeCubic 21 atom0900Coded := by decide +kernel
theorem atom0900Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48520679961600 : Int) atom0900Coded) := by
  have h := atom0900_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0900Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0901 : SparsePolynomial.Poly := [([3,14,16], 1)]
theorem eval_atom0901 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0901 = ((g 3) * (g 14) * (g 16)) := by
  norm_num [atom0901, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0901_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39984813388800 : Int) atom0901) := by
  rw [SparsePolynomial.eval_scale, eval_atom0901]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0901Coded : CoefficientMerge.Poly := [(1633, 1)]
theorem atom0901Coded_decode : atom0901 = SparsePolynomial.decodeCubic 21 atom0901Coded := by decide +kernel
theorem atom0901Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39984813388800 : Int) atom0901Coded) := by
  have h := atom0901_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0901Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0902 : SparsePolynomial.Poly := [([3,14,17], 1)]
theorem eval_atom0902 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0902 = ((g 3) * (g 14) * (g 17)) := by
  norm_num [atom0902, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0902_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58281619737600 : Int) atom0902) := by
  rw [SparsePolynomial.eval_scale, eval_atom0902]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0902Coded : CoefficientMerge.Poly := [(1634, 1)]
theorem atom0902Coded_decode : atom0902 = SparsePolynomial.decodeCubic 21 atom0902Coded := by decide +kernel
theorem atom0902Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (58281619737600 : Int) atom0902Coded) := by
  have h := atom0902_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0902Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0903 : SparsePolynomial.Poly := [([3,14,18], 1)]
theorem eval_atom0903 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0903 = ((g 3) * (g 14) * (g 18)) := by
  norm_num [atom0903, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0903_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53383959014400 : Int) atom0903) := by
  rw [SparsePolynomial.eval_scale, eval_atom0903]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0903Coded : CoefficientMerge.Poly := [(1635, 1)]
theorem atom0903Coded_decode : atom0903 = SparsePolynomial.decodeCubic 21 atom0903Coded := by decide +kernel
theorem atom0903Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53383959014400 : Int) atom0903Coded) := by
  have h := atom0903_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0903Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0904 : SparsePolynomial.Poly := [([3,14,19], 1)]
theorem eval_atom0904 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0904 = ((g 3) * (g 14) * (g 19)) := by
  norm_num [atom0904, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0904_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44697323059200 : Int) atom0904) := by
  rw [SparsePolynomial.eval_scale, eval_atom0904]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0904Coded : CoefficientMerge.Poly := [(1636, 1)]
theorem atom0904Coded_decode : atom0904 = SparsePolynomial.decodeCubic 21 atom0904Coded := by decide +kernel
theorem atom0904Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44697323059200 : Int) atom0904Coded) := by
  have h := atom0904_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0904Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0905 : SparsePolynomial.Poly := [([3,14,20], 1)]
theorem eval_atom0905 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0905 = ((g 3) * (g 14) * (g 20)) := by
  norm_num [atom0905, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0905_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59921164800000 : Int) atom0905) := by
  rw [SparsePolynomial.eval_scale, eval_atom0905]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0905Coded : CoefficientMerge.Poly := [(1637, 1)]
theorem atom0905Coded_decode : atom0905 = SparsePolynomial.decodeCubic 21 atom0905Coded := by decide +kernel
theorem atom0905Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (59921164800000 : Int) atom0905Coded) := by
  have h := atom0905_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0905Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0906 : SparsePolynomial.Poly := [([3,15,15], 1)]
theorem eval_atom0906 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0906 = ((g 3) * (g 15) * (g 15)) := by
  norm_num [atom0906, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0906_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30559794048000 : Int) atom0906) := by
  rw [SparsePolynomial.eval_scale, eval_atom0906]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0906Coded : CoefficientMerge.Poly := [(1653, 1)]
theorem atom0906Coded_decode : atom0906 = SparsePolynomial.decodeCubic 21 atom0906Coded := by decide +kernel
theorem atom0906Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30559794048000 : Int) atom0906Coded) := by
  have h := atom0906_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0906Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0907 : SparsePolynomial.Poly := [([3,15,16], 1)]
theorem eval_atom0907 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0907 = ((g 3) * (g 15) * (g 16)) := by
  norm_num [atom0907, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0907_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52085022796800 : Int) atom0907) := by
  rw [SparsePolynomial.eval_scale, eval_atom0907]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0907Coded : CoefficientMerge.Poly := [(1654, 1)]
theorem atom0907Coded_decode : atom0907 = SparsePolynomial.decodeCubic 21 atom0907Coded := by decide +kernel
theorem atom0907Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52085022796800 : Int) atom0907Coded) := by
  have h := atom0907_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0907Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0908 : SparsePolynomial.Poly := [([3,15,17], 1)]
theorem eval_atom0908 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0908 = ((g 3) * (g 15) * (g 17)) := by
  norm_num [atom0908, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0908_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72395953459200 : Int) atom0908) := by
  rw [SparsePolynomial.eval_scale, eval_atom0908]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0908Coded : CoefficientMerge.Poly := [(1655, 1)]
theorem atom0908Coded_decode : atom0908 = SparsePolynomial.decodeCubic 21 atom0908Coded := by decide +kernel
theorem atom0908Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (72395953459200 : Int) atom0908Coded) := by
  have h := atom0908_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0908Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0909 : SparsePolynomial.Poly := [([3,15,18], 1)]
theorem eval_atom0909 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0909 = ((g 3) * (g 15) * (g 18)) := by
  norm_num [atom0909, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0909_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (66129770649600 : Int) atom0909) := by
  rw [SparsePolynomial.eval_scale, eval_atom0909]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0909Coded : CoefficientMerge.Poly := [(1656, 1)]
theorem atom0909Coded_decode : atom0909 = SparsePolynomial.decodeCubic 21 atom0909Coded := by decide +kernel
theorem atom0909Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (66129770649600 : Int) atom0909Coded) := by
  have h := atom0909_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0909Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0910 : SparsePolynomial.Poly := [([3,15,19], 1)]
theorem eval_atom0910 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0910 = ((g 3) * (g 15) * (g 19)) := by
  norm_num [atom0910, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0910_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43317203328000 : Int) atom0910) := by
  rw [SparsePolynomial.eval_scale, eval_atom0910]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0910Coded : CoefficientMerge.Poly := [(1657, 1)]
theorem atom0910Coded_decode : atom0910 = SparsePolynomial.decodeCubic 21 atom0910Coded := by decide +kernel
theorem atom0910Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43317203328000 : Int) atom0910Coded) := by
  have h := atom0910_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0910Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0911 : SparsePolynomial.Poly := [([3,15,20], 1)]
theorem eval_atom0911 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0911 = ((g 3) * (g 15) * (g 20)) := by
  norm_num [atom0911, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0911_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63125980646400 : Int) atom0911) := by
  rw [SparsePolynomial.eval_scale, eval_atom0911]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0911Coded : CoefficientMerge.Poly := [(1658, 1)]
theorem atom0911Coded_decode : atom0911 = SparsePolynomial.decodeCubic 21 atom0911Coded := by decide +kernel
theorem atom0911Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (63125980646400 : Int) atom0911Coded) := by
  have h := atom0911_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0911Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0912 : SparsePolynomial.Poly := [([3,16,16], 1)]
theorem eval_atom0912 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0912 = ((g 3) * (g 16) * (g 16)) := by
  norm_num [atom0912, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0912_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20924470748160 : Int) atom0912) := by
  rw [SparsePolynomial.eval_scale, eval_atom0912]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0912Coded : CoefficientMerge.Poly := [(1675, 1)]
theorem atom0912Coded_decode : atom0912 = SparsePolynomial.decodeCubic 21 atom0912Coded := by decide +kernel
theorem atom0912Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20924470748160 : Int) atom0912Coded) := by
  have h := atom0912_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0912Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0913 : SparsePolynomial.Poly := [([3,16,17], 1)]
theorem eval_atom0913 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0913 = ((g 3) * (g 16) * (g 17)) := by
  norm_num [atom0913, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0913_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58450854873600 : Int) atom0913) := by
  rw [SparsePolynomial.eval_scale, eval_atom0913]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0913Coded : CoefficientMerge.Poly := [(1676, 1)]
theorem atom0913Coded_decode : atom0913 = SparsePolynomial.decodeCubic 21 atom0913Coded := by decide +kernel
theorem atom0913Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (58450854873600 : Int) atom0913Coded) := by
  have h := atom0913_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0913Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0914 : SparsePolynomial.Poly := [([3,16,18], 1)]
theorem eval_atom0914 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0914 = ((g 3) * (g 16) * (g 18)) := by
  norm_num [atom0914, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0914_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58152523968000 : Int) atom0914) := by
  rw [SparsePolynomial.eval_scale, eval_atom0914]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0914Coded : CoefficientMerge.Poly := [(1677, 1)]
theorem atom0914Coded_decode : atom0914 = SparsePolynomial.decodeCubic 21 atom0914Coded := by decide +kernel
theorem atom0914Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (58152523968000 : Int) atom0914Coded) := by
  have h := atom0914_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0914Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0915 : SparsePolynomial.Poly := [([3,16,19], 1)]
theorem eval_atom0915 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0915 = ((g 3) * (g 16) * (g 19)) := by
  norm_num [atom0915, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0915_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40238672947200 : Int) atom0915) := by
  rw [SparsePolynomial.eval_scale, eval_atom0915]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0915Coded : CoefficientMerge.Poly := [(1678, 1)]
theorem atom0915Coded_decode : atom0915 = SparsePolynomial.decodeCubic 21 atom0915Coded := by decide +kernel
theorem atom0915Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40238672947200 : Int) atom0915Coded) := by
  have h := atom0915_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0915Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0916 : SparsePolynomial.Poly := [([3,16,20], 1)]
theorem eval_atom0916 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0916 = ((g 3) * (g 16) * (g 20)) := by
  norm_num [atom0916, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0916_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46263971577600 : Int) atom0916) := by
  rw [SparsePolynomial.eval_scale, eval_atom0916]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0916Coded : CoefficientMerge.Poly := [(1679, 1)]
theorem atom0916Coded_decode : atom0916 = SparsePolynomial.decodeCubic 21 atom0916Coded := by decide +kernel
theorem atom0916Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46263971577600 : Int) atom0916Coded) := by
  have h := atom0916_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0916Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0917 : SparsePolynomial.Poly := [([3,17,17], 1)]
theorem eval_atom0917 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0917 = ((g 3) * (g 17) * (g 17)) := by
  norm_num [atom0917, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0917_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39608547955200 : Int) atom0917) := by
  rw [SparsePolynomial.eval_scale, eval_atom0917]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0917Coded : CoefficientMerge.Poly := [(1697, 1)]
theorem atom0917Coded_decode : atom0917 = SparsePolynomial.decodeCubic 21 atom0917Coded := by decide +kernel
theorem atom0917Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39608547955200 : Int) atom0917Coded) := by
  have h := atom0917_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0917Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0918 : SparsePolynomial.Poly := [([3,17,18], 1)]
theorem eval_atom0918 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0918 = ((g 3) * (g 17) * (g 18)) := by
  norm_num [atom0918, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0918_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61172435520000 : Int) atom0918) := by
  rw [SparsePolynomial.eval_scale, eval_atom0918]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0918Coded : CoefficientMerge.Poly := [(1698, 1)]
theorem atom0918Coded_decode : atom0918 = SparsePolynomial.decodeCubic 21 atom0918Coded := by decide +kernel
theorem atom0918Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (61172435520000 : Int) atom0918Coded) := by
  have h := atom0918_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0918Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0919 : SparsePolynomial.Poly := [([3,17,19], 1)]
theorem eval_atom0919 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0919 = ((g 3) * (g 17) * (g 19)) := by
  norm_num [atom0919, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0919_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40507146086400 : Int) atom0919) := by
  rw [SparsePolynomial.eval_scale, eval_atom0919]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0919Coded : CoefficientMerge.Poly := [(1699, 1)]
theorem atom0919Coded_decode : atom0919 = SparsePolynomial.decodeCubic 21 atom0919Coded := by decide +kernel
theorem atom0919Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40507146086400 : Int) atom0919Coded) := by
  have h := atom0919_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0919Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0920 : SparsePolynomial.Poly := [([3,17,20], 1)]
theorem eval_atom0920 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0920 = ((g 3) * (g 17) * (g 20)) := by
  norm_num [atom0920, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0920_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51452745523200 : Int) atom0920) := by
  rw [SparsePolynomial.eval_scale, eval_atom0920]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0920Coded : CoefficientMerge.Poly := [(1700, 1)]
theorem atom0920Coded_decode : atom0920 = SparsePolynomial.decodeCubic 21 atom0920Coded := by decide +kernel
theorem atom0920Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (51452745523200 : Int) atom0920Coded) := by
  have h := atom0920_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0920Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0921 : SparsePolynomial.Poly := [([3,18,18], 1)]
theorem eval_atom0921 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0921 = ((g 3) * (g 18) * (g 18)) := by
  norm_num [atom0921, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0921_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18834575155200 : Int) atom0921) := by
  rw [SparsePolynomial.eval_scale, eval_atom0921]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0921Coded : CoefficientMerge.Poly := [(1719, 1)]
theorem atom0921Coded_decode : atom0921 = SparsePolynomial.decodeCubic 21 atom0921Coded := by decide +kernel
theorem atom0921Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18834575155200 : Int) atom0921Coded) := by
  have h := atom0921_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0921Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0922 : SparsePolynomial.Poly := [([3,18,19], 1)]
theorem eval_atom0922 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0922 = ((g 3) * (g 18) * (g 19)) := by
  norm_num [atom0922, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0922_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22849293196800 : Int) atom0922) := by
  rw [SparsePolynomial.eval_scale, eval_atom0922]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0922Coded : CoefficientMerge.Poly := [(1720, 1)]
theorem atom0922Coded_decode : atom0922 = SparsePolynomial.decodeCubic 21 atom0922Coded := by decide +kernel
theorem atom0922Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22849293196800 : Int) atom0922Coded) := by
  have h := atom0922_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0922Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0923 : SparsePolynomial.Poly := [([3,18,20], 1)]
theorem eval_atom0923 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0923 = ((g 3) * (g 18) * (g 20)) := by
  norm_num [atom0923, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0923_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35421140160000 : Int) atom0923) := by
  rw [SparsePolynomial.eval_scale, eval_atom0923]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0923Coded : CoefficientMerge.Poly := [(1721, 1)]
theorem atom0923Coded_decode : atom0923 = SparsePolynomial.decodeCubic 21 atom0923Coded := by decide +kernel
theorem atom0923Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35421140160000 : Int) atom0923Coded) := by
  have h := atom0923_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0923Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0924 : SparsePolynomial.Poly := [([3,19,20], 1)]
theorem eval_atom0924 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0924 = ((g 3) * (g 19) * (g 20)) := by
  norm_num [atom0924, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0924_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12570880492800 : Int) atom0924) := by
  rw [SparsePolynomial.eval_scale, eval_atom0924]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0924Coded : CoefficientMerge.Poly := [(1742, 1)]
theorem atom0924Coded_decode : atom0924 = SparsePolynomial.decodeCubic 21 atom0924Coded := by decide +kernel
theorem atom0924Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12570880492800 : Int) atom0924Coded) := by
  have h := atom0924_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0924Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0925 : SparsePolynomial.Poly := [([3,20,20], 1)]
theorem eval_atom0925 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0925 = ((g 3) * (g 20) * (g 20)) := by
  norm_num [atom0925, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0925_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13316995641600 : Int) atom0925) := by
  rw [SparsePolynomial.eval_scale, eval_atom0925]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0925Coded : CoefficientMerge.Poly := [(1763, 1)]
theorem atom0925Coded_decode : atom0925 = SparsePolynomial.decodeCubic 21 atom0925Coded := by decide +kernel
theorem atom0925Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13316995641600 : Int) atom0925Coded) := by
  have h := atom0925_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0925Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0926 : SparsePolynomial.Poly := [([4,4,4], 1)]
theorem eval_atom0926 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0926 = ((g 4) * (g 4) * (g 4)) := by
  norm_num [atom0926, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0926_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1394616787200 : Int) atom0926) := by
  rw [SparsePolynomial.eval_scale, eval_atom0926]
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 4) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0926Coded : CoefficientMerge.Poly := [(1852, 1)]
theorem atom0926Coded_decode : atom0926 = SparsePolynomial.decodeCubic 21 atom0926Coded := by decide +kernel
theorem atom0926Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1394616787200 : Int) atom0926Coded) := by
  have h := atom0926_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0926Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0927 : SparsePolynomial.Poly := [([4,4,5], 1)]
theorem eval_atom0927 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0927 = ((g 4) * (g 4) * (g 5)) := by
  norm_num [atom0927, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0927_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (954758619648 : Int) atom0927) := by
  rw [SparsePolynomial.eval_scale, eval_atom0927]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0927Coded : CoefficientMerge.Poly := [(1853, 1)]
theorem atom0927Coded_decode : atom0927 = SparsePolynomial.decodeCubic 21 atom0927Coded := by decide +kernel
theorem atom0927Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (954758619648 : Int) atom0927Coded) := by
  have h := atom0927_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0927Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0928 : SparsePolynomial.Poly := [([4,4,6], 1)]
theorem eval_atom0928 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0928 = ((g 4) * (g 4) * (g 6)) := by
  norm_num [atom0928, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0928_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (923143737600 : Int) atom0928) := by
  rw [SparsePolynomial.eval_scale, eval_atom0928]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0928Coded : CoefficientMerge.Poly := [(1854, 1)]
theorem atom0928Coded_decode : atom0928 = SparsePolynomial.decodeCubic 21 atom0928Coded := by decide +kernel
theorem atom0928Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (923143737600 : Int) atom0928Coded) := by
  have h := atom0928_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0928Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0929 : SparsePolynomial.Poly := [([4,4,7], 1)]
theorem eval_atom0929 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0929 = ((g 4) * (g 4) * (g 7)) := by
  norm_num [atom0929, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0929_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1922698975104 : Int) atom0929) := by
  rw [SparsePolynomial.eval_scale, eval_atom0929]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0929Coded : CoefficientMerge.Poly := [(1855, 1)]
theorem atom0929Coded_decode : atom0929 = SparsePolynomial.decodeCubic 21 atom0929Coded := by decide +kernel
theorem atom0929Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1922698975104 : Int) atom0929Coded) := by
  have h := atom0929_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0929Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0930 : SparsePolynomial.Poly := [([4,4,8], 1)]
theorem eval_atom0930 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0930 = ((g 4) * (g 4) * (g 8)) := by
  norm_num [atom0930, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0930_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1970633145600 : Int) atom0930) := by
  rw [SparsePolynomial.eval_scale, eval_atom0930]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0930Coded : CoefficientMerge.Poly := [(1856, 1)]
theorem atom0930Coded_decode : atom0930 = SparsePolynomial.decodeCubic 21 atom0930Coded := by decide +kernel
theorem atom0930Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1970633145600 : Int) atom0930Coded) := by
  have h := atom0930_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0930Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0931 : SparsePolynomial.Poly := [([4,4,9], 1)]
theorem eval_atom0931 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0931 = ((g 4) * (g 4) * (g 9)) := by
  norm_num [atom0931, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0931_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1943571974400 : Int) atom0931) := by
  rw [SparsePolynomial.eval_scale, eval_atom0931]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0931Coded : CoefficientMerge.Poly := [(1857, 1)]
theorem atom0931Coded_decode : atom0931 = SparsePolynomial.decodeCubic 21 atom0931Coded := by decide +kernel
theorem atom0931Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1943571974400 : Int) atom0931Coded) := by
  have h := atom0931_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0931Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0932 : SparsePolynomial.Poly := [([4,4,10], 1)]
theorem eval_atom0932 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0932 = ((g 4) * (g 4) * (g 10)) := by
  norm_num [atom0932, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0932_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1916510803200 : Int) atom0932) := by
  rw [SparsePolynomial.eval_scale, eval_atom0932]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0932Coded : CoefficientMerge.Poly := [(1858, 1)]
theorem atom0932Coded_decode : atom0932 = SparsePolynomial.decodeCubic 21 atom0932Coded := by decide +kernel
theorem atom0932Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1916510803200 : Int) atom0932Coded) := by
  have h := atom0932_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0932Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0933 : SparsePolynomial.Poly := [([4,4,11], 1)]
theorem eval_atom0933 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0933 = ((g 4) * (g 4) * (g 11)) := by
  norm_num [atom0933, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0933_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1577526048000 : Int) atom0933) := by
  rw [SparsePolynomial.eval_scale, eval_atom0933]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0933Coded : CoefficientMerge.Poly := [(1859, 1)]
theorem atom0933Coded_decode : atom0933 = SparsePolynomial.decodeCubic 21 atom0933Coded := by decide +kernel
theorem atom0933Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1577526048000 : Int) atom0933Coded) := by
  have h := atom0933_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0933Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0934 : SparsePolynomial.Poly := [([4,4,15], 1)]
theorem eval_atom0934 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0934 = ((g 4) * (g 4) * (g 15)) := by
  norm_num [atom0934, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0934_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3145981960800 : Int) atom0934) := by
  rw [SparsePolynomial.eval_scale, eval_atom0934]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0934Coded : CoefficientMerge.Poly := [(1863, 1)]
theorem atom0934Coded_decode : atom0934 = SparsePolynomial.decodeCubic 21 atom0934Coded := by decide +kernel
theorem atom0934Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3145981960800 : Int) atom0934Coded) := by
  have h := atom0934_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0934Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0935 : SparsePolynomial.Poly := [([4,5,5], 1)]
theorem eval_atom0935 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0935 = ((g 4) * (g 5) * (g 5)) := by
  norm_num [atom0935, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0935_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2427545373696 : Int) atom0935) := by
  rw [SparsePolynomial.eval_scale, eval_atom0935]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0935Coded : CoefficientMerge.Poly := [(1874, 1)]
theorem atom0935Coded_decode : atom0935 = SparsePolynomial.decodeCubic 21 atom0935Coded := by decide +kernel
theorem atom0935Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2427545373696 : Int) atom0935Coded) := by
  have h := atom0935_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0935Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0936 : SparsePolynomial.Poly := [([4,5,6], 1)]
theorem eval_atom0936 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0936 = ((g 4) * (g 5) * (g 6)) := by
  norm_num [atom0936, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0936_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3197822282496 : Int) atom0936) := by
  rw [SparsePolynomial.eval_scale, eval_atom0936]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0936Coded : CoefficientMerge.Poly := [(1875, 1)]
theorem atom0936Coded_decode : atom0936 = SparsePolynomial.decodeCubic 21 atom0936Coded := by decide +kernel
theorem atom0936Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3197822282496 : Int) atom0936Coded) := by
  have h := atom0936_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0936Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0937 : SparsePolynomial.Poly := [([4,5,9], 1)]
theorem eval_atom0937 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0937 = ((g 4) * (g 5) * (g 9)) := by
  norm_num [atom0937, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0937_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1516392057600 : Int) atom0937) := by
  rw [SparsePolynomial.eval_scale, eval_atom0937]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0937Coded : CoefficientMerge.Poly := [(1878, 1)]
theorem atom0937Coded_decode : atom0937 = SparsePolynomial.decodeCubic 21 atom0937Coded := by decide +kernel
theorem atom0937Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1516392057600 : Int) atom0937Coded) := by
  have h := atom0937_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0937Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0938 : SparsePolynomial.Poly := [([4,5,10], 1)]
theorem eval_atom0938 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0938 = ((g 4) * (g 5) * (g 10)) := by
  norm_num [atom0938, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0938_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1573413811200 : Int) atom0938) := by
  rw [SparsePolynomial.eval_scale, eval_atom0938]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0938Coded : CoefficientMerge.Poly := [(1879, 1)]
theorem atom0938Coded_decode : atom0938 = SparsePolynomial.decodeCubic 21 atom0938Coded := by decide +kernel
theorem atom0938Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1573413811200 : Int) atom0938Coded) := by
  have h := atom0938_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0938Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0939 : SparsePolynomial.Poly := [([4,5,11], 1)]
theorem eval_atom0939 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0939 = ((g 4) * (g 5) * (g 11)) := by
  norm_num [atom0939, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0939_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1736273548800 : Int) atom0939) := by
  rw [SparsePolynomial.eval_scale, eval_atom0939]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0939Coded : CoefficientMerge.Poly := [(1880, 1)]
theorem atom0939Coded_decode : atom0939 = SparsePolynomial.decodeCubic 21 atom0939Coded := by decide +kernel
theorem atom0939Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1736273548800 : Int) atom0939Coded) := by
  have h := atom0939_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0939Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0940 : SparsePolynomial.Poly := [([4,5,13], 1)]
theorem eval_atom0940 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0940 = ((g 4) * (g 5) * (g 13)) := by
  norm_num [atom0940, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0940_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (165266438400 : Int) atom0940) := by
  rw [SparsePolynomial.eval_scale, eval_atom0940]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0940Coded : CoefficientMerge.Poly := [(1882, 1)]
theorem atom0940Coded_decode : atom0940 = SparsePolynomial.decodeCubic 21 atom0940Coded := by decide +kernel
theorem atom0940Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (165266438400 : Int) atom0940Coded) := by
  have h := atom0940_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0940Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0941 : SparsePolynomial.Poly := [([4,5,14], 1)]
theorem eval_atom0941 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0941 = ((g 4) * (g 5) * (g 14)) := by
  norm_num [atom0941, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0941_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (592446355200 : Int) atom0941) := by
  rw [SparsePolynomial.eval_scale, eval_atom0941]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0941Coded : CoefficientMerge.Poly := [(1883, 1)]
theorem atom0941Coded_decode : atom0941 = SparsePolynomial.decodeCubic 21 atom0941Coded := by decide +kernel
theorem atom0941Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (592446355200 : Int) atom0941Coded) := by
  have h := atom0941_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0941Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0942 : SparsePolynomial.Poly := [([4,5,15], 1)]
theorem eval_atom0942 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0942 = ((g 4) * (g 5) * (g 15)) := by
  norm_num [atom0942, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0942_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8758268900352 : Int) atom0942) := by
  rw [SparsePolynomial.eval_scale, eval_atom0942]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0942Coded : CoefficientMerge.Poly := [(1884, 1)]
theorem atom0942Coded_decode : atom0942 = SparsePolynomial.decodeCubic 21 atom0942Coded := by decide +kernel
theorem atom0942Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8758268900352 : Int) atom0942Coded) := by
  have h := atom0942_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0942Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0943 : SparsePolynomial.Poly := [([4,5,16], 1)]
theorem eval_atom0943 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0943 = ((g 4) * (g 5) * (g 16)) := by
  norm_num [atom0943, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0943_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3991786230240 : Int) atom0943) := by
  rw [SparsePolynomial.eval_scale, eval_atom0943]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0943Coded : CoefficientMerge.Poly := [(1885, 1)]
theorem atom0943Coded_decode : atom0943 = SparsePolynomial.decodeCubic 21 atom0943Coded := by decide +kernel
theorem atom0943Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3991786230240 : Int) atom0943Coded) := by
  have h := atom0943_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0943Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0944 : SparsePolynomial.Poly := [([4,5,17], 1)]
theorem eval_atom0944 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0944 = ((g 4) * (g 5) * (g 17)) := by
  norm_num [atom0944, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0944_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6523606342656 : Int) atom0944) := by
  rw [SparsePolynomial.eval_scale, eval_atom0944]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0944Coded : CoefficientMerge.Poly := [(1886, 1)]
theorem atom0944Coded_decode : atom0944 = SparsePolynomial.decodeCubic 21 atom0944Coded := by decide +kernel
theorem atom0944Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6523606342656 : Int) atom0944Coded) := by
  have h := atom0944_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0944Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0945 : SparsePolynomial.Poly := [([4,5,18], 1)]
theorem eval_atom0945 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0945 = ((g 4) * (g 5) * (g 18)) := by
  norm_num [atom0945, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0945_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9974479623840 : Int) atom0945) := by
  rw [SparsePolynomial.eval_scale, eval_atom0945]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0945Coded : CoefficientMerge.Poly := [(1887, 1)]
theorem atom0945Coded_decode : atom0945 = SparsePolynomial.decodeCubic 21 atom0945Coded := by decide +kernel
theorem atom0945Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9974479623840 : Int) atom0945Coded) := by
  have h := atom0945_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0945Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0946 : SparsePolynomial.Poly := [([4,5,19], 1)]
theorem eval_atom0946 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0946 = ((g 4) * (g 5) * (g 19)) := by
  norm_num [atom0946, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0946_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13828223276064 : Int) atom0946) := by
  rw [SparsePolynomial.eval_scale, eval_atom0946]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0946Coded : CoefficientMerge.Poly := [(1888, 1)]
theorem atom0946Coded_decode : atom0946 = SparsePolynomial.decodeCubic 21 atom0946Coded := by decide +kernel
theorem atom0946Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13828223276064 : Int) atom0946Coded) := by
  have h := atom0946_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0946Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0947 : SparsePolynomial.Poly := [([4,5,20], 1)]
theorem eval_atom0947 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0947 = ((g 4) * (g 5) * (g 20)) := by
  norm_num [atom0947, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0947_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17685804276000 : Int) atom0947) := by
  rw [SparsePolynomial.eval_scale, eval_atom0947]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0947Coded : CoefficientMerge.Poly := [(1889, 1)]
theorem atom0947Coded_decode : atom0947 = SparsePolynomial.decodeCubic 21 atom0947Coded := by decide +kernel
theorem atom0947Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17685804276000 : Int) atom0947Coded) := by
  have h := atom0947_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0947Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0948 : SparsePolynomial.Poly := [([4,6,6], 1)]
theorem eval_atom0948 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0948 = ((g 4) * (g 6) * (g 6)) := by
  norm_num [atom0948, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0948_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5472155404800 : Int) atom0948) := by
  rw [SparsePolynomial.eval_scale, eval_atom0948]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0948Coded : CoefficientMerge.Poly := [(1896, 1)]
theorem atom0948Coded_decode : atom0948 = SparsePolynomial.decodeCubic 21 atom0948Coded := by decide +kernel
theorem atom0948Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5472155404800 : Int) atom0948Coded) := by
  have h := atom0948_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0948Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0949 : SparsePolynomial.Poly := [([4,6,7], 1)]
theorem eval_atom0949 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0949 = ((g 4) * (g 6) * (g 7)) := by
  norm_num [atom0949, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0949_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8096350811904 : Int) atom0949) := by
  rw [SparsePolynomial.eval_scale, eval_atom0949]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0949Coded : CoefficientMerge.Poly := [(1897, 1)]
theorem atom0949Coded_decode : atom0949 = SparsePolynomial.decodeCubic 21 atom0949Coded := by decide +kernel
theorem atom0949Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8096350811904 : Int) atom0949Coded) := by
  have h := atom0949_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0949Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0950 : SparsePolynomial.Poly := [([4,6,8], 1)]
theorem eval_atom0950 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0950 = ((g 4) * (g 6) * (g 8)) := by
  norm_num [atom0950, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0950_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4467831580800 : Int) atom0950) := by
  rw [SparsePolynomial.eval_scale, eval_atom0950]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0950Coded : CoefficientMerge.Poly := [(1898, 1)]
theorem atom0950Coded_decode : atom0950 = SparsePolynomial.decodeCubic 21 atom0950Coded := by decide +kernel
theorem atom0950Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4467831580800 : Int) atom0950Coded) := by
  have h := atom0950_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0950Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0951 : SparsePolynomial.Poly := [([4,6,9], 1)]
theorem eval_atom0951 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0951 = ((g 4) * (g 6) * (g 9)) := by
  norm_num [atom0951, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0951_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2082106252800 : Int) atom0951) := by
  rw [SparsePolynomial.eval_scale, eval_atom0951]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0951Coded : CoefficientMerge.Poly := [(1899, 1)]
theorem atom0951Coded_decode : atom0951 = SparsePolynomial.decodeCubic 21 atom0951Coded := by decide +kernel
theorem atom0951Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2082106252800 : Int) atom0951Coded) := by
  have h := atom0951_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0951Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0952 : SparsePolynomial.Poly := [([4,6,10], 1)]
theorem eval_atom0952 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0952 = ((g 4) * (g 6) * (g 10)) := by
  norm_num [atom0952, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0952_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2657156140800 : Int) atom0952) := by
  rw [SparsePolynomial.eval_scale, eval_atom0952]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0952Coded : CoefficientMerge.Poly := [(1900, 1)]
theorem atom0952Coded_decode : atom0952 = SparsePolynomial.decodeCubic 21 atom0952Coded := by decide +kernel
theorem atom0952Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2657156140800 : Int) atom0952Coded) := by
  have h := atom0952_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0952Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0953 : SparsePolynomial.Poly := [([4,6,11], 1)]
theorem eval_atom0953 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0953 = ((g 4) * (g 6) * (g 11)) := by
  norm_num [atom0953, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0953_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2661268377600 : Int) atom0953) := by
  rw [SparsePolynomial.eval_scale, eval_atom0953]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0953Coded : CoefficientMerge.Poly := [(1901, 1)]
theorem atom0953Coded_decode : atom0953 = SparsePolynomial.decodeCubic 21 atom0953Coded := by decide +kernel
theorem atom0953Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2661268377600 : Int) atom0953Coded) := by
  have h := atom0953_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0953Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0954 : SparsePolynomial.Poly := [([4,6,12], 1)]
theorem eval_atom0954 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0954 = ((g 4) * (g 6) * (g 12)) := by
  norm_num [atom0954, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0954_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1769936313600 : Int) atom0954) := by
  rw [SparsePolynomial.eval_scale, eval_atom0954]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0954Coded : CoefficientMerge.Poly := [(1902, 1)]
theorem atom0954Coded_decode : atom0954 = SparsePolynomial.decodeCubic 21 atom0954Coded := by decide +kernel
theorem atom0954Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1769936313600 : Int) atom0954Coded) := by
  have h := atom0954_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0954Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0955 : SparsePolynomial.Poly := [([4,6,13], 1)]
theorem eval_atom0955 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0955 = ((g 4) * (g 6) * (g 13)) := by
  norm_num [atom0955, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0955_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2456130297600 : Int) atom0955) := by
  rw [SparsePolynomial.eval_scale, eval_atom0955]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0955Coded : CoefficientMerge.Poly := [(1903, 1)]
theorem atom0955Coded_decode : atom0955 = SparsePolynomial.decodeCubic 21 atom0955Coded := by decide +kernel
theorem atom0955Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2456130297600 : Int) atom0955Coded) := by
  have h := atom0955_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0955Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0956 : SparsePolynomial.Poly := [([4,6,14], 1)]
theorem eval_atom0956 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0956 = ((g 4) * (g 6) * (g 14)) := by
  norm_num [atom0956, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0956_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3142324281600 : Int) atom0956) := by
  rw [SparsePolynomial.eval_scale, eval_atom0956]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0956Coded : CoefficientMerge.Poly := [(1904, 1)]
theorem atom0956Coded_decode : atom0956 = SparsePolynomial.decodeCubic 21 atom0956Coded := by decide +kernel
theorem atom0956Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3142324281600 : Int) atom0956Coded) := by
  have h := atom0956_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0956Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0957 : SparsePolynomial.Poly := [([4,6,15], 1)]
theorem eval_atom0957 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0957 = ((g 4) * (g 6) * (g 15)) := by
  norm_num [atom0957, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0957_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12877580620800 : Int) atom0957) := by
  rw [SparsePolynomial.eval_scale, eval_atom0957]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0957Coded : CoefficientMerge.Poly := [(1905, 1)]
theorem atom0957Coded_decode : atom0957 = SparsePolynomial.decodeCubic 21 atom0957Coded := by decide +kernel
theorem atom0957Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12877580620800 : Int) atom0957Coded) := by
  have h := atom0957_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0957Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0958 : SparsePolynomial.Poly := [([4,6,16], 1)]
theorem eval_atom0958 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0958 = ((g 4) * (g 6) * (g 16)) := by
  norm_num [atom0958, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0958_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8729970328800 : Int) atom0958) := by
  rw [SparsePolynomial.eval_scale, eval_atom0958]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0958Coded : CoefficientMerge.Poly := [(1906, 1)]
theorem atom0958Coded_decode : atom0958 = SparsePolynomial.decodeCubic 21 atom0958Coded := by decide +kernel
theorem atom0958Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8729970328800 : Int) atom0958Coded) := by
  have h := atom0958_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0958Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0959 : SparsePolynomial.Poly := [([4,6,17], 1)]
theorem eval_atom0959 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0959 = ((g 4) * (g 6) * (g 17)) := by
  norm_num [atom0959, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0959_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12355275340800 : Int) atom0959) := by
  rw [SparsePolynomial.eval_scale, eval_atom0959]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0959Coded : CoefficientMerge.Poly := [(1907, 1)]
theorem atom0959Coded_decode : atom0959 = SparsePolynomial.decodeCubic 21 atom0959Coded := by decide +kernel
theorem atom0959Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12355275340800 : Int) atom0959Coded) := by
  have h := atom0959_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0959Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0960 : SparsePolynomial.Poly := [([4,6,18], 1)]
theorem eval_atom0960 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0960 = ((g 4) * (g 6) * (g 18)) := by
  norm_num [atom0960, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0960_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18532874455200 : Int) atom0960) := by
  rw [SparsePolynomial.eval_scale, eval_atom0960]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0960Coded : CoefficientMerge.Poly := [(1908, 1)]
theorem atom0960Coded_decode : atom0960 = SparsePolynomial.decodeCubic 21 atom0960Coded := by decide +kernel
theorem atom0960Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18532874455200 : Int) atom0960Coded) := by
  have h := atom0960_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0960Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0961 : SparsePolynomial.Poly := [([4,6,19], 1)]
theorem eval_atom0961 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0961 = ((g 4) * (g 6) * (g 19)) := by
  norm_num [atom0961, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0961_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24839412544800 : Int) atom0961) := by
  rw [SparsePolynomial.eval_scale, eval_atom0961]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0961Coded : CoefficientMerge.Poly := [(1909, 1)]
theorem atom0961Coded_decode : atom0961 = SparsePolynomial.decodeCubic 21 atom0961Coded := by decide +kernel
theorem atom0961Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24839412544800 : Int) atom0961Coded) := by
  have h := atom0961_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0961Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0962 : SparsePolynomial.Poly := [([4,6,20], 1)]
theorem eval_atom0962 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0962 = ((g 4) * (g 6) * (g 20)) := by
  norm_num [atom0962, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0962_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31145950634400 : Int) atom0962) := by
  rw [SparsePolynomial.eval_scale, eval_atom0962]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0962Coded : CoefficientMerge.Poly := [(1910, 1)]
theorem atom0962Coded_decode : atom0962 = SparsePolynomial.decodeCubic 21 atom0962Coded := by decide +kernel
theorem atom0962Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31145950634400 : Int) atom0962Coded) := by
  have h := atom0962_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0962Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0963 : SparsePolynomial.Poly := [([4,7,7], 1)]
theorem eval_atom0963 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0963 = ((g 4) * (g 7) * (g 7)) := by
  norm_num [atom0963, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0963_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6636980507904 : Int) atom0963) := by
  rw [SparsePolynomial.eval_scale, eval_atom0963]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0963Coded : CoefficientMerge.Poly := [(1918, 1)]
theorem atom0963Coded_decode : atom0963 = SparsePolynomial.decodeCubic 21 atom0963Coded := by decide +kernel
theorem atom0963Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6636980507904 : Int) atom0963Coded) := by
  have h := atom0963_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0963Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0964 : SparsePolynomial.Poly := [([4,7,8], 1)]
theorem eval_atom0964 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0964 = ((g 4) * (g 7) * (g 8)) := by
  norm_num [atom0964, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0964_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10513332203904 : Int) atom0964) := by
  rw [SparsePolynomial.eval_scale, eval_atom0964]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0964Coded : CoefficientMerge.Poly := [(1919, 1)]
theorem atom0964Coded_decode : atom0964 = SparsePolynomial.decodeCubic 21 atom0964Coded := by decide +kernel
theorem atom0964Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10513332203904 : Int) atom0964Coded) := by
  have h := atom0964_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0964Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0965 : SparsePolynomial.Poly := [([4,7,9], 1)]
theorem eval_atom0965 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0965 = ((g 4) * (g 7) * (g 9)) := by
  norm_num [atom0965, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0965_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8483261128704 : Int) atom0965) := by
  rw [SparsePolynomial.eval_scale, eval_atom0965]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0965Coded : CoefficientMerge.Poly := [(1920, 1)]
theorem atom0965Coded_decode : atom0965 = SparsePolynomial.decodeCubic 21 atom0965Coded := by decide +kernel
theorem atom0965Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8483261128704 : Int) atom0965Coded) := by
  have h := atom0965_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0965Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0966 : SparsePolynomial.Poly := [([4,7,10], 1)]
theorem eval_atom0966 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0966 = ((g 4) * (g 7) * (g 10)) := by
  norm_num [atom0966, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0966_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8890145167104 : Int) atom0966) := by
  rw [SparsePolynomial.eval_scale, eval_atom0966]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0966Coded : CoefficientMerge.Poly := [(1921, 1)]
theorem atom0966Coded_decode : atom0966 = SparsePolynomial.decodeCubic 21 atom0966Coded := by decide +kernel
theorem atom0966Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8890145167104 : Int) atom0966Coded) := by
  have h := atom0966_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0966Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0967 : SparsePolynomial.Poly := [([4,7,11], 1)]
theorem eval_atom0967 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0967 = ((g 4) * (g 7) * (g 11)) := by
  norm_num [atom0967, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0967_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9244119688704 : Int) atom0967) := by
  rw [SparsePolynomial.eval_scale, eval_atom0967]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0967Coded : CoefficientMerge.Poly := [(1922, 1)]
theorem atom0967Coded_decode : atom0967 = SparsePolynomial.decodeCubic 21 atom0967Coded := by decide +kernel
theorem atom0967Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9244119688704 : Int) atom0967Coded) := by
  have h := atom0967_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0967Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0968 : SparsePolynomial.Poly := [([4,7,12], 1)]
theorem eval_atom0968 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0968 = ((g 4) * (g 7) * (g 12)) := by
  norm_num [atom0968, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0968_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8443635842304 : Int) atom0968) := by
  rw [SparsePolynomial.eval_scale, eval_atom0968]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0968Coded : CoefficientMerge.Poly := [(1923, 1)]
theorem atom0968Coded_decode : atom0968 = SparsePolynomial.decodeCubic 21 atom0968Coded := by decide +kernel
theorem atom0968Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8443635842304 : Int) atom0968Coded) := by
  have h := atom0968_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0968Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0969 : SparsePolynomial.Poly := [([4,7,13], 1)]
theorem eval_atom0969 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0969 = ((g 4) * (g 7) * (g 13)) := by
  norm_num [atom0969, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0969_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9220678043904 : Int) atom0969) := by
  rw [SparsePolynomial.eval_scale, eval_atom0969]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0969Coded : CoefficientMerge.Poly := [(1924, 1)]
theorem atom0969Coded_decode : atom0969 = SparsePolynomial.decodeCubic 21 atom0969Coded := by decide +kernel
theorem atom0969Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9220678043904 : Int) atom0969Coded) := by
  have h := atom0969_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0969Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0970 : SparsePolynomial.Poly := [([4,7,14], 1)]
theorem eval_atom0970 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0970 = ((g 4) * (g 7) * (g 14)) := by
  norm_num [atom0970, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0970_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9997720245504 : Int) atom0970) := by
  rw [SparsePolynomial.eval_scale, eval_atom0970]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0970Coded : CoefficientMerge.Poly := [(1925, 1)]
theorem atom0970Coded_decode : atom0970 = SparsePolynomial.decodeCubic 21 atom0970Coded := by decide +kernel
theorem atom0970Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9997720245504 : Int) atom0970Coded) := by
  have h := atom0970_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0970Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0971 : SparsePolynomial.Poly := [([4,7,15], 1)]
theorem eval_atom0971 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0971 = ((g 4) * (g 7) * (g 15)) := by
  norm_num [atom0971, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0971_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19013184407808 : Int) atom0971) := by
  rw [SparsePolynomial.eval_scale, eval_atom0971]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0971Coded : CoefficientMerge.Poly := [(1926, 1)]
theorem atom0971Coded_decode : atom0971 = SparsePolynomial.decodeCubic 21 atom0971Coded := by decide +kernel
theorem atom0971Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19013184407808 : Int) atom0971Coded) := by
  have h := atom0971_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0971Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0972 : SparsePolynomial.Poly := [([4,7,16], 1)]
theorem eval_atom0972 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0972 = ((g 4) * (g 7) * (g 16)) := by
  norm_num [atom0972, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0972_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15624546121440 : Int) atom0972) := by
  rw [SparsePolynomial.eval_scale, eval_atom0972]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0972Coded : CoefficientMerge.Poly := [(1927, 1)]
theorem atom0972Coded_decode : atom0972 = SparsePolynomial.decodeCubic 21 atom0972Coded := by decide +kernel
theorem atom0972Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15624546121440 : Int) atom0972Coded) := by
  have h := atom0972_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0972Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0973 : SparsePolynomial.Poly := [([4,7,17], 1)]
theorem eval_atom0973 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0973 = ((g 4) * (g 7) * (g 17)) := by
  norm_num [atom0973, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0973_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20172537623808 : Int) atom0973) := by
  rw [SparsePolynomial.eval_scale, eval_atom0973]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0973Coded : CoefficientMerge.Poly := [(1928, 1)]
theorem atom0973Coded_decode : atom0973 = SparsePolynomial.decodeCubic 21 atom0973Coded := by decide +kernel
theorem atom0973Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20172537623808 : Int) atom0973Coded) := by
  have h := atom0973_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0973Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0974 : SparsePolynomial.Poly := [([4,7,18], 1)]
theorem eval_atom0974 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0974 = ((g 4) * (g 7) * (g 18)) := by
  norm_num [atom0974, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0974_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25324113470112 : Int) atom0974) := by
  rw [SparsePolynomial.eval_scale, eval_atom0974]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0974Coded : CoefficientMerge.Poly := [(1929, 1)]
theorem atom0974Coded_decode : atom0974 = SparsePolynomial.decodeCubic 21 atom0974Coded := by decide +kernel
theorem atom0974Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25324113470112 : Int) atom0974Coded) := by
  have h := atom0974_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0974Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0975 : SparsePolynomial.Poly := [([4,7,19], 1)]
theorem eval_atom0975 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0975 = ((g 4) * (g 7) * (g 19)) := by
  norm_num [atom0975, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0975_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31531477635360 : Int) atom0975) := by
  rw [SparsePolynomial.eval_scale, eval_atom0975]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0975Coded : CoefficientMerge.Poly := [(1930, 1)]
theorem atom0975Coded_decode : atom0975 = SparsePolynomial.decodeCubic 21 atom0975Coded := by decide +kernel
theorem atom0975Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31531477635360 : Int) atom0975Coded) := by
  have h := atom0975_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0975Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block013 : CoefficientMerge.Poly := [(1614, 47411171942400), (1615, 44102287944000), (1616, 53975438899200), (1631, 26303458406400), (1632, 48520679961600), (1633, 39984813388800), (1634, 58281619737600), (1635, 53383959014400), (1636, 44697323059200), (1637, 59921164800000), (1653, 30559794048000), (1654, 52085022796800), (1655, 72395953459200), (1656, 66129770649600), (1657, 43317203328000), (1658, 63125980646400), (1675, 20924470748160), (1676, 58450854873600), (1677, 58152523968000), (1678, 40238672947200), (1679, 46263971577600), (1697, 39608547955200), (1698, 61172435520000), (1699, 40507146086400), (1700, 51452745523200), (1719, 18834575155200), (1720, 22849293196800), (1721, 35421140160000), (1742, 12570880492800), (1763, 13316995641600), (1852, 1394616787200), (1853, 954758619648), (1854, 923143737600), (1855, 1922698975104), (1856, 1970633145600), (1857, 1943571974400), (1858, 1916510803200), (1859, 1577526048000), (1863, 3145981960800), (1874, 2427545373696), (1875, 3197822282496), (1878, 1516392057600), (1879, 1573413811200), (1880, 1736273548800), (1882, 165266438400), (1883, 592446355200), (1884, 8758268900352), (1885, 3991786230240), (1886, 6523606342656), (1887, 9974479623840), (1888, 13828223276064), (1889, 17685804276000), (1896, 5472155404800), (1897, 8096350811904), (1898, 4467831580800), (1899, 2082106252800), (1900, 2657156140800), (1901, 2661268377600), (1902, 1769936313600), (1903, 2456130297600), (1904, 3142324281600), (1905, 12877580620800), (1906, 8729970328800), (1907, 12355275340800), (1908, 18532874455200), (1909, 24839412544800), (1910, 31145950634400), (1918, 6636980507904), (1919, 10513332203904), (1920, 8483261128704), (1921, 8890145167104), (1922, 9244119688704), (1923, 8443635842304), (1924, 9220678043904), (1925, 9997720245504), (1926, 19013184407808), (1927, 15624546121440), (1928, 20172537623808), (1929, 25324113470112), (1930, 31531477635360)]
theorem block013_data : block013 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47411171942400 : Int) atom0896Coded) (CoefficientMerge.scale (44102287944000 : Int) atom0897Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53975438899200 : Int) atom0898Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26303458406400 : Int) atom0899Coded) (CoefficientMerge.scale (48520679961600 : Int) atom0900Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39984813388800 : Int) atom0901Coded) (CoefficientMerge.scale (58281619737600 : Int) atom0902Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53383959014400 : Int) atom0903Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44697323059200 : Int) atom0904Coded) (CoefficientMerge.scale (59921164800000 : Int) atom0905Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30559794048000 : Int) atom0906Coded) (CoefficientMerge.scale (52085022796800 : Int) atom0907Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (72395953459200 : Int) atom0908Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (66129770649600 : Int) atom0909Coded) (CoefficientMerge.scale (43317203328000 : Int) atom0910Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (63125980646400 : Int) atom0911Coded) (CoefficientMerge.scale (20924470748160 : Int) atom0912Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58450854873600 : Int) atom0913Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (58152523968000 : Int) atom0914Coded) (CoefficientMerge.scale (40238672947200 : Int) atom0915Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46263971577600 : Int) atom0916Coded) (CoefficientMerge.scale (39608547955200 : Int) atom0917Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61172435520000 : Int) atom0918Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40507146086400 : Int) atom0919Coded) (CoefficientMerge.scale (51452745523200 : Int) atom0920Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18834575155200 : Int) atom0921Coded) (CoefficientMerge.scale (22849293196800 : Int) atom0922Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35421140160000 : Int) atom0923Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12570880492800 : Int) atom0924Coded) (CoefficientMerge.scale (13316995641600 : Int) atom0925Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1394616787200 : Int) atom0926Coded) (CoefficientMerge.scale (954758619648 : Int) atom0927Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (923143737600 : Int) atom0928Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1922698975104 : Int) atom0929Coded) (CoefficientMerge.scale (1970633145600 : Int) atom0930Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1943571974400 : Int) atom0931Coded) (CoefficientMerge.scale (1916510803200 : Int) atom0932Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1577526048000 : Int) atom0933Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3145981960800 : Int) atom0934Coded) (CoefficientMerge.scale (2427545373696 : Int) atom0935Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3197822282496 : Int) atom0936Coded) (CoefficientMerge.scale (1516392057600 : Int) atom0937Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1573413811200 : Int) atom0938Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1736273548800 : Int) atom0939Coded) (CoefficientMerge.scale (165266438400 : Int) atom0940Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (592446355200 : Int) atom0941Coded) (CoefficientMerge.scale (8758268900352 : Int) atom0942Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3991786230240 : Int) atom0943Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6523606342656 : Int) atom0944Coded) (CoefficientMerge.scale (9974479623840 : Int) atom0945Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13828223276064 : Int) atom0946Coded) (CoefficientMerge.scale (17685804276000 : Int) atom0947Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5472155404800 : Int) atom0948Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8096350811904 : Int) atom0949Coded) (CoefficientMerge.scale (4467831580800 : Int) atom0950Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2082106252800 : Int) atom0951Coded) (CoefficientMerge.scale (2657156140800 : Int) atom0952Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2661268377600 : Int) atom0953Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1769936313600 : Int) atom0954Coded) (CoefficientMerge.scale (2456130297600 : Int) atom0955Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3142324281600 : Int) atom0956Coded) (CoefficientMerge.scale (12877580620800 : Int) atom0957Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8729970328800 : Int) atom0958Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12355275340800 : Int) atom0959Coded) (CoefficientMerge.scale (18532874455200 : Int) atom0960Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24839412544800 : Int) atom0961Coded) (CoefficientMerge.scale (31145950634400 : Int) atom0962Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6636980507904 : Int) atom0963Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10513332203904 : Int) atom0964Coded) (CoefficientMerge.scale (8483261128704 : Int) atom0965Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8890145167104 : Int) atom0966Coded) (CoefficientMerge.scale (9244119688704 : Int) atom0967Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8443635842304 : Int) atom0968Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9220678043904 : Int) atom0969Coded) (CoefficientMerge.scale (9997720245504 : Int) atom0970Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19013184407808 : Int) atom0971Coded) (CoefficientMerge.scale (15624546121440 : Int) atom0972Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20172537623808 : Int) atom0973Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25324113470112 : Int) atom0974Coded) (CoefficientMerge.scale (31531477635360 : Int) atom0975Coded)))))))) := by decide +kernel
theorem block013_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block013 := by
  rw [block013_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0896Coded_nonneg g hg hA hB) (atom0897Coded_nonneg g hg hA hB)) (add_nonneg (atom0898Coded_nonneg g hg hA hB) (add_nonneg (atom0899Coded_nonneg g hg hA hB) (atom0900Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0901Coded_nonneg g hg hA hB) (atom0902Coded_nonneg g hg hA hB)) (add_nonneg (atom0903Coded_nonneg g hg hA hB) (add_nonneg (atom0904Coded_nonneg g hg hA hB) (atom0905Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0906Coded_nonneg g hg hA hB) (atom0907Coded_nonneg g hg hA hB)) (add_nonneg (atom0908Coded_nonneg g hg hA hB) (add_nonneg (atom0909Coded_nonneg g hg hA hB) (atom0910Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0911Coded_nonneg g hg hA hB) (atom0912Coded_nonneg g hg hA hB)) (add_nonneg (atom0913Coded_nonneg g hg hA hB) (add_nonneg (atom0914Coded_nonneg g hg hA hB) (atom0915Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0916Coded_nonneg g hg hA hB) (atom0917Coded_nonneg g hg hA hB)) (add_nonneg (atom0918Coded_nonneg g hg hA hB) (add_nonneg (atom0919Coded_nonneg g hg hA hB) (atom0920Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0921Coded_nonneg g hg hA hB) (atom0922Coded_nonneg g hg hA hB)) (add_nonneg (atom0923Coded_nonneg g hg hA hB) (add_nonneg (atom0924Coded_nonneg g hg hA hB) (atom0925Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0926Coded_nonneg g hg hA hB) (atom0927Coded_nonneg g hg hA hB)) (add_nonneg (atom0928Coded_nonneg g hg hA hB) (add_nonneg (atom0929Coded_nonneg g hg hA hB) (atom0930Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0931Coded_nonneg g hg hA hB) (atom0932Coded_nonneg g hg hA hB)) (add_nonneg (atom0933Coded_nonneg g hg hA hB) (add_nonneg (atom0934Coded_nonneg g hg hA hB) (atom0935Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0936Coded_nonneg g hg hA hB) (atom0937Coded_nonneg g hg hA hB)) (add_nonneg (atom0938Coded_nonneg g hg hA hB) (add_nonneg (atom0939Coded_nonneg g hg hA hB) (atom0940Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0941Coded_nonneg g hg hA hB) (atom0942Coded_nonneg g hg hA hB)) (add_nonneg (atom0943Coded_nonneg g hg hA hB) (add_nonneg (atom0944Coded_nonneg g hg hA hB) (atom0945Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0946Coded_nonneg g hg hA hB) (atom0947Coded_nonneg g hg hA hB)) (add_nonneg (atom0948Coded_nonneg g hg hA hB) (add_nonneg (atom0949Coded_nonneg g hg hA hB) (atom0950Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0951Coded_nonneg g hg hA hB) (atom0952Coded_nonneg g hg hA hB)) (add_nonneg (atom0953Coded_nonneg g hg hA hB) (add_nonneg (atom0954Coded_nonneg g hg hA hB) (atom0955Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0956Coded_nonneg g hg hA hB) (atom0957Coded_nonneg g hg hA hB)) (add_nonneg (atom0958Coded_nonneg g hg hA hB) (add_nonneg (atom0959Coded_nonneg g hg hA hB) (atom0960Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0961Coded_nonneg g hg hA hB) (atom0962Coded_nonneg g hg hA hB)) (add_nonneg (atom0963Coded_nonneg g hg hA hB) (add_nonneg (atom0964Coded_nonneg g hg hA hB) (atom0965Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0966Coded_nonneg g hg hA hB) (atom0967Coded_nonneg g hg hA hB)) (add_nonneg (atom0968Coded_nonneg g hg hA hB) (add_nonneg (atom0969Coded_nonneg g hg hA hB) (atom0970Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0971Coded_nonneg g hg hA hB) (atom0972Coded_nonneg g hg hA hB)) (add_nonneg (atom0973Coded_nonneg g hg hA hB) (add_nonneg (atom0974Coded_nonneg g hg hA hB) (atom0975Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
