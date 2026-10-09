import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom1055 : SparsePolynomial.Poly := [([10,15,15], 1)]
theorem eval_atom1055 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1055 = ((g 10) * (g 15) * (g 15)) := by
  norm_num [atom1055, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1055_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6248911920 : Int) atom1055) := by
  rw [SparsePolynomial.eval_scale, eval_atom1055]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1055Coded : CoefficientMerge.Poly := [(3525, 1)]
theorem atom1055Coded_decode : atom1055 = SparsePolynomial.decodeCubic 18 atom1055Coded := by decide +kernel
theorem atom1055Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6248911920 : Int) atom1055Coded) := by
  have h := atom1055_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1055Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1056 : SparsePolynomial.Poly := [([10,15,16], 1)]
theorem eval_atom1056 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1056 = ((g 10) * (g 15) * (g 16)) := by
  norm_num [atom1056, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1056_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13592934960 : Int) atom1056) := by
  rw [SparsePolynomial.eval_scale, eval_atom1056]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1056Coded : CoefficientMerge.Poly := [(3526, 1)]
theorem atom1056Coded_decode : atom1056 = SparsePolynomial.decodeCubic 18 atom1056Coded := by decide +kernel
theorem atom1056Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13592934960 : Int) atom1056Coded) := by
  have h := atom1056_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1056Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1057 : SparsePolynomial.Poly := [([10,15,17], 1)]
theorem eval_atom1057 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1057 = ((g 10) * (g 15) * (g 17)) := by
  norm_num [atom1057, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1057_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20673746760 : Int) atom1057) := by
  rw [SparsePolynomial.eval_scale, eval_atom1057]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1057Coded : CoefficientMerge.Poly := [(3527, 1)]
theorem atom1057Coded_decode : atom1057 = SparsePolynomial.decodeCubic 18 atom1057Coded := by decide +kernel
theorem atom1057Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (20673746760 : Int) atom1057Coded) := by
  have h := atom1057_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1057Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1058 : SparsePolynomial.Poly := [([10,16,16], 1)]
theorem eval_atom1058 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1058 = ((g 10) * (g 16) * (g 16)) := by
  norm_num [atom1058, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1058_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5852063040 : Int) atom1058) := by
  rw [SparsePolynomial.eval_scale, eval_atom1058]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1058Coded : CoefficientMerge.Poly := [(3544, 1)]
theorem atom1058Coded_decode : atom1058 = SparsePolynomial.decodeCubic 18 atom1058Coded := by decide +kernel
theorem atom1058Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5852063040 : Int) atom1058Coded) := by
  have h := atom1058_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1058Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1059 : SparsePolynomial.Poly := [([10,16,17], 1)]
theorem eval_atom1059 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1059 = ((g 10) * (g 16) * (g 17)) := by
  norm_num [atom1059, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1059_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19571583720 : Int) atom1059) := by
  rw [SparsePolynomial.eval_scale, eval_atom1059]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1059Coded : CoefficientMerge.Poly := [(3545, 1)]
theorem atom1059Coded_decode : atom1059 = SparsePolynomial.decodeCubic 18 atom1059Coded := by decide +kernel
theorem atom1059Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (19571583720 : Int) atom1059Coded) := by
  have h := atom1059_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1059Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1060 : SparsePolynomial.Poly := [([10,17,17], 1)]
theorem eval_atom1060 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1060 = ((g 10) * (g 17) * (g 17)) := by
  norm_num [atom1060, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1060_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12795525120 : Int) atom1060) := by
  rw [SparsePolynomial.eval_scale, eval_atom1060]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1060Coded : CoefficientMerge.Poly := [(3563, 1)]
theorem atom1060Coded_decode : atom1060 = SparsePolynomial.decodeCubic 18 atom1060Coded := by decide +kernel
theorem atom1060Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12795525120 : Int) atom1060Coded) := by
  have h := atom1060_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1060Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1061 : SparsePolynomial.Poly := [([11,11,11], 1)]
theorem eval_atom1061 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1061 = ((g 11) * (g 11) * (g 11)) := by
  norm_num [atom1061, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1061_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (352235520 : Int) atom1061) := by
  rw [SparsePolynomial.eval_scale, eval_atom1061]
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 11) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1061Coded : CoefficientMerge.Poly := [(3773, 1)]
theorem atom1061Coded_decode : atom1061 = SparsePolynomial.decodeCubic 18 atom1061Coded := by decide +kernel
theorem atom1061Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (352235520 : Int) atom1061Coded) := by
  have h := atom1061_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1061Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1062 : SparsePolynomial.Poly := [([11,11,14], 1)]
theorem eval_atom1062 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1062 = ((g 11) * (g 11) * (g 14)) := by
  norm_num [atom1062, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1062_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1293593040 : Int) atom1062) := by
  rw [SparsePolynomial.eval_scale, eval_atom1062]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1062Coded : CoefficientMerge.Poly := [(3776, 1)]
theorem atom1062Coded_decode : atom1062 = SparsePolynomial.decodeCubic 18 atom1062Coded := by decide +kernel
theorem atom1062Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1293593040 : Int) atom1062Coded) := by
  have h := atom1062_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1062Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1063 : SparsePolynomial.Poly := [([11,11,15], 1)]
theorem eval_atom1063 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1063 = ((g 11) * (g 11) * (g 15)) := by
  norm_num [atom1063, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1063_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1033482240 : Int) atom1063) := by
  rw [SparsePolynomial.eval_scale, eval_atom1063]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1063Coded : CoefficientMerge.Poly := [(3777, 1)]
theorem atom1063Coded_decode : atom1063 = SparsePolynomial.decodeCubic 18 atom1063Coded := by decide +kernel
theorem atom1063Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1033482240 : Int) atom1063Coded) := by
  have h := atom1063_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1063Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1064 : SparsePolynomial.Poly := [([11,11,17], 1)]
theorem eval_atom1064 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1064 = ((g 11) * (g 11) * (g 17)) := by
  norm_num [atom1064, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1064_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2519838720 : Int) atom1064) := by
  rw [SparsePolynomial.eval_scale, eval_atom1064]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1064Coded : CoefficientMerge.Poly := [(3779, 1)]
theorem atom1064Coded_decode : atom1064 = SparsePolynomial.decodeCubic 18 atom1064Coded := by decide +kernel
theorem atom1064Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2519838720 : Int) atom1064Coded) := by
  have h := atom1064_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1064Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1065 : SparsePolynomial.Poly := [([11,12,13], 1)]
theorem eval_atom1065 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1065 = ((g 11) * (g 12) * (g 13)) := by
  norm_num [atom1065, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1065_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (974776320 : Int) atom1065) := by
  rw [SparsePolynomial.eval_scale, eval_atom1065]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1065Coded : CoefficientMerge.Poly := [(3793, 1)]
theorem atom1065Coded_decode : atom1065 = SparsePolynomial.decodeCubic 18 atom1065Coded := by decide +kernel
theorem atom1065Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (974776320 : Int) atom1065Coded) := by
  have h := atom1065_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1065Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1066 : SparsePolynomial.Poly := [([11,12,14], 1)]
theorem eval_atom1066 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1066 = ((g 11) * (g 12) * (g 14)) := by
  norm_num [atom1066, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1066_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8131347360 : Int) atom1066) := by
  rw [SparsePolynomial.eval_scale, eval_atom1066]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1066Coded : CoefficientMerge.Poly := [(3794, 1)]
theorem atom1066Coded_decode : atom1066 = SparsePolynomial.decodeCubic 18 atom1066Coded := by decide +kernel
theorem atom1066Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8131347360 : Int) atom1066Coded) := by
  have h := atom1066_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1066Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1067 : SparsePolynomial.Poly := [([11,12,15], 1)]
theorem eval_atom1067 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1067 = ((g 11) * (g 12) * (g 15)) := by
  norm_num [atom1067, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1067_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9358755840 : Int) atom1067) := by
  rw [SparsePolynomial.eval_scale, eval_atom1067]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1067Coded : CoefficientMerge.Poly := [(3795, 1)]
theorem atom1067Coded_decode : atom1067 = SparsePolynomial.decodeCubic 18 atom1067Coded := by decide +kernel
theorem atom1067Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9358755840 : Int) atom1067Coded) := by
  have h := atom1067_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1067Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1068 : SparsePolynomial.Poly := [([11,12,16], 1)]
theorem eval_atom1068 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1068 = ((g 11) * (g 12) * (g 16)) := by
  norm_num [atom1068, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1068_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6750535680 : Int) atom1068) := by
  rw [SparsePolynomial.eval_scale, eval_atom1068]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1068Coded : CoefficientMerge.Poly := [(3796, 1)]
theorem atom1068Coded_decode : atom1068 = SparsePolynomial.decodeCubic 18 atom1068Coded := by decide +kernel
theorem atom1068Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6750535680 : Int) atom1068Coded) := by
  have h := atom1068_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1068Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1069 : SparsePolynomial.Poly := [([11,12,17], 1)]
theorem eval_atom1069 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1069 = ((g 11) * (g 12) * (g 17)) := by
  norm_num [atom1069, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1069_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14862597120 : Int) atom1069) := by
  rw [SparsePolynomial.eval_scale, eval_atom1069]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1069Coded : CoefficientMerge.Poly := [(3797, 1)]
theorem atom1069Coded_decode : atom1069 = SparsePolynomial.decodeCubic 18 atom1069Coded := by decide +kernel
theorem atom1069Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (14862597120 : Int) atom1069Coded) := by
  have h := atom1069_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1069Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1070 : SparsePolynomial.Poly := [([11,13,13], 1)]
theorem eval_atom1070 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1070 = ((g 11) * (g 13) * (g 13)) := by
  norm_num [atom1070, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1070_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (276369408 : Int) atom1070) := by
  rw [SparsePolynomial.eval_scale, eval_atom1070]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1070Coded : CoefficientMerge.Poly := [(3811, 1)]
theorem atom1070Coded_decode : atom1070 = SparsePolynomial.decodeCubic 18 atom1070Coded := by decide +kernel
theorem atom1070Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (276369408 : Int) atom1070Coded) := by
  have h := atom1070_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1070Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1071 : SparsePolynomial.Poly := [([11,13,14], 1)]
theorem eval_atom1071 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1071 = ((g 11) * (g 13) * (g 14)) := by
  norm_num [atom1071, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1071_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7144572600 : Int) atom1071) := by
  rw [SparsePolynomial.eval_scale, eval_atom1071]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1071Coded : CoefficientMerge.Poly := [(3812, 1)]
theorem atom1071Coded_decode : atom1071 = SparsePolynomial.decodeCubic 18 atom1071Coded := by decide +kernel
theorem atom1071Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7144572600 : Int) atom1071Coded) := by
  have h := atom1071_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1071Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1072 : SparsePolynomial.Poly := [([11,13,15], 1)]
theorem eval_atom1072 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1072 = ((g 11) * (g 13) * (g 15)) := by
  norm_num [atom1072, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1072_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10606740480 : Int) atom1072) := by
  rw [SparsePolynomial.eval_scale, eval_atom1072]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1072Coded : CoefficientMerge.Poly := [(3813, 1)]
theorem atom1072Coded_decode : atom1072 = SparsePolynomial.decodeCubic 18 atom1072Coded := by decide +kernel
theorem atom1072Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10606740480 : Int) atom1072Coded) := by
  have h := atom1072_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1072Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1073 : SparsePolynomial.Poly := [([11,13,16], 1)]
theorem eval_atom1073 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1073 = ((g 11) * (g 13) * (g 16)) := by
  norm_num [atom1073, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1073_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10354176000 : Int) atom1073) := by
  rw [SparsePolynomial.eval_scale, eval_atom1073]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1073Coded : CoefficientMerge.Poly := [(3814, 1)]
theorem atom1073Coded_decode : atom1073 = SparsePolynomial.decodeCubic 18 atom1073Coded := by decide +kernel
theorem atom1073Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10354176000 : Int) atom1073Coded) := by
  have h := atom1073_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1073Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1074 : SparsePolynomial.Poly := [([11,13,17], 1)]
theorem eval_atom1074 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1074 = ((g 11) * (g 13) * (g 17)) := by
  norm_num [atom1074, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1074_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15571422720 : Int) atom1074) := by
  rw [SparsePolynomial.eval_scale, eval_atom1074]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1074Coded : CoefficientMerge.Poly := [(3815, 1)]
theorem atom1074Coded_decode : atom1074 = SparsePolynomial.decodeCubic 18 atom1074Coded := by decide +kernel
theorem atom1074Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (15571422720 : Int) atom1074Coded) := by
  have h := atom1074_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1074Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1075 : SparsePolynomial.Poly := [([11,14,14], 1)]
theorem eval_atom1075 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1075 = ((g 11) * (g 14) * (g 14)) := by
  norm_num [atom1075, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1075_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6980067000 : Int) atom1075) := by
  rw [SparsePolynomial.eval_scale, eval_atom1075]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1075Coded : CoefficientMerge.Poly := [(3830, 1)]
theorem atom1075Coded_decode : atom1075 = SparsePolynomial.decodeCubic 18 atom1075Coded := by decide +kernel
theorem atom1075Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6980067000 : Int) atom1075Coded) := by
  have h := atom1075_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1075Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1076 : SparsePolynomial.Poly := [([11,14,15], 1)]
theorem eval_atom1076 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1076 = ((g 11) * (g 14) * (g 15)) := by
  norm_num [atom1076, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1076_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14752472760 : Int) atom1076) := by
  rw [SparsePolynomial.eval_scale, eval_atom1076]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1076Coded : CoefficientMerge.Poly := [(3831, 1)]
theorem atom1076Coded_decode : atom1076 = SparsePolynomial.decodeCubic 18 atom1076Coded := by decide +kernel
theorem atom1076Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (14752472760 : Int) atom1076Coded) := by
  have h := atom1076_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1076Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1077 : SparsePolynomial.Poly := [([11,14,16], 1)]
theorem eval_atom1077 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1077 = ((g 11) * (g 14) * (g 16)) := by
  norm_num [atom1077, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1077_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15437203920 : Int) atom1077) := by
  rw [SparsePolynomial.eval_scale, eval_atom1077]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1077Coded : CoefficientMerge.Poly := [(3832, 1)]
theorem atom1077Coded_decode : atom1077 = SparsePolynomial.decodeCubic 18 atom1077Coded := by decide +kernel
theorem atom1077Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (15437203920 : Int) atom1077Coded) := by
  have h := atom1077_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1077Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1078 : SparsePolynomial.Poly := [([11,14,17], 1)]
theorem eval_atom1078 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1078 = ((g 11) * (g 14) * (g 17)) := by
  norm_num [atom1078, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1078_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21398112720 : Int) atom1078) := by
  rw [SparsePolynomial.eval_scale, eval_atom1078]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1078Coded : CoefficientMerge.Poly := [(3833, 1)]
theorem atom1078Coded_decode : atom1078 = SparsePolynomial.decodeCubic 18 atom1078Coded := by decide +kernel
theorem atom1078Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (21398112720 : Int) atom1078Coded) := by
  have h := atom1078_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1078Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1079 : SparsePolynomial.Poly := [([11,15,15], 1)]
theorem eval_atom1079 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1079 = ((g 11) * (g 15) * (g 15)) := by
  norm_num [atom1079, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1079_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6526033920 : Int) atom1079) := by
  rw [SparsePolynomial.eval_scale, eval_atom1079]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1079Coded : CoefficientMerge.Poly := [(3849, 1)]
theorem atom1079Coded_decode : atom1079 = SparsePolynomial.decodeCubic 18 atom1079Coded := by decide +kernel
theorem atom1079Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6526033920 : Int) atom1079Coded) := by
  have h := atom1079_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1079Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1080 : SparsePolynomial.Poly := [([11,15,16], 1)]
theorem eval_atom1080 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1080 = ((g 11) * (g 15) * (g 16)) := by
  norm_num [atom1080, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1080_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16063488000 : Int) atom1080) := by
  rw [SparsePolynomial.eval_scale, eval_atom1080]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1080Coded : CoefficientMerge.Poly := [(3850, 1)]
theorem atom1080Coded_decode : atom1080 = SparsePolynomial.decodeCubic 18 atom1080Coded := by decide +kernel
theorem atom1080Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (16063488000 : Int) atom1080Coded) := by
  have h := atom1080_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1080Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1081 : SparsePolynomial.Poly := [([11,15,17], 1)]
theorem eval_atom1081 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1081 = ((g 11) * (g 15) * (g 17)) := by
  norm_num [atom1081, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1081_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22628229120 : Int) atom1081) := by
  rw [SparsePolynomial.eval_scale, eval_atom1081]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1081Coded : CoefficientMerge.Poly := [(3851, 1)]
theorem atom1081Coded_decode : atom1081 = SparsePolynomial.decodeCubic 18 atom1081Coded := by decide +kernel
theorem atom1081Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (22628229120 : Int) atom1081Coded) := by
  have h := atom1081_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1081Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1082 : SparsePolynomial.Poly := [([11,16,16], 1)]
theorem eval_atom1082 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1082 = ((g 11) * (g 16) * (g 16)) := by
  norm_num [atom1082, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1082_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8291082240 : Int) atom1082) := by
  rw [SparsePolynomial.eval_scale, eval_atom1082]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1082Coded : CoefficientMerge.Poly := [(3868, 1)]
theorem atom1082Coded_decode : atom1082 = SparsePolynomial.decodeCubic 18 atom1082Coded := by decide +kernel
theorem atom1082Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8291082240 : Int) atom1082Coded) := by
  have h := atom1082_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1082Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1083 : SparsePolynomial.Poly := [([11,16,17], 1)]
theorem eval_atom1083 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1083 = ((g 11) * (g 16) * (g 17)) := by
  norm_num [atom1083, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1083_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23750737920 : Int) atom1083) := by
  rw [SparsePolynomial.eval_scale, eval_atom1083]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1083Coded : CoefficientMerge.Poly := [(3869, 1)]
theorem atom1083Coded_decode : atom1083 = SparsePolynomial.decodeCubic 18 atom1083Coded := by decide +kernel
theorem atom1083Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (23750737920 : Int) atom1083Coded) := by
  have h := atom1083_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1083Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1084 : SparsePolynomial.Poly := [([11,17,17], 1)]
theorem eval_atom1084 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1084 = ((g 11) * (g 17) * (g 17)) := by
  norm_num [atom1084, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1084_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14213283840 : Int) atom1084) := by
  rw [SparsePolynomial.eval_scale, eval_atom1084]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1084Coded : CoefficientMerge.Poly := [(3887, 1)]
theorem atom1084Coded_decode : atom1084 = SparsePolynomial.decodeCubic 18 atom1084Coded := by decide +kernel
theorem atom1084Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (14213283840 : Int) atom1084Coded) := by
  have h := atom1084_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1084Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1085 : SparsePolynomial.Poly := [([12,12,12], 1)]
theorem eval_atom1085 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1085 = ((g 12) * (g 12) * (g 12)) := by
  norm_num [atom1085, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1085_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (173537280 : Int) atom1085) := by
  rw [SparsePolynomial.eval_scale, eval_atom1085]
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 12) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1085Coded : CoefficientMerge.Poly := [(4116, 1)]
theorem atom1085Coded_decode : atom1085 = SparsePolynomial.decodeCubic 18 atom1085Coded := by decide +kernel
theorem atom1085Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (173537280 : Int) atom1085Coded) := by
  have h := atom1085_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1085Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1086 : SparsePolynomial.Poly := [([12,12,13], 1)]
theorem eval_atom1086 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1086 = ((g 12) * (g 12) * (g 13)) := by
  norm_num [atom1086, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1086_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1318625280 : Int) atom1086) := by
  rw [SparsePolynomial.eval_scale, eval_atom1086]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 12) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1086Coded : CoefficientMerge.Poly := [(4117, 1)]
theorem atom1086Coded_decode : atom1086 = SparsePolynomial.decodeCubic 18 atom1086Coded := by decide +kernel
theorem atom1086Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1318625280 : Int) atom1086Coded) := by
  have h := atom1086_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1086Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1087 : SparsePolynomial.Poly := [([12,12,14], 1)]
theorem eval_atom1087 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1087 = ((g 12) * (g 12) * (g 14)) := by
  norm_num [atom1087, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1087_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5562352080 : Int) atom1087) := by
  rw [SparsePolynomial.eval_scale, eval_atom1087]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1087Coded : CoefficientMerge.Poly := [(4118, 1)]
theorem atom1087Coded_decode : atom1087 = SparsePolynomial.decodeCubic 18 atom1087Coded := by decide +kernel
theorem atom1087Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5562352080 : Int) atom1087Coded) := by
  have h := atom1087_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1087Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1088 : SparsePolynomial.Poly := [([12,12,15], 1)]
theorem eval_atom1088 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1088 = ((g 12) * (g 12) * (g 15)) := by
  norm_num [atom1088, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1088_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6467973120 : Int) atom1088) := by
  rw [SparsePolynomial.eval_scale, eval_atom1088]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 12) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1088Coded : CoefficientMerge.Poly := [(4119, 1)]
theorem atom1088Coded_decode : atom1088 = SparsePolynomial.decodeCubic 18 atom1088Coded := by decide +kernel
theorem atom1088Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6467973120 : Int) atom1088Coded) := by
  have h := atom1088_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1088Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1089 : SparsePolynomial.Poly := [([12,12,16], 1)]
theorem eval_atom1089 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1089 = ((g 12) * (g 12) * (g 16)) := by
  norm_num [atom1089, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1089_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3712665600 : Int) atom1089) := by
  rw [SparsePolynomial.eval_scale, eval_atom1089]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1089Coded : CoefficientMerge.Poly := [(4120, 1)]
theorem atom1089Coded_decode : atom1089 = SparsePolynomial.decodeCubic 18 atom1089Coded := by decide +kernel
theorem atom1089Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3712665600 : Int) atom1089Coded) := by
  have h := atom1089_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1089Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1090 : SparsePolynomial.Poly := [([12,12,17], 1)]
theorem eval_atom1090 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1090 = ((g 12) * (g 12) * (g 17)) := by
  norm_num [atom1090, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1090_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8064000000 : Int) atom1090) := by
  rw [SparsePolynomial.eval_scale, eval_atom1090]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1090Coded : CoefficientMerge.Poly := [(4121, 1)]
theorem atom1090Coded_decode : atom1090 = SparsePolynomial.decodeCubic 18 atom1090Coded := by decide +kernel
theorem atom1090Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8064000000 : Int) atom1090Coded) := by
  have h := atom1090_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1090Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1091 : SparsePolynomial.Poly := [([12,13,13], 1)]
theorem eval_atom1091 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1091 = ((g 12) * (g 13) * (g 13)) := by
  norm_num [atom1091, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1091_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1465454592 : Int) atom1091) := by
  rw [SparsePolynomial.eval_scale, eval_atom1091]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 12) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1091Coded : CoefficientMerge.Poly := [(4135, 1)]
theorem atom1091Coded_decode : atom1091 = SparsePolynomial.decodeCubic 18 atom1091Coded := by decide +kernel
theorem atom1091Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1465454592 : Int) atom1091Coded) := by
  have h := atom1091_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1091Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1092 : SparsePolynomial.Poly := [([12,13,14], 1)]
theorem eval_atom1092 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1092 = ((g 12) * (g 13) * (g 14)) := by
  norm_num [atom1092, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1092_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10728214200 : Int) atom1092) := by
  rw [SparsePolynomial.eval_scale, eval_atom1092]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1092Coded : CoefficientMerge.Poly := [(4136, 1)]
theorem atom1092Coded_decode : atom1092 = SparsePolynomial.decodeCubic 18 atom1092Coded := by decide +kernel
theorem atom1092Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10728214200 : Int) atom1092Coded) := by
  have h := atom1092_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1092Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1093 : SparsePolynomial.Poly := [([12,13,15], 1)]
theorem eval_atom1093 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1093 = ((g 12) * (g 13) * (g 15)) := by
  norm_num [atom1093, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1093_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14916464640 : Int) atom1093) := by
  rw [SparsePolynomial.eval_scale, eval_atom1093]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 12) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1093Coded : CoefficientMerge.Poly := [(4137, 1)]
theorem atom1093Coded_decode : atom1093 = SparsePolynomial.decodeCubic 18 atom1093Coded := by decide +kernel
theorem atom1093Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (14916464640 : Int) atom1093Coded) := by
  have h := atom1093_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1093Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1094 : SparsePolynomial.Poly := [([12,13,16], 1)]
theorem eval_atom1094 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1094 = ((g 12) * (g 13) * (g 16)) := by
  norm_num [atom1094, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1094_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11836661760 : Int) atom1094) := by
  rw [SparsePolynomial.eval_scale, eval_atom1094]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1094Coded : CoefficientMerge.Poly := [(4138, 1)]
theorem atom1094Coded_decode : atom1094 = SparsePolynomial.decodeCubic 18 atom1094Coded := by decide +kernel
theorem atom1094Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11836661760 : Int) atom1094Coded) := by
  have h := atom1094_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1094Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1095 : SparsePolynomial.Poly := [([12,13,17], 1)]
theorem eval_atom1095 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1095 = ((g 12) * (g 13) * (g 17)) := by
  norm_num [atom1095, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1095_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17640161280 : Int) atom1095) := by
  rw [SparsePolynomial.eval_scale, eval_atom1095]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1095Coded : CoefficientMerge.Poly := [(4139, 1)]
theorem atom1095Coded_decode : atom1095 = SparsePolynomial.decodeCubic 18 atom1095Coded := by decide +kernel
theorem atom1095Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (17640161280 : Int) atom1095Coded) := by
  have h := atom1095_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1095Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1096 : SparsePolynomial.Poly := [([12,14,14], 1)]
theorem eval_atom1096 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1096 = ((g 12) * (g 14) * (g 14)) := by
  norm_num [atom1096, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1096_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8611575480 : Int) atom1096) := by
  rw [SparsePolynomial.eval_scale, eval_atom1096]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1096Coded : CoefficientMerge.Poly := [(4154, 1)]
theorem atom1096Coded_decode : atom1096 = SparsePolynomial.decodeCubic 18 atom1096Coded := by decide +kernel
theorem atom1096Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8611575480 : Int) atom1096Coded) := by
  have h := atom1096_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1096Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1097 : SparsePolynomial.Poly := [([12,14,15], 1)]
theorem eval_atom1097 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1097 = ((g 12) * (g 14) * (g 15)) := by
  norm_num [atom1097, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1097_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18512232120 : Int) atom1097) := by
  rw [SparsePolynomial.eval_scale, eval_atom1097]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 12) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1097Coded : CoefficientMerge.Poly := [(4155, 1)]
theorem atom1097Coded_decode : atom1097 = SparsePolynomial.decodeCubic 18 atom1097Coded := by decide +kernel
theorem atom1097Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (18512232120 : Int) atom1097Coded) := by
  have h := atom1097_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1097Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1098 : SparsePolynomial.Poly := [([12,14,16], 1)]
theorem eval_atom1098 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1098 = ((g 12) * (g 14) * (g 16)) := by
  norm_num [atom1098, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1098_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16140384720 : Int) atom1098) := by
  rw [SparsePolynomial.eval_scale, eval_atom1098]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1098Coded : CoefficientMerge.Poly := [(4156, 1)]
theorem atom1098Coded_decode : atom1098 = SparsePolynomial.decodeCubic 18 atom1098Coded := by decide +kernel
theorem atom1098Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (16140384720 : Int) atom1098Coded) := by
  have h := atom1098_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1098Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1099 : SparsePolynomial.Poly := [([12,14,17], 1)]
theorem eval_atom1099 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1099 = ((g 12) * (g 14) * (g 17)) := by
  norm_num [atom1099, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1099_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15706609200 : Int) atom1099) := by
  rw [SparsePolynomial.eval_scale, eval_atom1099]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1099Coded : CoefficientMerge.Poly := [(4157, 1)]
theorem atom1099Coded_decode : atom1099 = SparsePolynomial.decodeCubic 18 atom1099Coded := by decide +kernel
theorem atom1099Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (15706609200 : Int) atom1099Coded) := by
  have h := atom1099_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1099Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1100 : SparsePolynomial.Poly := [([12,15,15], 1)]
theorem eval_atom1100 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1100 = ((g 12) * (g 15) * (g 15)) := by
  norm_num [atom1100, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1100_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8550420480 : Int) atom1100) := by
  rw [SparsePolynomial.eval_scale, eval_atom1100]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 12) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1100Coded : CoefficientMerge.Poly := [(4173, 1)]
theorem atom1100Coded_decode : atom1100 = SparsePolynomial.decodeCubic 18 atom1100Coded := by decide +kernel
theorem atom1100Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8550420480 : Int) atom1100Coded) := by
  have h := atom1100_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1100Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1101 : SparsePolynomial.Poly := [([12,15,16], 1)]
theorem eval_atom1101 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1101 = ((g 12) * (g 15) * (g 16)) := by
  norm_num [atom1101, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1101_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17106001920 : Int) atom1101) := by
  rw [SparsePolynomial.eval_scale, eval_atom1101]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1101Coded : CoefficientMerge.Poly := [(4174, 1)]
theorem atom1101Coded_decode : atom1101 = SparsePolynomial.decodeCubic 18 atom1101Coded := by decide +kernel
theorem atom1101Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (17106001920 : Int) atom1101Coded) := by
  have h := atom1101_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1101Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1102 : SparsePolynomial.Poly := [([12,15,17], 1)]
theorem eval_atom1102 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1102 = ((g 12) * (g 15) * (g 17)) := by
  norm_num [atom1102, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1102_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17111162880 : Int) atom1102) := by
  rw [SparsePolynomial.eval_scale, eval_atom1102]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1102Coded : CoefficientMerge.Poly := [(4175, 1)]
theorem atom1102Coded_decode : atom1102 = SparsePolynomial.decodeCubic 18 atom1102Coded := by decide +kernel
theorem atom1102Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (17111162880 : Int) atom1102Coded) := by
  have h := atom1102_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1102Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1103 : SparsePolynomial.Poly := [([12,16,16], 1)]
theorem eval_atom1103 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1103 = ((g 12) * (g 16) * (g 16)) := by
  norm_num [atom1103, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1103_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8982005760 : Int) atom1103) := by
  rw [SparsePolynomial.eval_scale, eval_atom1103]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1103Coded : CoefficientMerge.Poly := [(4192, 1)]
theorem atom1103Coded_decode : atom1103 = SparsePolynomial.decodeCubic 18 atom1103Coded := by decide +kernel
theorem atom1103Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8982005760 : Int) atom1103Coded) := by
  have h := atom1103_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1103Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1104 : SparsePolynomial.Poly := [([12,16,17], 1)]
theorem eval_atom1104 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1104 = ((g 12) * (g 16) * (g 17)) := by
  norm_num [atom1104, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1104_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18623324160 : Int) atom1104) := by
  rw [SparsePolynomial.eval_scale, eval_atom1104]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1104Coded : CoefficientMerge.Poly := [(4193, 1)]
theorem atom1104Coded_decode : atom1104 = SparsePolynomial.decodeCubic 18 atom1104Coded := by decide +kernel
theorem atom1104Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (18623324160 : Int) atom1104Coded) := by
  have h := atom1104_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1104Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1105 : SparsePolynomial.Poly := [([12,17,17], 1)]
theorem eval_atom1105 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1105 = ((g 12) * (g 17) * (g 17)) := by
  norm_num [atom1105, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1105_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8291082240 : Int) atom1105) := by
  rw [SparsePolynomial.eval_scale, eval_atom1105]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1105Coded : CoefficientMerge.Poly := [(4211, 1)]
theorem atom1105Coded_decode : atom1105 = SparsePolynomial.decodeCubic 18 atom1105Coded := by decide +kernel
theorem atom1105Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8291082240 : Int) atom1105Coded) := by
  have h := atom1105_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1105Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1106 : SparsePolynomial.Poly := [([13,13,14], 1)]
theorem eval_atom1106 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1106 = ((g 13) * (g 13) * (g 14)) := by
  norm_num [atom1106, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1106_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3449713896 : Int) atom1106) := by
  rw [SparsePolynomial.eval_scale, eval_atom1106]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 13) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1106Coded : CoefficientMerge.Poly := [(4460, 1)]
theorem atom1106Coded_decode : atom1106 = SparsePolynomial.decodeCubic 18 atom1106Coded := by decide +kernel
theorem atom1106Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3449713896 : Int) atom1106Coded) := by
  have h := atom1106_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1106Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1107 : SparsePolynomial.Poly := [([13,13,15], 1)]
theorem eval_atom1107 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1107 = ((g 13) * (g 13) * (g 15)) := by
  norm_num [atom1107, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1107_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6428749824 : Int) atom1107) := by
  rw [SparsePolynomial.eval_scale, eval_atom1107]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 13) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1107Coded : CoefficientMerge.Poly := [(4461, 1)]
theorem atom1107Coded_decode : atom1107 = SparsePolynomial.decodeCubic 18 atom1107Coded := by decide +kernel
theorem atom1107Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6428749824 : Int) atom1107Coded) := by
  have h := atom1107_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1107Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1108 : SparsePolynomial.Poly := [([13,13,16], 1)]
theorem eval_atom1108 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1108 = ((g 13) * (g 13) * (g 16)) := by
  norm_num [atom1108, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1108_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5600931840 : Int) atom1108) := by
  rw [SparsePolynomial.eval_scale, eval_atom1108]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1108Coded : CoefficientMerge.Poly := [(4462, 1)]
theorem atom1108Coded_decode : atom1108 = SparsePolynomial.decodeCubic 18 atom1108Coded := by decide +kernel
theorem atom1108Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5600931840 : Int) atom1108Coded) := by
  have h := atom1108_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1108Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1109 : SparsePolynomial.Poly := [([13,13,17], 1)]
theorem eval_atom1109 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1109 = ((g 13) * (g 13) * (g 17)) := by
  norm_num [atom1109, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1109_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8326434816 : Int) atom1109) := by
  rw [SparsePolynomial.eval_scale, eval_atom1109]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1109Coded : CoefficientMerge.Poly := [(4463, 1)]
theorem atom1109Coded_decode : atom1109 = SparsePolynomial.decodeCubic 18 atom1109Coded := by decide +kernel
theorem atom1109Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8326434816 : Int) atom1109Coded) := by
  have h := atom1109_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1109Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1110 : SparsePolynomial.Poly := [([13,14,14], 1)]
theorem eval_atom1110 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1110 = ((g 13) * (g 14) * (g 14)) := by
  norm_num [atom1110, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1110_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6743566800 : Int) atom1110) := by
  rw [SparsePolynomial.eval_scale, eval_atom1110]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 13) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1110Coded : CoefficientMerge.Poly := [(4478, 1)]
theorem atom1110Coded_decode : atom1110 = SparsePolynomial.decodeCubic 18 atom1110Coded := by decide +kernel
theorem atom1110Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6743566800 : Int) atom1110Coded) := by
  have h := atom1110_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1110Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1111 : SparsePolynomial.Poly := [([13,14,15], 1)]
theorem eval_atom1111 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1111 = ((g 13) * (g 14) * (g 15)) := by
  norm_num [atom1111, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1111_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16995813840 : Int) atom1111) := by
  rw [SparsePolynomial.eval_scale, eval_atom1111]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 13) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1111Coded : CoefficientMerge.Poly := [(4479, 1)]
theorem atom1111Coded_decode : atom1111 = SparsePolynomial.decodeCubic 18 atom1111Coded := by decide +kernel
theorem atom1111Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (16995813840 : Int) atom1111Coded) := by
  have h := atom1111_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1111Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1112 : SparsePolynomial.Poly := [([13,14,16], 1)]
theorem eval_atom1112 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1112 = ((g 13) * (g 14) * (g 16)) := by
  norm_num [atom1112, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1112_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16843565520 : Int) atom1112) := by
  rw [SparsePolynomial.eval_scale, eval_atom1112]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1112Coded : CoefficientMerge.Poly := [(4480, 1)]
theorem atom1112Coded_decode : atom1112 = SparsePolynomial.decodeCubic 18 atom1112Coded := by decide +kernel
theorem atom1112Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (16843565520 : Int) atom1112Coded) := by
  have h := atom1112_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1112Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1113 : SparsePolynomial.Poly := [([13,14,17], 1)]
theorem eval_atom1113 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1113 = ((g 13) * (g 14) * (g 17)) := by
  norm_num [atom1113, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1113_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16906532400 : Int) atom1113) := by
  rw [SparsePolynomial.eval_scale, eval_atom1113]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1113Coded : CoefficientMerge.Poly := [(4481, 1)]
theorem atom1113Coded_decode : atom1113 = SparsePolynomial.decodeCubic 18 atom1113Coded := by decide +kernel
theorem atom1113Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (16906532400 : Int) atom1113Coded) := by
  have h := atom1113_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1113Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1114 : SparsePolynomial.Poly := [([13,15,15], 1)]
theorem eval_atom1114 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1114 = ((g 13) * (g 15) * (g 15)) := by
  norm_num [atom1114, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1114_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8798146560 : Int) atom1114) := by
  rw [SparsePolynomial.eval_scale, eval_atom1114]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 13) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1114Coded : CoefficientMerge.Poly := [(4497, 1)]
theorem atom1114Coded_decode : atom1114 = SparsePolynomial.decodeCubic 18 atom1114Coded := by decide +kernel
theorem atom1114Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8798146560 : Int) atom1114Coded) := by
  have h := atom1114_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1114Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1115 : SparsePolynomial.Poly := [([13,15,16], 1)]
theorem eval_atom1115 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1115 = ((g 13) * (g 15) * (g 16)) := by
  norm_num [atom1115, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1115_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18148515840 : Int) atom1115) := by
  rw [SparsePolynomial.eval_scale, eval_atom1115]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1115Coded : CoefficientMerge.Poly := [(4498, 1)]
theorem atom1115Coded_decode : atom1115 = SparsePolynomial.decodeCubic 18 atom1115Coded := by decide +kernel
theorem atom1115Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (18148515840 : Int) atom1115Coded) := by
  have h := atom1115_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1115Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1116 : SparsePolynomial.Poly := [([13,15,17], 1)]
theorem eval_atom1116 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1116 = ((g 13) * (g 15) * (g 17)) := by
  norm_num [atom1116, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1116_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18700738560 : Int) atom1116) := by
  rw [SparsePolynomial.eval_scale, eval_atom1116]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1116Coded : CoefficientMerge.Poly := [(4499, 1)]
theorem atom1116Coded_decode : atom1116 = SparsePolynomial.decodeCubic 18 atom1116Coded := by decide +kernel
theorem atom1116Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (18700738560 : Int) atom1116Coded) := by
  have h := atom1116_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1116Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1117 : SparsePolynomial.Poly := [([13,16,16], 1)]
theorem eval_atom1117 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1117 = ((g 13) * (g 16) * (g 16)) := by
  norm_num [atom1117, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1117_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9672929280 : Int) atom1117) := by
  rw [SparsePolynomial.eval_scale, eval_atom1117]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1117Coded : CoefficientMerge.Poly := [(4516, 1)]
theorem atom1117Coded_decode : atom1117 = SparsePolynomial.decodeCubic 18 atom1117Coded := by decide +kernel
theorem atom1117Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9672929280 : Int) atom1117Coded) := by
  have h := atom1117_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1117Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1118 : SparsePolynomial.Poly := [([13,16,17], 1)]
theorem eval_atom1118 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1118 = ((g 13) * (g 16) * (g 17)) := by
  norm_num [atom1118, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1118_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20602552320 : Int) atom1118) := by
  rw [SparsePolynomial.eval_scale, eval_atom1118]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1118Coded : CoefficientMerge.Poly := [(4517, 1)]
theorem atom1118Coded_decode : atom1118 = SparsePolynomial.decodeCubic 18 atom1118Coded := by decide +kernel
theorem atom1118Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (20602552320 : Int) atom1118Coded) := by
  have h := atom1118_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1118Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1119 : SparsePolynomial.Poly := [([13,17,17], 1)]
theorem eval_atom1119 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1119 = ((g 13) * (g 17) * (g 17)) := by
  norm_num [atom1119, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1119_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9475522560 : Int) atom1119) := by
  rw [SparsePolynomial.eval_scale, eval_atom1119]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1119Coded : CoefficientMerge.Poly := [(4535, 1)]
theorem atom1119Coded_decode : atom1119 = SparsePolynomial.decodeCubic 18 atom1119Coded := by decide +kernel
theorem atom1119Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9475522560 : Int) atom1119Coded) := by
  have h := atom1119_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1119Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1120 : SparsePolynomial.Poly := [([14,14,14], 1)]
theorem eval_atom1120 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1120 = ((g 14) * (g 14) * (g 14)) := by
  norm_num [atom1120, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1120_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2773757160 : Int) atom1120) := by
  rw [SparsePolynomial.eval_scale, eval_atom1120]
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 14) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1120Coded : CoefficientMerge.Poly := [(4802, 1)]
theorem atom1120Coded_decode : atom1120 = SparsePolynomial.decodeCubic 18 atom1120Coded := by decide +kernel
theorem atom1120Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2773757160 : Int) atom1120Coded) := by
  have h := atom1120_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1120Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1121 : SparsePolynomial.Poly := [([14,14,15], 1)]
theorem eval_atom1121 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1121 = ((g 14) * (g 14) * (g 15)) := by
  norm_num [atom1121, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1121_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8601126120 : Int) atom1121) := by
  rw [SparsePolynomial.eval_scale, eval_atom1121]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 14) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1121Coded : CoefficientMerge.Poly := [(4803, 1)]
theorem atom1121Coded_decode : atom1121 = SparsePolynomial.decodeCubic 18 atom1121Coded := by decide +kernel
theorem atom1121Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8601126120 : Int) atom1121Coded) := by
  have h := atom1121_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1121Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1122 : SparsePolynomial.Poly := [([14,14,16], 1)]
theorem eval_atom1122 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1122 = ((g 14) * (g 14) * (g 16)) := by
  norm_num [atom1122, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1122_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8773373160 : Int) atom1122) := by
  rw [SparsePolynomial.eval_scale, eval_atom1122]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 14) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1122Coded : CoefficientMerge.Poly := [(4804, 1)]
theorem atom1122Coded_decode : atom1122 = SparsePolynomial.decodeCubic 18 atom1122Coded := by decide +kernel
theorem atom1122Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8773373160 : Int) atom1122Coded) := by
  have h := atom1122_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1122Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1123 : SparsePolynomial.Poly := [([14,14,17], 1)]
theorem eval_atom1123 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1123 = ((g 14) * (g 14) * (g 17)) := by
  norm_num [atom1123, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1123_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5607514440 : Int) atom1123) := by
  rw [SparsePolynomial.eval_scale, eval_atom1123]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1123Coded : CoefficientMerge.Poly := [(4805, 1)]
theorem atom1123Coded_decode : atom1123 = SparsePolynomial.decodeCubic 18 atom1123Coded := by decide +kernel
theorem atom1123Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5607514440 : Int) atom1123Coded) := by
  have h := atom1123_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1123Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1124 : SparsePolynomial.Poly := [([14,15,15], 1)]
theorem eval_atom1124 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1124 = ((g 14) * (g 15) * (g 15)) := by
  norm_num [atom1124, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1124_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9045872640 : Int) atom1124) := by
  rw [SparsePolynomial.eval_scale, eval_atom1124]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 14) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1124Coded : CoefficientMerge.Poly := [(4821, 1)]
theorem atom1124Coded_decode : atom1124 = SparsePolynomial.decodeCubic 18 atom1124Coded := by decide +kernel
theorem atom1124Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9045872640 : Int) atom1124Coded) := by
  have h := atom1124_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1124Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1125 : SparsePolynomial.Poly := [([14,15,16], 1)]
theorem eval_atom1125 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1125 = ((g 14) * (g 15) * (g 16)) := by
  norm_num [atom1125, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1125_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19191029760 : Int) atom1125) := by
  rw [SparsePolynomial.eval_scale, eval_atom1125]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 14) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1125Coded : CoefficientMerge.Poly := [(4822, 1)]
theorem atom1125Coded_decode : atom1125 = SparsePolynomial.decodeCubic 18 atom1125Coded := by decide +kernel
theorem atom1125Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (19191029760 : Int) atom1125Coded) := by
  have h := atom1125_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1125Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1126 : SparsePolynomial.Poly := [([14,15,17], 1)]
theorem eval_atom1126 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1126 = ((g 14) * (g 15) * (g 17)) := by
  norm_num [atom1126, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1126_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13398887520 : Int) atom1126) := by
  rw [SparsePolynomial.eval_scale, eval_atom1126]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1126Coded : CoefficientMerge.Poly := [(4823, 1)]
theorem atom1126Coded_decode : atom1126 = SparsePolynomial.decodeCubic 18 atom1126Coded := by decide +kernel
theorem atom1126Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13398887520 : Int) atom1126Coded) := by
  have h := atom1126_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1126Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1127 : SparsePolynomial.Poly := [([14,16,16], 1)]
theorem eval_atom1127 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1127 = ((g 14) * (g 16) * (g 16)) := by
  norm_num [atom1127, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1127_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10363852800 : Int) atom1127) := by
  rw [SparsePolynomial.eval_scale, eval_atom1127]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 14) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1127Coded : CoefficientMerge.Poly := [(4840, 1)]
theorem atom1127Coded_decode : atom1127 = SparsePolynomial.decodeCubic 18 atom1127Coded := by decide +kernel
theorem atom1127Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10363852800 : Int) atom1127Coded) := by
  have h := atom1127_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1127Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1128 : SparsePolynomial.Poly := [([14,16,17], 1)]
theorem eval_atom1128 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1128 = ((g 14) * (g 16) * (g 17)) := by
  norm_num [atom1128, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1128_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15690353760 : Int) atom1128) := by
  rw [SparsePolynomial.eval_scale, eval_atom1128]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1128Coded : CoefficientMerge.Poly := [(4841, 1)]
theorem atom1128Coded_decode : atom1128 = SparsePolynomial.decodeCubic 18 atom1128Coded := by decide +kernel
theorem atom1128Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (15690353760 : Int) atom1128Coded) := by
  have h := atom1128_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1128Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1129 : SparsePolynomial.Poly := [([14,17,17], 1)]
theorem eval_atom1129 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1129 = ((g 14) * (g 17) * (g 17)) := by
  norm_num [atom1129, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1129_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3768536160 : Int) atom1129) := by
  rw [SparsePolynomial.eval_scale, eval_atom1129]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1129Coded : CoefficientMerge.Poly := [(4859, 1)]
theorem atom1129Coded_decode : atom1129 = SparsePolynomial.decodeCubic 18 atom1129Coded := by decide +kernel
theorem atom1129Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3768536160 : Int) atom1129Coded) := by
  have h := atom1129_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1129Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1130 : SparsePolynomial.Poly := [([15,15,15], 1)]
theorem eval_atom1130 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1130 = ((g 15) * (g 15) * (g 15)) := by
  norm_num [atom1130, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1130_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3097866240 : Int) atom1130) := by
  rw [SparsePolynomial.eval_scale, eval_atom1130]
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 15) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1130Coded : CoefficientMerge.Poly := [(5145, 1)]
theorem atom1130Coded_decode : atom1130 = SparsePolynomial.decodeCubic 18 atom1130Coded := by decide +kernel
theorem atom1130Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3097866240 : Int) atom1130Coded) := by
  have h := atom1130_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1130Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1131 : SparsePolynomial.Poly := [([15,15,16], 1)]
theorem eval_atom1131 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1131 = ((g 15) * (g 15) * (g 16)) := by
  norm_num [atom1131, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1131_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10116771840 : Int) atom1131) := by
  rw [SparsePolynomial.eval_scale, eval_atom1131]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 15) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1131Coded : CoefficientMerge.Poly := [(5146, 1)]
theorem atom1131Coded_decode : atom1131 = SparsePolynomial.decodeCubic 18 atom1131Coded := by decide +kernel
theorem atom1131Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10116771840 : Int) atom1131Coded) := by
  have h := atom1131_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1131Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1132 : SparsePolynomial.Poly := [([15,15,17], 1)]
theorem eval_atom1132 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1132 = ((g 15) * (g 15) * (g 17)) := by
  norm_num [atom1132, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1132_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7386624000 : Int) atom1132) := by
  rw [SparsePolynomial.eval_scale, eval_atom1132]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 15) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1132Coded : CoefficientMerge.Poly := [(5147, 1)]
theorem atom1132Coded_decode : atom1132 = SparsePolynomial.decodeCubic 18 atom1132Coded := by decide +kernel
theorem atom1132Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7386624000 : Int) atom1132Coded) := by
  have h := atom1132_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1132Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1133 : SparsePolynomial.Poly := [([15,16,16], 1)]
theorem eval_atom1133 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1133 = ((g 15) * (g 16) * (g 16)) := by
  norm_num [atom1133, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1133_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11054776320 : Int) atom1133) := by
  rw [SparsePolynomial.eval_scale, eval_atom1133]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 15) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1133Coded : CoefficientMerge.Poly := [(5164, 1)]
theorem atom1133Coded_decode : atom1133 = SparsePolynomial.decodeCubic 18 atom1133Coded := by decide +kernel
theorem atom1133Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11054776320 : Int) atom1133Coded) := by
  have h := atom1133_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1133Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1134 : SparsePolynomial.Poly := [([15,16,17], 1)]
theorem eval_atom1134 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom1134 = ((g 15) * (g 16) * (g 17)) := by
  norm_num [atom1134, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1134_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17454366720 : Int) atom1134) := by
  rw [SparsePolynomial.eval_scale, eval_atom1134]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 15) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1134Coded : CoefficientMerge.Poly := [(5165, 1)]
theorem atom1134Coded_decode : atom1134 = SparsePolynomial.decodeCubic 18 atom1134Coded := by decide +kernel
theorem atom1134Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (17454366720 : Int) atom1134Coded) := by
  have h := atom1134_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1134Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block014 : CoefficientMerge.Poly := [(3525, 6248911920), (3526, 13592934960), (3527, 20673746760), (3544, 5852063040), (3545, 19571583720), (3563, 12795525120), (3773, 352235520), (3776, 1293593040), (3777, 1033482240), (3779, 2519838720), (3793, 974776320), (3794, 8131347360), (3795, 9358755840), (3796, 6750535680), (3797, 14862597120), (3811, 276369408), (3812, 7144572600), (3813, 10606740480), (3814, 10354176000), (3815, 15571422720), (3830, 6980067000), (3831, 14752472760), (3832, 15437203920), (3833, 21398112720), (3849, 6526033920), (3850, 16063488000), (3851, 22628229120), (3868, 8291082240), (3869, 23750737920), (3887, 14213283840), (4116, 173537280), (4117, 1318625280), (4118, 5562352080), (4119, 6467973120), (4120, 3712665600), (4121, 8064000000), (4135, 1465454592), (4136, 10728214200), (4137, 14916464640), (4138, 11836661760), (4139, 17640161280), (4154, 8611575480), (4155, 18512232120), (4156, 16140384720), (4157, 15706609200), (4173, 8550420480), (4174, 17106001920), (4175, 17111162880), (4192, 8982005760), (4193, 18623324160), (4211, 8291082240), (4460, 3449713896), (4461, 6428749824), (4462, 5600931840), (4463, 8326434816), (4478, 6743566800), (4479, 16995813840), (4480, 16843565520), (4481, 16906532400), (4497, 8798146560), (4498, 18148515840), (4499, 18700738560), (4516, 9672929280), (4517, 20602552320), (4535, 9475522560), (4802, 2773757160), (4803, 8601126120), (4804, 8773373160), (4805, 5607514440), (4821, 9045872640), (4822, 19191029760), (4823, 13398887520), (4840, 10363852800), (4841, 15690353760), (4859, 3768536160), (5145, 3097866240), (5146, 10116771840), (5147, 7386624000), (5164, 11054776320), (5165, 17454366720)]
theorem block014_data : block014 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6248911920 : Int) atom1055Coded) (CoefficientMerge.scale (13592934960 : Int) atom1056Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20673746760 : Int) atom1057Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5852063040 : Int) atom1058Coded) (CoefficientMerge.scale (19571583720 : Int) atom1059Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12795525120 : Int) atom1060Coded) (CoefficientMerge.scale (352235520 : Int) atom1061Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1293593040 : Int) atom1062Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1033482240 : Int) atom1063Coded) (CoefficientMerge.scale (2519838720 : Int) atom1064Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (974776320 : Int) atom1065Coded) (CoefficientMerge.scale (8131347360 : Int) atom1066Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9358755840 : Int) atom1067Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6750535680 : Int) atom1068Coded) (CoefficientMerge.scale (14862597120 : Int) atom1069Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (276369408 : Int) atom1070Coded) (CoefficientMerge.scale (7144572600 : Int) atom1071Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10606740480 : Int) atom1072Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10354176000 : Int) atom1073Coded) (CoefficientMerge.scale (15571422720 : Int) atom1074Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6980067000 : Int) atom1075Coded) (CoefficientMerge.scale (14752472760 : Int) atom1076Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15437203920 : Int) atom1077Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21398112720 : Int) atom1078Coded) (CoefficientMerge.scale (6526033920 : Int) atom1079Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16063488000 : Int) atom1080Coded) (CoefficientMerge.scale (22628229120 : Int) atom1081Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8291082240 : Int) atom1082Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23750737920 : Int) atom1083Coded) (CoefficientMerge.scale (14213283840 : Int) atom1084Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (173537280 : Int) atom1085Coded) (CoefficientMerge.scale (1318625280 : Int) atom1086Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5562352080 : Int) atom1087Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6467973120 : Int) atom1088Coded) (CoefficientMerge.scale (3712665600 : Int) atom1089Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8064000000 : Int) atom1090Coded) (CoefficientMerge.scale (1465454592 : Int) atom1091Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10728214200 : Int) atom1092Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14916464640 : Int) atom1093Coded) (CoefficientMerge.scale (11836661760 : Int) atom1094Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17640161280 : Int) atom1095Coded) (CoefficientMerge.scale (8611575480 : Int) atom1096Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18512232120 : Int) atom1097Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16140384720 : Int) atom1098Coded) (CoefficientMerge.scale (15706609200 : Int) atom1099Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8550420480 : Int) atom1100Coded) (CoefficientMerge.scale (17106001920 : Int) atom1101Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17111162880 : Int) atom1102Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8982005760 : Int) atom1103Coded) (CoefficientMerge.scale (18623324160 : Int) atom1104Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8291082240 : Int) atom1105Coded) (CoefficientMerge.scale (3449713896 : Int) atom1106Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6428749824 : Int) atom1107Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5600931840 : Int) atom1108Coded) (CoefficientMerge.scale (8326434816 : Int) atom1109Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6743566800 : Int) atom1110Coded) (CoefficientMerge.scale (16995813840 : Int) atom1111Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16843565520 : Int) atom1112Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16906532400 : Int) atom1113Coded) (CoefficientMerge.scale (8798146560 : Int) atom1114Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (18148515840 : Int) atom1115Coded) (CoefficientMerge.scale (18700738560 : Int) atom1116Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9672929280 : Int) atom1117Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20602552320 : Int) atom1118Coded) (CoefficientMerge.scale (9475522560 : Int) atom1119Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2773757160 : Int) atom1120Coded) (CoefficientMerge.scale (8601126120 : Int) atom1121Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8773373160 : Int) atom1122Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5607514440 : Int) atom1123Coded) (CoefficientMerge.scale (9045872640 : Int) atom1124Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19191029760 : Int) atom1125Coded) (CoefficientMerge.scale (13398887520 : Int) atom1126Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10363852800 : Int) atom1127Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15690353760 : Int) atom1128Coded) (CoefficientMerge.scale (3768536160 : Int) atom1129Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3097866240 : Int) atom1130Coded) (CoefficientMerge.scale (10116771840 : Int) atom1131Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7386624000 : Int) atom1132Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11054776320 : Int) atom1133Coded) (CoefficientMerge.scale (17454366720 : Int) atom1134Coded)))))))) := by decide +kernel
theorem block014_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) block014 := by
  rw [block014_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1055Coded_nonneg g hg hA hB) (atom1056Coded_nonneg g hg hA hB)) (add_nonneg (atom1057Coded_nonneg g hg hA hB) (add_nonneg (atom1058Coded_nonneg g hg hA hB) (atom1059Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1060Coded_nonneg g hg hA hB) (atom1061Coded_nonneg g hg hA hB)) (add_nonneg (atom1062Coded_nonneg g hg hA hB) (add_nonneg (atom1063Coded_nonneg g hg hA hB) (atom1064Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1065Coded_nonneg g hg hA hB) (atom1066Coded_nonneg g hg hA hB)) (add_nonneg (atom1067Coded_nonneg g hg hA hB) (add_nonneg (atom1068Coded_nonneg g hg hA hB) (atom1069Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1070Coded_nonneg g hg hA hB) (atom1071Coded_nonneg g hg hA hB)) (add_nonneg (atom1072Coded_nonneg g hg hA hB) (add_nonneg (atom1073Coded_nonneg g hg hA hB) (atom1074Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1075Coded_nonneg g hg hA hB) (atom1076Coded_nonneg g hg hA hB)) (add_nonneg (atom1077Coded_nonneg g hg hA hB) (add_nonneg (atom1078Coded_nonneg g hg hA hB) (atom1079Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1080Coded_nonneg g hg hA hB) (atom1081Coded_nonneg g hg hA hB)) (add_nonneg (atom1082Coded_nonneg g hg hA hB) (add_nonneg (atom1083Coded_nonneg g hg hA hB) (atom1084Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1085Coded_nonneg g hg hA hB) (atom1086Coded_nonneg g hg hA hB)) (add_nonneg (atom1087Coded_nonneg g hg hA hB) (add_nonneg (atom1088Coded_nonneg g hg hA hB) (atom1089Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1090Coded_nonneg g hg hA hB) (atom1091Coded_nonneg g hg hA hB)) (add_nonneg (atom1092Coded_nonneg g hg hA hB) (add_nonneg (atom1093Coded_nonneg g hg hA hB) (atom1094Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1095Coded_nonneg g hg hA hB) (atom1096Coded_nonneg g hg hA hB)) (add_nonneg (atom1097Coded_nonneg g hg hA hB) (add_nonneg (atom1098Coded_nonneg g hg hA hB) (atom1099Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1100Coded_nonneg g hg hA hB) (atom1101Coded_nonneg g hg hA hB)) (add_nonneg (atom1102Coded_nonneg g hg hA hB) (add_nonneg (atom1103Coded_nonneg g hg hA hB) (atom1104Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1105Coded_nonneg g hg hA hB) (atom1106Coded_nonneg g hg hA hB)) (add_nonneg (atom1107Coded_nonneg g hg hA hB) (add_nonneg (atom1108Coded_nonneg g hg hA hB) (atom1109Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1110Coded_nonneg g hg hA hB) (atom1111Coded_nonneg g hg hA hB)) (add_nonneg (atom1112Coded_nonneg g hg hA hB) (add_nonneg (atom1113Coded_nonneg g hg hA hB) (atom1114Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1115Coded_nonneg g hg hA hB) (atom1116Coded_nonneg g hg hA hB)) (add_nonneg (atom1117Coded_nonneg g hg hA hB) (add_nonneg (atom1118Coded_nonneg g hg hA hB) (atom1119Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1120Coded_nonneg g hg hA hB) (atom1121Coded_nonneg g hg hA hB)) (add_nonneg (atom1122Coded_nonneg g hg hA hB) (add_nonneg (atom1123Coded_nonneg g hg hA hB) (atom1124Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1125Coded_nonneg g hg hA hB) (atom1126Coded_nonneg g hg hA hB)) (add_nonneg (atom1127Coded_nonneg g hg hA hB) (add_nonneg (atom1128Coded_nonneg g hg hA hB) (atom1129Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1130Coded_nonneg g hg hA hB) (atom1131Coded_nonneg g hg hA hB)) (add_nonneg (atom1132Coded_nonneg g hg hA hB) (add_nonneg (atom1133Coded_nonneg g hg hA hB) (atom1134Coded_nonneg g hg hA hB))))))))

end APPT.Finite18
