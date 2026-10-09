import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1296 : SparsePolynomial.Poly := [([7,8,15], 1)]
theorem eval_atom1296 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1296 = ((g 7) * (g 8) * (g 15)) := by
  norm_num [atom1296, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1296_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6427474232112 : Int) atom1296) := by
  rw [SparsePolynomial.eval_scale, eval_atom1296]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1296Coded : CoefficientMerge.Poly := [(3270, 1)]
theorem atom1296Coded_decode : atom1296 = SparsePolynomial.decodeCubic 21 atom1296Coded := by decide +kernel
theorem atom1296Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6427474232112 : Int) atom1296Coded) := by
  have h := atom1296_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1296Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1297 : SparsePolynomial.Poly := [([7,8,17], 1)]
theorem eval_atom1297 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1297 = ((g 7) * (g 8) * (g 17)) := by
  norm_num [atom1297, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1297_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1510388496720 : Int) atom1297) := by
  rw [SparsePolynomial.eval_scale, eval_atom1297]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1297Coded : CoefficientMerge.Poly := [(3272, 1)]
theorem atom1297Coded_decode : atom1297 = SparsePolynomial.decodeCubic 21 atom1297Coded := by decide +kernel
theorem atom1297Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1510388496720 : Int) atom1297Coded) := by
  have h := atom1297_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1297Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1298 : SparsePolynomial.Poly := [([7,8,18], 1)]
theorem eval_atom1298 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1298 = ((g 7) * (g 8) * (g 18)) := by
  norm_num [atom1298, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1298_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5786258284800 : Int) atom1298) := by
  rw [SparsePolynomial.eval_scale, eval_atom1298]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1298Coded : CoefficientMerge.Poly := [(3273, 1)]
theorem atom1298Coded_decode : atom1298 = SparsePolynomial.decodeCubic 21 atom1298Coded := by decide +kernel
theorem atom1298Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5786258284800 : Int) atom1298Coded) := by
  have h := atom1298_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1298Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1299 : SparsePolynomial.Poly := [([7,8,19], 1)]
theorem eval_atom1299 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1299 = ((g 7) * (g 8) * (g 19)) := by
  norm_num [atom1299, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1299_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11171238059520 : Int) atom1299) := by
  rw [SparsePolynomial.eval_scale, eval_atom1299]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1299Coded : CoefficientMerge.Poly := [(3274, 1)]
theorem atom1299Coded_decode : atom1299 = SparsePolynomial.decodeCubic 21 atom1299Coded := by decide +kernel
theorem atom1299Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11171238059520 : Int) atom1299Coded) := by
  have h := atom1299_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1299Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1300 : SparsePolynomial.Poly := [([7,8,20], 1)]
theorem eval_atom1300 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1300 = ((g 7) * (g 8) * (g 20)) := by
  norm_num [atom1300, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1300_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17391151612800 : Int) atom1300) := by
  rw [SparsePolynomial.eval_scale, eval_atom1300]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1300Coded : CoefficientMerge.Poly := [(3275, 1)]
theorem atom1300Coded_decode : atom1300 = SparsePolynomial.decodeCubic 21 atom1300Coded := by decide +kernel
theorem atom1300Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17391151612800 : Int) atom1300Coded) := by
  have h := atom1300_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1300Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1301 : SparsePolynomial.Poly := [([7,9,9], 1)]
theorem eval_atom1301 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1301 = ((g 7) * (g 9) * (g 9)) := by
  norm_num [atom1301, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1301_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (896401296000 : Int) atom1301) := by
  rw [SparsePolynomial.eval_scale, eval_atom1301]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1301Coded : CoefficientMerge.Poly := [(3285, 1)]
theorem atom1301Coded_decode : atom1301 = SparsePolynomial.decodeCubic 21 atom1301Coded := by decide +kernel
theorem atom1301Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (896401296000 : Int) atom1301Coded) := by
  have h := atom1301_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1301Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1302 : SparsePolynomial.Poly := [([7,9,12], 1)]
theorem eval_atom1302 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1302 = ((g 7) * (g 9) * (g 12)) := by
  norm_num [atom1302, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1302_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (686193984000 : Int) atom1302) := by
  rw [SparsePolynomial.eval_scale, eval_atom1302]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1302Coded : CoefficientMerge.Poly := [(3288, 1)]
theorem atom1302Coded_decode : atom1302 = SparsePolynomial.decodeCubic 21 atom1302Coded := by decide +kernel
theorem atom1302Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (686193984000 : Int) atom1302Coded) := by
  have h := atom1302_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1302Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1303 : SparsePolynomial.Poly := [([7,9,13], 1)]
theorem eval_atom1303 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1303 = ((g 7) * (g 9) * (g 13)) := by
  norm_num [atom1303, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1303_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1372387968000 : Int) atom1303) := by
  rw [SparsePolynomial.eval_scale, eval_atom1303]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1303Coded : CoefficientMerge.Poly := [(3289, 1)]
theorem atom1303Coded_decode : atom1303 = SparsePolynomial.decodeCubic 21 atom1303Coded := by decide +kernel
theorem atom1303Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1372387968000 : Int) atom1303Coded) := by
  have h := atom1303_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1303Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1304 : SparsePolynomial.Poly := [([7,9,14], 1)]
theorem eval_atom1304 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1304 = ((g 7) * (g 9) * (g 14)) := by
  norm_num [atom1304, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1304_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2058581952000 : Int) atom1304) := by
  rw [SparsePolynomial.eval_scale, eval_atom1304]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1304Coded : CoefficientMerge.Poly := [(3290, 1)]
theorem atom1304Coded_decode : atom1304 = SparsePolynomial.decodeCubic 21 atom1304Coded := by decide +kernel
theorem atom1304Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2058581952000 : Int) atom1304Coded) := by
  have h := atom1304_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1304Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1305 : SparsePolynomial.Poly := [([7,9,15], 1)]
theorem eval_atom1305 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1305 = ((g 7) * (g 9) * (g 15)) := by
  norm_num [atom1305, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1305_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8185219145856 : Int) atom1305) := by
  rw [SparsePolynomial.eval_scale, eval_atom1305]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1305Coded : CoefficientMerge.Poly := [(3291, 1)]
theorem atom1305Coded_decode : atom1305 = SparsePolynomial.decodeCubic 21 atom1305Coded := by decide +kernel
theorem atom1305Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8185219145856 : Int) atom1305Coded) := by
  have h := atom1305_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1305Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1306 : SparsePolynomial.Poly := [([7,9,16], 1)]
theorem eval_atom1306 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1306 = ((g 7) * (g 9) * (g 16)) := by
  norm_num [atom1306, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1306_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3335794446240 : Int) atom1306) := by
  rw [SparsePolynomial.eval_scale, eval_atom1306]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1306Coded : CoefficientMerge.Poly := [(3292, 1)]
theorem atom1306Coded_decode : atom1306 = SparsePolynomial.decodeCubic 21 atom1306Coded := by decide +kernel
theorem atom1306Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3335794446240 : Int) atom1306Coded) := by
  have h := atom1306_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1306Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1307 : SparsePolynomial.Poly := [([7,9,17], 1)]
theorem eval_atom1307 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1307 = ((g 7) * (g 9) * (g 17)) := by
  norm_num [atom1307, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1307_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9115747148160 : Int) atom1307) := by
  rw [SparsePolynomial.eval_scale, eval_atom1307]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1307Coded : CoefficientMerge.Poly := [(3293, 1)]
theorem atom1307Coded_decode : atom1307 = SparsePolynomial.decodeCubic 21 atom1307Coded := by decide +kernel
theorem atom1307Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9115747148160 : Int) atom1307Coded) := by
  have h := atom1307_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1307Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1308 : SparsePolynomial.Poly := [([7,9,18], 1)]
theorem eval_atom1308 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1308 = ((g 7) * (g 9) * (g 18)) := by
  norm_num [atom1308, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1308_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13951505319840 : Int) atom1308) := by
  rw [SparsePolynomial.eval_scale, eval_atom1308]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1308Coded : CoefficientMerge.Poly := [(3294, 1)]
theorem atom1308Coded_decode : atom1308 = SparsePolynomial.decodeCubic 21 atom1308Coded := by decide +kernel
theorem atom1308Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13951505319840 : Int) atom1308Coded) := by
  have h := atom1308_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1308Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1309 : SparsePolynomial.Poly := [([7,9,19], 1)]
theorem eval_atom1309 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1309 = ((g 7) * (g 9) * (g 19)) := by
  norm_num [atom1309, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1309_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22686649344864 : Int) atom1309) := by
  rw [SparsePolynomial.eval_scale, eval_atom1309]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1309Coded : CoefficientMerge.Poly := [(3295, 1)]
theorem atom1309Coded_decode : atom1309 = SparsePolynomial.decodeCubic 21 atom1309Coded := by decide +kernel
theorem atom1309Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22686649344864 : Int) atom1309Coded) := by
  have h := atom1309_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1309Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1310 : SparsePolynomial.Poly := [([7,9,20], 1)]
theorem eval_atom1310 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1310 = ((g 7) * (g 9) * (g 20)) := by
  norm_num [atom1310, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1310_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32365160755200 : Int) atom1310) := by
  rw [SparsePolynomial.eval_scale, eval_atom1310]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1310Coded : CoefficientMerge.Poly := [(3296, 1)]
theorem atom1310Coded_decode : atom1310 = SparsePolynomial.decodeCubic 21 atom1310Coded := by decide +kernel
theorem atom1310Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32365160755200 : Int) atom1310Coded) := by
  have h := atom1310_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1310Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1311 : SparsePolynomial.Poly := [([7,10,10], 1)]
theorem eval_atom1311 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1311 = ((g 7) * (g 10) * (g 10)) := by
  norm_num [atom1311, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1311_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2262023971200 : Int) atom1311) := by
  rw [SparsePolynomial.eval_scale, eval_atom1311]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1311Coded : CoefficientMerge.Poly := [(3307, 1)]
theorem atom1311Coded_decode : atom1311 = SparsePolynomial.decodeCubic 21 atom1311Coded := by decide +kernel
theorem atom1311Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2262023971200 : Int) atom1311Coded) := by
  have h := atom1311_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1311Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1312 : SparsePolynomial.Poly := [([7,10,11], 1)]
theorem eval_atom1312 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1312 = ((g 7) * (g 10) * (g 11)) := by
  norm_num [atom1312, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1312_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3851384544000 : Int) atom1312) := by
  rw [SparsePolynomial.eval_scale, eval_atom1312]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1312Coded : CoefficientMerge.Poly := [(3308, 1)]
theorem atom1312Coded_decode : atom1312 = SparsePolynomial.decodeCubic 21 atom1312Coded := by decide +kernel
theorem atom1312Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3851384544000 : Int) atom1312Coded) := by
  have h := atom1312_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1312Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1313 : SparsePolynomial.Poly := [([7,10,12], 1)]
theorem eval_atom1313 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1313 = ((g 7) * (g 10) * (g 12)) := by
  norm_num [atom1313, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1313_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4201246828800 : Int) atom1313) := by
  rw [SparsePolynomial.eval_scale, eval_atom1313]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1313Coded : CoefficientMerge.Poly := [(3309, 1)]
theorem atom1313Coded_decode : atom1313 = SparsePolynomial.decodeCubic 21 atom1313Coded := by decide +kernel
theorem atom1313Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4201246828800 : Int) atom1313Coded) := by
  have h := atom1313_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1313Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1314 : SparsePolynomial.Poly := [([7,10,13], 1)]
theorem eval_atom1314 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1314 = ((g 7) * (g 10) * (g 13)) := by
  norm_num [atom1314, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1314_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4978289030400 : Int) atom1314) := by
  rw [SparsePolynomial.eval_scale, eval_atom1314]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1314Coded : CoefficientMerge.Poly := [(3310, 1)]
theorem atom1314Coded_decode : atom1314 = SparsePolynomial.decodeCubic 21 atom1314Coded := by decide +kernel
theorem atom1314Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4978289030400 : Int) atom1314Coded) := by
  have h := atom1314_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1314Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1315 : SparsePolynomial.Poly := [([7,10,14], 1)]
theorem eval_atom1315 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1315 = ((g 7) * (g 10) * (g 14)) := by
  norm_num [atom1315, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1315_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5755331232000 : Int) atom1315) := by
  rw [SparsePolynomial.eval_scale, eval_atom1315]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1315Coded : CoefficientMerge.Poly := [(3311, 1)]
theorem atom1315Coded_decode : atom1315 = SparsePolynomial.decodeCubic 21 atom1315Coded := by decide +kernel
theorem atom1315Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5755331232000 : Int) atom1315Coded) := by
  have h := atom1315_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1315Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1316 : SparsePolynomial.Poly := [([7,10,15], 1)]
theorem eval_atom1316 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1316 = ((g 7) * (g 10) * (g 15)) := by
  norm_num [atom1316, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1316_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13173656115456 : Int) atom1316) := by
  rw [SparsePolynomial.eval_scale, eval_atom1316]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1316Coded : CoefficientMerge.Poly := [(3312, 1)]
theorem atom1316Coded_decode : atom1316 = SparsePolynomial.decodeCubic 21 atom1316Coded := by decide +kernel
theorem atom1316Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13173656115456 : Int) atom1316Coded) := by
  have h := atom1316_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1316Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1317 : SparsePolynomial.Poly := [([7,10,16], 1)]
theorem eval_atom1317 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1317 = ((g 7) * (g 10) * (g 16)) := by
  norm_num [atom1317, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1317_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9544641913440 : Int) atom1317) := by
  rw [SparsePolynomial.eval_scale, eval_atom1317]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1317Coded : CoefficientMerge.Poly := [(3313, 1)]
theorem atom1317Coded_decode : atom1317 = SparsePolynomial.decodeCubic 21 atom1317Coded := by decide +kernel
theorem atom1317Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9544641913440 : Int) atom1317Coded) := by
  have h := atom1317_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1317Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1318 : SparsePolynomial.Poly := [([7,10,17], 1)]
theorem eval_atom1318 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1318 = ((g 7) * (g 10) * (g 17)) := by
  norm_num [atom1318, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1318_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18856319074560 : Int) atom1318) := by
  rw [SparsePolynomial.eval_scale, eval_atom1318]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1318Coded : CoefficientMerge.Poly := [(3314, 1)]
theorem atom1318Coded_decode : atom1318 = SparsePolynomial.decodeCubic 21 atom1318Coded := by decide +kernel
theorem atom1318Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18856319074560 : Int) atom1318Coded) := by
  have h := atom1318_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1318Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1319 : SparsePolynomial.Poly := [([7,10,18], 1)]
theorem eval_atom1319 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1319 = ((g 7) * (g 10) * (g 18)) := by
  norm_num [atom1319, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1319_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22426001022240 : Int) atom1319) := by
  rw [SparsePolynomial.eval_scale, eval_atom1319]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1319Coded : CoefficientMerge.Poly := [(3315, 1)]
theorem atom1319Coded_decode : atom1319 = SparsePolynomial.decodeCubic 21 atom1319Coded := by decide +kernel
theorem atom1319Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22426001022240 : Int) atom1319Coded) := by
  have h := atom1319_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1319Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1320 : SparsePolynomial.Poly := [([7,10,19], 1)]
theorem eval_atom1320 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1320 = ((g 7) * (g 10) * (g 19)) := by
  norm_num [atom1320, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1320_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32125924124064 : Int) atom1320) := by
  rw [SparsePolynomial.eval_scale, eval_atom1320]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1320Coded : CoefficientMerge.Poly := [(3316, 1)]
theorem atom1320Coded_decode : atom1320 = SparsePolynomial.decodeCubic 21 atom1320Coded := by decide +kernel
theorem atom1320Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32125924124064 : Int) atom1320Coded) := by
  have h := atom1320_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1320Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1321 : SparsePolynomial.Poly := [([7,10,20], 1)]
theorem eval_atom1321 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1321 = ((g 7) * (g 10) * (g 20)) := by
  norm_num [atom1321, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1321_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42511529440800 : Int) atom1321) := by
  rw [SparsePolynomial.eval_scale, eval_atom1321]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1321Coded : CoefficientMerge.Poly := [(3317, 1)]
theorem atom1321Coded_decode : atom1321 = SparsePolynomial.decodeCubic 21 atom1321Coded := by decide +kernel
theorem atom1321Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42511529440800 : Int) atom1321Coded) := by
  have h := atom1321_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1321Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1322 : SparsePolynomial.Poly := [([7,11,11], 1)]
theorem eval_atom1322 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1322 = ((g 7) * (g 11) * (g 11)) := by
  norm_num [atom1322, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1322_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4747785840000 : Int) atom1322) := by
  rw [SparsePolynomial.eval_scale, eval_atom1322]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1322Coded : CoefficientMerge.Poly := [(3329, 1)]
theorem atom1322Coded_decode : atom1322 = SparsePolynomial.decodeCubic 21 atom1322Coded := by decide +kernel
theorem atom1322Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4747785840000 : Int) atom1322Coded) := by
  have h := atom1322_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1322Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1323 : SparsePolynomial.Poly := [([7,11,12], 1)]
theorem eval_atom1323 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1323 = ((g 7) * (g 11) * (g 12)) := by
  norm_num [atom1323, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1323_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8318410732800 : Int) atom1323) := by
  rw [SparsePolynomial.eval_scale, eval_atom1323]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1323Coded : CoefficientMerge.Poly := [(3330, 1)]
theorem atom1323Coded_decode : atom1323 = SparsePolynomial.decodeCubic 21 atom1323Coded := by decide +kernel
theorem atom1323Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8318410732800 : Int) atom1323Coded) := by
  have h := atom1323_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1323Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1324 : SparsePolynomial.Poly := [([7,11,13], 1)]
theorem eval_atom1324 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1324 = ((g 7) * (g 11) * (g 13)) := by
  norm_num [atom1324, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1324_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9018135302400 : Int) atom1324) := by
  rw [SparsePolynomial.eval_scale, eval_atom1324]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1324Coded : CoefficientMerge.Poly := [(3331, 1)]
theorem atom1324Coded_decode : atom1324 = SparsePolynomial.decodeCubic 21 atom1324Coded := by decide +kernel
theorem atom1324Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9018135302400 : Int) atom1324Coded) := by
  have h := atom1324_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1324Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1325 : SparsePolynomial.Poly := [([7,11,14], 1)]
theorem eval_atom1325 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1325 = ((g 7) * (g 11) * (g 14)) := by
  norm_num [atom1325, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1325_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9717859872000 : Int) atom1325) := by
  rw [SparsePolynomial.eval_scale, eval_atom1325]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1325Coded : CoefficientMerge.Poly := [(3332, 1)]
theorem atom1325Coded_decode : atom1325 = SparsePolynomial.decodeCubic 21 atom1325Coded := by decide +kernel
theorem atom1325Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9717859872000 : Int) atom1325Coded) := by
  have h := atom1325_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1325Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1326 : SparsePolynomial.Poly := [([7,11,15], 1)]
theorem eval_atom1326 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1326 = ((g 7) * (g 11) * (g 15)) := by
  norm_num [atom1326, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1326_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17823714742656 : Int) atom1326) := by
  rw [SparsePolynomial.eval_scale, eval_atom1326]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1326Coded : CoefficientMerge.Poly := [(3333, 1)]
theorem atom1326Coded_decode : atom1326 = SparsePolynomial.decodeCubic 21 atom1326Coded := by decide +kernel
theorem atom1326Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17823714742656 : Int) atom1326Coded) := by
  have h := atom1326_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1326Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1327 : SparsePolynomial.Poly := [([7,11,16], 1)]
theorem eval_atom1327 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1327 = ((g 7) * (g 11) * (g 16)) := by
  norm_num [atom1327, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1327_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15047395107840 : Int) atom1327) := by
  rw [SparsePolynomial.eval_scale, eval_atom1327]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1327Coded : CoefficientMerge.Poly := [(3334, 1)]
theorem atom1327Coded_decode : atom1327 = SparsePolynomial.decodeCubic 21 atom1327Coded := by decide +kernel
theorem atom1327Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15047395107840 : Int) atom1327Coded) := by
  have h := atom1327_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1327Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1328 : SparsePolynomial.Poly := [([7,11,17], 1)]
theorem eval_atom1328 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1328 = ((g 7) * (g 11) * (g 17)) := by
  norm_num [atom1328, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1328_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27687575007360 : Int) atom1328) := by
  rw [SparsePolynomial.eval_scale, eval_atom1328]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1328Coded : CoefficientMerge.Poly := [(3335, 1)]
theorem atom1328Coded_decode : atom1328 = SparsePolynomial.decodeCubic 21 atom1328Coded := by decide +kernel
theorem atom1328Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27687575007360 : Int) atom1328Coded) := by
  have h := atom1328_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1328Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1329 : SparsePolynomial.Poly := [([7,11,18], 1)]
theorem eval_atom1329 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1329 = ((g 7) * (g 11) * (g 18)) := by
  norm_num [atom1329, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1329_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29300658949440 : Int) atom1329) := by
  rw [SparsePolynomial.eval_scale, eval_atom1329]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1329Coded : CoefficientMerge.Poly := [(3336, 1)]
theorem atom1329Coded_decode : atom1329 = SparsePolynomial.decodeCubic 21 atom1329Coded := by decide +kernel
theorem atom1329Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29300658949440 : Int) atom1329Coded) := by
  have h := atom1329_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1329Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1330 : SparsePolynomial.Poly := [([7,11,19], 1)]
theorem eval_atom1330 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1330 = ((g 7) * (g 11) * (g 19)) := by
  norm_num [atom1330, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1330_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39568321822464 : Int) atom1330) := by
  rw [SparsePolynomial.eval_scale, eval_atom1330]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1330Coded : CoefficientMerge.Poly := [(3337, 1)]
theorem atom1330Coded_decode : atom1330 = SparsePolynomial.decodeCubic 21 atom1330Coded := by decide +kernel
theorem atom1330Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39568321822464 : Int) atom1330Coded) := by
  have h := atom1330_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1330Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1331 : SparsePolynomial.Poly := [([7,11,20], 1)]
theorem eval_atom1331 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1331 = ((g 7) * (g 11) * (g 20)) := by
  norm_num [atom1331, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1331_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50335348946400 : Int) atom1331) := by
  rw [SparsePolynomial.eval_scale, eval_atom1331]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1331Coded : CoefficientMerge.Poly := [(3338, 1)]
theorem atom1331Coded_decode : atom1331 = SparsePolynomial.decodeCubic 21 atom1331Coded := by decide +kernel
theorem atom1331Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50335348946400 : Int) atom1331Coded) := by
  have h := atom1331_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1331Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1332 : SparsePolynomial.Poly := [([7,12,12], 1)]
theorem eval_atom1332 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1332 = ((g 7) * (g 12) * (g 12)) := by
  norm_num [atom1332, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1332_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7156230076800 : Int) atom1332) := by
  rw [SparsePolynomial.eval_scale, eval_atom1332]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1332Coded : CoefficientMerge.Poly := [(3351, 1)]
theorem atom1332Coded_decode : atom1332 = SparsePolynomial.decodeCubic 21 atom1332Coded := by decide +kernel
theorem atom1332Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7156230076800 : Int) atom1332Coded) := by
  have h := atom1332_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1332Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1333 : SparsePolynomial.Poly := [([7,12,13], 1)]
theorem eval_atom1333 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1333 = ((g 7) * (g 12) * (g 13)) := by
  norm_num [atom1333, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1333_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14339521324800 : Int) atom1333) := by
  rw [SparsePolynomial.eval_scale, eval_atom1333]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1333Coded : CoefficientMerge.Poly := [(3352, 1)]
theorem atom1333Coded_decode : atom1333 = SparsePolynomial.decodeCubic 21 atom1333Coded := by decide +kernel
theorem atom1333Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14339521324800 : Int) atom1333Coded) := by
  have h := atom1333_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1333Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1334 : SparsePolynomial.Poly := [([7,12,14], 1)]
theorem eval_atom1334 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1334 = ((g 7) * (g 12) * (g 14)) := by
  norm_num [atom1334, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1334_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14793762412800 : Int) atom1334) := by
  rw [SparsePolynomial.eval_scale, eval_atom1334]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1334Coded : CoefficientMerge.Poly := [(3353, 1)]
theorem atom1334Coded_decode : atom1334 = SparsePolynomial.decodeCubic 21 atom1334Coded := by decide +kernel
theorem atom1334Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14793762412800 : Int) atom1334Coded) := by
  have h := atom1334_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1334Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1335 : SparsePolynomial.Poly := [([7,12,15], 1)]
theorem eval_atom1335 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1335 = ((g 7) * (g 12) * (g 15)) := by
  norm_num [atom1335, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1335_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19441485123456 : Int) atom1335) := by
  rw [SparsePolynomial.eval_scale, eval_atom1335]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1335Coded : CoefficientMerge.Poly := [(3354, 1)]
theorem atom1335Coded_decode : atom1335 = SparsePolynomial.decodeCubic 21 atom1335Coded := by decide +kernel
theorem atom1335Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19441485123456 : Int) atom1335Coded) := by
  have h := atom1335_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1335Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1336 : SparsePolynomial.Poly := [([7,12,16], 1)]
theorem eval_atom1336 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1336 = ((g 7) * (g 12) * (g 16)) := by
  norm_num [atom1336, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1336_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19397114109440 : Int) atom1336) := by
  rw [SparsePolynomial.eval_scale, eval_atom1336]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1336Coded : CoefficientMerge.Poly := [(3355, 1)]
theorem atom1336Coded_decode : atom1336 = SparsePolynomial.decodeCubic 21 atom1336Coded := by decide +kernel
theorem atom1336Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19397114109440 : Int) atom1336Coded) := by
  have h := atom1336_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1336Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1337 : SparsePolynomial.Poly := [([7,12,17], 1)]
theorem eval_atom1337 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1337 = ((g 7) * (g 12) * (g 17)) := by
  norm_num [atom1337, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1337_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31352906629760 : Int) atom1337) := by
  rw [SparsePolynomial.eval_scale, eval_atom1337]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1337Coded : CoefficientMerge.Poly := [(3356, 1)]
theorem atom1337Coded_decode : atom1337 = SparsePolynomial.decodeCubic 21 atom1337Coded := by decide +kernel
theorem atom1337Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31352906629760 : Int) atom1337Coded) := by
  have h := atom1337_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1337Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1338 : SparsePolynomial.Poly := [([7,12,18], 1)]
theorem eval_atom1338 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1338 = ((g 7) * (g 12) * (g 18)) := by
  norm_num [atom1338, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1338_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34150544280640 : Int) atom1338) := by
  rw [SparsePolynomial.eval_scale, eval_atom1338]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1338Coded : CoefficientMerge.Poly := [(3357, 1)]
theorem atom1338Coded_decode : atom1338 = SparsePolynomial.decodeCubic 21 atom1338Coded := by decide +kernel
theorem atom1338Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34150544280640 : Int) atom1338Coded) := by
  have h := atom1338_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1338Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1339 : SparsePolynomial.Poly := [([7,12,19], 1)]
theorem eval_atom1339 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1339 = ((g 7) * (g 12) * (g 19)) := by
  norm_num [atom1339, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1339_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43898083947264 : Int) atom1339) := by
  rw [SparsePolynomial.eval_scale, eval_atom1339]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1339Coded : CoefficientMerge.Poly := [(3358, 1)]
theorem atom1339Coded_decode : atom1339 = SparsePolynomial.decodeCubic 21 atom1339Coded := by decide +kernel
theorem atom1339Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43898083947264 : Int) atom1339Coded) := by
  have h := atom1339_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1339Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1340 : SparsePolynomial.Poly := [([7,12,20], 1)]
theorem eval_atom1340 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1340 = ((g 7) * (g 12) * (g 20)) := by
  norm_num [atom1340, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1340_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54883075413600 : Int) atom1340) := by
  rw [SparsePolynomial.eval_scale, eval_atom1340]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1340Coded : CoefficientMerge.Poly := [(3359, 1)]
theorem atom1340Coded_decode : atom1340 = SparsePolynomial.decodeCubic 21 atom1340Coded := by decide +kernel
theorem atom1340Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (54883075413600 : Int) atom1340Coded) := by
  have h := atom1340_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1340Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1341 : SparsePolynomial.Poly := [([7,13,13], 1)]
theorem eval_atom1341 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1341 = ((g 7) * (g 13) * (g 13)) := by
  norm_num [atom1341, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1341_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10477390550400 : Int) atom1341) := by
  rw [SparsePolynomial.eval_scale, eval_atom1341]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1341Coded : CoefficientMerge.Poly := [(3373, 1)]
theorem atom1341Coded_decode : atom1341 = SparsePolynomial.decodeCubic 21 atom1341Coded := by decide +kernel
theorem atom1341Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10477390550400 : Int) atom1341Coded) := by
  have h := atom1341_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1341Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1342 : SparsePolynomial.Poly := [([7,13,14], 1)]
theorem eval_atom1342 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1342 = ((g 7) * (g 13) * (g 14)) := by
  norm_num [atom1342, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1342_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19824839136000 : Int) atom1342) := by
  rw [SparsePolynomial.eval_scale, eval_atom1342]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1342Coded : CoefficientMerge.Poly := [(3374, 1)]
theorem atom1342Coded_decode : atom1342 = SparsePolynomial.decodeCubic 21 atom1342Coded := by decide +kernel
theorem atom1342Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19824839136000 : Int) atom1342Coded) := by
  have h := atom1342_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1342Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1343 : SparsePolynomial.Poly := [([7,13,15], 1)]
theorem eval_atom1343 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1343 = ((g 7) * (g 13) * (g 15)) := by
  norm_num [atom1343, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1343_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24472903179456 : Int) atom1343) := by
  rw [SparsePolynomial.eval_scale, eval_atom1343]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1343Coded : CoefficientMerge.Poly := [(3375, 1)]
theorem atom1343Coded_decode : atom1343 = SparsePolynomial.decodeCubic 21 atom1343Coded := by decide +kernel
theorem atom1343Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24472903179456 : Int) atom1343Coded) := by
  have h := atom1343_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1343Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1344 : SparsePolynomial.Poly := [([7,13,16], 1)]
theorem eval_atom1344 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1344 = ((g 7) * (g 13) * (g 16)) := by
  norm_num [atom1344, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1344_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24292870914240 : Int) atom1344) := by
  rw [SparsePolynomial.eval_scale, eval_atom1344]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1344Coded : CoefficientMerge.Poly := [(3376, 1)]
theorem atom1344Coded_decode : atom1344 = SparsePolynomial.decodeCubic 21 atom1344Coded := by decide +kernel
theorem atom1344Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24292870914240 : Int) atom1344Coded) := by
  have h := atom1344_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1344Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1345 : SparsePolynomial.Poly := [([7,13,17], 1)]
theorem eval_atom1345 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1345 = ((g 7) * (g 13) * (g 17)) := by
  norm_num [atom1345, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1345_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39375935372160 : Int) atom1345) := by
  rw [SparsePolynomial.eval_scale, eval_atom1345]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1345Coded : CoefficientMerge.Poly := [(3377, 1)]
theorem atom1345Coded_decode : atom1345 = SparsePolynomial.decodeCubic 21 atom1345Coded := by decide +kernel
theorem atom1345Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39375935372160 : Int) atom1345Coded) := by
  have h := atom1345_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1345Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1346 : SparsePolynomial.Poly := [([7,13,18], 1)]
theorem eval_atom1346 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1346 = ((g 7) * (g 13) * (g 18)) := by
  norm_num [atom1346, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1346_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43793896443840 : Int) atom1346) := by
  rw [SparsePolynomial.eval_scale, eval_atom1346]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1346Coded : CoefficientMerge.Poly := [(3378, 1)]
theorem atom1346Coded_decode : atom1346 = SparsePolynomial.decodeCubic 21 atom1346Coded := by decide +kernel
theorem atom1346Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43793896443840 : Int) atom1346Coded) := by
  have h := atom1346_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1346Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1347 : SparsePolynomial.Poly := [([7,13,19], 1)]
theorem eval_atom1347 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1347 = ((g 7) * (g 13) * (g 19)) := by
  norm_num [atom1347, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1347_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47292853414464 : Int) atom1347) := by
  rw [SparsePolynomial.eval_scale, eval_atom1347]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1347Coded : CoefficientMerge.Poly := [(3379, 1)]
theorem atom1347Coded_decode : atom1347 = SparsePolynomial.decodeCubic 21 atom1347Coded := by decide +kernel
theorem atom1347Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47292853414464 : Int) atom1347Coded) := by
  have h := atom1347_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1347Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1348 : SparsePolynomial.Poly := [([7,13,20], 1)]
theorem eval_atom1348 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1348 = ((g 7) * (g 13) * (g 20)) := by
  norm_num [atom1348, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1348_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64416097821600 : Int) atom1348) := by
  rw [SparsePolynomial.eval_scale, eval_atom1348]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1348Coded : CoefficientMerge.Poly := [(3380, 1)]
theorem atom1348Coded_decode : atom1348 = SparsePolynomial.decodeCubic 21 atom1348Coded := by decide +kernel
theorem atom1348Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (64416097821600 : Int) atom1348Coded) := by
  have h := atom1348_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1348Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1349 : SparsePolynomial.Poly := [([7,14,14], 1)]
theorem eval_atom1349 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1349 = ((g 7) * (g 14) * (g 14)) := by
  norm_num [atom1349, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1349_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14909899939200 : Int) atom1349) := by
  rw [SparsePolynomial.eval_scale, eval_atom1349]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1349Coded : CoefficientMerge.Poly := [(3395, 1)]
theorem atom1349Coded_decode : atom1349 = SparsePolynomial.decodeCubic 21 atom1349Coded := by decide +kernel
theorem atom1349Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14909899939200 : Int) atom1349Coded) := by
  have h := atom1349_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1349Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1350 : SparsePolynomial.Poly := [([7,14,15], 1)]
theorem eval_atom1350 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1350 = ((g 7) * (g 14) * (g 15)) := by
  norm_num [atom1350, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1350_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29392479133056 : Int) atom1350) := by
  rw [SparsePolynomial.eval_scale, eval_atom1350]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1350Coded : CoefficientMerge.Poly := [(3396, 1)]
theorem atom1350Coded_decode : atom1350 = SparsePolynomial.decodeCubic 21 atom1350Coded := by decide +kernel
theorem atom1350Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29392479133056 : Int) atom1350Coded) := by
  have h := atom1350_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1350Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1351 : SparsePolynomial.Poly := [([7,14,16], 1)]
theorem eval_atom1351 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1351 = ((g 7) * (g 14) * (g 16)) := by
  norm_num [atom1351, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1351_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29069478282240 : Int) atom1351) := by
  rw [SparsePolynomial.eval_scale, eval_atom1351]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1351Coded : CoefficientMerge.Poly := [(3397, 1)]
theorem atom1351Coded_decode : atom1351 = SparsePolynomial.decodeCubic 21 atom1351Coded := by decide +kernel
theorem atom1351Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29069478282240 : Int) atom1351Coded) := by
  have h := atom1351_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1351Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1352 : SparsePolynomial.Poly := [([7,14,17], 1)]
theorem eval_atom1352 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1352 = ((g 7) * (g 14) * (g 17)) := by
  norm_num [atom1352, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1352_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49592493970560 : Int) atom1352) := by
  rw [SparsePolynomial.eval_scale, eval_atom1352]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1352Coded : CoefficientMerge.Poly := [(3398, 1)]
theorem atom1352Coded_decode : atom1352 = SparsePolynomial.decodeCubic 21 atom1352Coded := by decide +kernel
theorem atom1352Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49592493970560 : Int) atom1352Coded) := by
  have h := atom1352_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1352Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1353 : SparsePolynomial.Poly := [([7,14,18], 1)]
theorem eval_atom1353 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1353 = ((g 7) * (g 14) * (g 18)) := by
  norm_num [atom1353, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1353_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55850131448640 : Int) atom1353) := by
  rw [SparsePolynomial.eval_scale, eval_atom1353]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1353Coded : CoefficientMerge.Poly := [(3399, 1)]
theorem atom1353Coded_decode : atom1353 = SparsePolynomial.decodeCubic 21 atom1353Coded := by decide +kernel
theorem atom1353Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55850131448640 : Int) atom1353Coded) := by
  have h := atom1353_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1353Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1354 : SparsePolynomial.Poly := [([7,14,19], 1)]
theorem eval_atom1354 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1354 = ((g 7) * (g 14) * (g 19)) := by
  norm_num [atom1354, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1354_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55138349470464 : Int) atom1354) := by
  rw [SparsePolynomial.eval_scale, eval_atom1354]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1354Coded : CoefficientMerge.Poly := [(3400, 1)]
theorem atom1354Coded_decode : atom1354 = SparsePolynomial.decodeCubic 21 atom1354Coded := by decide +kernel
theorem atom1354Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55138349470464 : Int) atom1354Coded) := by
  have h := atom1354_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1354Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1355 : SparsePolynomial.Poly := [([7,14,20], 1)]
theorem eval_atom1355 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1355 = ((g 7) * (g 14) * (g 20)) := by
  norm_num [atom1355, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1355_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78532122866400 : Int) atom1355) := by
  rw [SparsePolynomial.eval_scale, eval_atom1355]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1355Coded : CoefficientMerge.Poly := [(3401, 1)]
theorem atom1355Coded_decode : atom1355 = SparsePolynomial.decodeCubic 21 atom1355Coded := by decide +kernel
theorem atom1355Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (78532122866400 : Int) atom1355Coded) := by
  have h := atom1355_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1355Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1356 : SparsePolynomial.Poly := [([7,15,15], 1)]
theorem eval_atom1356 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1356 = ((g 7) * (g 15) * (g 15)) := by
  norm_num [atom1356, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1356_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21896742731904 : Int) atom1356) := by
  rw [SparsePolynomial.eval_scale, eval_atom1356]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1356Coded : CoefficientMerge.Poly := [(3417, 1)]
theorem atom1356Coded_decode : atom1356 = SparsePolynomial.decodeCubic 21 atom1356Coded := by decide +kernel
theorem atom1356Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21896742731904 : Int) atom1356Coded) := by
  have h := atom1356_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1356Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1357 : SparsePolynomial.Poly := [([7,15,16], 1)]
theorem eval_atom1357 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1357 = ((g 7) * (g 15) * (g 16)) := by
  norm_num [atom1357, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1357_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42928095901824 : Int) atom1357) := by
  rw [SparsePolynomial.eval_scale, eval_atom1357]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1357Coded : CoefficientMerge.Poly := [(3418, 1)]
theorem atom1357Coded_decode : atom1357 = SparsePolynomial.decodeCubic 21 atom1357Coded := by decide +kernel
theorem atom1357Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42928095901824 : Int) atom1357Coded) := by
  have h := atom1357_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1357Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1358 : SparsePolynomial.Poly := [([7,15,17], 1)]
theorem eval_atom1358 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1358 = ((g 7) * (g 15) * (g 17)) := by
  norm_num [atom1358, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1358_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68414874110208 : Int) atom1358) := by
  rw [SparsePolynomial.eval_scale, eval_atom1358]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1358Coded : CoefficientMerge.Poly := [(3419, 1)]
theorem atom1358Coded_decode : atom1358 = SparsePolynomial.decodeCubic 21 atom1358Coded := by decide +kernel
theorem atom1358Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (68414874110208 : Int) atom1358Coded) := by
  have h := atom1358_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1358Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1359 : SparsePolynomial.Poly := [([7,15,18], 1)]
theorem eval_atom1359 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1359 = ((g 7) * (g 15) * (g 18)) := by
  norm_num [atom1359, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1359_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (71594005599360 : Int) atom1359) := by
  rw [SparsePolynomial.eval_scale, eval_atom1359]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1359Coded : CoefficientMerge.Poly := [(3420, 1)]
theorem atom1359Coded_decode : atom1359 = SparsePolynomial.decodeCubic 21 atom1359Coded := by decide +kernel
theorem atom1359Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (71594005599360 : Int) atom1359Coded) := by
  have h := atom1359_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1359Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1360 : SparsePolynomial.Poly := [([7,15,19], 1)]
theorem eval_atom1360 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1360 = ((g 7) * (g 15) * (g 19)) := by
  norm_num [atom1360, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1360_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53238031188480 : Int) atom1360) := by
  rw [SparsePolynomial.eval_scale, eval_atom1360]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1360Coded : CoefficientMerge.Poly := [(3421, 1)]
theorem atom1360Coded_decode : atom1360 = SparsePolynomial.decodeCubic 21 atom1360Coded := by decide +kernel
theorem atom1360Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53238031188480 : Int) atom1360Coded) := by
  have h := atom1360_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1360Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1361 : SparsePolynomial.Poly := [([7,15,20], 1)]
theorem eval_atom1361 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1361 = ((g 7) * (g 15) * (g 20)) := by
  norm_num [atom1361, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1361_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (80901900693504 : Int) atom1361) := by
  rw [SparsePolynomial.eval_scale, eval_atom1361]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1361Coded : CoefficientMerge.Poly := [(3422, 1)]
theorem atom1361Coded_decode : atom1361 = SparsePolynomial.decodeCubic 21 atom1361Coded := by decide +kernel
theorem atom1361Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (80901900693504 : Int) atom1361Coded) := by
  have h := atom1361_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1361Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1362 : SparsePolynomial.Poly := [([7,16,16], 1)]
theorem eval_atom1362 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1362 = ((g 7) * (g 16) * (g 16)) := by
  norm_num [atom1362, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1362_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17225211406464 : Int) atom1362) := by
  rw [SparsePolynomial.eval_scale, eval_atom1362]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1362Coded : CoefficientMerge.Poly := [(3439, 1)]
theorem atom1362Coded_decode : atom1362 = SparsePolynomial.decodeCubic 21 atom1362Coded := by decide +kernel
theorem atom1362Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17225211406464 : Int) atom1362Coded) := by
  have h := atom1362_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1362Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1363 : SparsePolynomial.Poly := [([7,16,17], 1)]
theorem eval_atom1363 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1363 = ((g 7) * (g 16) * (g 17)) := by
  norm_num [atom1363, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1363_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56900847134592 : Int) atom1363) := by
  rw [SparsePolynomial.eval_scale, eval_atom1363]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1363Coded : CoefficientMerge.Poly := [(3440, 1)]
theorem atom1363Coded_decode : atom1363 = SparsePolynomial.decodeCubic 21 atom1363Coded := by decide +kernel
theorem atom1363Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (56900847134592 : Int) atom1363Coded) := by
  have h := atom1363_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1363Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1364 : SparsePolynomial.Poly := [([7,16,18], 1)]
theorem eval_atom1364 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1364 = ((g 7) * (g 16) * (g 18)) := by
  norm_num [atom1364, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1364_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63199359221184 : Int) atom1364) := by
  rw [SparsePolynomial.eval_scale, eval_atom1364]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1364Coded : CoefficientMerge.Poly := [(3441, 1)]
theorem atom1364Coded_decode : atom1364 = SparsePolynomial.decodeCubic 21 atom1364Coded := by decide +kernel
theorem atom1364Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (63199359221184 : Int) atom1364Coded) := by
  have h := atom1364_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1364Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1365 : SparsePolynomial.Poly := [([7,16,19], 1)]
theorem eval_atom1365 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1365 = ((g 7) * (g 16) * (g 19)) := by
  norm_num [atom1365, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1365_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47004130814208 : Int) atom1365) := by
  rw [SparsePolynomial.eval_scale, eval_atom1365]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1365Coded : CoefficientMerge.Poly := [(3442, 1)]
theorem atom1365Coded_decode : atom1365 = SparsePolynomial.decodeCubic 21 atom1365Coded := by decide +kernel
theorem atom1365Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47004130814208 : Int) atom1365Coded) := by
  have h := atom1365_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1365Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1366 : SparsePolynomial.Poly := [([7,16,20], 1)]
theorem eval_atom1366 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1366 = ((g 7) * (g 16) * (g 20)) := by
  norm_num [atom1366, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1366_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59161605357600 : Int) atom1366) := by
  rw [SparsePolynomial.eval_scale, eval_atom1366]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1366Coded : CoefficientMerge.Poly := [(3443, 1)]
theorem atom1366Coded_decode : atom1366 = SparsePolynomial.decodeCubic 21 atom1366Coded := by decide +kernel
theorem atom1366Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (59161605357600 : Int) atom1366Coded) := by
  have h := atom1366_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1366Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1367 : SparsePolynomial.Poly := [([7,17,17], 1)]
theorem eval_atom1367 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1367 = ((g 7) * (g 17) * (g 17)) := by
  norm_num [atom1367, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1367_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41545743986304 : Int) atom1367) := by
  rw [SparsePolynomial.eval_scale, eval_atom1367]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1367Coded : CoefficientMerge.Poly := [(3461, 1)]
theorem atom1367Coded_decode : atom1367 = SparsePolynomial.decodeCubic 21 atom1367Coded := by decide +kernel
theorem atom1367Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41545743986304 : Int) atom1367Coded) := by
  have h := atom1367_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1367Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1368 : SparsePolynomial.Poly := [([7,17,18], 1)]
theorem eval_atom1368 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1368 = ((g 7) * (g 17) * (g 18)) := by
  norm_num [atom1368, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1368_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (70291863363456 : Int) atom1368) := by
  rw [SparsePolynomial.eval_scale, eval_atom1368]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1368Coded : CoefficientMerge.Poly := [(3462, 1)]
theorem atom1368Coded_decode : atom1368 = SparsePolynomial.decodeCubic 21 atom1368Coded := by decide +kernel
theorem atom1368Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (70291863363456 : Int) atom1368Coded) := by
  have h := atom1368_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1368Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1369 : SparsePolynomial.Poly := [([7,17,19], 1)]
theorem eval_atom1369 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1369 = ((g 7) * (g 17) * (g 19)) := by
  norm_num [atom1369, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1369_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48185112168960 : Int) atom1369) := by
  rw [SparsePolynomial.eval_scale, eval_atom1369]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1369Coded : CoefficientMerge.Poly := [(3463, 1)]
theorem atom1369Coded_decode : atom1369 = SparsePolynomial.decodeCubic 21 atom1369Coded := by decide +kernel
theorem atom1369Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48185112168960 : Int) atom1369Coded) := by
  have h := atom1369_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1369Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1370 : SparsePolynomial.Poly := [([7,17,20], 1)]
theorem eval_atom1370 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1370 = ((g 7) * (g 17) * (g 20)) := by
  norm_num [atom1370, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1370_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51533139292416 : Int) atom1370) := by
  rw [SparsePolynomial.eval_scale, eval_atom1370]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1370Coded : CoefficientMerge.Poly := [(3464, 1)]
theorem atom1370Coded_decode : atom1370 = SparsePolynomial.decodeCubic 21 atom1370Coded := by decide +kernel
theorem atom1370Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (51533139292416 : Int) atom1370Coded) := by
  have h := atom1370_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1370Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1371 : SparsePolynomial.Poly := [([7,18,18], 1)]
theorem eval_atom1371 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1371 = ((g 7) * (g 18) * (g 18)) := by
  norm_num [atom1371, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1371_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22921685971776 : Int) atom1371) := by
  rw [SparsePolynomial.eval_scale, eval_atom1371]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1371Coded : CoefficientMerge.Poly := [(3483, 1)]
theorem atom1371Coded_decode : atom1371 = SparsePolynomial.decodeCubic 21 atom1371Coded := by decide +kernel
theorem atom1371Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22921685971776 : Int) atom1371Coded) := by
  have h := atom1371_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1371Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1372 : SparsePolynomial.Poly := [([7,18,19], 1)]
theorem eval_atom1372 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1372 = ((g 7) * (g 18) * (g 19)) := by
  norm_num [atom1372, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1372_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27537164315136 : Int) atom1372) := by
  rw [SparsePolynomial.eval_scale, eval_atom1372]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1372Coded : CoefficientMerge.Poly := [(3484, 1)]
theorem atom1372Coded_decode : atom1372 = SparsePolynomial.decodeCubic 21 atom1372Coded := by decide +kernel
theorem atom1372Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27537164315136 : Int) atom1372Coded) := by
  have h := atom1372_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1372Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1373 : SparsePolynomial.Poly := [([7,18,20], 1)]
theorem eval_atom1373 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1373 = ((g 7) * (g 18) * (g 20)) := by
  norm_num [atom1373, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1373_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31480194875040 : Int) atom1373) := by
  rw [SparsePolynomial.eval_scale, eval_atom1373]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1373Coded : CoefficientMerge.Poly := [(3485, 1)]
theorem atom1373Coded_decode : atom1373 = SparsePolynomial.decodeCubic 21 atom1373Coded := by decide +kernel
theorem atom1373Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31480194875040 : Int) atom1373Coded) := by
  have h := atom1373_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1373Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1374 : SparsePolynomial.Poly := [([8,8,8], 1)]
theorem eval_atom1374 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1374 = ((g 8) * (g 8) * (g 8)) := by
  norm_num [atom1374, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1374_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1353863952000 : Int) atom1374) := by
  rw [SparsePolynomial.eval_scale, eval_atom1374]
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 8) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1374Coded : CoefficientMerge.Poly := [(3704, 1)]
theorem atom1374Coded_decode : atom1374 = SparsePolynomial.decodeCubic 21 atom1374Coded := by decide +kernel
theorem atom1374Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1353863952000 : Int) atom1374Coded) := by
  have h := atom1374_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1374Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1375 : SparsePolynomial.Poly := [([8,8,9], 1)]
theorem eval_atom1375 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1375 = ((g 8) * (g 8) * (g 9)) := by
  norm_num [atom1375, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1375_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1372387968000 : Int) atom1375) := by
  rw [SparsePolynomial.eval_scale, eval_atom1375]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1375Coded : CoefficientMerge.Poly := [(3705, 1)]
theorem atom1375Coded_decode : atom1375 = SparsePolynomial.decodeCubic 21 atom1375Coded := by decide +kernel
theorem atom1375Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1372387968000 : Int) atom1375Coded) := by
  have h := atom1375_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1375Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block018 : CoefficientMerge.Poly := [(3270, 6427474232112), (3272, 1510388496720), (3273, 5786258284800), (3274, 11171238059520), (3275, 17391151612800), (3285, 896401296000), (3288, 686193984000), (3289, 1372387968000), (3290, 2058581952000), (3291, 8185219145856), (3292, 3335794446240), (3293, 9115747148160), (3294, 13951505319840), (3295, 22686649344864), (3296, 32365160755200), (3307, 2262023971200), (3308, 3851384544000), (3309, 4201246828800), (3310, 4978289030400), (3311, 5755331232000), (3312, 13173656115456), (3313, 9544641913440), (3314, 18856319074560), (3315, 22426001022240), (3316, 32125924124064), (3317, 42511529440800), (3329, 4747785840000), (3330, 8318410732800), (3331, 9018135302400), (3332, 9717859872000), (3333, 17823714742656), (3334, 15047395107840), (3335, 27687575007360), (3336, 29300658949440), (3337, 39568321822464), (3338, 50335348946400), (3351, 7156230076800), (3352, 14339521324800), (3353, 14793762412800), (3354, 19441485123456), (3355, 19397114109440), (3356, 31352906629760), (3357, 34150544280640), (3358, 43898083947264), (3359, 54883075413600), (3373, 10477390550400), (3374, 19824839136000), (3375, 24472903179456), (3376, 24292870914240), (3377, 39375935372160), (3378, 43793896443840), (3379, 47292853414464), (3380, 64416097821600), (3395, 14909899939200), (3396, 29392479133056), (3397, 29069478282240), (3398, 49592493970560), (3399, 55850131448640), (3400, 55138349470464), (3401, 78532122866400), (3417, 21896742731904), (3418, 42928095901824), (3419, 68414874110208), (3420, 71594005599360), (3421, 53238031188480), (3422, 80901900693504), (3439, 17225211406464), (3440, 56900847134592), (3441, 63199359221184), (3442, 47004130814208), (3443, 59161605357600), (3461, 41545743986304), (3462, 70291863363456), (3463, 48185112168960), (3464, 51533139292416), (3483, 22921685971776), (3484, 27537164315136), (3485, 31480194875040), (3704, 1353863952000), (3705, 1372387968000)]
theorem block018_data : block018 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6427474232112 : Int) atom1296Coded) (CoefficientMerge.scale (1510388496720 : Int) atom1297Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1299Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1300Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (896401296000 : Int) atom1301Coded) (CoefficientMerge.scale (686193984000 : Int) atom1302Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1372387968000 : Int) atom1303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2058581952000 : Int) atom1304Coded) (CoefficientMerge.scale (8185219145856 : Int) atom1305Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3335794446240 : Int) atom1306Coded) (CoefficientMerge.scale (9115747148160 : Int) atom1307Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13951505319840 : Int) atom1308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22686649344864 : Int) atom1309Coded) (CoefficientMerge.scale (32365160755200 : Int) atom1310Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2262023971200 : Int) atom1311Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1312Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4201246828800 : Int) atom1313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4978289030400 : Int) atom1314Coded) (CoefficientMerge.scale (5755331232000 : Int) atom1315Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13173656115456 : Int) atom1316Coded) (CoefficientMerge.scale (9544641913440 : Int) atom1317Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18856319074560 : Int) atom1318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22426001022240 : Int) atom1319Coded) (CoefficientMerge.scale (32125924124064 : Int) atom1320Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42511529440800 : Int) atom1321Coded) (CoefficientMerge.scale (4747785840000 : Int) atom1322Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8318410732800 : Int) atom1323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9018135302400 : Int) atom1324Coded) (CoefficientMerge.scale (9717859872000 : Int) atom1325Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17823714742656 : Int) atom1326Coded) (CoefficientMerge.scale (15047395107840 : Int) atom1327Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27687575007360 : Int) atom1328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29300658949440 : Int) atom1329Coded) (CoefficientMerge.scale (39568321822464 : Int) atom1330Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50335348946400 : Int) atom1331Coded) (CoefficientMerge.scale (7156230076800 : Int) atom1332Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14339521324800 : Int) atom1333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14793762412800 : Int) atom1334Coded) (CoefficientMerge.scale (19441485123456 : Int) atom1335Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19397114109440 : Int) atom1336Coded) (CoefficientMerge.scale (31352906629760 : Int) atom1337Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34150544280640 : Int) atom1338Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43898083947264 : Int) atom1339Coded) (CoefficientMerge.scale (54883075413600 : Int) atom1340Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10477390550400 : Int) atom1341Coded) (CoefficientMerge.scale (19824839136000 : Int) atom1342Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24472903179456 : Int) atom1343Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24292870914240 : Int) atom1344Coded) (CoefficientMerge.scale (39375935372160 : Int) atom1345Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43793896443840 : Int) atom1346Coded) (CoefficientMerge.scale (47292853414464 : Int) atom1347Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64416097821600 : Int) atom1348Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14909899939200 : Int) atom1349Coded) (CoefficientMerge.scale (29392479133056 : Int) atom1350Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29069478282240 : Int) atom1351Coded) (CoefficientMerge.scale (49592493970560 : Int) atom1352Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55850131448640 : Int) atom1353Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55138349470464 : Int) atom1354Coded) (CoefficientMerge.scale (78532122866400 : Int) atom1355Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21896742731904 : Int) atom1356Coded) (CoefficientMerge.scale (42928095901824 : Int) atom1357Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68414874110208 : Int) atom1358Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71594005599360 : Int) atom1359Coded) (CoefficientMerge.scale (53238031188480 : Int) atom1360Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (80901900693504 : Int) atom1361Coded) (CoefficientMerge.scale (17225211406464 : Int) atom1362Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56900847134592 : Int) atom1363Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63199359221184 : Int) atom1364Coded) (CoefficientMerge.scale (47004130814208 : Int) atom1365Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (59161605357600 : Int) atom1366Coded) (CoefficientMerge.scale (41545743986304 : Int) atom1367Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70291863363456 : Int) atom1368Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48185112168960 : Int) atom1369Coded) (CoefficientMerge.scale (51533139292416 : Int) atom1370Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22921685971776 : Int) atom1371Coded) (CoefficientMerge.scale (27537164315136 : Int) atom1372Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31480194875040 : Int) atom1373Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1353863952000 : Int) atom1374Coded) (CoefficientMerge.scale (1372387968000 : Int) atom1375Coded)))))))) := by decide +kernel
theorem block018_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block018 := by
  rw [block018_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1296Coded_nonneg g hg hA hB) (atom1297Coded_nonneg g hg hA hB)) (add_nonneg (atom1298Coded_nonneg g hg hA hB) (add_nonneg (atom1299Coded_nonneg g hg hA hB) (atom1300Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1301Coded_nonneg g hg hA hB) (atom1302Coded_nonneg g hg hA hB)) (add_nonneg (atom1303Coded_nonneg g hg hA hB) (add_nonneg (atom1304Coded_nonneg g hg hA hB) (atom1305Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1306Coded_nonneg g hg hA hB) (atom1307Coded_nonneg g hg hA hB)) (add_nonneg (atom1308Coded_nonneg g hg hA hB) (add_nonneg (atom1309Coded_nonneg g hg hA hB) (atom1310Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1311Coded_nonneg g hg hA hB) (atom1312Coded_nonneg g hg hA hB)) (add_nonneg (atom1313Coded_nonneg g hg hA hB) (add_nonneg (atom1314Coded_nonneg g hg hA hB) (atom1315Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1316Coded_nonneg g hg hA hB) (atom1317Coded_nonneg g hg hA hB)) (add_nonneg (atom1318Coded_nonneg g hg hA hB) (add_nonneg (atom1319Coded_nonneg g hg hA hB) (atom1320Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1321Coded_nonneg g hg hA hB) (atom1322Coded_nonneg g hg hA hB)) (add_nonneg (atom1323Coded_nonneg g hg hA hB) (add_nonneg (atom1324Coded_nonneg g hg hA hB) (atom1325Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1326Coded_nonneg g hg hA hB) (atom1327Coded_nonneg g hg hA hB)) (add_nonneg (atom1328Coded_nonneg g hg hA hB) (add_nonneg (atom1329Coded_nonneg g hg hA hB) (atom1330Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1331Coded_nonneg g hg hA hB) (atom1332Coded_nonneg g hg hA hB)) (add_nonneg (atom1333Coded_nonneg g hg hA hB) (add_nonneg (atom1334Coded_nonneg g hg hA hB) (atom1335Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1336Coded_nonneg g hg hA hB) (atom1337Coded_nonneg g hg hA hB)) (add_nonneg (atom1338Coded_nonneg g hg hA hB) (add_nonneg (atom1339Coded_nonneg g hg hA hB) (atom1340Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1341Coded_nonneg g hg hA hB) (atom1342Coded_nonneg g hg hA hB)) (add_nonneg (atom1343Coded_nonneg g hg hA hB) (add_nonneg (atom1344Coded_nonneg g hg hA hB) (atom1345Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1346Coded_nonneg g hg hA hB) (atom1347Coded_nonneg g hg hA hB)) (add_nonneg (atom1348Coded_nonneg g hg hA hB) (add_nonneg (atom1349Coded_nonneg g hg hA hB) (atom1350Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1351Coded_nonneg g hg hA hB) (atom1352Coded_nonneg g hg hA hB)) (add_nonneg (atom1353Coded_nonneg g hg hA hB) (add_nonneg (atom1354Coded_nonneg g hg hA hB) (atom1355Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1356Coded_nonneg g hg hA hB) (atom1357Coded_nonneg g hg hA hB)) (add_nonneg (atom1358Coded_nonneg g hg hA hB) (add_nonneg (atom1359Coded_nonneg g hg hA hB) (atom1360Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1361Coded_nonneg g hg hA hB) (atom1362Coded_nonneg g hg hA hB)) (add_nonneg (atom1363Coded_nonneg g hg hA hB) (add_nonneg (atom1364Coded_nonneg g hg hA hB) (atom1365Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1366Coded_nonneg g hg hA hB) (atom1367Coded_nonneg g hg hA hB)) (add_nonneg (atom1368Coded_nonneg g hg hA hB) (add_nonneg (atom1369Coded_nonneg g hg hA hB) (atom1370Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1371Coded_nonneg g hg hA hB) (atom1372Coded_nonneg g hg hA hB)) (add_nonneg (atom1373Coded_nonneg g hg hA hB) (add_nonneg (atom1374Coded_nonneg g hg hA hB) (atom1375Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
