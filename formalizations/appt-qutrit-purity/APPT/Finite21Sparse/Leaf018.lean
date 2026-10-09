-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1296 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1296Coded : CoefficientMerge.Poly := [(nat_lit 3270, Int.ofNat (nat_lit 1))]
theorem atom1296Coded_decode : atom1296 = SparsePolynomial.decodeCubic 21 atom1296Coded := by decide +kernel
theorem atom1296Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6427474232112 : Int) atom1296Coded) := by
  have h := atom1296_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1296Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1297 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1297Coded : CoefficientMerge.Poly := [(nat_lit 3272, Int.ofNat (nat_lit 1))]
theorem atom1297Coded_decode : atom1297 = SparsePolynomial.decodeCubic 21 atom1297Coded := by decide +kernel
theorem atom1297Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1510388496720 : Int) atom1297Coded) := by
  have h := atom1297_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1297Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1298 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1298Coded : CoefficientMerge.Poly := [(nat_lit 3273, Int.ofNat (nat_lit 1))]
theorem atom1298Coded_decode : atom1298 = SparsePolynomial.decodeCubic 21 atom1298Coded := by decide +kernel
theorem atom1298Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5786258284800 : Int) atom1298Coded) := by
  have h := atom1298_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1298Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1299 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1299Coded : CoefficientMerge.Poly := [(nat_lit 3274, Int.ofNat (nat_lit 1))]
theorem atom1299Coded_decode : atom1299 = SparsePolynomial.decodeCubic 21 atom1299Coded := by decide +kernel
theorem atom1299Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11171238059520 : Int) atom1299Coded) := by
  have h := atom1299_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1299Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1300 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1300Coded : CoefficientMerge.Poly := [(nat_lit 3275, Int.ofNat (nat_lit 1))]
theorem atom1300Coded_decode : atom1300 = SparsePolynomial.decodeCubic 21 atom1300Coded := by decide +kernel
theorem atom1300Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17391151612800 : Int) atom1300Coded) := by
  have h := atom1300_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1300Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1301 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1301 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1301 = ((g 7) * (g 9) * (g 9)) := by
  norm_num [atom1301, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1301_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (896401296000 : Int) atom1301) := by
  rw [SparsePolynomial.eval_scale, eval_atom1301]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1301Coded : CoefficientMerge.Poly := [(nat_lit 3285, Int.ofNat (nat_lit 1))]
theorem atom1301Coded_decode : atom1301 = SparsePolynomial.decodeCubic 21 atom1301Coded := by decide +kernel
theorem atom1301Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (896401296000 : Int) atom1301Coded) := by
  have h := atom1301_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1301Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1302 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
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
def atom1302Coded : CoefficientMerge.Poly := [(nat_lit 3288, Int.ofNat (nat_lit 1))]
theorem atom1302Coded_decode : atom1302 = SparsePolynomial.decodeCubic 21 atom1302Coded := by decide +kernel
theorem atom1302Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (686193984000 : Int) atom1302Coded) := by
  have h := atom1302_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1302Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1303 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom1303Coded : CoefficientMerge.Poly := [(nat_lit 3289, Int.ofNat (nat_lit 1))]
theorem atom1303Coded_decode : atom1303 = SparsePolynomial.decodeCubic 21 atom1303Coded := by decide +kernel
theorem atom1303Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1372387968000 : Int) atom1303Coded) := by
  have h := atom1303_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1303Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1304 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1304Coded : CoefficientMerge.Poly := [(nat_lit 3290, Int.ofNat (nat_lit 1))]
theorem atom1304Coded_decode : atom1304 = SparsePolynomial.decodeCubic 21 atom1304Coded := by decide +kernel
theorem atom1304Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2058581952000 : Int) atom1304Coded) := by
  have h := atom1304_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1304Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1305 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1305Coded : CoefficientMerge.Poly := [(nat_lit 3291, Int.ofNat (nat_lit 1))]
theorem atom1305Coded_decode : atom1305 = SparsePolynomial.decodeCubic 21 atom1305Coded := by decide +kernel
theorem atom1305Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8185219145856 : Int) atom1305Coded) := by
  have h := atom1305_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1305Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1306 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1306Coded : CoefficientMerge.Poly := [(nat_lit 3292, Int.ofNat (nat_lit 1))]
theorem atom1306Coded_decode : atom1306 = SparsePolynomial.decodeCubic 21 atom1306Coded := by decide +kernel
theorem atom1306Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3335794446240 : Int) atom1306Coded) := by
  have h := atom1306_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1306Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1307 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1307Coded : CoefficientMerge.Poly := [(nat_lit 3293, Int.ofNat (nat_lit 1))]
theorem atom1307Coded_decode : atom1307 = SparsePolynomial.decodeCubic 21 atom1307Coded := by decide +kernel
theorem atom1307Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9115747148160 : Int) atom1307Coded) := by
  have h := atom1307_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1307Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1308 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1308Coded : CoefficientMerge.Poly := [(nat_lit 3294, Int.ofNat (nat_lit 1))]
theorem atom1308Coded_decode : atom1308 = SparsePolynomial.decodeCubic 21 atom1308Coded := by decide +kernel
theorem atom1308Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13951505319840 : Int) atom1308Coded) := by
  have h := atom1308_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1308Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1309 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1309Coded : CoefficientMerge.Poly := [(nat_lit 3295, Int.ofNat (nat_lit 1))]
theorem atom1309Coded_decode : atom1309 = SparsePolynomial.decodeCubic 21 atom1309Coded := by decide +kernel
theorem atom1309Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22686649344864 : Int) atom1309Coded) := by
  have h := atom1309_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1309Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1310 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1310Coded : CoefficientMerge.Poly := [(nat_lit 3296, Int.ofNat (nat_lit 1))]
theorem atom1310Coded_decode : atom1310 = SparsePolynomial.decodeCubic 21 atom1310Coded := by decide +kernel
theorem atom1310Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32365160755200 : Int) atom1310Coded) := by
  have h := atom1310_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1310Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1311 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1311 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1311 = ((g 7) * (g 10) * (g 10)) := by
  norm_num [atom1311, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1311_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2262023971200 : Int) atom1311) := by
  rw [SparsePolynomial.eval_scale, eval_atom1311]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1311Coded : CoefficientMerge.Poly := [(nat_lit 3307, Int.ofNat (nat_lit 1))]
theorem atom1311Coded_decode : atom1311 = SparsePolynomial.decodeCubic 21 atom1311Coded := by decide +kernel
theorem atom1311Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2262023971200 : Int) atom1311Coded) := by
  have h := atom1311_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1311Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1312 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
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
def atom1312Coded : CoefficientMerge.Poly := [(nat_lit 3308, Int.ofNat (nat_lit 1))]
theorem atom1312Coded_decode : atom1312 = SparsePolynomial.decodeCubic 21 atom1312Coded := by decide +kernel
theorem atom1312Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3851384544000 : Int) atom1312Coded) := by
  have h := atom1312_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1312Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1313 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
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
def atom1313Coded : CoefficientMerge.Poly := [(nat_lit 3309, Int.ofNat (nat_lit 1))]
theorem atom1313Coded_decode : atom1313 = SparsePolynomial.decodeCubic 21 atom1313Coded := by decide +kernel
theorem atom1313Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4201246828800 : Int) atom1313Coded) := by
  have h := atom1313_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1313Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1314 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom1314Coded : CoefficientMerge.Poly := [(nat_lit 3310, Int.ofNat (nat_lit 1))]
theorem atom1314Coded_decode : atom1314 = SparsePolynomial.decodeCubic 21 atom1314Coded := by decide +kernel
theorem atom1314Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4978289030400 : Int) atom1314Coded) := by
  have h := atom1314_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1314Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1315 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1315Coded : CoefficientMerge.Poly := [(nat_lit 3311, Int.ofNat (nat_lit 1))]
theorem atom1315Coded_decode : atom1315 = SparsePolynomial.decodeCubic 21 atom1315Coded := by decide +kernel
theorem atom1315Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5755331232000 : Int) atom1315Coded) := by
  have h := atom1315_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1315Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1316 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1316Coded : CoefficientMerge.Poly := [(nat_lit 3312, Int.ofNat (nat_lit 1))]
theorem atom1316Coded_decode : atom1316 = SparsePolynomial.decodeCubic 21 atom1316Coded := by decide +kernel
theorem atom1316Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13173656115456 : Int) atom1316Coded) := by
  have h := atom1316_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1316Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1317 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1317Coded : CoefficientMerge.Poly := [(nat_lit 3313, Int.ofNat (nat_lit 1))]
theorem atom1317Coded_decode : atom1317 = SparsePolynomial.decodeCubic 21 atom1317Coded := by decide +kernel
theorem atom1317Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9544641913440 : Int) atom1317Coded) := by
  have h := atom1317_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1317Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1318 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1318Coded : CoefficientMerge.Poly := [(nat_lit 3314, Int.ofNat (nat_lit 1))]
theorem atom1318Coded_decode : atom1318 = SparsePolynomial.decodeCubic 21 atom1318Coded := by decide +kernel
theorem atom1318Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18856319074560 : Int) atom1318Coded) := by
  have h := atom1318_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1318Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1319 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1319Coded : CoefficientMerge.Poly := [(nat_lit 3315, Int.ofNat (nat_lit 1))]
theorem atom1319Coded_decode : atom1319 = SparsePolynomial.decodeCubic 21 atom1319Coded := by decide +kernel
theorem atom1319Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22426001022240 : Int) atom1319Coded) := by
  have h := atom1319_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1319Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1320 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1320Coded : CoefficientMerge.Poly := [(nat_lit 3316, Int.ofNat (nat_lit 1))]
theorem atom1320Coded_decode : atom1320 = SparsePolynomial.decodeCubic 21 atom1320Coded := by decide +kernel
theorem atom1320Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32125924124064 : Int) atom1320Coded) := by
  have h := atom1320_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1320Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1321 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1321Coded : CoefficientMerge.Poly := [(nat_lit 3317, Int.ofNat (nat_lit 1))]
theorem atom1321Coded_decode : atom1321 = SparsePolynomial.decodeCubic 21 atom1321Coded := by decide +kernel
theorem atom1321Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42511529440800 : Int) atom1321Coded) := by
  have h := atom1321_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1321Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1322 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1322 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1322 = ((g 7) * (g 11) * (g 11)) := by
  norm_num [atom1322, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1322_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4747785840000 : Int) atom1322) := by
  rw [SparsePolynomial.eval_scale, eval_atom1322]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1322Coded : CoefficientMerge.Poly := [(nat_lit 3329, Int.ofNat (nat_lit 1))]
theorem atom1322Coded_decode : atom1322 = SparsePolynomial.decodeCubic 21 atom1322Coded := by decide +kernel
theorem atom1322Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4747785840000 : Int) atom1322Coded) := by
  have h := atom1322_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1322Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1323 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
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
def atom1323Coded : CoefficientMerge.Poly := [(nat_lit 3330, Int.ofNat (nat_lit 1))]
theorem atom1323Coded_decode : atom1323 = SparsePolynomial.decodeCubic 21 atom1323Coded := by decide +kernel
theorem atom1323Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8318410732800 : Int) atom1323Coded) := by
  have h := atom1323_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1323Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1324 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom1324Coded : CoefficientMerge.Poly := [(nat_lit 3331, Int.ofNat (nat_lit 1))]
theorem atom1324Coded_decode : atom1324 = SparsePolynomial.decodeCubic 21 atom1324Coded := by decide +kernel
theorem atom1324Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9018135302400 : Int) atom1324Coded) := by
  have h := atom1324_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1324Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1325 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1325Coded : CoefficientMerge.Poly := [(nat_lit 3332, Int.ofNat (nat_lit 1))]
theorem atom1325Coded_decode : atom1325 = SparsePolynomial.decodeCubic 21 atom1325Coded := by decide +kernel
theorem atom1325Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9717859872000 : Int) atom1325Coded) := by
  have h := atom1325_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1325Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1326 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1326Coded : CoefficientMerge.Poly := [(nat_lit 3333, Int.ofNat (nat_lit 1))]
theorem atom1326Coded_decode : atom1326 = SparsePolynomial.decodeCubic 21 atom1326Coded := by decide +kernel
theorem atom1326Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17823714742656 : Int) atom1326Coded) := by
  have h := atom1326_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1326Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1327 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1327Coded : CoefficientMerge.Poly := [(nat_lit 3334, Int.ofNat (nat_lit 1))]
theorem atom1327Coded_decode : atom1327 = SparsePolynomial.decodeCubic 21 atom1327Coded := by decide +kernel
theorem atom1327Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15047395107840 : Int) atom1327Coded) := by
  have h := atom1327_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1327Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1328 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1328Coded : CoefficientMerge.Poly := [(nat_lit 3335, Int.ofNat (nat_lit 1))]
theorem atom1328Coded_decode : atom1328 = SparsePolynomial.decodeCubic 21 atom1328Coded := by decide +kernel
theorem atom1328Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27687575007360 : Int) atom1328Coded) := by
  have h := atom1328_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1328Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1329 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1329Coded : CoefficientMerge.Poly := [(nat_lit 3336, Int.ofNat (nat_lit 1))]
theorem atom1329Coded_decode : atom1329 = SparsePolynomial.decodeCubic 21 atom1329Coded := by decide +kernel
theorem atom1329Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29300658949440 : Int) atom1329Coded) := by
  have h := atom1329_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1329Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1330 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1330Coded : CoefficientMerge.Poly := [(nat_lit 3337, Int.ofNat (nat_lit 1))]
theorem atom1330Coded_decode : atom1330 = SparsePolynomial.decodeCubic 21 atom1330Coded := by decide +kernel
theorem atom1330Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39568321822464 : Int) atom1330Coded) := by
  have h := atom1330_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1330Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1331 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1331Coded : CoefficientMerge.Poly := [(nat_lit 3338, Int.ofNat (nat_lit 1))]
theorem atom1331Coded_decode : atom1331 = SparsePolynomial.decodeCubic 21 atom1331Coded := by decide +kernel
theorem atom1331Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50335348946400 : Int) atom1331Coded) := by
  have h := atom1331_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1331Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1332 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1332 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1332 = ((g 7) * (g 12) * (g 12)) := by
  norm_num [atom1332, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1332_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7156230076800 : Int) atom1332) := by
  rw [SparsePolynomial.eval_scale, eval_atom1332]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1332Coded : CoefficientMerge.Poly := [(nat_lit 3351, Int.ofNat (nat_lit 1))]
theorem atom1332Coded_decode : atom1332 = SparsePolynomial.decodeCubic 21 atom1332Coded := by decide +kernel
theorem atom1332Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7156230076800 : Int) atom1332Coded) := by
  have h := atom1332_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1332Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1333 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom1333Coded : CoefficientMerge.Poly := [(nat_lit 3352, Int.ofNat (nat_lit 1))]
theorem atom1333Coded_decode : atom1333 = SparsePolynomial.decodeCubic 21 atom1333Coded := by decide +kernel
theorem atom1333Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14339521324800 : Int) atom1333Coded) := by
  have h := atom1333_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1333Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1334 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1334Coded : CoefficientMerge.Poly := [(nat_lit 3353, Int.ofNat (nat_lit 1))]
theorem atom1334Coded_decode : atom1334 = SparsePolynomial.decodeCubic 21 atom1334Coded := by decide +kernel
theorem atom1334Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14793762412800 : Int) atom1334Coded) := by
  have h := atom1334_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1334Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1335 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1335Coded : CoefficientMerge.Poly := [(nat_lit 3354, Int.ofNat (nat_lit 1))]
theorem atom1335Coded_decode : atom1335 = SparsePolynomial.decodeCubic 21 atom1335Coded := by decide +kernel
theorem atom1335Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19441485123456 : Int) atom1335Coded) := by
  have h := atom1335_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1335Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1336 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1336Coded : CoefficientMerge.Poly := [(nat_lit 3355, Int.ofNat (nat_lit 1))]
theorem atom1336Coded_decode : atom1336 = SparsePolynomial.decodeCubic 21 atom1336Coded := by decide +kernel
theorem atom1336Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19397114109440 : Int) atom1336Coded) := by
  have h := atom1336_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1336Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1337 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1337Coded : CoefficientMerge.Poly := [(nat_lit 3356, Int.ofNat (nat_lit 1))]
theorem atom1337Coded_decode : atom1337 = SparsePolynomial.decodeCubic 21 atom1337Coded := by decide +kernel
theorem atom1337Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31352906629760 : Int) atom1337Coded) := by
  have h := atom1337_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1337Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1338 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1338Coded : CoefficientMerge.Poly := [(nat_lit 3357, Int.ofNat (nat_lit 1))]
theorem atom1338Coded_decode : atom1338 = SparsePolynomial.decodeCubic 21 atom1338Coded := by decide +kernel
theorem atom1338Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34150544280640 : Int) atom1338Coded) := by
  have h := atom1338_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1338Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1339 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1339Coded : CoefficientMerge.Poly := [(nat_lit 3358, Int.ofNat (nat_lit 1))]
theorem atom1339Coded_decode : atom1339 = SparsePolynomial.decodeCubic 21 atom1339Coded := by decide +kernel
theorem atom1339Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43898083947264 : Int) atom1339Coded) := by
  have h := atom1339_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1339Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1340 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1340Coded : CoefficientMerge.Poly := [(nat_lit 3359, Int.ofNat (nat_lit 1))]
theorem atom1340Coded_decode : atom1340 = SparsePolynomial.decodeCubic 21 atom1340Coded := by decide +kernel
theorem atom1340Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (54883075413600 : Int) atom1340Coded) := by
  have h := atom1340_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1340Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1341 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1341 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1341 = ((g 7) * (g 13) * (g 13)) := by
  norm_num [atom1341, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1341_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10477390550400 : Int) atom1341) := by
  rw [SparsePolynomial.eval_scale, eval_atom1341]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1341Coded : CoefficientMerge.Poly := [(nat_lit 3373, Int.ofNat (nat_lit 1))]
theorem atom1341Coded_decode : atom1341 = SparsePolynomial.decodeCubic 21 atom1341Coded := by decide +kernel
theorem atom1341Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10477390550400 : Int) atom1341Coded) := by
  have h := atom1341_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1341Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1342 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1342Coded : CoefficientMerge.Poly := [(nat_lit 3374, Int.ofNat (nat_lit 1))]
theorem atom1342Coded_decode : atom1342 = SparsePolynomial.decodeCubic 21 atom1342Coded := by decide +kernel
theorem atom1342Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19824839136000 : Int) atom1342Coded) := by
  have h := atom1342_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1342Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1343 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1343Coded : CoefficientMerge.Poly := [(nat_lit 3375, Int.ofNat (nat_lit 1))]
theorem atom1343Coded_decode : atom1343 = SparsePolynomial.decodeCubic 21 atom1343Coded := by decide +kernel
theorem atom1343Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24472903179456 : Int) atom1343Coded) := by
  have h := atom1343_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1343Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1344 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1344Coded : CoefficientMerge.Poly := [(nat_lit 3376, Int.ofNat (nat_lit 1))]
theorem atom1344Coded_decode : atom1344 = SparsePolynomial.decodeCubic 21 atom1344Coded := by decide +kernel
theorem atom1344Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24292870914240 : Int) atom1344Coded) := by
  have h := atom1344_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1344Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1345 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1345Coded : CoefficientMerge.Poly := [(nat_lit 3377, Int.ofNat (nat_lit 1))]
theorem atom1345Coded_decode : atom1345 = SparsePolynomial.decodeCubic 21 atom1345Coded := by decide +kernel
theorem atom1345Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39375935372160 : Int) atom1345Coded) := by
  have h := atom1345_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1345Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1346 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1346Coded : CoefficientMerge.Poly := [(nat_lit 3378, Int.ofNat (nat_lit 1))]
theorem atom1346Coded_decode : atom1346 = SparsePolynomial.decodeCubic 21 atom1346Coded := by decide +kernel
theorem atom1346Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43793896443840 : Int) atom1346Coded) := by
  have h := atom1346_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1346Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1347 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1347Coded : CoefficientMerge.Poly := [(nat_lit 3379, Int.ofNat (nat_lit 1))]
theorem atom1347Coded_decode : atom1347 = SparsePolynomial.decodeCubic 21 atom1347Coded := by decide +kernel
theorem atom1347Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47292853414464 : Int) atom1347Coded) := by
  have h := atom1347_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1347Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1348 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1348Coded : CoefficientMerge.Poly := [(nat_lit 3380, Int.ofNat (nat_lit 1))]
theorem atom1348Coded_decode : atom1348 = SparsePolynomial.decodeCubic 21 atom1348Coded := by decide +kernel
theorem atom1348Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (64416097821600 : Int) atom1348Coded) := by
  have h := atom1348_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1348Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1349 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1349 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1349 = ((g 7) * (g 14) * (g 14)) := by
  norm_num [atom1349, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1349_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14909899939200 : Int) atom1349) := by
  rw [SparsePolynomial.eval_scale, eval_atom1349]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1349Coded : CoefficientMerge.Poly := [(nat_lit 3395, Int.ofNat (nat_lit 1))]
theorem atom1349Coded_decode : atom1349 = SparsePolynomial.decodeCubic 21 atom1349Coded := by decide +kernel
theorem atom1349Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14909899939200 : Int) atom1349Coded) := by
  have h := atom1349_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1349Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1350 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1350Coded : CoefficientMerge.Poly := [(nat_lit 3396, Int.ofNat (nat_lit 1))]
theorem atom1350Coded_decode : atom1350 = SparsePolynomial.decodeCubic 21 atom1350Coded := by decide +kernel
theorem atom1350Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29392479133056 : Int) atom1350Coded) := by
  have h := atom1350_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1350Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1351 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1351Coded : CoefficientMerge.Poly := [(nat_lit 3397, Int.ofNat (nat_lit 1))]
theorem atom1351Coded_decode : atom1351 = SparsePolynomial.decodeCubic 21 atom1351Coded := by decide +kernel
theorem atom1351Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29069478282240 : Int) atom1351Coded) := by
  have h := atom1351_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1351Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1352 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1352Coded : CoefficientMerge.Poly := [(nat_lit 3398, Int.ofNat (nat_lit 1))]
theorem atom1352Coded_decode : atom1352 = SparsePolynomial.decodeCubic 21 atom1352Coded := by decide +kernel
theorem atom1352Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49592493970560 : Int) atom1352Coded) := by
  have h := atom1352_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1352Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1353 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1353Coded : CoefficientMerge.Poly := [(nat_lit 3399, Int.ofNat (nat_lit 1))]
theorem atom1353Coded_decode : atom1353 = SparsePolynomial.decodeCubic 21 atom1353Coded := by decide +kernel
theorem atom1353Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55850131448640 : Int) atom1353Coded) := by
  have h := atom1353_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1353Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1354 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1354Coded : CoefficientMerge.Poly := [(nat_lit 3400, Int.ofNat (nat_lit 1))]
theorem atom1354Coded_decode : atom1354 = SparsePolynomial.decodeCubic 21 atom1354Coded := by decide +kernel
theorem atom1354Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55138349470464 : Int) atom1354Coded) := by
  have h := atom1354_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1354Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1355 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1355Coded : CoefficientMerge.Poly := [(nat_lit 3401, Int.ofNat (nat_lit 1))]
theorem atom1355Coded_decode : atom1355 = SparsePolynomial.decodeCubic 21 atom1355Coded := by decide +kernel
theorem atom1355Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (78532122866400 : Int) atom1355Coded) := by
  have h := atom1355_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1355Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1356 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1356 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1356 = ((g 7) * (g 15) * (g 15)) := by
  norm_num [atom1356, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1356_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21896742731904 : Int) atom1356) := by
  rw [SparsePolynomial.eval_scale, eval_atom1356]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1356Coded : CoefficientMerge.Poly := [(nat_lit 3417, Int.ofNat (nat_lit 1))]
theorem atom1356Coded_decode : atom1356 = SparsePolynomial.decodeCubic 21 atom1356Coded := by decide +kernel
theorem atom1356Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21896742731904 : Int) atom1356Coded) := by
  have h := atom1356_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1356Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1357 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1357Coded : CoefficientMerge.Poly := [(nat_lit 3418, Int.ofNat (nat_lit 1))]
theorem atom1357Coded_decode : atom1357 = SparsePolynomial.decodeCubic 21 atom1357Coded := by decide +kernel
theorem atom1357Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42928095901824 : Int) atom1357Coded) := by
  have h := atom1357_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1357Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1358 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1358Coded : CoefficientMerge.Poly := [(nat_lit 3419, Int.ofNat (nat_lit 1))]
theorem atom1358Coded_decode : atom1358 = SparsePolynomial.decodeCubic 21 atom1358Coded := by decide +kernel
theorem atom1358Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (68414874110208 : Int) atom1358Coded) := by
  have h := atom1358_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1358Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1359 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1359Coded : CoefficientMerge.Poly := [(nat_lit 3420, Int.ofNat (nat_lit 1))]
theorem atom1359Coded_decode : atom1359 = SparsePolynomial.decodeCubic 21 atom1359Coded := by decide +kernel
theorem atom1359Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (71594005599360 : Int) atom1359Coded) := by
  have h := atom1359_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1359Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1360 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1360Coded : CoefficientMerge.Poly := [(nat_lit 3421, Int.ofNat (nat_lit 1))]
theorem atom1360Coded_decode : atom1360 = SparsePolynomial.decodeCubic 21 atom1360Coded := by decide +kernel
theorem atom1360Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53238031188480 : Int) atom1360Coded) := by
  have h := atom1360_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1360Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1361 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1361Coded : CoefficientMerge.Poly := [(nat_lit 3422, Int.ofNat (nat_lit 1))]
theorem atom1361Coded_decode : atom1361 = SparsePolynomial.decodeCubic 21 atom1361Coded := by decide +kernel
theorem atom1361Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (80901900693504 : Int) atom1361Coded) := by
  have h := atom1361_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1361Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1362 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1362 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1362 = ((g 7) * (g 16) * (g 16)) := by
  norm_num [atom1362, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1362_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17225211406464 : Int) atom1362) := by
  rw [SparsePolynomial.eval_scale, eval_atom1362]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1362Coded : CoefficientMerge.Poly := [(nat_lit 3439, Int.ofNat (nat_lit 1))]
theorem atom1362Coded_decode : atom1362 = SparsePolynomial.decodeCubic 21 atom1362Coded := by decide +kernel
theorem atom1362Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17225211406464 : Int) atom1362Coded) := by
  have h := atom1362_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1362Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1363 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1363Coded : CoefficientMerge.Poly := [(nat_lit 3440, Int.ofNat (nat_lit 1))]
theorem atom1363Coded_decode : atom1363 = SparsePolynomial.decodeCubic 21 atom1363Coded := by decide +kernel
theorem atom1363Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (56900847134592 : Int) atom1363Coded) := by
  have h := atom1363_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1363Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1364 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1364Coded : CoefficientMerge.Poly := [(nat_lit 3441, Int.ofNat (nat_lit 1))]
theorem atom1364Coded_decode : atom1364 = SparsePolynomial.decodeCubic 21 atom1364Coded := by decide +kernel
theorem atom1364Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (63199359221184 : Int) atom1364Coded) := by
  have h := atom1364_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1364Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1365 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1365Coded : CoefficientMerge.Poly := [(nat_lit 3442, Int.ofNat (nat_lit 1))]
theorem atom1365Coded_decode : atom1365 = SparsePolynomial.decodeCubic 21 atom1365Coded := by decide +kernel
theorem atom1365Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47004130814208 : Int) atom1365Coded) := by
  have h := atom1365_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1365Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1366 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1366Coded : CoefficientMerge.Poly := [(nat_lit 3443, Int.ofNat (nat_lit 1))]
theorem atom1366Coded_decode : atom1366 = SparsePolynomial.decodeCubic 21 atom1366Coded := by decide +kernel
theorem atom1366Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (59161605357600 : Int) atom1366Coded) := by
  have h := atom1366_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1366Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1367 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1367 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1367 = ((g 7) * (g 17) * (g 17)) := by
  norm_num [atom1367, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1367_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41545743986304 : Int) atom1367) := by
  rw [SparsePolynomial.eval_scale, eval_atom1367]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1367Coded : CoefficientMerge.Poly := [(nat_lit 3461, Int.ofNat (nat_lit 1))]
theorem atom1367Coded_decode : atom1367 = SparsePolynomial.decodeCubic 21 atom1367Coded := by decide +kernel
theorem atom1367Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41545743986304 : Int) atom1367Coded) := by
  have h := atom1367_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1367Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1368 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1368Coded : CoefficientMerge.Poly := [(nat_lit 3462, Int.ofNat (nat_lit 1))]
theorem atom1368Coded_decode : atom1368 = SparsePolynomial.decodeCubic 21 atom1368Coded := by decide +kernel
theorem atom1368Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (70291863363456 : Int) atom1368Coded) := by
  have h := atom1368_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1368Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1369 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1369Coded : CoefficientMerge.Poly := [(nat_lit 3463, Int.ofNat (nat_lit 1))]
theorem atom1369Coded_decode : atom1369 = SparsePolynomial.decodeCubic 21 atom1369Coded := by decide +kernel
theorem atom1369Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48185112168960 : Int) atom1369Coded) := by
  have h := atom1369_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1369Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1370 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1370Coded : CoefficientMerge.Poly := [(nat_lit 3464, Int.ofNat (nat_lit 1))]
theorem atom1370Coded_decode : atom1370 = SparsePolynomial.decodeCubic 21 atom1370Coded := by decide +kernel
theorem atom1370Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (51533139292416 : Int) atom1370Coded) := by
  have h := atom1370_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1370Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1371 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1371 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1371 = ((g 7) * (g 18) * (g 18)) := by
  norm_num [atom1371, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1371_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22921685971776 : Int) atom1371) := by
  rw [SparsePolynomial.eval_scale, eval_atom1371]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1371Coded : CoefficientMerge.Poly := [(nat_lit 3483, Int.ofNat (nat_lit 1))]
theorem atom1371Coded_decode : atom1371 = SparsePolynomial.decodeCubic 21 atom1371Coded := by decide +kernel
theorem atom1371Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22921685971776 : Int) atom1371Coded) := by
  have h := atom1371_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1371Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1372 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1372Coded : CoefficientMerge.Poly := [(nat_lit 3484, Int.ofNat (nat_lit 1))]
theorem atom1372Coded_decode : atom1372 = SparsePolynomial.decodeCubic 21 atom1372Coded := by decide +kernel
theorem atom1372Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27537164315136 : Int) atom1372Coded) := by
  have h := atom1372_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1372Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1373 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1373Coded : CoefficientMerge.Poly := [(nat_lit 3485, Int.ofNat (nat_lit 1))]
theorem atom1373Coded_decode : atom1373 = SparsePolynomial.decodeCubic 21 atom1373Coded := by decide +kernel
theorem atom1373Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31480194875040 : Int) atom1373Coded) := by
  have h := atom1373_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1373Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1374 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1374 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1374 = ((g 8) * (g 8) * (g 8)) := by
  norm_num [atom1374, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1374_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1353863952000 : Int) atom1374) := by
  rw [SparsePolynomial.eval_scale, eval_atom1374]
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 8) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1374Coded : CoefficientMerge.Poly := [(nat_lit 3704, Int.ofNat (nat_lit 1))]
theorem atom1374Coded_decode : atom1374 = SparsePolynomial.decodeCubic 21 atom1374Coded := by decide +kernel
theorem atom1374Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1353863952000 : Int) atom1374Coded) := by
  have h := atom1374_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1374Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1375 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1375 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1375 = ((g 8) * (g 8) * (g 9)) := by
  norm_num [atom1375, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1375_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1372387968000 : Int) atom1375) := by
  rw [SparsePolynomial.eval_scale, eval_atom1375]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1375Coded : CoefficientMerge.Poly := [(nat_lit 3705, Int.ofNat (nat_lit 1))]
theorem atom1375Coded_decode : atom1375 = SparsePolynomial.decodeCubic 21 atom1375Coded := by decide +kernel
theorem atom1375Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1372387968000 : Int) atom1375Coded) := by
  have h := atom1375_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1375Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block018 : CoefficientMerge.Poly := [(nat_lit 3270, Int.ofNat (nat_lit 6427474232112)), (nat_lit 3272, Int.ofNat (nat_lit 1510388496720)), (nat_lit 3273, Int.ofNat (nat_lit 5786258284800)), (nat_lit 3274, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3275, Int.ofNat (nat_lit 17391151612800)), (nat_lit 3285, Int.ofNat (nat_lit 896401296000)), (nat_lit 3288, Int.ofNat (nat_lit 686193984000)), (nat_lit 3289, Int.ofNat (nat_lit 1372387968000)), (nat_lit 3290, Int.ofNat (nat_lit 2058581952000)), (nat_lit 3291, Int.ofNat (nat_lit 8185219145856)), (nat_lit 3292, Int.ofNat (nat_lit 3335794446240)), (nat_lit 3293, Int.ofNat (nat_lit 9115747148160)), (nat_lit 3294, Int.ofNat (nat_lit 13951505319840)), (nat_lit 3295, Int.ofNat (nat_lit 22686649344864)), (nat_lit 3296, Int.ofNat (nat_lit 32365160755200)), (nat_lit 3307, Int.ofNat (nat_lit 2262023971200)), (nat_lit 3308, Int.ofNat (nat_lit 3851384544000)), (nat_lit 3309, Int.ofNat (nat_lit 4201246828800)), (nat_lit 3310, Int.ofNat (nat_lit 4978289030400)), (nat_lit 3311, Int.ofNat (nat_lit 5755331232000)), (nat_lit 3312, Int.ofNat (nat_lit 13173656115456)), (nat_lit 3313, Int.ofNat (nat_lit 9544641913440)), (nat_lit 3314, Int.ofNat (nat_lit 18856319074560)), (nat_lit 3315, Int.ofNat (nat_lit 22426001022240)), (nat_lit 3316, Int.ofNat (nat_lit 32125924124064)), (nat_lit 3317, Int.ofNat (nat_lit 42511529440800)), (nat_lit 3329, Int.ofNat (nat_lit 4747785840000)), (nat_lit 3330, Int.ofNat (nat_lit 8318410732800)), (nat_lit 3331, Int.ofNat (nat_lit 9018135302400)), (nat_lit 3332, Int.ofNat (nat_lit 9717859872000)), (nat_lit 3333, Int.ofNat (nat_lit 17823714742656)), (nat_lit 3334, Int.ofNat (nat_lit 15047395107840)), (nat_lit 3335, Int.ofNat (nat_lit 27687575007360)), (nat_lit 3336, Int.ofNat (nat_lit 29300658949440)), (nat_lit 3337, Int.ofNat (nat_lit 39568321822464)), (nat_lit 3338, Int.ofNat (nat_lit 50335348946400)), (nat_lit 3351, Int.ofNat (nat_lit 7156230076800)), (nat_lit 3352, Int.ofNat (nat_lit 14339521324800)), (nat_lit 3353, Int.ofNat (nat_lit 14793762412800)), (nat_lit 3354, Int.ofNat (nat_lit 19441485123456)), (nat_lit 3355, Int.ofNat (nat_lit 19397114109440)), (nat_lit 3356, Int.ofNat (nat_lit 31352906629760)), (nat_lit 3357, Int.ofNat (nat_lit 34150544280640)), (nat_lit 3358, Int.ofNat (nat_lit 43898083947264)), (nat_lit 3359, Int.ofNat (nat_lit 54883075413600)), (nat_lit 3373, Int.ofNat (nat_lit 10477390550400)), (nat_lit 3374, Int.ofNat (nat_lit 19824839136000)), (nat_lit 3375, Int.ofNat (nat_lit 24472903179456)), (nat_lit 3376, Int.ofNat (nat_lit 24292870914240)), (nat_lit 3377, Int.ofNat (nat_lit 39375935372160)), (nat_lit 3378, Int.ofNat (nat_lit 43793896443840)), (nat_lit 3379, Int.ofNat (nat_lit 47292853414464)), (nat_lit 3380, Int.ofNat (nat_lit 64416097821600)), (nat_lit 3395, Int.ofNat (nat_lit 14909899939200)), (nat_lit 3396, Int.ofNat (nat_lit 29392479133056)), (nat_lit 3397, Int.ofNat (nat_lit 29069478282240)), (nat_lit 3398, Int.ofNat (nat_lit 49592493970560)), (nat_lit 3399, Int.ofNat (nat_lit 55850131448640)), (nat_lit 3400, Int.ofNat (nat_lit 55138349470464)), (nat_lit 3401, Int.ofNat (nat_lit 78532122866400)), (nat_lit 3417, Int.ofNat (nat_lit 21896742731904)), (nat_lit 3418, Int.ofNat (nat_lit 42928095901824)), (nat_lit 3419, Int.ofNat (nat_lit 68414874110208)), (nat_lit 3420, Int.ofNat (nat_lit 71594005599360)), (nat_lit 3421, Int.ofNat (nat_lit 53238031188480)), (nat_lit 3422, Int.ofNat (nat_lit 80901900693504)), (nat_lit 3439, Int.ofNat (nat_lit 17225211406464)), (nat_lit 3440, Int.ofNat (nat_lit 56900847134592)), (nat_lit 3441, Int.ofNat (nat_lit 63199359221184)), (nat_lit 3442, Int.ofNat (nat_lit 47004130814208)), (nat_lit 3443, Int.ofNat (nat_lit 59161605357600)), (nat_lit 3461, Int.ofNat (nat_lit 41545743986304)), (nat_lit 3462, Int.ofNat (nat_lit 70291863363456)), (nat_lit 3463, Int.ofNat (nat_lit 48185112168960)), (nat_lit 3464, Int.ofNat (nat_lit 51533139292416)), (nat_lit 3483, Int.ofNat (nat_lit 22921685971776)), (nat_lit 3484, Int.ofNat (nat_lit 27537164315136)), (nat_lit 3485, Int.ofNat (nat_lit 31480194875040)), (nat_lit 3704, Int.ofNat (nat_lit 1353863952000)), (nat_lit 3705, Int.ofNat (nat_lit 1372387968000))]
def block018_data_flat000 : CoefficientMerge.Poly := [(nat_lit 3270, Int.ofNat (nat_lit 6427474232112))]
theorem block018_data_flat000_step : block018_data_flat000 = (CoefficientMerge.scale (6427474232112 : Int) atom1296Coded) := by decide +kernel
theorem block018_data_flat000_original : block018_data_flat000 = (CoefficientMerge.scale (6427474232112 : Int) atom1296Coded) := by
  rw [block018_data_flat000_step]
def block018_data_flat001 : CoefficientMerge.Poly := [(nat_lit 3272, Int.ofNat (nat_lit 1510388496720))]
theorem block018_data_flat001_step : block018_data_flat001 = (CoefficientMerge.scale (1510388496720 : Int) atom1297Coded) := by decide +kernel
theorem block018_data_flat001_original : block018_data_flat001 = (CoefficientMerge.scale (1510388496720 : Int) atom1297Coded) := by
  rw [block018_data_flat001_step]
def block018_data_flat002 : CoefficientMerge.Poly := [(nat_lit 3270, Int.ofNat (nat_lit 6427474232112)), (nat_lit 3272, Int.ofNat (nat_lit 1510388496720))]
theorem block018_data_flat002_step : block018_data_flat002 = (CoefficientMerge.fastMerge block018_data_flat000 block018_data_flat001) := by decide +kernel
theorem block018_data_flat002_original : block018_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6427474232112 : Int) atom1296Coded) (CoefficientMerge.scale (1510388496720 : Int) atom1297Coded)) := by
  rw [block018_data_flat002_step, block018_data_flat000_original, block018_data_flat001_original]
def block018_data_flat003 : CoefficientMerge.Poly := [(nat_lit 3273, Int.ofNat (nat_lit 5786258284800))]
theorem block018_data_flat003_step : block018_data_flat003 = (CoefficientMerge.scale (5786258284800 : Int) atom1298Coded) := by decide +kernel
theorem block018_data_flat003_original : block018_data_flat003 = (CoefficientMerge.scale (5786258284800 : Int) atom1298Coded) := by
  rw [block018_data_flat003_step]
def block018_data_flat004 : CoefficientMerge.Poly := [(nat_lit 3274, Int.ofNat (nat_lit 11171238059520))]
theorem block018_data_flat004_step : block018_data_flat004 = (CoefficientMerge.scale (11171238059520 : Int) atom1299Coded) := by decide +kernel
theorem block018_data_flat004_original : block018_data_flat004 = (CoefficientMerge.scale (11171238059520 : Int) atom1299Coded) := by
  rw [block018_data_flat004_step]
def block018_data_flat005 : CoefficientMerge.Poly := [(nat_lit 3275, Int.ofNat (nat_lit 17391151612800))]
theorem block018_data_flat005_step : block018_data_flat005 = (CoefficientMerge.scale (17391151612800 : Int) atom1300Coded) := by decide +kernel
theorem block018_data_flat005_original : block018_data_flat005 = (CoefficientMerge.scale (17391151612800 : Int) atom1300Coded) := by
  rw [block018_data_flat005_step]
def block018_data_flat006 : CoefficientMerge.Poly := [(nat_lit 3274, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3275, Int.ofNat (nat_lit 17391151612800))]
theorem block018_data_flat006_step : block018_data_flat006 = (CoefficientMerge.fastMerge block018_data_flat004 block018_data_flat005) := by decide +kernel
theorem block018_data_flat006_original : block018_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1299Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1300Coded)) := by
  rw [block018_data_flat006_step, block018_data_flat004_original, block018_data_flat005_original]
def block018_data_flat007 : CoefficientMerge.Poly := [(nat_lit 3273, Int.ofNat (nat_lit 5786258284800)), (nat_lit 3274, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3275, Int.ofNat (nat_lit 17391151612800))]
theorem block018_data_flat007_step : block018_data_flat007 = (CoefficientMerge.fastMerge block018_data_flat003 block018_data_flat006) := by decide +kernel
theorem block018_data_flat007_original : block018_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1299Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1300Coded))) := by
  rw [block018_data_flat007_step, block018_data_flat003_original, block018_data_flat006_original]
def block018_data_flat008 : CoefficientMerge.Poly := [(nat_lit 3270, Int.ofNat (nat_lit 6427474232112)), (nat_lit 3272, Int.ofNat (nat_lit 1510388496720)), (nat_lit 3273, Int.ofNat (nat_lit 5786258284800)), (nat_lit 3274, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3275, Int.ofNat (nat_lit 17391151612800))]
theorem block018_data_flat008_step : block018_data_flat008 = (CoefficientMerge.fastMerge block018_data_flat002 block018_data_flat007) := by decide +kernel
theorem block018_data_flat008_original : block018_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6427474232112 : Int) atom1296Coded) (CoefficientMerge.scale (1510388496720 : Int) atom1297Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1299Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1300Coded)))) := by
  rw [block018_data_flat008_step, block018_data_flat002_original, block018_data_flat007_original]
def block018_data_flat009 : CoefficientMerge.Poly := [(nat_lit 3285, Int.ofNat (nat_lit 896401296000))]
theorem block018_data_flat009_step : block018_data_flat009 = (CoefficientMerge.scale (896401296000 : Int) atom1301Coded) := by decide +kernel
theorem block018_data_flat009_original : block018_data_flat009 = (CoefficientMerge.scale (896401296000 : Int) atom1301Coded) := by
  rw [block018_data_flat009_step]
def block018_data_flat010 : CoefficientMerge.Poly := [(nat_lit 3288, Int.ofNat (nat_lit 686193984000))]
theorem block018_data_flat010_step : block018_data_flat010 = (CoefficientMerge.scale (686193984000 : Int) atom1302Coded) := by decide +kernel
theorem block018_data_flat010_original : block018_data_flat010 = (CoefficientMerge.scale (686193984000 : Int) atom1302Coded) := by
  rw [block018_data_flat010_step]
def block018_data_flat011 : CoefficientMerge.Poly := [(nat_lit 3285, Int.ofNat (nat_lit 896401296000)), (nat_lit 3288, Int.ofNat (nat_lit 686193984000))]
theorem block018_data_flat011_step : block018_data_flat011 = (CoefficientMerge.fastMerge block018_data_flat009 block018_data_flat010) := by decide +kernel
theorem block018_data_flat011_original : block018_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (896401296000 : Int) atom1301Coded) (CoefficientMerge.scale (686193984000 : Int) atom1302Coded)) := by
  rw [block018_data_flat011_step, block018_data_flat009_original, block018_data_flat010_original]
def block018_data_flat012 : CoefficientMerge.Poly := [(nat_lit 3289, Int.ofNat (nat_lit 1372387968000))]
theorem block018_data_flat012_step : block018_data_flat012 = (CoefficientMerge.scale (1372387968000 : Int) atom1303Coded) := by decide +kernel
theorem block018_data_flat012_original : block018_data_flat012 = (CoefficientMerge.scale (1372387968000 : Int) atom1303Coded) := by
  rw [block018_data_flat012_step]
def block018_data_flat013 : CoefficientMerge.Poly := [(nat_lit 3290, Int.ofNat (nat_lit 2058581952000))]
theorem block018_data_flat013_step : block018_data_flat013 = (CoefficientMerge.scale (2058581952000 : Int) atom1304Coded) := by decide +kernel
theorem block018_data_flat013_original : block018_data_flat013 = (CoefficientMerge.scale (2058581952000 : Int) atom1304Coded) := by
  rw [block018_data_flat013_step]
def block018_data_flat014 : CoefficientMerge.Poly := [(nat_lit 3291, Int.ofNat (nat_lit 8185219145856))]
theorem block018_data_flat014_step : block018_data_flat014 = (CoefficientMerge.scale (8185219145856 : Int) atom1305Coded) := by decide +kernel
theorem block018_data_flat014_original : block018_data_flat014 = (CoefficientMerge.scale (8185219145856 : Int) atom1305Coded) := by
  rw [block018_data_flat014_step]
def block018_data_flat015 : CoefficientMerge.Poly := [(nat_lit 3290, Int.ofNat (nat_lit 2058581952000)), (nat_lit 3291, Int.ofNat (nat_lit 8185219145856))]
theorem block018_data_flat015_step : block018_data_flat015 = (CoefficientMerge.fastMerge block018_data_flat013 block018_data_flat014) := by decide +kernel
theorem block018_data_flat015_original : block018_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2058581952000 : Int) atom1304Coded) (CoefficientMerge.scale (8185219145856 : Int) atom1305Coded)) := by
  rw [block018_data_flat015_step, block018_data_flat013_original, block018_data_flat014_original]
def block018_data_flat016 : CoefficientMerge.Poly := [(nat_lit 3289, Int.ofNat (nat_lit 1372387968000)), (nat_lit 3290, Int.ofNat (nat_lit 2058581952000)), (nat_lit 3291, Int.ofNat (nat_lit 8185219145856))]
theorem block018_data_flat016_step : block018_data_flat016 = (CoefficientMerge.fastMerge block018_data_flat012 block018_data_flat015) := by decide +kernel
theorem block018_data_flat016_original : block018_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1372387968000 : Int) atom1303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2058581952000 : Int) atom1304Coded) (CoefficientMerge.scale (8185219145856 : Int) atom1305Coded))) := by
  rw [block018_data_flat016_step, block018_data_flat012_original, block018_data_flat015_original]
def block018_data_flat017 : CoefficientMerge.Poly := [(nat_lit 3285, Int.ofNat (nat_lit 896401296000)), (nat_lit 3288, Int.ofNat (nat_lit 686193984000)), (nat_lit 3289, Int.ofNat (nat_lit 1372387968000)), (nat_lit 3290, Int.ofNat (nat_lit 2058581952000)), (nat_lit 3291, Int.ofNat (nat_lit 8185219145856))]
theorem block018_data_flat017_step : block018_data_flat017 = (CoefficientMerge.fastMerge block018_data_flat011 block018_data_flat016) := by decide +kernel
theorem block018_data_flat017_original : block018_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (896401296000 : Int) atom1301Coded) (CoefficientMerge.scale (686193984000 : Int) atom1302Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1372387968000 : Int) atom1303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2058581952000 : Int) atom1304Coded) (CoefficientMerge.scale (8185219145856 : Int) atom1305Coded)))) := by
  rw [block018_data_flat017_step, block018_data_flat011_original, block018_data_flat016_original]
def block018_data_flat018 : CoefficientMerge.Poly := [(nat_lit 3270, Int.ofNat (nat_lit 6427474232112)), (nat_lit 3272, Int.ofNat (nat_lit 1510388496720)), (nat_lit 3273, Int.ofNat (nat_lit 5786258284800)), (nat_lit 3274, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3275, Int.ofNat (nat_lit 17391151612800)), (nat_lit 3285, Int.ofNat (nat_lit 896401296000)), (nat_lit 3288, Int.ofNat (nat_lit 686193984000)), (nat_lit 3289, Int.ofNat (nat_lit 1372387968000)), (nat_lit 3290, Int.ofNat (nat_lit 2058581952000)), (nat_lit 3291, Int.ofNat (nat_lit 8185219145856))]
theorem block018_data_flat018_step : block018_data_flat018 = (CoefficientMerge.fastMerge block018_data_flat008 block018_data_flat017) := by decide +kernel
theorem block018_data_flat018_original : block018_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6427474232112 : Int) atom1296Coded) (CoefficientMerge.scale (1510388496720 : Int) atom1297Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1299Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1300Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (896401296000 : Int) atom1301Coded) (CoefficientMerge.scale (686193984000 : Int) atom1302Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1372387968000 : Int) atom1303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2058581952000 : Int) atom1304Coded) (CoefficientMerge.scale (8185219145856 : Int) atom1305Coded))))) := by
  rw [block018_data_flat018_step, block018_data_flat008_original, block018_data_flat017_original]
def block018_data_flat019 : CoefficientMerge.Poly := [(nat_lit 3292, Int.ofNat (nat_lit 3335794446240))]
theorem block018_data_flat019_step : block018_data_flat019 = (CoefficientMerge.scale (3335794446240 : Int) atom1306Coded) := by decide +kernel
theorem block018_data_flat019_original : block018_data_flat019 = (CoefficientMerge.scale (3335794446240 : Int) atom1306Coded) := by
  rw [block018_data_flat019_step]
def block018_data_flat020 : CoefficientMerge.Poly := [(nat_lit 3293, Int.ofNat (nat_lit 9115747148160))]
theorem block018_data_flat020_step : block018_data_flat020 = (CoefficientMerge.scale (9115747148160 : Int) atom1307Coded) := by decide +kernel
theorem block018_data_flat020_original : block018_data_flat020 = (CoefficientMerge.scale (9115747148160 : Int) atom1307Coded) := by
  rw [block018_data_flat020_step]
def block018_data_flat021 : CoefficientMerge.Poly := [(nat_lit 3292, Int.ofNat (nat_lit 3335794446240)), (nat_lit 3293, Int.ofNat (nat_lit 9115747148160))]
theorem block018_data_flat021_step : block018_data_flat021 = (CoefficientMerge.fastMerge block018_data_flat019 block018_data_flat020) := by decide +kernel
theorem block018_data_flat021_original : block018_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3335794446240 : Int) atom1306Coded) (CoefficientMerge.scale (9115747148160 : Int) atom1307Coded)) := by
  rw [block018_data_flat021_step, block018_data_flat019_original, block018_data_flat020_original]
def block018_data_flat022 : CoefficientMerge.Poly := [(nat_lit 3294, Int.ofNat (nat_lit 13951505319840))]
theorem block018_data_flat022_step : block018_data_flat022 = (CoefficientMerge.scale (13951505319840 : Int) atom1308Coded) := by decide +kernel
theorem block018_data_flat022_original : block018_data_flat022 = (CoefficientMerge.scale (13951505319840 : Int) atom1308Coded) := by
  rw [block018_data_flat022_step]
def block018_data_flat023 : CoefficientMerge.Poly := [(nat_lit 3295, Int.ofNat (nat_lit 22686649344864))]
theorem block018_data_flat023_step : block018_data_flat023 = (CoefficientMerge.scale (22686649344864 : Int) atom1309Coded) := by decide +kernel
theorem block018_data_flat023_original : block018_data_flat023 = (CoefficientMerge.scale (22686649344864 : Int) atom1309Coded) := by
  rw [block018_data_flat023_step]
def block018_data_flat024 : CoefficientMerge.Poly := [(nat_lit 3296, Int.ofNat (nat_lit 32365160755200))]
theorem block018_data_flat024_step : block018_data_flat024 = (CoefficientMerge.scale (32365160755200 : Int) atom1310Coded) := by decide +kernel
theorem block018_data_flat024_original : block018_data_flat024 = (CoefficientMerge.scale (32365160755200 : Int) atom1310Coded) := by
  rw [block018_data_flat024_step]
def block018_data_flat025 : CoefficientMerge.Poly := [(nat_lit 3295, Int.ofNat (nat_lit 22686649344864)), (nat_lit 3296, Int.ofNat (nat_lit 32365160755200))]
theorem block018_data_flat025_step : block018_data_flat025 = (CoefficientMerge.fastMerge block018_data_flat023 block018_data_flat024) := by decide +kernel
theorem block018_data_flat025_original : block018_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22686649344864 : Int) atom1309Coded) (CoefficientMerge.scale (32365160755200 : Int) atom1310Coded)) := by
  rw [block018_data_flat025_step, block018_data_flat023_original, block018_data_flat024_original]
def block018_data_flat026 : CoefficientMerge.Poly := [(nat_lit 3294, Int.ofNat (nat_lit 13951505319840)), (nat_lit 3295, Int.ofNat (nat_lit 22686649344864)), (nat_lit 3296, Int.ofNat (nat_lit 32365160755200))]
theorem block018_data_flat026_step : block018_data_flat026 = (CoefficientMerge.fastMerge block018_data_flat022 block018_data_flat025) := by decide +kernel
theorem block018_data_flat026_original : block018_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13951505319840 : Int) atom1308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22686649344864 : Int) atom1309Coded) (CoefficientMerge.scale (32365160755200 : Int) atom1310Coded))) := by
  rw [block018_data_flat026_step, block018_data_flat022_original, block018_data_flat025_original]
def block018_data_flat027 : CoefficientMerge.Poly := [(nat_lit 3292, Int.ofNat (nat_lit 3335794446240)), (nat_lit 3293, Int.ofNat (nat_lit 9115747148160)), (nat_lit 3294, Int.ofNat (nat_lit 13951505319840)), (nat_lit 3295, Int.ofNat (nat_lit 22686649344864)), (nat_lit 3296, Int.ofNat (nat_lit 32365160755200))]
theorem block018_data_flat027_step : block018_data_flat027 = (CoefficientMerge.fastMerge block018_data_flat021 block018_data_flat026) := by decide +kernel
theorem block018_data_flat027_original : block018_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3335794446240 : Int) atom1306Coded) (CoefficientMerge.scale (9115747148160 : Int) atom1307Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13951505319840 : Int) atom1308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22686649344864 : Int) atom1309Coded) (CoefficientMerge.scale (32365160755200 : Int) atom1310Coded)))) := by
  rw [block018_data_flat027_step, block018_data_flat021_original, block018_data_flat026_original]
def block018_data_flat028 : CoefficientMerge.Poly := [(nat_lit 3307, Int.ofNat (nat_lit 2262023971200))]
theorem block018_data_flat028_step : block018_data_flat028 = (CoefficientMerge.scale (2262023971200 : Int) atom1311Coded) := by decide +kernel
theorem block018_data_flat028_original : block018_data_flat028 = (CoefficientMerge.scale (2262023971200 : Int) atom1311Coded) := by
  rw [block018_data_flat028_step]
def block018_data_flat029 : CoefficientMerge.Poly := [(nat_lit 3308, Int.ofNat (nat_lit 3851384544000))]
theorem block018_data_flat029_step : block018_data_flat029 = (CoefficientMerge.scale (3851384544000 : Int) atom1312Coded) := by decide +kernel
theorem block018_data_flat029_original : block018_data_flat029 = (CoefficientMerge.scale (3851384544000 : Int) atom1312Coded) := by
  rw [block018_data_flat029_step]
def block018_data_flat030 : CoefficientMerge.Poly := [(nat_lit 3307, Int.ofNat (nat_lit 2262023971200)), (nat_lit 3308, Int.ofNat (nat_lit 3851384544000))]
theorem block018_data_flat030_step : block018_data_flat030 = (CoefficientMerge.fastMerge block018_data_flat028 block018_data_flat029) := by decide +kernel
theorem block018_data_flat030_original : block018_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2262023971200 : Int) atom1311Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1312Coded)) := by
  rw [block018_data_flat030_step, block018_data_flat028_original, block018_data_flat029_original]
def block018_data_flat031 : CoefficientMerge.Poly := [(nat_lit 3309, Int.ofNat (nat_lit 4201246828800))]
theorem block018_data_flat031_step : block018_data_flat031 = (CoefficientMerge.scale (4201246828800 : Int) atom1313Coded) := by decide +kernel
theorem block018_data_flat031_original : block018_data_flat031 = (CoefficientMerge.scale (4201246828800 : Int) atom1313Coded) := by
  rw [block018_data_flat031_step]
def block018_data_flat032 : CoefficientMerge.Poly := [(nat_lit 3310, Int.ofNat (nat_lit 4978289030400))]
theorem block018_data_flat032_step : block018_data_flat032 = (CoefficientMerge.scale (4978289030400 : Int) atom1314Coded) := by decide +kernel
theorem block018_data_flat032_original : block018_data_flat032 = (CoefficientMerge.scale (4978289030400 : Int) atom1314Coded) := by
  rw [block018_data_flat032_step]
def block018_data_flat033 : CoefficientMerge.Poly := [(nat_lit 3311, Int.ofNat (nat_lit 5755331232000))]
theorem block018_data_flat033_step : block018_data_flat033 = (CoefficientMerge.scale (5755331232000 : Int) atom1315Coded) := by decide +kernel
theorem block018_data_flat033_original : block018_data_flat033 = (CoefficientMerge.scale (5755331232000 : Int) atom1315Coded) := by
  rw [block018_data_flat033_step]
def block018_data_flat034 : CoefficientMerge.Poly := [(nat_lit 3310, Int.ofNat (nat_lit 4978289030400)), (nat_lit 3311, Int.ofNat (nat_lit 5755331232000))]
theorem block018_data_flat034_step : block018_data_flat034 = (CoefficientMerge.fastMerge block018_data_flat032 block018_data_flat033) := by decide +kernel
theorem block018_data_flat034_original : block018_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4978289030400 : Int) atom1314Coded) (CoefficientMerge.scale (5755331232000 : Int) atom1315Coded)) := by
  rw [block018_data_flat034_step, block018_data_flat032_original, block018_data_flat033_original]
def block018_data_flat035 : CoefficientMerge.Poly := [(nat_lit 3309, Int.ofNat (nat_lit 4201246828800)), (nat_lit 3310, Int.ofNat (nat_lit 4978289030400)), (nat_lit 3311, Int.ofNat (nat_lit 5755331232000))]
theorem block018_data_flat035_step : block018_data_flat035 = (CoefficientMerge.fastMerge block018_data_flat031 block018_data_flat034) := by decide +kernel
theorem block018_data_flat035_original : block018_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4201246828800 : Int) atom1313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4978289030400 : Int) atom1314Coded) (CoefficientMerge.scale (5755331232000 : Int) atom1315Coded))) := by
  rw [block018_data_flat035_step, block018_data_flat031_original, block018_data_flat034_original]
def block018_data_flat036 : CoefficientMerge.Poly := [(nat_lit 3307, Int.ofNat (nat_lit 2262023971200)), (nat_lit 3308, Int.ofNat (nat_lit 3851384544000)), (nat_lit 3309, Int.ofNat (nat_lit 4201246828800)), (nat_lit 3310, Int.ofNat (nat_lit 4978289030400)), (nat_lit 3311, Int.ofNat (nat_lit 5755331232000))]
theorem block018_data_flat036_step : block018_data_flat036 = (CoefficientMerge.fastMerge block018_data_flat030 block018_data_flat035) := by decide +kernel
theorem block018_data_flat036_original : block018_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2262023971200 : Int) atom1311Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1312Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4201246828800 : Int) atom1313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4978289030400 : Int) atom1314Coded) (CoefficientMerge.scale (5755331232000 : Int) atom1315Coded)))) := by
  rw [block018_data_flat036_step, block018_data_flat030_original, block018_data_flat035_original]
def block018_data_flat037 : CoefficientMerge.Poly := [(nat_lit 3292, Int.ofNat (nat_lit 3335794446240)), (nat_lit 3293, Int.ofNat (nat_lit 9115747148160)), (nat_lit 3294, Int.ofNat (nat_lit 13951505319840)), (nat_lit 3295, Int.ofNat (nat_lit 22686649344864)), (nat_lit 3296, Int.ofNat (nat_lit 32365160755200)), (nat_lit 3307, Int.ofNat (nat_lit 2262023971200)), (nat_lit 3308, Int.ofNat (nat_lit 3851384544000)), (nat_lit 3309, Int.ofNat (nat_lit 4201246828800)), (nat_lit 3310, Int.ofNat (nat_lit 4978289030400)), (nat_lit 3311, Int.ofNat (nat_lit 5755331232000))]
theorem block018_data_flat037_step : block018_data_flat037 = (CoefficientMerge.fastMerge block018_data_flat027 block018_data_flat036) := by decide +kernel
theorem block018_data_flat037_original : block018_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3335794446240 : Int) atom1306Coded) (CoefficientMerge.scale (9115747148160 : Int) atom1307Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13951505319840 : Int) atom1308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22686649344864 : Int) atom1309Coded) (CoefficientMerge.scale (32365160755200 : Int) atom1310Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2262023971200 : Int) atom1311Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1312Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4201246828800 : Int) atom1313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4978289030400 : Int) atom1314Coded) (CoefficientMerge.scale (5755331232000 : Int) atom1315Coded))))) := by
  rw [block018_data_flat037_step, block018_data_flat027_original, block018_data_flat036_original]
def block018_data_flat038 : CoefficientMerge.Poly := [(nat_lit 3270, Int.ofNat (nat_lit 6427474232112)), (nat_lit 3272, Int.ofNat (nat_lit 1510388496720)), (nat_lit 3273, Int.ofNat (nat_lit 5786258284800)), (nat_lit 3274, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3275, Int.ofNat (nat_lit 17391151612800)), (nat_lit 3285, Int.ofNat (nat_lit 896401296000)), (nat_lit 3288, Int.ofNat (nat_lit 686193984000)), (nat_lit 3289, Int.ofNat (nat_lit 1372387968000)), (nat_lit 3290, Int.ofNat (nat_lit 2058581952000)), (nat_lit 3291, Int.ofNat (nat_lit 8185219145856)), (nat_lit 3292, Int.ofNat (nat_lit 3335794446240)), (nat_lit 3293, Int.ofNat (nat_lit 9115747148160)), (nat_lit 3294, Int.ofNat (nat_lit 13951505319840)), (nat_lit 3295, Int.ofNat (nat_lit 22686649344864)), (nat_lit 3296, Int.ofNat (nat_lit 32365160755200)), (nat_lit 3307, Int.ofNat (nat_lit 2262023971200)), (nat_lit 3308, Int.ofNat (nat_lit 3851384544000)), (nat_lit 3309, Int.ofNat (nat_lit 4201246828800)), (nat_lit 3310, Int.ofNat (nat_lit 4978289030400)), (nat_lit 3311, Int.ofNat (nat_lit 5755331232000))]
theorem block018_data_flat038_step : block018_data_flat038 = (CoefficientMerge.fastMerge block018_data_flat018 block018_data_flat037) := by decide +kernel
theorem block018_data_flat038_original : block018_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6427474232112 : Int) atom1296Coded) (CoefficientMerge.scale (1510388496720 : Int) atom1297Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1299Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1300Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (896401296000 : Int) atom1301Coded) (CoefficientMerge.scale (686193984000 : Int) atom1302Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1372387968000 : Int) atom1303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2058581952000 : Int) atom1304Coded) (CoefficientMerge.scale (8185219145856 : Int) atom1305Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3335794446240 : Int) atom1306Coded) (CoefficientMerge.scale (9115747148160 : Int) atom1307Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13951505319840 : Int) atom1308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22686649344864 : Int) atom1309Coded) (CoefficientMerge.scale (32365160755200 : Int) atom1310Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2262023971200 : Int) atom1311Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1312Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4201246828800 : Int) atom1313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4978289030400 : Int) atom1314Coded) (CoefficientMerge.scale (5755331232000 : Int) atom1315Coded)))))) := by
  rw [block018_data_flat038_step, block018_data_flat018_original, block018_data_flat037_original]
def block018_data_flat039 : CoefficientMerge.Poly := [(nat_lit 3312, Int.ofNat (nat_lit 13173656115456))]
theorem block018_data_flat039_step : block018_data_flat039 = (CoefficientMerge.scale (13173656115456 : Int) atom1316Coded) := by decide +kernel
theorem block018_data_flat039_original : block018_data_flat039 = (CoefficientMerge.scale (13173656115456 : Int) atom1316Coded) := by
  rw [block018_data_flat039_step]
def block018_data_flat040 : CoefficientMerge.Poly := [(nat_lit 3313, Int.ofNat (nat_lit 9544641913440))]
theorem block018_data_flat040_step : block018_data_flat040 = (CoefficientMerge.scale (9544641913440 : Int) atom1317Coded) := by decide +kernel
theorem block018_data_flat040_original : block018_data_flat040 = (CoefficientMerge.scale (9544641913440 : Int) atom1317Coded) := by
  rw [block018_data_flat040_step]
def block018_data_flat041 : CoefficientMerge.Poly := [(nat_lit 3312, Int.ofNat (nat_lit 13173656115456)), (nat_lit 3313, Int.ofNat (nat_lit 9544641913440))]
theorem block018_data_flat041_step : block018_data_flat041 = (CoefficientMerge.fastMerge block018_data_flat039 block018_data_flat040) := by decide +kernel
theorem block018_data_flat041_original : block018_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13173656115456 : Int) atom1316Coded) (CoefficientMerge.scale (9544641913440 : Int) atom1317Coded)) := by
  rw [block018_data_flat041_step, block018_data_flat039_original, block018_data_flat040_original]
def block018_data_flat042 : CoefficientMerge.Poly := [(nat_lit 3314, Int.ofNat (nat_lit 18856319074560))]
theorem block018_data_flat042_step : block018_data_flat042 = (CoefficientMerge.scale (18856319074560 : Int) atom1318Coded) := by decide +kernel
theorem block018_data_flat042_original : block018_data_flat042 = (CoefficientMerge.scale (18856319074560 : Int) atom1318Coded) := by
  rw [block018_data_flat042_step]
def block018_data_flat043 : CoefficientMerge.Poly := [(nat_lit 3315, Int.ofNat (nat_lit 22426001022240))]
theorem block018_data_flat043_step : block018_data_flat043 = (CoefficientMerge.scale (22426001022240 : Int) atom1319Coded) := by decide +kernel
theorem block018_data_flat043_original : block018_data_flat043 = (CoefficientMerge.scale (22426001022240 : Int) atom1319Coded) := by
  rw [block018_data_flat043_step]
def block018_data_flat044 : CoefficientMerge.Poly := [(nat_lit 3316, Int.ofNat (nat_lit 32125924124064))]
theorem block018_data_flat044_step : block018_data_flat044 = (CoefficientMerge.scale (32125924124064 : Int) atom1320Coded) := by decide +kernel
theorem block018_data_flat044_original : block018_data_flat044 = (CoefficientMerge.scale (32125924124064 : Int) atom1320Coded) := by
  rw [block018_data_flat044_step]
def block018_data_flat045 : CoefficientMerge.Poly := [(nat_lit 3315, Int.ofNat (nat_lit 22426001022240)), (nat_lit 3316, Int.ofNat (nat_lit 32125924124064))]
theorem block018_data_flat045_step : block018_data_flat045 = (CoefficientMerge.fastMerge block018_data_flat043 block018_data_flat044) := by decide +kernel
theorem block018_data_flat045_original : block018_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22426001022240 : Int) atom1319Coded) (CoefficientMerge.scale (32125924124064 : Int) atom1320Coded)) := by
  rw [block018_data_flat045_step, block018_data_flat043_original, block018_data_flat044_original]
def block018_data_flat046 : CoefficientMerge.Poly := [(nat_lit 3314, Int.ofNat (nat_lit 18856319074560)), (nat_lit 3315, Int.ofNat (nat_lit 22426001022240)), (nat_lit 3316, Int.ofNat (nat_lit 32125924124064))]
theorem block018_data_flat046_step : block018_data_flat046 = (CoefficientMerge.fastMerge block018_data_flat042 block018_data_flat045) := by decide +kernel
theorem block018_data_flat046_original : block018_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18856319074560 : Int) atom1318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22426001022240 : Int) atom1319Coded) (CoefficientMerge.scale (32125924124064 : Int) atom1320Coded))) := by
  rw [block018_data_flat046_step, block018_data_flat042_original, block018_data_flat045_original]
def block018_data_flat047 : CoefficientMerge.Poly := [(nat_lit 3312, Int.ofNat (nat_lit 13173656115456)), (nat_lit 3313, Int.ofNat (nat_lit 9544641913440)), (nat_lit 3314, Int.ofNat (nat_lit 18856319074560)), (nat_lit 3315, Int.ofNat (nat_lit 22426001022240)), (nat_lit 3316, Int.ofNat (nat_lit 32125924124064))]
theorem block018_data_flat047_step : block018_data_flat047 = (CoefficientMerge.fastMerge block018_data_flat041 block018_data_flat046) := by decide +kernel
theorem block018_data_flat047_original : block018_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13173656115456 : Int) atom1316Coded) (CoefficientMerge.scale (9544641913440 : Int) atom1317Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18856319074560 : Int) atom1318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22426001022240 : Int) atom1319Coded) (CoefficientMerge.scale (32125924124064 : Int) atom1320Coded)))) := by
  rw [block018_data_flat047_step, block018_data_flat041_original, block018_data_flat046_original]
def block018_data_flat048 : CoefficientMerge.Poly := [(nat_lit 3317, Int.ofNat (nat_lit 42511529440800))]
theorem block018_data_flat048_step : block018_data_flat048 = (CoefficientMerge.scale (42511529440800 : Int) atom1321Coded) := by decide +kernel
theorem block018_data_flat048_original : block018_data_flat048 = (CoefficientMerge.scale (42511529440800 : Int) atom1321Coded) := by
  rw [block018_data_flat048_step]
def block018_data_flat049 : CoefficientMerge.Poly := [(nat_lit 3329, Int.ofNat (nat_lit 4747785840000))]
theorem block018_data_flat049_step : block018_data_flat049 = (CoefficientMerge.scale (4747785840000 : Int) atom1322Coded) := by decide +kernel
theorem block018_data_flat049_original : block018_data_flat049 = (CoefficientMerge.scale (4747785840000 : Int) atom1322Coded) := by
  rw [block018_data_flat049_step]
def block018_data_flat050 : CoefficientMerge.Poly := [(nat_lit 3317, Int.ofNat (nat_lit 42511529440800)), (nat_lit 3329, Int.ofNat (nat_lit 4747785840000))]
theorem block018_data_flat050_step : block018_data_flat050 = (CoefficientMerge.fastMerge block018_data_flat048 block018_data_flat049) := by decide +kernel
theorem block018_data_flat050_original : block018_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (42511529440800 : Int) atom1321Coded) (CoefficientMerge.scale (4747785840000 : Int) atom1322Coded)) := by
  rw [block018_data_flat050_step, block018_data_flat048_original, block018_data_flat049_original]
def block018_data_flat051 : CoefficientMerge.Poly := [(nat_lit 3330, Int.ofNat (nat_lit 8318410732800))]
theorem block018_data_flat051_step : block018_data_flat051 = (CoefficientMerge.scale (8318410732800 : Int) atom1323Coded) := by decide +kernel
theorem block018_data_flat051_original : block018_data_flat051 = (CoefficientMerge.scale (8318410732800 : Int) atom1323Coded) := by
  rw [block018_data_flat051_step]
def block018_data_flat052 : CoefficientMerge.Poly := [(nat_lit 3331, Int.ofNat (nat_lit 9018135302400))]
theorem block018_data_flat052_step : block018_data_flat052 = (CoefficientMerge.scale (9018135302400 : Int) atom1324Coded) := by decide +kernel
theorem block018_data_flat052_original : block018_data_flat052 = (CoefficientMerge.scale (9018135302400 : Int) atom1324Coded) := by
  rw [block018_data_flat052_step]
def block018_data_flat053 : CoefficientMerge.Poly := [(nat_lit 3332, Int.ofNat (nat_lit 9717859872000))]
theorem block018_data_flat053_step : block018_data_flat053 = (CoefficientMerge.scale (9717859872000 : Int) atom1325Coded) := by decide +kernel
theorem block018_data_flat053_original : block018_data_flat053 = (CoefficientMerge.scale (9717859872000 : Int) atom1325Coded) := by
  rw [block018_data_flat053_step]
def block018_data_flat054 : CoefficientMerge.Poly := [(nat_lit 3331, Int.ofNat (nat_lit 9018135302400)), (nat_lit 3332, Int.ofNat (nat_lit 9717859872000))]
theorem block018_data_flat054_step : block018_data_flat054 = (CoefficientMerge.fastMerge block018_data_flat052 block018_data_flat053) := by decide +kernel
theorem block018_data_flat054_original : block018_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9018135302400 : Int) atom1324Coded) (CoefficientMerge.scale (9717859872000 : Int) atom1325Coded)) := by
  rw [block018_data_flat054_step, block018_data_flat052_original, block018_data_flat053_original]
def block018_data_flat055 : CoefficientMerge.Poly := [(nat_lit 3330, Int.ofNat (nat_lit 8318410732800)), (nat_lit 3331, Int.ofNat (nat_lit 9018135302400)), (nat_lit 3332, Int.ofNat (nat_lit 9717859872000))]
theorem block018_data_flat055_step : block018_data_flat055 = (CoefficientMerge.fastMerge block018_data_flat051 block018_data_flat054) := by decide +kernel
theorem block018_data_flat055_original : block018_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8318410732800 : Int) atom1323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9018135302400 : Int) atom1324Coded) (CoefficientMerge.scale (9717859872000 : Int) atom1325Coded))) := by
  rw [block018_data_flat055_step, block018_data_flat051_original, block018_data_flat054_original]
def block018_data_flat056 : CoefficientMerge.Poly := [(nat_lit 3317, Int.ofNat (nat_lit 42511529440800)), (nat_lit 3329, Int.ofNat (nat_lit 4747785840000)), (nat_lit 3330, Int.ofNat (nat_lit 8318410732800)), (nat_lit 3331, Int.ofNat (nat_lit 9018135302400)), (nat_lit 3332, Int.ofNat (nat_lit 9717859872000))]
theorem block018_data_flat056_step : block018_data_flat056 = (CoefficientMerge.fastMerge block018_data_flat050 block018_data_flat055) := by decide +kernel
theorem block018_data_flat056_original : block018_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42511529440800 : Int) atom1321Coded) (CoefficientMerge.scale (4747785840000 : Int) atom1322Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8318410732800 : Int) atom1323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9018135302400 : Int) atom1324Coded) (CoefficientMerge.scale (9717859872000 : Int) atom1325Coded)))) := by
  rw [block018_data_flat056_step, block018_data_flat050_original, block018_data_flat055_original]
def block018_data_flat057 : CoefficientMerge.Poly := [(nat_lit 3312, Int.ofNat (nat_lit 13173656115456)), (nat_lit 3313, Int.ofNat (nat_lit 9544641913440)), (nat_lit 3314, Int.ofNat (nat_lit 18856319074560)), (nat_lit 3315, Int.ofNat (nat_lit 22426001022240)), (nat_lit 3316, Int.ofNat (nat_lit 32125924124064)), (nat_lit 3317, Int.ofNat (nat_lit 42511529440800)), (nat_lit 3329, Int.ofNat (nat_lit 4747785840000)), (nat_lit 3330, Int.ofNat (nat_lit 8318410732800)), (nat_lit 3331, Int.ofNat (nat_lit 9018135302400)), (nat_lit 3332, Int.ofNat (nat_lit 9717859872000))]
theorem block018_data_flat057_step : block018_data_flat057 = (CoefficientMerge.fastMerge block018_data_flat047 block018_data_flat056) := by decide +kernel
theorem block018_data_flat057_original : block018_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13173656115456 : Int) atom1316Coded) (CoefficientMerge.scale (9544641913440 : Int) atom1317Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18856319074560 : Int) atom1318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22426001022240 : Int) atom1319Coded) (CoefficientMerge.scale (32125924124064 : Int) atom1320Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42511529440800 : Int) atom1321Coded) (CoefficientMerge.scale (4747785840000 : Int) atom1322Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8318410732800 : Int) atom1323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9018135302400 : Int) atom1324Coded) (CoefficientMerge.scale (9717859872000 : Int) atom1325Coded))))) := by
  rw [block018_data_flat057_step, block018_data_flat047_original, block018_data_flat056_original]
def block018_data_flat058 : CoefficientMerge.Poly := [(nat_lit 3333, Int.ofNat (nat_lit 17823714742656))]
theorem block018_data_flat058_step : block018_data_flat058 = (CoefficientMerge.scale (17823714742656 : Int) atom1326Coded) := by decide +kernel
theorem block018_data_flat058_original : block018_data_flat058 = (CoefficientMerge.scale (17823714742656 : Int) atom1326Coded) := by
  rw [block018_data_flat058_step]
def block018_data_flat059 : CoefficientMerge.Poly := [(nat_lit 3334, Int.ofNat (nat_lit 15047395107840))]
theorem block018_data_flat059_step : block018_data_flat059 = (CoefficientMerge.scale (15047395107840 : Int) atom1327Coded) := by decide +kernel
theorem block018_data_flat059_original : block018_data_flat059 = (CoefficientMerge.scale (15047395107840 : Int) atom1327Coded) := by
  rw [block018_data_flat059_step]
def block018_data_flat060 : CoefficientMerge.Poly := [(nat_lit 3333, Int.ofNat (nat_lit 17823714742656)), (nat_lit 3334, Int.ofNat (nat_lit 15047395107840))]
theorem block018_data_flat060_step : block018_data_flat060 = (CoefficientMerge.fastMerge block018_data_flat058 block018_data_flat059) := by decide +kernel
theorem block018_data_flat060_original : block018_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17823714742656 : Int) atom1326Coded) (CoefficientMerge.scale (15047395107840 : Int) atom1327Coded)) := by
  rw [block018_data_flat060_step, block018_data_flat058_original, block018_data_flat059_original]
def block018_data_flat061 : CoefficientMerge.Poly := [(nat_lit 3335, Int.ofNat (nat_lit 27687575007360))]
theorem block018_data_flat061_step : block018_data_flat061 = (CoefficientMerge.scale (27687575007360 : Int) atom1328Coded) := by decide +kernel
theorem block018_data_flat061_original : block018_data_flat061 = (CoefficientMerge.scale (27687575007360 : Int) atom1328Coded) := by
  rw [block018_data_flat061_step]
def block018_data_flat062 : CoefficientMerge.Poly := [(nat_lit 3336, Int.ofNat (nat_lit 29300658949440))]
theorem block018_data_flat062_step : block018_data_flat062 = (CoefficientMerge.scale (29300658949440 : Int) atom1329Coded) := by decide +kernel
theorem block018_data_flat062_original : block018_data_flat062 = (CoefficientMerge.scale (29300658949440 : Int) atom1329Coded) := by
  rw [block018_data_flat062_step]
def block018_data_flat063 : CoefficientMerge.Poly := [(nat_lit 3337, Int.ofNat (nat_lit 39568321822464))]
theorem block018_data_flat063_step : block018_data_flat063 = (CoefficientMerge.scale (39568321822464 : Int) atom1330Coded) := by decide +kernel
theorem block018_data_flat063_original : block018_data_flat063 = (CoefficientMerge.scale (39568321822464 : Int) atom1330Coded) := by
  rw [block018_data_flat063_step]
def block018_data_flat064 : CoefficientMerge.Poly := [(nat_lit 3336, Int.ofNat (nat_lit 29300658949440)), (nat_lit 3337, Int.ofNat (nat_lit 39568321822464))]
theorem block018_data_flat064_step : block018_data_flat064 = (CoefficientMerge.fastMerge block018_data_flat062 block018_data_flat063) := by decide +kernel
theorem block018_data_flat064_original : block018_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (29300658949440 : Int) atom1329Coded) (CoefficientMerge.scale (39568321822464 : Int) atom1330Coded)) := by
  rw [block018_data_flat064_step, block018_data_flat062_original, block018_data_flat063_original]
def block018_data_flat065 : CoefficientMerge.Poly := [(nat_lit 3335, Int.ofNat (nat_lit 27687575007360)), (nat_lit 3336, Int.ofNat (nat_lit 29300658949440)), (nat_lit 3337, Int.ofNat (nat_lit 39568321822464))]
theorem block018_data_flat065_step : block018_data_flat065 = (CoefficientMerge.fastMerge block018_data_flat061 block018_data_flat064) := by decide +kernel
theorem block018_data_flat065_original : block018_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27687575007360 : Int) atom1328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29300658949440 : Int) atom1329Coded) (CoefficientMerge.scale (39568321822464 : Int) atom1330Coded))) := by
  rw [block018_data_flat065_step, block018_data_flat061_original, block018_data_flat064_original]
def block018_data_flat066 : CoefficientMerge.Poly := [(nat_lit 3333, Int.ofNat (nat_lit 17823714742656)), (nat_lit 3334, Int.ofNat (nat_lit 15047395107840)), (nat_lit 3335, Int.ofNat (nat_lit 27687575007360)), (nat_lit 3336, Int.ofNat (nat_lit 29300658949440)), (nat_lit 3337, Int.ofNat (nat_lit 39568321822464))]
theorem block018_data_flat066_step : block018_data_flat066 = (CoefficientMerge.fastMerge block018_data_flat060 block018_data_flat065) := by decide +kernel
theorem block018_data_flat066_original : block018_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17823714742656 : Int) atom1326Coded) (CoefficientMerge.scale (15047395107840 : Int) atom1327Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27687575007360 : Int) atom1328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29300658949440 : Int) atom1329Coded) (CoefficientMerge.scale (39568321822464 : Int) atom1330Coded)))) := by
  rw [block018_data_flat066_step, block018_data_flat060_original, block018_data_flat065_original]
def block018_data_flat067 : CoefficientMerge.Poly := [(nat_lit 3338, Int.ofNat (nat_lit 50335348946400))]
theorem block018_data_flat067_step : block018_data_flat067 = (CoefficientMerge.scale (50335348946400 : Int) atom1331Coded) := by decide +kernel
theorem block018_data_flat067_original : block018_data_flat067 = (CoefficientMerge.scale (50335348946400 : Int) atom1331Coded) := by
  rw [block018_data_flat067_step]
def block018_data_flat068 : CoefficientMerge.Poly := [(nat_lit 3351, Int.ofNat (nat_lit 7156230076800))]
theorem block018_data_flat068_step : block018_data_flat068 = (CoefficientMerge.scale (7156230076800 : Int) atom1332Coded) := by decide +kernel
theorem block018_data_flat068_original : block018_data_flat068 = (CoefficientMerge.scale (7156230076800 : Int) atom1332Coded) := by
  rw [block018_data_flat068_step]
def block018_data_flat069 : CoefficientMerge.Poly := [(nat_lit 3338, Int.ofNat (nat_lit 50335348946400)), (nat_lit 3351, Int.ofNat (nat_lit 7156230076800))]
theorem block018_data_flat069_step : block018_data_flat069 = (CoefficientMerge.fastMerge block018_data_flat067 block018_data_flat068) := by decide +kernel
theorem block018_data_flat069_original : block018_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (50335348946400 : Int) atom1331Coded) (CoefficientMerge.scale (7156230076800 : Int) atom1332Coded)) := by
  rw [block018_data_flat069_step, block018_data_flat067_original, block018_data_flat068_original]
def block018_data_flat070 : CoefficientMerge.Poly := [(nat_lit 3352, Int.ofNat (nat_lit 14339521324800))]
theorem block018_data_flat070_step : block018_data_flat070 = (CoefficientMerge.scale (14339521324800 : Int) atom1333Coded) := by decide +kernel
theorem block018_data_flat070_original : block018_data_flat070 = (CoefficientMerge.scale (14339521324800 : Int) atom1333Coded) := by
  rw [block018_data_flat070_step]
def block018_data_flat071 : CoefficientMerge.Poly := [(nat_lit 3353, Int.ofNat (nat_lit 14793762412800))]
theorem block018_data_flat071_step : block018_data_flat071 = (CoefficientMerge.scale (14793762412800 : Int) atom1334Coded) := by decide +kernel
theorem block018_data_flat071_original : block018_data_flat071 = (CoefficientMerge.scale (14793762412800 : Int) atom1334Coded) := by
  rw [block018_data_flat071_step]
def block018_data_flat072 : CoefficientMerge.Poly := [(nat_lit 3354, Int.ofNat (nat_lit 19441485123456))]
theorem block018_data_flat072_step : block018_data_flat072 = (CoefficientMerge.scale (19441485123456 : Int) atom1335Coded) := by decide +kernel
theorem block018_data_flat072_original : block018_data_flat072 = (CoefficientMerge.scale (19441485123456 : Int) atom1335Coded) := by
  rw [block018_data_flat072_step]
def block018_data_flat073 : CoefficientMerge.Poly := [(nat_lit 3353, Int.ofNat (nat_lit 14793762412800)), (nat_lit 3354, Int.ofNat (nat_lit 19441485123456))]
theorem block018_data_flat073_step : block018_data_flat073 = (CoefficientMerge.fastMerge block018_data_flat071 block018_data_flat072) := by decide +kernel
theorem block018_data_flat073_original : block018_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14793762412800 : Int) atom1334Coded) (CoefficientMerge.scale (19441485123456 : Int) atom1335Coded)) := by
  rw [block018_data_flat073_step, block018_data_flat071_original, block018_data_flat072_original]
def block018_data_flat074 : CoefficientMerge.Poly := [(nat_lit 3352, Int.ofNat (nat_lit 14339521324800)), (nat_lit 3353, Int.ofNat (nat_lit 14793762412800)), (nat_lit 3354, Int.ofNat (nat_lit 19441485123456))]
theorem block018_data_flat074_step : block018_data_flat074 = (CoefficientMerge.fastMerge block018_data_flat070 block018_data_flat073) := by decide +kernel
theorem block018_data_flat074_original : block018_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14339521324800 : Int) atom1333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14793762412800 : Int) atom1334Coded) (CoefficientMerge.scale (19441485123456 : Int) atom1335Coded))) := by
  rw [block018_data_flat074_step, block018_data_flat070_original, block018_data_flat073_original]
def block018_data_flat075 : CoefficientMerge.Poly := [(nat_lit 3338, Int.ofNat (nat_lit 50335348946400)), (nat_lit 3351, Int.ofNat (nat_lit 7156230076800)), (nat_lit 3352, Int.ofNat (nat_lit 14339521324800)), (nat_lit 3353, Int.ofNat (nat_lit 14793762412800)), (nat_lit 3354, Int.ofNat (nat_lit 19441485123456))]
theorem block018_data_flat075_step : block018_data_flat075 = (CoefficientMerge.fastMerge block018_data_flat069 block018_data_flat074) := by decide +kernel
theorem block018_data_flat075_original : block018_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50335348946400 : Int) atom1331Coded) (CoefficientMerge.scale (7156230076800 : Int) atom1332Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14339521324800 : Int) atom1333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14793762412800 : Int) atom1334Coded) (CoefficientMerge.scale (19441485123456 : Int) atom1335Coded)))) := by
  rw [block018_data_flat075_step, block018_data_flat069_original, block018_data_flat074_original]
def block018_data_flat076 : CoefficientMerge.Poly := [(nat_lit 3333, Int.ofNat (nat_lit 17823714742656)), (nat_lit 3334, Int.ofNat (nat_lit 15047395107840)), (nat_lit 3335, Int.ofNat (nat_lit 27687575007360)), (nat_lit 3336, Int.ofNat (nat_lit 29300658949440)), (nat_lit 3337, Int.ofNat (nat_lit 39568321822464)), (nat_lit 3338, Int.ofNat (nat_lit 50335348946400)), (nat_lit 3351, Int.ofNat (nat_lit 7156230076800)), (nat_lit 3352, Int.ofNat (nat_lit 14339521324800)), (nat_lit 3353, Int.ofNat (nat_lit 14793762412800)), (nat_lit 3354, Int.ofNat (nat_lit 19441485123456))]
theorem block018_data_flat076_step : block018_data_flat076 = (CoefficientMerge.fastMerge block018_data_flat066 block018_data_flat075) := by decide +kernel
theorem block018_data_flat076_original : block018_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17823714742656 : Int) atom1326Coded) (CoefficientMerge.scale (15047395107840 : Int) atom1327Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27687575007360 : Int) atom1328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29300658949440 : Int) atom1329Coded) (CoefficientMerge.scale (39568321822464 : Int) atom1330Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50335348946400 : Int) atom1331Coded) (CoefficientMerge.scale (7156230076800 : Int) atom1332Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14339521324800 : Int) atom1333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14793762412800 : Int) atom1334Coded) (CoefficientMerge.scale (19441485123456 : Int) atom1335Coded))))) := by
  rw [block018_data_flat076_step, block018_data_flat066_original, block018_data_flat075_original]
def block018_data_flat077 : CoefficientMerge.Poly := [(nat_lit 3312, Int.ofNat (nat_lit 13173656115456)), (nat_lit 3313, Int.ofNat (nat_lit 9544641913440)), (nat_lit 3314, Int.ofNat (nat_lit 18856319074560)), (nat_lit 3315, Int.ofNat (nat_lit 22426001022240)), (nat_lit 3316, Int.ofNat (nat_lit 32125924124064)), (nat_lit 3317, Int.ofNat (nat_lit 42511529440800)), (nat_lit 3329, Int.ofNat (nat_lit 4747785840000)), (nat_lit 3330, Int.ofNat (nat_lit 8318410732800)), (nat_lit 3331, Int.ofNat (nat_lit 9018135302400)), (nat_lit 3332, Int.ofNat (nat_lit 9717859872000)), (nat_lit 3333, Int.ofNat (nat_lit 17823714742656)), (nat_lit 3334, Int.ofNat (nat_lit 15047395107840)), (nat_lit 3335, Int.ofNat (nat_lit 27687575007360)), (nat_lit 3336, Int.ofNat (nat_lit 29300658949440)), (nat_lit 3337, Int.ofNat (nat_lit 39568321822464)), (nat_lit 3338, Int.ofNat (nat_lit 50335348946400)), (nat_lit 3351, Int.ofNat (nat_lit 7156230076800)), (nat_lit 3352, Int.ofNat (nat_lit 14339521324800)), (nat_lit 3353, Int.ofNat (nat_lit 14793762412800)), (nat_lit 3354, Int.ofNat (nat_lit 19441485123456))]
theorem block018_data_flat077_step : block018_data_flat077 = (CoefficientMerge.fastMerge block018_data_flat057 block018_data_flat076) := by decide +kernel
theorem block018_data_flat077_original : block018_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13173656115456 : Int) atom1316Coded) (CoefficientMerge.scale (9544641913440 : Int) atom1317Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18856319074560 : Int) atom1318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22426001022240 : Int) atom1319Coded) (CoefficientMerge.scale (32125924124064 : Int) atom1320Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42511529440800 : Int) atom1321Coded) (CoefficientMerge.scale (4747785840000 : Int) atom1322Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8318410732800 : Int) atom1323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9018135302400 : Int) atom1324Coded) (CoefficientMerge.scale (9717859872000 : Int) atom1325Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17823714742656 : Int) atom1326Coded) (CoefficientMerge.scale (15047395107840 : Int) atom1327Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27687575007360 : Int) atom1328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29300658949440 : Int) atom1329Coded) (CoefficientMerge.scale (39568321822464 : Int) atom1330Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50335348946400 : Int) atom1331Coded) (CoefficientMerge.scale (7156230076800 : Int) atom1332Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14339521324800 : Int) atom1333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14793762412800 : Int) atom1334Coded) (CoefficientMerge.scale (19441485123456 : Int) atom1335Coded)))))) := by
  rw [block018_data_flat077_step, block018_data_flat057_original, block018_data_flat076_original]
def block018_data_flat078 : CoefficientMerge.Poly := [(nat_lit 3270, Int.ofNat (nat_lit 6427474232112)), (nat_lit 3272, Int.ofNat (nat_lit 1510388496720)), (nat_lit 3273, Int.ofNat (nat_lit 5786258284800)), (nat_lit 3274, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3275, Int.ofNat (nat_lit 17391151612800)), (nat_lit 3285, Int.ofNat (nat_lit 896401296000)), (nat_lit 3288, Int.ofNat (nat_lit 686193984000)), (nat_lit 3289, Int.ofNat (nat_lit 1372387968000)), (nat_lit 3290, Int.ofNat (nat_lit 2058581952000)), (nat_lit 3291, Int.ofNat (nat_lit 8185219145856)), (nat_lit 3292, Int.ofNat (nat_lit 3335794446240)), (nat_lit 3293, Int.ofNat (nat_lit 9115747148160)), (nat_lit 3294, Int.ofNat (nat_lit 13951505319840)), (nat_lit 3295, Int.ofNat (nat_lit 22686649344864)), (nat_lit 3296, Int.ofNat (nat_lit 32365160755200)), (nat_lit 3307, Int.ofNat (nat_lit 2262023971200)), (nat_lit 3308, Int.ofNat (nat_lit 3851384544000)), (nat_lit 3309, Int.ofNat (nat_lit 4201246828800)), (nat_lit 3310, Int.ofNat (nat_lit 4978289030400)), (nat_lit 3311, Int.ofNat (nat_lit 5755331232000)), (nat_lit 3312, Int.ofNat (nat_lit 13173656115456)), (nat_lit 3313, Int.ofNat (nat_lit 9544641913440)), (nat_lit 3314, Int.ofNat (nat_lit 18856319074560)), (nat_lit 3315, Int.ofNat (nat_lit 22426001022240)), (nat_lit 3316, Int.ofNat (nat_lit 32125924124064)), (nat_lit 3317, Int.ofNat (nat_lit 42511529440800)), (nat_lit 3329, Int.ofNat (nat_lit 4747785840000)), (nat_lit 3330, Int.ofNat (nat_lit 8318410732800)), (nat_lit 3331, Int.ofNat (nat_lit 9018135302400)), (nat_lit 3332, Int.ofNat (nat_lit 9717859872000)), (nat_lit 3333, Int.ofNat (nat_lit 17823714742656)), (nat_lit 3334, Int.ofNat (nat_lit 15047395107840)), (nat_lit 3335, Int.ofNat (nat_lit 27687575007360)), (nat_lit 3336, Int.ofNat (nat_lit 29300658949440)), (nat_lit 3337, Int.ofNat (nat_lit 39568321822464)), (nat_lit 3338, Int.ofNat (nat_lit 50335348946400)), (nat_lit 3351, Int.ofNat (nat_lit 7156230076800)), (nat_lit 3352, Int.ofNat (nat_lit 14339521324800)), (nat_lit 3353, Int.ofNat (nat_lit 14793762412800)), (nat_lit 3354, Int.ofNat (nat_lit 19441485123456))]
theorem block018_data_flat078_step : block018_data_flat078 = (CoefficientMerge.fastMerge block018_data_flat038 block018_data_flat077) := by decide +kernel
theorem block018_data_flat078_original : block018_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6427474232112 : Int) atom1296Coded) (CoefficientMerge.scale (1510388496720 : Int) atom1297Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1299Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1300Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (896401296000 : Int) atom1301Coded) (CoefficientMerge.scale (686193984000 : Int) atom1302Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1372387968000 : Int) atom1303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2058581952000 : Int) atom1304Coded) (CoefficientMerge.scale (8185219145856 : Int) atom1305Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3335794446240 : Int) atom1306Coded) (CoefficientMerge.scale (9115747148160 : Int) atom1307Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13951505319840 : Int) atom1308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22686649344864 : Int) atom1309Coded) (CoefficientMerge.scale (32365160755200 : Int) atom1310Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2262023971200 : Int) atom1311Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1312Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4201246828800 : Int) atom1313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4978289030400 : Int) atom1314Coded) (CoefficientMerge.scale (5755331232000 : Int) atom1315Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13173656115456 : Int) atom1316Coded) (CoefficientMerge.scale (9544641913440 : Int) atom1317Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18856319074560 : Int) atom1318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22426001022240 : Int) atom1319Coded) (CoefficientMerge.scale (32125924124064 : Int) atom1320Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42511529440800 : Int) atom1321Coded) (CoefficientMerge.scale (4747785840000 : Int) atom1322Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8318410732800 : Int) atom1323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9018135302400 : Int) atom1324Coded) (CoefficientMerge.scale (9717859872000 : Int) atom1325Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17823714742656 : Int) atom1326Coded) (CoefficientMerge.scale (15047395107840 : Int) atom1327Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27687575007360 : Int) atom1328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29300658949440 : Int) atom1329Coded) (CoefficientMerge.scale (39568321822464 : Int) atom1330Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50335348946400 : Int) atom1331Coded) (CoefficientMerge.scale (7156230076800 : Int) atom1332Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14339521324800 : Int) atom1333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14793762412800 : Int) atom1334Coded) (CoefficientMerge.scale (19441485123456 : Int) atom1335Coded))))))) := by
  rw [block018_data_flat078_step, block018_data_flat038_original, block018_data_flat077_original]
def block018_data_flat079 : CoefficientMerge.Poly := [(nat_lit 3355, Int.ofNat (nat_lit 19397114109440))]
theorem block018_data_flat079_step : block018_data_flat079 = (CoefficientMerge.scale (19397114109440 : Int) atom1336Coded) := by decide +kernel
theorem block018_data_flat079_original : block018_data_flat079 = (CoefficientMerge.scale (19397114109440 : Int) atom1336Coded) := by
  rw [block018_data_flat079_step]
def block018_data_flat080 : CoefficientMerge.Poly := [(nat_lit 3356, Int.ofNat (nat_lit 31352906629760))]
theorem block018_data_flat080_step : block018_data_flat080 = (CoefficientMerge.scale (31352906629760 : Int) atom1337Coded) := by decide +kernel
theorem block018_data_flat080_original : block018_data_flat080 = (CoefficientMerge.scale (31352906629760 : Int) atom1337Coded) := by
  rw [block018_data_flat080_step]
def block018_data_flat081 : CoefficientMerge.Poly := [(nat_lit 3355, Int.ofNat (nat_lit 19397114109440)), (nat_lit 3356, Int.ofNat (nat_lit 31352906629760))]
theorem block018_data_flat081_step : block018_data_flat081 = (CoefficientMerge.fastMerge block018_data_flat079 block018_data_flat080) := by decide +kernel
theorem block018_data_flat081_original : block018_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19397114109440 : Int) atom1336Coded) (CoefficientMerge.scale (31352906629760 : Int) atom1337Coded)) := by
  rw [block018_data_flat081_step, block018_data_flat079_original, block018_data_flat080_original]
def block018_data_flat082 : CoefficientMerge.Poly := [(nat_lit 3357, Int.ofNat (nat_lit 34150544280640))]
theorem block018_data_flat082_step : block018_data_flat082 = (CoefficientMerge.scale (34150544280640 : Int) atom1338Coded) := by decide +kernel
theorem block018_data_flat082_original : block018_data_flat082 = (CoefficientMerge.scale (34150544280640 : Int) atom1338Coded) := by
  rw [block018_data_flat082_step]
def block018_data_flat083 : CoefficientMerge.Poly := [(nat_lit 3358, Int.ofNat (nat_lit 43898083947264))]
theorem block018_data_flat083_step : block018_data_flat083 = (CoefficientMerge.scale (43898083947264 : Int) atom1339Coded) := by decide +kernel
theorem block018_data_flat083_original : block018_data_flat083 = (CoefficientMerge.scale (43898083947264 : Int) atom1339Coded) := by
  rw [block018_data_flat083_step]
def block018_data_flat084 : CoefficientMerge.Poly := [(nat_lit 3359, Int.ofNat (nat_lit 54883075413600))]
theorem block018_data_flat084_step : block018_data_flat084 = (CoefficientMerge.scale (54883075413600 : Int) atom1340Coded) := by decide +kernel
theorem block018_data_flat084_original : block018_data_flat084 = (CoefficientMerge.scale (54883075413600 : Int) atom1340Coded) := by
  rw [block018_data_flat084_step]
def block018_data_flat085 : CoefficientMerge.Poly := [(nat_lit 3358, Int.ofNat (nat_lit 43898083947264)), (nat_lit 3359, Int.ofNat (nat_lit 54883075413600))]
theorem block018_data_flat085_step : block018_data_flat085 = (CoefficientMerge.fastMerge block018_data_flat083 block018_data_flat084) := by decide +kernel
theorem block018_data_flat085_original : block018_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (43898083947264 : Int) atom1339Coded) (CoefficientMerge.scale (54883075413600 : Int) atom1340Coded)) := by
  rw [block018_data_flat085_step, block018_data_flat083_original, block018_data_flat084_original]
def block018_data_flat086 : CoefficientMerge.Poly := [(nat_lit 3357, Int.ofNat (nat_lit 34150544280640)), (nat_lit 3358, Int.ofNat (nat_lit 43898083947264)), (nat_lit 3359, Int.ofNat (nat_lit 54883075413600))]
theorem block018_data_flat086_step : block018_data_flat086 = (CoefficientMerge.fastMerge block018_data_flat082 block018_data_flat085) := by decide +kernel
theorem block018_data_flat086_original : block018_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34150544280640 : Int) atom1338Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43898083947264 : Int) atom1339Coded) (CoefficientMerge.scale (54883075413600 : Int) atom1340Coded))) := by
  rw [block018_data_flat086_step, block018_data_flat082_original, block018_data_flat085_original]
def block018_data_flat087 : CoefficientMerge.Poly := [(nat_lit 3355, Int.ofNat (nat_lit 19397114109440)), (nat_lit 3356, Int.ofNat (nat_lit 31352906629760)), (nat_lit 3357, Int.ofNat (nat_lit 34150544280640)), (nat_lit 3358, Int.ofNat (nat_lit 43898083947264)), (nat_lit 3359, Int.ofNat (nat_lit 54883075413600))]
theorem block018_data_flat087_step : block018_data_flat087 = (CoefficientMerge.fastMerge block018_data_flat081 block018_data_flat086) := by decide +kernel
theorem block018_data_flat087_original : block018_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19397114109440 : Int) atom1336Coded) (CoefficientMerge.scale (31352906629760 : Int) atom1337Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34150544280640 : Int) atom1338Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43898083947264 : Int) atom1339Coded) (CoefficientMerge.scale (54883075413600 : Int) atom1340Coded)))) := by
  rw [block018_data_flat087_step, block018_data_flat081_original, block018_data_flat086_original]
def block018_data_flat088 : CoefficientMerge.Poly := [(nat_lit 3373, Int.ofNat (nat_lit 10477390550400))]
theorem block018_data_flat088_step : block018_data_flat088 = (CoefficientMerge.scale (10477390550400 : Int) atom1341Coded) := by decide +kernel
theorem block018_data_flat088_original : block018_data_flat088 = (CoefficientMerge.scale (10477390550400 : Int) atom1341Coded) := by
  rw [block018_data_flat088_step]
def block018_data_flat089 : CoefficientMerge.Poly := [(nat_lit 3374, Int.ofNat (nat_lit 19824839136000))]
theorem block018_data_flat089_step : block018_data_flat089 = (CoefficientMerge.scale (19824839136000 : Int) atom1342Coded) := by decide +kernel
theorem block018_data_flat089_original : block018_data_flat089 = (CoefficientMerge.scale (19824839136000 : Int) atom1342Coded) := by
  rw [block018_data_flat089_step]
def block018_data_flat090 : CoefficientMerge.Poly := [(nat_lit 3373, Int.ofNat (nat_lit 10477390550400)), (nat_lit 3374, Int.ofNat (nat_lit 19824839136000))]
theorem block018_data_flat090_step : block018_data_flat090 = (CoefficientMerge.fastMerge block018_data_flat088 block018_data_flat089) := by decide +kernel
theorem block018_data_flat090_original : block018_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10477390550400 : Int) atom1341Coded) (CoefficientMerge.scale (19824839136000 : Int) atom1342Coded)) := by
  rw [block018_data_flat090_step, block018_data_flat088_original, block018_data_flat089_original]
def block018_data_flat091 : CoefficientMerge.Poly := [(nat_lit 3375, Int.ofNat (nat_lit 24472903179456))]
theorem block018_data_flat091_step : block018_data_flat091 = (CoefficientMerge.scale (24472903179456 : Int) atom1343Coded) := by decide +kernel
theorem block018_data_flat091_original : block018_data_flat091 = (CoefficientMerge.scale (24472903179456 : Int) atom1343Coded) := by
  rw [block018_data_flat091_step]
def block018_data_flat092 : CoefficientMerge.Poly := [(nat_lit 3376, Int.ofNat (nat_lit 24292870914240))]
theorem block018_data_flat092_step : block018_data_flat092 = (CoefficientMerge.scale (24292870914240 : Int) atom1344Coded) := by decide +kernel
theorem block018_data_flat092_original : block018_data_flat092 = (CoefficientMerge.scale (24292870914240 : Int) atom1344Coded) := by
  rw [block018_data_flat092_step]
def block018_data_flat093 : CoefficientMerge.Poly := [(nat_lit 3377, Int.ofNat (nat_lit 39375935372160))]
theorem block018_data_flat093_step : block018_data_flat093 = (CoefficientMerge.scale (39375935372160 : Int) atom1345Coded) := by decide +kernel
theorem block018_data_flat093_original : block018_data_flat093 = (CoefficientMerge.scale (39375935372160 : Int) atom1345Coded) := by
  rw [block018_data_flat093_step]
def block018_data_flat094 : CoefficientMerge.Poly := [(nat_lit 3376, Int.ofNat (nat_lit 24292870914240)), (nat_lit 3377, Int.ofNat (nat_lit 39375935372160))]
theorem block018_data_flat094_step : block018_data_flat094 = (CoefficientMerge.fastMerge block018_data_flat092 block018_data_flat093) := by decide +kernel
theorem block018_data_flat094_original : block018_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24292870914240 : Int) atom1344Coded) (CoefficientMerge.scale (39375935372160 : Int) atom1345Coded)) := by
  rw [block018_data_flat094_step, block018_data_flat092_original, block018_data_flat093_original]
def block018_data_flat095 : CoefficientMerge.Poly := [(nat_lit 3375, Int.ofNat (nat_lit 24472903179456)), (nat_lit 3376, Int.ofNat (nat_lit 24292870914240)), (nat_lit 3377, Int.ofNat (nat_lit 39375935372160))]
theorem block018_data_flat095_step : block018_data_flat095 = (CoefficientMerge.fastMerge block018_data_flat091 block018_data_flat094) := by decide +kernel
theorem block018_data_flat095_original : block018_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24472903179456 : Int) atom1343Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24292870914240 : Int) atom1344Coded) (CoefficientMerge.scale (39375935372160 : Int) atom1345Coded))) := by
  rw [block018_data_flat095_step, block018_data_flat091_original, block018_data_flat094_original]
def block018_data_flat096 : CoefficientMerge.Poly := [(nat_lit 3373, Int.ofNat (nat_lit 10477390550400)), (nat_lit 3374, Int.ofNat (nat_lit 19824839136000)), (nat_lit 3375, Int.ofNat (nat_lit 24472903179456)), (nat_lit 3376, Int.ofNat (nat_lit 24292870914240)), (nat_lit 3377, Int.ofNat (nat_lit 39375935372160))]
theorem block018_data_flat096_step : block018_data_flat096 = (CoefficientMerge.fastMerge block018_data_flat090 block018_data_flat095) := by decide +kernel
theorem block018_data_flat096_original : block018_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10477390550400 : Int) atom1341Coded) (CoefficientMerge.scale (19824839136000 : Int) atom1342Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24472903179456 : Int) atom1343Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24292870914240 : Int) atom1344Coded) (CoefficientMerge.scale (39375935372160 : Int) atom1345Coded)))) := by
  rw [block018_data_flat096_step, block018_data_flat090_original, block018_data_flat095_original]
def block018_data_flat097 : CoefficientMerge.Poly := [(nat_lit 3355, Int.ofNat (nat_lit 19397114109440)), (nat_lit 3356, Int.ofNat (nat_lit 31352906629760)), (nat_lit 3357, Int.ofNat (nat_lit 34150544280640)), (nat_lit 3358, Int.ofNat (nat_lit 43898083947264)), (nat_lit 3359, Int.ofNat (nat_lit 54883075413600)), (nat_lit 3373, Int.ofNat (nat_lit 10477390550400)), (nat_lit 3374, Int.ofNat (nat_lit 19824839136000)), (nat_lit 3375, Int.ofNat (nat_lit 24472903179456)), (nat_lit 3376, Int.ofNat (nat_lit 24292870914240)), (nat_lit 3377, Int.ofNat (nat_lit 39375935372160))]
theorem block018_data_flat097_step : block018_data_flat097 = (CoefficientMerge.fastMerge block018_data_flat087 block018_data_flat096) := by decide +kernel
theorem block018_data_flat097_original : block018_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19397114109440 : Int) atom1336Coded) (CoefficientMerge.scale (31352906629760 : Int) atom1337Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34150544280640 : Int) atom1338Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43898083947264 : Int) atom1339Coded) (CoefficientMerge.scale (54883075413600 : Int) atom1340Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10477390550400 : Int) atom1341Coded) (CoefficientMerge.scale (19824839136000 : Int) atom1342Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24472903179456 : Int) atom1343Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24292870914240 : Int) atom1344Coded) (CoefficientMerge.scale (39375935372160 : Int) atom1345Coded))))) := by
  rw [block018_data_flat097_step, block018_data_flat087_original, block018_data_flat096_original]
def block018_data_flat098 : CoefficientMerge.Poly := [(nat_lit 3378, Int.ofNat (nat_lit 43793896443840))]
theorem block018_data_flat098_step : block018_data_flat098 = (CoefficientMerge.scale (43793896443840 : Int) atom1346Coded) := by decide +kernel
theorem block018_data_flat098_original : block018_data_flat098 = (CoefficientMerge.scale (43793896443840 : Int) atom1346Coded) := by
  rw [block018_data_flat098_step]
def block018_data_flat099 : CoefficientMerge.Poly := [(nat_lit 3379, Int.ofNat (nat_lit 47292853414464))]
theorem block018_data_flat099_step : block018_data_flat099 = (CoefficientMerge.scale (47292853414464 : Int) atom1347Coded) := by decide +kernel
theorem block018_data_flat099_original : block018_data_flat099 = (CoefficientMerge.scale (47292853414464 : Int) atom1347Coded) := by
  rw [block018_data_flat099_step]
def block018_data_flat100 : CoefficientMerge.Poly := [(nat_lit 3378, Int.ofNat (nat_lit 43793896443840)), (nat_lit 3379, Int.ofNat (nat_lit 47292853414464))]
theorem block018_data_flat100_step : block018_data_flat100 = (CoefficientMerge.fastMerge block018_data_flat098 block018_data_flat099) := by decide +kernel
theorem block018_data_flat100_original : block018_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (43793896443840 : Int) atom1346Coded) (CoefficientMerge.scale (47292853414464 : Int) atom1347Coded)) := by
  rw [block018_data_flat100_step, block018_data_flat098_original, block018_data_flat099_original]
def block018_data_flat101 : CoefficientMerge.Poly := [(nat_lit 3380, Int.ofNat (nat_lit 64416097821600))]
theorem block018_data_flat101_step : block018_data_flat101 = (CoefficientMerge.scale (64416097821600 : Int) atom1348Coded) := by decide +kernel
theorem block018_data_flat101_original : block018_data_flat101 = (CoefficientMerge.scale (64416097821600 : Int) atom1348Coded) := by
  rw [block018_data_flat101_step]
def block018_data_flat102 : CoefficientMerge.Poly := [(nat_lit 3395, Int.ofNat (nat_lit 14909899939200))]
theorem block018_data_flat102_step : block018_data_flat102 = (CoefficientMerge.scale (14909899939200 : Int) atom1349Coded) := by decide +kernel
theorem block018_data_flat102_original : block018_data_flat102 = (CoefficientMerge.scale (14909899939200 : Int) atom1349Coded) := by
  rw [block018_data_flat102_step]
def block018_data_flat103 : CoefficientMerge.Poly := [(nat_lit 3396, Int.ofNat (nat_lit 29392479133056))]
theorem block018_data_flat103_step : block018_data_flat103 = (CoefficientMerge.scale (29392479133056 : Int) atom1350Coded) := by decide +kernel
theorem block018_data_flat103_original : block018_data_flat103 = (CoefficientMerge.scale (29392479133056 : Int) atom1350Coded) := by
  rw [block018_data_flat103_step]
def block018_data_flat104 : CoefficientMerge.Poly := [(nat_lit 3395, Int.ofNat (nat_lit 14909899939200)), (nat_lit 3396, Int.ofNat (nat_lit 29392479133056))]
theorem block018_data_flat104_step : block018_data_flat104 = (CoefficientMerge.fastMerge block018_data_flat102 block018_data_flat103) := by decide +kernel
theorem block018_data_flat104_original : block018_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14909899939200 : Int) atom1349Coded) (CoefficientMerge.scale (29392479133056 : Int) atom1350Coded)) := by
  rw [block018_data_flat104_step, block018_data_flat102_original, block018_data_flat103_original]
def block018_data_flat105 : CoefficientMerge.Poly := [(nat_lit 3380, Int.ofNat (nat_lit 64416097821600)), (nat_lit 3395, Int.ofNat (nat_lit 14909899939200)), (nat_lit 3396, Int.ofNat (nat_lit 29392479133056))]
theorem block018_data_flat105_step : block018_data_flat105 = (CoefficientMerge.fastMerge block018_data_flat101 block018_data_flat104) := by decide +kernel
theorem block018_data_flat105_original : block018_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (64416097821600 : Int) atom1348Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14909899939200 : Int) atom1349Coded) (CoefficientMerge.scale (29392479133056 : Int) atom1350Coded))) := by
  rw [block018_data_flat105_step, block018_data_flat101_original, block018_data_flat104_original]
def block018_data_flat106 : CoefficientMerge.Poly := [(nat_lit 3378, Int.ofNat (nat_lit 43793896443840)), (nat_lit 3379, Int.ofNat (nat_lit 47292853414464)), (nat_lit 3380, Int.ofNat (nat_lit 64416097821600)), (nat_lit 3395, Int.ofNat (nat_lit 14909899939200)), (nat_lit 3396, Int.ofNat (nat_lit 29392479133056))]
theorem block018_data_flat106_step : block018_data_flat106 = (CoefficientMerge.fastMerge block018_data_flat100 block018_data_flat105) := by decide +kernel
theorem block018_data_flat106_original : block018_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43793896443840 : Int) atom1346Coded) (CoefficientMerge.scale (47292853414464 : Int) atom1347Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64416097821600 : Int) atom1348Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14909899939200 : Int) atom1349Coded) (CoefficientMerge.scale (29392479133056 : Int) atom1350Coded)))) := by
  rw [block018_data_flat106_step, block018_data_flat100_original, block018_data_flat105_original]
def block018_data_flat107 : CoefficientMerge.Poly := [(nat_lit 3397, Int.ofNat (nat_lit 29069478282240))]
theorem block018_data_flat107_step : block018_data_flat107 = (CoefficientMerge.scale (29069478282240 : Int) atom1351Coded) := by decide +kernel
theorem block018_data_flat107_original : block018_data_flat107 = (CoefficientMerge.scale (29069478282240 : Int) atom1351Coded) := by
  rw [block018_data_flat107_step]
def block018_data_flat108 : CoefficientMerge.Poly := [(nat_lit 3398, Int.ofNat (nat_lit 49592493970560))]
theorem block018_data_flat108_step : block018_data_flat108 = (CoefficientMerge.scale (49592493970560 : Int) atom1352Coded) := by decide +kernel
theorem block018_data_flat108_original : block018_data_flat108 = (CoefficientMerge.scale (49592493970560 : Int) atom1352Coded) := by
  rw [block018_data_flat108_step]
def block018_data_flat109 : CoefficientMerge.Poly := [(nat_lit 3397, Int.ofNat (nat_lit 29069478282240)), (nat_lit 3398, Int.ofNat (nat_lit 49592493970560))]
theorem block018_data_flat109_step : block018_data_flat109 = (CoefficientMerge.fastMerge block018_data_flat107 block018_data_flat108) := by decide +kernel
theorem block018_data_flat109_original : block018_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (29069478282240 : Int) atom1351Coded) (CoefficientMerge.scale (49592493970560 : Int) atom1352Coded)) := by
  rw [block018_data_flat109_step, block018_data_flat107_original, block018_data_flat108_original]
def block018_data_flat110 : CoefficientMerge.Poly := [(nat_lit 3399, Int.ofNat (nat_lit 55850131448640))]
theorem block018_data_flat110_step : block018_data_flat110 = (CoefficientMerge.scale (55850131448640 : Int) atom1353Coded) := by decide +kernel
theorem block018_data_flat110_original : block018_data_flat110 = (CoefficientMerge.scale (55850131448640 : Int) atom1353Coded) := by
  rw [block018_data_flat110_step]
def block018_data_flat111 : CoefficientMerge.Poly := [(nat_lit 3400, Int.ofNat (nat_lit 55138349470464))]
theorem block018_data_flat111_step : block018_data_flat111 = (CoefficientMerge.scale (55138349470464 : Int) atom1354Coded) := by decide +kernel
theorem block018_data_flat111_original : block018_data_flat111 = (CoefficientMerge.scale (55138349470464 : Int) atom1354Coded) := by
  rw [block018_data_flat111_step]
def block018_data_flat112 : CoefficientMerge.Poly := [(nat_lit 3401, Int.ofNat (nat_lit 78532122866400))]
theorem block018_data_flat112_step : block018_data_flat112 = (CoefficientMerge.scale (78532122866400 : Int) atom1355Coded) := by decide +kernel
theorem block018_data_flat112_original : block018_data_flat112 = (CoefficientMerge.scale (78532122866400 : Int) atom1355Coded) := by
  rw [block018_data_flat112_step]
def block018_data_flat113 : CoefficientMerge.Poly := [(nat_lit 3400, Int.ofNat (nat_lit 55138349470464)), (nat_lit 3401, Int.ofNat (nat_lit 78532122866400))]
theorem block018_data_flat113_step : block018_data_flat113 = (CoefficientMerge.fastMerge block018_data_flat111 block018_data_flat112) := by decide +kernel
theorem block018_data_flat113_original : block018_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (55138349470464 : Int) atom1354Coded) (CoefficientMerge.scale (78532122866400 : Int) atom1355Coded)) := by
  rw [block018_data_flat113_step, block018_data_flat111_original, block018_data_flat112_original]
def block018_data_flat114 : CoefficientMerge.Poly := [(nat_lit 3399, Int.ofNat (nat_lit 55850131448640)), (nat_lit 3400, Int.ofNat (nat_lit 55138349470464)), (nat_lit 3401, Int.ofNat (nat_lit 78532122866400))]
theorem block018_data_flat114_step : block018_data_flat114 = (CoefficientMerge.fastMerge block018_data_flat110 block018_data_flat113) := by decide +kernel
theorem block018_data_flat114_original : block018_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (55850131448640 : Int) atom1353Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55138349470464 : Int) atom1354Coded) (CoefficientMerge.scale (78532122866400 : Int) atom1355Coded))) := by
  rw [block018_data_flat114_step, block018_data_flat110_original, block018_data_flat113_original]
def block018_data_flat115 : CoefficientMerge.Poly := [(nat_lit 3397, Int.ofNat (nat_lit 29069478282240)), (nat_lit 3398, Int.ofNat (nat_lit 49592493970560)), (nat_lit 3399, Int.ofNat (nat_lit 55850131448640)), (nat_lit 3400, Int.ofNat (nat_lit 55138349470464)), (nat_lit 3401, Int.ofNat (nat_lit 78532122866400))]
theorem block018_data_flat115_step : block018_data_flat115 = (CoefficientMerge.fastMerge block018_data_flat109 block018_data_flat114) := by decide +kernel
theorem block018_data_flat115_original : block018_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29069478282240 : Int) atom1351Coded) (CoefficientMerge.scale (49592493970560 : Int) atom1352Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55850131448640 : Int) atom1353Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55138349470464 : Int) atom1354Coded) (CoefficientMerge.scale (78532122866400 : Int) atom1355Coded)))) := by
  rw [block018_data_flat115_step, block018_data_flat109_original, block018_data_flat114_original]
def block018_data_flat116 : CoefficientMerge.Poly := [(nat_lit 3378, Int.ofNat (nat_lit 43793896443840)), (nat_lit 3379, Int.ofNat (nat_lit 47292853414464)), (nat_lit 3380, Int.ofNat (nat_lit 64416097821600)), (nat_lit 3395, Int.ofNat (nat_lit 14909899939200)), (nat_lit 3396, Int.ofNat (nat_lit 29392479133056)), (nat_lit 3397, Int.ofNat (nat_lit 29069478282240)), (nat_lit 3398, Int.ofNat (nat_lit 49592493970560)), (nat_lit 3399, Int.ofNat (nat_lit 55850131448640)), (nat_lit 3400, Int.ofNat (nat_lit 55138349470464)), (nat_lit 3401, Int.ofNat (nat_lit 78532122866400))]
theorem block018_data_flat116_step : block018_data_flat116 = (CoefficientMerge.fastMerge block018_data_flat106 block018_data_flat115) := by decide +kernel
theorem block018_data_flat116_original : block018_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43793896443840 : Int) atom1346Coded) (CoefficientMerge.scale (47292853414464 : Int) atom1347Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64416097821600 : Int) atom1348Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14909899939200 : Int) atom1349Coded) (CoefficientMerge.scale (29392479133056 : Int) atom1350Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29069478282240 : Int) atom1351Coded) (CoefficientMerge.scale (49592493970560 : Int) atom1352Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55850131448640 : Int) atom1353Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55138349470464 : Int) atom1354Coded) (CoefficientMerge.scale (78532122866400 : Int) atom1355Coded))))) := by
  rw [block018_data_flat116_step, block018_data_flat106_original, block018_data_flat115_original]
def block018_data_flat117 : CoefficientMerge.Poly := [(nat_lit 3355, Int.ofNat (nat_lit 19397114109440)), (nat_lit 3356, Int.ofNat (nat_lit 31352906629760)), (nat_lit 3357, Int.ofNat (nat_lit 34150544280640)), (nat_lit 3358, Int.ofNat (nat_lit 43898083947264)), (nat_lit 3359, Int.ofNat (nat_lit 54883075413600)), (nat_lit 3373, Int.ofNat (nat_lit 10477390550400)), (nat_lit 3374, Int.ofNat (nat_lit 19824839136000)), (nat_lit 3375, Int.ofNat (nat_lit 24472903179456)), (nat_lit 3376, Int.ofNat (nat_lit 24292870914240)), (nat_lit 3377, Int.ofNat (nat_lit 39375935372160)), (nat_lit 3378, Int.ofNat (nat_lit 43793896443840)), (nat_lit 3379, Int.ofNat (nat_lit 47292853414464)), (nat_lit 3380, Int.ofNat (nat_lit 64416097821600)), (nat_lit 3395, Int.ofNat (nat_lit 14909899939200)), (nat_lit 3396, Int.ofNat (nat_lit 29392479133056)), (nat_lit 3397, Int.ofNat (nat_lit 29069478282240)), (nat_lit 3398, Int.ofNat (nat_lit 49592493970560)), (nat_lit 3399, Int.ofNat (nat_lit 55850131448640)), (nat_lit 3400, Int.ofNat (nat_lit 55138349470464)), (nat_lit 3401, Int.ofNat (nat_lit 78532122866400))]
theorem block018_data_flat117_step : block018_data_flat117 = (CoefficientMerge.fastMerge block018_data_flat097 block018_data_flat116) := by decide +kernel
theorem block018_data_flat117_original : block018_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19397114109440 : Int) atom1336Coded) (CoefficientMerge.scale (31352906629760 : Int) atom1337Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34150544280640 : Int) atom1338Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43898083947264 : Int) atom1339Coded) (CoefficientMerge.scale (54883075413600 : Int) atom1340Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10477390550400 : Int) atom1341Coded) (CoefficientMerge.scale (19824839136000 : Int) atom1342Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24472903179456 : Int) atom1343Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24292870914240 : Int) atom1344Coded) (CoefficientMerge.scale (39375935372160 : Int) atom1345Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43793896443840 : Int) atom1346Coded) (CoefficientMerge.scale (47292853414464 : Int) atom1347Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64416097821600 : Int) atom1348Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14909899939200 : Int) atom1349Coded) (CoefficientMerge.scale (29392479133056 : Int) atom1350Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29069478282240 : Int) atom1351Coded) (CoefficientMerge.scale (49592493970560 : Int) atom1352Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55850131448640 : Int) atom1353Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55138349470464 : Int) atom1354Coded) (CoefficientMerge.scale (78532122866400 : Int) atom1355Coded)))))) := by
  rw [block018_data_flat117_step, block018_data_flat097_original, block018_data_flat116_original]
def block018_data_flat118 : CoefficientMerge.Poly := [(nat_lit 3417, Int.ofNat (nat_lit 21896742731904))]
theorem block018_data_flat118_step : block018_data_flat118 = (CoefficientMerge.scale (21896742731904 : Int) atom1356Coded) := by decide +kernel
theorem block018_data_flat118_original : block018_data_flat118 = (CoefficientMerge.scale (21896742731904 : Int) atom1356Coded) := by
  rw [block018_data_flat118_step]
def block018_data_flat119 : CoefficientMerge.Poly := [(nat_lit 3418, Int.ofNat (nat_lit 42928095901824))]
theorem block018_data_flat119_step : block018_data_flat119 = (CoefficientMerge.scale (42928095901824 : Int) atom1357Coded) := by decide +kernel
theorem block018_data_flat119_original : block018_data_flat119 = (CoefficientMerge.scale (42928095901824 : Int) atom1357Coded) := by
  rw [block018_data_flat119_step]
def block018_data_flat120 : CoefficientMerge.Poly := [(nat_lit 3417, Int.ofNat (nat_lit 21896742731904)), (nat_lit 3418, Int.ofNat (nat_lit 42928095901824))]
theorem block018_data_flat120_step : block018_data_flat120 = (CoefficientMerge.fastMerge block018_data_flat118 block018_data_flat119) := by decide +kernel
theorem block018_data_flat120_original : block018_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21896742731904 : Int) atom1356Coded) (CoefficientMerge.scale (42928095901824 : Int) atom1357Coded)) := by
  rw [block018_data_flat120_step, block018_data_flat118_original, block018_data_flat119_original]
def block018_data_flat121 : CoefficientMerge.Poly := [(nat_lit 3419, Int.ofNat (nat_lit 68414874110208))]
theorem block018_data_flat121_step : block018_data_flat121 = (CoefficientMerge.scale (68414874110208 : Int) atom1358Coded) := by decide +kernel
theorem block018_data_flat121_original : block018_data_flat121 = (CoefficientMerge.scale (68414874110208 : Int) atom1358Coded) := by
  rw [block018_data_flat121_step]
def block018_data_flat122 : CoefficientMerge.Poly := [(nat_lit 3420, Int.ofNat (nat_lit 71594005599360))]
theorem block018_data_flat122_step : block018_data_flat122 = (CoefficientMerge.scale (71594005599360 : Int) atom1359Coded) := by decide +kernel
theorem block018_data_flat122_original : block018_data_flat122 = (CoefficientMerge.scale (71594005599360 : Int) atom1359Coded) := by
  rw [block018_data_flat122_step]
def block018_data_flat123 : CoefficientMerge.Poly := [(nat_lit 3421, Int.ofNat (nat_lit 53238031188480))]
theorem block018_data_flat123_step : block018_data_flat123 = (CoefficientMerge.scale (53238031188480 : Int) atom1360Coded) := by decide +kernel
theorem block018_data_flat123_original : block018_data_flat123 = (CoefficientMerge.scale (53238031188480 : Int) atom1360Coded) := by
  rw [block018_data_flat123_step]
def block018_data_flat124 : CoefficientMerge.Poly := [(nat_lit 3420, Int.ofNat (nat_lit 71594005599360)), (nat_lit 3421, Int.ofNat (nat_lit 53238031188480))]
theorem block018_data_flat124_step : block018_data_flat124 = (CoefficientMerge.fastMerge block018_data_flat122 block018_data_flat123) := by decide +kernel
theorem block018_data_flat124_original : block018_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (71594005599360 : Int) atom1359Coded) (CoefficientMerge.scale (53238031188480 : Int) atom1360Coded)) := by
  rw [block018_data_flat124_step, block018_data_flat122_original, block018_data_flat123_original]
def block018_data_flat125 : CoefficientMerge.Poly := [(nat_lit 3419, Int.ofNat (nat_lit 68414874110208)), (nat_lit 3420, Int.ofNat (nat_lit 71594005599360)), (nat_lit 3421, Int.ofNat (nat_lit 53238031188480))]
theorem block018_data_flat125_step : block018_data_flat125 = (CoefficientMerge.fastMerge block018_data_flat121 block018_data_flat124) := by decide +kernel
theorem block018_data_flat125_original : block018_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (68414874110208 : Int) atom1358Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71594005599360 : Int) atom1359Coded) (CoefficientMerge.scale (53238031188480 : Int) atom1360Coded))) := by
  rw [block018_data_flat125_step, block018_data_flat121_original, block018_data_flat124_original]
def block018_data_flat126 : CoefficientMerge.Poly := [(nat_lit 3417, Int.ofNat (nat_lit 21896742731904)), (nat_lit 3418, Int.ofNat (nat_lit 42928095901824)), (nat_lit 3419, Int.ofNat (nat_lit 68414874110208)), (nat_lit 3420, Int.ofNat (nat_lit 71594005599360)), (nat_lit 3421, Int.ofNat (nat_lit 53238031188480))]
theorem block018_data_flat126_step : block018_data_flat126 = (CoefficientMerge.fastMerge block018_data_flat120 block018_data_flat125) := by decide +kernel
theorem block018_data_flat126_original : block018_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21896742731904 : Int) atom1356Coded) (CoefficientMerge.scale (42928095901824 : Int) atom1357Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68414874110208 : Int) atom1358Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71594005599360 : Int) atom1359Coded) (CoefficientMerge.scale (53238031188480 : Int) atom1360Coded)))) := by
  rw [block018_data_flat126_step, block018_data_flat120_original, block018_data_flat125_original]
def block018_data_flat127 : CoefficientMerge.Poly := [(nat_lit 3422, Int.ofNat (nat_lit 80901900693504))]
theorem block018_data_flat127_step : block018_data_flat127 = (CoefficientMerge.scale (80901900693504 : Int) atom1361Coded) := by decide +kernel
theorem block018_data_flat127_original : block018_data_flat127 = (CoefficientMerge.scale (80901900693504 : Int) atom1361Coded) := by
  rw [block018_data_flat127_step]
def block018_data_flat128 : CoefficientMerge.Poly := [(nat_lit 3439, Int.ofNat (nat_lit 17225211406464))]
theorem block018_data_flat128_step : block018_data_flat128 = (CoefficientMerge.scale (17225211406464 : Int) atom1362Coded) := by decide +kernel
theorem block018_data_flat128_original : block018_data_flat128 = (CoefficientMerge.scale (17225211406464 : Int) atom1362Coded) := by
  rw [block018_data_flat128_step]
def block018_data_flat129 : CoefficientMerge.Poly := [(nat_lit 3422, Int.ofNat (nat_lit 80901900693504)), (nat_lit 3439, Int.ofNat (nat_lit 17225211406464))]
theorem block018_data_flat129_step : block018_data_flat129 = (CoefficientMerge.fastMerge block018_data_flat127 block018_data_flat128) := by decide +kernel
theorem block018_data_flat129_original : block018_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (80901900693504 : Int) atom1361Coded) (CoefficientMerge.scale (17225211406464 : Int) atom1362Coded)) := by
  rw [block018_data_flat129_step, block018_data_flat127_original, block018_data_flat128_original]
def block018_data_flat130 : CoefficientMerge.Poly := [(nat_lit 3440, Int.ofNat (nat_lit 56900847134592))]
theorem block018_data_flat130_step : block018_data_flat130 = (CoefficientMerge.scale (56900847134592 : Int) atom1363Coded) := by decide +kernel
theorem block018_data_flat130_original : block018_data_flat130 = (CoefficientMerge.scale (56900847134592 : Int) atom1363Coded) := by
  rw [block018_data_flat130_step]
def block018_data_flat131 : CoefficientMerge.Poly := [(nat_lit 3441, Int.ofNat (nat_lit 63199359221184))]
theorem block018_data_flat131_step : block018_data_flat131 = (CoefficientMerge.scale (63199359221184 : Int) atom1364Coded) := by decide +kernel
theorem block018_data_flat131_original : block018_data_flat131 = (CoefficientMerge.scale (63199359221184 : Int) atom1364Coded) := by
  rw [block018_data_flat131_step]
def block018_data_flat132 : CoefficientMerge.Poly := [(nat_lit 3442, Int.ofNat (nat_lit 47004130814208))]
theorem block018_data_flat132_step : block018_data_flat132 = (CoefficientMerge.scale (47004130814208 : Int) atom1365Coded) := by decide +kernel
theorem block018_data_flat132_original : block018_data_flat132 = (CoefficientMerge.scale (47004130814208 : Int) atom1365Coded) := by
  rw [block018_data_flat132_step]
def block018_data_flat133 : CoefficientMerge.Poly := [(nat_lit 3441, Int.ofNat (nat_lit 63199359221184)), (nat_lit 3442, Int.ofNat (nat_lit 47004130814208))]
theorem block018_data_flat133_step : block018_data_flat133 = (CoefficientMerge.fastMerge block018_data_flat131 block018_data_flat132) := by decide +kernel
theorem block018_data_flat133_original : block018_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (63199359221184 : Int) atom1364Coded) (CoefficientMerge.scale (47004130814208 : Int) atom1365Coded)) := by
  rw [block018_data_flat133_step, block018_data_flat131_original, block018_data_flat132_original]
def block018_data_flat134 : CoefficientMerge.Poly := [(nat_lit 3440, Int.ofNat (nat_lit 56900847134592)), (nat_lit 3441, Int.ofNat (nat_lit 63199359221184)), (nat_lit 3442, Int.ofNat (nat_lit 47004130814208))]
theorem block018_data_flat134_step : block018_data_flat134 = (CoefficientMerge.fastMerge block018_data_flat130 block018_data_flat133) := by decide +kernel
theorem block018_data_flat134_original : block018_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (56900847134592 : Int) atom1363Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63199359221184 : Int) atom1364Coded) (CoefficientMerge.scale (47004130814208 : Int) atom1365Coded))) := by
  rw [block018_data_flat134_step, block018_data_flat130_original, block018_data_flat133_original]
def block018_data_flat135 : CoefficientMerge.Poly := [(nat_lit 3422, Int.ofNat (nat_lit 80901900693504)), (nat_lit 3439, Int.ofNat (nat_lit 17225211406464)), (nat_lit 3440, Int.ofNat (nat_lit 56900847134592)), (nat_lit 3441, Int.ofNat (nat_lit 63199359221184)), (nat_lit 3442, Int.ofNat (nat_lit 47004130814208))]
theorem block018_data_flat135_step : block018_data_flat135 = (CoefficientMerge.fastMerge block018_data_flat129 block018_data_flat134) := by decide +kernel
theorem block018_data_flat135_original : block018_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (80901900693504 : Int) atom1361Coded) (CoefficientMerge.scale (17225211406464 : Int) atom1362Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56900847134592 : Int) atom1363Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63199359221184 : Int) atom1364Coded) (CoefficientMerge.scale (47004130814208 : Int) atom1365Coded)))) := by
  rw [block018_data_flat135_step, block018_data_flat129_original, block018_data_flat134_original]
def block018_data_flat136 : CoefficientMerge.Poly := [(nat_lit 3417, Int.ofNat (nat_lit 21896742731904)), (nat_lit 3418, Int.ofNat (nat_lit 42928095901824)), (nat_lit 3419, Int.ofNat (nat_lit 68414874110208)), (nat_lit 3420, Int.ofNat (nat_lit 71594005599360)), (nat_lit 3421, Int.ofNat (nat_lit 53238031188480)), (nat_lit 3422, Int.ofNat (nat_lit 80901900693504)), (nat_lit 3439, Int.ofNat (nat_lit 17225211406464)), (nat_lit 3440, Int.ofNat (nat_lit 56900847134592)), (nat_lit 3441, Int.ofNat (nat_lit 63199359221184)), (nat_lit 3442, Int.ofNat (nat_lit 47004130814208))]
theorem block018_data_flat136_step : block018_data_flat136 = (CoefficientMerge.fastMerge block018_data_flat126 block018_data_flat135) := by decide +kernel
theorem block018_data_flat136_original : block018_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21896742731904 : Int) atom1356Coded) (CoefficientMerge.scale (42928095901824 : Int) atom1357Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68414874110208 : Int) atom1358Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71594005599360 : Int) atom1359Coded) (CoefficientMerge.scale (53238031188480 : Int) atom1360Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (80901900693504 : Int) atom1361Coded) (CoefficientMerge.scale (17225211406464 : Int) atom1362Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56900847134592 : Int) atom1363Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63199359221184 : Int) atom1364Coded) (CoefficientMerge.scale (47004130814208 : Int) atom1365Coded))))) := by
  rw [block018_data_flat136_step, block018_data_flat126_original, block018_data_flat135_original]
def block018_data_flat137 : CoefficientMerge.Poly := [(nat_lit 3443, Int.ofNat (nat_lit 59161605357600))]
theorem block018_data_flat137_step : block018_data_flat137 = (CoefficientMerge.scale (59161605357600 : Int) atom1366Coded) := by decide +kernel
theorem block018_data_flat137_original : block018_data_flat137 = (CoefficientMerge.scale (59161605357600 : Int) atom1366Coded) := by
  rw [block018_data_flat137_step]
def block018_data_flat138 : CoefficientMerge.Poly := [(nat_lit 3461, Int.ofNat (nat_lit 41545743986304))]
theorem block018_data_flat138_step : block018_data_flat138 = (CoefficientMerge.scale (41545743986304 : Int) atom1367Coded) := by decide +kernel
theorem block018_data_flat138_original : block018_data_flat138 = (CoefficientMerge.scale (41545743986304 : Int) atom1367Coded) := by
  rw [block018_data_flat138_step]
def block018_data_flat139 : CoefficientMerge.Poly := [(nat_lit 3443, Int.ofNat (nat_lit 59161605357600)), (nat_lit 3461, Int.ofNat (nat_lit 41545743986304))]
theorem block018_data_flat139_step : block018_data_flat139 = (CoefficientMerge.fastMerge block018_data_flat137 block018_data_flat138) := by decide +kernel
theorem block018_data_flat139_original : block018_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (59161605357600 : Int) atom1366Coded) (CoefficientMerge.scale (41545743986304 : Int) atom1367Coded)) := by
  rw [block018_data_flat139_step, block018_data_flat137_original, block018_data_flat138_original]
def block018_data_flat140 : CoefficientMerge.Poly := [(nat_lit 3462, Int.ofNat (nat_lit 70291863363456))]
theorem block018_data_flat140_step : block018_data_flat140 = (CoefficientMerge.scale (70291863363456 : Int) atom1368Coded) := by decide +kernel
theorem block018_data_flat140_original : block018_data_flat140 = (CoefficientMerge.scale (70291863363456 : Int) atom1368Coded) := by
  rw [block018_data_flat140_step]
def block018_data_flat141 : CoefficientMerge.Poly := [(nat_lit 3463, Int.ofNat (nat_lit 48185112168960))]
theorem block018_data_flat141_step : block018_data_flat141 = (CoefficientMerge.scale (48185112168960 : Int) atom1369Coded) := by decide +kernel
theorem block018_data_flat141_original : block018_data_flat141 = (CoefficientMerge.scale (48185112168960 : Int) atom1369Coded) := by
  rw [block018_data_flat141_step]
def block018_data_flat142 : CoefficientMerge.Poly := [(nat_lit 3464, Int.ofNat (nat_lit 51533139292416))]
theorem block018_data_flat142_step : block018_data_flat142 = (CoefficientMerge.scale (51533139292416 : Int) atom1370Coded) := by decide +kernel
theorem block018_data_flat142_original : block018_data_flat142 = (CoefficientMerge.scale (51533139292416 : Int) atom1370Coded) := by
  rw [block018_data_flat142_step]
def block018_data_flat143 : CoefficientMerge.Poly := [(nat_lit 3463, Int.ofNat (nat_lit 48185112168960)), (nat_lit 3464, Int.ofNat (nat_lit 51533139292416))]
theorem block018_data_flat143_step : block018_data_flat143 = (CoefficientMerge.fastMerge block018_data_flat141 block018_data_flat142) := by decide +kernel
theorem block018_data_flat143_original : block018_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48185112168960 : Int) atom1369Coded) (CoefficientMerge.scale (51533139292416 : Int) atom1370Coded)) := by
  rw [block018_data_flat143_step, block018_data_flat141_original, block018_data_flat142_original]
def block018_data_flat144 : CoefficientMerge.Poly := [(nat_lit 3462, Int.ofNat (nat_lit 70291863363456)), (nat_lit 3463, Int.ofNat (nat_lit 48185112168960)), (nat_lit 3464, Int.ofNat (nat_lit 51533139292416))]
theorem block018_data_flat144_step : block018_data_flat144 = (CoefficientMerge.fastMerge block018_data_flat140 block018_data_flat143) := by decide +kernel
theorem block018_data_flat144_original : block018_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (70291863363456 : Int) atom1368Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48185112168960 : Int) atom1369Coded) (CoefficientMerge.scale (51533139292416 : Int) atom1370Coded))) := by
  rw [block018_data_flat144_step, block018_data_flat140_original, block018_data_flat143_original]
def block018_data_flat145 : CoefficientMerge.Poly := [(nat_lit 3443, Int.ofNat (nat_lit 59161605357600)), (nat_lit 3461, Int.ofNat (nat_lit 41545743986304)), (nat_lit 3462, Int.ofNat (nat_lit 70291863363456)), (nat_lit 3463, Int.ofNat (nat_lit 48185112168960)), (nat_lit 3464, Int.ofNat (nat_lit 51533139292416))]
theorem block018_data_flat145_step : block018_data_flat145 = (CoefficientMerge.fastMerge block018_data_flat139 block018_data_flat144) := by decide +kernel
theorem block018_data_flat145_original : block018_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (59161605357600 : Int) atom1366Coded) (CoefficientMerge.scale (41545743986304 : Int) atom1367Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70291863363456 : Int) atom1368Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48185112168960 : Int) atom1369Coded) (CoefficientMerge.scale (51533139292416 : Int) atom1370Coded)))) := by
  rw [block018_data_flat145_step, block018_data_flat139_original, block018_data_flat144_original]
def block018_data_flat146 : CoefficientMerge.Poly := [(nat_lit 3483, Int.ofNat (nat_lit 22921685971776))]
theorem block018_data_flat146_step : block018_data_flat146 = (CoefficientMerge.scale (22921685971776 : Int) atom1371Coded) := by decide +kernel
theorem block018_data_flat146_original : block018_data_flat146 = (CoefficientMerge.scale (22921685971776 : Int) atom1371Coded) := by
  rw [block018_data_flat146_step]
def block018_data_flat147 : CoefficientMerge.Poly := [(nat_lit 3484, Int.ofNat (nat_lit 27537164315136))]
theorem block018_data_flat147_step : block018_data_flat147 = (CoefficientMerge.scale (27537164315136 : Int) atom1372Coded) := by decide +kernel
theorem block018_data_flat147_original : block018_data_flat147 = (CoefficientMerge.scale (27537164315136 : Int) atom1372Coded) := by
  rw [block018_data_flat147_step]
def block018_data_flat148 : CoefficientMerge.Poly := [(nat_lit 3483, Int.ofNat (nat_lit 22921685971776)), (nat_lit 3484, Int.ofNat (nat_lit 27537164315136))]
theorem block018_data_flat148_step : block018_data_flat148 = (CoefficientMerge.fastMerge block018_data_flat146 block018_data_flat147) := by decide +kernel
theorem block018_data_flat148_original : block018_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22921685971776 : Int) atom1371Coded) (CoefficientMerge.scale (27537164315136 : Int) atom1372Coded)) := by
  rw [block018_data_flat148_step, block018_data_flat146_original, block018_data_flat147_original]
def block018_data_flat149 : CoefficientMerge.Poly := [(nat_lit 3485, Int.ofNat (nat_lit 31480194875040))]
theorem block018_data_flat149_step : block018_data_flat149 = (CoefficientMerge.scale (31480194875040 : Int) atom1373Coded) := by decide +kernel
theorem block018_data_flat149_original : block018_data_flat149 = (CoefficientMerge.scale (31480194875040 : Int) atom1373Coded) := by
  rw [block018_data_flat149_step]
def block018_data_flat150 : CoefficientMerge.Poly := [(nat_lit 3704, Int.ofNat (nat_lit 1353863952000))]
theorem block018_data_flat150_step : block018_data_flat150 = (CoefficientMerge.scale (1353863952000 : Int) atom1374Coded) := by decide +kernel
theorem block018_data_flat150_original : block018_data_flat150 = (CoefficientMerge.scale (1353863952000 : Int) atom1374Coded) := by
  rw [block018_data_flat150_step]
def block018_data_flat151 : CoefficientMerge.Poly := [(nat_lit 3705, Int.ofNat (nat_lit 1372387968000))]
theorem block018_data_flat151_step : block018_data_flat151 = (CoefficientMerge.scale (1372387968000 : Int) atom1375Coded) := by decide +kernel
theorem block018_data_flat151_original : block018_data_flat151 = (CoefficientMerge.scale (1372387968000 : Int) atom1375Coded) := by
  rw [block018_data_flat151_step]
def block018_data_flat152 : CoefficientMerge.Poly := [(nat_lit 3704, Int.ofNat (nat_lit 1353863952000)), (nat_lit 3705, Int.ofNat (nat_lit 1372387968000))]
theorem block018_data_flat152_step : block018_data_flat152 = (CoefficientMerge.fastMerge block018_data_flat150 block018_data_flat151) := by decide +kernel
theorem block018_data_flat152_original : block018_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1353863952000 : Int) atom1374Coded) (CoefficientMerge.scale (1372387968000 : Int) atom1375Coded)) := by
  rw [block018_data_flat152_step, block018_data_flat150_original, block018_data_flat151_original]
def block018_data_flat153 : CoefficientMerge.Poly := [(nat_lit 3485, Int.ofNat (nat_lit 31480194875040)), (nat_lit 3704, Int.ofNat (nat_lit 1353863952000)), (nat_lit 3705, Int.ofNat (nat_lit 1372387968000))]
theorem block018_data_flat153_step : block018_data_flat153 = (CoefficientMerge.fastMerge block018_data_flat149 block018_data_flat152) := by decide +kernel
theorem block018_data_flat153_original : block018_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31480194875040 : Int) atom1373Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1353863952000 : Int) atom1374Coded) (CoefficientMerge.scale (1372387968000 : Int) atom1375Coded))) := by
  rw [block018_data_flat153_step, block018_data_flat149_original, block018_data_flat152_original]
def block018_data_flat154 : CoefficientMerge.Poly := [(nat_lit 3483, Int.ofNat (nat_lit 22921685971776)), (nat_lit 3484, Int.ofNat (nat_lit 27537164315136)), (nat_lit 3485, Int.ofNat (nat_lit 31480194875040)), (nat_lit 3704, Int.ofNat (nat_lit 1353863952000)), (nat_lit 3705, Int.ofNat (nat_lit 1372387968000))]
theorem block018_data_flat154_step : block018_data_flat154 = (CoefficientMerge.fastMerge block018_data_flat148 block018_data_flat153) := by decide +kernel
theorem block018_data_flat154_original : block018_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22921685971776 : Int) atom1371Coded) (CoefficientMerge.scale (27537164315136 : Int) atom1372Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31480194875040 : Int) atom1373Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1353863952000 : Int) atom1374Coded) (CoefficientMerge.scale (1372387968000 : Int) atom1375Coded)))) := by
  rw [block018_data_flat154_step, block018_data_flat148_original, block018_data_flat153_original]
def block018_data_flat155 : CoefficientMerge.Poly := [(nat_lit 3443, Int.ofNat (nat_lit 59161605357600)), (nat_lit 3461, Int.ofNat (nat_lit 41545743986304)), (nat_lit 3462, Int.ofNat (nat_lit 70291863363456)), (nat_lit 3463, Int.ofNat (nat_lit 48185112168960)), (nat_lit 3464, Int.ofNat (nat_lit 51533139292416)), (nat_lit 3483, Int.ofNat (nat_lit 22921685971776)), (nat_lit 3484, Int.ofNat (nat_lit 27537164315136)), (nat_lit 3485, Int.ofNat (nat_lit 31480194875040)), (nat_lit 3704, Int.ofNat (nat_lit 1353863952000)), (nat_lit 3705, Int.ofNat (nat_lit 1372387968000))]
theorem block018_data_flat155_step : block018_data_flat155 = (CoefficientMerge.fastMerge block018_data_flat145 block018_data_flat154) := by decide +kernel
theorem block018_data_flat155_original : block018_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (59161605357600 : Int) atom1366Coded) (CoefficientMerge.scale (41545743986304 : Int) atom1367Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70291863363456 : Int) atom1368Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48185112168960 : Int) atom1369Coded) (CoefficientMerge.scale (51533139292416 : Int) atom1370Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22921685971776 : Int) atom1371Coded) (CoefficientMerge.scale (27537164315136 : Int) atom1372Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31480194875040 : Int) atom1373Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1353863952000 : Int) atom1374Coded) (CoefficientMerge.scale (1372387968000 : Int) atom1375Coded))))) := by
  rw [block018_data_flat155_step, block018_data_flat145_original, block018_data_flat154_original]
def block018_data_flat156 : CoefficientMerge.Poly := [(nat_lit 3417, Int.ofNat (nat_lit 21896742731904)), (nat_lit 3418, Int.ofNat (nat_lit 42928095901824)), (nat_lit 3419, Int.ofNat (nat_lit 68414874110208)), (nat_lit 3420, Int.ofNat (nat_lit 71594005599360)), (nat_lit 3421, Int.ofNat (nat_lit 53238031188480)), (nat_lit 3422, Int.ofNat (nat_lit 80901900693504)), (nat_lit 3439, Int.ofNat (nat_lit 17225211406464)), (nat_lit 3440, Int.ofNat (nat_lit 56900847134592)), (nat_lit 3441, Int.ofNat (nat_lit 63199359221184)), (nat_lit 3442, Int.ofNat (nat_lit 47004130814208)), (nat_lit 3443, Int.ofNat (nat_lit 59161605357600)), (nat_lit 3461, Int.ofNat (nat_lit 41545743986304)), (nat_lit 3462, Int.ofNat (nat_lit 70291863363456)), (nat_lit 3463, Int.ofNat (nat_lit 48185112168960)), (nat_lit 3464, Int.ofNat (nat_lit 51533139292416)), (nat_lit 3483, Int.ofNat (nat_lit 22921685971776)), (nat_lit 3484, Int.ofNat (nat_lit 27537164315136)), (nat_lit 3485, Int.ofNat (nat_lit 31480194875040)), (nat_lit 3704, Int.ofNat (nat_lit 1353863952000)), (nat_lit 3705, Int.ofNat (nat_lit 1372387968000))]
theorem block018_data_flat156_step : block018_data_flat156 = (CoefficientMerge.fastMerge block018_data_flat136 block018_data_flat155) := by decide +kernel
theorem block018_data_flat156_original : block018_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21896742731904 : Int) atom1356Coded) (CoefficientMerge.scale (42928095901824 : Int) atom1357Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68414874110208 : Int) atom1358Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71594005599360 : Int) atom1359Coded) (CoefficientMerge.scale (53238031188480 : Int) atom1360Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (80901900693504 : Int) atom1361Coded) (CoefficientMerge.scale (17225211406464 : Int) atom1362Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56900847134592 : Int) atom1363Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63199359221184 : Int) atom1364Coded) (CoefficientMerge.scale (47004130814208 : Int) atom1365Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (59161605357600 : Int) atom1366Coded) (CoefficientMerge.scale (41545743986304 : Int) atom1367Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70291863363456 : Int) atom1368Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48185112168960 : Int) atom1369Coded) (CoefficientMerge.scale (51533139292416 : Int) atom1370Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22921685971776 : Int) atom1371Coded) (CoefficientMerge.scale (27537164315136 : Int) atom1372Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31480194875040 : Int) atom1373Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1353863952000 : Int) atom1374Coded) (CoefficientMerge.scale (1372387968000 : Int) atom1375Coded)))))) := by
  rw [block018_data_flat156_step, block018_data_flat136_original, block018_data_flat155_original]
def block018_data_flat157 : CoefficientMerge.Poly := [(nat_lit 3355, Int.ofNat (nat_lit 19397114109440)), (nat_lit 3356, Int.ofNat (nat_lit 31352906629760)), (nat_lit 3357, Int.ofNat (nat_lit 34150544280640)), (nat_lit 3358, Int.ofNat (nat_lit 43898083947264)), (nat_lit 3359, Int.ofNat (nat_lit 54883075413600)), (nat_lit 3373, Int.ofNat (nat_lit 10477390550400)), (nat_lit 3374, Int.ofNat (nat_lit 19824839136000)), (nat_lit 3375, Int.ofNat (nat_lit 24472903179456)), (nat_lit 3376, Int.ofNat (nat_lit 24292870914240)), (nat_lit 3377, Int.ofNat (nat_lit 39375935372160)), (nat_lit 3378, Int.ofNat (nat_lit 43793896443840)), (nat_lit 3379, Int.ofNat (nat_lit 47292853414464)), (nat_lit 3380, Int.ofNat (nat_lit 64416097821600)), (nat_lit 3395, Int.ofNat (nat_lit 14909899939200)), (nat_lit 3396, Int.ofNat (nat_lit 29392479133056)), (nat_lit 3397, Int.ofNat (nat_lit 29069478282240)), (nat_lit 3398, Int.ofNat (nat_lit 49592493970560)), (nat_lit 3399, Int.ofNat (nat_lit 55850131448640)), (nat_lit 3400, Int.ofNat (nat_lit 55138349470464)), (nat_lit 3401, Int.ofNat (nat_lit 78532122866400)), (nat_lit 3417, Int.ofNat (nat_lit 21896742731904)), (nat_lit 3418, Int.ofNat (nat_lit 42928095901824)), (nat_lit 3419, Int.ofNat (nat_lit 68414874110208)), (nat_lit 3420, Int.ofNat (nat_lit 71594005599360)), (nat_lit 3421, Int.ofNat (nat_lit 53238031188480)), (nat_lit 3422, Int.ofNat (nat_lit 80901900693504)), (nat_lit 3439, Int.ofNat (nat_lit 17225211406464)), (nat_lit 3440, Int.ofNat (nat_lit 56900847134592)), (nat_lit 3441, Int.ofNat (nat_lit 63199359221184)), (nat_lit 3442, Int.ofNat (nat_lit 47004130814208)), (nat_lit 3443, Int.ofNat (nat_lit 59161605357600)), (nat_lit 3461, Int.ofNat (nat_lit 41545743986304)), (nat_lit 3462, Int.ofNat (nat_lit 70291863363456)), (nat_lit 3463, Int.ofNat (nat_lit 48185112168960)), (nat_lit 3464, Int.ofNat (nat_lit 51533139292416)), (nat_lit 3483, Int.ofNat (nat_lit 22921685971776)), (nat_lit 3484, Int.ofNat (nat_lit 27537164315136)), (nat_lit 3485, Int.ofNat (nat_lit 31480194875040)), (nat_lit 3704, Int.ofNat (nat_lit 1353863952000)), (nat_lit 3705, Int.ofNat (nat_lit 1372387968000))]
theorem block018_data_flat157_step : block018_data_flat157 = (CoefficientMerge.fastMerge block018_data_flat117 block018_data_flat156) := by decide +kernel
theorem block018_data_flat157_original : block018_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19397114109440 : Int) atom1336Coded) (CoefficientMerge.scale (31352906629760 : Int) atom1337Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34150544280640 : Int) atom1338Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43898083947264 : Int) atom1339Coded) (CoefficientMerge.scale (54883075413600 : Int) atom1340Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10477390550400 : Int) atom1341Coded) (CoefficientMerge.scale (19824839136000 : Int) atom1342Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24472903179456 : Int) atom1343Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24292870914240 : Int) atom1344Coded) (CoefficientMerge.scale (39375935372160 : Int) atom1345Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43793896443840 : Int) atom1346Coded) (CoefficientMerge.scale (47292853414464 : Int) atom1347Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64416097821600 : Int) atom1348Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14909899939200 : Int) atom1349Coded) (CoefficientMerge.scale (29392479133056 : Int) atom1350Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29069478282240 : Int) atom1351Coded) (CoefficientMerge.scale (49592493970560 : Int) atom1352Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55850131448640 : Int) atom1353Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55138349470464 : Int) atom1354Coded) (CoefficientMerge.scale (78532122866400 : Int) atom1355Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21896742731904 : Int) atom1356Coded) (CoefficientMerge.scale (42928095901824 : Int) atom1357Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68414874110208 : Int) atom1358Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71594005599360 : Int) atom1359Coded) (CoefficientMerge.scale (53238031188480 : Int) atom1360Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (80901900693504 : Int) atom1361Coded) (CoefficientMerge.scale (17225211406464 : Int) atom1362Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56900847134592 : Int) atom1363Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63199359221184 : Int) atom1364Coded) (CoefficientMerge.scale (47004130814208 : Int) atom1365Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (59161605357600 : Int) atom1366Coded) (CoefficientMerge.scale (41545743986304 : Int) atom1367Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70291863363456 : Int) atom1368Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48185112168960 : Int) atom1369Coded) (CoefficientMerge.scale (51533139292416 : Int) atom1370Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22921685971776 : Int) atom1371Coded) (CoefficientMerge.scale (27537164315136 : Int) atom1372Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31480194875040 : Int) atom1373Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1353863952000 : Int) atom1374Coded) (CoefficientMerge.scale (1372387968000 : Int) atom1375Coded))))))) := by
  rw [block018_data_flat157_step, block018_data_flat117_original, block018_data_flat156_original]
def block018_data_flat158 : CoefficientMerge.Poly := [(nat_lit 3270, Int.ofNat (nat_lit 6427474232112)), (nat_lit 3272, Int.ofNat (nat_lit 1510388496720)), (nat_lit 3273, Int.ofNat (nat_lit 5786258284800)), (nat_lit 3274, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3275, Int.ofNat (nat_lit 17391151612800)), (nat_lit 3285, Int.ofNat (nat_lit 896401296000)), (nat_lit 3288, Int.ofNat (nat_lit 686193984000)), (nat_lit 3289, Int.ofNat (nat_lit 1372387968000)), (nat_lit 3290, Int.ofNat (nat_lit 2058581952000)), (nat_lit 3291, Int.ofNat (nat_lit 8185219145856)), (nat_lit 3292, Int.ofNat (nat_lit 3335794446240)), (nat_lit 3293, Int.ofNat (nat_lit 9115747148160)), (nat_lit 3294, Int.ofNat (nat_lit 13951505319840)), (nat_lit 3295, Int.ofNat (nat_lit 22686649344864)), (nat_lit 3296, Int.ofNat (nat_lit 32365160755200)), (nat_lit 3307, Int.ofNat (nat_lit 2262023971200)), (nat_lit 3308, Int.ofNat (nat_lit 3851384544000)), (nat_lit 3309, Int.ofNat (nat_lit 4201246828800)), (nat_lit 3310, Int.ofNat (nat_lit 4978289030400)), (nat_lit 3311, Int.ofNat (nat_lit 5755331232000)), (nat_lit 3312, Int.ofNat (nat_lit 13173656115456)), (nat_lit 3313, Int.ofNat (nat_lit 9544641913440)), (nat_lit 3314, Int.ofNat (nat_lit 18856319074560)), (nat_lit 3315, Int.ofNat (nat_lit 22426001022240)), (nat_lit 3316, Int.ofNat (nat_lit 32125924124064)), (nat_lit 3317, Int.ofNat (nat_lit 42511529440800)), (nat_lit 3329, Int.ofNat (nat_lit 4747785840000)), (nat_lit 3330, Int.ofNat (nat_lit 8318410732800)), (nat_lit 3331, Int.ofNat (nat_lit 9018135302400)), (nat_lit 3332, Int.ofNat (nat_lit 9717859872000)), (nat_lit 3333, Int.ofNat (nat_lit 17823714742656)), (nat_lit 3334, Int.ofNat (nat_lit 15047395107840)), (nat_lit 3335, Int.ofNat (nat_lit 27687575007360)), (nat_lit 3336, Int.ofNat (nat_lit 29300658949440)), (nat_lit 3337, Int.ofNat (nat_lit 39568321822464)), (nat_lit 3338, Int.ofNat (nat_lit 50335348946400)), (nat_lit 3351, Int.ofNat (nat_lit 7156230076800)), (nat_lit 3352, Int.ofNat (nat_lit 14339521324800)), (nat_lit 3353, Int.ofNat (nat_lit 14793762412800)), (nat_lit 3354, Int.ofNat (nat_lit 19441485123456)), (nat_lit 3355, Int.ofNat (nat_lit 19397114109440)), (nat_lit 3356, Int.ofNat (nat_lit 31352906629760)), (nat_lit 3357, Int.ofNat (nat_lit 34150544280640)), (nat_lit 3358, Int.ofNat (nat_lit 43898083947264)), (nat_lit 3359, Int.ofNat (nat_lit 54883075413600)), (nat_lit 3373, Int.ofNat (nat_lit 10477390550400)), (nat_lit 3374, Int.ofNat (nat_lit 19824839136000)), (nat_lit 3375, Int.ofNat (nat_lit 24472903179456)), (nat_lit 3376, Int.ofNat (nat_lit 24292870914240)), (nat_lit 3377, Int.ofNat (nat_lit 39375935372160)), (nat_lit 3378, Int.ofNat (nat_lit 43793896443840)), (nat_lit 3379, Int.ofNat (nat_lit 47292853414464)), (nat_lit 3380, Int.ofNat (nat_lit 64416097821600)), (nat_lit 3395, Int.ofNat (nat_lit 14909899939200)), (nat_lit 3396, Int.ofNat (nat_lit 29392479133056)), (nat_lit 3397, Int.ofNat (nat_lit 29069478282240)), (nat_lit 3398, Int.ofNat (nat_lit 49592493970560)), (nat_lit 3399, Int.ofNat (nat_lit 55850131448640)), (nat_lit 3400, Int.ofNat (nat_lit 55138349470464)), (nat_lit 3401, Int.ofNat (nat_lit 78532122866400)), (nat_lit 3417, Int.ofNat (nat_lit 21896742731904)), (nat_lit 3418, Int.ofNat (nat_lit 42928095901824)), (nat_lit 3419, Int.ofNat (nat_lit 68414874110208)), (nat_lit 3420, Int.ofNat (nat_lit 71594005599360)), (nat_lit 3421, Int.ofNat (nat_lit 53238031188480)), (nat_lit 3422, Int.ofNat (nat_lit 80901900693504)), (nat_lit 3439, Int.ofNat (nat_lit 17225211406464)), (nat_lit 3440, Int.ofNat (nat_lit 56900847134592)), (nat_lit 3441, Int.ofNat (nat_lit 63199359221184)), (nat_lit 3442, Int.ofNat (nat_lit 47004130814208)), (nat_lit 3443, Int.ofNat (nat_lit 59161605357600)), (nat_lit 3461, Int.ofNat (nat_lit 41545743986304)), (nat_lit 3462, Int.ofNat (nat_lit 70291863363456)), (nat_lit 3463, Int.ofNat (nat_lit 48185112168960)), (nat_lit 3464, Int.ofNat (nat_lit 51533139292416)), (nat_lit 3483, Int.ofNat (nat_lit 22921685971776)), (nat_lit 3484, Int.ofNat (nat_lit 27537164315136)), (nat_lit 3485, Int.ofNat (nat_lit 31480194875040)), (nat_lit 3704, Int.ofNat (nat_lit 1353863952000)), (nat_lit 3705, Int.ofNat (nat_lit 1372387968000))]
theorem block018_data_flat158_step : block018_data_flat158 = (CoefficientMerge.fastMerge block018_data_flat078 block018_data_flat157) := by decide +kernel
theorem block018_data_flat158_original : block018_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6427474232112 : Int) atom1296Coded) (CoefficientMerge.scale (1510388496720 : Int) atom1297Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1299Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1300Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (896401296000 : Int) atom1301Coded) (CoefficientMerge.scale (686193984000 : Int) atom1302Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1372387968000 : Int) atom1303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2058581952000 : Int) atom1304Coded) (CoefficientMerge.scale (8185219145856 : Int) atom1305Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3335794446240 : Int) atom1306Coded) (CoefficientMerge.scale (9115747148160 : Int) atom1307Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13951505319840 : Int) atom1308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22686649344864 : Int) atom1309Coded) (CoefficientMerge.scale (32365160755200 : Int) atom1310Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2262023971200 : Int) atom1311Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1312Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4201246828800 : Int) atom1313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4978289030400 : Int) atom1314Coded) (CoefficientMerge.scale (5755331232000 : Int) atom1315Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13173656115456 : Int) atom1316Coded) (CoefficientMerge.scale (9544641913440 : Int) atom1317Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18856319074560 : Int) atom1318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22426001022240 : Int) atom1319Coded) (CoefficientMerge.scale (32125924124064 : Int) atom1320Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42511529440800 : Int) atom1321Coded) (CoefficientMerge.scale (4747785840000 : Int) atom1322Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8318410732800 : Int) atom1323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9018135302400 : Int) atom1324Coded) (CoefficientMerge.scale (9717859872000 : Int) atom1325Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17823714742656 : Int) atom1326Coded) (CoefficientMerge.scale (15047395107840 : Int) atom1327Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27687575007360 : Int) atom1328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29300658949440 : Int) atom1329Coded) (CoefficientMerge.scale (39568321822464 : Int) atom1330Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50335348946400 : Int) atom1331Coded) (CoefficientMerge.scale (7156230076800 : Int) atom1332Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14339521324800 : Int) atom1333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14793762412800 : Int) atom1334Coded) (CoefficientMerge.scale (19441485123456 : Int) atom1335Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19397114109440 : Int) atom1336Coded) (CoefficientMerge.scale (31352906629760 : Int) atom1337Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34150544280640 : Int) atom1338Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43898083947264 : Int) atom1339Coded) (CoefficientMerge.scale (54883075413600 : Int) atom1340Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10477390550400 : Int) atom1341Coded) (CoefficientMerge.scale (19824839136000 : Int) atom1342Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24472903179456 : Int) atom1343Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24292870914240 : Int) atom1344Coded) (CoefficientMerge.scale (39375935372160 : Int) atom1345Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43793896443840 : Int) atom1346Coded) (CoefficientMerge.scale (47292853414464 : Int) atom1347Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64416097821600 : Int) atom1348Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14909899939200 : Int) atom1349Coded) (CoefficientMerge.scale (29392479133056 : Int) atom1350Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29069478282240 : Int) atom1351Coded) (CoefficientMerge.scale (49592493970560 : Int) atom1352Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55850131448640 : Int) atom1353Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55138349470464 : Int) atom1354Coded) (CoefficientMerge.scale (78532122866400 : Int) atom1355Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21896742731904 : Int) atom1356Coded) (CoefficientMerge.scale (42928095901824 : Int) atom1357Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68414874110208 : Int) atom1358Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71594005599360 : Int) atom1359Coded) (CoefficientMerge.scale (53238031188480 : Int) atom1360Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (80901900693504 : Int) atom1361Coded) (CoefficientMerge.scale (17225211406464 : Int) atom1362Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56900847134592 : Int) atom1363Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63199359221184 : Int) atom1364Coded) (CoefficientMerge.scale (47004130814208 : Int) atom1365Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (59161605357600 : Int) atom1366Coded) (CoefficientMerge.scale (41545743986304 : Int) atom1367Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70291863363456 : Int) atom1368Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48185112168960 : Int) atom1369Coded) (CoefficientMerge.scale (51533139292416 : Int) atom1370Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22921685971776 : Int) atom1371Coded) (CoefficientMerge.scale (27537164315136 : Int) atom1372Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31480194875040 : Int) atom1373Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1353863952000 : Int) atom1374Coded) (CoefficientMerge.scale (1372387968000 : Int) atom1375Coded)))))))) := by
  rw [block018_data_flat158_step, block018_data_flat078_original, block018_data_flat157_original]
def block018_data_flat159 : CoefficientMerge.Poly := [(nat_lit 3270, Int.ofNat (nat_lit 6427474232112)), (nat_lit 3272, Int.ofNat (nat_lit 1510388496720)), (nat_lit 3273, Int.ofNat (nat_lit 5786258284800)), (nat_lit 3274, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3275, Int.ofNat (nat_lit 17391151612800)), (nat_lit 3285, Int.ofNat (nat_lit 896401296000)), (nat_lit 3288, Int.ofNat (nat_lit 686193984000)), (nat_lit 3289, Int.ofNat (nat_lit 1372387968000)), (nat_lit 3290, Int.ofNat (nat_lit 2058581952000)), (nat_lit 3291, Int.ofNat (nat_lit 8185219145856)), (nat_lit 3292, Int.ofNat (nat_lit 3335794446240)), (nat_lit 3293, Int.ofNat (nat_lit 9115747148160)), (nat_lit 3294, Int.ofNat (nat_lit 13951505319840)), (nat_lit 3295, Int.ofNat (nat_lit 22686649344864)), (nat_lit 3296, Int.ofNat (nat_lit 32365160755200)), (nat_lit 3307, Int.ofNat (nat_lit 2262023971200)), (nat_lit 3308, Int.ofNat (nat_lit 3851384544000)), (nat_lit 3309, Int.ofNat (nat_lit 4201246828800)), (nat_lit 3310, Int.ofNat (nat_lit 4978289030400)), (nat_lit 3311, Int.ofNat (nat_lit 5755331232000)), (nat_lit 3312, Int.ofNat (nat_lit 13173656115456)), (nat_lit 3313, Int.ofNat (nat_lit 9544641913440)), (nat_lit 3314, Int.ofNat (nat_lit 18856319074560)), (nat_lit 3315, Int.ofNat (nat_lit 22426001022240)), (nat_lit 3316, Int.ofNat (nat_lit 32125924124064)), (nat_lit 3317, Int.ofNat (nat_lit 42511529440800)), (nat_lit 3329, Int.ofNat (nat_lit 4747785840000)), (nat_lit 3330, Int.ofNat (nat_lit 8318410732800)), (nat_lit 3331, Int.ofNat (nat_lit 9018135302400)), (nat_lit 3332, Int.ofNat (nat_lit 9717859872000)), (nat_lit 3333, Int.ofNat (nat_lit 17823714742656)), (nat_lit 3334, Int.ofNat (nat_lit 15047395107840)), (nat_lit 3335, Int.ofNat (nat_lit 27687575007360)), (nat_lit 3336, Int.ofNat (nat_lit 29300658949440)), (nat_lit 3337, Int.ofNat (nat_lit 39568321822464)), (nat_lit 3338, Int.ofNat (nat_lit 50335348946400)), (nat_lit 3351, Int.ofNat (nat_lit 7156230076800)), (nat_lit 3352, Int.ofNat (nat_lit 14339521324800)), (nat_lit 3353, Int.ofNat (nat_lit 14793762412800)), (nat_lit 3354, Int.ofNat (nat_lit 19441485123456)), (nat_lit 3355, Int.ofNat (nat_lit 19397114109440)), (nat_lit 3356, Int.ofNat (nat_lit 31352906629760)), (nat_lit 3357, Int.ofNat (nat_lit 34150544280640)), (nat_lit 3358, Int.ofNat (nat_lit 43898083947264)), (nat_lit 3359, Int.ofNat (nat_lit 54883075413600)), (nat_lit 3373, Int.ofNat (nat_lit 10477390550400)), (nat_lit 3374, Int.ofNat (nat_lit 19824839136000)), (nat_lit 3375, Int.ofNat (nat_lit 24472903179456)), (nat_lit 3376, Int.ofNat (nat_lit 24292870914240)), (nat_lit 3377, Int.ofNat (nat_lit 39375935372160)), (nat_lit 3378, Int.ofNat (nat_lit 43793896443840)), (nat_lit 3379, Int.ofNat (nat_lit 47292853414464)), (nat_lit 3380, Int.ofNat (nat_lit 64416097821600)), (nat_lit 3395, Int.ofNat (nat_lit 14909899939200)), (nat_lit 3396, Int.ofNat (nat_lit 29392479133056)), (nat_lit 3397, Int.ofNat (nat_lit 29069478282240)), (nat_lit 3398, Int.ofNat (nat_lit 49592493970560)), (nat_lit 3399, Int.ofNat (nat_lit 55850131448640)), (nat_lit 3400, Int.ofNat (nat_lit 55138349470464)), (nat_lit 3401, Int.ofNat (nat_lit 78532122866400)), (nat_lit 3417, Int.ofNat (nat_lit 21896742731904)), (nat_lit 3418, Int.ofNat (nat_lit 42928095901824)), (nat_lit 3419, Int.ofNat (nat_lit 68414874110208)), (nat_lit 3420, Int.ofNat (nat_lit 71594005599360)), (nat_lit 3421, Int.ofNat (nat_lit 53238031188480)), (nat_lit 3422, Int.ofNat (nat_lit 80901900693504)), (nat_lit 3439, Int.ofNat (nat_lit 17225211406464)), (nat_lit 3440, Int.ofNat (nat_lit 56900847134592)), (nat_lit 3441, Int.ofNat (nat_lit 63199359221184)), (nat_lit 3442, Int.ofNat (nat_lit 47004130814208)), (nat_lit 3443, Int.ofNat (nat_lit 59161605357600)), (nat_lit 3461, Int.ofNat (nat_lit 41545743986304)), (nat_lit 3462, Int.ofNat (nat_lit 70291863363456)), (nat_lit 3463, Int.ofNat (nat_lit 48185112168960)), (nat_lit 3464, Int.ofNat (nat_lit 51533139292416)), (nat_lit 3483, Int.ofNat (nat_lit 22921685971776)), (nat_lit 3484, Int.ofNat (nat_lit 27537164315136)), (nat_lit 3485, Int.ofNat (nat_lit 31480194875040)), (nat_lit 3704, Int.ofNat (nat_lit 1353863952000)), (nat_lit 3705, Int.ofNat (nat_lit 1372387968000))]
theorem block018_data_flat159_step : block018_data_flat159 = (CoefficientMerge.trim block018_data_flat158) := by decide +kernel
theorem block018_data_flat159_original : block018_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6427474232112 : Int) atom1296Coded) (CoefficientMerge.scale (1510388496720 : Int) atom1297Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1299Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1300Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (896401296000 : Int) atom1301Coded) (CoefficientMerge.scale (686193984000 : Int) atom1302Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1372387968000 : Int) atom1303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2058581952000 : Int) atom1304Coded) (CoefficientMerge.scale (8185219145856 : Int) atom1305Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3335794446240 : Int) atom1306Coded) (CoefficientMerge.scale (9115747148160 : Int) atom1307Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13951505319840 : Int) atom1308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22686649344864 : Int) atom1309Coded) (CoefficientMerge.scale (32365160755200 : Int) atom1310Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2262023971200 : Int) atom1311Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1312Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4201246828800 : Int) atom1313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4978289030400 : Int) atom1314Coded) (CoefficientMerge.scale (5755331232000 : Int) atom1315Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13173656115456 : Int) atom1316Coded) (CoefficientMerge.scale (9544641913440 : Int) atom1317Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18856319074560 : Int) atom1318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22426001022240 : Int) atom1319Coded) (CoefficientMerge.scale (32125924124064 : Int) atom1320Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42511529440800 : Int) atom1321Coded) (CoefficientMerge.scale (4747785840000 : Int) atom1322Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8318410732800 : Int) atom1323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9018135302400 : Int) atom1324Coded) (CoefficientMerge.scale (9717859872000 : Int) atom1325Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17823714742656 : Int) atom1326Coded) (CoefficientMerge.scale (15047395107840 : Int) atom1327Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27687575007360 : Int) atom1328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29300658949440 : Int) atom1329Coded) (CoefficientMerge.scale (39568321822464 : Int) atom1330Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50335348946400 : Int) atom1331Coded) (CoefficientMerge.scale (7156230076800 : Int) atom1332Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14339521324800 : Int) atom1333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14793762412800 : Int) atom1334Coded) (CoefficientMerge.scale (19441485123456 : Int) atom1335Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19397114109440 : Int) atom1336Coded) (CoefficientMerge.scale (31352906629760 : Int) atom1337Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34150544280640 : Int) atom1338Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43898083947264 : Int) atom1339Coded) (CoefficientMerge.scale (54883075413600 : Int) atom1340Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10477390550400 : Int) atom1341Coded) (CoefficientMerge.scale (19824839136000 : Int) atom1342Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24472903179456 : Int) atom1343Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24292870914240 : Int) atom1344Coded) (CoefficientMerge.scale (39375935372160 : Int) atom1345Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43793896443840 : Int) atom1346Coded) (CoefficientMerge.scale (47292853414464 : Int) atom1347Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64416097821600 : Int) atom1348Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14909899939200 : Int) atom1349Coded) (CoefficientMerge.scale (29392479133056 : Int) atom1350Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29069478282240 : Int) atom1351Coded) (CoefficientMerge.scale (49592493970560 : Int) atom1352Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55850131448640 : Int) atom1353Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55138349470464 : Int) atom1354Coded) (CoefficientMerge.scale (78532122866400 : Int) atom1355Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21896742731904 : Int) atom1356Coded) (CoefficientMerge.scale (42928095901824 : Int) atom1357Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68414874110208 : Int) atom1358Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71594005599360 : Int) atom1359Coded) (CoefficientMerge.scale (53238031188480 : Int) atom1360Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (80901900693504 : Int) atom1361Coded) (CoefficientMerge.scale (17225211406464 : Int) atom1362Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56900847134592 : Int) atom1363Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63199359221184 : Int) atom1364Coded) (CoefficientMerge.scale (47004130814208 : Int) atom1365Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (59161605357600 : Int) atom1366Coded) (CoefficientMerge.scale (41545743986304 : Int) atom1367Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70291863363456 : Int) atom1368Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48185112168960 : Int) atom1369Coded) (CoefficientMerge.scale (51533139292416 : Int) atom1370Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22921685971776 : Int) atom1371Coded) (CoefficientMerge.scale (27537164315136 : Int) atom1372Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31480194875040 : Int) atom1373Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1353863952000 : Int) atom1374Coded) (CoefficientMerge.scale (1372387968000 : Int) atom1375Coded))))))))) := by
  rw [block018_data_flat159_step, block018_data_flat158_original]
theorem block018_data : block018 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6427474232112 : Int) atom1296Coded) (CoefficientMerge.scale (1510388496720 : Int) atom1297Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5786258284800 : Int) atom1298Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1299Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1300Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (896401296000 : Int) atom1301Coded) (CoefficientMerge.scale (686193984000 : Int) atom1302Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1372387968000 : Int) atom1303Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2058581952000 : Int) atom1304Coded) (CoefficientMerge.scale (8185219145856 : Int) atom1305Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3335794446240 : Int) atom1306Coded) (CoefficientMerge.scale (9115747148160 : Int) atom1307Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13951505319840 : Int) atom1308Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22686649344864 : Int) atom1309Coded) (CoefficientMerge.scale (32365160755200 : Int) atom1310Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2262023971200 : Int) atom1311Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1312Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4201246828800 : Int) atom1313Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4978289030400 : Int) atom1314Coded) (CoefficientMerge.scale (5755331232000 : Int) atom1315Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13173656115456 : Int) atom1316Coded) (CoefficientMerge.scale (9544641913440 : Int) atom1317Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18856319074560 : Int) atom1318Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22426001022240 : Int) atom1319Coded) (CoefficientMerge.scale (32125924124064 : Int) atom1320Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42511529440800 : Int) atom1321Coded) (CoefficientMerge.scale (4747785840000 : Int) atom1322Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8318410732800 : Int) atom1323Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9018135302400 : Int) atom1324Coded) (CoefficientMerge.scale (9717859872000 : Int) atom1325Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17823714742656 : Int) atom1326Coded) (CoefficientMerge.scale (15047395107840 : Int) atom1327Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27687575007360 : Int) atom1328Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29300658949440 : Int) atom1329Coded) (CoefficientMerge.scale (39568321822464 : Int) atom1330Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50335348946400 : Int) atom1331Coded) (CoefficientMerge.scale (7156230076800 : Int) atom1332Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14339521324800 : Int) atom1333Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14793762412800 : Int) atom1334Coded) (CoefficientMerge.scale (19441485123456 : Int) atom1335Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19397114109440 : Int) atom1336Coded) (CoefficientMerge.scale (31352906629760 : Int) atom1337Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34150544280640 : Int) atom1338Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43898083947264 : Int) atom1339Coded) (CoefficientMerge.scale (54883075413600 : Int) atom1340Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10477390550400 : Int) atom1341Coded) (CoefficientMerge.scale (19824839136000 : Int) atom1342Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24472903179456 : Int) atom1343Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24292870914240 : Int) atom1344Coded) (CoefficientMerge.scale (39375935372160 : Int) atom1345Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43793896443840 : Int) atom1346Coded) (CoefficientMerge.scale (47292853414464 : Int) atom1347Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64416097821600 : Int) atom1348Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14909899939200 : Int) atom1349Coded) (CoefficientMerge.scale (29392479133056 : Int) atom1350Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (29069478282240 : Int) atom1351Coded) (CoefficientMerge.scale (49592493970560 : Int) atom1352Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55850131448640 : Int) atom1353Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55138349470464 : Int) atom1354Coded) (CoefficientMerge.scale (78532122866400 : Int) atom1355Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21896742731904 : Int) atom1356Coded) (CoefficientMerge.scale (42928095901824 : Int) atom1357Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68414874110208 : Int) atom1358Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (71594005599360 : Int) atom1359Coded) (CoefficientMerge.scale (53238031188480 : Int) atom1360Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (80901900693504 : Int) atom1361Coded) (CoefficientMerge.scale (17225211406464 : Int) atom1362Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56900847134592 : Int) atom1363Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (63199359221184 : Int) atom1364Coded) (CoefficientMerge.scale (47004130814208 : Int) atom1365Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (59161605357600 : Int) atom1366Coded) (CoefficientMerge.scale (41545743986304 : Int) atom1367Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70291863363456 : Int) atom1368Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48185112168960 : Int) atom1369Coded) (CoefficientMerge.scale (51533139292416 : Int) atom1370Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22921685971776 : Int) atom1371Coded) (CoefficientMerge.scale (27537164315136 : Int) atom1372Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31480194875040 : Int) atom1373Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1353863952000 : Int) atom1374Coded) (CoefficientMerge.scale (1372387968000 : Int) atom1375Coded)))))))) := by
  have h : block018 = block018_data_flat159 := by decide +kernel
  exact h.trans block018_data_flat159_original
theorem block018_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block018 := by
  rw [block018_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1296Coded_nonneg g hg hA hB) (atom1297Coded_nonneg g hg hA hB)) (add_nonneg (atom1298Coded_nonneg g hg hA hB) (add_nonneg (atom1299Coded_nonneg g hg hA hB) (atom1300Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1301Coded_nonneg g hg hA hB) (atom1302Coded_nonneg g hg hA hB)) (add_nonneg (atom1303Coded_nonneg g hg hA hB) (add_nonneg (atom1304Coded_nonneg g hg hA hB) (atom1305Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1306Coded_nonneg g hg hA hB) (atom1307Coded_nonneg g hg hA hB)) (add_nonneg (atom1308Coded_nonneg g hg hA hB) (add_nonneg (atom1309Coded_nonneg g hg hA hB) (atom1310Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1311Coded_nonneg g hg hA hB) (atom1312Coded_nonneg g hg hA hB)) (add_nonneg (atom1313Coded_nonneg g hg hA hB) (add_nonneg (atom1314Coded_nonneg g hg hA hB) (atom1315Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1316Coded_nonneg g hg hA hB) (atom1317Coded_nonneg g hg hA hB)) (add_nonneg (atom1318Coded_nonneg g hg hA hB) (add_nonneg (atom1319Coded_nonneg g hg hA hB) (atom1320Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1321Coded_nonneg g hg hA hB) (atom1322Coded_nonneg g hg hA hB)) (add_nonneg (atom1323Coded_nonneg g hg hA hB) (add_nonneg (atom1324Coded_nonneg g hg hA hB) (atom1325Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1326Coded_nonneg g hg hA hB) (atom1327Coded_nonneg g hg hA hB)) (add_nonneg (atom1328Coded_nonneg g hg hA hB) (add_nonneg (atom1329Coded_nonneg g hg hA hB) (atom1330Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1331Coded_nonneg g hg hA hB) (atom1332Coded_nonneg g hg hA hB)) (add_nonneg (atom1333Coded_nonneg g hg hA hB) (add_nonneg (atom1334Coded_nonneg g hg hA hB) (atom1335Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1336Coded_nonneg g hg hA hB) (atom1337Coded_nonneg g hg hA hB)) (add_nonneg (atom1338Coded_nonneg g hg hA hB) (add_nonneg (atom1339Coded_nonneg g hg hA hB) (atom1340Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1341Coded_nonneg g hg hA hB) (atom1342Coded_nonneg g hg hA hB)) (add_nonneg (atom1343Coded_nonneg g hg hA hB) (add_nonneg (atom1344Coded_nonneg g hg hA hB) (atom1345Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1346Coded_nonneg g hg hA hB) (atom1347Coded_nonneg g hg hA hB)) (add_nonneg (atom1348Coded_nonneg g hg hA hB) (add_nonneg (atom1349Coded_nonneg g hg hA hB) (atom1350Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1351Coded_nonneg g hg hA hB) (atom1352Coded_nonneg g hg hA hB)) (add_nonneg (atom1353Coded_nonneg g hg hA hB) (add_nonneg (atom1354Coded_nonneg g hg hA hB) (atom1355Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1356Coded_nonneg g hg hA hB) (atom1357Coded_nonneg g hg hA hB)) (add_nonneg (atom1358Coded_nonneg g hg hA hB) (add_nonneg (atom1359Coded_nonneg g hg hA hB) (atom1360Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1361Coded_nonneg g hg hA hB) (atom1362Coded_nonneg g hg hA hB)) (add_nonneg (atom1363Coded_nonneg g hg hA hB) (add_nonneg (atom1364Coded_nonneg g hg hA hB) (atom1365Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1366Coded_nonneg g hg hA hB) (atom1367Coded_nonneg g hg hA hB)) (add_nonneg (atom1368Coded_nonneg g hg hA hB) (add_nonneg (atom1369Coded_nonneg g hg hA hB) (atom1370Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1371Coded_nonneg g hg hA hB) (atom1372Coded_nonneg g hg hA hB)) (add_nonneg (atom1373Coded_nonneg g hg hA hB) (add_nonneg (atom1374Coded_nonneg g hg hA hB) (atom1375Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
