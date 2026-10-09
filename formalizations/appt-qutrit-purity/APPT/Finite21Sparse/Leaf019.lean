import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1376 : SparsePolynomial.Poly := [([8,8,10], 1)]
theorem eval_atom1376 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1376 = ((g 8) * (g 8) * (g 10)) := by
  norm_num [atom1376, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1376_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (770276908800 : Int) atom1376) := by
  rw [SparsePolynomial.eval_scale, eval_atom1376]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1376Coded : CoefficientMerge.Poly := [(3706, 1)]
theorem atom1376Coded_decode : atom1376 = SparsePolynomial.decodeCubic 21 atom1376Coded := by decide +kernel
theorem atom1376Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (770276908800 : Int) atom1376Coded) := by
  have h := atom1376_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1376Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1377 : SparsePolynomial.Poly := [([8,8,11], 1)]
theorem eval_atom1377 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1377 = ((g 8) * (g 8) * (g 11)) := by
  norm_num [atom1377, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1377_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1377) := by
  rw [SparsePolynomial.eval_scale, eval_atom1377]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1377Coded : CoefficientMerge.Poly := [(3707, 1)]
theorem atom1377Coded_decode : atom1377 = SparsePolynomial.decodeCubic 21 atom1377Coded := by decide +kernel
theorem atom1377Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1377Coded) := by
  have h := atom1377_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1377Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1378 : SparsePolynomial.Poly := [([8,8,15], 1)]
theorem eval_atom1378 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1378 = ((g 8) * (g 8) * (g 15)) := by
  norm_num [atom1378, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1378_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3093893233200 : Int) atom1378) := by
  rw [SparsePolynomial.eval_scale, eval_atom1378]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1378Coded : CoefficientMerge.Poly := [(3711, 1)]
theorem atom1378Coded_decode : atom1378 = SparsePolynomial.decodeCubic 21 atom1378Coded := by decide +kernel
theorem atom1378Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3093893233200 : Int) atom1378Coded) := by
  have h := atom1378_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1378Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1379 : SparsePolynomial.Poly := [([8,9,9], 1)]
theorem eval_atom1379 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1379 = ((g 8) * (g 9) * (g 9)) := by
  norm_num [atom1379, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1379_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1414429430400 : Int) atom1379) := by
  rw [SparsePolynomial.eval_scale, eval_atom1379]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1379Coded : CoefficientMerge.Poly := [(3726, 1)]
theorem atom1379Coded_decode : atom1379 = SparsePolynomial.decodeCubic 21 atom1379Coded := by decide +kernel
theorem atom1379Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1414429430400 : Int) atom1379Coded) := by
  have h := atom1379_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1379Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1380 : SparsePolynomial.Poly := [([8,9,10], 1)]
theorem eval_atom1380 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1380 = ((g 8) * (g 9) * (g 10)) := by
  norm_num [atom1380, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1380_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (518028134400 : Int) atom1380) := by
  rw [SparsePolynomial.eval_scale, eval_atom1380]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1380Coded : CoefficientMerge.Poly := [(3727, 1)]
theorem atom1380Coded_decode : atom1380 = SparsePolynomial.decodeCubic 21 atom1380Coded := by decide +kernel
theorem atom1380Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (518028134400 : Int) atom1380Coded) := by
  have h := atom1380_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1380Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1381 : SparsePolynomial.Poly := [([8,9,13], 1)]
theorem eval_atom1381 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1381 = ((g 8) * (g 9) * (g 13)) := by
  norm_num [atom1381, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1381_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1381) := by
  rw [SparsePolynomial.eval_scale, eval_atom1381]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1381Coded : CoefficientMerge.Poly := [(3730, 1)]
theorem atom1381Coded_decode : atom1381 = SparsePolynomial.decodeCubic 21 atom1381Coded := by decide +kernel
theorem atom1381Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1381Coded) := by
  have h := atom1381_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1381Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1382 : SparsePolynomial.Poly := [([8,9,14], 1)]
theorem eval_atom1382 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1382 = ((g 8) * (g 9) * (g 14)) := by
  norm_num [atom1382, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1382_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (854359833600 : Int) atom1382) := by
  rw [SparsePolynomial.eval_scale, eval_atom1382]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1382Coded : CoefficientMerge.Poly := [(3731, 1)]
theorem atom1382Coded_decode : atom1382 = SparsePolynomial.decodeCubic 21 atom1382Coded := by decide +kernel
theorem atom1382Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (854359833600 : Int) atom1382Coded) := by
  have h := atom1382_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1382Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1383 : SparsePolynomial.Poly := [([8,9,15], 1)]
theorem eval_atom1383 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1383 = ((g 8) * (g 9) * (g 15)) := by
  norm_num [atom1383, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1383_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5687746762320 : Int) atom1383) := by
  rw [SparsePolynomial.eval_scale, eval_atom1383]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1383Coded : CoefficientMerge.Poly := [(3732, 1)]
theorem atom1383Coded_decode : atom1383 = SparsePolynomial.decodeCubic 21 atom1383Coded := by decide +kernel
theorem atom1383Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5687746762320 : Int) atom1383Coded) := by
  have h := atom1383_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1383Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1384 : SparsePolynomial.Poly := [([8,9,17], 1)]
theorem eval_atom1384 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1384 = ((g 8) * (g 9) * (g 17)) := by
  norm_num [atom1384, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1384_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2944323370800 : Int) atom1384) := by
  rw [SparsePolynomial.eval_scale, eval_atom1384]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1384Coded : CoefficientMerge.Poly := [(3734, 1)]
theorem atom1384Coded_decode : atom1384 = SparsePolynomial.decodeCubic 21 atom1384Coded := by decide +kernel
theorem atom1384Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2944323370800 : Int) atom1384Coded) := by
  have h := atom1384_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1384Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1385 : SparsePolynomial.Poly := [([8,9,18], 1)]
theorem eval_atom1385 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1385 = ((g 8) * (g 9) * (g 18)) := by
  norm_num [atom1385, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1385_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5786258284800 : Int) atom1385) := by
  rw [SparsePolynomial.eval_scale, eval_atom1385]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1385Coded : CoefficientMerge.Poly := [(3735, 1)]
theorem atom1385Coded_decode : atom1385 = SparsePolynomial.decodeCubic 21 atom1385Coded := by decide +kernel
theorem atom1385Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5786258284800 : Int) atom1385Coded) := by
  have h := atom1385_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1385Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1386 : SparsePolynomial.Poly := [([8,9,19], 1)]
theorem eval_atom1386 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1386 = ((g 8) * (g 9) * (g 19)) := by
  norm_num [atom1386, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1386_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11171238059520 : Int) atom1386) := by
  rw [SparsePolynomial.eval_scale, eval_atom1386]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1386Coded : CoefficientMerge.Poly := [(3736, 1)]
theorem atom1386Coded_decode : atom1386 = SparsePolynomial.decodeCubic 21 atom1386Coded := by decide +kernel
theorem atom1386Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11171238059520 : Int) atom1386Coded) := by
  have h := atom1386_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1386Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1387 : SparsePolynomial.Poly := [([8,9,20], 1)]
theorem eval_atom1387 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1387 = ((g 8) * (g 9) * (g 20)) := by
  norm_num [atom1387, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1387_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17391151612800 : Int) atom1387) := by
  rw [SparsePolynomial.eval_scale, eval_atom1387]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1387Coded : CoefficientMerge.Poly := [(3737, 1)]
theorem atom1387Coded_decode : atom1387 = SparsePolynomial.decodeCubic 21 atom1387Coded := by decide +kernel
theorem atom1387Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17391151612800 : Int) atom1387Coded) := by
  have h := atom1387_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1387Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1388 : SparsePolynomial.Poly := [([8,10,10], 1)]
theorem eval_atom1388 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1388 = ((g 8) * (g 10) * (g 10)) := by
  norm_num [atom1388, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1388_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1834844054400 : Int) atom1388) := by
  rw [SparsePolynomial.eval_scale, eval_atom1388]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1388Coded : CoefficientMerge.Poly := [(3748, 1)]
theorem atom1388Coded_decode : atom1388 = SparsePolynomial.decodeCubic 21 atom1388Coded := by decide +kernel
theorem atom1388Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1834844054400 : Int) atom1388Coded) := by
  have h := atom1388_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1388Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1389 : SparsePolynomial.Poly := [([8,10,11], 1)]
theorem eval_atom1389 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1389 = ((g 8) * (g 10) * (g 11)) := by
  norm_num [atom1389, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1389_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2647162425600 : Int) atom1389) := by
  rw [SparsePolynomial.eval_scale, eval_atom1389]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1389Coded : CoefficientMerge.Poly := [(3749, 1)]
theorem atom1389Coded_decode : atom1389 = SparsePolynomial.decodeCubic 21 atom1389Coded := by decide +kernel
theorem atom1389Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2647162425600 : Int) atom1389Coded) := by
  have h := atom1389_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1389Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1390 : SparsePolynomial.Poly := [([8,10,12], 1)]
theorem eval_atom1390 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1390 = ((g 8) * (g 10) * (g 12)) := by
  norm_num [atom1390, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1390_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2478996576000 : Int) atom1390) := by
  rw [SparsePolynomial.eval_scale, eval_atom1390]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1390Coded : CoefficientMerge.Poly := [(3750, 1)]
theorem atom1390Coded_decode : atom1390 = SparsePolynomial.decodeCubic 21 atom1390Coded := by decide +kernel
theorem atom1390Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2478996576000 : Int) atom1390Coded) := by
  have h := atom1390_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1390Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1391 : SparsePolynomial.Poly := [([8,10,13], 1)]
theorem eval_atom1391 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1391 = ((g 8) * (g 10) * (g 13)) := by
  norm_num [atom1391, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1391_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3165190560000 : Int) atom1391) := by
  rw [SparsePolynomial.eval_scale, eval_atom1391]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1391Coded : CoefficientMerge.Poly := [(3751, 1)]
theorem atom1391Coded_decode : atom1391 = SparsePolynomial.decodeCubic 21 atom1391Coded := by decide +kernel
theorem atom1391Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3165190560000 : Int) atom1391Coded) := by
  have h := atom1391_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1391Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1392 : SparsePolynomial.Poly := [([8,10,14], 1)]
theorem eval_atom1392 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1392 = ((g 8) * (g 10) * (g 14)) := by
  norm_num [atom1392, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1392_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3851384544000 : Int) atom1392) := by
  rw [SparsePolynomial.eval_scale, eval_atom1392]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1392Coded : CoefficientMerge.Poly := [(3752, 1)]
theorem atom1392Coded_decode : atom1392 = SparsePolynomial.decodeCubic 21 atom1392Coded := by decide +kernel
theorem atom1392Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3851384544000 : Int) atom1392Coded) := by
  have h := atom1392_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1392Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1393 : SparsePolynomial.Poly := [([8,10,15], 1)]
theorem eval_atom1393 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1393 = ((g 8) * (g 10) * (g 15)) := by
  norm_num [atom1393, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1393_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7803362548800 : Int) atom1393) := by
  rw [SparsePolynomial.eval_scale, eval_atom1393]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1393Coded : CoefficientMerge.Poly := [(3753, 1)]
theorem atom1393Coded_decode : atom1393 = SparsePolynomial.decodeCubic 21 atom1393Coded := by decide +kernel
theorem atom1393Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7803362548800 : Int) atom1393Coded) := by
  have h := atom1393_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1393Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1394 : SparsePolynomial.Poly := [([8,10,16], 1)]
theorem eval_atom1394 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1394 = ((g 8) * (g 10) * (g 16)) := by
  norm_num [atom1394, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1394_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2139543982800 : Int) atom1394) := by
  rw [SparsePolynomial.eval_scale, eval_atom1394]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1394Coded : CoefficientMerge.Poly := [(3754, 1)]
theorem atom1394Coded_decode : atom1394 = SparsePolynomial.decodeCubic 21 atom1394Coded := by decide +kernel
theorem atom1394Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2139543982800 : Int) atom1394Coded) := by
  have h := atom1394_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1394Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1395 : SparsePolynomial.Poly := [([8,10,17], 1)]
theorem eval_atom1395 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1395 = ((g 8) * (g 10) * (g 17)) := by
  norm_num [atom1395, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1395_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9372338136000 : Int) atom1395) := by
  rw [SparsePolynomial.eval_scale, eval_atom1395]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1395Coded : CoefficientMerge.Poly := [(3755, 1)]
theorem atom1395Coded_decode : atom1395 = SparsePolynomial.decodeCubic 21 atom1395Coded := by decide +kernel
theorem atom1395Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9372338136000 : Int) atom1395Coded) := by
  have h := atom1395_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1395Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1396 : SparsePolynomial.Poly := [([8,10,18], 1)]
theorem eval_atom1396 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1396 = ((g 8) * (g 10) * (g 18)) := by
  norm_num [atom1396, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1396_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11410652912400 : Int) atom1396) := by
  rw [SparsePolynomial.eval_scale, eval_atom1396]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1396Coded : CoefficientMerge.Poly := [(3756, 1)]
theorem atom1396Coded_decode : atom1396 = SparsePolynomial.decodeCubic 21 atom1396Coded := by decide +kernel
theorem atom1396Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11410652912400 : Int) atom1396Coded) := by
  have h := atom1396_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1396Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1397 : SparsePolynomial.Poly := [([8,10,19], 1)]
theorem eval_atom1397 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1397 = ((g 8) * (g 10) * (g 19)) := by
  norm_num [atom1397, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1397_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20176096474800 : Int) atom1397) := by
  rw [SparsePolynomial.eval_scale, eval_atom1397]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1397Coded : CoefficientMerge.Poly := [(3757, 1)]
theorem atom1397Coded_decode : atom1397 = SparsePolynomial.decodeCubic 21 atom1397Coded := by decide +kernel
theorem atom1397Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20176096474800 : Int) atom1397Coded) := by
  have h := atom1397_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1397Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1398 : SparsePolynomial.Poly := [([8,10,20], 1)]
theorem eval_atom1398 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1398 = ((g 8) * (g 10) * (g 20)) := by
  norm_num [atom1398, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1398_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30348257839200 : Int) atom1398) := by
  rw [SparsePolynomial.eval_scale, eval_atom1398]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1398Coded : CoefficientMerge.Poly := [(3758, 1)]
theorem atom1398Coded_decode : atom1398 = SparsePolynomial.decodeCubic 21 atom1398Coded := by decide +kernel
theorem atom1398Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30348257839200 : Int) atom1398Coded) := by
  have h := atom1398_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1398Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1399 : SparsePolynomial.Poly := [([8,11,11], 1)]
theorem eval_atom1399 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1399 = ((g 8) * (g 11) * (g 11)) := by
  norm_num [atom1399, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1399_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3543563721600 : Int) atom1399) := by
  rw [SparsePolynomial.eval_scale, eval_atom1399]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1399Coded : CoefficientMerge.Poly := [(3770, 1)]
theorem atom1399Coded_decode : atom1399 = SparsePolynomial.decodeCubic 21 atom1399Coded := by decide +kernel
theorem atom1399Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3543563721600 : Int) atom1399Coded) := by
  have h := atom1399_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1399Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1400 : SparsePolynomial.Poly := [([8,11,12], 1)]
theorem eval_atom1400 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1400 = ((g 8) * (g 11) * (g 12)) := by
  norm_num [atom1400, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1400_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5560104211200 : Int) atom1400) := by
  rw [SparsePolynomial.eval_scale, eval_atom1400]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1400Coded : CoefficientMerge.Poly := [(3771, 1)]
theorem atom1400Coded_decode : atom1400 = SparsePolynomial.decodeCubic 21 atom1400Coded := by decide +kernel
theorem atom1400Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5560104211200 : Int) atom1400Coded) := by
  have h := atom1400_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1400Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1401 : SparsePolynomial.Poly := [([8,11,13], 1)]
theorem eval_atom1401 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1401 = ((g 8) * (g 11) * (g 13)) := by
  norm_num [atom1401, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1401_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6337146412800 : Int) atom1401) := by
  rw [SparsePolynomial.eval_scale, eval_atom1401]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1401Coded : CoefficientMerge.Poly := [(3772, 1)]
theorem atom1401Coded_decode : atom1401 = SparsePolynomial.decodeCubic 21 atom1401Coded := by decide +kernel
theorem atom1401Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6337146412800 : Int) atom1401Coded) := by
  have h := atom1401_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1401Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1402 : SparsePolynomial.Poly := [([8,11,14], 1)]
theorem eval_atom1402 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1402 = ((g 8) * (g 11) * (g 14)) := by
  norm_num [atom1402, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1402_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7114188614400 : Int) atom1402) := by
  rw [SparsePolynomial.eval_scale, eval_atom1402]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1402Coded : CoefficientMerge.Poly := [(3773, 1)]
theorem atom1402Coded_decode : atom1402 = SparsePolynomial.decodeCubic 21 atom1402Coded := by decide +kernel
theorem atom1402Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7114188614400 : Int) atom1402Coded) := by
  have h := atom1402_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1402Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1403 : SparsePolynomial.Poly := [([8,11,15], 1)]
theorem eval_atom1403 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1403 = ((g 8) * (g 11) * (g 15)) := by
  norm_num [atom1403, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1403_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12510442929600 : Int) atom1403) := by
  rw [SparsePolynomial.eval_scale, eval_atom1403]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1403Coded : CoefficientMerge.Poly := [(3774, 1)]
theorem atom1403Coded_decode : atom1403 = SparsePolynomial.decodeCubic 21 atom1403Coded := by decide +kernel
theorem atom1403Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12510442929600 : Int) atom1403Coded) := by
  have h := atom1403_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1403Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1404 : SparsePolynomial.Poly := [([8,11,16], 1)]
theorem eval_atom1404 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1404 = ((g 8) * (g 11) * (g 16)) := by
  norm_num [atom1404, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1404_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8456065254000 : Int) atom1404) := by
  rw [SparsePolynomial.eval_scale, eval_atom1404]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1404Coded : CoefficientMerge.Poly := [(3775, 1)]
theorem atom1404Coded_decode : atom1404 = SparsePolynomial.decodeCubic 21 atom1404Coded := by decide +kernel
theorem atom1404Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8456065254000 : Int) atom1404Coded) := by
  have h := atom1404_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1404Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1405 : SparsePolynomial.Poly := [([8,11,17], 1)]
theorem eval_atom1405 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1405 = ((g 8) * (g 11) * (g 17)) := by
  norm_num [atom1405, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1405_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19774108468800 : Int) atom1405) := by
  rw [SparsePolynomial.eval_scale, eval_atom1405]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1405Coded : CoefficientMerge.Poly := [(3776, 1)]
theorem atom1405Coded_decode : atom1405 = SparsePolynomial.decodeCubic 21 atom1405Coded := by decide +kernel
theorem atom1405Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19774108468800 : Int) atom1405Coded) := by
  have h := atom1405_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1405Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1406 : SparsePolynomial.Poly := [([8,11,18], 1)]
theorem eval_atom1406 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1406 = ((g 8) * (g 11) * (g 18)) := by
  norm_num [atom1406, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1406_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20318281326000 : Int) atom1406) := by
  rw [SparsePolynomial.eval_scale, eval_atom1406]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1406Coded : CoefficientMerge.Poly := [(3777, 1)]
theorem atom1406Coded_decode : atom1406 = SparsePolynomial.decodeCubic 21 atom1406Coded := by decide +kernel
theorem atom1406Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20318281326000 : Int) atom1406Coded) := by
  have h := atom1406_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1406Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1407 : SparsePolynomial.Poly := [([8,11,19], 1)]
theorem eval_atom1407 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1407 = ((g 8) * (g 11) * (g 19)) := by
  norm_num [atom1407, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1407_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30113920746000 : Int) atom1407) := by
  rw [SparsePolynomial.eval_scale, eval_atom1407]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1407Coded : CoefficientMerge.Poly := [(3778, 1)]
theorem atom1407Coded_decode : atom1407 = SparsePolynomial.decodeCubic 21 atom1407Coded := by decide +kernel
theorem atom1407Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30113920746000 : Int) atom1407Coded) := by
  have h := atom1407_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1407Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1408 : SparsePolynomial.Poly := [([8,11,20], 1)]
theorem eval_atom1408 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1408 = ((g 8) * (g 11) * (g 20)) := by
  norm_num [atom1408, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1408_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40982814885600 : Int) atom1408) := by
  rw [SparsePolynomial.eval_scale, eval_atom1408]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1408Coded : CoefficientMerge.Poly := [(3779, 1)]
theorem atom1408Coded_decode : atom1408 = SparsePolynomial.decodeCubic 21 atom1408Coded := by decide +kernel
theorem atom1408Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40982814885600 : Int) atom1408Coded) := by
  have h := atom1408_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1408Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1409 : SparsePolynomial.Poly := [([8,12,12], 1)]
theorem eval_atom1409 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1409 = ((g 8) * (g 12) * (g 12)) := by
  norm_num [atom1409, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1409_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5174965756800 : Int) atom1409) := by
  rw [SparsePolynomial.eval_scale, eval_atom1409]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1409Coded : CoefficientMerge.Poly := [(3792, 1)]
theorem atom1409Coded_decode : atom1409 = SparsePolynomial.decodeCubic 21 atom1409Coded := by decide +kernel
theorem atom1409Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5174965756800 : Int) atom1409Coded) := by
  have h := atom1409_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1409Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1410 : SparsePolynomial.Poly := [([8,12,13], 1)]
theorem eval_atom1410 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1410 = ((g 8) * (g 12) * (g 13)) := by
  norm_num [atom1410, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1410_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10622476166400 : Int) atom1410) := by
  rw [SparsePolynomial.eval_scale, eval_atom1410]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1410Coded : CoefficientMerge.Poly := [(3793, 1)]
theorem atom1410Coded_decode : atom1410 = SparsePolynomial.decodeCubic 21 atom1410Coded := by decide +kernel
theorem atom1410Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10622476166400 : Int) atom1410Coded) := by
  have h := atom1410_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1410Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1411 : SparsePolynomial.Poly := [([8,12,14], 1)]
theorem eval_atom1411 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1411 = ((g 8) * (g 12) * (g 14)) := by
  norm_num [atom1411, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1411_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11322200736000 : Int) atom1411) := by
  rw [SparsePolynomial.eval_scale, eval_atom1411]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1411Coded : CoefficientMerge.Poly := [(3794, 1)]
theorem atom1411Coded_decode : atom1411 = SparsePolynomial.decodeCubic 21 atom1411Coded := by decide +kernel
theorem atom1411Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11322200736000 : Int) atom1411Coded) := by
  have h := atom1411_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1411Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1412 : SparsePolynomial.Poly := [([8,12,15], 1)]
theorem eval_atom1412 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1412 = ((g 8) * (g 12) * (g 15)) := by
  norm_num [atom1412, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1412_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14101152139200 : Int) atom1412) := by
  rw [SparsePolynomial.eval_scale, eval_atom1412]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1412Coded : CoefficientMerge.Poly := [(3795, 1)]
theorem atom1412Coded_decode : atom1412 = SparsePolynomial.decodeCubic 21 atom1412Coded := by decide +kernel
theorem atom1412Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14101152139200 : Int) atom1412Coded) := by
  have h := atom1412_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1412Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1413 : SparsePolynomial.Poly := [([8,12,16], 1)]
theorem eval_atom1413 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1413 = ((g 8) * (g 12) * (g 16)) := by
  norm_num [atom1413, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1413_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13619552332400 : Int) atom1413) := by
  rw [SparsePolynomial.eval_scale, eval_atom1413]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1413Coded : CoefficientMerge.Poly := [(3796, 1)]
theorem atom1413Coded_decode : atom1413 = SparsePolynomial.decodeCubic 21 atom1413Coded := by decide +kernel
theorem atom1413Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13619552332400 : Int) atom1413Coded) := by
  have h := atom1413_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1413Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1414 : SparsePolynomial.Poly := [([8,12,17], 1)]
theorem eval_atom1414 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1414 = ((g 8) * (g 12) * (g 17)) := by
  norm_num [atom1414, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1414_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25094037416000 : Int) atom1414) := by
  rw [SparsePolynomial.eval_scale, eval_atom1414]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1414Coded : CoefficientMerge.Poly := [(3797, 1)]
theorem atom1414Coded_decode : atom1414 = SparsePolynomial.decodeCubic 21 atom1414Coded := by decide +kernel
theorem atom1414Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25094037416000 : Int) atom1414Coded) := by
  have h := atom1414_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1414Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1415 : SparsePolynomial.Poly := [([8,12,18], 1)]
theorem eval_atom1415 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1415 = ((g 8) * (g 12) * (g 18)) := by
  norm_num [atom1415, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1415_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27327261530800 : Int) atom1415) := by
  rw [SparsePolynomial.eval_scale, eval_atom1415]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1415Coded : CoefficientMerge.Poly := [(3798, 1)]
theorem atom1415Coded_decode : atom1415 = SparsePolynomial.decodeCubic 21 atom1415Coded := by decide +kernel
theorem atom1415Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27327261530800 : Int) atom1415Coded) := by
  have h := atom1415_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1415Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1416 : SparsePolynomial.Poly := [([8,12,19], 1)]
theorem eval_atom1416 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1416 = ((g 8) * (g 12) * (g 19)) := by
  norm_num [atom1416, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1416_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37107275293200 : Int) atom1416) := by
  rw [SparsePolynomial.eval_scale, eval_atom1416]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1416Coded : CoefficientMerge.Poly := [(3799, 1)]
theorem atom1416Coded_decode : atom1416 = SparsePolynomial.decodeCubic 21 atom1416Coded := by decide +kernel
theorem atom1416Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37107275293200 : Int) atom1416Coded) := by
  have h := atom1416_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1416Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1417 : SparsePolynomial.Poly := [([8,12,20], 1)]
theorem eval_atom1417 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1417 = ((g 8) * (g 12) * (g 20)) := by
  norm_num [atom1417, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1417_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48530465474400 : Int) atom1417) := by
  rw [SparsePolynomial.eval_scale, eval_atom1417]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1417Coded : CoefficientMerge.Poly := [(3800, 1)]
theorem atom1417Coded_decode : atom1417 = SparsePolynomial.decodeCubic 21 atom1417Coded := by decide +kernel
theorem atom1417Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48530465474400 : Int) atom1417Coded) := by
  have h := atom1417_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1417Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1418 : SparsePolynomial.Poly := [([8,13,13], 1)]
theorem eval_atom1418 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1418 = ((g 8) * (g 13) * (g 13)) := by
  norm_num [atom1418, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1418_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8314429795200 : Int) atom1418) := by
  rw [SparsePolynomial.eval_scale, eval_atom1418]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1418Coded : CoefficientMerge.Poly := [(3814, 1)]
theorem atom1418Coded_decode : atom1418 = SparsePolynomial.decodeCubic 21 atom1418Coded := by decide +kernel
theorem atom1418Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8314429795200 : Int) atom1418Coded) := by
  have h := atom1418_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1418Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1419 : SparsePolynomial.Poly := [([8,13,14], 1)]
theorem eval_atom1419 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1419 = ((g 8) * (g 13) * (g 14)) := by
  norm_num [atom1419, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1419_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15912566956800 : Int) atom1419) := by
  rw [SparsePolynomial.eval_scale, eval_atom1419]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1419Coded : CoefficientMerge.Poly := [(3815, 1)]
theorem atom1419Coded_decode : atom1419 = SparsePolynomial.decodeCubic 21 atom1419Coded := by decide +kernel
theorem atom1419Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15912566956800 : Int) atom1419Coded) := by
  have h := atom1419_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1419Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1420 : SparsePolynomial.Poly := [([8,13,15], 1)]
theorem eval_atom1420 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1420 = ((g 8) * (g 13) * (g 15)) := by
  norm_num [atom1420, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1420_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19319098982400 : Int) atom1420) := by
  rw [SparsePolynomial.eval_scale, eval_atom1420]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1420Coded : CoefficientMerge.Poly := [(3816, 1)]
theorem atom1420Coded_decode : atom1420 = SparsePolynomial.decodeCubic 21 atom1420Coded := by decide +kernel
theorem atom1420Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19319098982400 : Int) atom1420Coded) := by
  have h := atom1420_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1420Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1421 : SparsePolynomial.Poly := [([8,13,16], 1)]
theorem eval_atom1421 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1421 = ((g 8) * (g 13) * (g 16)) := by
  norm_num [atom1421, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1421_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19329077214000 : Int) atom1421) := by
  rw [SparsePolynomial.eval_scale, eval_atom1421]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1421Coded : CoefficientMerge.Poly := [(3817, 1)]
theorem atom1421Coded_decode : atom1421 = SparsePolynomial.decodeCubic 21 atom1421Coded := by decide +kernel
theorem atom1421Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19329077214000 : Int) atom1421Coded) := by
  have h := atom1421_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1421Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1422 : SparsePolynomial.Poly := [([8,13,17], 1)]
theorem eval_atom1422 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1422 = ((g 8) * (g 13) * (g 17)) := by
  norm_num [atom1422, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1422_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34558073524800 : Int) atom1422) := by
  rw [SparsePolynomial.eval_scale, eval_atom1422]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1422Coded : CoefficientMerge.Poly := [(3818, 1)]
theorem atom1422Coded_decode : atom1422 = SparsePolynomial.decodeCubic 21 atom1422Coded := by decide +kernel
theorem atom1422Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34558073524800 : Int) atom1422Coded) := by
  have h := atom1422_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1422Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1423 : SparsePolynomial.Poly := [([8,13,18], 1)]
theorem eval_atom1423 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1423 = ((g 8) * (g 13) * (g 18)) := by
  norm_num [atom1423, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1423_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38809323630000 : Int) atom1423) := by
  rw [SparsePolynomial.eval_scale, eval_atom1423]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1423Coded : CoefficientMerge.Poly := [(3819, 1)]
theorem atom1423Coded_decode : atom1423 = SparsePolynomial.decodeCubic 21 atom1423Coded := by decide +kernel
theorem atom1423Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38809323630000 : Int) atom1423Coded) := by
  have h := atom1423_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1423Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1424 : SparsePolynomial.Poly := [([8,13,19], 1)]
theorem eval_atom1424 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1424 = ((g 8) * (g 13) * (g 19)) := by
  norm_num [atom1424, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1424_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42738457266000 : Int) atom1424) := by
  rw [SparsePolynomial.eval_scale, eval_atom1424]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1424Coded : CoefficientMerge.Poly := [(3820, 1)]
theorem atom1424Coded_decode : atom1424 = SparsePolynomial.decodeCubic 21 atom1424Coded := by decide +kernel
theorem atom1424Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42738457266000 : Int) atom1424Coded) := by
  have h := atom1424_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1424Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1425 : SparsePolynomial.Poly := [([8,13,20], 1)]
theorem eval_atom1425 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1425 = ((g 8) * (g 13) * (g 20)) := by
  norm_num [atom1425, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1425_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60582834597600 : Int) atom1425) := by
  rw [SparsePolynomial.eval_scale, eval_atom1425]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1425Coded : CoefficientMerge.Poly := [(3821, 1)]
theorem atom1425Coded_decode : atom1425 = SparsePolynomial.decodeCubic 21 atom1425Coded := by decide +kernel
theorem atom1425Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (60582834597600 : Int) atom1425Coded) := by
  have h := atom1425_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1425Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1426 : SparsePolynomial.Poly := [([8,14,14], 1)]
theorem eval_atom1426 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1426 = ((g 8) * (g 14) * (g 14)) := by
  norm_num [atom1426, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1426_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12733408598400 : Int) atom1426) := by
  rw [SparsePolynomial.eval_scale, eval_atom1426]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1426Coded : CoefficientMerge.Poly := [(3836, 1)]
theorem atom1426Coded_decode : atom1426 = SparsePolynomial.decodeCubic 21 atom1426Coded := by decide +kernel
theorem atom1426Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12733408598400 : Int) atom1426Coded) := by
  have h := atom1426_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1426Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1427 : SparsePolynomial.Poly := [([8,14,15], 1)]
theorem eval_atom1427 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1427 = ((g 8) * (g 14) * (g 15)) := by
  norm_num [atom1427, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1427_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24425203723200 : Int) atom1427) := by
  rw [SparsePolynomial.eval_scale, eval_atom1427]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1427Coded : CoefficientMerge.Poly := [(3837, 1)]
theorem atom1427Coded_decode : atom1427 = SparsePolynomial.decodeCubic 21 atom1427Coded := by decide +kernel
theorem atom1427Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24425203723200 : Int) atom1427Coded) := by
  have h := atom1427_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1427Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1428 : SparsePolynomial.Poly := [([8,14,16], 1)]
theorem eval_atom1428 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1428 = ((g 8) * (g 14) * (g 16)) := by
  norm_num [atom1428, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1428_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24919452658800 : Int) atom1428) := by
  rw [SparsePolynomial.eval_scale, eval_atom1428]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1428Coded : CoefficientMerge.Poly := [(3838, 1)]
theorem atom1428Coded_decode : atom1428 = SparsePolynomial.decodeCubic 21 atom1428Coded := by decide +kernel
theorem atom1428Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24919452658800 : Int) atom1428Coded) := by
  have h := atom1428_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1428Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1429 : SparsePolynomial.Poly := [([8,14,17], 1)]
theorem eval_atom1429 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1429 = ((g 8) * (g 14) * (g 17)) := by
  norm_num [atom1429, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1429_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46215639489600 : Int) atom1429) := by
  rw [SparsePolynomial.eval_scale, eval_atom1429]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1429Coded : CoefficientMerge.Poly := [(3839, 1)]
theorem atom1429Coded_decode : atom1429 = SparsePolynomial.decodeCubic 21 atom1429Coded := by decide +kernel
theorem atom1429Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46215639489600 : Int) atom1429Coded) := by
  have h := atom1429_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1429Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1430 : SparsePolynomial.Poly := [([8,14,18], 1)]
theorem eval_atom1430 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1430 = ((g 8) * (g 14) * (g 18)) := by
  norm_num [atom1430, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1430_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52704268570800 : Int) atom1430) := by
  rw [SparsePolynomial.eval_scale, eval_atom1430]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1430Coded : CoefficientMerge.Poly := [(3840, 1)]
theorem atom1430Coded_decode : atom1430 = SparsePolynomial.decodeCubic 21 atom1430Coded := by decide +kernel
theorem atom1430Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52704268570800 : Int) atom1430Coded) := by
  have h := atom1430_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1430Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1431 : SparsePolynomial.Poly := [([8,14,19], 1)]
theorem eval_atom1431 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1431 = ((g 8) * (g 14) * (g 19)) := by
  norm_num [atom1431, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1431_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52820365827600 : Int) atom1431) := by
  rw [SparsePolynomial.eval_scale, eval_atom1431]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1431Coded : CoefficientMerge.Poly := [(3841, 1)]
theorem atom1431Coded_decode : atom1431 = SparsePolynomial.decodeCubic 21 atom1431Coded := by decide +kernel
theorem atom1431Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52820365827600 : Int) atom1431Coded) := by
  have h := atom1431_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1431Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1432 : SparsePolynomial.Poly := [([8,14,20], 1)]
theorem eval_atom1432 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1432 = ((g 8) * (g 14) * (g 20)) := by
  norm_num [atom1432, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1432_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77218206357600 : Int) atom1432) := by
  rw [SparsePolynomial.eval_scale, eval_atom1432]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1432Coded : CoefficientMerge.Poly := [(3842, 1)]
theorem atom1432Coded_decode : atom1432 = SparsePolynomial.decodeCubic 21 atom1432Coded := by decide +kernel
theorem atom1432Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (77218206357600 : Int) atom1432Coded) := by
  have h := atom1432_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1432Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1433 : SparsePolynomial.Poly := [([8,15,15], 1)]
theorem eval_atom1433 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1433 = ((g 8) * (g 15) * (g 15)) := by
  norm_num [atom1433, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1433_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19383530342400 : Int) atom1433) := by
  rw [SparsePolynomial.eval_scale, eval_atom1433]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1433Coded : CoefficientMerge.Poly := [(3858, 1)]
theorem atom1433Coded_decode : atom1433 = SparsePolynomial.decodeCubic 21 atom1433Coded := by decide +kernel
theorem atom1433Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19383530342400 : Int) atom1433Coded) := by
  have h := atom1433_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1433Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1434 : SparsePolynomial.Poly := [([8,15,16], 1)]
theorem eval_atom1434 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1434 = ((g 8) * (g 15) * (g 16)) := by
  norm_num [atom1434, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1434_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39580818694200 : Int) atom1434) := by
  rw [SparsePolynomial.eval_scale, eval_atom1434]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1434Coded : CoefficientMerge.Poly := [(3859, 1)]
theorem atom1434Coded_decode : atom1434 = SparsePolynomial.decodeCubic 21 atom1434Coded := by decide +kernel
theorem atom1434Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39580818694200 : Int) atom1434Coded) := by
  have h := atom1434_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1434Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1435 : SparsePolynomial.Poly := [([8,15,17], 1)]
theorem eval_atom1435 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1435 = ((g 8) * (g 15) * (g 17)) := by
  norm_num [atom1435, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1435_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (66724705152000 : Int) atom1435) := by
  rw [SparsePolynomial.eval_scale, eval_atom1435]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1435Coded : CoefficientMerge.Poly := [(3860, 1)]
theorem atom1435Coded_decode : atom1435 = SparsePolynomial.decodeCubic 21 atom1435Coded := by decide +kernel
theorem atom1435Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (66724705152000 : Int) atom1435Coded) := by
  have h := atom1435_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1435Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1436 : SparsePolynomial.Poly := [([8,15,18], 1)]
theorem eval_atom1436 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1436 = ((g 8) * (g 15) * (g 18)) := by
  norm_num [atom1436, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1436_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (71113667221800 : Int) atom1436) := by
  rw [SparsePolynomial.eval_scale, eval_atom1436]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1436Coded : CoefficientMerge.Poly := [(3861, 1)]
theorem atom1436Coded_decode : atom1436 = SparsePolynomial.decodeCubic 21 atom1436Coded := by decide +kernel
theorem atom1436Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (71113667221800 : Int) atom1436Coded) := by
  have h := atom1436_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1436Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1437 : SparsePolynomial.Poly := [([8,15,19], 1)]
theorem eval_atom1437 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1437 = ((g 8) * (g 15) * (g 19)) := by
  norm_num [atom1437, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1437_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53763791949000 : Int) atom1437) := by
  rw [SparsePolynomial.eval_scale, eval_atom1437]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1437Coded : CoefficientMerge.Poly := [(3862, 1)]
theorem atom1437Coded_decode : atom1437 = SparsePolynomial.decodeCubic 21 atom1437Coded := by decide +kernel
theorem atom1437Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53763791949000 : Int) atom1437Coded) := by
  have h := atom1437_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1437Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1438 : SparsePolynomial.Poly := [([8,15,20], 1)]
theorem eval_atom1438 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1438 = ((g 8) * (g 15) * (g 20)) := by
  norm_num [atom1438, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1438_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82935935850600 : Int) atom1438) := by
  rw [SparsePolynomial.eval_scale, eval_atom1438]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1438Coded : CoefficientMerge.Poly := [(3863, 1)]
theorem atom1438Coded_decode : atom1438 = SparsePolynomial.decodeCubic 21 atom1438Coded := by decide +kernel
theorem atom1438Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (82935935850600 : Int) atom1438Coded) := by
  have h := atom1438_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1438Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1439 : SparsePolynomial.Poly := [([8,16,16], 1)]
theorem eval_atom1439 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1439 = ((g 8) * (g 16) * (g 16)) := by
  norm_num [atom1439, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1439_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15952947010560 : Int) atom1439) := by
  rw [SparsePolynomial.eval_scale, eval_atom1439]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1439Coded : CoefficientMerge.Poly := [(3880, 1)]
theorem atom1439Coded_decode : atom1439 = SparsePolynomial.decodeCubic 21 atom1439Coded := by decide +kernel
theorem atom1439Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15952947010560 : Int) atom1439Coded) := by
  have h := atom1439_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1439Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1440 : SparsePolynomial.Poly := [([8,16,17], 1)]
theorem eval_atom1440 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1440 = ((g 8) * (g 16) * (g 17)) := by
  norm_num [atom1440, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1440_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56181592441800 : Int) atom1440) := by
  rw [SparsePolynomial.eval_scale, eval_atom1440]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1440Coded : CoefficientMerge.Poly := [(3881, 1)]
theorem atom1440Coded_decode : atom1440 = SparsePolynomial.decodeCubic 21 atom1440Coded := by decide +kernel
theorem atom1440Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (56181592441800 : Int) atom1440Coded) := by
  have h := atom1440_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1440Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1441 : SparsePolynomial.Poly := [([8,16,18], 1)]
theorem eval_atom1441 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1441 = ((g 8) * (g 16) * (g 18)) := by
  norm_num [atom1441, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1441_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64310888457900 : Int) atom1441) := by
  rw [SparsePolynomial.eval_scale, eval_atom1441]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1441Coded : CoefficientMerge.Poly := [(3882, 1)]
theorem atom1441Coded_decode : atom1441 = SparsePolynomial.decodeCubic 21 atom1441Coded := by decide +kernel
theorem atom1441Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (64310888457900 : Int) atom1441Coded) := by
  have h := atom1441_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1441Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1442 : SparsePolynomial.Poly := [([8,16,19], 1)]
theorem eval_atom1442 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1442 = ((g 8) * (g 16) * (g 19)) := by
  norm_num [atom1442, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1442_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46815859734000 : Int) atom1442) := by
  rw [SparsePolynomial.eval_scale, eval_atom1442]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1442Coded : CoefficientMerge.Poly := [(3883, 1)]
theorem atom1442Coded_decode : atom1442 = SparsePolynomial.decodeCubic 21 atom1442Coded := by decide +kernel
theorem atom1442Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46815859734000 : Int) atom1442Coded) := by
  have h := atom1442_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1442Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1443 : SparsePolynomial.Poly := [([8,16,20], 1)]
theorem eval_atom1443 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1443 = ((g 8) * (g 16) * (g 20)) := by
  norm_num [atom1443, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1443_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61853161781250 : Int) atom1443) := by
  rw [SparsePolynomial.eval_scale, eval_atom1443]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1443Coded : CoefficientMerge.Poly := [(3884, 1)]
theorem atom1443Coded_decode : atom1443 = SparsePolynomial.decodeCubic 21 atom1443Coded := by decide +kernel
theorem atom1443Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (61853161781250 : Int) atom1443Coded) := by
  have h := atom1443_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1443Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1444 : SparsePolynomial.Poly := [([8,17,17], 1)]
theorem eval_atom1444 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1444 = ((g 8) * (g 17) * (g 17)) := by
  norm_num [atom1444, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1444_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41682593433600 : Int) atom1444) := by
  rw [SparsePolynomial.eval_scale, eval_atom1444]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1444Coded : CoefficientMerge.Poly := [(3902, 1)]
theorem atom1444Coded_decode : atom1444 = SparsePolynomial.decodeCubic 21 atom1444Coded := by decide +kernel
theorem atom1444Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41682593433600 : Int) atom1444Coded) := by
  have h := atom1444_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1444Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1445 : SparsePolynomial.Poly := [([8,17,18], 1)]
theorem eval_atom1445 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1445 = ((g 8) * (g 17) * (g 18)) := by
  norm_num [atom1445, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1445_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (73028319197400 : Int) atom1445) := by
  rw [SparsePolynomial.eval_scale, eval_atom1445]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1445Coded : CoefficientMerge.Poly := [(3903, 1)]
theorem atom1445Coded_decode : atom1445 = SparsePolynomial.decodeCubic 21 atom1445Coded := by decide +kernel
theorem atom1445Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (73028319197400 : Int) atom1445Coded) := by
  have h := atom1445_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1445Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1446 : SparsePolynomial.Poly := [([8,17,19], 1)]
theorem eval_atom1446 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1446 = ((g 8) * (g 17) * (g 19)) := by
  norm_num [atom1446, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1446_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49453121621400 : Int) atom1446) := by
  rw [SparsePolynomial.eval_scale, eval_atom1446]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1446Coded : CoefficientMerge.Poly := [(3904, 1)]
theorem atom1446Coded_decode : atom1446 = SparsePolynomial.decodeCubic 21 atom1446Coded := by decide +kernel
theorem atom1446Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49453121621400 : Int) atom1446Coded) := by
  have h := atom1446_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1446Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1447 : SparsePolynomial.Poly := [([8,17,20], 1)]
theorem eval_atom1447 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1447 = ((g 8) * (g 17) * (g 20)) := by
  norm_num [atom1447, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1447_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54003049493400 : Int) atom1447) := by
  rw [SparsePolynomial.eval_scale, eval_atom1447]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1447Coded : CoefficientMerge.Poly := [(3905, 1)]
theorem atom1447Coded_decode : atom1447 = SparsePolynomial.decodeCubic 21 atom1447Coded := by decide +kernel
theorem atom1447Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (54003049493400 : Int) atom1447Coded) := by
  have h := atom1447_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1447Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1448 : SparsePolynomial.Poly := [([8,18,18], 1)]
theorem eval_atom1448 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1448 = ((g 8) * (g 18) * (g 18)) := by
  norm_num [atom1448, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1448_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25323261106500 : Int) atom1448) := by
  rw [SparsePolynomial.eval_scale, eval_atom1448]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1448Coded : CoefficientMerge.Poly := [(3924, 1)]
theorem atom1448Coded_decode : atom1448 = SparsePolynomial.decodeCubic 21 atom1448Coded := by decide +kernel
theorem atom1448Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25323261106500 : Int) atom1448Coded) := by
  have h := atom1448_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1448Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1449 : SparsePolynomial.Poly := [([8,18,19], 1)]
theorem eval_atom1449 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1449 = ((g 8) * (g 18) * (g 19)) := by
  norm_num [atom1449, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1449_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30034904980500 : Int) atom1449) := by
  rw [SparsePolynomial.eval_scale, eval_atom1449]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 8) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1449Coded : CoefficientMerge.Poly := [(3925, 1)]
theorem atom1449Coded_decode : atom1449 = SparsePolynomial.decodeCubic 21 atom1449Coded := by decide +kernel
theorem atom1449Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30034904980500 : Int) atom1449Coded) := by
  have h := atom1449_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1449Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1450 : SparsePolynomial.Poly := [([8,18,20], 1)]
theorem eval_atom1450 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1450 = ((g 8) * (g 18) * (g 20)) := by
  norm_num [atom1450, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1450_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36065647557450 : Int) atom1450) := by
  rw [SparsePolynomial.eval_scale, eval_atom1450]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1450Coded : CoefficientMerge.Poly := [(3926, 1)]
theorem atom1450Coded_decode : atom1450 = SparsePolynomial.decodeCubic 21 atom1450Coded := by decide +kernel
theorem atom1450Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36065647557450 : Int) atom1450Coded) := by
  have h := atom1450_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1450Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1451 : SparsePolynomial.Poly := [([8,19,20], 1)]
theorem eval_atom1451 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1451 = ((g 8) * (g 19) * (g 20)) := by
  norm_num [atom1451, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1451_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5439574781550 : Int) atom1451) := by
  rw [SparsePolynomial.eval_scale, eval_atom1451]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1451Coded : CoefficientMerge.Poly := [(3947, 1)]
theorem atom1451Coded_decode : atom1451 = SparsePolynomial.decodeCubic 21 atom1451Coded := by decide +kernel
theorem atom1451Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5439574781550 : Int) atom1451Coded) := by
  have h := atom1451_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1451Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1452 : SparsePolynomial.Poly := [([8,20,20], 1)]
theorem eval_atom1452 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1452 = ((g 8) * (g 20) * (g 20)) := by
  norm_num [atom1452, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1452_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3482925254550 : Int) atom1452) := by
  rw [SparsePolynomial.eval_scale, eval_atom1452]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1452Coded : CoefficientMerge.Poly := [(3968, 1)]
theorem atom1452Coded_decode : atom1452 = SparsePolynomial.decodeCubic 21 atom1452Coded := by decide +kernel
theorem atom1452Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3482925254550 : Int) atom1452Coded) := by
  have h := atom1452_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1452Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1453 : SparsePolynomial.Poly := [([9,9,9], 1)]
theorem eval_atom1453 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1453 = ((g 9) * (g 9) * (g 9)) := by
  norm_num [atom1453, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1453_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (912670214400 : Int) atom1453) := by
  rw [SparsePolynomial.eval_scale, eval_atom1453]
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 9) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1453Coded : CoefficientMerge.Poly := [(4167, 1)]
theorem atom1453Coded_decode : atom1453 = SparsePolynomial.decodeCubic 21 atom1453Coded := by decide +kernel
theorem atom1453Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (912670214400 : Int) atom1453Coded) := by
  have h := atom1453_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1453Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1454 : SparsePolynomial.Poly := [([9,9,10], 1)]
theorem eval_atom1454 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1454 = ((g 9) * (g 9) * (g 10)) := by
  norm_num [atom1454, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1454_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (602111059200 : Int) atom1454) := by
  rw [SparsePolynomial.eval_scale, eval_atom1454]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1454Coded : CoefficientMerge.Poly := [(4168, 1)]
theorem atom1454Coded_decode : atom1454 = SparsePolynomial.decodeCubic 21 atom1454Coded := by decide +kernel
theorem atom1454Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (602111059200 : Int) atom1454Coded) := by
  have h := atom1454_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1454Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1455 : SparsePolynomial.Poly := [([9,9,15], 1)]
theorem eval_atom1455 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1455 = ((g 9) * (g 9) * (g 15)) := by
  norm_num [atom1455, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1455_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2995132039200 : Int) atom1455) := by
  rw [SparsePolynomial.eval_scale, eval_atom1455]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1455Coded : CoefficientMerge.Poly := [(4173, 1)]
theorem atom1455Coded_decode : atom1455 = SparsePolynomial.decodeCubic 21 atom1455Coded := by decide +kernel
theorem atom1455Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2995132039200 : Int) atom1455Coded) := by
  have h := atom1455_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1455Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block019 : CoefficientMerge.Poly := [(3706, 770276908800), (3707, 427179916800), (3711, 3093893233200), (3726, 1414429430400), (3727, 518028134400), (3730, 427179916800), (3731, 854359833600), (3732, 5687746762320), (3734, 2944323370800), (3735, 5786258284800), (3736, 11171238059520), (3737, 17391151612800), (3748, 1834844054400), (3749, 2647162425600), (3750, 2478996576000), (3751, 3165190560000), (3752, 3851384544000), (3753, 7803362548800), (3754, 2139543982800), (3755, 9372338136000), (3756, 11410652912400), (3757, 20176096474800), (3758, 30348257839200), (3770, 3543563721600), (3771, 5560104211200), (3772, 6337146412800), (3773, 7114188614400), (3774, 12510442929600), (3775, 8456065254000), (3776, 19774108468800), (3777, 20318281326000), (3778, 30113920746000), (3779, 40982814885600), (3792, 5174965756800), (3793, 10622476166400), (3794, 11322200736000), (3795, 14101152139200), (3796, 13619552332400), (3797, 25094037416000), (3798, 27327261530800), (3799, 37107275293200), (3800, 48530465474400), (3814, 8314429795200), (3815, 15912566956800), (3816, 19319098982400), (3817, 19329077214000), (3818, 34558073524800), (3819, 38809323630000), (3820, 42738457266000), (3821, 60582834597600), (3836, 12733408598400), (3837, 24425203723200), (3838, 24919452658800), (3839, 46215639489600), (3840, 52704268570800), (3841, 52820365827600), (3842, 77218206357600), (3858, 19383530342400), (3859, 39580818694200), (3860, 66724705152000), (3861, 71113667221800), (3862, 53763791949000), (3863, 82935935850600), (3880, 15952947010560), (3881, 56181592441800), (3882, 64310888457900), (3883, 46815859734000), (3884, 61853161781250), (3902, 41682593433600), (3903, 73028319197400), (3904, 49453121621400), (3905, 54003049493400), (3924, 25323261106500), (3925, 30034904980500), (3926, 36065647557450), (3947, 5439574781550), (3968, 3482925254550), (4167, 912670214400), (4168, 602111059200), (4173, 2995132039200)]
theorem block019_data : block019 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (770276908800 : Int) atom1376Coded) (CoefficientMerge.scale (427179916800 : Int) atom1377Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3093893233200 : Int) atom1378Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1414429430400 : Int) atom1379Coded) (CoefficientMerge.scale (518028134400 : Int) atom1380Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1381Coded) (CoefficientMerge.scale (854359833600 : Int) atom1382Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5687746762320 : Int) atom1383Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2944323370800 : Int) atom1384Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1385Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1386Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1387Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1834844054400 : Int) atom1388Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2647162425600 : Int) atom1389Coded) (CoefficientMerge.scale (2478996576000 : Int) atom1390Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3165190560000 : Int) atom1391Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1392Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7803362548800 : Int) atom1393Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2139543982800 : Int) atom1394Coded) (CoefficientMerge.scale (9372338136000 : Int) atom1395Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11410652912400 : Int) atom1396Coded) (CoefficientMerge.scale (20176096474800 : Int) atom1397Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30348257839200 : Int) atom1398Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3543563721600 : Int) atom1399Coded) (CoefficientMerge.scale (5560104211200 : Int) atom1400Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6337146412800 : Int) atom1401Coded) (CoefficientMerge.scale (7114188614400 : Int) atom1402Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12510442929600 : Int) atom1403Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8456065254000 : Int) atom1404Coded) (CoefficientMerge.scale (19774108468800 : Int) atom1405Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20318281326000 : Int) atom1406Coded) (CoefficientMerge.scale (30113920746000 : Int) atom1407Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40982814885600 : Int) atom1408Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5174965756800 : Int) atom1409Coded) (CoefficientMerge.scale (10622476166400 : Int) atom1410Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11322200736000 : Int) atom1411Coded) (CoefficientMerge.scale (14101152139200 : Int) atom1412Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13619552332400 : Int) atom1413Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25094037416000 : Int) atom1414Coded) (CoefficientMerge.scale (27327261530800 : Int) atom1415Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37107275293200 : Int) atom1416Coded) (CoefficientMerge.scale (48530465474400 : Int) atom1417Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8314429795200 : Int) atom1418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15912566956800 : Int) atom1419Coded) (CoefficientMerge.scale (19319098982400 : Int) atom1420Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19329077214000 : Int) atom1421Coded) (CoefficientMerge.scale (34558073524800 : Int) atom1422Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38809323630000 : Int) atom1423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42738457266000 : Int) atom1424Coded) (CoefficientMerge.scale (60582834597600 : Int) atom1425Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12733408598400 : Int) atom1426Coded) (CoefficientMerge.scale (24425203723200 : Int) atom1427Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24919452658800 : Int) atom1428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46215639489600 : Int) atom1429Coded) (CoefficientMerge.scale (52704268570800 : Int) atom1430Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52820365827600 : Int) atom1431Coded) (CoefficientMerge.scale (77218206357600 : Int) atom1432Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19383530342400 : Int) atom1433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39580818694200 : Int) atom1434Coded) (CoefficientMerge.scale (66724705152000 : Int) atom1435Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (71113667221800 : Int) atom1436Coded) (CoefficientMerge.scale (53763791949000 : Int) atom1437Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82935935850600 : Int) atom1438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15952947010560 : Int) atom1439Coded) (CoefficientMerge.scale (56181592441800 : Int) atom1440Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64310888457900 : Int) atom1441Coded) (CoefficientMerge.scale (46815859734000 : Int) atom1442Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61853161781250 : Int) atom1443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41682593433600 : Int) atom1444Coded) (CoefficientMerge.scale (73028319197400 : Int) atom1445Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49453121621400 : Int) atom1446Coded) (CoefficientMerge.scale (54003049493400 : Int) atom1447Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25323261106500 : Int) atom1448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034904980500 : Int) atom1449Coded) (CoefficientMerge.scale (36065647557450 : Int) atom1450Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5439574781550 : Int) atom1451Coded) (CoefficientMerge.scale (3482925254550 : Int) atom1452Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (912670214400 : Int) atom1453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (602111059200 : Int) atom1454Coded) (CoefficientMerge.scale (2995132039200 : Int) atom1455Coded)))))))) := by decide +kernel
theorem block019_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block019 := by
  rw [block019_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1376Coded_nonneg g hg hA hB) (atom1377Coded_nonneg g hg hA hB)) (add_nonneg (atom1378Coded_nonneg g hg hA hB) (add_nonneg (atom1379Coded_nonneg g hg hA hB) (atom1380Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1381Coded_nonneg g hg hA hB) (atom1382Coded_nonneg g hg hA hB)) (add_nonneg (atom1383Coded_nonneg g hg hA hB) (add_nonneg (atom1384Coded_nonneg g hg hA hB) (atom1385Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1386Coded_nonneg g hg hA hB) (atom1387Coded_nonneg g hg hA hB)) (add_nonneg (atom1388Coded_nonneg g hg hA hB) (add_nonneg (atom1389Coded_nonneg g hg hA hB) (atom1390Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1391Coded_nonneg g hg hA hB) (atom1392Coded_nonneg g hg hA hB)) (add_nonneg (atom1393Coded_nonneg g hg hA hB) (add_nonneg (atom1394Coded_nonneg g hg hA hB) (atom1395Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1396Coded_nonneg g hg hA hB) (atom1397Coded_nonneg g hg hA hB)) (add_nonneg (atom1398Coded_nonneg g hg hA hB) (add_nonneg (atom1399Coded_nonneg g hg hA hB) (atom1400Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1401Coded_nonneg g hg hA hB) (atom1402Coded_nonneg g hg hA hB)) (add_nonneg (atom1403Coded_nonneg g hg hA hB) (add_nonneg (atom1404Coded_nonneg g hg hA hB) (atom1405Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1406Coded_nonneg g hg hA hB) (atom1407Coded_nonneg g hg hA hB)) (add_nonneg (atom1408Coded_nonneg g hg hA hB) (add_nonneg (atom1409Coded_nonneg g hg hA hB) (atom1410Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1411Coded_nonneg g hg hA hB) (atom1412Coded_nonneg g hg hA hB)) (add_nonneg (atom1413Coded_nonneg g hg hA hB) (add_nonneg (atom1414Coded_nonneg g hg hA hB) (atom1415Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1416Coded_nonneg g hg hA hB) (atom1417Coded_nonneg g hg hA hB)) (add_nonneg (atom1418Coded_nonneg g hg hA hB) (add_nonneg (atom1419Coded_nonneg g hg hA hB) (atom1420Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1421Coded_nonneg g hg hA hB) (atom1422Coded_nonneg g hg hA hB)) (add_nonneg (atom1423Coded_nonneg g hg hA hB) (add_nonneg (atom1424Coded_nonneg g hg hA hB) (atom1425Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1426Coded_nonneg g hg hA hB) (atom1427Coded_nonneg g hg hA hB)) (add_nonneg (atom1428Coded_nonneg g hg hA hB) (add_nonneg (atom1429Coded_nonneg g hg hA hB) (atom1430Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1431Coded_nonneg g hg hA hB) (atom1432Coded_nonneg g hg hA hB)) (add_nonneg (atom1433Coded_nonneg g hg hA hB) (add_nonneg (atom1434Coded_nonneg g hg hA hB) (atom1435Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1436Coded_nonneg g hg hA hB) (atom1437Coded_nonneg g hg hA hB)) (add_nonneg (atom1438Coded_nonneg g hg hA hB) (add_nonneg (atom1439Coded_nonneg g hg hA hB) (atom1440Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1441Coded_nonneg g hg hA hB) (atom1442Coded_nonneg g hg hA hB)) (add_nonneg (atom1443Coded_nonneg g hg hA hB) (add_nonneg (atom1444Coded_nonneg g hg hA hB) (atom1445Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1446Coded_nonneg g hg hA hB) (atom1447Coded_nonneg g hg hA hB)) (add_nonneg (atom1448Coded_nonneg g hg hA hB) (add_nonneg (atom1449Coded_nonneg g hg hA hB) (atom1450Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1451Coded_nonneg g hg hA hB) (atom1452Coded_nonneg g hg hA hB)) (add_nonneg (atom1453Coded_nonneg g hg hA hB) (add_nonneg (atom1454Coded_nonneg g hg hA hB) (atom1455Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
