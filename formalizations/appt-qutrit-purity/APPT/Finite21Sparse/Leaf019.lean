-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1376 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1376 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1376 = ((g 8) * (g 8) * (g 10)) := by
  norm_num [atom1376, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1376_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (770276908800 : Int) atom1376) := by
  rw [SparsePolynomial.eval_scale, eval_atom1376]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1376Coded : CoefficientMerge.Poly := [(nat_lit 3706, Int.ofNat (nat_lit 1))]
theorem atom1376Coded_decode : atom1376 = SparsePolynomial.decodeCubic 21 atom1376Coded := by decide +kernel
theorem atom1376Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (770276908800 : Int) atom1376Coded) := by
  have h := atom1376_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1376Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1377 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1377 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1377 = ((g 8) * (g 8) * (g 11)) := by
  norm_num [atom1377, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1377_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1377) := by
  rw [SparsePolynomial.eval_scale, eval_atom1377]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1377Coded : CoefficientMerge.Poly := [(nat_lit 3707, Int.ofNat (nat_lit 1))]
theorem atom1377Coded_decode : atom1377 = SparsePolynomial.decodeCubic 21 atom1377Coded := by decide +kernel
theorem atom1377Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1377Coded) := by
  have h := atom1377_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1377Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1378 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1378 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1378 = ((g 8) * (g 8) * (g 15)) := by
  norm_num [atom1378, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1378_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3093893233200 : Int) atom1378) := by
  rw [SparsePolynomial.eval_scale, eval_atom1378]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1378Coded : CoefficientMerge.Poly := [(nat_lit 3711, Int.ofNat (nat_lit 1))]
theorem atom1378Coded_decode : atom1378 = SparsePolynomial.decodeCubic 21 atom1378Coded := by decide +kernel
theorem atom1378Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3093893233200 : Int) atom1378Coded) := by
  have h := atom1378_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1378Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1379 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1379 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1379 = ((g 8) * (g 9) * (g 9)) := by
  norm_num [atom1379, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1379_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1414429430400 : Int) atom1379) := by
  rw [SparsePolynomial.eval_scale, eval_atom1379]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1379Coded : CoefficientMerge.Poly := [(nat_lit 3726, Int.ofNat (nat_lit 1))]
theorem atom1379Coded_decode : atom1379 = SparsePolynomial.decodeCubic 21 atom1379Coded := by decide +kernel
theorem atom1379Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1414429430400 : Int) atom1379Coded) := by
  have h := atom1379_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1379Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1380 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
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
def atom1380Coded : CoefficientMerge.Poly := [(nat_lit 3727, Int.ofNat (nat_lit 1))]
theorem atom1380Coded_decode : atom1380 = SparsePolynomial.decodeCubic 21 atom1380Coded := by decide +kernel
theorem atom1380Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (518028134400 : Int) atom1380Coded) := by
  have h := atom1380_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1380Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1381 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom1381Coded : CoefficientMerge.Poly := [(nat_lit 3730, Int.ofNat (nat_lit 1))]
theorem atom1381Coded_decode : atom1381 = SparsePolynomial.decodeCubic 21 atom1381Coded := by decide +kernel
theorem atom1381Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1381Coded) := by
  have h := atom1381_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1381Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1382 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1382Coded : CoefficientMerge.Poly := [(nat_lit 3731, Int.ofNat (nat_lit 1))]
theorem atom1382Coded_decode : atom1382 = SparsePolynomial.decodeCubic 21 atom1382Coded := by decide +kernel
theorem atom1382Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (854359833600 : Int) atom1382Coded) := by
  have h := atom1382_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1382Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1383 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1383Coded : CoefficientMerge.Poly := [(nat_lit 3732, Int.ofNat (nat_lit 1))]
theorem atom1383Coded_decode : atom1383 = SparsePolynomial.decodeCubic 21 atom1383Coded := by decide +kernel
theorem atom1383Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5687746762320 : Int) atom1383Coded) := by
  have h := atom1383_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1383Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1384 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1384Coded : CoefficientMerge.Poly := [(nat_lit 3734, Int.ofNat (nat_lit 1))]
theorem atom1384Coded_decode : atom1384 = SparsePolynomial.decodeCubic 21 atom1384Coded := by decide +kernel
theorem atom1384Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2944323370800 : Int) atom1384Coded) := by
  have h := atom1384_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1384Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1385 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1385Coded : CoefficientMerge.Poly := [(nat_lit 3735, Int.ofNat (nat_lit 1))]
theorem atom1385Coded_decode : atom1385 = SparsePolynomial.decodeCubic 21 atom1385Coded := by decide +kernel
theorem atom1385Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5786258284800 : Int) atom1385Coded) := by
  have h := atom1385_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1385Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1386 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1386Coded : CoefficientMerge.Poly := [(nat_lit 3736, Int.ofNat (nat_lit 1))]
theorem atom1386Coded_decode : atom1386 = SparsePolynomial.decodeCubic 21 atom1386Coded := by decide +kernel
theorem atom1386Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11171238059520 : Int) atom1386Coded) := by
  have h := atom1386_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1386Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1387 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1387Coded : CoefficientMerge.Poly := [(nat_lit 3737, Int.ofNat (nat_lit 1))]
theorem atom1387Coded_decode : atom1387 = SparsePolynomial.decodeCubic 21 atom1387Coded := by decide +kernel
theorem atom1387Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17391151612800 : Int) atom1387Coded) := by
  have h := atom1387_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1387Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1388 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1388 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1388 = ((g 8) * (g 10) * (g 10)) := by
  norm_num [atom1388, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1388_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1834844054400 : Int) atom1388) := by
  rw [SparsePolynomial.eval_scale, eval_atom1388]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1388Coded : CoefficientMerge.Poly := [(nat_lit 3748, Int.ofNat (nat_lit 1))]
theorem atom1388Coded_decode : atom1388 = SparsePolynomial.decodeCubic 21 atom1388Coded := by decide +kernel
theorem atom1388Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1834844054400 : Int) atom1388Coded) := by
  have h := atom1388_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1388Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1389 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
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
def atom1389Coded : CoefficientMerge.Poly := [(nat_lit 3749, Int.ofNat (nat_lit 1))]
theorem atom1389Coded_decode : atom1389 = SparsePolynomial.decodeCubic 21 atom1389Coded := by decide +kernel
theorem atom1389Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2647162425600 : Int) atom1389Coded) := by
  have h := atom1389_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1389Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1390 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
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
def atom1390Coded : CoefficientMerge.Poly := [(nat_lit 3750, Int.ofNat (nat_lit 1))]
theorem atom1390Coded_decode : atom1390 = SparsePolynomial.decodeCubic 21 atom1390Coded := by decide +kernel
theorem atom1390Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2478996576000 : Int) atom1390Coded) := by
  have h := atom1390_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1390Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1391 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom1391Coded : CoefficientMerge.Poly := [(nat_lit 3751, Int.ofNat (nat_lit 1))]
theorem atom1391Coded_decode : atom1391 = SparsePolynomial.decodeCubic 21 atom1391Coded := by decide +kernel
theorem atom1391Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3165190560000 : Int) atom1391Coded) := by
  have h := atom1391_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1391Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1392 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1392Coded : CoefficientMerge.Poly := [(nat_lit 3752, Int.ofNat (nat_lit 1))]
theorem atom1392Coded_decode : atom1392 = SparsePolynomial.decodeCubic 21 atom1392Coded := by decide +kernel
theorem atom1392Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3851384544000 : Int) atom1392Coded) := by
  have h := atom1392_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1392Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1393 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1393Coded : CoefficientMerge.Poly := [(nat_lit 3753, Int.ofNat (nat_lit 1))]
theorem atom1393Coded_decode : atom1393 = SparsePolynomial.decodeCubic 21 atom1393Coded := by decide +kernel
theorem atom1393Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7803362548800 : Int) atom1393Coded) := by
  have h := atom1393_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1393Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1394 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1394Coded : CoefficientMerge.Poly := [(nat_lit 3754, Int.ofNat (nat_lit 1))]
theorem atom1394Coded_decode : atom1394 = SparsePolynomial.decodeCubic 21 atom1394Coded := by decide +kernel
theorem atom1394Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2139543982800 : Int) atom1394Coded) := by
  have h := atom1394_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1394Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1395 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1395Coded : CoefficientMerge.Poly := [(nat_lit 3755, Int.ofNat (nat_lit 1))]
theorem atom1395Coded_decode : atom1395 = SparsePolynomial.decodeCubic 21 atom1395Coded := by decide +kernel
theorem atom1395Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9372338136000 : Int) atom1395Coded) := by
  have h := atom1395_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1395Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1396 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1396Coded : CoefficientMerge.Poly := [(nat_lit 3756, Int.ofNat (nat_lit 1))]
theorem atom1396Coded_decode : atom1396 = SparsePolynomial.decodeCubic 21 atom1396Coded := by decide +kernel
theorem atom1396Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11410652912400 : Int) atom1396Coded) := by
  have h := atom1396_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1396Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1397 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1397Coded : CoefficientMerge.Poly := [(nat_lit 3757, Int.ofNat (nat_lit 1))]
theorem atom1397Coded_decode : atom1397 = SparsePolynomial.decodeCubic 21 atom1397Coded := by decide +kernel
theorem atom1397Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20176096474800 : Int) atom1397Coded) := by
  have h := atom1397_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1397Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1398 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1398Coded : CoefficientMerge.Poly := [(nat_lit 3758, Int.ofNat (nat_lit 1))]
theorem atom1398Coded_decode : atom1398 = SparsePolynomial.decodeCubic 21 atom1398Coded := by decide +kernel
theorem atom1398Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30348257839200 : Int) atom1398Coded) := by
  have h := atom1398_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1398Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1399 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1399 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1399 = ((g 8) * (g 11) * (g 11)) := by
  norm_num [atom1399, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1399_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3543563721600 : Int) atom1399) := by
  rw [SparsePolynomial.eval_scale, eval_atom1399]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1399Coded : CoefficientMerge.Poly := [(nat_lit 3770, Int.ofNat (nat_lit 1))]
theorem atom1399Coded_decode : atom1399 = SparsePolynomial.decodeCubic 21 atom1399Coded := by decide +kernel
theorem atom1399Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3543563721600 : Int) atom1399Coded) := by
  have h := atom1399_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1399Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1400 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
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
def atom1400Coded : CoefficientMerge.Poly := [(nat_lit 3771, Int.ofNat (nat_lit 1))]
theorem atom1400Coded_decode : atom1400 = SparsePolynomial.decodeCubic 21 atom1400Coded := by decide +kernel
theorem atom1400Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5560104211200 : Int) atom1400Coded) := by
  have h := atom1400_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1400Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1401 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom1401Coded : CoefficientMerge.Poly := [(nat_lit 3772, Int.ofNat (nat_lit 1))]
theorem atom1401Coded_decode : atom1401 = SparsePolynomial.decodeCubic 21 atom1401Coded := by decide +kernel
theorem atom1401Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6337146412800 : Int) atom1401Coded) := by
  have h := atom1401_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1401Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1402 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1402Coded : CoefficientMerge.Poly := [(nat_lit 3773, Int.ofNat (nat_lit 1))]
theorem atom1402Coded_decode : atom1402 = SparsePolynomial.decodeCubic 21 atom1402Coded := by decide +kernel
theorem atom1402Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7114188614400 : Int) atom1402Coded) := by
  have h := atom1402_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1402Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1403 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1403Coded : CoefficientMerge.Poly := [(nat_lit 3774, Int.ofNat (nat_lit 1))]
theorem atom1403Coded_decode : atom1403 = SparsePolynomial.decodeCubic 21 atom1403Coded := by decide +kernel
theorem atom1403Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12510442929600 : Int) atom1403Coded) := by
  have h := atom1403_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1403Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1404 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1404Coded : CoefficientMerge.Poly := [(nat_lit 3775, Int.ofNat (nat_lit 1))]
theorem atom1404Coded_decode : atom1404 = SparsePolynomial.decodeCubic 21 atom1404Coded := by decide +kernel
theorem atom1404Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8456065254000 : Int) atom1404Coded) := by
  have h := atom1404_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1404Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1405 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1405Coded : CoefficientMerge.Poly := [(nat_lit 3776, Int.ofNat (nat_lit 1))]
theorem atom1405Coded_decode : atom1405 = SparsePolynomial.decodeCubic 21 atom1405Coded := by decide +kernel
theorem atom1405Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19774108468800 : Int) atom1405Coded) := by
  have h := atom1405_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1405Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1406 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1406Coded : CoefficientMerge.Poly := [(nat_lit 3777, Int.ofNat (nat_lit 1))]
theorem atom1406Coded_decode : atom1406 = SparsePolynomial.decodeCubic 21 atom1406Coded := by decide +kernel
theorem atom1406Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20318281326000 : Int) atom1406Coded) := by
  have h := atom1406_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1406Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1407 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1407Coded : CoefficientMerge.Poly := [(nat_lit 3778, Int.ofNat (nat_lit 1))]
theorem atom1407Coded_decode : atom1407 = SparsePolynomial.decodeCubic 21 atom1407Coded := by decide +kernel
theorem atom1407Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30113920746000 : Int) atom1407Coded) := by
  have h := atom1407_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1407Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1408 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1408Coded : CoefficientMerge.Poly := [(nat_lit 3779, Int.ofNat (nat_lit 1))]
theorem atom1408Coded_decode : atom1408 = SparsePolynomial.decodeCubic 21 atom1408Coded := by decide +kernel
theorem atom1408Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40982814885600 : Int) atom1408Coded) := by
  have h := atom1408_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1408Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1409 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1409 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1409 = ((g 8) * (g 12) * (g 12)) := by
  norm_num [atom1409, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1409_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5174965756800 : Int) atom1409) := by
  rw [SparsePolynomial.eval_scale, eval_atom1409]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1409Coded : CoefficientMerge.Poly := [(nat_lit 3792, Int.ofNat (nat_lit 1))]
theorem atom1409Coded_decode : atom1409 = SparsePolynomial.decodeCubic 21 atom1409Coded := by decide +kernel
theorem atom1409Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5174965756800 : Int) atom1409Coded) := by
  have h := atom1409_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1409Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1410 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
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
def atom1410Coded : CoefficientMerge.Poly := [(nat_lit 3793, Int.ofNat (nat_lit 1))]
theorem atom1410Coded_decode : atom1410 = SparsePolynomial.decodeCubic 21 atom1410Coded := by decide +kernel
theorem atom1410Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10622476166400 : Int) atom1410Coded) := by
  have h := atom1410_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1410Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1411 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1411Coded : CoefficientMerge.Poly := [(nat_lit 3794, Int.ofNat (nat_lit 1))]
theorem atom1411Coded_decode : atom1411 = SparsePolynomial.decodeCubic 21 atom1411Coded := by decide +kernel
theorem atom1411Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11322200736000 : Int) atom1411Coded) := by
  have h := atom1411_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1411Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1412 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1412Coded : CoefficientMerge.Poly := [(nat_lit 3795, Int.ofNat (nat_lit 1))]
theorem atom1412Coded_decode : atom1412 = SparsePolynomial.decodeCubic 21 atom1412Coded := by decide +kernel
theorem atom1412Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14101152139200 : Int) atom1412Coded) := by
  have h := atom1412_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1412Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1413 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1413Coded : CoefficientMerge.Poly := [(nat_lit 3796, Int.ofNat (nat_lit 1))]
theorem atom1413Coded_decode : atom1413 = SparsePolynomial.decodeCubic 21 atom1413Coded := by decide +kernel
theorem atom1413Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13619552332400 : Int) atom1413Coded) := by
  have h := atom1413_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1413Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1414 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1414Coded : CoefficientMerge.Poly := [(nat_lit 3797, Int.ofNat (nat_lit 1))]
theorem atom1414Coded_decode : atom1414 = SparsePolynomial.decodeCubic 21 atom1414Coded := by decide +kernel
theorem atom1414Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25094037416000 : Int) atom1414Coded) := by
  have h := atom1414_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1414Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1415 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1415Coded : CoefficientMerge.Poly := [(nat_lit 3798, Int.ofNat (nat_lit 1))]
theorem atom1415Coded_decode : atom1415 = SparsePolynomial.decodeCubic 21 atom1415Coded := by decide +kernel
theorem atom1415Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27327261530800 : Int) atom1415Coded) := by
  have h := atom1415_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1415Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1416 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1416Coded : CoefficientMerge.Poly := [(nat_lit 3799, Int.ofNat (nat_lit 1))]
theorem atom1416Coded_decode : atom1416 = SparsePolynomial.decodeCubic 21 atom1416Coded := by decide +kernel
theorem atom1416Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37107275293200 : Int) atom1416Coded) := by
  have h := atom1416_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1416Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1417 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1417Coded : CoefficientMerge.Poly := [(nat_lit 3800, Int.ofNat (nat_lit 1))]
theorem atom1417Coded_decode : atom1417 = SparsePolynomial.decodeCubic 21 atom1417Coded := by decide +kernel
theorem atom1417Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48530465474400 : Int) atom1417Coded) := by
  have h := atom1417_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1417Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1418 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1418 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1418 = ((g 8) * (g 13) * (g 13)) := by
  norm_num [atom1418, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1418_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8314429795200 : Int) atom1418) := by
  rw [SparsePolynomial.eval_scale, eval_atom1418]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1418Coded : CoefficientMerge.Poly := [(nat_lit 3814, Int.ofNat (nat_lit 1))]
theorem atom1418Coded_decode : atom1418 = SparsePolynomial.decodeCubic 21 atom1418Coded := by decide +kernel
theorem atom1418Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8314429795200 : Int) atom1418Coded) := by
  have h := atom1418_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1418Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1419 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
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
def atom1419Coded : CoefficientMerge.Poly := [(nat_lit 3815, Int.ofNat (nat_lit 1))]
theorem atom1419Coded_decode : atom1419 = SparsePolynomial.decodeCubic 21 atom1419Coded := by decide +kernel
theorem atom1419Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15912566956800 : Int) atom1419Coded) := by
  have h := atom1419_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1419Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1420 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1420Coded : CoefficientMerge.Poly := [(nat_lit 3816, Int.ofNat (nat_lit 1))]
theorem atom1420Coded_decode : atom1420 = SparsePolynomial.decodeCubic 21 atom1420Coded := by decide +kernel
theorem atom1420Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19319098982400 : Int) atom1420Coded) := by
  have h := atom1420_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1420Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1421 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1421Coded : CoefficientMerge.Poly := [(nat_lit 3817, Int.ofNat (nat_lit 1))]
theorem atom1421Coded_decode : atom1421 = SparsePolynomial.decodeCubic 21 atom1421Coded := by decide +kernel
theorem atom1421Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19329077214000 : Int) atom1421Coded) := by
  have h := atom1421_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1421Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1422 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1422Coded : CoefficientMerge.Poly := [(nat_lit 3818, Int.ofNat (nat_lit 1))]
theorem atom1422Coded_decode : atom1422 = SparsePolynomial.decodeCubic 21 atom1422Coded := by decide +kernel
theorem atom1422Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34558073524800 : Int) atom1422Coded) := by
  have h := atom1422_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1422Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1423 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1423Coded : CoefficientMerge.Poly := [(nat_lit 3819, Int.ofNat (nat_lit 1))]
theorem atom1423Coded_decode : atom1423 = SparsePolynomial.decodeCubic 21 atom1423Coded := by decide +kernel
theorem atom1423Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38809323630000 : Int) atom1423Coded) := by
  have h := atom1423_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1423Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1424 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1424Coded : CoefficientMerge.Poly := [(nat_lit 3820, Int.ofNat (nat_lit 1))]
theorem atom1424Coded_decode : atom1424 = SparsePolynomial.decodeCubic 21 atom1424Coded := by decide +kernel
theorem atom1424Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42738457266000 : Int) atom1424Coded) := by
  have h := atom1424_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1424Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1425 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1425Coded : CoefficientMerge.Poly := [(nat_lit 3821, Int.ofNat (nat_lit 1))]
theorem atom1425Coded_decode : atom1425 = SparsePolynomial.decodeCubic 21 atom1425Coded := by decide +kernel
theorem atom1425Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (60582834597600 : Int) atom1425Coded) := by
  have h := atom1425_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1425Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1426 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1426 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1426 = ((g 8) * (g 14) * (g 14)) := by
  norm_num [atom1426, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1426_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12733408598400 : Int) atom1426) := by
  rw [SparsePolynomial.eval_scale, eval_atom1426]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1426Coded : CoefficientMerge.Poly := [(nat_lit 3836, Int.ofNat (nat_lit 1))]
theorem atom1426Coded_decode : atom1426 = SparsePolynomial.decodeCubic 21 atom1426Coded := by decide +kernel
theorem atom1426Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12733408598400 : Int) atom1426Coded) := by
  have h := atom1426_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1426Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1427 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
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
def atom1427Coded : CoefficientMerge.Poly := [(nat_lit 3837, Int.ofNat (nat_lit 1))]
theorem atom1427Coded_decode : atom1427 = SparsePolynomial.decodeCubic 21 atom1427Coded := by decide +kernel
theorem atom1427Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24425203723200 : Int) atom1427Coded) := by
  have h := atom1427_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1427Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1428 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1428Coded : CoefficientMerge.Poly := [(nat_lit 3838, Int.ofNat (nat_lit 1))]
theorem atom1428Coded_decode : atom1428 = SparsePolynomial.decodeCubic 21 atom1428Coded := by decide +kernel
theorem atom1428Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24919452658800 : Int) atom1428Coded) := by
  have h := atom1428_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1428Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1429 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1429Coded : CoefficientMerge.Poly := [(nat_lit 3839, Int.ofNat (nat_lit 1))]
theorem atom1429Coded_decode : atom1429 = SparsePolynomial.decodeCubic 21 atom1429Coded := by decide +kernel
theorem atom1429Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46215639489600 : Int) atom1429Coded) := by
  have h := atom1429_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1429Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1430 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1430Coded : CoefficientMerge.Poly := [(nat_lit 3840, Int.ofNat (nat_lit 1))]
theorem atom1430Coded_decode : atom1430 = SparsePolynomial.decodeCubic 21 atom1430Coded := by decide +kernel
theorem atom1430Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52704268570800 : Int) atom1430Coded) := by
  have h := atom1430_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1430Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1431 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1431Coded : CoefficientMerge.Poly := [(nat_lit 3841, Int.ofNat (nat_lit 1))]
theorem atom1431Coded_decode : atom1431 = SparsePolynomial.decodeCubic 21 atom1431Coded := by decide +kernel
theorem atom1431Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52820365827600 : Int) atom1431Coded) := by
  have h := atom1431_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1431Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1432 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1432Coded : CoefficientMerge.Poly := [(nat_lit 3842, Int.ofNat (nat_lit 1))]
theorem atom1432Coded_decode : atom1432 = SparsePolynomial.decodeCubic 21 atom1432Coded := by decide +kernel
theorem atom1432Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (77218206357600 : Int) atom1432Coded) := by
  have h := atom1432_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1432Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1433 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1433 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1433 = ((g 8) * (g 15) * (g 15)) := by
  norm_num [atom1433, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1433_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19383530342400 : Int) atom1433) := by
  rw [SparsePolynomial.eval_scale, eval_atom1433]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1433Coded : CoefficientMerge.Poly := [(nat_lit 3858, Int.ofNat (nat_lit 1))]
theorem atom1433Coded_decode : atom1433 = SparsePolynomial.decodeCubic 21 atom1433Coded := by decide +kernel
theorem atom1433Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19383530342400 : Int) atom1433Coded) := by
  have h := atom1433_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1433Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1434 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
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
def atom1434Coded : CoefficientMerge.Poly := [(nat_lit 3859, Int.ofNat (nat_lit 1))]
theorem atom1434Coded_decode : atom1434 = SparsePolynomial.decodeCubic 21 atom1434Coded := by decide +kernel
theorem atom1434Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39580818694200 : Int) atom1434Coded) := by
  have h := atom1434_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1434Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1435 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1435Coded : CoefficientMerge.Poly := [(nat_lit 3860, Int.ofNat (nat_lit 1))]
theorem atom1435Coded_decode : atom1435 = SparsePolynomial.decodeCubic 21 atom1435Coded := by decide +kernel
theorem atom1435Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (66724705152000 : Int) atom1435Coded) := by
  have h := atom1435_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1435Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1436 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1436Coded : CoefficientMerge.Poly := [(nat_lit 3861, Int.ofNat (nat_lit 1))]
theorem atom1436Coded_decode : atom1436 = SparsePolynomial.decodeCubic 21 atom1436Coded := by decide +kernel
theorem atom1436Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (71113667221800 : Int) atom1436Coded) := by
  have h := atom1436_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1436Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1437 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1437Coded : CoefficientMerge.Poly := [(nat_lit 3862, Int.ofNat (nat_lit 1))]
theorem atom1437Coded_decode : atom1437 = SparsePolynomial.decodeCubic 21 atom1437Coded := by decide +kernel
theorem atom1437Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53763791949000 : Int) atom1437Coded) := by
  have h := atom1437_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1437Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1438 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1438Coded : CoefficientMerge.Poly := [(nat_lit 3863, Int.ofNat (nat_lit 1))]
theorem atom1438Coded_decode : atom1438 = SparsePolynomial.decodeCubic 21 atom1438Coded := by decide +kernel
theorem atom1438Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (82935935850600 : Int) atom1438Coded) := by
  have h := atom1438_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1438Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1439 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1439 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1439 = ((g 8) * (g 16) * (g 16)) := by
  norm_num [atom1439, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1439_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15952947010560 : Int) atom1439) := by
  rw [SparsePolynomial.eval_scale, eval_atom1439]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1439Coded : CoefficientMerge.Poly := [(nat_lit 3880, Int.ofNat (nat_lit 1))]
theorem atom1439Coded_decode : atom1439 = SparsePolynomial.decodeCubic 21 atom1439Coded := by decide +kernel
theorem atom1439Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15952947010560 : Int) atom1439Coded) := by
  have h := atom1439_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1439Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1440 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
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
def atom1440Coded : CoefficientMerge.Poly := [(nat_lit 3881, Int.ofNat (nat_lit 1))]
theorem atom1440Coded_decode : atom1440 = SparsePolynomial.decodeCubic 21 atom1440Coded := by decide +kernel
theorem atom1440Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (56181592441800 : Int) atom1440Coded) := by
  have h := atom1440_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1440Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1441 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1441Coded : CoefficientMerge.Poly := [(nat_lit 3882, Int.ofNat (nat_lit 1))]
theorem atom1441Coded_decode : atom1441 = SparsePolynomial.decodeCubic 21 atom1441Coded := by decide +kernel
theorem atom1441Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (64310888457900 : Int) atom1441Coded) := by
  have h := atom1441_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1441Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1442 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1442Coded : CoefficientMerge.Poly := [(nat_lit 3883, Int.ofNat (nat_lit 1))]
theorem atom1442Coded_decode : atom1442 = SparsePolynomial.decodeCubic 21 atom1442Coded := by decide +kernel
theorem atom1442Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46815859734000 : Int) atom1442Coded) := by
  have h := atom1442_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1442Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1443 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1443Coded : CoefficientMerge.Poly := [(nat_lit 3884, Int.ofNat (nat_lit 1))]
theorem atom1443Coded_decode : atom1443 = SparsePolynomial.decodeCubic 21 atom1443Coded := by decide +kernel
theorem atom1443Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (61853161781250 : Int) atom1443Coded) := by
  have h := atom1443_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1443Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1444 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1444 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1444 = ((g 8) * (g 17) * (g 17)) := by
  norm_num [atom1444, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1444_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41682593433600 : Int) atom1444) := by
  rw [SparsePolynomial.eval_scale, eval_atom1444]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1444Coded : CoefficientMerge.Poly := [(nat_lit 3902, Int.ofNat (nat_lit 1))]
theorem atom1444Coded_decode : atom1444 = SparsePolynomial.decodeCubic 21 atom1444Coded := by decide +kernel
theorem atom1444Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41682593433600 : Int) atom1444Coded) := by
  have h := atom1444_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1444Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1445 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
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
def atom1445Coded : CoefficientMerge.Poly := [(nat_lit 3903, Int.ofNat (nat_lit 1))]
theorem atom1445Coded_decode : atom1445 = SparsePolynomial.decodeCubic 21 atom1445Coded := by decide +kernel
theorem atom1445Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (73028319197400 : Int) atom1445Coded) := by
  have h := atom1445_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1445Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1446 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1446Coded : CoefficientMerge.Poly := [(nat_lit 3904, Int.ofNat (nat_lit 1))]
theorem atom1446Coded_decode : atom1446 = SparsePolynomial.decodeCubic 21 atom1446Coded := by decide +kernel
theorem atom1446Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49453121621400 : Int) atom1446Coded) := by
  have h := atom1446_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1446Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1447 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1447Coded : CoefficientMerge.Poly := [(nat_lit 3905, Int.ofNat (nat_lit 1))]
theorem atom1447Coded_decode : atom1447 = SparsePolynomial.decodeCubic 21 atom1447Coded := by decide +kernel
theorem atom1447Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (54003049493400 : Int) atom1447Coded) := by
  have h := atom1447_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1447Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1448 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1448 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1448 = ((g 8) * (g 18) * (g 18)) := by
  norm_num [atom1448, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1448_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25323261106500 : Int) atom1448) := by
  rw [SparsePolynomial.eval_scale, eval_atom1448]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 8) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1448Coded : CoefficientMerge.Poly := [(nat_lit 3924, Int.ofNat (nat_lit 1))]
theorem atom1448Coded_decode : atom1448 = SparsePolynomial.decodeCubic 21 atom1448Coded := by decide +kernel
theorem atom1448Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25323261106500 : Int) atom1448Coded) := by
  have h := atom1448_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1448Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1449 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
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
def atom1449Coded : CoefficientMerge.Poly := [(nat_lit 3925, Int.ofNat (nat_lit 1))]
theorem atom1449Coded_decode : atom1449 = SparsePolynomial.decodeCubic 21 atom1449Coded := by decide +kernel
theorem atom1449Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30034904980500 : Int) atom1449Coded) := by
  have h := atom1449_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1449Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1450 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1450Coded : CoefficientMerge.Poly := [(nat_lit 3926, Int.ofNat (nat_lit 1))]
theorem atom1450Coded_decode : atom1450 = SparsePolynomial.decodeCubic 21 atom1450Coded := by decide +kernel
theorem atom1450Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36065647557450 : Int) atom1450Coded) := by
  have h := atom1450_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1450Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1451 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
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
def atom1451Coded : CoefficientMerge.Poly := [(nat_lit 3947, Int.ofNat (nat_lit 1))]
theorem atom1451Coded_decode : atom1451 = SparsePolynomial.decodeCubic 21 atom1451Coded := by decide +kernel
theorem atom1451Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5439574781550 : Int) atom1451Coded) := by
  have h := atom1451_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1451Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1452 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1452 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1452 = ((g 8) * (g 20) * (g 20)) := by
  norm_num [atom1452, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1452_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3482925254550 : Int) atom1452) := by
  rw [SparsePolynomial.eval_scale, eval_atom1452]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 8) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1452Coded : CoefficientMerge.Poly := [(nat_lit 3968, Int.ofNat (nat_lit 1))]
theorem atom1452Coded_decode : atom1452 = SparsePolynomial.decodeCubic 21 atom1452Coded := by decide +kernel
theorem atom1452Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3482925254550 : Int) atom1452Coded) := by
  have h := atom1452_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1452Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1453 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1453 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1453 = ((g 9) * (g 9) * (g 9)) := by
  norm_num [atom1453, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1453_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (912670214400 : Int) atom1453) := by
  rw [SparsePolynomial.eval_scale, eval_atom1453]
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 9) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1453Coded : CoefficientMerge.Poly := [(nat_lit 4167, Int.ofNat (nat_lit 1))]
theorem atom1453Coded_decode : atom1453 = SparsePolynomial.decodeCubic 21 atom1453Coded := by decide +kernel
theorem atom1453Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (912670214400 : Int) atom1453Coded) := by
  have h := atom1453_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1453Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1454 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1454 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1454 = ((g 9) * (g 9) * (g 10)) := by
  norm_num [atom1454, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1454_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (602111059200 : Int) atom1454) := by
  rw [SparsePolynomial.eval_scale, eval_atom1454]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1454Coded : CoefficientMerge.Poly := [(nat_lit 4168, Int.ofNat (nat_lit 1))]
theorem atom1454Coded_decode : atom1454 = SparsePolynomial.decodeCubic 21 atom1454Coded := by decide +kernel
theorem atom1454Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (602111059200 : Int) atom1454Coded) := by
  have h := atom1454_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1454Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1455 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1455 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1455 = ((g 9) * (g 9) * (g 15)) := by
  norm_num [atom1455, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1455_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2995132039200 : Int) atom1455) := by
  rw [SparsePolynomial.eval_scale, eval_atom1455]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 9) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1455Coded : CoefficientMerge.Poly := [(nat_lit 4173, Int.ofNat (nat_lit 1))]
theorem atom1455Coded_decode : atom1455 = SparsePolynomial.decodeCubic 21 atom1455Coded := by decide +kernel
theorem atom1455Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2995132039200 : Int) atom1455Coded) := by
  have h := atom1455_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1455Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block019 : CoefficientMerge.Poly := [(nat_lit 3706, Int.ofNat (nat_lit 770276908800)), (nat_lit 3707, Int.ofNat (nat_lit 427179916800)), (nat_lit 3711, Int.ofNat (nat_lit 3093893233200)), (nat_lit 3726, Int.ofNat (nat_lit 1414429430400)), (nat_lit 3727, Int.ofNat (nat_lit 518028134400)), (nat_lit 3730, Int.ofNat (nat_lit 427179916800)), (nat_lit 3731, Int.ofNat (nat_lit 854359833600)), (nat_lit 3732, Int.ofNat (nat_lit 5687746762320)), (nat_lit 3734, Int.ofNat (nat_lit 2944323370800)), (nat_lit 3735, Int.ofNat (nat_lit 5786258284800)), (nat_lit 3736, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3737, Int.ofNat (nat_lit 17391151612800)), (nat_lit 3748, Int.ofNat (nat_lit 1834844054400)), (nat_lit 3749, Int.ofNat (nat_lit 2647162425600)), (nat_lit 3750, Int.ofNat (nat_lit 2478996576000)), (nat_lit 3751, Int.ofNat (nat_lit 3165190560000)), (nat_lit 3752, Int.ofNat (nat_lit 3851384544000)), (nat_lit 3753, Int.ofNat (nat_lit 7803362548800)), (nat_lit 3754, Int.ofNat (nat_lit 2139543982800)), (nat_lit 3755, Int.ofNat (nat_lit 9372338136000)), (nat_lit 3756, Int.ofNat (nat_lit 11410652912400)), (nat_lit 3757, Int.ofNat (nat_lit 20176096474800)), (nat_lit 3758, Int.ofNat (nat_lit 30348257839200)), (nat_lit 3770, Int.ofNat (nat_lit 3543563721600)), (nat_lit 3771, Int.ofNat (nat_lit 5560104211200)), (nat_lit 3772, Int.ofNat (nat_lit 6337146412800)), (nat_lit 3773, Int.ofNat (nat_lit 7114188614400)), (nat_lit 3774, Int.ofNat (nat_lit 12510442929600)), (nat_lit 3775, Int.ofNat (nat_lit 8456065254000)), (nat_lit 3776, Int.ofNat (nat_lit 19774108468800)), (nat_lit 3777, Int.ofNat (nat_lit 20318281326000)), (nat_lit 3778, Int.ofNat (nat_lit 30113920746000)), (nat_lit 3779, Int.ofNat (nat_lit 40982814885600)), (nat_lit 3792, Int.ofNat (nat_lit 5174965756800)), (nat_lit 3793, Int.ofNat (nat_lit 10622476166400)), (nat_lit 3794, Int.ofNat (nat_lit 11322200736000)), (nat_lit 3795, Int.ofNat (nat_lit 14101152139200)), (nat_lit 3796, Int.ofNat (nat_lit 13619552332400)), (nat_lit 3797, Int.ofNat (nat_lit 25094037416000)), (nat_lit 3798, Int.ofNat (nat_lit 27327261530800)), (nat_lit 3799, Int.ofNat (nat_lit 37107275293200)), (nat_lit 3800, Int.ofNat (nat_lit 48530465474400)), (nat_lit 3814, Int.ofNat (nat_lit 8314429795200)), (nat_lit 3815, Int.ofNat (nat_lit 15912566956800)), (nat_lit 3816, Int.ofNat (nat_lit 19319098982400)), (nat_lit 3817, Int.ofNat (nat_lit 19329077214000)), (nat_lit 3818, Int.ofNat (nat_lit 34558073524800)), (nat_lit 3819, Int.ofNat (nat_lit 38809323630000)), (nat_lit 3820, Int.ofNat (nat_lit 42738457266000)), (nat_lit 3821, Int.ofNat (nat_lit 60582834597600)), (nat_lit 3836, Int.ofNat (nat_lit 12733408598400)), (nat_lit 3837, Int.ofNat (nat_lit 24425203723200)), (nat_lit 3838, Int.ofNat (nat_lit 24919452658800)), (nat_lit 3839, Int.ofNat (nat_lit 46215639489600)), (nat_lit 3840, Int.ofNat (nat_lit 52704268570800)), (nat_lit 3841, Int.ofNat (nat_lit 52820365827600)), (nat_lit 3842, Int.ofNat (nat_lit 77218206357600)), (nat_lit 3858, Int.ofNat (nat_lit 19383530342400)), (nat_lit 3859, Int.ofNat (nat_lit 39580818694200)), (nat_lit 3860, Int.ofNat (nat_lit 66724705152000)), (nat_lit 3861, Int.ofNat (nat_lit 71113667221800)), (nat_lit 3862, Int.ofNat (nat_lit 53763791949000)), (nat_lit 3863, Int.ofNat (nat_lit 82935935850600)), (nat_lit 3880, Int.ofNat (nat_lit 15952947010560)), (nat_lit 3881, Int.ofNat (nat_lit 56181592441800)), (nat_lit 3882, Int.ofNat (nat_lit 64310888457900)), (nat_lit 3883, Int.ofNat (nat_lit 46815859734000)), (nat_lit 3884, Int.ofNat (nat_lit 61853161781250)), (nat_lit 3902, Int.ofNat (nat_lit 41682593433600)), (nat_lit 3903, Int.ofNat (nat_lit 73028319197400)), (nat_lit 3904, Int.ofNat (nat_lit 49453121621400)), (nat_lit 3905, Int.ofNat (nat_lit 54003049493400)), (nat_lit 3924, Int.ofNat (nat_lit 25323261106500)), (nat_lit 3925, Int.ofNat (nat_lit 30034904980500)), (nat_lit 3926, Int.ofNat (nat_lit 36065647557450)), (nat_lit 3947, Int.ofNat (nat_lit 5439574781550)), (nat_lit 3968, Int.ofNat (nat_lit 3482925254550)), (nat_lit 4167, Int.ofNat (nat_lit 912670214400)), (nat_lit 4168, Int.ofNat (nat_lit 602111059200)), (nat_lit 4173, Int.ofNat (nat_lit 2995132039200))]
def block019_data_flat000 : CoefficientMerge.Poly := [(nat_lit 3706, Int.ofNat (nat_lit 770276908800))]
theorem block019_data_flat000_step : block019_data_flat000 = (CoefficientMerge.scale (770276908800 : Int) atom1376Coded) := by decide +kernel
theorem block019_data_flat000_original : block019_data_flat000 = (CoefficientMerge.scale (770276908800 : Int) atom1376Coded) := by
  rw [block019_data_flat000_step]
def block019_data_flat001 : CoefficientMerge.Poly := [(nat_lit 3707, Int.ofNat (nat_lit 427179916800))]
theorem block019_data_flat001_step : block019_data_flat001 = (CoefficientMerge.scale (427179916800 : Int) atom1377Coded) := by decide +kernel
theorem block019_data_flat001_original : block019_data_flat001 = (CoefficientMerge.scale (427179916800 : Int) atom1377Coded) := by
  rw [block019_data_flat001_step]
def block019_data_flat002 : CoefficientMerge.Poly := [(nat_lit 3706, Int.ofNat (nat_lit 770276908800)), (nat_lit 3707, Int.ofNat (nat_lit 427179916800))]
theorem block019_data_flat002_step : block019_data_flat002 = (CoefficientMerge.fastMerge block019_data_flat000 block019_data_flat001) := by decide +kernel
theorem block019_data_flat002_original : block019_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (770276908800 : Int) atom1376Coded) (CoefficientMerge.scale (427179916800 : Int) atom1377Coded)) := by
  rw [block019_data_flat002_step, block019_data_flat000_original, block019_data_flat001_original]
def block019_data_flat003 : CoefficientMerge.Poly := [(nat_lit 3711, Int.ofNat (nat_lit 3093893233200))]
theorem block019_data_flat003_step : block019_data_flat003 = (CoefficientMerge.scale (3093893233200 : Int) atom1378Coded) := by decide +kernel
theorem block019_data_flat003_original : block019_data_flat003 = (CoefficientMerge.scale (3093893233200 : Int) atom1378Coded) := by
  rw [block019_data_flat003_step]
def block019_data_flat004 : CoefficientMerge.Poly := [(nat_lit 3726, Int.ofNat (nat_lit 1414429430400))]
theorem block019_data_flat004_step : block019_data_flat004 = (CoefficientMerge.scale (1414429430400 : Int) atom1379Coded) := by decide +kernel
theorem block019_data_flat004_original : block019_data_flat004 = (CoefficientMerge.scale (1414429430400 : Int) atom1379Coded) := by
  rw [block019_data_flat004_step]
def block019_data_flat005 : CoefficientMerge.Poly := [(nat_lit 3727, Int.ofNat (nat_lit 518028134400))]
theorem block019_data_flat005_step : block019_data_flat005 = (CoefficientMerge.scale (518028134400 : Int) atom1380Coded) := by decide +kernel
theorem block019_data_flat005_original : block019_data_flat005 = (CoefficientMerge.scale (518028134400 : Int) atom1380Coded) := by
  rw [block019_data_flat005_step]
def block019_data_flat006 : CoefficientMerge.Poly := [(nat_lit 3726, Int.ofNat (nat_lit 1414429430400)), (nat_lit 3727, Int.ofNat (nat_lit 518028134400))]
theorem block019_data_flat006_step : block019_data_flat006 = (CoefficientMerge.fastMerge block019_data_flat004 block019_data_flat005) := by decide +kernel
theorem block019_data_flat006_original : block019_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1414429430400 : Int) atom1379Coded) (CoefficientMerge.scale (518028134400 : Int) atom1380Coded)) := by
  rw [block019_data_flat006_step, block019_data_flat004_original, block019_data_flat005_original]
def block019_data_flat007 : CoefficientMerge.Poly := [(nat_lit 3711, Int.ofNat (nat_lit 3093893233200)), (nat_lit 3726, Int.ofNat (nat_lit 1414429430400)), (nat_lit 3727, Int.ofNat (nat_lit 518028134400))]
theorem block019_data_flat007_step : block019_data_flat007 = (CoefficientMerge.fastMerge block019_data_flat003 block019_data_flat006) := by decide +kernel
theorem block019_data_flat007_original : block019_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3093893233200 : Int) atom1378Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1414429430400 : Int) atom1379Coded) (CoefficientMerge.scale (518028134400 : Int) atom1380Coded))) := by
  rw [block019_data_flat007_step, block019_data_flat003_original, block019_data_flat006_original]
def block019_data_flat008 : CoefficientMerge.Poly := [(nat_lit 3706, Int.ofNat (nat_lit 770276908800)), (nat_lit 3707, Int.ofNat (nat_lit 427179916800)), (nat_lit 3711, Int.ofNat (nat_lit 3093893233200)), (nat_lit 3726, Int.ofNat (nat_lit 1414429430400)), (nat_lit 3727, Int.ofNat (nat_lit 518028134400))]
theorem block019_data_flat008_step : block019_data_flat008 = (CoefficientMerge.fastMerge block019_data_flat002 block019_data_flat007) := by decide +kernel
theorem block019_data_flat008_original : block019_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (770276908800 : Int) atom1376Coded) (CoefficientMerge.scale (427179916800 : Int) atom1377Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3093893233200 : Int) atom1378Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1414429430400 : Int) atom1379Coded) (CoefficientMerge.scale (518028134400 : Int) atom1380Coded)))) := by
  rw [block019_data_flat008_step, block019_data_flat002_original, block019_data_flat007_original]
def block019_data_flat009 : CoefficientMerge.Poly := [(nat_lit 3730, Int.ofNat (nat_lit 427179916800))]
theorem block019_data_flat009_step : block019_data_flat009 = (CoefficientMerge.scale (427179916800 : Int) atom1381Coded) := by decide +kernel
theorem block019_data_flat009_original : block019_data_flat009 = (CoefficientMerge.scale (427179916800 : Int) atom1381Coded) := by
  rw [block019_data_flat009_step]
def block019_data_flat010 : CoefficientMerge.Poly := [(nat_lit 3731, Int.ofNat (nat_lit 854359833600))]
theorem block019_data_flat010_step : block019_data_flat010 = (CoefficientMerge.scale (854359833600 : Int) atom1382Coded) := by decide +kernel
theorem block019_data_flat010_original : block019_data_flat010 = (CoefficientMerge.scale (854359833600 : Int) atom1382Coded) := by
  rw [block019_data_flat010_step]
def block019_data_flat011 : CoefficientMerge.Poly := [(nat_lit 3730, Int.ofNat (nat_lit 427179916800)), (nat_lit 3731, Int.ofNat (nat_lit 854359833600))]
theorem block019_data_flat011_step : block019_data_flat011 = (CoefficientMerge.fastMerge block019_data_flat009 block019_data_flat010) := by decide +kernel
theorem block019_data_flat011_original : block019_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1381Coded) (CoefficientMerge.scale (854359833600 : Int) atom1382Coded)) := by
  rw [block019_data_flat011_step, block019_data_flat009_original, block019_data_flat010_original]
def block019_data_flat012 : CoefficientMerge.Poly := [(nat_lit 3732, Int.ofNat (nat_lit 5687746762320))]
theorem block019_data_flat012_step : block019_data_flat012 = (CoefficientMerge.scale (5687746762320 : Int) atom1383Coded) := by decide +kernel
theorem block019_data_flat012_original : block019_data_flat012 = (CoefficientMerge.scale (5687746762320 : Int) atom1383Coded) := by
  rw [block019_data_flat012_step]
def block019_data_flat013 : CoefficientMerge.Poly := [(nat_lit 3734, Int.ofNat (nat_lit 2944323370800))]
theorem block019_data_flat013_step : block019_data_flat013 = (CoefficientMerge.scale (2944323370800 : Int) atom1384Coded) := by decide +kernel
theorem block019_data_flat013_original : block019_data_flat013 = (CoefficientMerge.scale (2944323370800 : Int) atom1384Coded) := by
  rw [block019_data_flat013_step]
def block019_data_flat014 : CoefficientMerge.Poly := [(nat_lit 3735, Int.ofNat (nat_lit 5786258284800))]
theorem block019_data_flat014_step : block019_data_flat014 = (CoefficientMerge.scale (5786258284800 : Int) atom1385Coded) := by decide +kernel
theorem block019_data_flat014_original : block019_data_flat014 = (CoefficientMerge.scale (5786258284800 : Int) atom1385Coded) := by
  rw [block019_data_flat014_step]
def block019_data_flat015 : CoefficientMerge.Poly := [(nat_lit 3734, Int.ofNat (nat_lit 2944323370800)), (nat_lit 3735, Int.ofNat (nat_lit 5786258284800))]
theorem block019_data_flat015_step : block019_data_flat015 = (CoefficientMerge.fastMerge block019_data_flat013 block019_data_flat014) := by decide +kernel
theorem block019_data_flat015_original : block019_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2944323370800 : Int) atom1384Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1385Coded)) := by
  rw [block019_data_flat015_step, block019_data_flat013_original, block019_data_flat014_original]
def block019_data_flat016 : CoefficientMerge.Poly := [(nat_lit 3732, Int.ofNat (nat_lit 5687746762320)), (nat_lit 3734, Int.ofNat (nat_lit 2944323370800)), (nat_lit 3735, Int.ofNat (nat_lit 5786258284800))]
theorem block019_data_flat016_step : block019_data_flat016 = (CoefficientMerge.fastMerge block019_data_flat012 block019_data_flat015) := by decide +kernel
theorem block019_data_flat016_original : block019_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5687746762320 : Int) atom1383Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2944323370800 : Int) atom1384Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1385Coded))) := by
  rw [block019_data_flat016_step, block019_data_flat012_original, block019_data_flat015_original]
def block019_data_flat017 : CoefficientMerge.Poly := [(nat_lit 3730, Int.ofNat (nat_lit 427179916800)), (nat_lit 3731, Int.ofNat (nat_lit 854359833600)), (nat_lit 3732, Int.ofNat (nat_lit 5687746762320)), (nat_lit 3734, Int.ofNat (nat_lit 2944323370800)), (nat_lit 3735, Int.ofNat (nat_lit 5786258284800))]
theorem block019_data_flat017_step : block019_data_flat017 = (CoefficientMerge.fastMerge block019_data_flat011 block019_data_flat016) := by decide +kernel
theorem block019_data_flat017_original : block019_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1381Coded) (CoefficientMerge.scale (854359833600 : Int) atom1382Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5687746762320 : Int) atom1383Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2944323370800 : Int) atom1384Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1385Coded)))) := by
  rw [block019_data_flat017_step, block019_data_flat011_original, block019_data_flat016_original]
def block019_data_flat018 : CoefficientMerge.Poly := [(nat_lit 3706, Int.ofNat (nat_lit 770276908800)), (nat_lit 3707, Int.ofNat (nat_lit 427179916800)), (nat_lit 3711, Int.ofNat (nat_lit 3093893233200)), (nat_lit 3726, Int.ofNat (nat_lit 1414429430400)), (nat_lit 3727, Int.ofNat (nat_lit 518028134400)), (nat_lit 3730, Int.ofNat (nat_lit 427179916800)), (nat_lit 3731, Int.ofNat (nat_lit 854359833600)), (nat_lit 3732, Int.ofNat (nat_lit 5687746762320)), (nat_lit 3734, Int.ofNat (nat_lit 2944323370800)), (nat_lit 3735, Int.ofNat (nat_lit 5786258284800))]
theorem block019_data_flat018_step : block019_data_flat018 = (CoefficientMerge.fastMerge block019_data_flat008 block019_data_flat017) := by decide +kernel
theorem block019_data_flat018_original : block019_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (770276908800 : Int) atom1376Coded) (CoefficientMerge.scale (427179916800 : Int) atom1377Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3093893233200 : Int) atom1378Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1414429430400 : Int) atom1379Coded) (CoefficientMerge.scale (518028134400 : Int) atom1380Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1381Coded) (CoefficientMerge.scale (854359833600 : Int) atom1382Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5687746762320 : Int) atom1383Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2944323370800 : Int) atom1384Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1385Coded))))) := by
  rw [block019_data_flat018_step, block019_data_flat008_original, block019_data_flat017_original]
def block019_data_flat019 : CoefficientMerge.Poly := [(nat_lit 3736, Int.ofNat (nat_lit 11171238059520))]
theorem block019_data_flat019_step : block019_data_flat019 = (CoefficientMerge.scale (11171238059520 : Int) atom1386Coded) := by decide +kernel
theorem block019_data_flat019_original : block019_data_flat019 = (CoefficientMerge.scale (11171238059520 : Int) atom1386Coded) := by
  rw [block019_data_flat019_step]
def block019_data_flat020 : CoefficientMerge.Poly := [(nat_lit 3737, Int.ofNat (nat_lit 17391151612800))]
theorem block019_data_flat020_step : block019_data_flat020 = (CoefficientMerge.scale (17391151612800 : Int) atom1387Coded) := by decide +kernel
theorem block019_data_flat020_original : block019_data_flat020 = (CoefficientMerge.scale (17391151612800 : Int) atom1387Coded) := by
  rw [block019_data_flat020_step]
def block019_data_flat021 : CoefficientMerge.Poly := [(nat_lit 3736, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3737, Int.ofNat (nat_lit 17391151612800))]
theorem block019_data_flat021_step : block019_data_flat021 = (CoefficientMerge.fastMerge block019_data_flat019 block019_data_flat020) := by decide +kernel
theorem block019_data_flat021_original : block019_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1386Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1387Coded)) := by
  rw [block019_data_flat021_step, block019_data_flat019_original, block019_data_flat020_original]
def block019_data_flat022 : CoefficientMerge.Poly := [(nat_lit 3748, Int.ofNat (nat_lit 1834844054400))]
theorem block019_data_flat022_step : block019_data_flat022 = (CoefficientMerge.scale (1834844054400 : Int) atom1388Coded) := by decide +kernel
theorem block019_data_flat022_original : block019_data_flat022 = (CoefficientMerge.scale (1834844054400 : Int) atom1388Coded) := by
  rw [block019_data_flat022_step]
def block019_data_flat023 : CoefficientMerge.Poly := [(nat_lit 3749, Int.ofNat (nat_lit 2647162425600))]
theorem block019_data_flat023_step : block019_data_flat023 = (CoefficientMerge.scale (2647162425600 : Int) atom1389Coded) := by decide +kernel
theorem block019_data_flat023_original : block019_data_flat023 = (CoefficientMerge.scale (2647162425600 : Int) atom1389Coded) := by
  rw [block019_data_flat023_step]
def block019_data_flat024 : CoefficientMerge.Poly := [(nat_lit 3750, Int.ofNat (nat_lit 2478996576000))]
theorem block019_data_flat024_step : block019_data_flat024 = (CoefficientMerge.scale (2478996576000 : Int) atom1390Coded) := by decide +kernel
theorem block019_data_flat024_original : block019_data_flat024 = (CoefficientMerge.scale (2478996576000 : Int) atom1390Coded) := by
  rw [block019_data_flat024_step]
def block019_data_flat025 : CoefficientMerge.Poly := [(nat_lit 3749, Int.ofNat (nat_lit 2647162425600)), (nat_lit 3750, Int.ofNat (nat_lit 2478996576000))]
theorem block019_data_flat025_step : block019_data_flat025 = (CoefficientMerge.fastMerge block019_data_flat023 block019_data_flat024) := by decide +kernel
theorem block019_data_flat025_original : block019_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2647162425600 : Int) atom1389Coded) (CoefficientMerge.scale (2478996576000 : Int) atom1390Coded)) := by
  rw [block019_data_flat025_step, block019_data_flat023_original, block019_data_flat024_original]
def block019_data_flat026 : CoefficientMerge.Poly := [(nat_lit 3748, Int.ofNat (nat_lit 1834844054400)), (nat_lit 3749, Int.ofNat (nat_lit 2647162425600)), (nat_lit 3750, Int.ofNat (nat_lit 2478996576000))]
theorem block019_data_flat026_step : block019_data_flat026 = (CoefficientMerge.fastMerge block019_data_flat022 block019_data_flat025) := by decide +kernel
theorem block019_data_flat026_original : block019_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1834844054400 : Int) atom1388Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2647162425600 : Int) atom1389Coded) (CoefficientMerge.scale (2478996576000 : Int) atom1390Coded))) := by
  rw [block019_data_flat026_step, block019_data_flat022_original, block019_data_flat025_original]
def block019_data_flat027 : CoefficientMerge.Poly := [(nat_lit 3736, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3737, Int.ofNat (nat_lit 17391151612800)), (nat_lit 3748, Int.ofNat (nat_lit 1834844054400)), (nat_lit 3749, Int.ofNat (nat_lit 2647162425600)), (nat_lit 3750, Int.ofNat (nat_lit 2478996576000))]
theorem block019_data_flat027_step : block019_data_flat027 = (CoefficientMerge.fastMerge block019_data_flat021 block019_data_flat026) := by decide +kernel
theorem block019_data_flat027_original : block019_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1386Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1387Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1834844054400 : Int) atom1388Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2647162425600 : Int) atom1389Coded) (CoefficientMerge.scale (2478996576000 : Int) atom1390Coded)))) := by
  rw [block019_data_flat027_step, block019_data_flat021_original, block019_data_flat026_original]
def block019_data_flat028 : CoefficientMerge.Poly := [(nat_lit 3751, Int.ofNat (nat_lit 3165190560000))]
theorem block019_data_flat028_step : block019_data_flat028 = (CoefficientMerge.scale (3165190560000 : Int) atom1391Coded) := by decide +kernel
theorem block019_data_flat028_original : block019_data_flat028 = (CoefficientMerge.scale (3165190560000 : Int) atom1391Coded) := by
  rw [block019_data_flat028_step]
def block019_data_flat029 : CoefficientMerge.Poly := [(nat_lit 3752, Int.ofNat (nat_lit 3851384544000))]
theorem block019_data_flat029_step : block019_data_flat029 = (CoefficientMerge.scale (3851384544000 : Int) atom1392Coded) := by decide +kernel
theorem block019_data_flat029_original : block019_data_flat029 = (CoefficientMerge.scale (3851384544000 : Int) atom1392Coded) := by
  rw [block019_data_flat029_step]
def block019_data_flat030 : CoefficientMerge.Poly := [(nat_lit 3751, Int.ofNat (nat_lit 3165190560000)), (nat_lit 3752, Int.ofNat (nat_lit 3851384544000))]
theorem block019_data_flat030_step : block019_data_flat030 = (CoefficientMerge.fastMerge block019_data_flat028 block019_data_flat029) := by decide +kernel
theorem block019_data_flat030_original : block019_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3165190560000 : Int) atom1391Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1392Coded)) := by
  rw [block019_data_flat030_step, block019_data_flat028_original, block019_data_flat029_original]
def block019_data_flat031 : CoefficientMerge.Poly := [(nat_lit 3753, Int.ofNat (nat_lit 7803362548800))]
theorem block019_data_flat031_step : block019_data_flat031 = (CoefficientMerge.scale (7803362548800 : Int) atom1393Coded) := by decide +kernel
theorem block019_data_flat031_original : block019_data_flat031 = (CoefficientMerge.scale (7803362548800 : Int) atom1393Coded) := by
  rw [block019_data_flat031_step]
def block019_data_flat032 : CoefficientMerge.Poly := [(nat_lit 3754, Int.ofNat (nat_lit 2139543982800))]
theorem block019_data_flat032_step : block019_data_flat032 = (CoefficientMerge.scale (2139543982800 : Int) atom1394Coded) := by decide +kernel
theorem block019_data_flat032_original : block019_data_flat032 = (CoefficientMerge.scale (2139543982800 : Int) atom1394Coded) := by
  rw [block019_data_flat032_step]
def block019_data_flat033 : CoefficientMerge.Poly := [(nat_lit 3755, Int.ofNat (nat_lit 9372338136000))]
theorem block019_data_flat033_step : block019_data_flat033 = (CoefficientMerge.scale (9372338136000 : Int) atom1395Coded) := by decide +kernel
theorem block019_data_flat033_original : block019_data_flat033 = (CoefficientMerge.scale (9372338136000 : Int) atom1395Coded) := by
  rw [block019_data_flat033_step]
def block019_data_flat034 : CoefficientMerge.Poly := [(nat_lit 3754, Int.ofNat (nat_lit 2139543982800)), (nat_lit 3755, Int.ofNat (nat_lit 9372338136000))]
theorem block019_data_flat034_step : block019_data_flat034 = (CoefficientMerge.fastMerge block019_data_flat032 block019_data_flat033) := by decide +kernel
theorem block019_data_flat034_original : block019_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2139543982800 : Int) atom1394Coded) (CoefficientMerge.scale (9372338136000 : Int) atom1395Coded)) := by
  rw [block019_data_flat034_step, block019_data_flat032_original, block019_data_flat033_original]
def block019_data_flat035 : CoefficientMerge.Poly := [(nat_lit 3753, Int.ofNat (nat_lit 7803362548800)), (nat_lit 3754, Int.ofNat (nat_lit 2139543982800)), (nat_lit 3755, Int.ofNat (nat_lit 9372338136000))]
theorem block019_data_flat035_step : block019_data_flat035 = (CoefficientMerge.fastMerge block019_data_flat031 block019_data_flat034) := by decide +kernel
theorem block019_data_flat035_original : block019_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7803362548800 : Int) atom1393Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2139543982800 : Int) atom1394Coded) (CoefficientMerge.scale (9372338136000 : Int) atom1395Coded))) := by
  rw [block019_data_flat035_step, block019_data_flat031_original, block019_data_flat034_original]
def block019_data_flat036 : CoefficientMerge.Poly := [(nat_lit 3751, Int.ofNat (nat_lit 3165190560000)), (nat_lit 3752, Int.ofNat (nat_lit 3851384544000)), (nat_lit 3753, Int.ofNat (nat_lit 7803362548800)), (nat_lit 3754, Int.ofNat (nat_lit 2139543982800)), (nat_lit 3755, Int.ofNat (nat_lit 9372338136000))]
theorem block019_data_flat036_step : block019_data_flat036 = (CoefficientMerge.fastMerge block019_data_flat030 block019_data_flat035) := by decide +kernel
theorem block019_data_flat036_original : block019_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3165190560000 : Int) atom1391Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1392Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7803362548800 : Int) atom1393Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2139543982800 : Int) atom1394Coded) (CoefficientMerge.scale (9372338136000 : Int) atom1395Coded)))) := by
  rw [block019_data_flat036_step, block019_data_flat030_original, block019_data_flat035_original]
def block019_data_flat037 : CoefficientMerge.Poly := [(nat_lit 3736, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3737, Int.ofNat (nat_lit 17391151612800)), (nat_lit 3748, Int.ofNat (nat_lit 1834844054400)), (nat_lit 3749, Int.ofNat (nat_lit 2647162425600)), (nat_lit 3750, Int.ofNat (nat_lit 2478996576000)), (nat_lit 3751, Int.ofNat (nat_lit 3165190560000)), (nat_lit 3752, Int.ofNat (nat_lit 3851384544000)), (nat_lit 3753, Int.ofNat (nat_lit 7803362548800)), (nat_lit 3754, Int.ofNat (nat_lit 2139543982800)), (nat_lit 3755, Int.ofNat (nat_lit 9372338136000))]
theorem block019_data_flat037_step : block019_data_flat037 = (CoefficientMerge.fastMerge block019_data_flat027 block019_data_flat036) := by decide +kernel
theorem block019_data_flat037_original : block019_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1386Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1387Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1834844054400 : Int) atom1388Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2647162425600 : Int) atom1389Coded) (CoefficientMerge.scale (2478996576000 : Int) atom1390Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3165190560000 : Int) atom1391Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1392Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7803362548800 : Int) atom1393Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2139543982800 : Int) atom1394Coded) (CoefficientMerge.scale (9372338136000 : Int) atom1395Coded))))) := by
  rw [block019_data_flat037_step, block019_data_flat027_original, block019_data_flat036_original]
def block019_data_flat038 : CoefficientMerge.Poly := [(nat_lit 3706, Int.ofNat (nat_lit 770276908800)), (nat_lit 3707, Int.ofNat (nat_lit 427179916800)), (nat_lit 3711, Int.ofNat (nat_lit 3093893233200)), (nat_lit 3726, Int.ofNat (nat_lit 1414429430400)), (nat_lit 3727, Int.ofNat (nat_lit 518028134400)), (nat_lit 3730, Int.ofNat (nat_lit 427179916800)), (nat_lit 3731, Int.ofNat (nat_lit 854359833600)), (nat_lit 3732, Int.ofNat (nat_lit 5687746762320)), (nat_lit 3734, Int.ofNat (nat_lit 2944323370800)), (nat_lit 3735, Int.ofNat (nat_lit 5786258284800)), (nat_lit 3736, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3737, Int.ofNat (nat_lit 17391151612800)), (nat_lit 3748, Int.ofNat (nat_lit 1834844054400)), (nat_lit 3749, Int.ofNat (nat_lit 2647162425600)), (nat_lit 3750, Int.ofNat (nat_lit 2478996576000)), (nat_lit 3751, Int.ofNat (nat_lit 3165190560000)), (nat_lit 3752, Int.ofNat (nat_lit 3851384544000)), (nat_lit 3753, Int.ofNat (nat_lit 7803362548800)), (nat_lit 3754, Int.ofNat (nat_lit 2139543982800)), (nat_lit 3755, Int.ofNat (nat_lit 9372338136000))]
theorem block019_data_flat038_step : block019_data_flat038 = (CoefficientMerge.fastMerge block019_data_flat018 block019_data_flat037) := by decide +kernel
theorem block019_data_flat038_original : block019_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (770276908800 : Int) atom1376Coded) (CoefficientMerge.scale (427179916800 : Int) atom1377Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3093893233200 : Int) atom1378Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1414429430400 : Int) atom1379Coded) (CoefficientMerge.scale (518028134400 : Int) atom1380Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1381Coded) (CoefficientMerge.scale (854359833600 : Int) atom1382Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5687746762320 : Int) atom1383Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2944323370800 : Int) atom1384Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1385Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1386Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1387Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1834844054400 : Int) atom1388Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2647162425600 : Int) atom1389Coded) (CoefficientMerge.scale (2478996576000 : Int) atom1390Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3165190560000 : Int) atom1391Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1392Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7803362548800 : Int) atom1393Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2139543982800 : Int) atom1394Coded) (CoefficientMerge.scale (9372338136000 : Int) atom1395Coded)))))) := by
  rw [block019_data_flat038_step, block019_data_flat018_original, block019_data_flat037_original]
def block019_data_flat039 : CoefficientMerge.Poly := [(nat_lit 3756, Int.ofNat (nat_lit 11410652912400))]
theorem block019_data_flat039_step : block019_data_flat039 = (CoefficientMerge.scale (11410652912400 : Int) atom1396Coded) := by decide +kernel
theorem block019_data_flat039_original : block019_data_flat039 = (CoefficientMerge.scale (11410652912400 : Int) atom1396Coded) := by
  rw [block019_data_flat039_step]
def block019_data_flat040 : CoefficientMerge.Poly := [(nat_lit 3757, Int.ofNat (nat_lit 20176096474800))]
theorem block019_data_flat040_step : block019_data_flat040 = (CoefficientMerge.scale (20176096474800 : Int) atom1397Coded) := by decide +kernel
theorem block019_data_flat040_original : block019_data_flat040 = (CoefficientMerge.scale (20176096474800 : Int) atom1397Coded) := by
  rw [block019_data_flat040_step]
def block019_data_flat041 : CoefficientMerge.Poly := [(nat_lit 3756, Int.ofNat (nat_lit 11410652912400)), (nat_lit 3757, Int.ofNat (nat_lit 20176096474800))]
theorem block019_data_flat041_step : block019_data_flat041 = (CoefficientMerge.fastMerge block019_data_flat039 block019_data_flat040) := by decide +kernel
theorem block019_data_flat041_original : block019_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11410652912400 : Int) atom1396Coded) (CoefficientMerge.scale (20176096474800 : Int) atom1397Coded)) := by
  rw [block019_data_flat041_step, block019_data_flat039_original, block019_data_flat040_original]
def block019_data_flat042 : CoefficientMerge.Poly := [(nat_lit 3758, Int.ofNat (nat_lit 30348257839200))]
theorem block019_data_flat042_step : block019_data_flat042 = (CoefficientMerge.scale (30348257839200 : Int) atom1398Coded) := by decide +kernel
theorem block019_data_flat042_original : block019_data_flat042 = (CoefficientMerge.scale (30348257839200 : Int) atom1398Coded) := by
  rw [block019_data_flat042_step]
def block019_data_flat043 : CoefficientMerge.Poly := [(nat_lit 3770, Int.ofNat (nat_lit 3543563721600))]
theorem block019_data_flat043_step : block019_data_flat043 = (CoefficientMerge.scale (3543563721600 : Int) atom1399Coded) := by decide +kernel
theorem block019_data_flat043_original : block019_data_flat043 = (CoefficientMerge.scale (3543563721600 : Int) atom1399Coded) := by
  rw [block019_data_flat043_step]
def block019_data_flat044 : CoefficientMerge.Poly := [(nat_lit 3771, Int.ofNat (nat_lit 5560104211200))]
theorem block019_data_flat044_step : block019_data_flat044 = (CoefficientMerge.scale (5560104211200 : Int) atom1400Coded) := by decide +kernel
theorem block019_data_flat044_original : block019_data_flat044 = (CoefficientMerge.scale (5560104211200 : Int) atom1400Coded) := by
  rw [block019_data_flat044_step]
def block019_data_flat045 : CoefficientMerge.Poly := [(nat_lit 3770, Int.ofNat (nat_lit 3543563721600)), (nat_lit 3771, Int.ofNat (nat_lit 5560104211200))]
theorem block019_data_flat045_step : block019_data_flat045 = (CoefficientMerge.fastMerge block019_data_flat043 block019_data_flat044) := by decide +kernel
theorem block019_data_flat045_original : block019_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3543563721600 : Int) atom1399Coded) (CoefficientMerge.scale (5560104211200 : Int) atom1400Coded)) := by
  rw [block019_data_flat045_step, block019_data_flat043_original, block019_data_flat044_original]
def block019_data_flat046 : CoefficientMerge.Poly := [(nat_lit 3758, Int.ofNat (nat_lit 30348257839200)), (nat_lit 3770, Int.ofNat (nat_lit 3543563721600)), (nat_lit 3771, Int.ofNat (nat_lit 5560104211200))]
theorem block019_data_flat046_step : block019_data_flat046 = (CoefficientMerge.fastMerge block019_data_flat042 block019_data_flat045) := by decide +kernel
theorem block019_data_flat046_original : block019_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30348257839200 : Int) atom1398Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3543563721600 : Int) atom1399Coded) (CoefficientMerge.scale (5560104211200 : Int) atom1400Coded))) := by
  rw [block019_data_flat046_step, block019_data_flat042_original, block019_data_flat045_original]
def block019_data_flat047 : CoefficientMerge.Poly := [(nat_lit 3756, Int.ofNat (nat_lit 11410652912400)), (nat_lit 3757, Int.ofNat (nat_lit 20176096474800)), (nat_lit 3758, Int.ofNat (nat_lit 30348257839200)), (nat_lit 3770, Int.ofNat (nat_lit 3543563721600)), (nat_lit 3771, Int.ofNat (nat_lit 5560104211200))]
theorem block019_data_flat047_step : block019_data_flat047 = (CoefficientMerge.fastMerge block019_data_flat041 block019_data_flat046) := by decide +kernel
theorem block019_data_flat047_original : block019_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11410652912400 : Int) atom1396Coded) (CoefficientMerge.scale (20176096474800 : Int) atom1397Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30348257839200 : Int) atom1398Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3543563721600 : Int) atom1399Coded) (CoefficientMerge.scale (5560104211200 : Int) atom1400Coded)))) := by
  rw [block019_data_flat047_step, block019_data_flat041_original, block019_data_flat046_original]
def block019_data_flat048 : CoefficientMerge.Poly := [(nat_lit 3772, Int.ofNat (nat_lit 6337146412800))]
theorem block019_data_flat048_step : block019_data_flat048 = (CoefficientMerge.scale (6337146412800 : Int) atom1401Coded) := by decide +kernel
theorem block019_data_flat048_original : block019_data_flat048 = (CoefficientMerge.scale (6337146412800 : Int) atom1401Coded) := by
  rw [block019_data_flat048_step]
def block019_data_flat049 : CoefficientMerge.Poly := [(nat_lit 3773, Int.ofNat (nat_lit 7114188614400))]
theorem block019_data_flat049_step : block019_data_flat049 = (CoefficientMerge.scale (7114188614400 : Int) atom1402Coded) := by decide +kernel
theorem block019_data_flat049_original : block019_data_flat049 = (CoefficientMerge.scale (7114188614400 : Int) atom1402Coded) := by
  rw [block019_data_flat049_step]
def block019_data_flat050 : CoefficientMerge.Poly := [(nat_lit 3772, Int.ofNat (nat_lit 6337146412800)), (nat_lit 3773, Int.ofNat (nat_lit 7114188614400))]
theorem block019_data_flat050_step : block019_data_flat050 = (CoefficientMerge.fastMerge block019_data_flat048 block019_data_flat049) := by decide +kernel
theorem block019_data_flat050_original : block019_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6337146412800 : Int) atom1401Coded) (CoefficientMerge.scale (7114188614400 : Int) atom1402Coded)) := by
  rw [block019_data_flat050_step, block019_data_flat048_original, block019_data_flat049_original]
def block019_data_flat051 : CoefficientMerge.Poly := [(nat_lit 3774, Int.ofNat (nat_lit 12510442929600))]
theorem block019_data_flat051_step : block019_data_flat051 = (CoefficientMerge.scale (12510442929600 : Int) atom1403Coded) := by decide +kernel
theorem block019_data_flat051_original : block019_data_flat051 = (CoefficientMerge.scale (12510442929600 : Int) atom1403Coded) := by
  rw [block019_data_flat051_step]
def block019_data_flat052 : CoefficientMerge.Poly := [(nat_lit 3775, Int.ofNat (nat_lit 8456065254000))]
theorem block019_data_flat052_step : block019_data_flat052 = (CoefficientMerge.scale (8456065254000 : Int) atom1404Coded) := by decide +kernel
theorem block019_data_flat052_original : block019_data_flat052 = (CoefficientMerge.scale (8456065254000 : Int) atom1404Coded) := by
  rw [block019_data_flat052_step]
def block019_data_flat053 : CoefficientMerge.Poly := [(nat_lit 3776, Int.ofNat (nat_lit 19774108468800))]
theorem block019_data_flat053_step : block019_data_flat053 = (CoefficientMerge.scale (19774108468800 : Int) atom1405Coded) := by decide +kernel
theorem block019_data_flat053_original : block019_data_flat053 = (CoefficientMerge.scale (19774108468800 : Int) atom1405Coded) := by
  rw [block019_data_flat053_step]
def block019_data_flat054 : CoefficientMerge.Poly := [(nat_lit 3775, Int.ofNat (nat_lit 8456065254000)), (nat_lit 3776, Int.ofNat (nat_lit 19774108468800))]
theorem block019_data_flat054_step : block019_data_flat054 = (CoefficientMerge.fastMerge block019_data_flat052 block019_data_flat053) := by decide +kernel
theorem block019_data_flat054_original : block019_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8456065254000 : Int) atom1404Coded) (CoefficientMerge.scale (19774108468800 : Int) atom1405Coded)) := by
  rw [block019_data_flat054_step, block019_data_flat052_original, block019_data_flat053_original]
def block019_data_flat055 : CoefficientMerge.Poly := [(nat_lit 3774, Int.ofNat (nat_lit 12510442929600)), (nat_lit 3775, Int.ofNat (nat_lit 8456065254000)), (nat_lit 3776, Int.ofNat (nat_lit 19774108468800))]
theorem block019_data_flat055_step : block019_data_flat055 = (CoefficientMerge.fastMerge block019_data_flat051 block019_data_flat054) := by decide +kernel
theorem block019_data_flat055_original : block019_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12510442929600 : Int) atom1403Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8456065254000 : Int) atom1404Coded) (CoefficientMerge.scale (19774108468800 : Int) atom1405Coded))) := by
  rw [block019_data_flat055_step, block019_data_flat051_original, block019_data_flat054_original]
def block019_data_flat056 : CoefficientMerge.Poly := [(nat_lit 3772, Int.ofNat (nat_lit 6337146412800)), (nat_lit 3773, Int.ofNat (nat_lit 7114188614400)), (nat_lit 3774, Int.ofNat (nat_lit 12510442929600)), (nat_lit 3775, Int.ofNat (nat_lit 8456065254000)), (nat_lit 3776, Int.ofNat (nat_lit 19774108468800))]
theorem block019_data_flat056_step : block019_data_flat056 = (CoefficientMerge.fastMerge block019_data_flat050 block019_data_flat055) := by decide +kernel
theorem block019_data_flat056_original : block019_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6337146412800 : Int) atom1401Coded) (CoefficientMerge.scale (7114188614400 : Int) atom1402Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12510442929600 : Int) atom1403Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8456065254000 : Int) atom1404Coded) (CoefficientMerge.scale (19774108468800 : Int) atom1405Coded)))) := by
  rw [block019_data_flat056_step, block019_data_flat050_original, block019_data_flat055_original]
def block019_data_flat057 : CoefficientMerge.Poly := [(nat_lit 3756, Int.ofNat (nat_lit 11410652912400)), (nat_lit 3757, Int.ofNat (nat_lit 20176096474800)), (nat_lit 3758, Int.ofNat (nat_lit 30348257839200)), (nat_lit 3770, Int.ofNat (nat_lit 3543563721600)), (nat_lit 3771, Int.ofNat (nat_lit 5560104211200)), (nat_lit 3772, Int.ofNat (nat_lit 6337146412800)), (nat_lit 3773, Int.ofNat (nat_lit 7114188614400)), (nat_lit 3774, Int.ofNat (nat_lit 12510442929600)), (nat_lit 3775, Int.ofNat (nat_lit 8456065254000)), (nat_lit 3776, Int.ofNat (nat_lit 19774108468800))]
theorem block019_data_flat057_step : block019_data_flat057 = (CoefficientMerge.fastMerge block019_data_flat047 block019_data_flat056) := by decide +kernel
theorem block019_data_flat057_original : block019_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11410652912400 : Int) atom1396Coded) (CoefficientMerge.scale (20176096474800 : Int) atom1397Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30348257839200 : Int) atom1398Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3543563721600 : Int) atom1399Coded) (CoefficientMerge.scale (5560104211200 : Int) atom1400Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6337146412800 : Int) atom1401Coded) (CoefficientMerge.scale (7114188614400 : Int) atom1402Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12510442929600 : Int) atom1403Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8456065254000 : Int) atom1404Coded) (CoefficientMerge.scale (19774108468800 : Int) atom1405Coded))))) := by
  rw [block019_data_flat057_step, block019_data_flat047_original, block019_data_flat056_original]
def block019_data_flat058 : CoefficientMerge.Poly := [(nat_lit 3777, Int.ofNat (nat_lit 20318281326000))]
theorem block019_data_flat058_step : block019_data_flat058 = (CoefficientMerge.scale (20318281326000 : Int) atom1406Coded) := by decide +kernel
theorem block019_data_flat058_original : block019_data_flat058 = (CoefficientMerge.scale (20318281326000 : Int) atom1406Coded) := by
  rw [block019_data_flat058_step]
def block019_data_flat059 : CoefficientMerge.Poly := [(nat_lit 3778, Int.ofNat (nat_lit 30113920746000))]
theorem block019_data_flat059_step : block019_data_flat059 = (CoefficientMerge.scale (30113920746000 : Int) atom1407Coded) := by decide +kernel
theorem block019_data_flat059_original : block019_data_flat059 = (CoefficientMerge.scale (30113920746000 : Int) atom1407Coded) := by
  rw [block019_data_flat059_step]
def block019_data_flat060 : CoefficientMerge.Poly := [(nat_lit 3777, Int.ofNat (nat_lit 20318281326000)), (nat_lit 3778, Int.ofNat (nat_lit 30113920746000))]
theorem block019_data_flat060_step : block019_data_flat060 = (CoefficientMerge.fastMerge block019_data_flat058 block019_data_flat059) := by decide +kernel
theorem block019_data_flat060_original : block019_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20318281326000 : Int) atom1406Coded) (CoefficientMerge.scale (30113920746000 : Int) atom1407Coded)) := by
  rw [block019_data_flat060_step, block019_data_flat058_original, block019_data_flat059_original]
def block019_data_flat061 : CoefficientMerge.Poly := [(nat_lit 3779, Int.ofNat (nat_lit 40982814885600))]
theorem block019_data_flat061_step : block019_data_flat061 = (CoefficientMerge.scale (40982814885600 : Int) atom1408Coded) := by decide +kernel
theorem block019_data_flat061_original : block019_data_flat061 = (CoefficientMerge.scale (40982814885600 : Int) atom1408Coded) := by
  rw [block019_data_flat061_step]
def block019_data_flat062 : CoefficientMerge.Poly := [(nat_lit 3792, Int.ofNat (nat_lit 5174965756800))]
theorem block019_data_flat062_step : block019_data_flat062 = (CoefficientMerge.scale (5174965756800 : Int) atom1409Coded) := by decide +kernel
theorem block019_data_flat062_original : block019_data_flat062 = (CoefficientMerge.scale (5174965756800 : Int) atom1409Coded) := by
  rw [block019_data_flat062_step]
def block019_data_flat063 : CoefficientMerge.Poly := [(nat_lit 3793, Int.ofNat (nat_lit 10622476166400))]
theorem block019_data_flat063_step : block019_data_flat063 = (CoefficientMerge.scale (10622476166400 : Int) atom1410Coded) := by decide +kernel
theorem block019_data_flat063_original : block019_data_flat063 = (CoefficientMerge.scale (10622476166400 : Int) atom1410Coded) := by
  rw [block019_data_flat063_step]
def block019_data_flat064 : CoefficientMerge.Poly := [(nat_lit 3792, Int.ofNat (nat_lit 5174965756800)), (nat_lit 3793, Int.ofNat (nat_lit 10622476166400))]
theorem block019_data_flat064_step : block019_data_flat064 = (CoefficientMerge.fastMerge block019_data_flat062 block019_data_flat063) := by decide +kernel
theorem block019_data_flat064_original : block019_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5174965756800 : Int) atom1409Coded) (CoefficientMerge.scale (10622476166400 : Int) atom1410Coded)) := by
  rw [block019_data_flat064_step, block019_data_flat062_original, block019_data_flat063_original]
def block019_data_flat065 : CoefficientMerge.Poly := [(nat_lit 3779, Int.ofNat (nat_lit 40982814885600)), (nat_lit 3792, Int.ofNat (nat_lit 5174965756800)), (nat_lit 3793, Int.ofNat (nat_lit 10622476166400))]
theorem block019_data_flat065_step : block019_data_flat065 = (CoefficientMerge.fastMerge block019_data_flat061 block019_data_flat064) := by decide +kernel
theorem block019_data_flat065_original : block019_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40982814885600 : Int) atom1408Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5174965756800 : Int) atom1409Coded) (CoefficientMerge.scale (10622476166400 : Int) atom1410Coded))) := by
  rw [block019_data_flat065_step, block019_data_flat061_original, block019_data_flat064_original]
def block019_data_flat066 : CoefficientMerge.Poly := [(nat_lit 3777, Int.ofNat (nat_lit 20318281326000)), (nat_lit 3778, Int.ofNat (nat_lit 30113920746000)), (nat_lit 3779, Int.ofNat (nat_lit 40982814885600)), (nat_lit 3792, Int.ofNat (nat_lit 5174965756800)), (nat_lit 3793, Int.ofNat (nat_lit 10622476166400))]
theorem block019_data_flat066_step : block019_data_flat066 = (CoefficientMerge.fastMerge block019_data_flat060 block019_data_flat065) := by decide +kernel
theorem block019_data_flat066_original : block019_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20318281326000 : Int) atom1406Coded) (CoefficientMerge.scale (30113920746000 : Int) atom1407Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40982814885600 : Int) atom1408Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5174965756800 : Int) atom1409Coded) (CoefficientMerge.scale (10622476166400 : Int) atom1410Coded)))) := by
  rw [block019_data_flat066_step, block019_data_flat060_original, block019_data_flat065_original]
def block019_data_flat067 : CoefficientMerge.Poly := [(nat_lit 3794, Int.ofNat (nat_lit 11322200736000))]
theorem block019_data_flat067_step : block019_data_flat067 = (CoefficientMerge.scale (11322200736000 : Int) atom1411Coded) := by decide +kernel
theorem block019_data_flat067_original : block019_data_flat067 = (CoefficientMerge.scale (11322200736000 : Int) atom1411Coded) := by
  rw [block019_data_flat067_step]
def block019_data_flat068 : CoefficientMerge.Poly := [(nat_lit 3795, Int.ofNat (nat_lit 14101152139200))]
theorem block019_data_flat068_step : block019_data_flat068 = (CoefficientMerge.scale (14101152139200 : Int) atom1412Coded) := by decide +kernel
theorem block019_data_flat068_original : block019_data_flat068 = (CoefficientMerge.scale (14101152139200 : Int) atom1412Coded) := by
  rw [block019_data_flat068_step]
def block019_data_flat069 : CoefficientMerge.Poly := [(nat_lit 3794, Int.ofNat (nat_lit 11322200736000)), (nat_lit 3795, Int.ofNat (nat_lit 14101152139200))]
theorem block019_data_flat069_step : block019_data_flat069 = (CoefficientMerge.fastMerge block019_data_flat067 block019_data_flat068) := by decide +kernel
theorem block019_data_flat069_original : block019_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11322200736000 : Int) atom1411Coded) (CoefficientMerge.scale (14101152139200 : Int) atom1412Coded)) := by
  rw [block019_data_flat069_step, block019_data_flat067_original, block019_data_flat068_original]
def block019_data_flat070 : CoefficientMerge.Poly := [(nat_lit 3796, Int.ofNat (nat_lit 13619552332400))]
theorem block019_data_flat070_step : block019_data_flat070 = (CoefficientMerge.scale (13619552332400 : Int) atom1413Coded) := by decide +kernel
theorem block019_data_flat070_original : block019_data_flat070 = (CoefficientMerge.scale (13619552332400 : Int) atom1413Coded) := by
  rw [block019_data_flat070_step]
def block019_data_flat071 : CoefficientMerge.Poly := [(nat_lit 3797, Int.ofNat (nat_lit 25094037416000))]
theorem block019_data_flat071_step : block019_data_flat071 = (CoefficientMerge.scale (25094037416000 : Int) atom1414Coded) := by decide +kernel
theorem block019_data_flat071_original : block019_data_flat071 = (CoefficientMerge.scale (25094037416000 : Int) atom1414Coded) := by
  rw [block019_data_flat071_step]
def block019_data_flat072 : CoefficientMerge.Poly := [(nat_lit 3798, Int.ofNat (nat_lit 27327261530800))]
theorem block019_data_flat072_step : block019_data_flat072 = (CoefficientMerge.scale (27327261530800 : Int) atom1415Coded) := by decide +kernel
theorem block019_data_flat072_original : block019_data_flat072 = (CoefficientMerge.scale (27327261530800 : Int) atom1415Coded) := by
  rw [block019_data_flat072_step]
def block019_data_flat073 : CoefficientMerge.Poly := [(nat_lit 3797, Int.ofNat (nat_lit 25094037416000)), (nat_lit 3798, Int.ofNat (nat_lit 27327261530800))]
theorem block019_data_flat073_step : block019_data_flat073 = (CoefficientMerge.fastMerge block019_data_flat071 block019_data_flat072) := by decide +kernel
theorem block019_data_flat073_original : block019_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25094037416000 : Int) atom1414Coded) (CoefficientMerge.scale (27327261530800 : Int) atom1415Coded)) := by
  rw [block019_data_flat073_step, block019_data_flat071_original, block019_data_flat072_original]
def block019_data_flat074 : CoefficientMerge.Poly := [(nat_lit 3796, Int.ofNat (nat_lit 13619552332400)), (nat_lit 3797, Int.ofNat (nat_lit 25094037416000)), (nat_lit 3798, Int.ofNat (nat_lit 27327261530800))]
theorem block019_data_flat074_step : block019_data_flat074 = (CoefficientMerge.fastMerge block019_data_flat070 block019_data_flat073) := by decide +kernel
theorem block019_data_flat074_original : block019_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13619552332400 : Int) atom1413Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25094037416000 : Int) atom1414Coded) (CoefficientMerge.scale (27327261530800 : Int) atom1415Coded))) := by
  rw [block019_data_flat074_step, block019_data_flat070_original, block019_data_flat073_original]
def block019_data_flat075 : CoefficientMerge.Poly := [(nat_lit 3794, Int.ofNat (nat_lit 11322200736000)), (nat_lit 3795, Int.ofNat (nat_lit 14101152139200)), (nat_lit 3796, Int.ofNat (nat_lit 13619552332400)), (nat_lit 3797, Int.ofNat (nat_lit 25094037416000)), (nat_lit 3798, Int.ofNat (nat_lit 27327261530800))]
theorem block019_data_flat075_step : block019_data_flat075 = (CoefficientMerge.fastMerge block019_data_flat069 block019_data_flat074) := by decide +kernel
theorem block019_data_flat075_original : block019_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11322200736000 : Int) atom1411Coded) (CoefficientMerge.scale (14101152139200 : Int) atom1412Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13619552332400 : Int) atom1413Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25094037416000 : Int) atom1414Coded) (CoefficientMerge.scale (27327261530800 : Int) atom1415Coded)))) := by
  rw [block019_data_flat075_step, block019_data_flat069_original, block019_data_flat074_original]
def block019_data_flat076 : CoefficientMerge.Poly := [(nat_lit 3777, Int.ofNat (nat_lit 20318281326000)), (nat_lit 3778, Int.ofNat (nat_lit 30113920746000)), (nat_lit 3779, Int.ofNat (nat_lit 40982814885600)), (nat_lit 3792, Int.ofNat (nat_lit 5174965756800)), (nat_lit 3793, Int.ofNat (nat_lit 10622476166400)), (nat_lit 3794, Int.ofNat (nat_lit 11322200736000)), (nat_lit 3795, Int.ofNat (nat_lit 14101152139200)), (nat_lit 3796, Int.ofNat (nat_lit 13619552332400)), (nat_lit 3797, Int.ofNat (nat_lit 25094037416000)), (nat_lit 3798, Int.ofNat (nat_lit 27327261530800))]
theorem block019_data_flat076_step : block019_data_flat076 = (CoefficientMerge.fastMerge block019_data_flat066 block019_data_flat075) := by decide +kernel
theorem block019_data_flat076_original : block019_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20318281326000 : Int) atom1406Coded) (CoefficientMerge.scale (30113920746000 : Int) atom1407Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40982814885600 : Int) atom1408Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5174965756800 : Int) atom1409Coded) (CoefficientMerge.scale (10622476166400 : Int) atom1410Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11322200736000 : Int) atom1411Coded) (CoefficientMerge.scale (14101152139200 : Int) atom1412Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13619552332400 : Int) atom1413Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25094037416000 : Int) atom1414Coded) (CoefficientMerge.scale (27327261530800 : Int) atom1415Coded))))) := by
  rw [block019_data_flat076_step, block019_data_flat066_original, block019_data_flat075_original]
def block019_data_flat077 : CoefficientMerge.Poly := [(nat_lit 3756, Int.ofNat (nat_lit 11410652912400)), (nat_lit 3757, Int.ofNat (nat_lit 20176096474800)), (nat_lit 3758, Int.ofNat (nat_lit 30348257839200)), (nat_lit 3770, Int.ofNat (nat_lit 3543563721600)), (nat_lit 3771, Int.ofNat (nat_lit 5560104211200)), (nat_lit 3772, Int.ofNat (nat_lit 6337146412800)), (nat_lit 3773, Int.ofNat (nat_lit 7114188614400)), (nat_lit 3774, Int.ofNat (nat_lit 12510442929600)), (nat_lit 3775, Int.ofNat (nat_lit 8456065254000)), (nat_lit 3776, Int.ofNat (nat_lit 19774108468800)), (nat_lit 3777, Int.ofNat (nat_lit 20318281326000)), (nat_lit 3778, Int.ofNat (nat_lit 30113920746000)), (nat_lit 3779, Int.ofNat (nat_lit 40982814885600)), (nat_lit 3792, Int.ofNat (nat_lit 5174965756800)), (nat_lit 3793, Int.ofNat (nat_lit 10622476166400)), (nat_lit 3794, Int.ofNat (nat_lit 11322200736000)), (nat_lit 3795, Int.ofNat (nat_lit 14101152139200)), (nat_lit 3796, Int.ofNat (nat_lit 13619552332400)), (nat_lit 3797, Int.ofNat (nat_lit 25094037416000)), (nat_lit 3798, Int.ofNat (nat_lit 27327261530800))]
theorem block019_data_flat077_step : block019_data_flat077 = (CoefficientMerge.fastMerge block019_data_flat057 block019_data_flat076) := by decide +kernel
theorem block019_data_flat077_original : block019_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11410652912400 : Int) atom1396Coded) (CoefficientMerge.scale (20176096474800 : Int) atom1397Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30348257839200 : Int) atom1398Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3543563721600 : Int) atom1399Coded) (CoefficientMerge.scale (5560104211200 : Int) atom1400Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6337146412800 : Int) atom1401Coded) (CoefficientMerge.scale (7114188614400 : Int) atom1402Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12510442929600 : Int) atom1403Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8456065254000 : Int) atom1404Coded) (CoefficientMerge.scale (19774108468800 : Int) atom1405Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20318281326000 : Int) atom1406Coded) (CoefficientMerge.scale (30113920746000 : Int) atom1407Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40982814885600 : Int) atom1408Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5174965756800 : Int) atom1409Coded) (CoefficientMerge.scale (10622476166400 : Int) atom1410Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11322200736000 : Int) atom1411Coded) (CoefficientMerge.scale (14101152139200 : Int) atom1412Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13619552332400 : Int) atom1413Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25094037416000 : Int) atom1414Coded) (CoefficientMerge.scale (27327261530800 : Int) atom1415Coded)))))) := by
  rw [block019_data_flat077_step, block019_data_flat057_original, block019_data_flat076_original]
def block019_data_flat078 : CoefficientMerge.Poly := [(nat_lit 3706, Int.ofNat (nat_lit 770276908800)), (nat_lit 3707, Int.ofNat (nat_lit 427179916800)), (nat_lit 3711, Int.ofNat (nat_lit 3093893233200)), (nat_lit 3726, Int.ofNat (nat_lit 1414429430400)), (nat_lit 3727, Int.ofNat (nat_lit 518028134400)), (nat_lit 3730, Int.ofNat (nat_lit 427179916800)), (nat_lit 3731, Int.ofNat (nat_lit 854359833600)), (nat_lit 3732, Int.ofNat (nat_lit 5687746762320)), (nat_lit 3734, Int.ofNat (nat_lit 2944323370800)), (nat_lit 3735, Int.ofNat (nat_lit 5786258284800)), (nat_lit 3736, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3737, Int.ofNat (nat_lit 17391151612800)), (nat_lit 3748, Int.ofNat (nat_lit 1834844054400)), (nat_lit 3749, Int.ofNat (nat_lit 2647162425600)), (nat_lit 3750, Int.ofNat (nat_lit 2478996576000)), (nat_lit 3751, Int.ofNat (nat_lit 3165190560000)), (nat_lit 3752, Int.ofNat (nat_lit 3851384544000)), (nat_lit 3753, Int.ofNat (nat_lit 7803362548800)), (nat_lit 3754, Int.ofNat (nat_lit 2139543982800)), (nat_lit 3755, Int.ofNat (nat_lit 9372338136000)), (nat_lit 3756, Int.ofNat (nat_lit 11410652912400)), (nat_lit 3757, Int.ofNat (nat_lit 20176096474800)), (nat_lit 3758, Int.ofNat (nat_lit 30348257839200)), (nat_lit 3770, Int.ofNat (nat_lit 3543563721600)), (nat_lit 3771, Int.ofNat (nat_lit 5560104211200)), (nat_lit 3772, Int.ofNat (nat_lit 6337146412800)), (nat_lit 3773, Int.ofNat (nat_lit 7114188614400)), (nat_lit 3774, Int.ofNat (nat_lit 12510442929600)), (nat_lit 3775, Int.ofNat (nat_lit 8456065254000)), (nat_lit 3776, Int.ofNat (nat_lit 19774108468800)), (nat_lit 3777, Int.ofNat (nat_lit 20318281326000)), (nat_lit 3778, Int.ofNat (nat_lit 30113920746000)), (nat_lit 3779, Int.ofNat (nat_lit 40982814885600)), (nat_lit 3792, Int.ofNat (nat_lit 5174965756800)), (nat_lit 3793, Int.ofNat (nat_lit 10622476166400)), (nat_lit 3794, Int.ofNat (nat_lit 11322200736000)), (nat_lit 3795, Int.ofNat (nat_lit 14101152139200)), (nat_lit 3796, Int.ofNat (nat_lit 13619552332400)), (nat_lit 3797, Int.ofNat (nat_lit 25094037416000)), (nat_lit 3798, Int.ofNat (nat_lit 27327261530800))]
theorem block019_data_flat078_step : block019_data_flat078 = (CoefficientMerge.fastMerge block019_data_flat038 block019_data_flat077) := by decide +kernel
theorem block019_data_flat078_original : block019_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (770276908800 : Int) atom1376Coded) (CoefficientMerge.scale (427179916800 : Int) atom1377Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3093893233200 : Int) atom1378Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1414429430400 : Int) atom1379Coded) (CoefficientMerge.scale (518028134400 : Int) atom1380Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1381Coded) (CoefficientMerge.scale (854359833600 : Int) atom1382Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5687746762320 : Int) atom1383Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2944323370800 : Int) atom1384Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1385Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1386Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1387Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1834844054400 : Int) atom1388Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2647162425600 : Int) atom1389Coded) (CoefficientMerge.scale (2478996576000 : Int) atom1390Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3165190560000 : Int) atom1391Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1392Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7803362548800 : Int) atom1393Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2139543982800 : Int) atom1394Coded) (CoefficientMerge.scale (9372338136000 : Int) atom1395Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11410652912400 : Int) atom1396Coded) (CoefficientMerge.scale (20176096474800 : Int) atom1397Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30348257839200 : Int) atom1398Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3543563721600 : Int) atom1399Coded) (CoefficientMerge.scale (5560104211200 : Int) atom1400Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6337146412800 : Int) atom1401Coded) (CoefficientMerge.scale (7114188614400 : Int) atom1402Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12510442929600 : Int) atom1403Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8456065254000 : Int) atom1404Coded) (CoefficientMerge.scale (19774108468800 : Int) atom1405Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20318281326000 : Int) atom1406Coded) (CoefficientMerge.scale (30113920746000 : Int) atom1407Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40982814885600 : Int) atom1408Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5174965756800 : Int) atom1409Coded) (CoefficientMerge.scale (10622476166400 : Int) atom1410Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11322200736000 : Int) atom1411Coded) (CoefficientMerge.scale (14101152139200 : Int) atom1412Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13619552332400 : Int) atom1413Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25094037416000 : Int) atom1414Coded) (CoefficientMerge.scale (27327261530800 : Int) atom1415Coded))))))) := by
  rw [block019_data_flat078_step, block019_data_flat038_original, block019_data_flat077_original]
def block019_data_flat079 : CoefficientMerge.Poly := [(nat_lit 3799, Int.ofNat (nat_lit 37107275293200))]
theorem block019_data_flat079_step : block019_data_flat079 = (CoefficientMerge.scale (37107275293200 : Int) atom1416Coded) := by decide +kernel
theorem block019_data_flat079_original : block019_data_flat079 = (CoefficientMerge.scale (37107275293200 : Int) atom1416Coded) := by
  rw [block019_data_flat079_step]
def block019_data_flat080 : CoefficientMerge.Poly := [(nat_lit 3800, Int.ofNat (nat_lit 48530465474400))]
theorem block019_data_flat080_step : block019_data_flat080 = (CoefficientMerge.scale (48530465474400 : Int) atom1417Coded) := by decide +kernel
theorem block019_data_flat080_original : block019_data_flat080 = (CoefficientMerge.scale (48530465474400 : Int) atom1417Coded) := by
  rw [block019_data_flat080_step]
def block019_data_flat081 : CoefficientMerge.Poly := [(nat_lit 3799, Int.ofNat (nat_lit 37107275293200)), (nat_lit 3800, Int.ofNat (nat_lit 48530465474400))]
theorem block019_data_flat081_step : block019_data_flat081 = (CoefficientMerge.fastMerge block019_data_flat079 block019_data_flat080) := by decide +kernel
theorem block019_data_flat081_original : block019_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (37107275293200 : Int) atom1416Coded) (CoefficientMerge.scale (48530465474400 : Int) atom1417Coded)) := by
  rw [block019_data_flat081_step, block019_data_flat079_original, block019_data_flat080_original]
def block019_data_flat082 : CoefficientMerge.Poly := [(nat_lit 3814, Int.ofNat (nat_lit 8314429795200))]
theorem block019_data_flat082_step : block019_data_flat082 = (CoefficientMerge.scale (8314429795200 : Int) atom1418Coded) := by decide +kernel
theorem block019_data_flat082_original : block019_data_flat082 = (CoefficientMerge.scale (8314429795200 : Int) atom1418Coded) := by
  rw [block019_data_flat082_step]
def block019_data_flat083 : CoefficientMerge.Poly := [(nat_lit 3815, Int.ofNat (nat_lit 15912566956800))]
theorem block019_data_flat083_step : block019_data_flat083 = (CoefficientMerge.scale (15912566956800 : Int) atom1419Coded) := by decide +kernel
theorem block019_data_flat083_original : block019_data_flat083 = (CoefficientMerge.scale (15912566956800 : Int) atom1419Coded) := by
  rw [block019_data_flat083_step]
def block019_data_flat084 : CoefficientMerge.Poly := [(nat_lit 3816, Int.ofNat (nat_lit 19319098982400))]
theorem block019_data_flat084_step : block019_data_flat084 = (CoefficientMerge.scale (19319098982400 : Int) atom1420Coded) := by decide +kernel
theorem block019_data_flat084_original : block019_data_flat084 = (CoefficientMerge.scale (19319098982400 : Int) atom1420Coded) := by
  rw [block019_data_flat084_step]
def block019_data_flat085 : CoefficientMerge.Poly := [(nat_lit 3815, Int.ofNat (nat_lit 15912566956800)), (nat_lit 3816, Int.ofNat (nat_lit 19319098982400))]
theorem block019_data_flat085_step : block019_data_flat085 = (CoefficientMerge.fastMerge block019_data_flat083 block019_data_flat084) := by decide +kernel
theorem block019_data_flat085_original : block019_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15912566956800 : Int) atom1419Coded) (CoefficientMerge.scale (19319098982400 : Int) atom1420Coded)) := by
  rw [block019_data_flat085_step, block019_data_flat083_original, block019_data_flat084_original]
def block019_data_flat086 : CoefficientMerge.Poly := [(nat_lit 3814, Int.ofNat (nat_lit 8314429795200)), (nat_lit 3815, Int.ofNat (nat_lit 15912566956800)), (nat_lit 3816, Int.ofNat (nat_lit 19319098982400))]
theorem block019_data_flat086_step : block019_data_flat086 = (CoefficientMerge.fastMerge block019_data_flat082 block019_data_flat085) := by decide +kernel
theorem block019_data_flat086_original : block019_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8314429795200 : Int) atom1418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15912566956800 : Int) atom1419Coded) (CoefficientMerge.scale (19319098982400 : Int) atom1420Coded))) := by
  rw [block019_data_flat086_step, block019_data_flat082_original, block019_data_flat085_original]
def block019_data_flat087 : CoefficientMerge.Poly := [(nat_lit 3799, Int.ofNat (nat_lit 37107275293200)), (nat_lit 3800, Int.ofNat (nat_lit 48530465474400)), (nat_lit 3814, Int.ofNat (nat_lit 8314429795200)), (nat_lit 3815, Int.ofNat (nat_lit 15912566956800)), (nat_lit 3816, Int.ofNat (nat_lit 19319098982400))]
theorem block019_data_flat087_step : block019_data_flat087 = (CoefficientMerge.fastMerge block019_data_flat081 block019_data_flat086) := by decide +kernel
theorem block019_data_flat087_original : block019_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37107275293200 : Int) atom1416Coded) (CoefficientMerge.scale (48530465474400 : Int) atom1417Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8314429795200 : Int) atom1418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15912566956800 : Int) atom1419Coded) (CoefficientMerge.scale (19319098982400 : Int) atom1420Coded)))) := by
  rw [block019_data_flat087_step, block019_data_flat081_original, block019_data_flat086_original]
def block019_data_flat088 : CoefficientMerge.Poly := [(nat_lit 3817, Int.ofNat (nat_lit 19329077214000))]
theorem block019_data_flat088_step : block019_data_flat088 = (CoefficientMerge.scale (19329077214000 : Int) atom1421Coded) := by decide +kernel
theorem block019_data_flat088_original : block019_data_flat088 = (CoefficientMerge.scale (19329077214000 : Int) atom1421Coded) := by
  rw [block019_data_flat088_step]
def block019_data_flat089 : CoefficientMerge.Poly := [(nat_lit 3818, Int.ofNat (nat_lit 34558073524800))]
theorem block019_data_flat089_step : block019_data_flat089 = (CoefficientMerge.scale (34558073524800 : Int) atom1422Coded) := by decide +kernel
theorem block019_data_flat089_original : block019_data_flat089 = (CoefficientMerge.scale (34558073524800 : Int) atom1422Coded) := by
  rw [block019_data_flat089_step]
def block019_data_flat090 : CoefficientMerge.Poly := [(nat_lit 3817, Int.ofNat (nat_lit 19329077214000)), (nat_lit 3818, Int.ofNat (nat_lit 34558073524800))]
theorem block019_data_flat090_step : block019_data_flat090 = (CoefficientMerge.fastMerge block019_data_flat088 block019_data_flat089) := by decide +kernel
theorem block019_data_flat090_original : block019_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19329077214000 : Int) atom1421Coded) (CoefficientMerge.scale (34558073524800 : Int) atom1422Coded)) := by
  rw [block019_data_flat090_step, block019_data_flat088_original, block019_data_flat089_original]
def block019_data_flat091 : CoefficientMerge.Poly := [(nat_lit 3819, Int.ofNat (nat_lit 38809323630000))]
theorem block019_data_flat091_step : block019_data_flat091 = (CoefficientMerge.scale (38809323630000 : Int) atom1423Coded) := by decide +kernel
theorem block019_data_flat091_original : block019_data_flat091 = (CoefficientMerge.scale (38809323630000 : Int) atom1423Coded) := by
  rw [block019_data_flat091_step]
def block019_data_flat092 : CoefficientMerge.Poly := [(nat_lit 3820, Int.ofNat (nat_lit 42738457266000))]
theorem block019_data_flat092_step : block019_data_flat092 = (CoefficientMerge.scale (42738457266000 : Int) atom1424Coded) := by decide +kernel
theorem block019_data_flat092_original : block019_data_flat092 = (CoefficientMerge.scale (42738457266000 : Int) atom1424Coded) := by
  rw [block019_data_flat092_step]
def block019_data_flat093 : CoefficientMerge.Poly := [(nat_lit 3821, Int.ofNat (nat_lit 60582834597600))]
theorem block019_data_flat093_step : block019_data_flat093 = (CoefficientMerge.scale (60582834597600 : Int) atom1425Coded) := by decide +kernel
theorem block019_data_flat093_original : block019_data_flat093 = (CoefficientMerge.scale (60582834597600 : Int) atom1425Coded) := by
  rw [block019_data_flat093_step]
def block019_data_flat094 : CoefficientMerge.Poly := [(nat_lit 3820, Int.ofNat (nat_lit 42738457266000)), (nat_lit 3821, Int.ofNat (nat_lit 60582834597600))]
theorem block019_data_flat094_step : block019_data_flat094 = (CoefficientMerge.fastMerge block019_data_flat092 block019_data_flat093) := by decide +kernel
theorem block019_data_flat094_original : block019_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (42738457266000 : Int) atom1424Coded) (CoefficientMerge.scale (60582834597600 : Int) atom1425Coded)) := by
  rw [block019_data_flat094_step, block019_data_flat092_original, block019_data_flat093_original]
def block019_data_flat095 : CoefficientMerge.Poly := [(nat_lit 3819, Int.ofNat (nat_lit 38809323630000)), (nat_lit 3820, Int.ofNat (nat_lit 42738457266000)), (nat_lit 3821, Int.ofNat (nat_lit 60582834597600))]
theorem block019_data_flat095_step : block019_data_flat095 = (CoefficientMerge.fastMerge block019_data_flat091 block019_data_flat094) := by decide +kernel
theorem block019_data_flat095_original : block019_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (38809323630000 : Int) atom1423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42738457266000 : Int) atom1424Coded) (CoefficientMerge.scale (60582834597600 : Int) atom1425Coded))) := by
  rw [block019_data_flat095_step, block019_data_flat091_original, block019_data_flat094_original]
def block019_data_flat096 : CoefficientMerge.Poly := [(nat_lit 3817, Int.ofNat (nat_lit 19329077214000)), (nat_lit 3818, Int.ofNat (nat_lit 34558073524800)), (nat_lit 3819, Int.ofNat (nat_lit 38809323630000)), (nat_lit 3820, Int.ofNat (nat_lit 42738457266000)), (nat_lit 3821, Int.ofNat (nat_lit 60582834597600))]
theorem block019_data_flat096_step : block019_data_flat096 = (CoefficientMerge.fastMerge block019_data_flat090 block019_data_flat095) := by decide +kernel
theorem block019_data_flat096_original : block019_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19329077214000 : Int) atom1421Coded) (CoefficientMerge.scale (34558073524800 : Int) atom1422Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38809323630000 : Int) atom1423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42738457266000 : Int) atom1424Coded) (CoefficientMerge.scale (60582834597600 : Int) atom1425Coded)))) := by
  rw [block019_data_flat096_step, block019_data_flat090_original, block019_data_flat095_original]
def block019_data_flat097 : CoefficientMerge.Poly := [(nat_lit 3799, Int.ofNat (nat_lit 37107275293200)), (nat_lit 3800, Int.ofNat (nat_lit 48530465474400)), (nat_lit 3814, Int.ofNat (nat_lit 8314429795200)), (nat_lit 3815, Int.ofNat (nat_lit 15912566956800)), (nat_lit 3816, Int.ofNat (nat_lit 19319098982400)), (nat_lit 3817, Int.ofNat (nat_lit 19329077214000)), (nat_lit 3818, Int.ofNat (nat_lit 34558073524800)), (nat_lit 3819, Int.ofNat (nat_lit 38809323630000)), (nat_lit 3820, Int.ofNat (nat_lit 42738457266000)), (nat_lit 3821, Int.ofNat (nat_lit 60582834597600))]
theorem block019_data_flat097_step : block019_data_flat097 = (CoefficientMerge.fastMerge block019_data_flat087 block019_data_flat096) := by decide +kernel
theorem block019_data_flat097_original : block019_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37107275293200 : Int) atom1416Coded) (CoefficientMerge.scale (48530465474400 : Int) atom1417Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8314429795200 : Int) atom1418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15912566956800 : Int) atom1419Coded) (CoefficientMerge.scale (19319098982400 : Int) atom1420Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19329077214000 : Int) atom1421Coded) (CoefficientMerge.scale (34558073524800 : Int) atom1422Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38809323630000 : Int) atom1423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42738457266000 : Int) atom1424Coded) (CoefficientMerge.scale (60582834597600 : Int) atom1425Coded))))) := by
  rw [block019_data_flat097_step, block019_data_flat087_original, block019_data_flat096_original]
def block019_data_flat098 : CoefficientMerge.Poly := [(nat_lit 3836, Int.ofNat (nat_lit 12733408598400))]
theorem block019_data_flat098_step : block019_data_flat098 = (CoefficientMerge.scale (12733408598400 : Int) atom1426Coded) := by decide +kernel
theorem block019_data_flat098_original : block019_data_flat098 = (CoefficientMerge.scale (12733408598400 : Int) atom1426Coded) := by
  rw [block019_data_flat098_step]
def block019_data_flat099 : CoefficientMerge.Poly := [(nat_lit 3837, Int.ofNat (nat_lit 24425203723200))]
theorem block019_data_flat099_step : block019_data_flat099 = (CoefficientMerge.scale (24425203723200 : Int) atom1427Coded) := by decide +kernel
theorem block019_data_flat099_original : block019_data_flat099 = (CoefficientMerge.scale (24425203723200 : Int) atom1427Coded) := by
  rw [block019_data_flat099_step]
def block019_data_flat100 : CoefficientMerge.Poly := [(nat_lit 3836, Int.ofNat (nat_lit 12733408598400)), (nat_lit 3837, Int.ofNat (nat_lit 24425203723200))]
theorem block019_data_flat100_step : block019_data_flat100 = (CoefficientMerge.fastMerge block019_data_flat098 block019_data_flat099) := by decide +kernel
theorem block019_data_flat100_original : block019_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12733408598400 : Int) atom1426Coded) (CoefficientMerge.scale (24425203723200 : Int) atom1427Coded)) := by
  rw [block019_data_flat100_step, block019_data_flat098_original, block019_data_flat099_original]
def block019_data_flat101 : CoefficientMerge.Poly := [(nat_lit 3838, Int.ofNat (nat_lit 24919452658800))]
theorem block019_data_flat101_step : block019_data_flat101 = (CoefficientMerge.scale (24919452658800 : Int) atom1428Coded) := by decide +kernel
theorem block019_data_flat101_original : block019_data_flat101 = (CoefficientMerge.scale (24919452658800 : Int) atom1428Coded) := by
  rw [block019_data_flat101_step]
def block019_data_flat102 : CoefficientMerge.Poly := [(nat_lit 3839, Int.ofNat (nat_lit 46215639489600))]
theorem block019_data_flat102_step : block019_data_flat102 = (CoefficientMerge.scale (46215639489600 : Int) atom1429Coded) := by decide +kernel
theorem block019_data_flat102_original : block019_data_flat102 = (CoefficientMerge.scale (46215639489600 : Int) atom1429Coded) := by
  rw [block019_data_flat102_step]
def block019_data_flat103 : CoefficientMerge.Poly := [(nat_lit 3840, Int.ofNat (nat_lit 52704268570800))]
theorem block019_data_flat103_step : block019_data_flat103 = (CoefficientMerge.scale (52704268570800 : Int) atom1430Coded) := by decide +kernel
theorem block019_data_flat103_original : block019_data_flat103 = (CoefficientMerge.scale (52704268570800 : Int) atom1430Coded) := by
  rw [block019_data_flat103_step]
def block019_data_flat104 : CoefficientMerge.Poly := [(nat_lit 3839, Int.ofNat (nat_lit 46215639489600)), (nat_lit 3840, Int.ofNat (nat_lit 52704268570800))]
theorem block019_data_flat104_step : block019_data_flat104 = (CoefficientMerge.fastMerge block019_data_flat102 block019_data_flat103) := by decide +kernel
theorem block019_data_flat104_original : block019_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46215639489600 : Int) atom1429Coded) (CoefficientMerge.scale (52704268570800 : Int) atom1430Coded)) := by
  rw [block019_data_flat104_step, block019_data_flat102_original, block019_data_flat103_original]
def block019_data_flat105 : CoefficientMerge.Poly := [(nat_lit 3838, Int.ofNat (nat_lit 24919452658800)), (nat_lit 3839, Int.ofNat (nat_lit 46215639489600)), (nat_lit 3840, Int.ofNat (nat_lit 52704268570800))]
theorem block019_data_flat105_step : block019_data_flat105 = (CoefficientMerge.fastMerge block019_data_flat101 block019_data_flat104) := by decide +kernel
theorem block019_data_flat105_original : block019_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24919452658800 : Int) atom1428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46215639489600 : Int) atom1429Coded) (CoefficientMerge.scale (52704268570800 : Int) atom1430Coded))) := by
  rw [block019_data_flat105_step, block019_data_flat101_original, block019_data_flat104_original]
def block019_data_flat106 : CoefficientMerge.Poly := [(nat_lit 3836, Int.ofNat (nat_lit 12733408598400)), (nat_lit 3837, Int.ofNat (nat_lit 24425203723200)), (nat_lit 3838, Int.ofNat (nat_lit 24919452658800)), (nat_lit 3839, Int.ofNat (nat_lit 46215639489600)), (nat_lit 3840, Int.ofNat (nat_lit 52704268570800))]
theorem block019_data_flat106_step : block019_data_flat106 = (CoefficientMerge.fastMerge block019_data_flat100 block019_data_flat105) := by decide +kernel
theorem block019_data_flat106_original : block019_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12733408598400 : Int) atom1426Coded) (CoefficientMerge.scale (24425203723200 : Int) atom1427Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24919452658800 : Int) atom1428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46215639489600 : Int) atom1429Coded) (CoefficientMerge.scale (52704268570800 : Int) atom1430Coded)))) := by
  rw [block019_data_flat106_step, block019_data_flat100_original, block019_data_flat105_original]
def block019_data_flat107 : CoefficientMerge.Poly := [(nat_lit 3841, Int.ofNat (nat_lit 52820365827600))]
theorem block019_data_flat107_step : block019_data_flat107 = (CoefficientMerge.scale (52820365827600 : Int) atom1431Coded) := by decide +kernel
theorem block019_data_flat107_original : block019_data_flat107 = (CoefficientMerge.scale (52820365827600 : Int) atom1431Coded) := by
  rw [block019_data_flat107_step]
def block019_data_flat108 : CoefficientMerge.Poly := [(nat_lit 3842, Int.ofNat (nat_lit 77218206357600))]
theorem block019_data_flat108_step : block019_data_flat108 = (CoefficientMerge.scale (77218206357600 : Int) atom1432Coded) := by decide +kernel
theorem block019_data_flat108_original : block019_data_flat108 = (CoefficientMerge.scale (77218206357600 : Int) atom1432Coded) := by
  rw [block019_data_flat108_step]
def block019_data_flat109 : CoefficientMerge.Poly := [(nat_lit 3841, Int.ofNat (nat_lit 52820365827600)), (nat_lit 3842, Int.ofNat (nat_lit 77218206357600))]
theorem block019_data_flat109_step : block019_data_flat109 = (CoefficientMerge.fastMerge block019_data_flat107 block019_data_flat108) := by decide +kernel
theorem block019_data_flat109_original : block019_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (52820365827600 : Int) atom1431Coded) (CoefficientMerge.scale (77218206357600 : Int) atom1432Coded)) := by
  rw [block019_data_flat109_step, block019_data_flat107_original, block019_data_flat108_original]
def block019_data_flat110 : CoefficientMerge.Poly := [(nat_lit 3858, Int.ofNat (nat_lit 19383530342400))]
theorem block019_data_flat110_step : block019_data_flat110 = (CoefficientMerge.scale (19383530342400 : Int) atom1433Coded) := by decide +kernel
theorem block019_data_flat110_original : block019_data_flat110 = (CoefficientMerge.scale (19383530342400 : Int) atom1433Coded) := by
  rw [block019_data_flat110_step]
def block019_data_flat111 : CoefficientMerge.Poly := [(nat_lit 3859, Int.ofNat (nat_lit 39580818694200))]
theorem block019_data_flat111_step : block019_data_flat111 = (CoefficientMerge.scale (39580818694200 : Int) atom1434Coded) := by decide +kernel
theorem block019_data_flat111_original : block019_data_flat111 = (CoefficientMerge.scale (39580818694200 : Int) atom1434Coded) := by
  rw [block019_data_flat111_step]
def block019_data_flat112 : CoefficientMerge.Poly := [(nat_lit 3860, Int.ofNat (nat_lit 66724705152000))]
theorem block019_data_flat112_step : block019_data_flat112 = (CoefficientMerge.scale (66724705152000 : Int) atom1435Coded) := by decide +kernel
theorem block019_data_flat112_original : block019_data_flat112 = (CoefficientMerge.scale (66724705152000 : Int) atom1435Coded) := by
  rw [block019_data_flat112_step]
def block019_data_flat113 : CoefficientMerge.Poly := [(nat_lit 3859, Int.ofNat (nat_lit 39580818694200)), (nat_lit 3860, Int.ofNat (nat_lit 66724705152000))]
theorem block019_data_flat113_step : block019_data_flat113 = (CoefficientMerge.fastMerge block019_data_flat111 block019_data_flat112) := by decide +kernel
theorem block019_data_flat113_original : block019_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (39580818694200 : Int) atom1434Coded) (CoefficientMerge.scale (66724705152000 : Int) atom1435Coded)) := by
  rw [block019_data_flat113_step, block019_data_flat111_original, block019_data_flat112_original]
def block019_data_flat114 : CoefficientMerge.Poly := [(nat_lit 3858, Int.ofNat (nat_lit 19383530342400)), (nat_lit 3859, Int.ofNat (nat_lit 39580818694200)), (nat_lit 3860, Int.ofNat (nat_lit 66724705152000))]
theorem block019_data_flat114_step : block019_data_flat114 = (CoefficientMerge.fastMerge block019_data_flat110 block019_data_flat113) := by decide +kernel
theorem block019_data_flat114_original : block019_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19383530342400 : Int) atom1433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39580818694200 : Int) atom1434Coded) (CoefficientMerge.scale (66724705152000 : Int) atom1435Coded))) := by
  rw [block019_data_flat114_step, block019_data_flat110_original, block019_data_flat113_original]
def block019_data_flat115 : CoefficientMerge.Poly := [(nat_lit 3841, Int.ofNat (nat_lit 52820365827600)), (nat_lit 3842, Int.ofNat (nat_lit 77218206357600)), (nat_lit 3858, Int.ofNat (nat_lit 19383530342400)), (nat_lit 3859, Int.ofNat (nat_lit 39580818694200)), (nat_lit 3860, Int.ofNat (nat_lit 66724705152000))]
theorem block019_data_flat115_step : block019_data_flat115 = (CoefficientMerge.fastMerge block019_data_flat109 block019_data_flat114) := by decide +kernel
theorem block019_data_flat115_original : block019_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52820365827600 : Int) atom1431Coded) (CoefficientMerge.scale (77218206357600 : Int) atom1432Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19383530342400 : Int) atom1433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39580818694200 : Int) atom1434Coded) (CoefficientMerge.scale (66724705152000 : Int) atom1435Coded)))) := by
  rw [block019_data_flat115_step, block019_data_flat109_original, block019_data_flat114_original]
def block019_data_flat116 : CoefficientMerge.Poly := [(nat_lit 3836, Int.ofNat (nat_lit 12733408598400)), (nat_lit 3837, Int.ofNat (nat_lit 24425203723200)), (nat_lit 3838, Int.ofNat (nat_lit 24919452658800)), (nat_lit 3839, Int.ofNat (nat_lit 46215639489600)), (nat_lit 3840, Int.ofNat (nat_lit 52704268570800)), (nat_lit 3841, Int.ofNat (nat_lit 52820365827600)), (nat_lit 3842, Int.ofNat (nat_lit 77218206357600)), (nat_lit 3858, Int.ofNat (nat_lit 19383530342400)), (nat_lit 3859, Int.ofNat (nat_lit 39580818694200)), (nat_lit 3860, Int.ofNat (nat_lit 66724705152000))]
theorem block019_data_flat116_step : block019_data_flat116 = (CoefficientMerge.fastMerge block019_data_flat106 block019_data_flat115) := by decide +kernel
theorem block019_data_flat116_original : block019_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12733408598400 : Int) atom1426Coded) (CoefficientMerge.scale (24425203723200 : Int) atom1427Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24919452658800 : Int) atom1428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46215639489600 : Int) atom1429Coded) (CoefficientMerge.scale (52704268570800 : Int) atom1430Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52820365827600 : Int) atom1431Coded) (CoefficientMerge.scale (77218206357600 : Int) atom1432Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19383530342400 : Int) atom1433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39580818694200 : Int) atom1434Coded) (CoefficientMerge.scale (66724705152000 : Int) atom1435Coded))))) := by
  rw [block019_data_flat116_step, block019_data_flat106_original, block019_data_flat115_original]
def block019_data_flat117 : CoefficientMerge.Poly := [(nat_lit 3799, Int.ofNat (nat_lit 37107275293200)), (nat_lit 3800, Int.ofNat (nat_lit 48530465474400)), (nat_lit 3814, Int.ofNat (nat_lit 8314429795200)), (nat_lit 3815, Int.ofNat (nat_lit 15912566956800)), (nat_lit 3816, Int.ofNat (nat_lit 19319098982400)), (nat_lit 3817, Int.ofNat (nat_lit 19329077214000)), (nat_lit 3818, Int.ofNat (nat_lit 34558073524800)), (nat_lit 3819, Int.ofNat (nat_lit 38809323630000)), (nat_lit 3820, Int.ofNat (nat_lit 42738457266000)), (nat_lit 3821, Int.ofNat (nat_lit 60582834597600)), (nat_lit 3836, Int.ofNat (nat_lit 12733408598400)), (nat_lit 3837, Int.ofNat (nat_lit 24425203723200)), (nat_lit 3838, Int.ofNat (nat_lit 24919452658800)), (nat_lit 3839, Int.ofNat (nat_lit 46215639489600)), (nat_lit 3840, Int.ofNat (nat_lit 52704268570800)), (nat_lit 3841, Int.ofNat (nat_lit 52820365827600)), (nat_lit 3842, Int.ofNat (nat_lit 77218206357600)), (nat_lit 3858, Int.ofNat (nat_lit 19383530342400)), (nat_lit 3859, Int.ofNat (nat_lit 39580818694200)), (nat_lit 3860, Int.ofNat (nat_lit 66724705152000))]
theorem block019_data_flat117_step : block019_data_flat117 = (CoefficientMerge.fastMerge block019_data_flat097 block019_data_flat116) := by decide +kernel
theorem block019_data_flat117_original : block019_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37107275293200 : Int) atom1416Coded) (CoefficientMerge.scale (48530465474400 : Int) atom1417Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8314429795200 : Int) atom1418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15912566956800 : Int) atom1419Coded) (CoefficientMerge.scale (19319098982400 : Int) atom1420Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19329077214000 : Int) atom1421Coded) (CoefficientMerge.scale (34558073524800 : Int) atom1422Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38809323630000 : Int) atom1423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42738457266000 : Int) atom1424Coded) (CoefficientMerge.scale (60582834597600 : Int) atom1425Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12733408598400 : Int) atom1426Coded) (CoefficientMerge.scale (24425203723200 : Int) atom1427Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24919452658800 : Int) atom1428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46215639489600 : Int) atom1429Coded) (CoefficientMerge.scale (52704268570800 : Int) atom1430Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52820365827600 : Int) atom1431Coded) (CoefficientMerge.scale (77218206357600 : Int) atom1432Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19383530342400 : Int) atom1433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39580818694200 : Int) atom1434Coded) (CoefficientMerge.scale (66724705152000 : Int) atom1435Coded)))))) := by
  rw [block019_data_flat117_step, block019_data_flat097_original, block019_data_flat116_original]
def block019_data_flat118 : CoefficientMerge.Poly := [(nat_lit 3861, Int.ofNat (nat_lit 71113667221800))]
theorem block019_data_flat118_step : block019_data_flat118 = (CoefficientMerge.scale (71113667221800 : Int) atom1436Coded) := by decide +kernel
theorem block019_data_flat118_original : block019_data_flat118 = (CoefficientMerge.scale (71113667221800 : Int) atom1436Coded) := by
  rw [block019_data_flat118_step]
def block019_data_flat119 : CoefficientMerge.Poly := [(nat_lit 3862, Int.ofNat (nat_lit 53763791949000))]
theorem block019_data_flat119_step : block019_data_flat119 = (CoefficientMerge.scale (53763791949000 : Int) atom1437Coded) := by decide +kernel
theorem block019_data_flat119_original : block019_data_flat119 = (CoefficientMerge.scale (53763791949000 : Int) atom1437Coded) := by
  rw [block019_data_flat119_step]
def block019_data_flat120 : CoefficientMerge.Poly := [(nat_lit 3861, Int.ofNat (nat_lit 71113667221800)), (nat_lit 3862, Int.ofNat (nat_lit 53763791949000))]
theorem block019_data_flat120_step : block019_data_flat120 = (CoefficientMerge.fastMerge block019_data_flat118 block019_data_flat119) := by decide +kernel
theorem block019_data_flat120_original : block019_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (71113667221800 : Int) atom1436Coded) (CoefficientMerge.scale (53763791949000 : Int) atom1437Coded)) := by
  rw [block019_data_flat120_step, block019_data_flat118_original, block019_data_flat119_original]
def block019_data_flat121 : CoefficientMerge.Poly := [(nat_lit 3863, Int.ofNat (nat_lit 82935935850600))]
theorem block019_data_flat121_step : block019_data_flat121 = (CoefficientMerge.scale (82935935850600 : Int) atom1438Coded) := by decide +kernel
theorem block019_data_flat121_original : block019_data_flat121 = (CoefficientMerge.scale (82935935850600 : Int) atom1438Coded) := by
  rw [block019_data_flat121_step]
def block019_data_flat122 : CoefficientMerge.Poly := [(nat_lit 3880, Int.ofNat (nat_lit 15952947010560))]
theorem block019_data_flat122_step : block019_data_flat122 = (CoefficientMerge.scale (15952947010560 : Int) atom1439Coded) := by decide +kernel
theorem block019_data_flat122_original : block019_data_flat122 = (CoefficientMerge.scale (15952947010560 : Int) atom1439Coded) := by
  rw [block019_data_flat122_step]
def block019_data_flat123 : CoefficientMerge.Poly := [(nat_lit 3881, Int.ofNat (nat_lit 56181592441800))]
theorem block019_data_flat123_step : block019_data_flat123 = (CoefficientMerge.scale (56181592441800 : Int) atom1440Coded) := by decide +kernel
theorem block019_data_flat123_original : block019_data_flat123 = (CoefficientMerge.scale (56181592441800 : Int) atom1440Coded) := by
  rw [block019_data_flat123_step]
def block019_data_flat124 : CoefficientMerge.Poly := [(nat_lit 3880, Int.ofNat (nat_lit 15952947010560)), (nat_lit 3881, Int.ofNat (nat_lit 56181592441800))]
theorem block019_data_flat124_step : block019_data_flat124 = (CoefficientMerge.fastMerge block019_data_flat122 block019_data_flat123) := by decide +kernel
theorem block019_data_flat124_original : block019_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15952947010560 : Int) atom1439Coded) (CoefficientMerge.scale (56181592441800 : Int) atom1440Coded)) := by
  rw [block019_data_flat124_step, block019_data_flat122_original, block019_data_flat123_original]
def block019_data_flat125 : CoefficientMerge.Poly := [(nat_lit 3863, Int.ofNat (nat_lit 82935935850600)), (nat_lit 3880, Int.ofNat (nat_lit 15952947010560)), (nat_lit 3881, Int.ofNat (nat_lit 56181592441800))]
theorem block019_data_flat125_step : block019_data_flat125 = (CoefficientMerge.fastMerge block019_data_flat121 block019_data_flat124) := by decide +kernel
theorem block019_data_flat125_original : block019_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (82935935850600 : Int) atom1438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15952947010560 : Int) atom1439Coded) (CoefficientMerge.scale (56181592441800 : Int) atom1440Coded))) := by
  rw [block019_data_flat125_step, block019_data_flat121_original, block019_data_flat124_original]
def block019_data_flat126 : CoefficientMerge.Poly := [(nat_lit 3861, Int.ofNat (nat_lit 71113667221800)), (nat_lit 3862, Int.ofNat (nat_lit 53763791949000)), (nat_lit 3863, Int.ofNat (nat_lit 82935935850600)), (nat_lit 3880, Int.ofNat (nat_lit 15952947010560)), (nat_lit 3881, Int.ofNat (nat_lit 56181592441800))]
theorem block019_data_flat126_step : block019_data_flat126 = (CoefficientMerge.fastMerge block019_data_flat120 block019_data_flat125) := by decide +kernel
theorem block019_data_flat126_original : block019_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (71113667221800 : Int) atom1436Coded) (CoefficientMerge.scale (53763791949000 : Int) atom1437Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82935935850600 : Int) atom1438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15952947010560 : Int) atom1439Coded) (CoefficientMerge.scale (56181592441800 : Int) atom1440Coded)))) := by
  rw [block019_data_flat126_step, block019_data_flat120_original, block019_data_flat125_original]
def block019_data_flat127 : CoefficientMerge.Poly := [(nat_lit 3882, Int.ofNat (nat_lit 64310888457900))]
theorem block019_data_flat127_step : block019_data_flat127 = (CoefficientMerge.scale (64310888457900 : Int) atom1441Coded) := by decide +kernel
theorem block019_data_flat127_original : block019_data_flat127 = (CoefficientMerge.scale (64310888457900 : Int) atom1441Coded) := by
  rw [block019_data_flat127_step]
def block019_data_flat128 : CoefficientMerge.Poly := [(nat_lit 3883, Int.ofNat (nat_lit 46815859734000))]
theorem block019_data_flat128_step : block019_data_flat128 = (CoefficientMerge.scale (46815859734000 : Int) atom1442Coded) := by decide +kernel
theorem block019_data_flat128_original : block019_data_flat128 = (CoefficientMerge.scale (46815859734000 : Int) atom1442Coded) := by
  rw [block019_data_flat128_step]
def block019_data_flat129 : CoefficientMerge.Poly := [(nat_lit 3882, Int.ofNat (nat_lit 64310888457900)), (nat_lit 3883, Int.ofNat (nat_lit 46815859734000))]
theorem block019_data_flat129_step : block019_data_flat129 = (CoefficientMerge.fastMerge block019_data_flat127 block019_data_flat128) := by decide +kernel
theorem block019_data_flat129_original : block019_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (64310888457900 : Int) atom1441Coded) (CoefficientMerge.scale (46815859734000 : Int) atom1442Coded)) := by
  rw [block019_data_flat129_step, block019_data_flat127_original, block019_data_flat128_original]
def block019_data_flat130 : CoefficientMerge.Poly := [(nat_lit 3884, Int.ofNat (nat_lit 61853161781250))]
theorem block019_data_flat130_step : block019_data_flat130 = (CoefficientMerge.scale (61853161781250 : Int) atom1443Coded) := by decide +kernel
theorem block019_data_flat130_original : block019_data_flat130 = (CoefficientMerge.scale (61853161781250 : Int) atom1443Coded) := by
  rw [block019_data_flat130_step]
def block019_data_flat131 : CoefficientMerge.Poly := [(nat_lit 3902, Int.ofNat (nat_lit 41682593433600))]
theorem block019_data_flat131_step : block019_data_flat131 = (CoefficientMerge.scale (41682593433600 : Int) atom1444Coded) := by decide +kernel
theorem block019_data_flat131_original : block019_data_flat131 = (CoefficientMerge.scale (41682593433600 : Int) atom1444Coded) := by
  rw [block019_data_flat131_step]
def block019_data_flat132 : CoefficientMerge.Poly := [(nat_lit 3903, Int.ofNat (nat_lit 73028319197400))]
theorem block019_data_flat132_step : block019_data_flat132 = (CoefficientMerge.scale (73028319197400 : Int) atom1445Coded) := by decide +kernel
theorem block019_data_flat132_original : block019_data_flat132 = (CoefficientMerge.scale (73028319197400 : Int) atom1445Coded) := by
  rw [block019_data_flat132_step]
def block019_data_flat133 : CoefficientMerge.Poly := [(nat_lit 3902, Int.ofNat (nat_lit 41682593433600)), (nat_lit 3903, Int.ofNat (nat_lit 73028319197400))]
theorem block019_data_flat133_step : block019_data_flat133 = (CoefficientMerge.fastMerge block019_data_flat131 block019_data_flat132) := by decide +kernel
theorem block019_data_flat133_original : block019_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (41682593433600 : Int) atom1444Coded) (CoefficientMerge.scale (73028319197400 : Int) atom1445Coded)) := by
  rw [block019_data_flat133_step, block019_data_flat131_original, block019_data_flat132_original]
def block019_data_flat134 : CoefficientMerge.Poly := [(nat_lit 3884, Int.ofNat (nat_lit 61853161781250)), (nat_lit 3902, Int.ofNat (nat_lit 41682593433600)), (nat_lit 3903, Int.ofNat (nat_lit 73028319197400))]
theorem block019_data_flat134_step : block019_data_flat134 = (CoefficientMerge.fastMerge block019_data_flat130 block019_data_flat133) := by decide +kernel
theorem block019_data_flat134_original : block019_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (61853161781250 : Int) atom1443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41682593433600 : Int) atom1444Coded) (CoefficientMerge.scale (73028319197400 : Int) atom1445Coded))) := by
  rw [block019_data_flat134_step, block019_data_flat130_original, block019_data_flat133_original]
def block019_data_flat135 : CoefficientMerge.Poly := [(nat_lit 3882, Int.ofNat (nat_lit 64310888457900)), (nat_lit 3883, Int.ofNat (nat_lit 46815859734000)), (nat_lit 3884, Int.ofNat (nat_lit 61853161781250)), (nat_lit 3902, Int.ofNat (nat_lit 41682593433600)), (nat_lit 3903, Int.ofNat (nat_lit 73028319197400))]
theorem block019_data_flat135_step : block019_data_flat135 = (CoefficientMerge.fastMerge block019_data_flat129 block019_data_flat134) := by decide +kernel
theorem block019_data_flat135_original : block019_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64310888457900 : Int) atom1441Coded) (CoefficientMerge.scale (46815859734000 : Int) atom1442Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61853161781250 : Int) atom1443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41682593433600 : Int) atom1444Coded) (CoefficientMerge.scale (73028319197400 : Int) atom1445Coded)))) := by
  rw [block019_data_flat135_step, block019_data_flat129_original, block019_data_flat134_original]
def block019_data_flat136 : CoefficientMerge.Poly := [(nat_lit 3861, Int.ofNat (nat_lit 71113667221800)), (nat_lit 3862, Int.ofNat (nat_lit 53763791949000)), (nat_lit 3863, Int.ofNat (nat_lit 82935935850600)), (nat_lit 3880, Int.ofNat (nat_lit 15952947010560)), (nat_lit 3881, Int.ofNat (nat_lit 56181592441800)), (nat_lit 3882, Int.ofNat (nat_lit 64310888457900)), (nat_lit 3883, Int.ofNat (nat_lit 46815859734000)), (nat_lit 3884, Int.ofNat (nat_lit 61853161781250)), (nat_lit 3902, Int.ofNat (nat_lit 41682593433600)), (nat_lit 3903, Int.ofNat (nat_lit 73028319197400))]
theorem block019_data_flat136_step : block019_data_flat136 = (CoefficientMerge.fastMerge block019_data_flat126 block019_data_flat135) := by decide +kernel
theorem block019_data_flat136_original : block019_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (71113667221800 : Int) atom1436Coded) (CoefficientMerge.scale (53763791949000 : Int) atom1437Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82935935850600 : Int) atom1438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15952947010560 : Int) atom1439Coded) (CoefficientMerge.scale (56181592441800 : Int) atom1440Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64310888457900 : Int) atom1441Coded) (CoefficientMerge.scale (46815859734000 : Int) atom1442Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61853161781250 : Int) atom1443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41682593433600 : Int) atom1444Coded) (CoefficientMerge.scale (73028319197400 : Int) atom1445Coded))))) := by
  rw [block019_data_flat136_step, block019_data_flat126_original, block019_data_flat135_original]
def block019_data_flat137 : CoefficientMerge.Poly := [(nat_lit 3904, Int.ofNat (nat_lit 49453121621400))]
theorem block019_data_flat137_step : block019_data_flat137 = (CoefficientMerge.scale (49453121621400 : Int) atom1446Coded) := by decide +kernel
theorem block019_data_flat137_original : block019_data_flat137 = (CoefficientMerge.scale (49453121621400 : Int) atom1446Coded) := by
  rw [block019_data_flat137_step]
def block019_data_flat138 : CoefficientMerge.Poly := [(nat_lit 3905, Int.ofNat (nat_lit 54003049493400))]
theorem block019_data_flat138_step : block019_data_flat138 = (CoefficientMerge.scale (54003049493400 : Int) atom1447Coded) := by decide +kernel
theorem block019_data_flat138_original : block019_data_flat138 = (CoefficientMerge.scale (54003049493400 : Int) atom1447Coded) := by
  rw [block019_data_flat138_step]
def block019_data_flat139 : CoefficientMerge.Poly := [(nat_lit 3904, Int.ofNat (nat_lit 49453121621400)), (nat_lit 3905, Int.ofNat (nat_lit 54003049493400))]
theorem block019_data_flat139_step : block019_data_flat139 = (CoefficientMerge.fastMerge block019_data_flat137 block019_data_flat138) := by decide +kernel
theorem block019_data_flat139_original : block019_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (49453121621400 : Int) atom1446Coded) (CoefficientMerge.scale (54003049493400 : Int) atom1447Coded)) := by
  rw [block019_data_flat139_step, block019_data_flat137_original, block019_data_flat138_original]
def block019_data_flat140 : CoefficientMerge.Poly := [(nat_lit 3924, Int.ofNat (nat_lit 25323261106500))]
theorem block019_data_flat140_step : block019_data_flat140 = (CoefficientMerge.scale (25323261106500 : Int) atom1448Coded) := by decide +kernel
theorem block019_data_flat140_original : block019_data_flat140 = (CoefficientMerge.scale (25323261106500 : Int) atom1448Coded) := by
  rw [block019_data_flat140_step]
def block019_data_flat141 : CoefficientMerge.Poly := [(nat_lit 3925, Int.ofNat (nat_lit 30034904980500))]
theorem block019_data_flat141_step : block019_data_flat141 = (CoefficientMerge.scale (30034904980500 : Int) atom1449Coded) := by decide +kernel
theorem block019_data_flat141_original : block019_data_flat141 = (CoefficientMerge.scale (30034904980500 : Int) atom1449Coded) := by
  rw [block019_data_flat141_step]
def block019_data_flat142 : CoefficientMerge.Poly := [(nat_lit 3926, Int.ofNat (nat_lit 36065647557450))]
theorem block019_data_flat142_step : block019_data_flat142 = (CoefficientMerge.scale (36065647557450 : Int) atom1450Coded) := by decide +kernel
theorem block019_data_flat142_original : block019_data_flat142 = (CoefficientMerge.scale (36065647557450 : Int) atom1450Coded) := by
  rw [block019_data_flat142_step]
def block019_data_flat143 : CoefficientMerge.Poly := [(nat_lit 3925, Int.ofNat (nat_lit 30034904980500)), (nat_lit 3926, Int.ofNat (nat_lit 36065647557450))]
theorem block019_data_flat143_step : block019_data_flat143 = (CoefficientMerge.fastMerge block019_data_flat141 block019_data_flat142) := by decide +kernel
theorem block019_data_flat143_original : block019_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034904980500 : Int) atom1449Coded) (CoefficientMerge.scale (36065647557450 : Int) atom1450Coded)) := by
  rw [block019_data_flat143_step, block019_data_flat141_original, block019_data_flat142_original]
def block019_data_flat144 : CoefficientMerge.Poly := [(nat_lit 3924, Int.ofNat (nat_lit 25323261106500)), (nat_lit 3925, Int.ofNat (nat_lit 30034904980500)), (nat_lit 3926, Int.ofNat (nat_lit 36065647557450))]
theorem block019_data_flat144_step : block019_data_flat144 = (CoefficientMerge.fastMerge block019_data_flat140 block019_data_flat143) := by decide +kernel
theorem block019_data_flat144_original : block019_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25323261106500 : Int) atom1448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034904980500 : Int) atom1449Coded) (CoefficientMerge.scale (36065647557450 : Int) atom1450Coded))) := by
  rw [block019_data_flat144_step, block019_data_flat140_original, block019_data_flat143_original]
def block019_data_flat145 : CoefficientMerge.Poly := [(nat_lit 3904, Int.ofNat (nat_lit 49453121621400)), (nat_lit 3905, Int.ofNat (nat_lit 54003049493400)), (nat_lit 3924, Int.ofNat (nat_lit 25323261106500)), (nat_lit 3925, Int.ofNat (nat_lit 30034904980500)), (nat_lit 3926, Int.ofNat (nat_lit 36065647557450))]
theorem block019_data_flat145_step : block019_data_flat145 = (CoefficientMerge.fastMerge block019_data_flat139 block019_data_flat144) := by decide +kernel
theorem block019_data_flat145_original : block019_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49453121621400 : Int) atom1446Coded) (CoefficientMerge.scale (54003049493400 : Int) atom1447Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25323261106500 : Int) atom1448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034904980500 : Int) atom1449Coded) (CoefficientMerge.scale (36065647557450 : Int) atom1450Coded)))) := by
  rw [block019_data_flat145_step, block019_data_flat139_original, block019_data_flat144_original]
def block019_data_flat146 : CoefficientMerge.Poly := [(nat_lit 3947, Int.ofNat (nat_lit 5439574781550))]
theorem block019_data_flat146_step : block019_data_flat146 = (CoefficientMerge.scale (5439574781550 : Int) atom1451Coded) := by decide +kernel
theorem block019_data_flat146_original : block019_data_flat146 = (CoefficientMerge.scale (5439574781550 : Int) atom1451Coded) := by
  rw [block019_data_flat146_step]
def block019_data_flat147 : CoefficientMerge.Poly := [(nat_lit 3968, Int.ofNat (nat_lit 3482925254550))]
theorem block019_data_flat147_step : block019_data_flat147 = (CoefficientMerge.scale (3482925254550 : Int) atom1452Coded) := by decide +kernel
theorem block019_data_flat147_original : block019_data_flat147 = (CoefficientMerge.scale (3482925254550 : Int) atom1452Coded) := by
  rw [block019_data_flat147_step]
def block019_data_flat148 : CoefficientMerge.Poly := [(nat_lit 3947, Int.ofNat (nat_lit 5439574781550)), (nat_lit 3968, Int.ofNat (nat_lit 3482925254550))]
theorem block019_data_flat148_step : block019_data_flat148 = (CoefficientMerge.fastMerge block019_data_flat146 block019_data_flat147) := by decide +kernel
theorem block019_data_flat148_original : block019_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5439574781550 : Int) atom1451Coded) (CoefficientMerge.scale (3482925254550 : Int) atom1452Coded)) := by
  rw [block019_data_flat148_step, block019_data_flat146_original, block019_data_flat147_original]
def block019_data_flat149 : CoefficientMerge.Poly := [(nat_lit 4167, Int.ofNat (nat_lit 912670214400))]
theorem block019_data_flat149_step : block019_data_flat149 = (CoefficientMerge.scale (912670214400 : Int) atom1453Coded) := by decide +kernel
theorem block019_data_flat149_original : block019_data_flat149 = (CoefficientMerge.scale (912670214400 : Int) atom1453Coded) := by
  rw [block019_data_flat149_step]
def block019_data_flat150 : CoefficientMerge.Poly := [(nat_lit 4168, Int.ofNat (nat_lit 602111059200))]
theorem block019_data_flat150_step : block019_data_flat150 = (CoefficientMerge.scale (602111059200 : Int) atom1454Coded) := by decide +kernel
theorem block019_data_flat150_original : block019_data_flat150 = (CoefficientMerge.scale (602111059200 : Int) atom1454Coded) := by
  rw [block019_data_flat150_step]
def block019_data_flat151 : CoefficientMerge.Poly := [(nat_lit 4173, Int.ofNat (nat_lit 2995132039200))]
theorem block019_data_flat151_step : block019_data_flat151 = (CoefficientMerge.scale (2995132039200 : Int) atom1455Coded) := by decide +kernel
theorem block019_data_flat151_original : block019_data_flat151 = (CoefficientMerge.scale (2995132039200 : Int) atom1455Coded) := by
  rw [block019_data_flat151_step]
def block019_data_flat152 : CoefficientMerge.Poly := [(nat_lit 4168, Int.ofNat (nat_lit 602111059200)), (nat_lit 4173, Int.ofNat (nat_lit 2995132039200))]
theorem block019_data_flat152_step : block019_data_flat152 = (CoefficientMerge.fastMerge block019_data_flat150 block019_data_flat151) := by decide +kernel
theorem block019_data_flat152_original : block019_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (602111059200 : Int) atom1454Coded) (CoefficientMerge.scale (2995132039200 : Int) atom1455Coded)) := by
  rw [block019_data_flat152_step, block019_data_flat150_original, block019_data_flat151_original]
def block019_data_flat153 : CoefficientMerge.Poly := [(nat_lit 4167, Int.ofNat (nat_lit 912670214400)), (nat_lit 4168, Int.ofNat (nat_lit 602111059200)), (nat_lit 4173, Int.ofNat (nat_lit 2995132039200))]
theorem block019_data_flat153_step : block019_data_flat153 = (CoefficientMerge.fastMerge block019_data_flat149 block019_data_flat152) := by decide +kernel
theorem block019_data_flat153_original : block019_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (912670214400 : Int) atom1453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (602111059200 : Int) atom1454Coded) (CoefficientMerge.scale (2995132039200 : Int) atom1455Coded))) := by
  rw [block019_data_flat153_step, block019_data_flat149_original, block019_data_flat152_original]
def block019_data_flat154 : CoefficientMerge.Poly := [(nat_lit 3947, Int.ofNat (nat_lit 5439574781550)), (nat_lit 3968, Int.ofNat (nat_lit 3482925254550)), (nat_lit 4167, Int.ofNat (nat_lit 912670214400)), (nat_lit 4168, Int.ofNat (nat_lit 602111059200)), (nat_lit 4173, Int.ofNat (nat_lit 2995132039200))]
theorem block019_data_flat154_step : block019_data_flat154 = (CoefficientMerge.fastMerge block019_data_flat148 block019_data_flat153) := by decide +kernel
theorem block019_data_flat154_original : block019_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5439574781550 : Int) atom1451Coded) (CoefficientMerge.scale (3482925254550 : Int) atom1452Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (912670214400 : Int) atom1453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (602111059200 : Int) atom1454Coded) (CoefficientMerge.scale (2995132039200 : Int) atom1455Coded)))) := by
  rw [block019_data_flat154_step, block019_data_flat148_original, block019_data_flat153_original]
def block019_data_flat155 : CoefficientMerge.Poly := [(nat_lit 3904, Int.ofNat (nat_lit 49453121621400)), (nat_lit 3905, Int.ofNat (nat_lit 54003049493400)), (nat_lit 3924, Int.ofNat (nat_lit 25323261106500)), (nat_lit 3925, Int.ofNat (nat_lit 30034904980500)), (nat_lit 3926, Int.ofNat (nat_lit 36065647557450)), (nat_lit 3947, Int.ofNat (nat_lit 5439574781550)), (nat_lit 3968, Int.ofNat (nat_lit 3482925254550)), (nat_lit 4167, Int.ofNat (nat_lit 912670214400)), (nat_lit 4168, Int.ofNat (nat_lit 602111059200)), (nat_lit 4173, Int.ofNat (nat_lit 2995132039200))]
theorem block019_data_flat155_step : block019_data_flat155 = (CoefficientMerge.fastMerge block019_data_flat145 block019_data_flat154) := by decide +kernel
theorem block019_data_flat155_original : block019_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49453121621400 : Int) atom1446Coded) (CoefficientMerge.scale (54003049493400 : Int) atom1447Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25323261106500 : Int) atom1448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034904980500 : Int) atom1449Coded) (CoefficientMerge.scale (36065647557450 : Int) atom1450Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5439574781550 : Int) atom1451Coded) (CoefficientMerge.scale (3482925254550 : Int) atom1452Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (912670214400 : Int) atom1453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (602111059200 : Int) atom1454Coded) (CoefficientMerge.scale (2995132039200 : Int) atom1455Coded))))) := by
  rw [block019_data_flat155_step, block019_data_flat145_original, block019_data_flat154_original]
def block019_data_flat156 : CoefficientMerge.Poly := [(nat_lit 3861, Int.ofNat (nat_lit 71113667221800)), (nat_lit 3862, Int.ofNat (nat_lit 53763791949000)), (nat_lit 3863, Int.ofNat (nat_lit 82935935850600)), (nat_lit 3880, Int.ofNat (nat_lit 15952947010560)), (nat_lit 3881, Int.ofNat (nat_lit 56181592441800)), (nat_lit 3882, Int.ofNat (nat_lit 64310888457900)), (nat_lit 3883, Int.ofNat (nat_lit 46815859734000)), (nat_lit 3884, Int.ofNat (nat_lit 61853161781250)), (nat_lit 3902, Int.ofNat (nat_lit 41682593433600)), (nat_lit 3903, Int.ofNat (nat_lit 73028319197400)), (nat_lit 3904, Int.ofNat (nat_lit 49453121621400)), (nat_lit 3905, Int.ofNat (nat_lit 54003049493400)), (nat_lit 3924, Int.ofNat (nat_lit 25323261106500)), (nat_lit 3925, Int.ofNat (nat_lit 30034904980500)), (nat_lit 3926, Int.ofNat (nat_lit 36065647557450)), (nat_lit 3947, Int.ofNat (nat_lit 5439574781550)), (nat_lit 3968, Int.ofNat (nat_lit 3482925254550)), (nat_lit 4167, Int.ofNat (nat_lit 912670214400)), (nat_lit 4168, Int.ofNat (nat_lit 602111059200)), (nat_lit 4173, Int.ofNat (nat_lit 2995132039200))]
theorem block019_data_flat156_step : block019_data_flat156 = (CoefficientMerge.fastMerge block019_data_flat136 block019_data_flat155) := by decide +kernel
theorem block019_data_flat156_original : block019_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (71113667221800 : Int) atom1436Coded) (CoefficientMerge.scale (53763791949000 : Int) atom1437Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82935935850600 : Int) atom1438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15952947010560 : Int) atom1439Coded) (CoefficientMerge.scale (56181592441800 : Int) atom1440Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64310888457900 : Int) atom1441Coded) (CoefficientMerge.scale (46815859734000 : Int) atom1442Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61853161781250 : Int) atom1443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41682593433600 : Int) atom1444Coded) (CoefficientMerge.scale (73028319197400 : Int) atom1445Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49453121621400 : Int) atom1446Coded) (CoefficientMerge.scale (54003049493400 : Int) atom1447Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25323261106500 : Int) atom1448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034904980500 : Int) atom1449Coded) (CoefficientMerge.scale (36065647557450 : Int) atom1450Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5439574781550 : Int) atom1451Coded) (CoefficientMerge.scale (3482925254550 : Int) atom1452Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (912670214400 : Int) atom1453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (602111059200 : Int) atom1454Coded) (CoefficientMerge.scale (2995132039200 : Int) atom1455Coded)))))) := by
  rw [block019_data_flat156_step, block019_data_flat136_original, block019_data_flat155_original]
def block019_data_flat157 : CoefficientMerge.Poly := [(nat_lit 3799, Int.ofNat (nat_lit 37107275293200)), (nat_lit 3800, Int.ofNat (nat_lit 48530465474400)), (nat_lit 3814, Int.ofNat (nat_lit 8314429795200)), (nat_lit 3815, Int.ofNat (nat_lit 15912566956800)), (nat_lit 3816, Int.ofNat (nat_lit 19319098982400)), (nat_lit 3817, Int.ofNat (nat_lit 19329077214000)), (nat_lit 3818, Int.ofNat (nat_lit 34558073524800)), (nat_lit 3819, Int.ofNat (nat_lit 38809323630000)), (nat_lit 3820, Int.ofNat (nat_lit 42738457266000)), (nat_lit 3821, Int.ofNat (nat_lit 60582834597600)), (nat_lit 3836, Int.ofNat (nat_lit 12733408598400)), (nat_lit 3837, Int.ofNat (nat_lit 24425203723200)), (nat_lit 3838, Int.ofNat (nat_lit 24919452658800)), (nat_lit 3839, Int.ofNat (nat_lit 46215639489600)), (nat_lit 3840, Int.ofNat (nat_lit 52704268570800)), (nat_lit 3841, Int.ofNat (nat_lit 52820365827600)), (nat_lit 3842, Int.ofNat (nat_lit 77218206357600)), (nat_lit 3858, Int.ofNat (nat_lit 19383530342400)), (nat_lit 3859, Int.ofNat (nat_lit 39580818694200)), (nat_lit 3860, Int.ofNat (nat_lit 66724705152000)), (nat_lit 3861, Int.ofNat (nat_lit 71113667221800)), (nat_lit 3862, Int.ofNat (nat_lit 53763791949000)), (nat_lit 3863, Int.ofNat (nat_lit 82935935850600)), (nat_lit 3880, Int.ofNat (nat_lit 15952947010560)), (nat_lit 3881, Int.ofNat (nat_lit 56181592441800)), (nat_lit 3882, Int.ofNat (nat_lit 64310888457900)), (nat_lit 3883, Int.ofNat (nat_lit 46815859734000)), (nat_lit 3884, Int.ofNat (nat_lit 61853161781250)), (nat_lit 3902, Int.ofNat (nat_lit 41682593433600)), (nat_lit 3903, Int.ofNat (nat_lit 73028319197400)), (nat_lit 3904, Int.ofNat (nat_lit 49453121621400)), (nat_lit 3905, Int.ofNat (nat_lit 54003049493400)), (nat_lit 3924, Int.ofNat (nat_lit 25323261106500)), (nat_lit 3925, Int.ofNat (nat_lit 30034904980500)), (nat_lit 3926, Int.ofNat (nat_lit 36065647557450)), (nat_lit 3947, Int.ofNat (nat_lit 5439574781550)), (nat_lit 3968, Int.ofNat (nat_lit 3482925254550)), (nat_lit 4167, Int.ofNat (nat_lit 912670214400)), (nat_lit 4168, Int.ofNat (nat_lit 602111059200)), (nat_lit 4173, Int.ofNat (nat_lit 2995132039200))]
theorem block019_data_flat157_step : block019_data_flat157 = (CoefficientMerge.fastMerge block019_data_flat117 block019_data_flat156) := by decide +kernel
theorem block019_data_flat157_original : block019_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37107275293200 : Int) atom1416Coded) (CoefficientMerge.scale (48530465474400 : Int) atom1417Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8314429795200 : Int) atom1418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15912566956800 : Int) atom1419Coded) (CoefficientMerge.scale (19319098982400 : Int) atom1420Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19329077214000 : Int) atom1421Coded) (CoefficientMerge.scale (34558073524800 : Int) atom1422Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38809323630000 : Int) atom1423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42738457266000 : Int) atom1424Coded) (CoefficientMerge.scale (60582834597600 : Int) atom1425Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12733408598400 : Int) atom1426Coded) (CoefficientMerge.scale (24425203723200 : Int) atom1427Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24919452658800 : Int) atom1428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46215639489600 : Int) atom1429Coded) (CoefficientMerge.scale (52704268570800 : Int) atom1430Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52820365827600 : Int) atom1431Coded) (CoefficientMerge.scale (77218206357600 : Int) atom1432Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19383530342400 : Int) atom1433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39580818694200 : Int) atom1434Coded) (CoefficientMerge.scale (66724705152000 : Int) atom1435Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (71113667221800 : Int) atom1436Coded) (CoefficientMerge.scale (53763791949000 : Int) atom1437Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82935935850600 : Int) atom1438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15952947010560 : Int) atom1439Coded) (CoefficientMerge.scale (56181592441800 : Int) atom1440Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64310888457900 : Int) atom1441Coded) (CoefficientMerge.scale (46815859734000 : Int) atom1442Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61853161781250 : Int) atom1443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41682593433600 : Int) atom1444Coded) (CoefficientMerge.scale (73028319197400 : Int) atom1445Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49453121621400 : Int) atom1446Coded) (CoefficientMerge.scale (54003049493400 : Int) atom1447Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25323261106500 : Int) atom1448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034904980500 : Int) atom1449Coded) (CoefficientMerge.scale (36065647557450 : Int) atom1450Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5439574781550 : Int) atom1451Coded) (CoefficientMerge.scale (3482925254550 : Int) atom1452Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (912670214400 : Int) atom1453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (602111059200 : Int) atom1454Coded) (CoefficientMerge.scale (2995132039200 : Int) atom1455Coded))))))) := by
  rw [block019_data_flat157_step, block019_data_flat117_original, block019_data_flat156_original]
def block019_data_flat158 : CoefficientMerge.Poly := [(nat_lit 3706, Int.ofNat (nat_lit 770276908800)), (nat_lit 3707, Int.ofNat (nat_lit 427179916800)), (nat_lit 3711, Int.ofNat (nat_lit 3093893233200)), (nat_lit 3726, Int.ofNat (nat_lit 1414429430400)), (nat_lit 3727, Int.ofNat (nat_lit 518028134400)), (nat_lit 3730, Int.ofNat (nat_lit 427179916800)), (nat_lit 3731, Int.ofNat (nat_lit 854359833600)), (nat_lit 3732, Int.ofNat (nat_lit 5687746762320)), (nat_lit 3734, Int.ofNat (nat_lit 2944323370800)), (nat_lit 3735, Int.ofNat (nat_lit 5786258284800)), (nat_lit 3736, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3737, Int.ofNat (nat_lit 17391151612800)), (nat_lit 3748, Int.ofNat (nat_lit 1834844054400)), (nat_lit 3749, Int.ofNat (nat_lit 2647162425600)), (nat_lit 3750, Int.ofNat (nat_lit 2478996576000)), (nat_lit 3751, Int.ofNat (nat_lit 3165190560000)), (nat_lit 3752, Int.ofNat (nat_lit 3851384544000)), (nat_lit 3753, Int.ofNat (nat_lit 7803362548800)), (nat_lit 3754, Int.ofNat (nat_lit 2139543982800)), (nat_lit 3755, Int.ofNat (nat_lit 9372338136000)), (nat_lit 3756, Int.ofNat (nat_lit 11410652912400)), (nat_lit 3757, Int.ofNat (nat_lit 20176096474800)), (nat_lit 3758, Int.ofNat (nat_lit 30348257839200)), (nat_lit 3770, Int.ofNat (nat_lit 3543563721600)), (nat_lit 3771, Int.ofNat (nat_lit 5560104211200)), (nat_lit 3772, Int.ofNat (nat_lit 6337146412800)), (nat_lit 3773, Int.ofNat (nat_lit 7114188614400)), (nat_lit 3774, Int.ofNat (nat_lit 12510442929600)), (nat_lit 3775, Int.ofNat (nat_lit 8456065254000)), (nat_lit 3776, Int.ofNat (nat_lit 19774108468800)), (nat_lit 3777, Int.ofNat (nat_lit 20318281326000)), (nat_lit 3778, Int.ofNat (nat_lit 30113920746000)), (nat_lit 3779, Int.ofNat (nat_lit 40982814885600)), (nat_lit 3792, Int.ofNat (nat_lit 5174965756800)), (nat_lit 3793, Int.ofNat (nat_lit 10622476166400)), (nat_lit 3794, Int.ofNat (nat_lit 11322200736000)), (nat_lit 3795, Int.ofNat (nat_lit 14101152139200)), (nat_lit 3796, Int.ofNat (nat_lit 13619552332400)), (nat_lit 3797, Int.ofNat (nat_lit 25094037416000)), (nat_lit 3798, Int.ofNat (nat_lit 27327261530800)), (nat_lit 3799, Int.ofNat (nat_lit 37107275293200)), (nat_lit 3800, Int.ofNat (nat_lit 48530465474400)), (nat_lit 3814, Int.ofNat (nat_lit 8314429795200)), (nat_lit 3815, Int.ofNat (nat_lit 15912566956800)), (nat_lit 3816, Int.ofNat (nat_lit 19319098982400)), (nat_lit 3817, Int.ofNat (nat_lit 19329077214000)), (nat_lit 3818, Int.ofNat (nat_lit 34558073524800)), (nat_lit 3819, Int.ofNat (nat_lit 38809323630000)), (nat_lit 3820, Int.ofNat (nat_lit 42738457266000)), (nat_lit 3821, Int.ofNat (nat_lit 60582834597600)), (nat_lit 3836, Int.ofNat (nat_lit 12733408598400)), (nat_lit 3837, Int.ofNat (nat_lit 24425203723200)), (nat_lit 3838, Int.ofNat (nat_lit 24919452658800)), (nat_lit 3839, Int.ofNat (nat_lit 46215639489600)), (nat_lit 3840, Int.ofNat (nat_lit 52704268570800)), (nat_lit 3841, Int.ofNat (nat_lit 52820365827600)), (nat_lit 3842, Int.ofNat (nat_lit 77218206357600)), (nat_lit 3858, Int.ofNat (nat_lit 19383530342400)), (nat_lit 3859, Int.ofNat (nat_lit 39580818694200)), (nat_lit 3860, Int.ofNat (nat_lit 66724705152000)), (nat_lit 3861, Int.ofNat (nat_lit 71113667221800)), (nat_lit 3862, Int.ofNat (nat_lit 53763791949000)), (nat_lit 3863, Int.ofNat (nat_lit 82935935850600)), (nat_lit 3880, Int.ofNat (nat_lit 15952947010560)), (nat_lit 3881, Int.ofNat (nat_lit 56181592441800)), (nat_lit 3882, Int.ofNat (nat_lit 64310888457900)), (nat_lit 3883, Int.ofNat (nat_lit 46815859734000)), (nat_lit 3884, Int.ofNat (nat_lit 61853161781250)), (nat_lit 3902, Int.ofNat (nat_lit 41682593433600)), (nat_lit 3903, Int.ofNat (nat_lit 73028319197400)), (nat_lit 3904, Int.ofNat (nat_lit 49453121621400)), (nat_lit 3905, Int.ofNat (nat_lit 54003049493400)), (nat_lit 3924, Int.ofNat (nat_lit 25323261106500)), (nat_lit 3925, Int.ofNat (nat_lit 30034904980500)), (nat_lit 3926, Int.ofNat (nat_lit 36065647557450)), (nat_lit 3947, Int.ofNat (nat_lit 5439574781550)), (nat_lit 3968, Int.ofNat (nat_lit 3482925254550)), (nat_lit 4167, Int.ofNat (nat_lit 912670214400)), (nat_lit 4168, Int.ofNat (nat_lit 602111059200)), (nat_lit 4173, Int.ofNat (nat_lit 2995132039200))]
theorem block019_data_flat158_step : block019_data_flat158 = (CoefficientMerge.fastMerge block019_data_flat078 block019_data_flat157) := by decide +kernel
theorem block019_data_flat158_original : block019_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (770276908800 : Int) atom1376Coded) (CoefficientMerge.scale (427179916800 : Int) atom1377Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3093893233200 : Int) atom1378Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1414429430400 : Int) atom1379Coded) (CoefficientMerge.scale (518028134400 : Int) atom1380Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1381Coded) (CoefficientMerge.scale (854359833600 : Int) atom1382Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5687746762320 : Int) atom1383Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2944323370800 : Int) atom1384Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1385Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1386Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1387Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1834844054400 : Int) atom1388Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2647162425600 : Int) atom1389Coded) (CoefficientMerge.scale (2478996576000 : Int) atom1390Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3165190560000 : Int) atom1391Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1392Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7803362548800 : Int) atom1393Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2139543982800 : Int) atom1394Coded) (CoefficientMerge.scale (9372338136000 : Int) atom1395Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11410652912400 : Int) atom1396Coded) (CoefficientMerge.scale (20176096474800 : Int) atom1397Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30348257839200 : Int) atom1398Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3543563721600 : Int) atom1399Coded) (CoefficientMerge.scale (5560104211200 : Int) atom1400Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6337146412800 : Int) atom1401Coded) (CoefficientMerge.scale (7114188614400 : Int) atom1402Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12510442929600 : Int) atom1403Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8456065254000 : Int) atom1404Coded) (CoefficientMerge.scale (19774108468800 : Int) atom1405Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20318281326000 : Int) atom1406Coded) (CoefficientMerge.scale (30113920746000 : Int) atom1407Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40982814885600 : Int) atom1408Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5174965756800 : Int) atom1409Coded) (CoefficientMerge.scale (10622476166400 : Int) atom1410Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11322200736000 : Int) atom1411Coded) (CoefficientMerge.scale (14101152139200 : Int) atom1412Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13619552332400 : Int) atom1413Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25094037416000 : Int) atom1414Coded) (CoefficientMerge.scale (27327261530800 : Int) atom1415Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37107275293200 : Int) atom1416Coded) (CoefficientMerge.scale (48530465474400 : Int) atom1417Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8314429795200 : Int) atom1418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15912566956800 : Int) atom1419Coded) (CoefficientMerge.scale (19319098982400 : Int) atom1420Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19329077214000 : Int) atom1421Coded) (CoefficientMerge.scale (34558073524800 : Int) atom1422Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38809323630000 : Int) atom1423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42738457266000 : Int) atom1424Coded) (CoefficientMerge.scale (60582834597600 : Int) atom1425Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12733408598400 : Int) atom1426Coded) (CoefficientMerge.scale (24425203723200 : Int) atom1427Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24919452658800 : Int) atom1428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46215639489600 : Int) atom1429Coded) (CoefficientMerge.scale (52704268570800 : Int) atom1430Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52820365827600 : Int) atom1431Coded) (CoefficientMerge.scale (77218206357600 : Int) atom1432Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19383530342400 : Int) atom1433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39580818694200 : Int) atom1434Coded) (CoefficientMerge.scale (66724705152000 : Int) atom1435Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (71113667221800 : Int) atom1436Coded) (CoefficientMerge.scale (53763791949000 : Int) atom1437Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82935935850600 : Int) atom1438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15952947010560 : Int) atom1439Coded) (CoefficientMerge.scale (56181592441800 : Int) atom1440Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64310888457900 : Int) atom1441Coded) (CoefficientMerge.scale (46815859734000 : Int) atom1442Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61853161781250 : Int) atom1443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41682593433600 : Int) atom1444Coded) (CoefficientMerge.scale (73028319197400 : Int) atom1445Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49453121621400 : Int) atom1446Coded) (CoefficientMerge.scale (54003049493400 : Int) atom1447Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25323261106500 : Int) atom1448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034904980500 : Int) atom1449Coded) (CoefficientMerge.scale (36065647557450 : Int) atom1450Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5439574781550 : Int) atom1451Coded) (CoefficientMerge.scale (3482925254550 : Int) atom1452Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (912670214400 : Int) atom1453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (602111059200 : Int) atom1454Coded) (CoefficientMerge.scale (2995132039200 : Int) atom1455Coded)))))))) := by
  rw [block019_data_flat158_step, block019_data_flat078_original, block019_data_flat157_original]
def block019_data_flat159 : CoefficientMerge.Poly := [(nat_lit 3706, Int.ofNat (nat_lit 770276908800)), (nat_lit 3707, Int.ofNat (nat_lit 427179916800)), (nat_lit 3711, Int.ofNat (nat_lit 3093893233200)), (nat_lit 3726, Int.ofNat (nat_lit 1414429430400)), (nat_lit 3727, Int.ofNat (nat_lit 518028134400)), (nat_lit 3730, Int.ofNat (nat_lit 427179916800)), (nat_lit 3731, Int.ofNat (nat_lit 854359833600)), (nat_lit 3732, Int.ofNat (nat_lit 5687746762320)), (nat_lit 3734, Int.ofNat (nat_lit 2944323370800)), (nat_lit 3735, Int.ofNat (nat_lit 5786258284800)), (nat_lit 3736, Int.ofNat (nat_lit 11171238059520)), (nat_lit 3737, Int.ofNat (nat_lit 17391151612800)), (nat_lit 3748, Int.ofNat (nat_lit 1834844054400)), (nat_lit 3749, Int.ofNat (nat_lit 2647162425600)), (nat_lit 3750, Int.ofNat (nat_lit 2478996576000)), (nat_lit 3751, Int.ofNat (nat_lit 3165190560000)), (nat_lit 3752, Int.ofNat (nat_lit 3851384544000)), (nat_lit 3753, Int.ofNat (nat_lit 7803362548800)), (nat_lit 3754, Int.ofNat (nat_lit 2139543982800)), (nat_lit 3755, Int.ofNat (nat_lit 9372338136000)), (nat_lit 3756, Int.ofNat (nat_lit 11410652912400)), (nat_lit 3757, Int.ofNat (nat_lit 20176096474800)), (nat_lit 3758, Int.ofNat (nat_lit 30348257839200)), (nat_lit 3770, Int.ofNat (nat_lit 3543563721600)), (nat_lit 3771, Int.ofNat (nat_lit 5560104211200)), (nat_lit 3772, Int.ofNat (nat_lit 6337146412800)), (nat_lit 3773, Int.ofNat (nat_lit 7114188614400)), (nat_lit 3774, Int.ofNat (nat_lit 12510442929600)), (nat_lit 3775, Int.ofNat (nat_lit 8456065254000)), (nat_lit 3776, Int.ofNat (nat_lit 19774108468800)), (nat_lit 3777, Int.ofNat (nat_lit 20318281326000)), (nat_lit 3778, Int.ofNat (nat_lit 30113920746000)), (nat_lit 3779, Int.ofNat (nat_lit 40982814885600)), (nat_lit 3792, Int.ofNat (nat_lit 5174965756800)), (nat_lit 3793, Int.ofNat (nat_lit 10622476166400)), (nat_lit 3794, Int.ofNat (nat_lit 11322200736000)), (nat_lit 3795, Int.ofNat (nat_lit 14101152139200)), (nat_lit 3796, Int.ofNat (nat_lit 13619552332400)), (nat_lit 3797, Int.ofNat (nat_lit 25094037416000)), (nat_lit 3798, Int.ofNat (nat_lit 27327261530800)), (nat_lit 3799, Int.ofNat (nat_lit 37107275293200)), (nat_lit 3800, Int.ofNat (nat_lit 48530465474400)), (nat_lit 3814, Int.ofNat (nat_lit 8314429795200)), (nat_lit 3815, Int.ofNat (nat_lit 15912566956800)), (nat_lit 3816, Int.ofNat (nat_lit 19319098982400)), (nat_lit 3817, Int.ofNat (nat_lit 19329077214000)), (nat_lit 3818, Int.ofNat (nat_lit 34558073524800)), (nat_lit 3819, Int.ofNat (nat_lit 38809323630000)), (nat_lit 3820, Int.ofNat (nat_lit 42738457266000)), (nat_lit 3821, Int.ofNat (nat_lit 60582834597600)), (nat_lit 3836, Int.ofNat (nat_lit 12733408598400)), (nat_lit 3837, Int.ofNat (nat_lit 24425203723200)), (nat_lit 3838, Int.ofNat (nat_lit 24919452658800)), (nat_lit 3839, Int.ofNat (nat_lit 46215639489600)), (nat_lit 3840, Int.ofNat (nat_lit 52704268570800)), (nat_lit 3841, Int.ofNat (nat_lit 52820365827600)), (nat_lit 3842, Int.ofNat (nat_lit 77218206357600)), (nat_lit 3858, Int.ofNat (nat_lit 19383530342400)), (nat_lit 3859, Int.ofNat (nat_lit 39580818694200)), (nat_lit 3860, Int.ofNat (nat_lit 66724705152000)), (nat_lit 3861, Int.ofNat (nat_lit 71113667221800)), (nat_lit 3862, Int.ofNat (nat_lit 53763791949000)), (nat_lit 3863, Int.ofNat (nat_lit 82935935850600)), (nat_lit 3880, Int.ofNat (nat_lit 15952947010560)), (nat_lit 3881, Int.ofNat (nat_lit 56181592441800)), (nat_lit 3882, Int.ofNat (nat_lit 64310888457900)), (nat_lit 3883, Int.ofNat (nat_lit 46815859734000)), (nat_lit 3884, Int.ofNat (nat_lit 61853161781250)), (nat_lit 3902, Int.ofNat (nat_lit 41682593433600)), (nat_lit 3903, Int.ofNat (nat_lit 73028319197400)), (nat_lit 3904, Int.ofNat (nat_lit 49453121621400)), (nat_lit 3905, Int.ofNat (nat_lit 54003049493400)), (nat_lit 3924, Int.ofNat (nat_lit 25323261106500)), (nat_lit 3925, Int.ofNat (nat_lit 30034904980500)), (nat_lit 3926, Int.ofNat (nat_lit 36065647557450)), (nat_lit 3947, Int.ofNat (nat_lit 5439574781550)), (nat_lit 3968, Int.ofNat (nat_lit 3482925254550)), (nat_lit 4167, Int.ofNat (nat_lit 912670214400)), (nat_lit 4168, Int.ofNat (nat_lit 602111059200)), (nat_lit 4173, Int.ofNat (nat_lit 2995132039200))]
theorem block019_data_flat159_step : block019_data_flat159 = (CoefficientMerge.trim block019_data_flat158) := by decide +kernel
theorem block019_data_flat159_original : block019_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (770276908800 : Int) atom1376Coded) (CoefficientMerge.scale (427179916800 : Int) atom1377Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3093893233200 : Int) atom1378Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1414429430400 : Int) atom1379Coded) (CoefficientMerge.scale (518028134400 : Int) atom1380Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1381Coded) (CoefficientMerge.scale (854359833600 : Int) atom1382Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5687746762320 : Int) atom1383Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2944323370800 : Int) atom1384Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1385Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1386Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1387Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1834844054400 : Int) atom1388Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2647162425600 : Int) atom1389Coded) (CoefficientMerge.scale (2478996576000 : Int) atom1390Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3165190560000 : Int) atom1391Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1392Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7803362548800 : Int) atom1393Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2139543982800 : Int) atom1394Coded) (CoefficientMerge.scale (9372338136000 : Int) atom1395Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11410652912400 : Int) atom1396Coded) (CoefficientMerge.scale (20176096474800 : Int) atom1397Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30348257839200 : Int) atom1398Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3543563721600 : Int) atom1399Coded) (CoefficientMerge.scale (5560104211200 : Int) atom1400Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6337146412800 : Int) atom1401Coded) (CoefficientMerge.scale (7114188614400 : Int) atom1402Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12510442929600 : Int) atom1403Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8456065254000 : Int) atom1404Coded) (CoefficientMerge.scale (19774108468800 : Int) atom1405Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20318281326000 : Int) atom1406Coded) (CoefficientMerge.scale (30113920746000 : Int) atom1407Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40982814885600 : Int) atom1408Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5174965756800 : Int) atom1409Coded) (CoefficientMerge.scale (10622476166400 : Int) atom1410Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11322200736000 : Int) atom1411Coded) (CoefficientMerge.scale (14101152139200 : Int) atom1412Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13619552332400 : Int) atom1413Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25094037416000 : Int) atom1414Coded) (CoefficientMerge.scale (27327261530800 : Int) atom1415Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37107275293200 : Int) atom1416Coded) (CoefficientMerge.scale (48530465474400 : Int) atom1417Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8314429795200 : Int) atom1418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15912566956800 : Int) atom1419Coded) (CoefficientMerge.scale (19319098982400 : Int) atom1420Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19329077214000 : Int) atom1421Coded) (CoefficientMerge.scale (34558073524800 : Int) atom1422Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38809323630000 : Int) atom1423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42738457266000 : Int) atom1424Coded) (CoefficientMerge.scale (60582834597600 : Int) atom1425Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12733408598400 : Int) atom1426Coded) (CoefficientMerge.scale (24425203723200 : Int) atom1427Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24919452658800 : Int) atom1428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46215639489600 : Int) atom1429Coded) (CoefficientMerge.scale (52704268570800 : Int) atom1430Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52820365827600 : Int) atom1431Coded) (CoefficientMerge.scale (77218206357600 : Int) atom1432Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19383530342400 : Int) atom1433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39580818694200 : Int) atom1434Coded) (CoefficientMerge.scale (66724705152000 : Int) atom1435Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (71113667221800 : Int) atom1436Coded) (CoefficientMerge.scale (53763791949000 : Int) atom1437Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82935935850600 : Int) atom1438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15952947010560 : Int) atom1439Coded) (CoefficientMerge.scale (56181592441800 : Int) atom1440Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64310888457900 : Int) atom1441Coded) (CoefficientMerge.scale (46815859734000 : Int) atom1442Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61853161781250 : Int) atom1443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41682593433600 : Int) atom1444Coded) (CoefficientMerge.scale (73028319197400 : Int) atom1445Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49453121621400 : Int) atom1446Coded) (CoefficientMerge.scale (54003049493400 : Int) atom1447Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25323261106500 : Int) atom1448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034904980500 : Int) atom1449Coded) (CoefficientMerge.scale (36065647557450 : Int) atom1450Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5439574781550 : Int) atom1451Coded) (CoefficientMerge.scale (3482925254550 : Int) atom1452Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (912670214400 : Int) atom1453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (602111059200 : Int) atom1454Coded) (CoefficientMerge.scale (2995132039200 : Int) atom1455Coded))))))))) := by
  rw [block019_data_flat159_step, block019_data_flat158_original]
theorem block019_data : block019 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (770276908800 : Int) atom1376Coded) (CoefficientMerge.scale (427179916800 : Int) atom1377Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3093893233200 : Int) atom1378Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1414429430400 : Int) atom1379Coded) (CoefficientMerge.scale (518028134400 : Int) atom1380Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1381Coded) (CoefficientMerge.scale (854359833600 : Int) atom1382Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5687746762320 : Int) atom1383Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2944323370800 : Int) atom1384Coded) (CoefficientMerge.scale (5786258284800 : Int) atom1385Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11171238059520 : Int) atom1386Coded) (CoefficientMerge.scale (17391151612800 : Int) atom1387Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1834844054400 : Int) atom1388Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2647162425600 : Int) atom1389Coded) (CoefficientMerge.scale (2478996576000 : Int) atom1390Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3165190560000 : Int) atom1391Coded) (CoefficientMerge.scale (3851384544000 : Int) atom1392Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7803362548800 : Int) atom1393Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2139543982800 : Int) atom1394Coded) (CoefficientMerge.scale (9372338136000 : Int) atom1395Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11410652912400 : Int) atom1396Coded) (CoefficientMerge.scale (20176096474800 : Int) atom1397Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30348257839200 : Int) atom1398Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3543563721600 : Int) atom1399Coded) (CoefficientMerge.scale (5560104211200 : Int) atom1400Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6337146412800 : Int) atom1401Coded) (CoefficientMerge.scale (7114188614400 : Int) atom1402Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12510442929600 : Int) atom1403Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8456065254000 : Int) atom1404Coded) (CoefficientMerge.scale (19774108468800 : Int) atom1405Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20318281326000 : Int) atom1406Coded) (CoefficientMerge.scale (30113920746000 : Int) atom1407Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40982814885600 : Int) atom1408Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5174965756800 : Int) atom1409Coded) (CoefficientMerge.scale (10622476166400 : Int) atom1410Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11322200736000 : Int) atom1411Coded) (CoefficientMerge.scale (14101152139200 : Int) atom1412Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13619552332400 : Int) atom1413Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25094037416000 : Int) atom1414Coded) (CoefficientMerge.scale (27327261530800 : Int) atom1415Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37107275293200 : Int) atom1416Coded) (CoefficientMerge.scale (48530465474400 : Int) atom1417Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8314429795200 : Int) atom1418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15912566956800 : Int) atom1419Coded) (CoefficientMerge.scale (19319098982400 : Int) atom1420Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19329077214000 : Int) atom1421Coded) (CoefficientMerge.scale (34558073524800 : Int) atom1422Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38809323630000 : Int) atom1423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42738457266000 : Int) atom1424Coded) (CoefficientMerge.scale (60582834597600 : Int) atom1425Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12733408598400 : Int) atom1426Coded) (CoefficientMerge.scale (24425203723200 : Int) atom1427Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24919452658800 : Int) atom1428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46215639489600 : Int) atom1429Coded) (CoefficientMerge.scale (52704268570800 : Int) atom1430Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52820365827600 : Int) atom1431Coded) (CoefficientMerge.scale (77218206357600 : Int) atom1432Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19383530342400 : Int) atom1433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39580818694200 : Int) atom1434Coded) (CoefficientMerge.scale (66724705152000 : Int) atom1435Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (71113667221800 : Int) atom1436Coded) (CoefficientMerge.scale (53763791949000 : Int) atom1437Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82935935850600 : Int) atom1438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15952947010560 : Int) atom1439Coded) (CoefficientMerge.scale (56181592441800 : Int) atom1440Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64310888457900 : Int) atom1441Coded) (CoefficientMerge.scale (46815859734000 : Int) atom1442Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61853161781250 : Int) atom1443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41682593433600 : Int) atom1444Coded) (CoefficientMerge.scale (73028319197400 : Int) atom1445Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49453121621400 : Int) atom1446Coded) (CoefficientMerge.scale (54003049493400 : Int) atom1447Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25323261106500 : Int) atom1448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30034904980500 : Int) atom1449Coded) (CoefficientMerge.scale (36065647557450 : Int) atom1450Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5439574781550 : Int) atom1451Coded) (CoefficientMerge.scale (3482925254550 : Int) atom1452Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (912670214400 : Int) atom1453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (602111059200 : Int) atom1454Coded) (CoefficientMerge.scale (2995132039200 : Int) atom1455Coded)))))))) := by
  have h : block019 = block019_data_flat159 := by decide +kernel
  exact h.trans block019_data_flat159_original
theorem block019_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block019 := by
  rw [block019_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1376Coded_nonneg g hg hA hB) (atom1377Coded_nonneg g hg hA hB)) (add_nonneg (atom1378Coded_nonneg g hg hA hB) (add_nonneg (atom1379Coded_nonneg g hg hA hB) (atom1380Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1381Coded_nonneg g hg hA hB) (atom1382Coded_nonneg g hg hA hB)) (add_nonneg (atom1383Coded_nonneg g hg hA hB) (add_nonneg (atom1384Coded_nonneg g hg hA hB) (atom1385Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1386Coded_nonneg g hg hA hB) (atom1387Coded_nonneg g hg hA hB)) (add_nonneg (atom1388Coded_nonneg g hg hA hB) (add_nonneg (atom1389Coded_nonneg g hg hA hB) (atom1390Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1391Coded_nonneg g hg hA hB) (atom1392Coded_nonneg g hg hA hB)) (add_nonneg (atom1393Coded_nonneg g hg hA hB) (add_nonneg (atom1394Coded_nonneg g hg hA hB) (atom1395Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1396Coded_nonneg g hg hA hB) (atom1397Coded_nonneg g hg hA hB)) (add_nonneg (atom1398Coded_nonneg g hg hA hB) (add_nonneg (atom1399Coded_nonneg g hg hA hB) (atom1400Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1401Coded_nonneg g hg hA hB) (atom1402Coded_nonneg g hg hA hB)) (add_nonneg (atom1403Coded_nonneg g hg hA hB) (add_nonneg (atom1404Coded_nonneg g hg hA hB) (atom1405Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1406Coded_nonneg g hg hA hB) (atom1407Coded_nonneg g hg hA hB)) (add_nonneg (atom1408Coded_nonneg g hg hA hB) (add_nonneg (atom1409Coded_nonneg g hg hA hB) (atom1410Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1411Coded_nonneg g hg hA hB) (atom1412Coded_nonneg g hg hA hB)) (add_nonneg (atom1413Coded_nonneg g hg hA hB) (add_nonneg (atom1414Coded_nonneg g hg hA hB) (atom1415Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1416Coded_nonneg g hg hA hB) (atom1417Coded_nonneg g hg hA hB)) (add_nonneg (atom1418Coded_nonneg g hg hA hB) (add_nonneg (atom1419Coded_nonneg g hg hA hB) (atom1420Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1421Coded_nonneg g hg hA hB) (atom1422Coded_nonneg g hg hA hB)) (add_nonneg (atom1423Coded_nonneg g hg hA hB) (add_nonneg (atom1424Coded_nonneg g hg hA hB) (atom1425Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1426Coded_nonneg g hg hA hB) (atom1427Coded_nonneg g hg hA hB)) (add_nonneg (atom1428Coded_nonneg g hg hA hB) (add_nonneg (atom1429Coded_nonneg g hg hA hB) (atom1430Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1431Coded_nonneg g hg hA hB) (atom1432Coded_nonneg g hg hA hB)) (add_nonneg (atom1433Coded_nonneg g hg hA hB) (add_nonneg (atom1434Coded_nonneg g hg hA hB) (atom1435Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1436Coded_nonneg g hg hA hB) (atom1437Coded_nonneg g hg hA hB)) (add_nonneg (atom1438Coded_nonneg g hg hA hB) (add_nonneg (atom1439Coded_nonneg g hg hA hB) (atom1440Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1441Coded_nonneg g hg hA hB) (atom1442Coded_nonneg g hg hA hB)) (add_nonneg (atom1443Coded_nonneg g hg hA hB) (add_nonneg (atom1444Coded_nonneg g hg hA hB) (atom1445Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1446Coded_nonneg g hg hA hB) (atom1447Coded_nonneg g hg hA hB)) (add_nonneg (atom1448Coded_nonneg g hg hA hB) (add_nonneg (atom1449Coded_nonneg g hg hA hB) (atom1450Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1451Coded_nonneg g hg hA hB) (atom1452Coded_nonneg g hg hA hB)) (add_nonneg (atom1453Coded_nonneg g hg hA hB) (add_nonneg (atom1454Coded_nonneg g hg hA hB) (atom1455Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
