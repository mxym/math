-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0335 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0335 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0335 = ((g 1) * (g 5) * (g 16)) := by
  norm_num [atom0335, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0335_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5898088840 : Int) atom0335) := by
  rw [SparsePolynomial.eval_scale, eval_atom0335]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0335Coded : CoefficientMerge.Poly := [(nat_lit 430, Int.ofNat (nat_lit 1))]
theorem atom0335Coded_decode : atom0335 = SparsePolynomial.decodeCubic 18 atom0335Coded := by decide +kernel
theorem atom0335Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5898088840 : Int) atom0335Coded) := by
  have h := atom0335_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0335Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0336 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0336 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0336 = ((g 1) * (g 5) * (g 17)) := by
  norm_num [atom0336, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0336_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6018711240 : Int) atom0336) := by
  rw [SparsePolynomial.eval_scale, eval_atom0336]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0336Coded : CoefficientMerge.Poly := [(nat_lit 431, Int.ofNat (nat_lit 1))]
theorem atom0336Coded_decode : atom0336 = SparsePolynomial.decodeCubic 18 atom0336Coded := by decide +kernel
theorem atom0336Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6018711240 : Int) atom0336Coded) := by
  have h := atom0336_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0336Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0337 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0337 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0337 = ((g 1) * (g 6) * (g 6)) := by
  norm_num [atom0337, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0337_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2000907360 : Int) atom0337) := by
  rw [SparsePolynomial.eval_scale, eval_atom0337]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0337Coded : CoefficientMerge.Poly := [(nat_lit 438, Int.ofNat (nat_lit 1))]
theorem atom0337Coded_decode : atom0337 = SparsePolynomial.decodeCubic 18 atom0337Coded := by decide +kernel
theorem atom0337Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2000907360 : Int) atom0337Coded) := by
  have h := atom0337_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0337Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0338 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0338 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0338 = ((g 1) * (g 6) * (g 7)) := by
  norm_num [atom0338, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0338_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3212404128 : Int) atom0338) := by
  rw [SparsePolynomial.eval_scale, eval_atom0338]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0338Coded : CoefficientMerge.Poly := [(nat_lit 439, Int.ofNat (nat_lit 1))]
theorem atom0338Coded_decode : atom0338 = SparsePolynomial.decodeCubic 18 atom0338Coded := by decide +kernel
theorem atom0338Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3212404128 : Int) atom0338Coded) := by
  have h := atom0338_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0338Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0339 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0339 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0339 = ((g 1) * (g 6) * (g 8)) := by
  norm_num [atom0339, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0339_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2905871040 : Int) atom0339) := by
  rw [SparsePolynomial.eval_scale, eval_atom0339]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0339Coded : CoefficientMerge.Poly := [(nat_lit 440, Int.ofNat (nat_lit 1))]
theorem atom0339Coded_decode : atom0339 = SparsePolynomial.decodeCubic 18 atom0339Coded := by decide +kernel
theorem atom0339Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2905871040 : Int) atom0339Coded) := by
  have h := atom0339_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0339Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0340 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0340 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0340 = ((g 1) * (g 6) * (g 9)) := by
  norm_num [atom0340, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0340_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2903290560 : Int) atom0340) := by
  rw [SparsePolynomial.eval_scale, eval_atom0340]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0340Coded : CoefficientMerge.Poly := [(nat_lit 441, Int.ofNat (nat_lit 1))]
theorem atom0340Coded_decode : atom0340 = SparsePolynomial.decodeCubic 18 atom0340Coded := by decide +kernel
theorem atom0340Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2903290560 : Int) atom0340Coded) := by
  have h := atom0340_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0340Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0341 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0341 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0341 = ((g 1) * (g 6) * (g 10)) := by
  norm_num [atom0341, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0341_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2951029440 : Int) atom0341) := by
  rw [SparsePolynomial.eval_scale, eval_atom0341]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0341Coded : CoefficientMerge.Poly := [(nat_lit 442, Int.ofNat (nat_lit 1))]
theorem atom0341Coded_decode : atom0341 = SparsePolynomial.decodeCubic 18 atom0341Coded := by decide +kernel
theorem atom0341Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2951029440 : Int) atom0341Coded) := by
  have h := atom0341_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0341Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0342 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0342 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0342 = ((g 1) * (g 6) * (g 11)) := by
  norm_num [atom0342, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0342_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3174733760 : Int) atom0342) := by
  rw [SparsePolynomial.eval_scale, eval_atom0342]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0342Coded : CoefficientMerge.Poly := [(nat_lit 443, Int.ofNat (nat_lit 1))]
theorem atom0342Coded_decode : atom0342 = SparsePolynomial.decodeCubic 18 atom0342Coded := by decide +kernel
theorem atom0342Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3174733760 : Int) atom0342Coded) := by
  have h := atom0342_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0342Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0343 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0343 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0343 = ((g 1) * (g 6) * (g 12)) := by
  norm_num [atom0343, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0343_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5883494400 : Int) atom0343) := by
  rw [SparsePolynomial.eval_scale, eval_atom0343]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0343Coded : CoefficientMerge.Poly := [(nat_lit 444, Int.ofNat (nat_lit 1))]
theorem atom0343Coded_decode : atom0343 = SparsePolynomial.decodeCubic 18 atom0343Coded := by decide +kernel
theorem atom0343Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5883494400 : Int) atom0343Coded) := by
  have h := atom0343_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0343Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0344 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0344 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0344 = ((g 1) * (g 6) * (g 13)) := by
  norm_num [atom0344, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0344_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4456174040 : Int) atom0344) := by
  rw [SparsePolynomial.eval_scale, eval_atom0344]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0344Coded : CoefficientMerge.Poly := [(nat_lit 445, Int.ofNat (nat_lit 1))]
theorem atom0344Coded_decode : atom0344 = SparsePolynomial.decodeCubic 18 atom0344Coded := by decide +kernel
theorem atom0344Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4456174040 : Int) atom0344Coded) := by
  have h := atom0344_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0344Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0345 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0345 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0345 = ((g 1) * (g 6) * (g 14)) := by
  norm_num [atom0345, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0345_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6098833080 : Int) atom0345) := by
  rw [SparsePolynomial.eval_scale, eval_atom0345]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0345Coded : CoefficientMerge.Poly := [(nat_lit 446, Int.ofNat (nat_lit 1))]
theorem atom0345Coded_decode : atom0345 = SparsePolynomial.decodeCubic 18 atom0345Coded := by decide +kernel
theorem atom0345Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6098833080 : Int) atom0345Coded) := by
  have h := atom0345_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0345Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0346 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0346 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0346 = ((g 1) * (g 6) * (g 15)) := by
  norm_num [atom0346, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0346_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5959982600 : Int) atom0346) := by
  rw [SparsePolynomial.eval_scale, eval_atom0346]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0346Coded : CoefficientMerge.Poly := [(nat_lit 447, Int.ofNat (nat_lit 1))]
theorem atom0346Coded_decode : atom0346 = SparsePolynomial.decodeCubic 18 atom0346Coded := by decide +kernel
theorem atom0346Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5959982600 : Int) atom0346Coded) := by
  have h := atom0346_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0346Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0347 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0347 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0347 = ((g 1) * (g 6) * (g 16)) := by
  norm_num [atom0347, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0347_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6391196200 : Int) atom0347) := by
  rw [SparsePolynomial.eval_scale, eval_atom0347]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0347Coded : CoefficientMerge.Poly := [(nat_lit 448, Int.ofNat (nat_lit 1))]
theorem atom0347Coded_decode : atom0347 = SparsePolynomial.decodeCubic 18 atom0347Coded := by decide +kernel
theorem atom0347Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6391196200 : Int) atom0347Coded) := by
  have h := atom0347_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0347Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0348 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0348 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0348 = ((g 1) * (g 6) * (g 17)) := by
  norm_num [atom0348, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0348_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6822409800 : Int) atom0348) := by
  rw [SparsePolynomial.eval_scale, eval_atom0348]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0348Coded : CoefficientMerge.Poly := [(nat_lit 449, Int.ofNat (nat_lit 1))]
theorem atom0348Coded_decode : atom0348 = SparsePolynomial.decodeCubic 18 atom0348Coded := by decide +kernel
theorem atom0348Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6822409800 : Int) atom0348Coded) := by
  have h := atom0348_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0348Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0349 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0349 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0349 = ((g 1) * (g 7) * (g 7)) := by
  norm_num [atom0349, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0349_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2336973120 : Int) atom0349) := by
  rw [SparsePolynomial.eval_scale, eval_atom0349]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0349Coded : CoefficientMerge.Poly := [(nat_lit 457, Int.ofNat (nat_lit 1))]
theorem atom0349Coded_decode : atom0349 = SparsePolynomial.decodeCubic 18 atom0349Coded := by decide +kernel
theorem atom0349Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2336973120 : Int) atom0349Coded) := by
  have h := atom0349_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0349Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0350 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0350 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0350 = ((g 1) * (g 7) * (g 8)) := by
  norm_num [atom0350, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0350_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3943380288 : Int) atom0350) := by
  rw [SparsePolynomial.eval_scale, eval_atom0350]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0350Coded : CoefficientMerge.Poly := [(nat_lit 458, Int.ofNat (nat_lit 1))]
theorem atom0350Coded_decode : atom0350 = SparsePolynomial.decodeCubic 18 atom0350Coded := by decide +kernel
theorem atom0350Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3943380288 : Int) atom0350Coded) := by
  have h := atom0350_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0350Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0351 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0351 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0351 = ((g 1) * (g 7) * (g 9)) := by
  norm_num [atom0351, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0351_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3334043520 : Int) atom0351) := by
  rw [SparsePolynomial.eval_scale, eval_atom0351]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0351Coded : CoefficientMerge.Poly := [(nat_lit 459, Int.ofNat (nat_lit 1))]
theorem atom0351Coded_decode : atom0351 = SparsePolynomial.decodeCubic 18 atom0351Coded := by decide +kernel
theorem atom0351Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3334043520 : Int) atom0351Coded) := by
  have h := atom0351_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0351Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0352 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0352 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0352 = ((g 1) * (g 7) * (g 10)) := by
  norm_num [atom0352, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0352_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3358235520 : Int) atom0352) := by
  rw [SparsePolynomial.eval_scale, eval_atom0352]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0352Coded : CoefficientMerge.Poly := [(nat_lit 460, Int.ofNat (nat_lit 1))]
theorem atom0352Coded_decode : atom0352 = SparsePolynomial.decodeCubic 18 atom0352Coded := by decide +kernel
theorem atom0352Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3358235520 : Int) atom0352Coded) := by
  have h := atom0352_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0352Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0353 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0353 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0353 = ((g 1) * (g 7) * (g 11)) := by
  norm_num [atom0353, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0353_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3558392960 : Int) atom0353) := by
  rw [SparsePolynomial.eval_scale, eval_atom0353]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0353Coded : CoefficientMerge.Poly := [(nat_lit 461, Int.ofNat (nat_lit 1))]
theorem atom0353Coded_decode : atom0353 = SparsePolynomial.decodeCubic 18 atom0353Coded := by decide +kernel
theorem atom0353Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3558392960 : Int) atom0353Coded) := by
  have h := atom0353_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0353Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0354 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0354 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0354 = ((g 1) * (g 7) * (g 12)) := by
  norm_num [atom0354, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0354_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6159605760 : Int) atom0354) := by
  rw [SparsePolynomial.eval_scale, eval_atom0354]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0354Coded : CoefficientMerge.Poly := [(nat_lit 462, Int.ofNat (nat_lit 1))]
theorem atom0354Coded_decode : atom0354 = SparsePolynomial.decodeCubic 18 atom0354Coded := by decide +kernel
theorem atom0354Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6159605760 : Int) atom0354Coded) := by
  have h := atom0354_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0354Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0355 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0355 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0355 = ((g 1) * (g 7) * (g 13)) := by
  norm_num [atom0355, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0355_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4881594320 : Int) atom0355) := by
  rw [SparsePolynomial.eval_scale, eval_atom0355]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0355Coded : CoefficientMerge.Poly := [(nat_lit 463, Int.ofNat (nat_lit 1))]
theorem atom0355Coded_decode : atom0355 = SparsePolynomial.decodeCubic 18 atom0355Coded := by decide +kernel
theorem atom0355Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4881594320 : Int) atom0355Coded) := by
  have h := atom0355_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0355Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0356 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0356 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0356 = ((g 1) * (g 7) * (g 14)) := by
  norm_num [atom0356, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0356_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6576221880 : Int) atom0356) := by
  rw [SparsePolynomial.eval_scale, eval_atom0356]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0356Coded : CoefficientMerge.Poly := [(nat_lit 464, Int.ofNat (nat_lit 1))]
theorem atom0356Coded_decode : atom0356 = SparsePolynomial.decodeCubic 18 atom0356Coded := by decide +kernel
theorem atom0356Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6576221880 : Int) atom0356Coded) := by
  have h := atom0356_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0356Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0357 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0357 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0357 = ((g 1) * (g 7) * (g 15)) := by
  norm_num [atom0357, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0357_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6516018800 : Int) atom0357) := by
  rw [SparsePolynomial.eval_scale, eval_atom0357]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0357Coded : CoefficientMerge.Poly := [(nat_lit 465, Int.ofNat (nat_lit 1))]
theorem atom0357Coded_decode : atom0357 = SparsePolynomial.decodeCubic 18 atom0357Coded := by decide +kernel
theorem atom0357Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6516018800 : Int) atom0357Coded) := by
  have h := atom0357_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0357Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0358 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0358 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0358 = ((g 1) * (g 7) * (g 16)) := by
  norm_num [atom0358, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0358_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7042158640 : Int) atom0358) := by
  rw [SparsePolynomial.eval_scale, eval_atom0358]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0358Coded : CoefficientMerge.Poly := [(nat_lit 466, Int.ofNat (nat_lit 1))]
theorem atom0358Coded_decode : atom0358 = SparsePolynomial.decodeCubic 18 atom0358Coded := by decide +kernel
theorem atom0358Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7042158640 : Int) atom0358Coded) := by
  have h := atom0358_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0358Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0359 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0359 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0359 = ((g 1) * (g 7) * (g 17)) := by
  norm_num [atom0359, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0359_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7568298480 : Int) atom0359) := by
  rw [SparsePolynomial.eval_scale, eval_atom0359]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0359Coded : CoefficientMerge.Poly := [(nat_lit 467, Int.ofNat (nat_lit 1))]
theorem atom0359Coded_decode : atom0359 = SparsePolynomial.decodeCubic 18 atom0359Coded := by decide +kernel
theorem atom0359Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7568298480 : Int) atom0359Coded) := by
  have h := atom0359_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0359Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0360 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0360 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0360 = ((g 1) * (g 8) * (g 8)) := by
  norm_num [atom0360, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0360_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2731883520 : Int) atom0360) := by
  rw [SparsePolynomial.eval_scale, eval_atom0360]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0360Coded : CoefficientMerge.Poly := [(nat_lit 476, Int.ofNat (nat_lit 1))]
theorem atom0360Coded_decode : atom0360 = SparsePolynomial.decodeCubic 18 atom0360Coded := by decide +kernel
theorem atom0360Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2731883520 : Int) atom0360Coded) := by
  have h := atom0360_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0360Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0361 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0361 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0361 = ((g 1) * (g 8) * (g 9)) := by
  norm_num [atom0361, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0361_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4672629120 : Int) atom0361) := by
  rw [SparsePolynomial.eval_scale, eval_atom0361]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0361Coded : CoefficientMerge.Poly := [(nat_lit 477, Int.ofNat (nat_lit 1))]
theorem atom0361Coded_decode : atom0361 = SparsePolynomial.decodeCubic 18 atom0361Coded := by decide +kernel
theorem atom0361Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4672629120 : Int) atom0361Coded) := by
  have h := atom0361_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0361Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0362 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0362 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0362 = ((g 1) * (g 8) * (g 10)) := by
  norm_num [atom0362, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0362_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3937045632 : Int) atom0362) := by
  rw [SparsePolynomial.eval_scale, eval_atom0362]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0362Coded : CoefficientMerge.Poly := [(nat_lit 478, Int.ofNat (nat_lit 1))]
theorem atom0362Coded_decode : atom0362 = SparsePolynomial.decodeCubic 18 atom0362Coded := by decide +kernel
theorem atom0362Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3937045632 : Int) atom0362Coded) := by
  have h := atom0362_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0362Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0363 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0363 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0363 = ((g 1) * (g 8) * (g 11)) := by
  norm_num [atom0363, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0363_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4045591040 : Int) atom0363) := by
  rw [SparsePolynomial.eval_scale, eval_atom0363]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0363Coded : CoefficientMerge.Poly := [(nat_lit 479, Int.ofNat (nat_lit 1))]
theorem atom0363Coded_decode : atom0363 = SparsePolynomial.decodeCubic 18 atom0363Coded := by decide +kernel
theorem atom0363Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4045591040 : Int) atom0363Coded) := by
  have h := atom0363_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0363Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0364 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0364 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0364 = ((g 1) * (g 8) * (g 12)) := by
  norm_num [atom0364, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0364_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6538183680 : Int) atom0364) := by
  rw [SparsePolynomial.eval_scale, eval_atom0364]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0364Coded : CoefficientMerge.Poly := [(nat_lit 480, Int.ofNat (nat_lit 1))]
theorem atom0364Coded_decode : atom0364 = SparsePolynomial.decodeCubic 18 atom0364Coded := by decide +kernel
theorem atom0364Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6538183680 : Int) atom0364Coded) := by
  have h := atom0364_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0364Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0365 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0365 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0365 = ((g 1) * (g 8) * (g 13)) := by
  norm_num [atom0365, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0365_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5324168960 : Int) atom0365) := by
  rw [SparsePolynomial.eval_scale, eval_atom0365]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0365Coded : CoefficientMerge.Poly := [(nat_lit 481, Int.ofNat (nat_lit 1))]
theorem atom0365Coded_decode : atom0365 = SparsePolynomial.decodeCubic 18 atom0365Coded := by decide +kernel
theorem atom0365Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5324168960 : Int) atom0365Coded) := by
  have h := atom0365_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0365Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0366 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0366 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0366 = ((g 1) * (g 8) * (g 14)) := by
  norm_num [atom0366, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0366_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7156077240 : Int) atom0366) := by
  rw [SparsePolynomial.eval_scale, eval_atom0366]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0366Coded : CoefficientMerge.Poly := [(nat_lit 482, Int.ofNat (nat_lit 1))]
theorem atom0366Coded_decode : atom0366 = SparsePolynomial.decodeCubic 18 atom0366Coded := by decide +kernel
theorem atom0366Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7156077240 : Int) atom0366Coded) := by
  have h := atom0366_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0366Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0367 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0367 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0367 = ((g 1) * (g 8) * (g 15)) := by
  norm_num [atom0367, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0367_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6966759680 : Int) atom0367) := by
  rw [SparsePolynomial.eval_scale, eval_atom0367]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0367Coded : CoefficientMerge.Poly := [(nat_lit 483, Int.ofNat (nat_lit 1))]
theorem atom0367Coded_decode : atom0367 = SparsePolynomial.decodeCubic 18 atom0367Coded := by decide +kernel
theorem atom0367Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6966759680 : Int) atom0367Coded) := by
  have h := atom0367_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0367Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0368 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0368 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0368 = ((g 1) * (g 8) * (g 16)) := by
  norm_num [atom0368, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0368_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7463345920 : Int) atom0368) := by
  rw [SparsePolynomial.eval_scale, eval_atom0368]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0368Coded : CoefficientMerge.Poly := [(nat_lit 484, Int.ofNat (nat_lit 1))]
theorem atom0368Coded_decode : atom0368 = SparsePolynomial.decodeCubic 18 atom0368Coded := by decide +kernel
theorem atom0368Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7463345920 : Int) atom0368Coded) := by
  have h := atom0368_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0368Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0369 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0369 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0369 = ((g 1) * (g 8) * (g 17)) := by
  norm_num [atom0369, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0369_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8011165440 : Int) atom0369) := by
  rw [SparsePolynomial.eval_scale, eval_atom0369]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0369Coded : CoefficientMerge.Poly := [(nat_lit 485, Int.ofNat (nat_lit 1))]
theorem atom0369Coded_decode : atom0369 = SparsePolynomial.decodeCubic 18 atom0369Coded := by decide +kernel
theorem atom0369Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8011165440 : Int) atom0369Coded) := by
  have h := atom0369_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0369Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0370 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0370 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0370 = ((g 1) * (g 9) * (g 9)) := by
  norm_num [atom0370, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0370_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3038632320 : Int) atom0370) := by
  rw [SparsePolynomial.eval_scale, eval_atom0370]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0370Coded : CoefficientMerge.Poly := [(nat_lit 495, Int.ofNat (nat_lit 1))]
theorem atom0370Coded_decode : atom0370 = SparsePolynomial.decodeCubic 18 atom0370Coded := by decide +kernel
theorem atom0370Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3038632320 : Int) atom0370Coded) := by
  have h := atom0370_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0370Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0371 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0371 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0371 = ((g 1) * (g 9) * (g 10)) := by
  norm_num [atom0371, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0371_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5210772480 : Int) atom0371) := by
  rw [SparsePolynomial.eval_scale, eval_atom0371]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0371Coded : CoefficientMerge.Poly := [(nat_lit 496, Int.ofNat (nat_lit 1))]
theorem atom0371Coded_decode : atom0371 = SparsePolynomial.decodeCubic 18 atom0371Coded := by decide +kernel
theorem atom0371Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5210772480 : Int) atom0371Coded) := by
  have h := atom0371_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0371Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0372 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0372 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0372 = ((g 1) * (g 9) * (g 11)) := by
  norm_num [atom0372, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0372_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4660776320 : Int) atom0372) := by
  rw [SparsePolynomial.eval_scale, eval_atom0372]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0372Coded : CoefficientMerge.Poly := [(nat_lit 497, Int.ofNat (nat_lit 1))]
theorem atom0372Coded_decode : atom0372 = SparsePolynomial.decodeCubic 18 atom0372Coded := by decide +kernel
theorem atom0372Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4660776320 : Int) atom0372Coded) := by
  have h := atom0372_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0372Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0373 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0373 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0373 = ((g 1) * (g 9) * (g 12)) := by
  norm_num [atom0373, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0373_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6904803360 : Int) atom0373) := by
  rw [SparsePolynomial.eval_scale, eval_atom0373]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0373Coded : CoefficientMerge.Poly := [(nat_lit 498, Int.ofNat (nat_lit 1))]
theorem atom0373Coded_decode : atom0373 = SparsePolynomial.decodeCubic 18 atom0373Coded := by decide +kernel
theorem atom0373Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6904803360 : Int) atom0373Coded) := by
  have h := atom0373_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0373Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0374 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0374 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0374 = ((g 1) * (g 9) * (g 13)) := by
  norm_num [atom0374, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0374_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5640737120 : Int) atom0374) := by
  rw [SparsePolynomial.eval_scale, eval_atom0374]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0374Coded : CoefficientMerge.Poly := [(nat_lit 499, Int.ofNat (nat_lit 1))]
theorem atom0374Coded_decode : atom0374 = SparsePolynomial.decodeCubic 18 atom0374Coded := by decide +kernel
theorem atom0374Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5640737120 : Int) atom0374Coded) := by
  have h := atom0374_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0374Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0375 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0375 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0375 = ((g 1) * (g 9) * (g 14)) := by
  norm_num [atom0375, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0375_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7615402680 : Int) atom0375) := by
  rw [SparsePolynomial.eval_scale, eval_atom0375]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0375Coded : CoefficientMerge.Poly := [(nat_lit 500, Int.ofNat (nat_lit 1))]
theorem atom0375Coded_decode : atom0375 = SparsePolynomial.decodeCubic 18 atom0375Coded := by decide +kernel
theorem atom0375Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7615402680 : Int) atom0375Coded) := by
  have h := atom0375_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0375Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0376 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0376 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0376 = ((g 1) * (g 9) * (g 15)) := by
  norm_num [atom0376, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0376_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7207039520 : Int) atom0376) := by
  rw [SparsePolynomial.eval_scale, eval_atom0376]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0376Coded : CoefficientMerge.Poly := [(nat_lit 501, Int.ofNat (nat_lit 1))]
theorem atom0376Coded_decode : atom0376 = SparsePolynomial.decodeCubic 18 atom0376Coded := by decide +kernel
theorem atom0376Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7207039520 : Int) atom0376Coded) := by
  have h := atom0376_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0376Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0377 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0377 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0377 = ((g 1) * (g 9) * (g 16)) := by
  norm_num [atom0377, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0377_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7686420640 : Int) atom0377) := by
  rw [SparsePolynomial.eval_scale, eval_atom0377]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0377Coded : CoefficientMerge.Poly := [(nat_lit 502, Int.ofNat (nat_lit 1))]
theorem atom0377Coded_decode : atom0377 = SparsePolynomial.decodeCubic 18 atom0377Coded := by decide +kernel
theorem atom0377Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7686420640 : Int) atom0377Coded) := by
  have h := atom0377_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0377Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0378 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0378 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0378 = ((g 1) * (g 9) * (g 17)) := by
  norm_num [atom0378, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0378_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8208003360 : Int) atom0378) := by
  rw [SparsePolynomial.eval_scale, eval_atom0378]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0378Coded : CoefficientMerge.Poly := [(nat_lit 503, Int.ofNat (nat_lit 1))]
theorem atom0378Coded_decode : atom0378 = SparsePolynomial.decodeCubic 18 atom0378Coded := by decide +kernel
theorem atom0378Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8208003360 : Int) atom0378Coded) := by
  have h := atom0378_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0378Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0379 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0379 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0379 = ((g 1) * (g 10) * (g 10)) := by
  norm_num [atom0379, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0379_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3287337600 : Int) atom0379) := by
  rw [SparsePolynomial.eval_scale, eval_atom0379]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0379Coded : CoefficientMerge.Poly := [(nat_lit 514, Int.ofNat (nat_lit 1))]
theorem atom0379Coded_decode : atom0379 = SparsePolynomial.decodeCubic 18 atom0379Coded := by decide +kernel
theorem atom0379Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3287337600 : Int) atom0379Coded) := by
  have h := atom0379_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0379Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0380 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0380 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0380 = ((g 1) * (g 10) * (g 11)) := by
  norm_num [atom0380, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0380_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5911061120 : Int) atom0380) := by
  rw [SparsePolynomial.eval_scale, eval_atom0380]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0380Coded : CoefficientMerge.Poly := [(nat_lit 515, Int.ofNat (nat_lit 1))]
theorem atom0380Coded_decode : atom0380 = SparsePolynomial.decodeCubic 18 atom0380Coded := by decide +kernel
theorem atom0380Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5911061120 : Int) atom0380Coded) := by
  have h := atom0380_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0380Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0381 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0381 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0381 = ((g 1) * (g 10) * (g 12)) := by
  norm_num [atom0381, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0381_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7349472480 : Int) atom0381) := by
  rw [SparsePolynomial.eval_scale, eval_atom0381]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0381Coded : CoefficientMerge.Poly := [(nat_lit 516, Int.ofNat (nat_lit 1))]
theorem atom0381Coded_decode : atom0381 = SparsePolynomial.decodeCubic 18 atom0381Coded := by decide +kernel
theorem atom0381Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7349472480 : Int) atom0381Coded) := by
  have h := atom0381_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0381Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0382 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0382 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0382 = ((g 1) * (g 10) * (g 13)) := by
  norm_num [atom0382, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0382_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5975361440 : Int) atom0382) := by
  rw [SparsePolynomial.eval_scale, eval_atom0382]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0382Coded : CoefficientMerge.Poly := [(nat_lit 517, Int.ofNat (nat_lit 1))]
theorem atom0382Coded_decode : atom0382 = SparsePolynomial.decodeCubic 18 atom0382Coded := by decide +kernel
theorem atom0382Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5975361440 : Int) atom0382Coded) := by
  have h := atom0382_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0382Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0383 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0383 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0383 = ((g 1) * (g 10) * (g 14)) := by
  norm_num [atom0383, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0383_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8125047480 : Int) atom0383) := by
  rw [SparsePolynomial.eval_scale, eval_atom0383]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0383Coded : CoefficientMerge.Poly := [(nat_lit 518, Int.ofNat (nat_lit 1))]
theorem atom0383Coded_decode : atom0383 = SparsePolynomial.decodeCubic 18 atom0383Coded := by decide +kernel
theorem atom0383Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8125047480 : Int) atom0383Coded) := by
  have h := atom0383_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0383Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0384 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0384 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0384 = ((g 1) * (g 10) * (g 15)) := by
  norm_num [atom0384, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0384_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7310555360 : Int) atom0384) := by
  rw [SparsePolynomial.eval_scale, eval_atom0384]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0384Coded : CoefficientMerge.Poly := [(nat_lit 519, Int.ofNat (nat_lit 1))]
theorem atom0384Coded_decode : atom0384 = SparsePolynomial.decodeCubic 18 atom0384Coded := by decide +kernel
theorem atom0384Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7310555360 : Int) atom0384Coded) := by
  have h := atom0384_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0384Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0385 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0385 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0385 = ((g 1) * (g 10) * (g 16)) := by
  norm_num [atom0385, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0385_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7652744800 : Int) atom0385) := by
  rw [SparsePolynomial.eval_scale, eval_atom0385]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0385Coded : CoefficientMerge.Poly := [(nat_lit 520, Int.ofNat (nat_lit 1))]
theorem atom0385Coded_decode : atom0385 = SparsePolynomial.decodeCubic 18 atom0385Coded := by decide +kernel
theorem atom0385Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7652744800 : Int) atom0385Coded) := by
  have h := atom0385_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0385Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0386 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0386 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0386 = ((g 1) * (g 10) * (g 17)) := by
  norm_num [atom0386, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0386_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8198641920 : Int) atom0386) := by
  rw [SparsePolynomial.eval_scale, eval_atom0386]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0386Coded : CoefficientMerge.Poly := [(nat_lit 521, Int.ofNat (nat_lit 1))]
theorem atom0386Coded_decode : atom0386 = SparsePolynomial.decodeCubic 18 atom0386Coded := by decide +kernel
theorem atom0386Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8198641920 : Int) atom0386Coded) := by
  have h := atom0386_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0386Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0387 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0387 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0387 = ((g 1) * (g 11) * (g 11)) := by
  norm_num [atom0387, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0387_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3794524160 : Int) atom0387) := by
  rw [SparsePolynomial.eval_scale, eval_atom0387]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0387Coded : CoefficientMerge.Poly := [(nat_lit 533, Int.ofNat (nat_lit 1))]
theorem atom0387Coded_decode : atom0387 = SparsePolynomial.decodeCubic 18 atom0387Coded := by decide +kernel
theorem atom0387Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3794524160 : Int) atom0387Coded) := by
  have h := atom0387_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0387Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0388 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0388 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0388 = ((g 1) * (g 11) * (g 12)) := by
  norm_num [atom0388, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0388_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7850429440 : Int) atom0388) := by
  rw [SparsePolynomial.eval_scale, eval_atom0388]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0388Coded : CoefficientMerge.Poly := [(nat_lit 534, Int.ofNat (nat_lit 1))]
theorem atom0388Coded_decode : atom0388 = SparsePolynomial.decodeCubic 18 atom0388Coded := by decide +kernel
theorem atom0388Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7850429440 : Int) atom0388Coded) := by
  have h := atom0388_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0388Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0389 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0389 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0389 = ((g 1) * (g 11) * (g 13)) := by
  norm_num [atom0389, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0389_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6205292800 : Int) atom0389) := by
  rw [SparsePolynomial.eval_scale, eval_atom0389]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0389Coded : CoefficientMerge.Poly := [(nat_lit 535, Int.ofNat (nat_lit 1))]
theorem atom0389Coded_decode : atom0389 = SparsePolynomial.decodeCubic 18 atom0389Coded := by decide +kernel
theorem atom0389Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6205292800 : Int) atom0389Coded) := by
  have h := atom0389_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0389Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0390 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0390 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0390 = ((g 1) * (g 11) * (g 14)) := by
  norm_num [atom0390, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0390_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8413864120 : Int) atom0390) := by
  rw [SparsePolynomial.eval_scale, eval_atom0390]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0390Coded : CoefficientMerge.Poly := [(nat_lit 536, Int.ofNat (nat_lit 1))]
theorem atom0390Coded_decode : atom0390 = SparsePolynomial.decodeCubic 18 atom0390Coded := by decide +kernel
theorem atom0390Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8413864120 : Int) atom0390Coded) := by
  have h := atom0390_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0390Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0391 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0391 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0391 = ((g 1) * (g 11) * (g 15)) := by
  norm_num [atom0391, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0391_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7605570560 : Int) atom0391) := by
  rw [SparsePolynomial.eval_scale, eval_atom0391]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0391Coded : CoefficientMerge.Poly := [(nat_lit 537, Int.ofNat (nat_lit 1))]
theorem atom0391Coded_decode : atom0391 = SparsePolynomial.decodeCubic 18 atom0391Coded := by decide +kernel
theorem atom0391Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7605570560 : Int) atom0391Coded) := by
  have h := atom0391_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0391Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0392 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0392 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0392 = ((g 1) * (g 11) * (g 16)) := by
  norm_num [atom0392, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0392_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7277580800 : Int) atom0392) := by
  rw [SparsePolynomial.eval_scale, eval_atom0392]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0392Coded : CoefficientMerge.Poly := [(nat_lit 538, Int.ofNat (nat_lit 1))]
theorem atom0392Coded_decode : atom0392 = SparsePolynomial.decodeCubic 18 atom0392Coded := by decide +kernel
theorem atom0392Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7277580800 : Int) atom0392Coded) := by
  have h := atom0392_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0392Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0393 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0393 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0393 = ((g 1) * (g 11) * (g 17)) := by
  norm_num [atom0393, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0393_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8654338560 : Int) atom0393) := by
  rw [SparsePolynomial.eval_scale, eval_atom0393]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0393Coded : CoefficientMerge.Poly := [(nat_lit 539, Int.ofNat (nat_lit 1))]
theorem atom0393Coded_decode : atom0393 = SparsePolynomial.decodeCubic 18 atom0393Coded := by decide +kernel
theorem atom0393Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8654338560 : Int) atom0393Coded) := by
  have h := atom0393_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0393Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0394 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0394 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0394 = ((g 1) * (g 12) * (g 12)) := by
  norm_num [atom0394, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0394_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5546741760 : Int) atom0394) := by
  rw [SparsePolynomial.eval_scale, eval_atom0394]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0394Coded : CoefficientMerge.Poly := [(nat_lit 552, Int.ofNat (nat_lit 1))]
theorem atom0394Coded_decode : atom0394 = SparsePolynomial.decodeCubic 18 atom0394Coded := by decide +kernel
theorem atom0394Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5546741760 : Int) atom0394Coded) := by
  have h := atom0394_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0394Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0395 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0395 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0395 = ((g 1) * (g 12) * (g 13)) := by
  norm_num [atom0395, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0395_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8918250880 : Int) atom0395) := by
  rw [SparsePolynomial.eval_scale, eval_atom0395]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0395Coded : CoefficientMerge.Poly := [(nat_lit 553, Int.ofNat (nat_lit 1))]
theorem atom0395Coded_decode : atom0395 = SparsePolynomial.decodeCubic 18 atom0395Coded := by decide +kernel
theorem atom0395Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8918250880 : Int) atom0395Coded) := by
  have h := atom0395_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0395Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0396 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0396 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0396 = ((g 1) * (g 12) * (g 14)) := by
  norm_num [atom0396, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0396_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12516486840 : Int) atom0396) := by
  rw [SparsePolynomial.eval_scale, eval_atom0396]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0396Coded : CoefficientMerge.Poly := [(nat_lit 554, Int.ofNat (nat_lit 1))]
theorem atom0396Coded_decode : atom0396 = SparsePolynomial.decodeCubic 18 atom0396Coded := by decide +kernel
theorem atom0396Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12516486840 : Int) atom0396Coded) := by
  have h := atom0396_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0396Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0397 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0397 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0397 = ((g 1) * (g 12) * (g 15)) := by
  norm_num [atom0397, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0397_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11769116800 : Int) atom0397) := by
  rw [SparsePolynomial.eval_scale, eval_atom0397]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0397Coded : CoefficientMerge.Poly := [(nat_lit 555, Int.ofNat (nat_lit 1))]
theorem atom0397Coded_decode : atom0397 = SparsePolynomial.decodeCubic 18 atom0397Coded := by decide +kernel
theorem atom0397Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11769116800 : Int) atom0397Coded) := by
  have h := atom0397_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0397Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0398 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0398 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0398 = ((g 1) * (g 12) * (g 16)) := by
  norm_num [atom0398, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0398_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7645850240 : Int) atom0398) := by
  rw [SparsePolynomial.eval_scale, eval_atom0398]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0398Coded : CoefficientMerge.Poly := [(nat_lit 556, Int.ofNat (nat_lit 1))]
theorem atom0398Coded_decode : atom0398 = SparsePolynomial.decodeCubic 18 atom0398Coded := by decide +kernel
theorem atom0398Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7645850240 : Int) atom0398Coded) := by
  have h := atom0398_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0398Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0399 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0399 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0399 = ((g 1) * (g 12) * (g 17)) := by
  norm_num [atom0399, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0399_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8873682720 : Int) atom0399) := by
  rw [SparsePolynomial.eval_scale, eval_atom0399]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0399Coded : CoefficientMerge.Poly := [(nat_lit 557, Int.ofNat (nat_lit 1))]
theorem atom0399Coded_decode : atom0399 = SparsePolynomial.decodeCubic 18 atom0399Coded := by decide +kernel
theorem atom0399Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8873682720 : Int) atom0399Coded) := by
  have h := atom0399_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0399Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0400 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0400 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0400 = ((g 1) * (g 13) * (g 13)) := by
  norm_num [atom0400, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0400_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3470027456 : Int) atom0400) := by
  rw [SparsePolynomial.eval_scale, eval_atom0400]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0400Coded : CoefficientMerge.Poly := [(nat_lit 571, Int.ofNat (nat_lit 1))]
theorem atom0400Coded_decode : atom0400 = SparsePolynomial.decodeCubic 18 atom0400Coded := by decide +kernel
theorem atom0400Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3470027456 : Int) atom0400Coded) := by
  have h := atom0400_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0400Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0401 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0401 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0401 = ((g 1) * (g 13) * (g 14)) := by
  norm_num [atom0401, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0401_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9201418000 : Int) atom0401) := by
  rw [SparsePolynomial.eval_scale, eval_atom0401]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0401Coded : CoefficientMerge.Poly := [(nat_lit 572, Int.ofNat (nat_lit 1))]
theorem atom0401Coded_decode : atom0401 = SparsePolynomial.decodeCubic 18 atom0401Coded := by decide +kernel
theorem atom0401Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9201418000 : Int) atom0401Coded) := by
  have h := atom0401_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0401Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0402 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0402 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0402 = ((g 1) * (g 13) * (g 15)) := by
  norm_num [atom0402, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0402_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10093237280 : Int) atom0402) := by
  rw [SparsePolynomial.eval_scale, eval_atom0402]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0402Coded : CoefficientMerge.Poly := [(nat_lit 573, Int.ofNat (nat_lit 1))]
theorem atom0402Coded_decode : atom0402 = SparsePolynomial.decodeCubic 18 atom0402Coded := by decide +kernel
theorem atom0402Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10093237280 : Int) atom0402Coded) := by
  have h := atom0402_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0402Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0403 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0403 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0403 = ((g 1) * (g 13) * (g 16)) := by
  norm_num [atom0403, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0403_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7347075680 : Int) atom0403) := by
  rw [SparsePolynomial.eval_scale, eval_atom0403]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0403Coded : CoefficientMerge.Poly := [(nat_lit 574, Int.ofNat (nat_lit 1))]
theorem atom0403Coded_decode : atom0403 = SparsePolynomial.decodeCubic 18 atom0403Coded := by decide +kernel
theorem atom0403Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7347075680 : Int) atom0403Coded) := by
  have h := atom0403_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0403Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0404 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0404 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0404 = ((g 1) * (g 13) * (g 17)) := by
  norm_num [atom0404, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0404_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7882412160 : Int) atom0404) := by
  rw [SparsePolynomial.eval_scale, eval_atom0404]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0404Coded : CoefficientMerge.Poly := [(nat_lit 575, Int.ofNat (nat_lit 1))]
theorem atom0404Coded_decode : atom0404 = SparsePolynomial.decodeCubic 18 atom0404Coded := by decide +kernel
theorem atom0404Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7882412160 : Int) atom0404Coded) := by
  have h := atom0404_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0404Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0405 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0405 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0405 = ((g 1) * (g 14) * (g 14)) := by
  norm_num [atom0405, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0405_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6708730320 : Int) atom0405) := by
  rw [SparsePolynomial.eval_scale, eval_atom0405]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0405Coded : CoefficientMerge.Poly := [(nat_lit 590, Int.ofNat (nat_lit 1))]
theorem atom0405Coded_decode : atom0405 = SparsePolynomial.decodeCubic 18 atom0405Coded := by decide +kernel
theorem atom0405Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6708730320 : Int) atom0405Coded) := by
  have h := atom0405_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0405Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0406 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0406 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0406 = ((g 1) * (g 14) * (g 15)) := by
  norm_num [atom0406, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0406_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10927396240 : Int) atom0406) := by
  rw [SparsePolynomial.eval_scale, eval_atom0406]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0406Coded : CoefficientMerge.Poly := [(nat_lit 591, Int.ofNat (nat_lit 1))]
theorem atom0406Coded_decode : atom0406 = SparsePolynomial.decodeCubic 18 atom0406Coded := by decide +kernel
theorem atom0406Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10927396240 : Int) atom0406Coded) := by
  have h := atom0406_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0406Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0407 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0407 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0407 = ((g 1) * (g 14) * (g 16)) := by
  norm_num [atom0407, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0407_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8160306320 : Int) atom0407) := by
  rw [SparsePolynomial.eval_scale, eval_atom0407]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0407Coded : CoefficientMerge.Poly := [(nat_lit 592, Int.ofNat (nat_lit 1))]
theorem atom0407Coded_decode : atom0407 = SparsePolynomial.decodeCubic 18 atom0407Coded := by decide +kernel
theorem atom0407Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8160306320 : Int) atom0407Coded) := by
  have h := atom0407_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0407Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0408 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0408 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0408 = ((g 1) * (g 14) * (g 17)) := by
  norm_num [atom0408, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0408_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8967654960 : Int) atom0408) := by
  rw [SparsePolynomial.eval_scale, eval_atom0408]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0408Coded : CoefficientMerge.Poly := [(nat_lit 593, Int.ofNat (nat_lit 1))]
theorem atom0408Coded_decode : atom0408 = SparsePolynomial.decodeCubic 18 atom0408Coded := by decide +kernel
theorem atom0408Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8967654960 : Int) atom0408Coded) := by
  have h := atom0408_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0408Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0409 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0409 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0409 = ((g 1) * (g 15) * (g 15)) := by
  norm_num [atom0409, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0409_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3992019360 : Int) atom0409) := by
  rw [SparsePolynomial.eval_scale, eval_atom0409]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0409Coded : CoefficientMerge.Poly := [(nat_lit 609, Int.ofNat (nat_lit 1))]
theorem atom0409Coded_decode : atom0409 = SparsePolynomial.decodeCubic 18 atom0409Coded := by decide +kernel
theorem atom0409Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3992019360 : Int) atom0409Coded) := by
  have h := atom0409_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0409Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0410 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0410 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0410 = ((g 1) * (g 15) * (g 16)) := by
  norm_num [atom0410, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0410_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5176124800 : Int) atom0410) := by
  rw [SparsePolynomial.eval_scale, eval_atom0410]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0410Coded : CoefficientMerge.Poly := [(nat_lit 610, Int.ofNat (nat_lit 1))]
theorem atom0410Coded_decode : atom0410 = SparsePolynomial.decodeCubic 18 atom0410Coded := by decide +kernel
theorem atom0410Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5176124800 : Int) atom0410Coded) := by
  have h := atom0410_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0410Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0411 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0411 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0411 = ((g 1) * (g 15) * (g 17)) := by
  norm_num [atom0411, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0411_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5897774400 : Int) atom0411) := by
  rw [SparsePolynomial.eval_scale, eval_atom0411]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0411Coded : CoefficientMerge.Poly := [(nat_lit 611, Int.ofNat (nat_lit 1))]
theorem atom0411Coded_decode : atom0411 = SparsePolynomial.decodeCubic 18 atom0411Coded := by decide +kernel
theorem atom0411Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5897774400 : Int) atom0411Coded) := by
  have h := atom0411_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0411Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0412 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0412 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0412 = ((g 1) * (g 16) * (g 16)) := by
  norm_num [atom0412, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0412_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (769123040 : Int) atom0412) := by
  rw [SparsePolynomial.eval_scale, eval_atom0412]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0412Coded : CoefficientMerge.Poly := [(nat_lit 628, Int.ofNat (nat_lit 1))]
theorem atom0412Coded_decode : atom0412 = SparsePolynomial.decodeCubic 18 atom0412Coded := by decide +kernel
theorem atom0412Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (769123040 : Int) atom0412Coded) := by
  have h := atom0412_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0412Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0413 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0413 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0413 = ((g 1) * (g 16) * (g 17)) := by
  norm_num [atom0413, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0413_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1724694720 : Int) atom0413) := by
  rw [SparsePolynomial.eval_scale, eval_atom0413]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0413Coded : CoefficientMerge.Poly := [(nat_lit 629, Int.ofNat (nat_lit 1))]
theorem atom0413Coded_decode : atom0413 = SparsePolynomial.decodeCubic 18 atom0413Coded := by decide +kernel
theorem atom0413Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1724694720 : Int) atom0413Coded) := by
  have h := atom0413_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0413Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0414 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0414 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0414 = ((g 1) * (g 17) * (g 17)) := by
  norm_num [atom0414, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0414_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (333335520 : Int) atom0414) := by
  rw [SparsePolynomial.eval_scale, eval_atom0414]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0414Coded : CoefficientMerge.Poly := [(nat_lit 647, Int.ofNat (nat_lit 1))]
theorem atom0414Coded_decode : atom0414 = SparsePolynomial.decodeCubic 18 atom0414Coded := by decide +kernel
theorem atom0414Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (333335520 : Int) atom0414Coded) := by
  have h := atom0414_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0414Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block005 : CoefficientMerge.Poly := [(nat_lit 430, Int.ofNat (nat_lit 5898088840)), (nat_lit 431, Int.ofNat (nat_lit 6018711240)), (nat_lit 438, Int.ofNat (nat_lit 2000907360)), (nat_lit 439, Int.ofNat (nat_lit 3212404128)), (nat_lit 440, Int.ofNat (nat_lit 2905871040)), (nat_lit 441, Int.ofNat (nat_lit 2903290560)), (nat_lit 442, Int.ofNat (nat_lit 2951029440)), (nat_lit 443, Int.ofNat (nat_lit 3174733760)), (nat_lit 444, Int.ofNat (nat_lit 5883494400)), (nat_lit 445, Int.ofNat (nat_lit 4456174040)), (nat_lit 446, Int.ofNat (nat_lit 6098833080)), (nat_lit 447, Int.ofNat (nat_lit 5959982600)), (nat_lit 448, Int.ofNat (nat_lit 6391196200)), (nat_lit 449, Int.ofNat (nat_lit 6822409800)), (nat_lit 457, Int.ofNat (nat_lit 2336973120)), (nat_lit 458, Int.ofNat (nat_lit 3943380288)), (nat_lit 459, Int.ofNat (nat_lit 3334043520)), (nat_lit 460, Int.ofNat (nat_lit 3358235520)), (nat_lit 461, Int.ofNat (nat_lit 3558392960)), (nat_lit 462, Int.ofNat (nat_lit 6159605760)), (nat_lit 463, Int.ofNat (nat_lit 4881594320)), (nat_lit 464, Int.ofNat (nat_lit 6576221880)), (nat_lit 465, Int.ofNat (nat_lit 6516018800)), (nat_lit 466, Int.ofNat (nat_lit 7042158640)), (nat_lit 467, Int.ofNat (nat_lit 7568298480)), (nat_lit 476, Int.ofNat (nat_lit 2731883520)), (nat_lit 477, Int.ofNat (nat_lit 4672629120)), (nat_lit 478, Int.ofNat (nat_lit 3937045632)), (nat_lit 479, Int.ofNat (nat_lit 4045591040)), (nat_lit 480, Int.ofNat (nat_lit 6538183680)), (nat_lit 481, Int.ofNat (nat_lit 5324168960)), (nat_lit 482, Int.ofNat (nat_lit 7156077240)), (nat_lit 483, Int.ofNat (nat_lit 6966759680)), (nat_lit 484, Int.ofNat (nat_lit 7463345920)), (nat_lit 485, Int.ofNat (nat_lit 8011165440)), (nat_lit 495, Int.ofNat (nat_lit 3038632320)), (nat_lit 496, Int.ofNat (nat_lit 5210772480)), (nat_lit 497, Int.ofNat (nat_lit 4660776320)), (nat_lit 498, Int.ofNat (nat_lit 6904803360)), (nat_lit 499, Int.ofNat (nat_lit 5640737120)), (nat_lit 500, Int.ofNat (nat_lit 7615402680)), (nat_lit 501, Int.ofNat (nat_lit 7207039520)), (nat_lit 502, Int.ofNat (nat_lit 7686420640)), (nat_lit 503, Int.ofNat (nat_lit 8208003360)), (nat_lit 514, Int.ofNat (nat_lit 3287337600)), (nat_lit 515, Int.ofNat (nat_lit 5911061120)), (nat_lit 516, Int.ofNat (nat_lit 7349472480)), (nat_lit 517, Int.ofNat (nat_lit 5975361440)), (nat_lit 518, Int.ofNat (nat_lit 8125047480)), (nat_lit 519, Int.ofNat (nat_lit 7310555360)), (nat_lit 520, Int.ofNat (nat_lit 7652744800)), (nat_lit 521, Int.ofNat (nat_lit 8198641920)), (nat_lit 533, Int.ofNat (nat_lit 3794524160)), (nat_lit 534, Int.ofNat (nat_lit 7850429440)), (nat_lit 535, Int.ofNat (nat_lit 6205292800)), (nat_lit 536, Int.ofNat (nat_lit 8413864120)), (nat_lit 537, Int.ofNat (nat_lit 7605570560)), (nat_lit 538, Int.ofNat (nat_lit 7277580800)), (nat_lit 539, Int.ofNat (nat_lit 8654338560)), (nat_lit 552, Int.ofNat (nat_lit 5546741760)), (nat_lit 553, Int.ofNat (nat_lit 8918250880)), (nat_lit 554, Int.ofNat (nat_lit 12516486840)), (nat_lit 555, Int.ofNat (nat_lit 11769116800)), (nat_lit 556, Int.ofNat (nat_lit 7645850240)), (nat_lit 557, Int.ofNat (nat_lit 8873682720)), (nat_lit 571, Int.ofNat (nat_lit 3470027456)), (nat_lit 572, Int.ofNat (nat_lit 9201418000)), (nat_lit 573, Int.ofNat (nat_lit 10093237280)), (nat_lit 574, Int.ofNat (nat_lit 7347075680)), (nat_lit 575, Int.ofNat (nat_lit 7882412160)), (nat_lit 590, Int.ofNat (nat_lit 6708730320)), (nat_lit 591, Int.ofNat (nat_lit 10927396240)), (nat_lit 592, Int.ofNat (nat_lit 8160306320)), (nat_lit 593, Int.ofNat (nat_lit 8967654960)), (nat_lit 609, Int.ofNat (nat_lit 3992019360)), (nat_lit 610, Int.ofNat (nat_lit 5176124800)), (nat_lit 611, Int.ofNat (nat_lit 5897774400)), (nat_lit 628, Int.ofNat (nat_lit 769123040)), (nat_lit 629, Int.ofNat (nat_lit 1724694720)), (nat_lit 647, Int.ofNat (nat_lit 333335520))]
def block005_data_flat000 : CoefficientMerge.Poly := [(nat_lit 430, Int.ofNat (nat_lit 5898088840))]
theorem block005_data_flat000_step : block005_data_flat000 = (CoefficientMerge.scale (5898088840 : Int) atom0335Coded) := by decide +kernel
theorem block005_data_flat000_original : block005_data_flat000 = (CoefficientMerge.scale (5898088840 : Int) atom0335Coded) := by
  rw [block005_data_flat000_step]
def block005_data_flat001 : CoefficientMerge.Poly := [(nat_lit 431, Int.ofNat (nat_lit 6018711240))]
theorem block005_data_flat001_step : block005_data_flat001 = (CoefficientMerge.scale (6018711240 : Int) atom0336Coded) := by decide +kernel
theorem block005_data_flat001_original : block005_data_flat001 = (CoefficientMerge.scale (6018711240 : Int) atom0336Coded) := by
  rw [block005_data_flat001_step]
def block005_data_flat002 : CoefficientMerge.Poly := [(nat_lit 430, Int.ofNat (nat_lit 5898088840)), (nat_lit 431, Int.ofNat (nat_lit 6018711240))]
theorem block005_data_flat002_step : block005_data_flat002 = (CoefficientMerge.fastMerge block005_data_flat000 block005_data_flat001) := by decide +kernel
theorem block005_data_flat002_original : block005_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5898088840 : Int) atom0335Coded) (CoefficientMerge.scale (6018711240 : Int) atom0336Coded)) := by
  rw [block005_data_flat002_step, block005_data_flat000_original, block005_data_flat001_original]
def block005_data_flat003 : CoefficientMerge.Poly := [(nat_lit 438, Int.ofNat (nat_lit 2000907360))]
theorem block005_data_flat003_step : block005_data_flat003 = (CoefficientMerge.scale (2000907360 : Int) atom0337Coded) := by decide +kernel
theorem block005_data_flat003_original : block005_data_flat003 = (CoefficientMerge.scale (2000907360 : Int) atom0337Coded) := by
  rw [block005_data_flat003_step]
def block005_data_flat004 : CoefficientMerge.Poly := [(nat_lit 439, Int.ofNat (nat_lit 3212404128))]
theorem block005_data_flat004_step : block005_data_flat004 = (CoefficientMerge.scale (3212404128 : Int) atom0338Coded) := by decide +kernel
theorem block005_data_flat004_original : block005_data_flat004 = (CoefficientMerge.scale (3212404128 : Int) atom0338Coded) := by
  rw [block005_data_flat004_step]
def block005_data_flat005 : CoefficientMerge.Poly := [(nat_lit 440, Int.ofNat (nat_lit 2905871040))]
theorem block005_data_flat005_step : block005_data_flat005 = (CoefficientMerge.scale (2905871040 : Int) atom0339Coded) := by decide +kernel
theorem block005_data_flat005_original : block005_data_flat005 = (CoefficientMerge.scale (2905871040 : Int) atom0339Coded) := by
  rw [block005_data_flat005_step]
def block005_data_flat006 : CoefficientMerge.Poly := [(nat_lit 439, Int.ofNat (nat_lit 3212404128)), (nat_lit 440, Int.ofNat (nat_lit 2905871040))]
theorem block005_data_flat006_step : block005_data_flat006 = (CoefficientMerge.fastMerge block005_data_flat004 block005_data_flat005) := by decide +kernel
theorem block005_data_flat006_original : block005_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3212404128 : Int) atom0338Coded) (CoefficientMerge.scale (2905871040 : Int) atom0339Coded)) := by
  rw [block005_data_flat006_step, block005_data_flat004_original, block005_data_flat005_original]
def block005_data_flat007 : CoefficientMerge.Poly := [(nat_lit 438, Int.ofNat (nat_lit 2000907360)), (nat_lit 439, Int.ofNat (nat_lit 3212404128)), (nat_lit 440, Int.ofNat (nat_lit 2905871040))]
theorem block005_data_flat007_step : block005_data_flat007 = (CoefficientMerge.fastMerge block005_data_flat003 block005_data_flat006) := by decide +kernel
theorem block005_data_flat007_original : block005_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2000907360 : Int) atom0337Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3212404128 : Int) atom0338Coded) (CoefficientMerge.scale (2905871040 : Int) atom0339Coded))) := by
  rw [block005_data_flat007_step, block005_data_flat003_original, block005_data_flat006_original]
def block005_data_flat008 : CoefficientMerge.Poly := [(nat_lit 430, Int.ofNat (nat_lit 5898088840)), (nat_lit 431, Int.ofNat (nat_lit 6018711240)), (nat_lit 438, Int.ofNat (nat_lit 2000907360)), (nat_lit 439, Int.ofNat (nat_lit 3212404128)), (nat_lit 440, Int.ofNat (nat_lit 2905871040))]
theorem block005_data_flat008_step : block005_data_flat008 = (CoefficientMerge.fastMerge block005_data_flat002 block005_data_flat007) := by decide +kernel
theorem block005_data_flat008_original : block005_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5898088840 : Int) atom0335Coded) (CoefficientMerge.scale (6018711240 : Int) atom0336Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2000907360 : Int) atom0337Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3212404128 : Int) atom0338Coded) (CoefficientMerge.scale (2905871040 : Int) atom0339Coded)))) := by
  rw [block005_data_flat008_step, block005_data_flat002_original, block005_data_flat007_original]
def block005_data_flat009 : CoefficientMerge.Poly := [(nat_lit 441, Int.ofNat (nat_lit 2903290560))]
theorem block005_data_flat009_step : block005_data_flat009 = (CoefficientMerge.scale (2903290560 : Int) atom0340Coded) := by decide +kernel
theorem block005_data_flat009_original : block005_data_flat009 = (CoefficientMerge.scale (2903290560 : Int) atom0340Coded) := by
  rw [block005_data_flat009_step]
def block005_data_flat010 : CoefficientMerge.Poly := [(nat_lit 442, Int.ofNat (nat_lit 2951029440))]
theorem block005_data_flat010_step : block005_data_flat010 = (CoefficientMerge.scale (2951029440 : Int) atom0341Coded) := by decide +kernel
theorem block005_data_flat010_original : block005_data_flat010 = (CoefficientMerge.scale (2951029440 : Int) atom0341Coded) := by
  rw [block005_data_flat010_step]
def block005_data_flat011 : CoefficientMerge.Poly := [(nat_lit 441, Int.ofNat (nat_lit 2903290560)), (nat_lit 442, Int.ofNat (nat_lit 2951029440))]
theorem block005_data_flat011_step : block005_data_flat011 = (CoefficientMerge.fastMerge block005_data_flat009 block005_data_flat010) := by decide +kernel
theorem block005_data_flat011_original : block005_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2903290560 : Int) atom0340Coded) (CoefficientMerge.scale (2951029440 : Int) atom0341Coded)) := by
  rw [block005_data_flat011_step, block005_data_flat009_original, block005_data_flat010_original]
def block005_data_flat012 : CoefficientMerge.Poly := [(nat_lit 443, Int.ofNat (nat_lit 3174733760))]
theorem block005_data_flat012_step : block005_data_flat012 = (CoefficientMerge.scale (3174733760 : Int) atom0342Coded) := by decide +kernel
theorem block005_data_flat012_original : block005_data_flat012 = (CoefficientMerge.scale (3174733760 : Int) atom0342Coded) := by
  rw [block005_data_flat012_step]
def block005_data_flat013 : CoefficientMerge.Poly := [(nat_lit 444, Int.ofNat (nat_lit 5883494400))]
theorem block005_data_flat013_step : block005_data_flat013 = (CoefficientMerge.scale (5883494400 : Int) atom0343Coded) := by decide +kernel
theorem block005_data_flat013_original : block005_data_flat013 = (CoefficientMerge.scale (5883494400 : Int) atom0343Coded) := by
  rw [block005_data_flat013_step]
def block005_data_flat014 : CoefficientMerge.Poly := [(nat_lit 445, Int.ofNat (nat_lit 4456174040))]
theorem block005_data_flat014_step : block005_data_flat014 = (CoefficientMerge.scale (4456174040 : Int) atom0344Coded) := by decide +kernel
theorem block005_data_flat014_original : block005_data_flat014 = (CoefficientMerge.scale (4456174040 : Int) atom0344Coded) := by
  rw [block005_data_flat014_step]
def block005_data_flat015 : CoefficientMerge.Poly := [(nat_lit 444, Int.ofNat (nat_lit 5883494400)), (nat_lit 445, Int.ofNat (nat_lit 4456174040))]
theorem block005_data_flat015_step : block005_data_flat015 = (CoefficientMerge.fastMerge block005_data_flat013 block005_data_flat014) := by decide +kernel
theorem block005_data_flat015_original : block005_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5883494400 : Int) atom0343Coded) (CoefficientMerge.scale (4456174040 : Int) atom0344Coded)) := by
  rw [block005_data_flat015_step, block005_data_flat013_original, block005_data_flat014_original]
def block005_data_flat016 : CoefficientMerge.Poly := [(nat_lit 443, Int.ofNat (nat_lit 3174733760)), (nat_lit 444, Int.ofNat (nat_lit 5883494400)), (nat_lit 445, Int.ofNat (nat_lit 4456174040))]
theorem block005_data_flat016_step : block005_data_flat016 = (CoefficientMerge.fastMerge block005_data_flat012 block005_data_flat015) := by decide +kernel
theorem block005_data_flat016_original : block005_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3174733760 : Int) atom0342Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5883494400 : Int) atom0343Coded) (CoefficientMerge.scale (4456174040 : Int) atom0344Coded))) := by
  rw [block005_data_flat016_step, block005_data_flat012_original, block005_data_flat015_original]
def block005_data_flat017 : CoefficientMerge.Poly := [(nat_lit 441, Int.ofNat (nat_lit 2903290560)), (nat_lit 442, Int.ofNat (nat_lit 2951029440)), (nat_lit 443, Int.ofNat (nat_lit 3174733760)), (nat_lit 444, Int.ofNat (nat_lit 5883494400)), (nat_lit 445, Int.ofNat (nat_lit 4456174040))]
theorem block005_data_flat017_step : block005_data_flat017 = (CoefficientMerge.fastMerge block005_data_flat011 block005_data_flat016) := by decide +kernel
theorem block005_data_flat017_original : block005_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2903290560 : Int) atom0340Coded) (CoefficientMerge.scale (2951029440 : Int) atom0341Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3174733760 : Int) atom0342Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5883494400 : Int) atom0343Coded) (CoefficientMerge.scale (4456174040 : Int) atom0344Coded)))) := by
  rw [block005_data_flat017_step, block005_data_flat011_original, block005_data_flat016_original]
def block005_data_flat018 : CoefficientMerge.Poly := [(nat_lit 430, Int.ofNat (nat_lit 5898088840)), (nat_lit 431, Int.ofNat (nat_lit 6018711240)), (nat_lit 438, Int.ofNat (nat_lit 2000907360)), (nat_lit 439, Int.ofNat (nat_lit 3212404128)), (nat_lit 440, Int.ofNat (nat_lit 2905871040)), (nat_lit 441, Int.ofNat (nat_lit 2903290560)), (nat_lit 442, Int.ofNat (nat_lit 2951029440)), (nat_lit 443, Int.ofNat (nat_lit 3174733760)), (nat_lit 444, Int.ofNat (nat_lit 5883494400)), (nat_lit 445, Int.ofNat (nat_lit 4456174040))]
theorem block005_data_flat018_step : block005_data_flat018 = (CoefficientMerge.fastMerge block005_data_flat008 block005_data_flat017) := by decide +kernel
theorem block005_data_flat018_original : block005_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5898088840 : Int) atom0335Coded) (CoefficientMerge.scale (6018711240 : Int) atom0336Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2000907360 : Int) atom0337Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3212404128 : Int) atom0338Coded) (CoefficientMerge.scale (2905871040 : Int) atom0339Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2903290560 : Int) atom0340Coded) (CoefficientMerge.scale (2951029440 : Int) atom0341Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3174733760 : Int) atom0342Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5883494400 : Int) atom0343Coded) (CoefficientMerge.scale (4456174040 : Int) atom0344Coded))))) := by
  rw [block005_data_flat018_step, block005_data_flat008_original, block005_data_flat017_original]
def block005_data_flat019 : CoefficientMerge.Poly := [(nat_lit 446, Int.ofNat (nat_lit 6098833080))]
theorem block005_data_flat019_step : block005_data_flat019 = (CoefficientMerge.scale (6098833080 : Int) atom0345Coded) := by decide +kernel
theorem block005_data_flat019_original : block005_data_flat019 = (CoefficientMerge.scale (6098833080 : Int) atom0345Coded) := by
  rw [block005_data_flat019_step]
def block005_data_flat020 : CoefficientMerge.Poly := [(nat_lit 447, Int.ofNat (nat_lit 5959982600))]
theorem block005_data_flat020_step : block005_data_flat020 = (CoefficientMerge.scale (5959982600 : Int) atom0346Coded) := by decide +kernel
theorem block005_data_flat020_original : block005_data_flat020 = (CoefficientMerge.scale (5959982600 : Int) atom0346Coded) := by
  rw [block005_data_flat020_step]
def block005_data_flat021 : CoefficientMerge.Poly := [(nat_lit 446, Int.ofNat (nat_lit 6098833080)), (nat_lit 447, Int.ofNat (nat_lit 5959982600))]
theorem block005_data_flat021_step : block005_data_flat021 = (CoefficientMerge.fastMerge block005_data_flat019 block005_data_flat020) := by decide +kernel
theorem block005_data_flat021_original : block005_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6098833080 : Int) atom0345Coded) (CoefficientMerge.scale (5959982600 : Int) atom0346Coded)) := by
  rw [block005_data_flat021_step, block005_data_flat019_original, block005_data_flat020_original]
def block005_data_flat022 : CoefficientMerge.Poly := [(nat_lit 448, Int.ofNat (nat_lit 6391196200))]
theorem block005_data_flat022_step : block005_data_flat022 = (CoefficientMerge.scale (6391196200 : Int) atom0347Coded) := by decide +kernel
theorem block005_data_flat022_original : block005_data_flat022 = (CoefficientMerge.scale (6391196200 : Int) atom0347Coded) := by
  rw [block005_data_flat022_step]
def block005_data_flat023 : CoefficientMerge.Poly := [(nat_lit 449, Int.ofNat (nat_lit 6822409800))]
theorem block005_data_flat023_step : block005_data_flat023 = (CoefficientMerge.scale (6822409800 : Int) atom0348Coded) := by decide +kernel
theorem block005_data_flat023_original : block005_data_flat023 = (CoefficientMerge.scale (6822409800 : Int) atom0348Coded) := by
  rw [block005_data_flat023_step]
def block005_data_flat024 : CoefficientMerge.Poly := [(nat_lit 457, Int.ofNat (nat_lit 2336973120))]
theorem block005_data_flat024_step : block005_data_flat024 = (CoefficientMerge.scale (2336973120 : Int) atom0349Coded) := by decide +kernel
theorem block005_data_flat024_original : block005_data_flat024 = (CoefficientMerge.scale (2336973120 : Int) atom0349Coded) := by
  rw [block005_data_flat024_step]
def block005_data_flat025 : CoefficientMerge.Poly := [(nat_lit 449, Int.ofNat (nat_lit 6822409800)), (nat_lit 457, Int.ofNat (nat_lit 2336973120))]
theorem block005_data_flat025_step : block005_data_flat025 = (CoefficientMerge.fastMerge block005_data_flat023 block005_data_flat024) := by decide +kernel
theorem block005_data_flat025_original : block005_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6822409800 : Int) atom0348Coded) (CoefficientMerge.scale (2336973120 : Int) atom0349Coded)) := by
  rw [block005_data_flat025_step, block005_data_flat023_original, block005_data_flat024_original]
def block005_data_flat026 : CoefficientMerge.Poly := [(nat_lit 448, Int.ofNat (nat_lit 6391196200)), (nat_lit 449, Int.ofNat (nat_lit 6822409800)), (nat_lit 457, Int.ofNat (nat_lit 2336973120))]
theorem block005_data_flat026_step : block005_data_flat026 = (CoefficientMerge.fastMerge block005_data_flat022 block005_data_flat025) := by decide +kernel
theorem block005_data_flat026_original : block005_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6391196200 : Int) atom0347Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6822409800 : Int) atom0348Coded) (CoefficientMerge.scale (2336973120 : Int) atom0349Coded))) := by
  rw [block005_data_flat026_step, block005_data_flat022_original, block005_data_flat025_original]
def block005_data_flat027 : CoefficientMerge.Poly := [(nat_lit 446, Int.ofNat (nat_lit 6098833080)), (nat_lit 447, Int.ofNat (nat_lit 5959982600)), (nat_lit 448, Int.ofNat (nat_lit 6391196200)), (nat_lit 449, Int.ofNat (nat_lit 6822409800)), (nat_lit 457, Int.ofNat (nat_lit 2336973120))]
theorem block005_data_flat027_step : block005_data_flat027 = (CoefficientMerge.fastMerge block005_data_flat021 block005_data_flat026) := by decide +kernel
theorem block005_data_flat027_original : block005_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6098833080 : Int) atom0345Coded) (CoefficientMerge.scale (5959982600 : Int) atom0346Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6391196200 : Int) atom0347Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6822409800 : Int) atom0348Coded) (CoefficientMerge.scale (2336973120 : Int) atom0349Coded)))) := by
  rw [block005_data_flat027_step, block005_data_flat021_original, block005_data_flat026_original]
def block005_data_flat028 : CoefficientMerge.Poly := [(nat_lit 458, Int.ofNat (nat_lit 3943380288))]
theorem block005_data_flat028_step : block005_data_flat028 = (CoefficientMerge.scale (3943380288 : Int) atom0350Coded) := by decide +kernel
theorem block005_data_flat028_original : block005_data_flat028 = (CoefficientMerge.scale (3943380288 : Int) atom0350Coded) := by
  rw [block005_data_flat028_step]
def block005_data_flat029 : CoefficientMerge.Poly := [(nat_lit 459, Int.ofNat (nat_lit 3334043520))]
theorem block005_data_flat029_step : block005_data_flat029 = (CoefficientMerge.scale (3334043520 : Int) atom0351Coded) := by decide +kernel
theorem block005_data_flat029_original : block005_data_flat029 = (CoefficientMerge.scale (3334043520 : Int) atom0351Coded) := by
  rw [block005_data_flat029_step]
def block005_data_flat030 : CoefficientMerge.Poly := [(nat_lit 458, Int.ofNat (nat_lit 3943380288)), (nat_lit 459, Int.ofNat (nat_lit 3334043520))]
theorem block005_data_flat030_step : block005_data_flat030 = (CoefficientMerge.fastMerge block005_data_flat028 block005_data_flat029) := by decide +kernel
theorem block005_data_flat030_original : block005_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3943380288 : Int) atom0350Coded) (CoefficientMerge.scale (3334043520 : Int) atom0351Coded)) := by
  rw [block005_data_flat030_step, block005_data_flat028_original, block005_data_flat029_original]
def block005_data_flat031 : CoefficientMerge.Poly := [(nat_lit 460, Int.ofNat (nat_lit 3358235520))]
theorem block005_data_flat031_step : block005_data_flat031 = (CoefficientMerge.scale (3358235520 : Int) atom0352Coded) := by decide +kernel
theorem block005_data_flat031_original : block005_data_flat031 = (CoefficientMerge.scale (3358235520 : Int) atom0352Coded) := by
  rw [block005_data_flat031_step]
def block005_data_flat032 : CoefficientMerge.Poly := [(nat_lit 461, Int.ofNat (nat_lit 3558392960))]
theorem block005_data_flat032_step : block005_data_flat032 = (CoefficientMerge.scale (3558392960 : Int) atom0353Coded) := by decide +kernel
theorem block005_data_flat032_original : block005_data_flat032 = (CoefficientMerge.scale (3558392960 : Int) atom0353Coded) := by
  rw [block005_data_flat032_step]
def block005_data_flat033 : CoefficientMerge.Poly := [(nat_lit 462, Int.ofNat (nat_lit 6159605760))]
theorem block005_data_flat033_step : block005_data_flat033 = (CoefficientMerge.scale (6159605760 : Int) atom0354Coded) := by decide +kernel
theorem block005_data_flat033_original : block005_data_flat033 = (CoefficientMerge.scale (6159605760 : Int) atom0354Coded) := by
  rw [block005_data_flat033_step]
def block005_data_flat034 : CoefficientMerge.Poly := [(nat_lit 461, Int.ofNat (nat_lit 3558392960)), (nat_lit 462, Int.ofNat (nat_lit 6159605760))]
theorem block005_data_flat034_step : block005_data_flat034 = (CoefficientMerge.fastMerge block005_data_flat032 block005_data_flat033) := by decide +kernel
theorem block005_data_flat034_original : block005_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3558392960 : Int) atom0353Coded) (CoefficientMerge.scale (6159605760 : Int) atom0354Coded)) := by
  rw [block005_data_flat034_step, block005_data_flat032_original, block005_data_flat033_original]
def block005_data_flat035 : CoefficientMerge.Poly := [(nat_lit 460, Int.ofNat (nat_lit 3358235520)), (nat_lit 461, Int.ofNat (nat_lit 3558392960)), (nat_lit 462, Int.ofNat (nat_lit 6159605760))]
theorem block005_data_flat035_step : block005_data_flat035 = (CoefficientMerge.fastMerge block005_data_flat031 block005_data_flat034) := by decide +kernel
theorem block005_data_flat035_original : block005_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3358235520 : Int) atom0352Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3558392960 : Int) atom0353Coded) (CoefficientMerge.scale (6159605760 : Int) atom0354Coded))) := by
  rw [block005_data_flat035_step, block005_data_flat031_original, block005_data_flat034_original]
def block005_data_flat036 : CoefficientMerge.Poly := [(nat_lit 458, Int.ofNat (nat_lit 3943380288)), (nat_lit 459, Int.ofNat (nat_lit 3334043520)), (nat_lit 460, Int.ofNat (nat_lit 3358235520)), (nat_lit 461, Int.ofNat (nat_lit 3558392960)), (nat_lit 462, Int.ofNat (nat_lit 6159605760))]
theorem block005_data_flat036_step : block005_data_flat036 = (CoefficientMerge.fastMerge block005_data_flat030 block005_data_flat035) := by decide +kernel
theorem block005_data_flat036_original : block005_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3943380288 : Int) atom0350Coded) (CoefficientMerge.scale (3334043520 : Int) atom0351Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3358235520 : Int) atom0352Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3558392960 : Int) atom0353Coded) (CoefficientMerge.scale (6159605760 : Int) atom0354Coded)))) := by
  rw [block005_data_flat036_step, block005_data_flat030_original, block005_data_flat035_original]
def block005_data_flat037 : CoefficientMerge.Poly := [(nat_lit 446, Int.ofNat (nat_lit 6098833080)), (nat_lit 447, Int.ofNat (nat_lit 5959982600)), (nat_lit 448, Int.ofNat (nat_lit 6391196200)), (nat_lit 449, Int.ofNat (nat_lit 6822409800)), (nat_lit 457, Int.ofNat (nat_lit 2336973120)), (nat_lit 458, Int.ofNat (nat_lit 3943380288)), (nat_lit 459, Int.ofNat (nat_lit 3334043520)), (nat_lit 460, Int.ofNat (nat_lit 3358235520)), (nat_lit 461, Int.ofNat (nat_lit 3558392960)), (nat_lit 462, Int.ofNat (nat_lit 6159605760))]
theorem block005_data_flat037_step : block005_data_flat037 = (CoefficientMerge.fastMerge block005_data_flat027 block005_data_flat036) := by decide +kernel
theorem block005_data_flat037_original : block005_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6098833080 : Int) atom0345Coded) (CoefficientMerge.scale (5959982600 : Int) atom0346Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6391196200 : Int) atom0347Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6822409800 : Int) atom0348Coded) (CoefficientMerge.scale (2336973120 : Int) atom0349Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3943380288 : Int) atom0350Coded) (CoefficientMerge.scale (3334043520 : Int) atom0351Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3358235520 : Int) atom0352Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3558392960 : Int) atom0353Coded) (CoefficientMerge.scale (6159605760 : Int) atom0354Coded))))) := by
  rw [block005_data_flat037_step, block005_data_flat027_original, block005_data_flat036_original]
def block005_data_flat038 : CoefficientMerge.Poly := [(nat_lit 430, Int.ofNat (nat_lit 5898088840)), (nat_lit 431, Int.ofNat (nat_lit 6018711240)), (nat_lit 438, Int.ofNat (nat_lit 2000907360)), (nat_lit 439, Int.ofNat (nat_lit 3212404128)), (nat_lit 440, Int.ofNat (nat_lit 2905871040)), (nat_lit 441, Int.ofNat (nat_lit 2903290560)), (nat_lit 442, Int.ofNat (nat_lit 2951029440)), (nat_lit 443, Int.ofNat (nat_lit 3174733760)), (nat_lit 444, Int.ofNat (nat_lit 5883494400)), (nat_lit 445, Int.ofNat (nat_lit 4456174040)), (nat_lit 446, Int.ofNat (nat_lit 6098833080)), (nat_lit 447, Int.ofNat (nat_lit 5959982600)), (nat_lit 448, Int.ofNat (nat_lit 6391196200)), (nat_lit 449, Int.ofNat (nat_lit 6822409800)), (nat_lit 457, Int.ofNat (nat_lit 2336973120)), (nat_lit 458, Int.ofNat (nat_lit 3943380288)), (nat_lit 459, Int.ofNat (nat_lit 3334043520)), (nat_lit 460, Int.ofNat (nat_lit 3358235520)), (nat_lit 461, Int.ofNat (nat_lit 3558392960)), (nat_lit 462, Int.ofNat (nat_lit 6159605760))]
theorem block005_data_flat038_step : block005_data_flat038 = (CoefficientMerge.fastMerge block005_data_flat018 block005_data_flat037) := by decide +kernel
theorem block005_data_flat038_original : block005_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5898088840 : Int) atom0335Coded) (CoefficientMerge.scale (6018711240 : Int) atom0336Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2000907360 : Int) atom0337Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3212404128 : Int) atom0338Coded) (CoefficientMerge.scale (2905871040 : Int) atom0339Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2903290560 : Int) atom0340Coded) (CoefficientMerge.scale (2951029440 : Int) atom0341Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3174733760 : Int) atom0342Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5883494400 : Int) atom0343Coded) (CoefficientMerge.scale (4456174040 : Int) atom0344Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6098833080 : Int) atom0345Coded) (CoefficientMerge.scale (5959982600 : Int) atom0346Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6391196200 : Int) atom0347Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6822409800 : Int) atom0348Coded) (CoefficientMerge.scale (2336973120 : Int) atom0349Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3943380288 : Int) atom0350Coded) (CoefficientMerge.scale (3334043520 : Int) atom0351Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3358235520 : Int) atom0352Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3558392960 : Int) atom0353Coded) (CoefficientMerge.scale (6159605760 : Int) atom0354Coded)))))) := by
  rw [block005_data_flat038_step, block005_data_flat018_original, block005_data_flat037_original]
def block005_data_flat039 : CoefficientMerge.Poly := [(nat_lit 463, Int.ofNat (nat_lit 4881594320))]
theorem block005_data_flat039_step : block005_data_flat039 = (CoefficientMerge.scale (4881594320 : Int) atom0355Coded) := by decide +kernel
theorem block005_data_flat039_original : block005_data_flat039 = (CoefficientMerge.scale (4881594320 : Int) atom0355Coded) := by
  rw [block005_data_flat039_step]
def block005_data_flat040 : CoefficientMerge.Poly := [(nat_lit 464, Int.ofNat (nat_lit 6576221880))]
theorem block005_data_flat040_step : block005_data_flat040 = (CoefficientMerge.scale (6576221880 : Int) atom0356Coded) := by decide +kernel
theorem block005_data_flat040_original : block005_data_flat040 = (CoefficientMerge.scale (6576221880 : Int) atom0356Coded) := by
  rw [block005_data_flat040_step]
def block005_data_flat041 : CoefficientMerge.Poly := [(nat_lit 463, Int.ofNat (nat_lit 4881594320)), (nat_lit 464, Int.ofNat (nat_lit 6576221880))]
theorem block005_data_flat041_step : block005_data_flat041 = (CoefficientMerge.fastMerge block005_data_flat039 block005_data_flat040) := by decide +kernel
theorem block005_data_flat041_original : block005_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4881594320 : Int) atom0355Coded) (CoefficientMerge.scale (6576221880 : Int) atom0356Coded)) := by
  rw [block005_data_flat041_step, block005_data_flat039_original, block005_data_flat040_original]
def block005_data_flat042 : CoefficientMerge.Poly := [(nat_lit 465, Int.ofNat (nat_lit 6516018800))]
theorem block005_data_flat042_step : block005_data_flat042 = (CoefficientMerge.scale (6516018800 : Int) atom0357Coded) := by decide +kernel
theorem block005_data_flat042_original : block005_data_flat042 = (CoefficientMerge.scale (6516018800 : Int) atom0357Coded) := by
  rw [block005_data_flat042_step]
def block005_data_flat043 : CoefficientMerge.Poly := [(nat_lit 466, Int.ofNat (nat_lit 7042158640))]
theorem block005_data_flat043_step : block005_data_flat043 = (CoefficientMerge.scale (7042158640 : Int) atom0358Coded) := by decide +kernel
theorem block005_data_flat043_original : block005_data_flat043 = (CoefficientMerge.scale (7042158640 : Int) atom0358Coded) := by
  rw [block005_data_flat043_step]
def block005_data_flat044 : CoefficientMerge.Poly := [(nat_lit 467, Int.ofNat (nat_lit 7568298480))]
theorem block005_data_flat044_step : block005_data_flat044 = (CoefficientMerge.scale (7568298480 : Int) atom0359Coded) := by decide +kernel
theorem block005_data_flat044_original : block005_data_flat044 = (CoefficientMerge.scale (7568298480 : Int) atom0359Coded) := by
  rw [block005_data_flat044_step]
def block005_data_flat045 : CoefficientMerge.Poly := [(nat_lit 466, Int.ofNat (nat_lit 7042158640)), (nat_lit 467, Int.ofNat (nat_lit 7568298480))]
theorem block005_data_flat045_step : block005_data_flat045 = (CoefficientMerge.fastMerge block005_data_flat043 block005_data_flat044) := by decide +kernel
theorem block005_data_flat045_original : block005_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7042158640 : Int) atom0358Coded) (CoefficientMerge.scale (7568298480 : Int) atom0359Coded)) := by
  rw [block005_data_flat045_step, block005_data_flat043_original, block005_data_flat044_original]
def block005_data_flat046 : CoefficientMerge.Poly := [(nat_lit 465, Int.ofNat (nat_lit 6516018800)), (nat_lit 466, Int.ofNat (nat_lit 7042158640)), (nat_lit 467, Int.ofNat (nat_lit 7568298480))]
theorem block005_data_flat046_step : block005_data_flat046 = (CoefficientMerge.fastMerge block005_data_flat042 block005_data_flat045) := by decide +kernel
theorem block005_data_flat046_original : block005_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6516018800 : Int) atom0357Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7042158640 : Int) atom0358Coded) (CoefficientMerge.scale (7568298480 : Int) atom0359Coded))) := by
  rw [block005_data_flat046_step, block005_data_flat042_original, block005_data_flat045_original]
def block005_data_flat047 : CoefficientMerge.Poly := [(nat_lit 463, Int.ofNat (nat_lit 4881594320)), (nat_lit 464, Int.ofNat (nat_lit 6576221880)), (nat_lit 465, Int.ofNat (nat_lit 6516018800)), (nat_lit 466, Int.ofNat (nat_lit 7042158640)), (nat_lit 467, Int.ofNat (nat_lit 7568298480))]
theorem block005_data_flat047_step : block005_data_flat047 = (CoefficientMerge.fastMerge block005_data_flat041 block005_data_flat046) := by decide +kernel
theorem block005_data_flat047_original : block005_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4881594320 : Int) atom0355Coded) (CoefficientMerge.scale (6576221880 : Int) atom0356Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6516018800 : Int) atom0357Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7042158640 : Int) atom0358Coded) (CoefficientMerge.scale (7568298480 : Int) atom0359Coded)))) := by
  rw [block005_data_flat047_step, block005_data_flat041_original, block005_data_flat046_original]
def block005_data_flat048 : CoefficientMerge.Poly := [(nat_lit 476, Int.ofNat (nat_lit 2731883520))]
theorem block005_data_flat048_step : block005_data_flat048 = (CoefficientMerge.scale (2731883520 : Int) atom0360Coded) := by decide +kernel
theorem block005_data_flat048_original : block005_data_flat048 = (CoefficientMerge.scale (2731883520 : Int) atom0360Coded) := by
  rw [block005_data_flat048_step]
def block005_data_flat049 : CoefficientMerge.Poly := [(nat_lit 477, Int.ofNat (nat_lit 4672629120))]
theorem block005_data_flat049_step : block005_data_flat049 = (CoefficientMerge.scale (4672629120 : Int) atom0361Coded) := by decide +kernel
theorem block005_data_flat049_original : block005_data_flat049 = (CoefficientMerge.scale (4672629120 : Int) atom0361Coded) := by
  rw [block005_data_flat049_step]
def block005_data_flat050 : CoefficientMerge.Poly := [(nat_lit 476, Int.ofNat (nat_lit 2731883520)), (nat_lit 477, Int.ofNat (nat_lit 4672629120))]
theorem block005_data_flat050_step : block005_data_flat050 = (CoefficientMerge.fastMerge block005_data_flat048 block005_data_flat049) := by decide +kernel
theorem block005_data_flat050_original : block005_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2731883520 : Int) atom0360Coded) (CoefficientMerge.scale (4672629120 : Int) atom0361Coded)) := by
  rw [block005_data_flat050_step, block005_data_flat048_original, block005_data_flat049_original]
def block005_data_flat051 : CoefficientMerge.Poly := [(nat_lit 478, Int.ofNat (nat_lit 3937045632))]
theorem block005_data_flat051_step : block005_data_flat051 = (CoefficientMerge.scale (3937045632 : Int) atom0362Coded) := by decide +kernel
theorem block005_data_flat051_original : block005_data_flat051 = (CoefficientMerge.scale (3937045632 : Int) atom0362Coded) := by
  rw [block005_data_flat051_step]
def block005_data_flat052 : CoefficientMerge.Poly := [(nat_lit 479, Int.ofNat (nat_lit 4045591040))]
theorem block005_data_flat052_step : block005_data_flat052 = (CoefficientMerge.scale (4045591040 : Int) atom0363Coded) := by decide +kernel
theorem block005_data_flat052_original : block005_data_flat052 = (CoefficientMerge.scale (4045591040 : Int) atom0363Coded) := by
  rw [block005_data_flat052_step]
def block005_data_flat053 : CoefficientMerge.Poly := [(nat_lit 480, Int.ofNat (nat_lit 6538183680))]
theorem block005_data_flat053_step : block005_data_flat053 = (CoefficientMerge.scale (6538183680 : Int) atom0364Coded) := by decide +kernel
theorem block005_data_flat053_original : block005_data_flat053 = (CoefficientMerge.scale (6538183680 : Int) atom0364Coded) := by
  rw [block005_data_flat053_step]
def block005_data_flat054 : CoefficientMerge.Poly := [(nat_lit 479, Int.ofNat (nat_lit 4045591040)), (nat_lit 480, Int.ofNat (nat_lit 6538183680))]
theorem block005_data_flat054_step : block005_data_flat054 = (CoefficientMerge.fastMerge block005_data_flat052 block005_data_flat053) := by decide +kernel
theorem block005_data_flat054_original : block005_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4045591040 : Int) atom0363Coded) (CoefficientMerge.scale (6538183680 : Int) atom0364Coded)) := by
  rw [block005_data_flat054_step, block005_data_flat052_original, block005_data_flat053_original]
def block005_data_flat055 : CoefficientMerge.Poly := [(nat_lit 478, Int.ofNat (nat_lit 3937045632)), (nat_lit 479, Int.ofNat (nat_lit 4045591040)), (nat_lit 480, Int.ofNat (nat_lit 6538183680))]
theorem block005_data_flat055_step : block005_data_flat055 = (CoefficientMerge.fastMerge block005_data_flat051 block005_data_flat054) := by decide +kernel
theorem block005_data_flat055_original : block005_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3937045632 : Int) atom0362Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4045591040 : Int) atom0363Coded) (CoefficientMerge.scale (6538183680 : Int) atom0364Coded))) := by
  rw [block005_data_flat055_step, block005_data_flat051_original, block005_data_flat054_original]
def block005_data_flat056 : CoefficientMerge.Poly := [(nat_lit 476, Int.ofNat (nat_lit 2731883520)), (nat_lit 477, Int.ofNat (nat_lit 4672629120)), (nat_lit 478, Int.ofNat (nat_lit 3937045632)), (nat_lit 479, Int.ofNat (nat_lit 4045591040)), (nat_lit 480, Int.ofNat (nat_lit 6538183680))]
theorem block005_data_flat056_step : block005_data_flat056 = (CoefficientMerge.fastMerge block005_data_flat050 block005_data_flat055) := by decide +kernel
theorem block005_data_flat056_original : block005_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2731883520 : Int) atom0360Coded) (CoefficientMerge.scale (4672629120 : Int) atom0361Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3937045632 : Int) atom0362Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4045591040 : Int) atom0363Coded) (CoefficientMerge.scale (6538183680 : Int) atom0364Coded)))) := by
  rw [block005_data_flat056_step, block005_data_flat050_original, block005_data_flat055_original]
def block005_data_flat057 : CoefficientMerge.Poly := [(nat_lit 463, Int.ofNat (nat_lit 4881594320)), (nat_lit 464, Int.ofNat (nat_lit 6576221880)), (nat_lit 465, Int.ofNat (nat_lit 6516018800)), (nat_lit 466, Int.ofNat (nat_lit 7042158640)), (nat_lit 467, Int.ofNat (nat_lit 7568298480)), (nat_lit 476, Int.ofNat (nat_lit 2731883520)), (nat_lit 477, Int.ofNat (nat_lit 4672629120)), (nat_lit 478, Int.ofNat (nat_lit 3937045632)), (nat_lit 479, Int.ofNat (nat_lit 4045591040)), (nat_lit 480, Int.ofNat (nat_lit 6538183680))]
theorem block005_data_flat057_step : block005_data_flat057 = (CoefficientMerge.fastMerge block005_data_flat047 block005_data_flat056) := by decide +kernel
theorem block005_data_flat057_original : block005_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4881594320 : Int) atom0355Coded) (CoefficientMerge.scale (6576221880 : Int) atom0356Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6516018800 : Int) atom0357Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7042158640 : Int) atom0358Coded) (CoefficientMerge.scale (7568298480 : Int) atom0359Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2731883520 : Int) atom0360Coded) (CoefficientMerge.scale (4672629120 : Int) atom0361Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3937045632 : Int) atom0362Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4045591040 : Int) atom0363Coded) (CoefficientMerge.scale (6538183680 : Int) atom0364Coded))))) := by
  rw [block005_data_flat057_step, block005_data_flat047_original, block005_data_flat056_original]
def block005_data_flat058 : CoefficientMerge.Poly := [(nat_lit 481, Int.ofNat (nat_lit 5324168960))]
theorem block005_data_flat058_step : block005_data_flat058 = (CoefficientMerge.scale (5324168960 : Int) atom0365Coded) := by decide +kernel
theorem block005_data_flat058_original : block005_data_flat058 = (CoefficientMerge.scale (5324168960 : Int) atom0365Coded) := by
  rw [block005_data_flat058_step]
def block005_data_flat059 : CoefficientMerge.Poly := [(nat_lit 482, Int.ofNat (nat_lit 7156077240))]
theorem block005_data_flat059_step : block005_data_flat059 = (CoefficientMerge.scale (7156077240 : Int) atom0366Coded) := by decide +kernel
theorem block005_data_flat059_original : block005_data_flat059 = (CoefficientMerge.scale (7156077240 : Int) atom0366Coded) := by
  rw [block005_data_flat059_step]
def block005_data_flat060 : CoefficientMerge.Poly := [(nat_lit 481, Int.ofNat (nat_lit 5324168960)), (nat_lit 482, Int.ofNat (nat_lit 7156077240))]
theorem block005_data_flat060_step : block005_data_flat060 = (CoefficientMerge.fastMerge block005_data_flat058 block005_data_flat059) := by decide +kernel
theorem block005_data_flat060_original : block005_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5324168960 : Int) atom0365Coded) (CoefficientMerge.scale (7156077240 : Int) atom0366Coded)) := by
  rw [block005_data_flat060_step, block005_data_flat058_original, block005_data_flat059_original]
def block005_data_flat061 : CoefficientMerge.Poly := [(nat_lit 483, Int.ofNat (nat_lit 6966759680))]
theorem block005_data_flat061_step : block005_data_flat061 = (CoefficientMerge.scale (6966759680 : Int) atom0367Coded) := by decide +kernel
theorem block005_data_flat061_original : block005_data_flat061 = (CoefficientMerge.scale (6966759680 : Int) atom0367Coded) := by
  rw [block005_data_flat061_step]
def block005_data_flat062 : CoefficientMerge.Poly := [(nat_lit 484, Int.ofNat (nat_lit 7463345920))]
theorem block005_data_flat062_step : block005_data_flat062 = (CoefficientMerge.scale (7463345920 : Int) atom0368Coded) := by decide +kernel
theorem block005_data_flat062_original : block005_data_flat062 = (CoefficientMerge.scale (7463345920 : Int) atom0368Coded) := by
  rw [block005_data_flat062_step]
def block005_data_flat063 : CoefficientMerge.Poly := [(nat_lit 485, Int.ofNat (nat_lit 8011165440))]
theorem block005_data_flat063_step : block005_data_flat063 = (CoefficientMerge.scale (8011165440 : Int) atom0369Coded) := by decide +kernel
theorem block005_data_flat063_original : block005_data_flat063 = (CoefficientMerge.scale (8011165440 : Int) atom0369Coded) := by
  rw [block005_data_flat063_step]
def block005_data_flat064 : CoefficientMerge.Poly := [(nat_lit 484, Int.ofNat (nat_lit 7463345920)), (nat_lit 485, Int.ofNat (nat_lit 8011165440))]
theorem block005_data_flat064_step : block005_data_flat064 = (CoefficientMerge.fastMerge block005_data_flat062 block005_data_flat063) := by decide +kernel
theorem block005_data_flat064_original : block005_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7463345920 : Int) atom0368Coded) (CoefficientMerge.scale (8011165440 : Int) atom0369Coded)) := by
  rw [block005_data_flat064_step, block005_data_flat062_original, block005_data_flat063_original]
def block005_data_flat065 : CoefficientMerge.Poly := [(nat_lit 483, Int.ofNat (nat_lit 6966759680)), (nat_lit 484, Int.ofNat (nat_lit 7463345920)), (nat_lit 485, Int.ofNat (nat_lit 8011165440))]
theorem block005_data_flat065_step : block005_data_flat065 = (CoefficientMerge.fastMerge block005_data_flat061 block005_data_flat064) := by decide +kernel
theorem block005_data_flat065_original : block005_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6966759680 : Int) atom0367Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7463345920 : Int) atom0368Coded) (CoefficientMerge.scale (8011165440 : Int) atom0369Coded))) := by
  rw [block005_data_flat065_step, block005_data_flat061_original, block005_data_flat064_original]
def block005_data_flat066 : CoefficientMerge.Poly := [(nat_lit 481, Int.ofNat (nat_lit 5324168960)), (nat_lit 482, Int.ofNat (nat_lit 7156077240)), (nat_lit 483, Int.ofNat (nat_lit 6966759680)), (nat_lit 484, Int.ofNat (nat_lit 7463345920)), (nat_lit 485, Int.ofNat (nat_lit 8011165440))]
theorem block005_data_flat066_step : block005_data_flat066 = (CoefficientMerge.fastMerge block005_data_flat060 block005_data_flat065) := by decide +kernel
theorem block005_data_flat066_original : block005_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5324168960 : Int) atom0365Coded) (CoefficientMerge.scale (7156077240 : Int) atom0366Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6966759680 : Int) atom0367Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7463345920 : Int) atom0368Coded) (CoefficientMerge.scale (8011165440 : Int) atom0369Coded)))) := by
  rw [block005_data_flat066_step, block005_data_flat060_original, block005_data_flat065_original]
def block005_data_flat067 : CoefficientMerge.Poly := [(nat_lit 495, Int.ofNat (nat_lit 3038632320))]
theorem block005_data_flat067_step : block005_data_flat067 = (CoefficientMerge.scale (3038632320 : Int) atom0370Coded) := by decide +kernel
theorem block005_data_flat067_original : block005_data_flat067 = (CoefficientMerge.scale (3038632320 : Int) atom0370Coded) := by
  rw [block005_data_flat067_step]
def block005_data_flat068 : CoefficientMerge.Poly := [(nat_lit 496, Int.ofNat (nat_lit 5210772480))]
theorem block005_data_flat068_step : block005_data_flat068 = (CoefficientMerge.scale (5210772480 : Int) atom0371Coded) := by decide +kernel
theorem block005_data_flat068_original : block005_data_flat068 = (CoefficientMerge.scale (5210772480 : Int) atom0371Coded) := by
  rw [block005_data_flat068_step]
def block005_data_flat069 : CoefficientMerge.Poly := [(nat_lit 495, Int.ofNat (nat_lit 3038632320)), (nat_lit 496, Int.ofNat (nat_lit 5210772480))]
theorem block005_data_flat069_step : block005_data_flat069 = (CoefficientMerge.fastMerge block005_data_flat067 block005_data_flat068) := by decide +kernel
theorem block005_data_flat069_original : block005_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3038632320 : Int) atom0370Coded) (CoefficientMerge.scale (5210772480 : Int) atom0371Coded)) := by
  rw [block005_data_flat069_step, block005_data_flat067_original, block005_data_flat068_original]
def block005_data_flat070 : CoefficientMerge.Poly := [(nat_lit 497, Int.ofNat (nat_lit 4660776320))]
theorem block005_data_flat070_step : block005_data_flat070 = (CoefficientMerge.scale (4660776320 : Int) atom0372Coded) := by decide +kernel
theorem block005_data_flat070_original : block005_data_flat070 = (CoefficientMerge.scale (4660776320 : Int) atom0372Coded) := by
  rw [block005_data_flat070_step]
def block005_data_flat071 : CoefficientMerge.Poly := [(nat_lit 498, Int.ofNat (nat_lit 6904803360))]
theorem block005_data_flat071_step : block005_data_flat071 = (CoefficientMerge.scale (6904803360 : Int) atom0373Coded) := by decide +kernel
theorem block005_data_flat071_original : block005_data_flat071 = (CoefficientMerge.scale (6904803360 : Int) atom0373Coded) := by
  rw [block005_data_flat071_step]
def block005_data_flat072 : CoefficientMerge.Poly := [(nat_lit 499, Int.ofNat (nat_lit 5640737120))]
theorem block005_data_flat072_step : block005_data_flat072 = (CoefficientMerge.scale (5640737120 : Int) atom0374Coded) := by decide +kernel
theorem block005_data_flat072_original : block005_data_flat072 = (CoefficientMerge.scale (5640737120 : Int) atom0374Coded) := by
  rw [block005_data_flat072_step]
def block005_data_flat073 : CoefficientMerge.Poly := [(nat_lit 498, Int.ofNat (nat_lit 6904803360)), (nat_lit 499, Int.ofNat (nat_lit 5640737120))]
theorem block005_data_flat073_step : block005_data_flat073 = (CoefficientMerge.fastMerge block005_data_flat071 block005_data_flat072) := by decide +kernel
theorem block005_data_flat073_original : block005_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6904803360 : Int) atom0373Coded) (CoefficientMerge.scale (5640737120 : Int) atom0374Coded)) := by
  rw [block005_data_flat073_step, block005_data_flat071_original, block005_data_flat072_original]
def block005_data_flat074 : CoefficientMerge.Poly := [(nat_lit 497, Int.ofNat (nat_lit 4660776320)), (nat_lit 498, Int.ofNat (nat_lit 6904803360)), (nat_lit 499, Int.ofNat (nat_lit 5640737120))]
theorem block005_data_flat074_step : block005_data_flat074 = (CoefficientMerge.fastMerge block005_data_flat070 block005_data_flat073) := by decide +kernel
theorem block005_data_flat074_original : block005_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4660776320 : Int) atom0372Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6904803360 : Int) atom0373Coded) (CoefficientMerge.scale (5640737120 : Int) atom0374Coded))) := by
  rw [block005_data_flat074_step, block005_data_flat070_original, block005_data_flat073_original]
def block005_data_flat075 : CoefficientMerge.Poly := [(nat_lit 495, Int.ofNat (nat_lit 3038632320)), (nat_lit 496, Int.ofNat (nat_lit 5210772480)), (nat_lit 497, Int.ofNat (nat_lit 4660776320)), (nat_lit 498, Int.ofNat (nat_lit 6904803360)), (nat_lit 499, Int.ofNat (nat_lit 5640737120))]
theorem block005_data_flat075_step : block005_data_flat075 = (CoefficientMerge.fastMerge block005_data_flat069 block005_data_flat074) := by decide +kernel
theorem block005_data_flat075_original : block005_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3038632320 : Int) atom0370Coded) (CoefficientMerge.scale (5210772480 : Int) atom0371Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4660776320 : Int) atom0372Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6904803360 : Int) atom0373Coded) (CoefficientMerge.scale (5640737120 : Int) atom0374Coded)))) := by
  rw [block005_data_flat075_step, block005_data_flat069_original, block005_data_flat074_original]
def block005_data_flat076 : CoefficientMerge.Poly := [(nat_lit 481, Int.ofNat (nat_lit 5324168960)), (nat_lit 482, Int.ofNat (nat_lit 7156077240)), (nat_lit 483, Int.ofNat (nat_lit 6966759680)), (nat_lit 484, Int.ofNat (nat_lit 7463345920)), (nat_lit 485, Int.ofNat (nat_lit 8011165440)), (nat_lit 495, Int.ofNat (nat_lit 3038632320)), (nat_lit 496, Int.ofNat (nat_lit 5210772480)), (nat_lit 497, Int.ofNat (nat_lit 4660776320)), (nat_lit 498, Int.ofNat (nat_lit 6904803360)), (nat_lit 499, Int.ofNat (nat_lit 5640737120))]
theorem block005_data_flat076_step : block005_data_flat076 = (CoefficientMerge.fastMerge block005_data_flat066 block005_data_flat075) := by decide +kernel
theorem block005_data_flat076_original : block005_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5324168960 : Int) atom0365Coded) (CoefficientMerge.scale (7156077240 : Int) atom0366Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6966759680 : Int) atom0367Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7463345920 : Int) atom0368Coded) (CoefficientMerge.scale (8011165440 : Int) atom0369Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3038632320 : Int) atom0370Coded) (CoefficientMerge.scale (5210772480 : Int) atom0371Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4660776320 : Int) atom0372Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6904803360 : Int) atom0373Coded) (CoefficientMerge.scale (5640737120 : Int) atom0374Coded))))) := by
  rw [block005_data_flat076_step, block005_data_flat066_original, block005_data_flat075_original]
def block005_data_flat077 : CoefficientMerge.Poly := [(nat_lit 463, Int.ofNat (nat_lit 4881594320)), (nat_lit 464, Int.ofNat (nat_lit 6576221880)), (nat_lit 465, Int.ofNat (nat_lit 6516018800)), (nat_lit 466, Int.ofNat (nat_lit 7042158640)), (nat_lit 467, Int.ofNat (nat_lit 7568298480)), (nat_lit 476, Int.ofNat (nat_lit 2731883520)), (nat_lit 477, Int.ofNat (nat_lit 4672629120)), (nat_lit 478, Int.ofNat (nat_lit 3937045632)), (nat_lit 479, Int.ofNat (nat_lit 4045591040)), (nat_lit 480, Int.ofNat (nat_lit 6538183680)), (nat_lit 481, Int.ofNat (nat_lit 5324168960)), (nat_lit 482, Int.ofNat (nat_lit 7156077240)), (nat_lit 483, Int.ofNat (nat_lit 6966759680)), (nat_lit 484, Int.ofNat (nat_lit 7463345920)), (nat_lit 485, Int.ofNat (nat_lit 8011165440)), (nat_lit 495, Int.ofNat (nat_lit 3038632320)), (nat_lit 496, Int.ofNat (nat_lit 5210772480)), (nat_lit 497, Int.ofNat (nat_lit 4660776320)), (nat_lit 498, Int.ofNat (nat_lit 6904803360)), (nat_lit 499, Int.ofNat (nat_lit 5640737120))]
theorem block005_data_flat077_step : block005_data_flat077 = (CoefficientMerge.fastMerge block005_data_flat057 block005_data_flat076) := by decide +kernel
theorem block005_data_flat077_original : block005_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4881594320 : Int) atom0355Coded) (CoefficientMerge.scale (6576221880 : Int) atom0356Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6516018800 : Int) atom0357Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7042158640 : Int) atom0358Coded) (CoefficientMerge.scale (7568298480 : Int) atom0359Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2731883520 : Int) atom0360Coded) (CoefficientMerge.scale (4672629120 : Int) atom0361Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3937045632 : Int) atom0362Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4045591040 : Int) atom0363Coded) (CoefficientMerge.scale (6538183680 : Int) atom0364Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5324168960 : Int) atom0365Coded) (CoefficientMerge.scale (7156077240 : Int) atom0366Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6966759680 : Int) atom0367Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7463345920 : Int) atom0368Coded) (CoefficientMerge.scale (8011165440 : Int) atom0369Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3038632320 : Int) atom0370Coded) (CoefficientMerge.scale (5210772480 : Int) atom0371Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4660776320 : Int) atom0372Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6904803360 : Int) atom0373Coded) (CoefficientMerge.scale (5640737120 : Int) atom0374Coded)))))) := by
  rw [block005_data_flat077_step, block005_data_flat057_original, block005_data_flat076_original]
def block005_data_flat078 : CoefficientMerge.Poly := [(nat_lit 430, Int.ofNat (nat_lit 5898088840)), (nat_lit 431, Int.ofNat (nat_lit 6018711240)), (nat_lit 438, Int.ofNat (nat_lit 2000907360)), (nat_lit 439, Int.ofNat (nat_lit 3212404128)), (nat_lit 440, Int.ofNat (nat_lit 2905871040)), (nat_lit 441, Int.ofNat (nat_lit 2903290560)), (nat_lit 442, Int.ofNat (nat_lit 2951029440)), (nat_lit 443, Int.ofNat (nat_lit 3174733760)), (nat_lit 444, Int.ofNat (nat_lit 5883494400)), (nat_lit 445, Int.ofNat (nat_lit 4456174040)), (nat_lit 446, Int.ofNat (nat_lit 6098833080)), (nat_lit 447, Int.ofNat (nat_lit 5959982600)), (nat_lit 448, Int.ofNat (nat_lit 6391196200)), (nat_lit 449, Int.ofNat (nat_lit 6822409800)), (nat_lit 457, Int.ofNat (nat_lit 2336973120)), (nat_lit 458, Int.ofNat (nat_lit 3943380288)), (nat_lit 459, Int.ofNat (nat_lit 3334043520)), (nat_lit 460, Int.ofNat (nat_lit 3358235520)), (nat_lit 461, Int.ofNat (nat_lit 3558392960)), (nat_lit 462, Int.ofNat (nat_lit 6159605760)), (nat_lit 463, Int.ofNat (nat_lit 4881594320)), (nat_lit 464, Int.ofNat (nat_lit 6576221880)), (nat_lit 465, Int.ofNat (nat_lit 6516018800)), (nat_lit 466, Int.ofNat (nat_lit 7042158640)), (nat_lit 467, Int.ofNat (nat_lit 7568298480)), (nat_lit 476, Int.ofNat (nat_lit 2731883520)), (nat_lit 477, Int.ofNat (nat_lit 4672629120)), (nat_lit 478, Int.ofNat (nat_lit 3937045632)), (nat_lit 479, Int.ofNat (nat_lit 4045591040)), (nat_lit 480, Int.ofNat (nat_lit 6538183680)), (nat_lit 481, Int.ofNat (nat_lit 5324168960)), (nat_lit 482, Int.ofNat (nat_lit 7156077240)), (nat_lit 483, Int.ofNat (nat_lit 6966759680)), (nat_lit 484, Int.ofNat (nat_lit 7463345920)), (nat_lit 485, Int.ofNat (nat_lit 8011165440)), (nat_lit 495, Int.ofNat (nat_lit 3038632320)), (nat_lit 496, Int.ofNat (nat_lit 5210772480)), (nat_lit 497, Int.ofNat (nat_lit 4660776320)), (nat_lit 498, Int.ofNat (nat_lit 6904803360)), (nat_lit 499, Int.ofNat (nat_lit 5640737120))]
theorem block005_data_flat078_step : block005_data_flat078 = (CoefficientMerge.fastMerge block005_data_flat038 block005_data_flat077) := by decide +kernel
theorem block005_data_flat078_original : block005_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5898088840 : Int) atom0335Coded) (CoefficientMerge.scale (6018711240 : Int) atom0336Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2000907360 : Int) atom0337Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3212404128 : Int) atom0338Coded) (CoefficientMerge.scale (2905871040 : Int) atom0339Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2903290560 : Int) atom0340Coded) (CoefficientMerge.scale (2951029440 : Int) atom0341Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3174733760 : Int) atom0342Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5883494400 : Int) atom0343Coded) (CoefficientMerge.scale (4456174040 : Int) atom0344Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6098833080 : Int) atom0345Coded) (CoefficientMerge.scale (5959982600 : Int) atom0346Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6391196200 : Int) atom0347Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6822409800 : Int) atom0348Coded) (CoefficientMerge.scale (2336973120 : Int) atom0349Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3943380288 : Int) atom0350Coded) (CoefficientMerge.scale (3334043520 : Int) atom0351Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3358235520 : Int) atom0352Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3558392960 : Int) atom0353Coded) (CoefficientMerge.scale (6159605760 : Int) atom0354Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4881594320 : Int) atom0355Coded) (CoefficientMerge.scale (6576221880 : Int) atom0356Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6516018800 : Int) atom0357Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7042158640 : Int) atom0358Coded) (CoefficientMerge.scale (7568298480 : Int) atom0359Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2731883520 : Int) atom0360Coded) (CoefficientMerge.scale (4672629120 : Int) atom0361Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3937045632 : Int) atom0362Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4045591040 : Int) atom0363Coded) (CoefficientMerge.scale (6538183680 : Int) atom0364Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5324168960 : Int) atom0365Coded) (CoefficientMerge.scale (7156077240 : Int) atom0366Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6966759680 : Int) atom0367Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7463345920 : Int) atom0368Coded) (CoefficientMerge.scale (8011165440 : Int) atom0369Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3038632320 : Int) atom0370Coded) (CoefficientMerge.scale (5210772480 : Int) atom0371Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4660776320 : Int) atom0372Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6904803360 : Int) atom0373Coded) (CoefficientMerge.scale (5640737120 : Int) atom0374Coded))))))) := by
  rw [block005_data_flat078_step, block005_data_flat038_original, block005_data_flat077_original]
def block005_data_flat079 : CoefficientMerge.Poly := [(nat_lit 500, Int.ofNat (nat_lit 7615402680))]
theorem block005_data_flat079_step : block005_data_flat079 = (CoefficientMerge.scale (7615402680 : Int) atom0375Coded) := by decide +kernel
theorem block005_data_flat079_original : block005_data_flat079 = (CoefficientMerge.scale (7615402680 : Int) atom0375Coded) := by
  rw [block005_data_flat079_step]
def block005_data_flat080 : CoefficientMerge.Poly := [(nat_lit 501, Int.ofNat (nat_lit 7207039520))]
theorem block005_data_flat080_step : block005_data_flat080 = (CoefficientMerge.scale (7207039520 : Int) atom0376Coded) := by decide +kernel
theorem block005_data_flat080_original : block005_data_flat080 = (CoefficientMerge.scale (7207039520 : Int) atom0376Coded) := by
  rw [block005_data_flat080_step]
def block005_data_flat081 : CoefficientMerge.Poly := [(nat_lit 500, Int.ofNat (nat_lit 7615402680)), (nat_lit 501, Int.ofNat (nat_lit 7207039520))]
theorem block005_data_flat081_step : block005_data_flat081 = (CoefficientMerge.fastMerge block005_data_flat079 block005_data_flat080) := by decide +kernel
theorem block005_data_flat081_original : block005_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7615402680 : Int) atom0375Coded) (CoefficientMerge.scale (7207039520 : Int) atom0376Coded)) := by
  rw [block005_data_flat081_step, block005_data_flat079_original, block005_data_flat080_original]
def block005_data_flat082 : CoefficientMerge.Poly := [(nat_lit 502, Int.ofNat (nat_lit 7686420640))]
theorem block005_data_flat082_step : block005_data_flat082 = (CoefficientMerge.scale (7686420640 : Int) atom0377Coded) := by decide +kernel
theorem block005_data_flat082_original : block005_data_flat082 = (CoefficientMerge.scale (7686420640 : Int) atom0377Coded) := by
  rw [block005_data_flat082_step]
def block005_data_flat083 : CoefficientMerge.Poly := [(nat_lit 503, Int.ofNat (nat_lit 8208003360))]
theorem block005_data_flat083_step : block005_data_flat083 = (CoefficientMerge.scale (8208003360 : Int) atom0378Coded) := by decide +kernel
theorem block005_data_flat083_original : block005_data_flat083 = (CoefficientMerge.scale (8208003360 : Int) atom0378Coded) := by
  rw [block005_data_flat083_step]
def block005_data_flat084 : CoefficientMerge.Poly := [(nat_lit 514, Int.ofNat (nat_lit 3287337600))]
theorem block005_data_flat084_step : block005_data_flat084 = (CoefficientMerge.scale (3287337600 : Int) atom0379Coded) := by decide +kernel
theorem block005_data_flat084_original : block005_data_flat084 = (CoefficientMerge.scale (3287337600 : Int) atom0379Coded) := by
  rw [block005_data_flat084_step]
def block005_data_flat085 : CoefficientMerge.Poly := [(nat_lit 503, Int.ofNat (nat_lit 8208003360)), (nat_lit 514, Int.ofNat (nat_lit 3287337600))]
theorem block005_data_flat085_step : block005_data_flat085 = (CoefficientMerge.fastMerge block005_data_flat083 block005_data_flat084) := by decide +kernel
theorem block005_data_flat085_original : block005_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8208003360 : Int) atom0378Coded) (CoefficientMerge.scale (3287337600 : Int) atom0379Coded)) := by
  rw [block005_data_flat085_step, block005_data_flat083_original, block005_data_flat084_original]
def block005_data_flat086 : CoefficientMerge.Poly := [(nat_lit 502, Int.ofNat (nat_lit 7686420640)), (nat_lit 503, Int.ofNat (nat_lit 8208003360)), (nat_lit 514, Int.ofNat (nat_lit 3287337600))]
theorem block005_data_flat086_step : block005_data_flat086 = (CoefficientMerge.fastMerge block005_data_flat082 block005_data_flat085) := by decide +kernel
theorem block005_data_flat086_original : block005_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7686420640 : Int) atom0377Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8208003360 : Int) atom0378Coded) (CoefficientMerge.scale (3287337600 : Int) atom0379Coded))) := by
  rw [block005_data_flat086_step, block005_data_flat082_original, block005_data_flat085_original]
def block005_data_flat087 : CoefficientMerge.Poly := [(nat_lit 500, Int.ofNat (nat_lit 7615402680)), (nat_lit 501, Int.ofNat (nat_lit 7207039520)), (nat_lit 502, Int.ofNat (nat_lit 7686420640)), (nat_lit 503, Int.ofNat (nat_lit 8208003360)), (nat_lit 514, Int.ofNat (nat_lit 3287337600))]
theorem block005_data_flat087_step : block005_data_flat087 = (CoefficientMerge.fastMerge block005_data_flat081 block005_data_flat086) := by decide +kernel
theorem block005_data_flat087_original : block005_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7615402680 : Int) atom0375Coded) (CoefficientMerge.scale (7207039520 : Int) atom0376Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7686420640 : Int) atom0377Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8208003360 : Int) atom0378Coded) (CoefficientMerge.scale (3287337600 : Int) atom0379Coded)))) := by
  rw [block005_data_flat087_step, block005_data_flat081_original, block005_data_flat086_original]
def block005_data_flat088 : CoefficientMerge.Poly := [(nat_lit 515, Int.ofNat (nat_lit 5911061120))]
theorem block005_data_flat088_step : block005_data_flat088 = (CoefficientMerge.scale (5911061120 : Int) atom0380Coded) := by decide +kernel
theorem block005_data_flat088_original : block005_data_flat088 = (CoefficientMerge.scale (5911061120 : Int) atom0380Coded) := by
  rw [block005_data_flat088_step]
def block005_data_flat089 : CoefficientMerge.Poly := [(nat_lit 516, Int.ofNat (nat_lit 7349472480))]
theorem block005_data_flat089_step : block005_data_flat089 = (CoefficientMerge.scale (7349472480 : Int) atom0381Coded) := by decide +kernel
theorem block005_data_flat089_original : block005_data_flat089 = (CoefficientMerge.scale (7349472480 : Int) atom0381Coded) := by
  rw [block005_data_flat089_step]
def block005_data_flat090 : CoefficientMerge.Poly := [(nat_lit 515, Int.ofNat (nat_lit 5911061120)), (nat_lit 516, Int.ofNat (nat_lit 7349472480))]
theorem block005_data_flat090_step : block005_data_flat090 = (CoefficientMerge.fastMerge block005_data_flat088 block005_data_flat089) := by decide +kernel
theorem block005_data_flat090_original : block005_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5911061120 : Int) atom0380Coded) (CoefficientMerge.scale (7349472480 : Int) atom0381Coded)) := by
  rw [block005_data_flat090_step, block005_data_flat088_original, block005_data_flat089_original]
def block005_data_flat091 : CoefficientMerge.Poly := [(nat_lit 517, Int.ofNat (nat_lit 5975361440))]
theorem block005_data_flat091_step : block005_data_flat091 = (CoefficientMerge.scale (5975361440 : Int) atom0382Coded) := by decide +kernel
theorem block005_data_flat091_original : block005_data_flat091 = (CoefficientMerge.scale (5975361440 : Int) atom0382Coded) := by
  rw [block005_data_flat091_step]
def block005_data_flat092 : CoefficientMerge.Poly := [(nat_lit 518, Int.ofNat (nat_lit 8125047480))]
theorem block005_data_flat092_step : block005_data_flat092 = (CoefficientMerge.scale (8125047480 : Int) atom0383Coded) := by decide +kernel
theorem block005_data_flat092_original : block005_data_flat092 = (CoefficientMerge.scale (8125047480 : Int) atom0383Coded) := by
  rw [block005_data_flat092_step]
def block005_data_flat093 : CoefficientMerge.Poly := [(nat_lit 519, Int.ofNat (nat_lit 7310555360))]
theorem block005_data_flat093_step : block005_data_flat093 = (CoefficientMerge.scale (7310555360 : Int) atom0384Coded) := by decide +kernel
theorem block005_data_flat093_original : block005_data_flat093 = (CoefficientMerge.scale (7310555360 : Int) atom0384Coded) := by
  rw [block005_data_flat093_step]
def block005_data_flat094 : CoefficientMerge.Poly := [(nat_lit 518, Int.ofNat (nat_lit 8125047480)), (nat_lit 519, Int.ofNat (nat_lit 7310555360))]
theorem block005_data_flat094_step : block005_data_flat094 = (CoefficientMerge.fastMerge block005_data_flat092 block005_data_flat093) := by decide +kernel
theorem block005_data_flat094_original : block005_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8125047480 : Int) atom0383Coded) (CoefficientMerge.scale (7310555360 : Int) atom0384Coded)) := by
  rw [block005_data_flat094_step, block005_data_flat092_original, block005_data_flat093_original]
def block005_data_flat095 : CoefficientMerge.Poly := [(nat_lit 517, Int.ofNat (nat_lit 5975361440)), (nat_lit 518, Int.ofNat (nat_lit 8125047480)), (nat_lit 519, Int.ofNat (nat_lit 7310555360))]
theorem block005_data_flat095_step : block005_data_flat095 = (CoefficientMerge.fastMerge block005_data_flat091 block005_data_flat094) := by decide +kernel
theorem block005_data_flat095_original : block005_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5975361440 : Int) atom0382Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8125047480 : Int) atom0383Coded) (CoefficientMerge.scale (7310555360 : Int) atom0384Coded))) := by
  rw [block005_data_flat095_step, block005_data_flat091_original, block005_data_flat094_original]
def block005_data_flat096 : CoefficientMerge.Poly := [(nat_lit 515, Int.ofNat (nat_lit 5911061120)), (nat_lit 516, Int.ofNat (nat_lit 7349472480)), (nat_lit 517, Int.ofNat (nat_lit 5975361440)), (nat_lit 518, Int.ofNat (nat_lit 8125047480)), (nat_lit 519, Int.ofNat (nat_lit 7310555360))]
theorem block005_data_flat096_step : block005_data_flat096 = (CoefficientMerge.fastMerge block005_data_flat090 block005_data_flat095) := by decide +kernel
theorem block005_data_flat096_original : block005_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5911061120 : Int) atom0380Coded) (CoefficientMerge.scale (7349472480 : Int) atom0381Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5975361440 : Int) atom0382Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8125047480 : Int) atom0383Coded) (CoefficientMerge.scale (7310555360 : Int) atom0384Coded)))) := by
  rw [block005_data_flat096_step, block005_data_flat090_original, block005_data_flat095_original]
def block005_data_flat097 : CoefficientMerge.Poly := [(nat_lit 500, Int.ofNat (nat_lit 7615402680)), (nat_lit 501, Int.ofNat (nat_lit 7207039520)), (nat_lit 502, Int.ofNat (nat_lit 7686420640)), (nat_lit 503, Int.ofNat (nat_lit 8208003360)), (nat_lit 514, Int.ofNat (nat_lit 3287337600)), (nat_lit 515, Int.ofNat (nat_lit 5911061120)), (nat_lit 516, Int.ofNat (nat_lit 7349472480)), (nat_lit 517, Int.ofNat (nat_lit 5975361440)), (nat_lit 518, Int.ofNat (nat_lit 8125047480)), (nat_lit 519, Int.ofNat (nat_lit 7310555360))]
theorem block005_data_flat097_step : block005_data_flat097 = (CoefficientMerge.fastMerge block005_data_flat087 block005_data_flat096) := by decide +kernel
theorem block005_data_flat097_original : block005_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7615402680 : Int) atom0375Coded) (CoefficientMerge.scale (7207039520 : Int) atom0376Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7686420640 : Int) atom0377Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8208003360 : Int) atom0378Coded) (CoefficientMerge.scale (3287337600 : Int) atom0379Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5911061120 : Int) atom0380Coded) (CoefficientMerge.scale (7349472480 : Int) atom0381Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5975361440 : Int) atom0382Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8125047480 : Int) atom0383Coded) (CoefficientMerge.scale (7310555360 : Int) atom0384Coded))))) := by
  rw [block005_data_flat097_step, block005_data_flat087_original, block005_data_flat096_original]
def block005_data_flat098 : CoefficientMerge.Poly := [(nat_lit 520, Int.ofNat (nat_lit 7652744800))]
theorem block005_data_flat098_step : block005_data_flat098 = (CoefficientMerge.scale (7652744800 : Int) atom0385Coded) := by decide +kernel
theorem block005_data_flat098_original : block005_data_flat098 = (CoefficientMerge.scale (7652744800 : Int) atom0385Coded) := by
  rw [block005_data_flat098_step]
def block005_data_flat099 : CoefficientMerge.Poly := [(nat_lit 521, Int.ofNat (nat_lit 8198641920))]
theorem block005_data_flat099_step : block005_data_flat099 = (CoefficientMerge.scale (8198641920 : Int) atom0386Coded) := by decide +kernel
theorem block005_data_flat099_original : block005_data_flat099 = (CoefficientMerge.scale (8198641920 : Int) atom0386Coded) := by
  rw [block005_data_flat099_step]
def block005_data_flat100 : CoefficientMerge.Poly := [(nat_lit 520, Int.ofNat (nat_lit 7652744800)), (nat_lit 521, Int.ofNat (nat_lit 8198641920))]
theorem block005_data_flat100_step : block005_data_flat100 = (CoefficientMerge.fastMerge block005_data_flat098 block005_data_flat099) := by decide +kernel
theorem block005_data_flat100_original : block005_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7652744800 : Int) atom0385Coded) (CoefficientMerge.scale (8198641920 : Int) atom0386Coded)) := by
  rw [block005_data_flat100_step, block005_data_flat098_original, block005_data_flat099_original]
def block005_data_flat101 : CoefficientMerge.Poly := [(nat_lit 533, Int.ofNat (nat_lit 3794524160))]
theorem block005_data_flat101_step : block005_data_flat101 = (CoefficientMerge.scale (3794524160 : Int) atom0387Coded) := by decide +kernel
theorem block005_data_flat101_original : block005_data_flat101 = (CoefficientMerge.scale (3794524160 : Int) atom0387Coded) := by
  rw [block005_data_flat101_step]
def block005_data_flat102 : CoefficientMerge.Poly := [(nat_lit 534, Int.ofNat (nat_lit 7850429440))]
theorem block005_data_flat102_step : block005_data_flat102 = (CoefficientMerge.scale (7850429440 : Int) atom0388Coded) := by decide +kernel
theorem block005_data_flat102_original : block005_data_flat102 = (CoefficientMerge.scale (7850429440 : Int) atom0388Coded) := by
  rw [block005_data_flat102_step]
def block005_data_flat103 : CoefficientMerge.Poly := [(nat_lit 535, Int.ofNat (nat_lit 6205292800))]
theorem block005_data_flat103_step : block005_data_flat103 = (CoefficientMerge.scale (6205292800 : Int) atom0389Coded) := by decide +kernel
theorem block005_data_flat103_original : block005_data_flat103 = (CoefficientMerge.scale (6205292800 : Int) atom0389Coded) := by
  rw [block005_data_flat103_step]
def block005_data_flat104 : CoefficientMerge.Poly := [(nat_lit 534, Int.ofNat (nat_lit 7850429440)), (nat_lit 535, Int.ofNat (nat_lit 6205292800))]
theorem block005_data_flat104_step : block005_data_flat104 = (CoefficientMerge.fastMerge block005_data_flat102 block005_data_flat103) := by decide +kernel
theorem block005_data_flat104_original : block005_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850429440 : Int) atom0388Coded) (CoefficientMerge.scale (6205292800 : Int) atom0389Coded)) := by
  rw [block005_data_flat104_step, block005_data_flat102_original, block005_data_flat103_original]
def block005_data_flat105 : CoefficientMerge.Poly := [(nat_lit 533, Int.ofNat (nat_lit 3794524160)), (nat_lit 534, Int.ofNat (nat_lit 7850429440)), (nat_lit 535, Int.ofNat (nat_lit 6205292800))]
theorem block005_data_flat105_step : block005_data_flat105 = (CoefficientMerge.fastMerge block005_data_flat101 block005_data_flat104) := by decide +kernel
theorem block005_data_flat105_original : block005_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3794524160 : Int) atom0387Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850429440 : Int) atom0388Coded) (CoefficientMerge.scale (6205292800 : Int) atom0389Coded))) := by
  rw [block005_data_flat105_step, block005_data_flat101_original, block005_data_flat104_original]
def block005_data_flat106 : CoefficientMerge.Poly := [(nat_lit 520, Int.ofNat (nat_lit 7652744800)), (nat_lit 521, Int.ofNat (nat_lit 8198641920)), (nat_lit 533, Int.ofNat (nat_lit 3794524160)), (nat_lit 534, Int.ofNat (nat_lit 7850429440)), (nat_lit 535, Int.ofNat (nat_lit 6205292800))]
theorem block005_data_flat106_step : block005_data_flat106 = (CoefficientMerge.fastMerge block005_data_flat100 block005_data_flat105) := by decide +kernel
theorem block005_data_flat106_original : block005_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7652744800 : Int) atom0385Coded) (CoefficientMerge.scale (8198641920 : Int) atom0386Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3794524160 : Int) atom0387Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850429440 : Int) atom0388Coded) (CoefficientMerge.scale (6205292800 : Int) atom0389Coded)))) := by
  rw [block005_data_flat106_step, block005_data_flat100_original, block005_data_flat105_original]
def block005_data_flat107 : CoefficientMerge.Poly := [(nat_lit 536, Int.ofNat (nat_lit 8413864120))]
theorem block005_data_flat107_step : block005_data_flat107 = (CoefficientMerge.scale (8413864120 : Int) atom0390Coded) := by decide +kernel
theorem block005_data_flat107_original : block005_data_flat107 = (CoefficientMerge.scale (8413864120 : Int) atom0390Coded) := by
  rw [block005_data_flat107_step]
def block005_data_flat108 : CoefficientMerge.Poly := [(nat_lit 537, Int.ofNat (nat_lit 7605570560))]
theorem block005_data_flat108_step : block005_data_flat108 = (CoefficientMerge.scale (7605570560 : Int) atom0391Coded) := by decide +kernel
theorem block005_data_flat108_original : block005_data_flat108 = (CoefficientMerge.scale (7605570560 : Int) atom0391Coded) := by
  rw [block005_data_flat108_step]
def block005_data_flat109 : CoefficientMerge.Poly := [(nat_lit 536, Int.ofNat (nat_lit 8413864120)), (nat_lit 537, Int.ofNat (nat_lit 7605570560))]
theorem block005_data_flat109_step : block005_data_flat109 = (CoefficientMerge.fastMerge block005_data_flat107 block005_data_flat108) := by decide +kernel
theorem block005_data_flat109_original : block005_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8413864120 : Int) atom0390Coded) (CoefficientMerge.scale (7605570560 : Int) atom0391Coded)) := by
  rw [block005_data_flat109_step, block005_data_flat107_original, block005_data_flat108_original]
def block005_data_flat110 : CoefficientMerge.Poly := [(nat_lit 538, Int.ofNat (nat_lit 7277580800))]
theorem block005_data_flat110_step : block005_data_flat110 = (CoefficientMerge.scale (7277580800 : Int) atom0392Coded) := by decide +kernel
theorem block005_data_flat110_original : block005_data_flat110 = (CoefficientMerge.scale (7277580800 : Int) atom0392Coded) := by
  rw [block005_data_flat110_step]
def block005_data_flat111 : CoefficientMerge.Poly := [(nat_lit 539, Int.ofNat (nat_lit 8654338560))]
theorem block005_data_flat111_step : block005_data_flat111 = (CoefficientMerge.scale (8654338560 : Int) atom0393Coded) := by decide +kernel
theorem block005_data_flat111_original : block005_data_flat111 = (CoefficientMerge.scale (8654338560 : Int) atom0393Coded) := by
  rw [block005_data_flat111_step]
def block005_data_flat112 : CoefficientMerge.Poly := [(nat_lit 552, Int.ofNat (nat_lit 5546741760))]
theorem block005_data_flat112_step : block005_data_flat112 = (CoefficientMerge.scale (5546741760 : Int) atom0394Coded) := by decide +kernel
theorem block005_data_flat112_original : block005_data_flat112 = (CoefficientMerge.scale (5546741760 : Int) atom0394Coded) := by
  rw [block005_data_flat112_step]
def block005_data_flat113 : CoefficientMerge.Poly := [(nat_lit 539, Int.ofNat (nat_lit 8654338560)), (nat_lit 552, Int.ofNat (nat_lit 5546741760))]
theorem block005_data_flat113_step : block005_data_flat113 = (CoefficientMerge.fastMerge block005_data_flat111 block005_data_flat112) := by decide +kernel
theorem block005_data_flat113_original : block005_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8654338560 : Int) atom0393Coded) (CoefficientMerge.scale (5546741760 : Int) atom0394Coded)) := by
  rw [block005_data_flat113_step, block005_data_flat111_original, block005_data_flat112_original]
def block005_data_flat114 : CoefficientMerge.Poly := [(nat_lit 538, Int.ofNat (nat_lit 7277580800)), (nat_lit 539, Int.ofNat (nat_lit 8654338560)), (nat_lit 552, Int.ofNat (nat_lit 5546741760))]
theorem block005_data_flat114_step : block005_data_flat114 = (CoefficientMerge.fastMerge block005_data_flat110 block005_data_flat113) := by decide +kernel
theorem block005_data_flat114_original : block005_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7277580800 : Int) atom0392Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8654338560 : Int) atom0393Coded) (CoefficientMerge.scale (5546741760 : Int) atom0394Coded))) := by
  rw [block005_data_flat114_step, block005_data_flat110_original, block005_data_flat113_original]
def block005_data_flat115 : CoefficientMerge.Poly := [(nat_lit 536, Int.ofNat (nat_lit 8413864120)), (nat_lit 537, Int.ofNat (nat_lit 7605570560)), (nat_lit 538, Int.ofNat (nat_lit 7277580800)), (nat_lit 539, Int.ofNat (nat_lit 8654338560)), (nat_lit 552, Int.ofNat (nat_lit 5546741760))]
theorem block005_data_flat115_step : block005_data_flat115 = (CoefficientMerge.fastMerge block005_data_flat109 block005_data_flat114) := by decide +kernel
theorem block005_data_flat115_original : block005_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8413864120 : Int) atom0390Coded) (CoefficientMerge.scale (7605570560 : Int) atom0391Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7277580800 : Int) atom0392Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8654338560 : Int) atom0393Coded) (CoefficientMerge.scale (5546741760 : Int) atom0394Coded)))) := by
  rw [block005_data_flat115_step, block005_data_flat109_original, block005_data_flat114_original]
def block005_data_flat116 : CoefficientMerge.Poly := [(nat_lit 520, Int.ofNat (nat_lit 7652744800)), (nat_lit 521, Int.ofNat (nat_lit 8198641920)), (nat_lit 533, Int.ofNat (nat_lit 3794524160)), (nat_lit 534, Int.ofNat (nat_lit 7850429440)), (nat_lit 535, Int.ofNat (nat_lit 6205292800)), (nat_lit 536, Int.ofNat (nat_lit 8413864120)), (nat_lit 537, Int.ofNat (nat_lit 7605570560)), (nat_lit 538, Int.ofNat (nat_lit 7277580800)), (nat_lit 539, Int.ofNat (nat_lit 8654338560)), (nat_lit 552, Int.ofNat (nat_lit 5546741760))]
theorem block005_data_flat116_step : block005_data_flat116 = (CoefficientMerge.fastMerge block005_data_flat106 block005_data_flat115) := by decide +kernel
theorem block005_data_flat116_original : block005_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7652744800 : Int) atom0385Coded) (CoefficientMerge.scale (8198641920 : Int) atom0386Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3794524160 : Int) atom0387Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850429440 : Int) atom0388Coded) (CoefficientMerge.scale (6205292800 : Int) atom0389Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8413864120 : Int) atom0390Coded) (CoefficientMerge.scale (7605570560 : Int) atom0391Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7277580800 : Int) atom0392Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8654338560 : Int) atom0393Coded) (CoefficientMerge.scale (5546741760 : Int) atom0394Coded))))) := by
  rw [block005_data_flat116_step, block005_data_flat106_original, block005_data_flat115_original]
def block005_data_flat117 : CoefficientMerge.Poly := [(nat_lit 500, Int.ofNat (nat_lit 7615402680)), (nat_lit 501, Int.ofNat (nat_lit 7207039520)), (nat_lit 502, Int.ofNat (nat_lit 7686420640)), (nat_lit 503, Int.ofNat (nat_lit 8208003360)), (nat_lit 514, Int.ofNat (nat_lit 3287337600)), (nat_lit 515, Int.ofNat (nat_lit 5911061120)), (nat_lit 516, Int.ofNat (nat_lit 7349472480)), (nat_lit 517, Int.ofNat (nat_lit 5975361440)), (nat_lit 518, Int.ofNat (nat_lit 8125047480)), (nat_lit 519, Int.ofNat (nat_lit 7310555360)), (nat_lit 520, Int.ofNat (nat_lit 7652744800)), (nat_lit 521, Int.ofNat (nat_lit 8198641920)), (nat_lit 533, Int.ofNat (nat_lit 3794524160)), (nat_lit 534, Int.ofNat (nat_lit 7850429440)), (nat_lit 535, Int.ofNat (nat_lit 6205292800)), (nat_lit 536, Int.ofNat (nat_lit 8413864120)), (nat_lit 537, Int.ofNat (nat_lit 7605570560)), (nat_lit 538, Int.ofNat (nat_lit 7277580800)), (nat_lit 539, Int.ofNat (nat_lit 8654338560)), (nat_lit 552, Int.ofNat (nat_lit 5546741760))]
theorem block005_data_flat117_step : block005_data_flat117 = (CoefficientMerge.fastMerge block005_data_flat097 block005_data_flat116) := by decide +kernel
theorem block005_data_flat117_original : block005_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7615402680 : Int) atom0375Coded) (CoefficientMerge.scale (7207039520 : Int) atom0376Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7686420640 : Int) atom0377Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8208003360 : Int) atom0378Coded) (CoefficientMerge.scale (3287337600 : Int) atom0379Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5911061120 : Int) atom0380Coded) (CoefficientMerge.scale (7349472480 : Int) atom0381Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5975361440 : Int) atom0382Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8125047480 : Int) atom0383Coded) (CoefficientMerge.scale (7310555360 : Int) atom0384Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7652744800 : Int) atom0385Coded) (CoefficientMerge.scale (8198641920 : Int) atom0386Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3794524160 : Int) atom0387Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850429440 : Int) atom0388Coded) (CoefficientMerge.scale (6205292800 : Int) atom0389Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8413864120 : Int) atom0390Coded) (CoefficientMerge.scale (7605570560 : Int) atom0391Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7277580800 : Int) atom0392Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8654338560 : Int) atom0393Coded) (CoefficientMerge.scale (5546741760 : Int) atom0394Coded)))))) := by
  rw [block005_data_flat117_step, block005_data_flat097_original, block005_data_flat116_original]
def block005_data_flat118 : CoefficientMerge.Poly := [(nat_lit 553, Int.ofNat (nat_lit 8918250880))]
theorem block005_data_flat118_step : block005_data_flat118 = (CoefficientMerge.scale (8918250880 : Int) atom0395Coded) := by decide +kernel
theorem block005_data_flat118_original : block005_data_flat118 = (CoefficientMerge.scale (8918250880 : Int) atom0395Coded) := by
  rw [block005_data_flat118_step]
def block005_data_flat119 : CoefficientMerge.Poly := [(nat_lit 554, Int.ofNat (nat_lit 12516486840))]
theorem block005_data_flat119_step : block005_data_flat119 = (CoefficientMerge.scale (12516486840 : Int) atom0396Coded) := by decide +kernel
theorem block005_data_flat119_original : block005_data_flat119 = (CoefficientMerge.scale (12516486840 : Int) atom0396Coded) := by
  rw [block005_data_flat119_step]
def block005_data_flat120 : CoefficientMerge.Poly := [(nat_lit 553, Int.ofNat (nat_lit 8918250880)), (nat_lit 554, Int.ofNat (nat_lit 12516486840))]
theorem block005_data_flat120_step : block005_data_flat120 = (CoefficientMerge.fastMerge block005_data_flat118 block005_data_flat119) := by decide +kernel
theorem block005_data_flat120_original : block005_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8918250880 : Int) atom0395Coded) (CoefficientMerge.scale (12516486840 : Int) atom0396Coded)) := by
  rw [block005_data_flat120_step, block005_data_flat118_original, block005_data_flat119_original]
def block005_data_flat121 : CoefficientMerge.Poly := [(nat_lit 555, Int.ofNat (nat_lit 11769116800))]
theorem block005_data_flat121_step : block005_data_flat121 = (CoefficientMerge.scale (11769116800 : Int) atom0397Coded) := by decide +kernel
theorem block005_data_flat121_original : block005_data_flat121 = (CoefficientMerge.scale (11769116800 : Int) atom0397Coded) := by
  rw [block005_data_flat121_step]
def block005_data_flat122 : CoefficientMerge.Poly := [(nat_lit 556, Int.ofNat (nat_lit 7645850240))]
theorem block005_data_flat122_step : block005_data_flat122 = (CoefficientMerge.scale (7645850240 : Int) atom0398Coded) := by decide +kernel
theorem block005_data_flat122_original : block005_data_flat122 = (CoefficientMerge.scale (7645850240 : Int) atom0398Coded) := by
  rw [block005_data_flat122_step]
def block005_data_flat123 : CoefficientMerge.Poly := [(nat_lit 557, Int.ofNat (nat_lit 8873682720))]
theorem block005_data_flat123_step : block005_data_flat123 = (CoefficientMerge.scale (8873682720 : Int) atom0399Coded) := by decide +kernel
theorem block005_data_flat123_original : block005_data_flat123 = (CoefficientMerge.scale (8873682720 : Int) atom0399Coded) := by
  rw [block005_data_flat123_step]
def block005_data_flat124 : CoefficientMerge.Poly := [(nat_lit 556, Int.ofNat (nat_lit 7645850240)), (nat_lit 557, Int.ofNat (nat_lit 8873682720))]
theorem block005_data_flat124_step : block005_data_flat124 = (CoefficientMerge.fastMerge block005_data_flat122 block005_data_flat123) := by decide +kernel
theorem block005_data_flat124_original : block005_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7645850240 : Int) atom0398Coded) (CoefficientMerge.scale (8873682720 : Int) atom0399Coded)) := by
  rw [block005_data_flat124_step, block005_data_flat122_original, block005_data_flat123_original]
def block005_data_flat125 : CoefficientMerge.Poly := [(nat_lit 555, Int.ofNat (nat_lit 11769116800)), (nat_lit 556, Int.ofNat (nat_lit 7645850240)), (nat_lit 557, Int.ofNat (nat_lit 8873682720))]
theorem block005_data_flat125_step : block005_data_flat125 = (CoefficientMerge.fastMerge block005_data_flat121 block005_data_flat124) := by decide +kernel
theorem block005_data_flat125_original : block005_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11769116800 : Int) atom0397Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7645850240 : Int) atom0398Coded) (CoefficientMerge.scale (8873682720 : Int) atom0399Coded))) := by
  rw [block005_data_flat125_step, block005_data_flat121_original, block005_data_flat124_original]
def block005_data_flat126 : CoefficientMerge.Poly := [(nat_lit 553, Int.ofNat (nat_lit 8918250880)), (nat_lit 554, Int.ofNat (nat_lit 12516486840)), (nat_lit 555, Int.ofNat (nat_lit 11769116800)), (nat_lit 556, Int.ofNat (nat_lit 7645850240)), (nat_lit 557, Int.ofNat (nat_lit 8873682720))]
theorem block005_data_flat126_step : block005_data_flat126 = (CoefficientMerge.fastMerge block005_data_flat120 block005_data_flat125) := by decide +kernel
theorem block005_data_flat126_original : block005_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8918250880 : Int) atom0395Coded) (CoefficientMerge.scale (12516486840 : Int) atom0396Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11769116800 : Int) atom0397Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7645850240 : Int) atom0398Coded) (CoefficientMerge.scale (8873682720 : Int) atom0399Coded)))) := by
  rw [block005_data_flat126_step, block005_data_flat120_original, block005_data_flat125_original]
def block005_data_flat127 : CoefficientMerge.Poly := [(nat_lit 571, Int.ofNat (nat_lit 3470027456))]
theorem block005_data_flat127_step : block005_data_flat127 = (CoefficientMerge.scale (3470027456 : Int) atom0400Coded) := by decide +kernel
theorem block005_data_flat127_original : block005_data_flat127 = (CoefficientMerge.scale (3470027456 : Int) atom0400Coded) := by
  rw [block005_data_flat127_step]
def block005_data_flat128 : CoefficientMerge.Poly := [(nat_lit 572, Int.ofNat (nat_lit 9201418000))]
theorem block005_data_flat128_step : block005_data_flat128 = (CoefficientMerge.scale (9201418000 : Int) atom0401Coded) := by decide +kernel
theorem block005_data_flat128_original : block005_data_flat128 = (CoefficientMerge.scale (9201418000 : Int) atom0401Coded) := by
  rw [block005_data_flat128_step]
def block005_data_flat129 : CoefficientMerge.Poly := [(nat_lit 571, Int.ofNat (nat_lit 3470027456)), (nat_lit 572, Int.ofNat (nat_lit 9201418000))]
theorem block005_data_flat129_step : block005_data_flat129 = (CoefficientMerge.fastMerge block005_data_flat127 block005_data_flat128) := by decide +kernel
theorem block005_data_flat129_original : block005_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3470027456 : Int) atom0400Coded) (CoefficientMerge.scale (9201418000 : Int) atom0401Coded)) := by
  rw [block005_data_flat129_step, block005_data_flat127_original, block005_data_flat128_original]
def block005_data_flat130 : CoefficientMerge.Poly := [(nat_lit 573, Int.ofNat (nat_lit 10093237280))]
theorem block005_data_flat130_step : block005_data_flat130 = (CoefficientMerge.scale (10093237280 : Int) atom0402Coded) := by decide +kernel
theorem block005_data_flat130_original : block005_data_flat130 = (CoefficientMerge.scale (10093237280 : Int) atom0402Coded) := by
  rw [block005_data_flat130_step]
def block005_data_flat131 : CoefficientMerge.Poly := [(nat_lit 574, Int.ofNat (nat_lit 7347075680))]
theorem block005_data_flat131_step : block005_data_flat131 = (CoefficientMerge.scale (7347075680 : Int) atom0403Coded) := by decide +kernel
theorem block005_data_flat131_original : block005_data_flat131 = (CoefficientMerge.scale (7347075680 : Int) atom0403Coded) := by
  rw [block005_data_flat131_step]
def block005_data_flat132 : CoefficientMerge.Poly := [(nat_lit 575, Int.ofNat (nat_lit 7882412160))]
theorem block005_data_flat132_step : block005_data_flat132 = (CoefficientMerge.scale (7882412160 : Int) atom0404Coded) := by decide +kernel
theorem block005_data_flat132_original : block005_data_flat132 = (CoefficientMerge.scale (7882412160 : Int) atom0404Coded) := by
  rw [block005_data_flat132_step]
def block005_data_flat133 : CoefficientMerge.Poly := [(nat_lit 574, Int.ofNat (nat_lit 7347075680)), (nat_lit 575, Int.ofNat (nat_lit 7882412160))]
theorem block005_data_flat133_step : block005_data_flat133 = (CoefficientMerge.fastMerge block005_data_flat131 block005_data_flat132) := by decide +kernel
theorem block005_data_flat133_original : block005_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7347075680 : Int) atom0403Coded) (CoefficientMerge.scale (7882412160 : Int) atom0404Coded)) := by
  rw [block005_data_flat133_step, block005_data_flat131_original, block005_data_flat132_original]
def block005_data_flat134 : CoefficientMerge.Poly := [(nat_lit 573, Int.ofNat (nat_lit 10093237280)), (nat_lit 574, Int.ofNat (nat_lit 7347075680)), (nat_lit 575, Int.ofNat (nat_lit 7882412160))]
theorem block005_data_flat134_step : block005_data_flat134 = (CoefficientMerge.fastMerge block005_data_flat130 block005_data_flat133) := by decide +kernel
theorem block005_data_flat134_original : block005_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10093237280 : Int) atom0402Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7347075680 : Int) atom0403Coded) (CoefficientMerge.scale (7882412160 : Int) atom0404Coded))) := by
  rw [block005_data_flat134_step, block005_data_flat130_original, block005_data_flat133_original]
def block005_data_flat135 : CoefficientMerge.Poly := [(nat_lit 571, Int.ofNat (nat_lit 3470027456)), (nat_lit 572, Int.ofNat (nat_lit 9201418000)), (nat_lit 573, Int.ofNat (nat_lit 10093237280)), (nat_lit 574, Int.ofNat (nat_lit 7347075680)), (nat_lit 575, Int.ofNat (nat_lit 7882412160))]
theorem block005_data_flat135_step : block005_data_flat135 = (CoefficientMerge.fastMerge block005_data_flat129 block005_data_flat134) := by decide +kernel
theorem block005_data_flat135_original : block005_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3470027456 : Int) atom0400Coded) (CoefficientMerge.scale (9201418000 : Int) atom0401Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10093237280 : Int) atom0402Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7347075680 : Int) atom0403Coded) (CoefficientMerge.scale (7882412160 : Int) atom0404Coded)))) := by
  rw [block005_data_flat135_step, block005_data_flat129_original, block005_data_flat134_original]
def block005_data_flat136 : CoefficientMerge.Poly := [(nat_lit 553, Int.ofNat (nat_lit 8918250880)), (nat_lit 554, Int.ofNat (nat_lit 12516486840)), (nat_lit 555, Int.ofNat (nat_lit 11769116800)), (nat_lit 556, Int.ofNat (nat_lit 7645850240)), (nat_lit 557, Int.ofNat (nat_lit 8873682720)), (nat_lit 571, Int.ofNat (nat_lit 3470027456)), (nat_lit 572, Int.ofNat (nat_lit 9201418000)), (nat_lit 573, Int.ofNat (nat_lit 10093237280)), (nat_lit 574, Int.ofNat (nat_lit 7347075680)), (nat_lit 575, Int.ofNat (nat_lit 7882412160))]
theorem block005_data_flat136_step : block005_data_flat136 = (CoefficientMerge.fastMerge block005_data_flat126 block005_data_flat135) := by decide +kernel
theorem block005_data_flat136_original : block005_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8918250880 : Int) atom0395Coded) (CoefficientMerge.scale (12516486840 : Int) atom0396Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11769116800 : Int) atom0397Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7645850240 : Int) atom0398Coded) (CoefficientMerge.scale (8873682720 : Int) atom0399Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3470027456 : Int) atom0400Coded) (CoefficientMerge.scale (9201418000 : Int) atom0401Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10093237280 : Int) atom0402Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7347075680 : Int) atom0403Coded) (CoefficientMerge.scale (7882412160 : Int) atom0404Coded))))) := by
  rw [block005_data_flat136_step, block005_data_flat126_original, block005_data_flat135_original]
def block005_data_flat137 : CoefficientMerge.Poly := [(nat_lit 590, Int.ofNat (nat_lit 6708730320))]
theorem block005_data_flat137_step : block005_data_flat137 = (CoefficientMerge.scale (6708730320 : Int) atom0405Coded) := by decide +kernel
theorem block005_data_flat137_original : block005_data_flat137 = (CoefficientMerge.scale (6708730320 : Int) atom0405Coded) := by
  rw [block005_data_flat137_step]
def block005_data_flat138 : CoefficientMerge.Poly := [(nat_lit 591, Int.ofNat (nat_lit 10927396240))]
theorem block005_data_flat138_step : block005_data_flat138 = (CoefficientMerge.scale (10927396240 : Int) atom0406Coded) := by decide +kernel
theorem block005_data_flat138_original : block005_data_flat138 = (CoefficientMerge.scale (10927396240 : Int) atom0406Coded) := by
  rw [block005_data_flat138_step]
def block005_data_flat139 : CoefficientMerge.Poly := [(nat_lit 590, Int.ofNat (nat_lit 6708730320)), (nat_lit 591, Int.ofNat (nat_lit 10927396240))]
theorem block005_data_flat139_step : block005_data_flat139 = (CoefficientMerge.fastMerge block005_data_flat137 block005_data_flat138) := by decide +kernel
theorem block005_data_flat139_original : block005_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6708730320 : Int) atom0405Coded) (CoefficientMerge.scale (10927396240 : Int) atom0406Coded)) := by
  rw [block005_data_flat139_step, block005_data_flat137_original, block005_data_flat138_original]
def block005_data_flat140 : CoefficientMerge.Poly := [(nat_lit 592, Int.ofNat (nat_lit 8160306320))]
theorem block005_data_flat140_step : block005_data_flat140 = (CoefficientMerge.scale (8160306320 : Int) atom0407Coded) := by decide +kernel
theorem block005_data_flat140_original : block005_data_flat140 = (CoefficientMerge.scale (8160306320 : Int) atom0407Coded) := by
  rw [block005_data_flat140_step]
def block005_data_flat141 : CoefficientMerge.Poly := [(nat_lit 593, Int.ofNat (nat_lit 8967654960))]
theorem block005_data_flat141_step : block005_data_flat141 = (CoefficientMerge.scale (8967654960 : Int) atom0408Coded) := by decide +kernel
theorem block005_data_flat141_original : block005_data_flat141 = (CoefficientMerge.scale (8967654960 : Int) atom0408Coded) := by
  rw [block005_data_flat141_step]
def block005_data_flat142 : CoefficientMerge.Poly := [(nat_lit 609, Int.ofNat (nat_lit 3992019360))]
theorem block005_data_flat142_step : block005_data_flat142 = (CoefficientMerge.scale (3992019360 : Int) atom0409Coded) := by decide +kernel
theorem block005_data_flat142_original : block005_data_flat142 = (CoefficientMerge.scale (3992019360 : Int) atom0409Coded) := by
  rw [block005_data_flat142_step]
def block005_data_flat143 : CoefficientMerge.Poly := [(nat_lit 593, Int.ofNat (nat_lit 8967654960)), (nat_lit 609, Int.ofNat (nat_lit 3992019360))]
theorem block005_data_flat143_step : block005_data_flat143 = (CoefficientMerge.fastMerge block005_data_flat141 block005_data_flat142) := by decide +kernel
theorem block005_data_flat143_original : block005_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8967654960 : Int) atom0408Coded) (CoefficientMerge.scale (3992019360 : Int) atom0409Coded)) := by
  rw [block005_data_flat143_step, block005_data_flat141_original, block005_data_flat142_original]
def block005_data_flat144 : CoefficientMerge.Poly := [(nat_lit 592, Int.ofNat (nat_lit 8160306320)), (nat_lit 593, Int.ofNat (nat_lit 8967654960)), (nat_lit 609, Int.ofNat (nat_lit 3992019360))]
theorem block005_data_flat144_step : block005_data_flat144 = (CoefficientMerge.fastMerge block005_data_flat140 block005_data_flat143) := by decide +kernel
theorem block005_data_flat144_original : block005_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8160306320 : Int) atom0407Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8967654960 : Int) atom0408Coded) (CoefficientMerge.scale (3992019360 : Int) atom0409Coded))) := by
  rw [block005_data_flat144_step, block005_data_flat140_original, block005_data_flat143_original]
def block005_data_flat145 : CoefficientMerge.Poly := [(nat_lit 590, Int.ofNat (nat_lit 6708730320)), (nat_lit 591, Int.ofNat (nat_lit 10927396240)), (nat_lit 592, Int.ofNat (nat_lit 8160306320)), (nat_lit 593, Int.ofNat (nat_lit 8967654960)), (nat_lit 609, Int.ofNat (nat_lit 3992019360))]
theorem block005_data_flat145_step : block005_data_flat145 = (CoefficientMerge.fastMerge block005_data_flat139 block005_data_flat144) := by decide +kernel
theorem block005_data_flat145_original : block005_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6708730320 : Int) atom0405Coded) (CoefficientMerge.scale (10927396240 : Int) atom0406Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8160306320 : Int) atom0407Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8967654960 : Int) atom0408Coded) (CoefficientMerge.scale (3992019360 : Int) atom0409Coded)))) := by
  rw [block005_data_flat145_step, block005_data_flat139_original, block005_data_flat144_original]
def block005_data_flat146 : CoefficientMerge.Poly := [(nat_lit 610, Int.ofNat (nat_lit 5176124800))]
theorem block005_data_flat146_step : block005_data_flat146 = (CoefficientMerge.scale (5176124800 : Int) atom0410Coded) := by decide +kernel
theorem block005_data_flat146_original : block005_data_flat146 = (CoefficientMerge.scale (5176124800 : Int) atom0410Coded) := by
  rw [block005_data_flat146_step]
def block005_data_flat147 : CoefficientMerge.Poly := [(nat_lit 611, Int.ofNat (nat_lit 5897774400))]
theorem block005_data_flat147_step : block005_data_flat147 = (CoefficientMerge.scale (5897774400 : Int) atom0411Coded) := by decide +kernel
theorem block005_data_flat147_original : block005_data_flat147 = (CoefficientMerge.scale (5897774400 : Int) atom0411Coded) := by
  rw [block005_data_flat147_step]
def block005_data_flat148 : CoefficientMerge.Poly := [(nat_lit 610, Int.ofNat (nat_lit 5176124800)), (nat_lit 611, Int.ofNat (nat_lit 5897774400))]
theorem block005_data_flat148_step : block005_data_flat148 = (CoefficientMerge.fastMerge block005_data_flat146 block005_data_flat147) := by decide +kernel
theorem block005_data_flat148_original : block005_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5176124800 : Int) atom0410Coded) (CoefficientMerge.scale (5897774400 : Int) atom0411Coded)) := by
  rw [block005_data_flat148_step, block005_data_flat146_original, block005_data_flat147_original]
def block005_data_flat149 : CoefficientMerge.Poly := [(nat_lit 628, Int.ofNat (nat_lit 769123040))]
theorem block005_data_flat149_step : block005_data_flat149 = (CoefficientMerge.scale (769123040 : Int) atom0412Coded) := by decide +kernel
theorem block005_data_flat149_original : block005_data_flat149 = (CoefficientMerge.scale (769123040 : Int) atom0412Coded) := by
  rw [block005_data_flat149_step]
def block005_data_flat150 : CoefficientMerge.Poly := [(nat_lit 629, Int.ofNat (nat_lit 1724694720))]
theorem block005_data_flat150_step : block005_data_flat150 = (CoefficientMerge.scale (1724694720 : Int) atom0413Coded) := by decide +kernel
theorem block005_data_flat150_original : block005_data_flat150 = (CoefficientMerge.scale (1724694720 : Int) atom0413Coded) := by
  rw [block005_data_flat150_step]
def block005_data_flat151 : CoefficientMerge.Poly := [(nat_lit 647, Int.ofNat (nat_lit 333335520))]
theorem block005_data_flat151_step : block005_data_flat151 = (CoefficientMerge.scale (333335520 : Int) atom0414Coded) := by decide +kernel
theorem block005_data_flat151_original : block005_data_flat151 = (CoefficientMerge.scale (333335520 : Int) atom0414Coded) := by
  rw [block005_data_flat151_step]
def block005_data_flat152 : CoefficientMerge.Poly := [(nat_lit 629, Int.ofNat (nat_lit 1724694720)), (nat_lit 647, Int.ofNat (nat_lit 333335520))]
theorem block005_data_flat152_step : block005_data_flat152 = (CoefficientMerge.fastMerge block005_data_flat150 block005_data_flat151) := by decide +kernel
theorem block005_data_flat152_original : block005_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1724694720 : Int) atom0413Coded) (CoefficientMerge.scale (333335520 : Int) atom0414Coded)) := by
  rw [block005_data_flat152_step, block005_data_flat150_original, block005_data_flat151_original]
def block005_data_flat153 : CoefficientMerge.Poly := [(nat_lit 628, Int.ofNat (nat_lit 769123040)), (nat_lit 629, Int.ofNat (nat_lit 1724694720)), (nat_lit 647, Int.ofNat (nat_lit 333335520))]
theorem block005_data_flat153_step : block005_data_flat153 = (CoefficientMerge.fastMerge block005_data_flat149 block005_data_flat152) := by decide +kernel
theorem block005_data_flat153_original : block005_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (769123040 : Int) atom0412Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1724694720 : Int) atom0413Coded) (CoefficientMerge.scale (333335520 : Int) atom0414Coded))) := by
  rw [block005_data_flat153_step, block005_data_flat149_original, block005_data_flat152_original]
def block005_data_flat154 : CoefficientMerge.Poly := [(nat_lit 610, Int.ofNat (nat_lit 5176124800)), (nat_lit 611, Int.ofNat (nat_lit 5897774400)), (nat_lit 628, Int.ofNat (nat_lit 769123040)), (nat_lit 629, Int.ofNat (nat_lit 1724694720)), (nat_lit 647, Int.ofNat (nat_lit 333335520))]
theorem block005_data_flat154_step : block005_data_flat154 = (CoefficientMerge.fastMerge block005_data_flat148 block005_data_flat153) := by decide +kernel
theorem block005_data_flat154_original : block005_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5176124800 : Int) atom0410Coded) (CoefficientMerge.scale (5897774400 : Int) atom0411Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (769123040 : Int) atom0412Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1724694720 : Int) atom0413Coded) (CoefficientMerge.scale (333335520 : Int) atom0414Coded)))) := by
  rw [block005_data_flat154_step, block005_data_flat148_original, block005_data_flat153_original]
def block005_data_flat155 : CoefficientMerge.Poly := [(nat_lit 590, Int.ofNat (nat_lit 6708730320)), (nat_lit 591, Int.ofNat (nat_lit 10927396240)), (nat_lit 592, Int.ofNat (nat_lit 8160306320)), (nat_lit 593, Int.ofNat (nat_lit 8967654960)), (nat_lit 609, Int.ofNat (nat_lit 3992019360)), (nat_lit 610, Int.ofNat (nat_lit 5176124800)), (nat_lit 611, Int.ofNat (nat_lit 5897774400)), (nat_lit 628, Int.ofNat (nat_lit 769123040)), (nat_lit 629, Int.ofNat (nat_lit 1724694720)), (nat_lit 647, Int.ofNat (nat_lit 333335520))]
theorem block005_data_flat155_step : block005_data_flat155 = (CoefficientMerge.fastMerge block005_data_flat145 block005_data_flat154) := by decide +kernel
theorem block005_data_flat155_original : block005_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6708730320 : Int) atom0405Coded) (CoefficientMerge.scale (10927396240 : Int) atom0406Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8160306320 : Int) atom0407Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8967654960 : Int) atom0408Coded) (CoefficientMerge.scale (3992019360 : Int) atom0409Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5176124800 : Int) atom0410Coded) (CoefficientMerge.scale (5897774400 : Int) atom0411Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (769123040 : Int) atom0412Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1724694720 : Int) atom0413Coded) (CoefficientMerge.scale (333335520 : Int) atom0414Coded))))) := by
  rw [block005_data_flat155_step, block005_data_flat145_original, block005_data_flat154_original]
def block005_data_flat156 : CoefficientMerge.Poly := [(nat_lit 553, Int.ofNat (nat_lit 8918250880)), (nat_lit 554, Int.ofNat (nat_lit 12516486840)), (nat_lit 555, Int.ofNat (nat_lit 11769116800)), (nat_lit 556, Int.ofNat (nat_lit 7645850240)), (nat_lit 557, Int.ofNat (nat_lit 8873682720)), (nat_lit 571, Int.ofNat (nat_lit 3470027456)), (nat_lit 572, Int.ofNat (nat_lit 9201418000)), (nat_lit 573, Int.ofNat (nat_lit 10093237280)), (nat_lit 574, Int.ofNat (nat_lit 7347075680)), (nat_lit 575, Int.ofNat (nat_lit 7882412160)), (nat_lit 590, Int.ofNat (nat_lit 6708730320)), (nat_lit 591, Int.ofNat (nat_lit 10927396240)), (nat_lit 592, Int.ofNat (nat_lit 8160306320)), (nat_lit 593, Int.ofNat (nat_lit 8967654960)), (nat_lit 609, Int.ofNat (nat_lit 3992019360)), (nat_lit 610, Int.ofNat (nat_lit 5176124800)), (nat_lit 611, Int.ofNat (nat_lit 5897774400)), (nat_lit 628, Int.ofNat (nat_lit 769123040)), (nat_lit 629, Int.ofNat (nat_lit 1724694720)), (nat_lit 647, Int.ofNat (nat_lit 333335520))]
theorem block005_data_flat156_step : block005_data_flat156 = (CoefficientMerge.fastMerge block005_data_flat136 block005_data_flat155) := by decide +kernel
theorem block005_data_flat156_original : block005_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8918250880 : Int) atom0395Coded) (CoefficientMerge.scale (12516486840 : Int) atom0396Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11769116800 : Int) atom0397Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7645850240 : Int) atom0398Coded) (CoefficientMerge.scale (8873682720 : Int) atom0399Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3470027456 : Int) atom0400Coded) (CoefficientMerge.scale (9201418000 : Int) atom0401Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10093237280 : Int) atom0402Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7347075680 : Int) atom0403Coded) (CoefficientMerge.scale (7882412160 : Int) atom0404Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6708730320 : Int) atom0405Coded) (CoefficientMerge.scale (10927396240 : Int) atom0406Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8160306320 : Int) atom0407Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8967654960 : Int) atom0408Coded) (CoefficientMerge.scale (3992019360 : Int) atom0409Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5176124800 : Int) atom0410Coded) (CoefficientMerge.scale (5897774400 : Int) atom0411Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (769123040 : Int) atom0412Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1724694720 : Int) atom0413Coded) (CoefficientMerge.scale (333335520 : Int) atom0414Coded)))))) := by
  rw [block005_data_flat156_step, block005_data_flat136_original, block005_data_flat155_original]
def block005_data_flat157 : CoefficientMerge.Poly := [(nat_lit 500, Int.ofNat (nat_lit 7615402680)), (nat_lit 501, Int.ofNat (nat_lit 7207039520)), (nat_lit 502, Int.ofNat (nat_lit 7686420640)), (nat_lit 503, Int.ofNat (nat_lit 8208003360)), (nat_lit 514, Int.ofNat (nat_lit 3287337600)), (nat_lit 515, Int.ofNat (nat_lit 5911061120)), (nat_lit 516, Int.ofNat (nat_lit 7349472480)), (nat_lit 517, Int.ofNat (nat_lit 5975361440)), (nat_lit 518, Int.ofNat (nat_lit 8125047480)), (nat_lit 519, Int.ofNat (nat_lit 7310555360)), (nat_lit 520, Int.ofNat (nat_lit 7652744800)), (nat_lit 521, Int.ofNat (nat_lit 8198641920)), (nat_lit 533, Int.ofNat (nat_lit 3794524160)), (nat_lit 534, Int.ofNat (nat_lit 7850429440)), (nat_lit 535, Int.ofNat (nat_lit 6205292800)), (nat_lit 536, Int.ofNat (nat_lit 8413864120)), (nat_lit 537, Int.ofNat (nat_lit 7605570560)), (nat_lit 538, Int.ofNat (nat_lit 7277580800)), (nat_lit 539, Int.ofNat (nat_lit 8654338560)), (nat_lit 552, Int.ofNat (nat_lit 5546741760)), (nat_lit 553, Int.ofNat (nat_lit 8918250880)), (nat_lit 554, Int.ofNat (nat_lit 12516486840)), (nat_lit 555, Int.ofNat (nat_lit 11769116800)), (nat_lit 556, Int.ofNat (nat_lit 7645850240)), (nat_lit 557, Int.ofNat (nat_lit 8873682720)), (nat_lit 571, Int.ofNat (nat_lit 3470027456)), (nat_lit 572, Int.ofNat (nat_lit 9201418000)), (nat_lit 573, Int.ofNat (nat_lit 10093237280)), (nat_lit 574, Int.ofNat (nat_lit 7347075680)), (nat_lit 575, Int.ofNat (nat_lit 7882412160)), (nat_lit 590, Int.ofNat (nat_lit 6708730320)), (nat_lit 591, Int.ofNat (nat_lit 10927396240)), (nat_lit 592, Int.ofNat (nat_lit 8160306320)), (nat_lit 593, Int.ofNat (nat_lit 8967654960)), (nat_lit 609, Int.ofNat (nat_lit 3992019360)), (nat_lit 610, Int.ofNat (nat_lit 5176124800)), (nat_lit 611, Int.ofNat (nat_lit 5897774400)), (nat_lit 628, Int.ofNat (nat_lit 769123040)), (nat_lit 629, Int.ofNat (nat_lit 1724694720)), (nat_lit 647, Int.ofNat (nat_lit 333335520))]
theorem block005_data_flat157_step : block005_data_flat157 = (CoefficientMerge.fastMerge block005_data_flat117 block005_data_flat156) := by decide +kernel
theorem block005_data_flat157_original : block005_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7615402680 : Int) atom0375Coded) (CoefficientMerge.scale (7207039520 : Int) atom0376Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7686420640 : Int) atom0377Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8208003360 : Int) atom0378Coded) (CoefficientMerge.scale (3287337600 : Int) atom0379Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5911061120 : Int) atom0380Coded) (CoefficientMerge.scale (7349472480 : Int) atom0381Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5975361440 : Int) atom0382Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8125047480 : Int) atom0383Coded) (CoefficientMerge.scale (7310555360 : Int) atom0384Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7652744800 : Int) atom0385Coded) (CoefficientMerge.scale (8198641920 : Int) atom0386Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3794524160 : Int) atom0387Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850429440 : Int) atom0388Coded) (CoefficientMerge.scale (6205292800 : Int) atom0389Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8413864120 : Int) atom0390Coded) (CoefficientMerge.scale (7605570560 : Int) atom0391Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7277580800 : Int) atom0392Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8654338560 : Int) atom0393Coded) (CoefficientMerge.scale (5546741760 : Int) atom0394Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8918250880 : Int) atom0395Coded) (CoefficientMerge.scale (12516486840 : Int) atom0396Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11769116800 : Int) atom0397Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7645850240 : Int) atom0398Coded) (CoefficientMerge.scale (8873682720 : Int) atom0399Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3470027456 : Int) atom0400Coded) (CoefficientMerge.scale (9201418000 : Int) atom0401Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10093237280 : Int) atom0402Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7347075680 : Int) atom0403Coded) (CoefficientMerge.scale (7882412160 : Int) atom0404Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6708730320 : Int) atom0405Coded) (CoefficientMerge.scale (10927396240 : Int) atom0406Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8160306320 : Int) atom0407Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8967654960 : Int) atom0408Coded) (CoefficientMerge.scale (3992019360 : Int) atom0409Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5176124800 : Int) atom0410Coded) (CoefficientMerge.scale (5897774400 : Int) atom0411Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (769123040 : Int) atom0412Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1724694720 : Int) atom0413Coded) (CoefficientMerge.scale (333335520 : Int) atom0414Coded))))))) := by
  rw [block005_data_flat157_step, block005_data_flat117_original, block005_data_flat156_original]
def block005_data_flat158 : CoefficientMerge.Poly := [(nat_lit 430, Int.ofNat (nat_lit 5898088840)), (nat_lit 431, Int.ofNat (nat_lit 6018711240)), (nat_lit 438, Int.ofNat (nat_lit 2000907360)), (nat_lit 439, Int.ofNat (nat_lit 3212404128)), (nat_lit 440, Int.ofNat (nat_lit 2905871040)), (nat_lit 441, Int.ofNat (nat_lit 2903290560)), (nat_lit 442, Int.ofNat (nat_lit 2951029440)), (nat_lit 443, Int.ofNat (nat_lit 3174733760)), (nat_lit 444, Int.ofNat (nat_lit 5883494400)), (nat_lit 445, Int.ofNat (nat_lit 4456174040)), (nat_lit 446, Int.ofNat (nat_lit 6098833080)), (nat_lit 447, Int.ofNat (nat_lit 5959982600)), (nat_lit 448, Int.ofNat (nat_lit 6391196200)), (nat_lit 449, Int.ofNat (nat_lit 6822409800)), (nat_lit 457, Int.ofNat (nat_lit 2336973120)), (nat_lit 458, Int.ofNat (nat_lit 3943380288)), (nat_lit 459, Int.ofNat (nat_lit 3334043520)), (nat_lit 460, Int.ofNat (nat_lit 3358235520)), (nat_lit 461, Int.ofNat (nat_lit 3558392960)), (nat_lit 462, Int.ofNat (nat_lit 6159605760)), (nat_lit 463, Int.ofNat (nat_lit 4881594320)), (nat_lit 464, Int.ofNat (nat_lit 6576221880)), (nat_lit 465, Int.ofNat (nat_lit 6516018800)), (nat_lit 466, Int.ofNat (nat_lit 7042158640)), (nat_lit 467, Int.ofNat (nat_lit 7568298480)), (nat_lit 476, Int.ofNat (nat_lit 2731883520)), (nat_lit 477, Int.ofNat (nat_lit 4672629120)), (nat_lit 478, Int.ofNat (nat_lit 3937045632)), (nat_lit 479, Int.ofNat (nat_lit 4045591040)), (nat_lit 480, Int.ofNat (nat_lit 6538183680)), (nat_lit 481, Int.ofNat (nat_lit 5324168960)), (nat_lit 482, Int.ofNat (nat_lit 7156077240)), (nat_lit 483, Int.ofNat (nat_lit 6966759680)), (nat_lit 484, Int.ofNat (nat_lit 7463345920)), (nat_lit 485, Int.ofNat (nat_lit 8011165440)), (nat_lit 495, Int.ofNat (nat_lit 3038632320)), (nat_lit 496, Int.ofNat (nat_lit 5210772480)), (nat_lit 497, Int.ofNat (nat_lit 4660776320)), (nat_lit 498, Int.ofNat (nat_lit 6904803360)), (nat_lit 499, Int.ofNat (nat_lit 5640737120)), (nat_lit 500, Int.ofNat (nat_lit 7615402680)), (nat_lit 501, Int.ofNat (nat_lit 7207039520)), (nat_lit 502, Int.ofNat (nat_lit 7686420640)), (nat_lit 503, Int.ofNat (nat_lit 8208003360)), (nat_lit 514, Int.ofNat (nat_lit 3287337600)), (nat_lit 515, Int.ofNat (nat_lit 5911061120)), (nat_lit 516, Int.ofNat (nat_lit 7349472480)), (nat_lit 517, Int.ofNat (nat_lit 5975361440)), (nat_lit 518, Int.ofNat (nat_lit 8125047480)), (nat_lit 519, Int.ofNat (nat_lit 7310555360)), (nat_lit 520, Int.ofNat (nat_lit 7652744800)), (nat_lit 521, Int.ofNat (nat_lit 8198641920)), (nat_lit 533, Int.ofNat (nat_lit 3794524160)), (nat_lit 534, Int.ofNat (nat_lit 7850429440)), (nat_lit 535, Int.ofNat (nat_lit 6205292800)), (nat_lit 536, Int.ofNat (nat_lit 8413864120)), (nat_lit 537, Int.ofNat (nat_lit 7605570560)), (nat_lit 538, Int.ofNat (nat_lit 7277580800)), (nat_lit 539, Int.ofNat (nat_lit 8654338560)), (nat_lit 552, Int.ofNat (nat_lit 5546741760)), (nat_lit 553, Int.ofNat (nat_lit 8918250880)), (nat_lit 554, Int.ofNat (nat_lit 12516486840)), (nat_lit 555, Int.ofNat (nat_lit 11769116800)), (nat_lit 556, Int.ofNat (nat_lit 7645850240)), (nat_lit 557, Int.ofNat (nat_lit 8873682720)), (nat_lit 571, Int.ofNat (nat_lit 3470027456)), (nat_lit 572, Int.ofNat (nat_lit 9201418000)), (nat_lit 573, Int.ofNat (nat_lit 10093237280)), (nat_lit 574, Int.ofNat (nat_lit 7347075680)), (nat_lit 575, Int.ofNat (nat_lit 7882412160)), (nat_lit 590, Int.ofNat (nat_lit 6708730320)), (nat_lit 591, Int.ofNat (nat_lit 10927396240)), (nat_lit 592, Int.ofNat (nat_lit 8160306320)), (nat_lit 593, Int.ofNat (nat_lit 8967654960)), (nat_lit 609, Int.ofNat (nat_lit 3992019360)), (nat_lit 610, Int.ofNat (nat_lit 5176124800)), (nat_lit 611, Int.ofNat (nat_lit 5897774400)), (nat_lit 628, Int.ofNat (nat_lit 769123040)), (nat_lit 629, Int.ofNat (nat_lit 1724694720)), (nat_lit 647, Int.ofNat (nat_lit 333335520))]
theorem block005_data_flat158_step : block005_data_flat158 = (CoefficientMerge.fastMerge block005_data_flat078 block005_data_flat157) := by decide +kernel
theorem block005_data_flat158_original : block005_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5898088840 : Int) atom0335Coded) (CoefficientMerge.scale (6018711240 : Int) atom0336Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2000907360 : Int) atom0337Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3212404128 : Int) atom0338Coded) (CoefficientMerge.scale (2905871040 : Int) atom0339Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2903290560 : Int) atom0340Coded) (CoefficientMerge.scale (2951029440 : Int) atom0341Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3174733760 : Int) atom0342Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5883494400 : Int) atom0343Coded) (CoefficientMerge.scale (4456174040 : Int) atom0344Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6098833080 : Int) atom0345Coded) (CoefficientMerge.scale (5959982600 : Int) atom0346Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6391196200 : Int) atom0347Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6822409800 : Int) atom0348Coded) (CoefficientMerge.scale (2336973120 : Int) atom0349Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3943380288 : Int) atom0350Coded) (CoefficientMerge.scale (3334043520 : Int) atom0351Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3358235520 : Int) atom0352Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3558392960 : Int) atom0353Coded) (CoefficientMerge.scale (6159605760 : Int) atom0354Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4881594320 : Int) atom0355Coded) (CoefficientMerge.scale (6576221880 : Int) atom0356Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6516018800 : Int) atom0357Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7042158640 : Int) atom0358Coded) (CoefficientMerge.scale (7568298480 : Int) atom0359Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2731883520 : Int) atom0360Coded) (CoefficientMerge.scale (4672629120 : Int) atom0361Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3937045632 : Int) atom0362Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4045591040 : Int) atom0363Coded) (CoefficientMerge.scale (6538183680 : Int) atom0364Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5324168960 : Int) atom0365Coded) (CoefficientMerge.scale (7156077240 : Int) atom0366Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6966759680 : Int) atom0367Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7463345920 : Int) atom0368Coded) (CoefficientMerge.scale (8011165440 : Int) atom0369Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3038632320 : Int) atom0370Coded) (CoefficientMerge.scale (5210772480 : Int) atom0371Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4660776320 : Int) atom0372Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6904803360 : Int) atom0373Coded) (CoefficientMerge.scale (5640737120 : Int) atom0374Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7615402680 : Int) atom0375Coded) (CoefficientMerge.scale (7207039520 : Int) atom0376Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7686420640 : Int) atom0377Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8208003360 : Int) atom0378Coded) (CoefficientMerge.scale (3287337600 : Int) atom0379Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5911061120 : Int) atom0380Coded) (CoefficientMerge.scale (7349472480 : Int) atom0381Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5975361440 : Int) atom0382Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8125047480 : Int) atom0383Coded) (CoefficientMerge.scale (7310555360 : Int) atom0384Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7652744800 : Int) atom0385Coded) (CoefficientMerge.scale (8198641920 : Int) atom0386Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3794524160 : Int) atom0387Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850429440 : Int) atom0388Coded) (CoefficientMerge.scale (6205292800 : Int) atom0389Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8413864120 : Int) atom0390Coded) (CoefficientMerge.scale (7605570560 : Int) atom0391Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7277580800 : Int) atom0392Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8654338560 : Int) atom0393Coded) (CoefficientMerge.scale (5546741760 : Int) atom0394Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8918250880 : Int) atom0395Coded) (CoefficientMerge.scale (12516486840 : Int) atom0396Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11769116800 : Int) atom0397Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7645850240 : Int) atom0398Coded) (CoefficientMerge.scale (8873682720 : Int) atom0399Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3470027456 : Int) atom0400Coded) (CoefficientMerge.scale (9201418000 : Int) atom0401Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10093237280 : Int) atom0402Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7347075680 : Int) atom0403Coded) (CoefficientMerge.scale (7882412160 : Int) atom0404Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6708730320 : Int) atom0405Coded) (CoefficientMerge.scale (10927396240 : Int) atom0406Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8160306320 : Int) atom0407Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8967654960 : Int) atom0408Coded) (CoefficientMerge.scale (3992019360 : Int) atom0409Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5176124800 : Int) atom0410Coded) (CoefficientMerge.scale (5897774400 : Int) atom0411Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (769123040 : Int) atom0412Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1724694720 : Int) atom0413Coded) (CoefficientMerge.scale (333335520 : Int) atom0414Coded)))))))) := by
  rw [block005_data_flat158_step, block005_data_flat078_original, block005_data_flat157_original]
def block005_data_flat159 : CoefficientMerge.Poly := [(nat_lit 430, Int.ofNat (nat_lit 5898088840)), (nat_lit 431, Int.ofNat (nat_lit 6018711240)), (nat_lit 438, Int.ofNat (nat_lit 2000907360)), (nat_lit 439, Int.ofNat (nat_lit 3212404128)), (nat_lit 440, Int.ofNat (nat_lit 2905871040)), (nat_lit 441, Int.ofNat (nat_lit 2903290560)), (nat_lit 442, Int.ofNat (nat_lit 2951029440)), (nat_lit 443, Int.ofNat (nat_lit 3174733760)), (nat_lit 444, Int.ofNat (nat_lit 5883494400)), (nat_lit 445, Int.ofNat (nat_lit 4456174040)), (nat_lit 446, Int.ofNat (nat_lit 6098833080)), (nat_lit 447, Int.ofNat (nat_lit 5959982600)), (nat_lit 448, Int.ofNat (nat_lit 6391196200)), (nat_lit 449, Int.ofNat (nat_lit 6822409800)), (nat_lit 457, Int.ofNat (nat_lit 2336973120)), (nat_lit 458, Int.ofNat (nat_lit 3943380288)), (nat_lit 459, Int.ofNat (nat_lit 3334043520)), (nat_lit 460, Int.ofNat (nat_lit 3358235520)), (nat_lit 461, Int.ofNat (nat_lit 3558392960)), (nat_lit 462, Int.ofNat (nat_lit 6159605760)), (nat_lit 463, Int.ofNat (nat_lit 4881594320)), (nat_lit 464, Int.ofNat (nat_lit 6576221880)), (nat_lit 465, Int.ofNat (nat_lit 6516018800)), (nat_lit 466, Int.ofNat (nat_lit 7042158640)), (nat_lit 467, Int.ofNat (nat_lit 7568298480)), (nat_lit 476, Int.ofNat (nat_lit 2731883520)), (nat_lit 477, Int.ofNat (nat_lit 4672629120)), (nat_lit 478, Int.ofNat (nat_lit 3937045632)), (nat_lit 479, Int.ofNat (nat_lit 4045591040)), (nat_lit 480, Int.ofNat (nat_lit 6538183680)), (nat_lit 481, Int.ofNat (nat_lit 5324168960)), (nat_lit 482, Int.ofNat (nat_lit 7156077240)), (nat_lit 483, Int.ofNat (nat_lit 6966759680)), (nat_lit 484, Int.ofNat (nat_lit 7463345920)), (nat_lit 485, Int.ofNat (nat_lit 8011165440)), (nat_lit 495, Int.ofNat (nat_lit 3038632320)), (nat_lit 496, Int.ofNat (nat_lit 5210772480)), (nat_lit 497, Int.ofNat (nat_lit 4660776320)), (nat_lit 498, Int.ofNat (nat_lit 6904803360)), (nat_lit 499, Int.ofNat (nat_lit 5640737120)), (nat_lit 500, Int.ofNat (nat_lit 7615402680)), (nat_lit 501, Int.ofNat (nat_lit 7207039520)), (nat_lit 502, Int.ofNat (nat_lit 7686420640)), (nat_lit 503, Int.ofNat (nat_lit 8208003360)), (nat_lit 514, Int.ofNat (nat_lit 3287337600)), (nat_lit 515, Int.ofNat (nat_lit 5911061120)), (nat_lit 516, Int.ofNat (nat_lit 7349472480)), (nat_lit 517, Int.ofNat (nat_lit 5975361440)), (nat_lit 518, Int.ofNat (nat_lit 8125047480)), (nat_lit 519, Int.ofNat (nat_lit 7310555360)), (nat_lit 520, Int.ofNat (nat_lit 7652744800)), (nat_lit 521, Int.ofNat (nat_lit 8198641920)), (nat_lit 533, Int.ofNat (nat_lit 3794524160)), (nat_lit 534, Int.ofNat (nat_lit 7850429440)), (nat_lit 535, Int.ofNat (nat_lit 6205292800)), (nat_lit 536, Int.ofNat (nat_lit 8413864120)), (nat_lit 537, Int.ofNat (nat_lit 7605570560)), (nat_lit 538, Int.ofNat (nat_lit 7277580800)), (nat_lit 539, Int.ofNat (nat_lit 8654338560)), (nat_lit 552, Int.ofNat (nat_lit 5546741760)), (nat_lit 553, Int.ofNat (nat_lit 8918250880)), (nat_lit 554, Int.ofNat (nat_lit 12516486840)), (nat_lit 555, Int.ofNat (nat_lit 11769116800)), (nat_lit 556, Int.ofNat (nat_lit 7645850240)), (nat_lit 557, Int.ofNat (nat_lit 8873682720)), (nat_lit 571, Int.ofNat (nat_lit 3470027456)), (nat_lit 572, Int.ofNat (nat_lit 9201418000)), (nat_lit 573, Int.ofNat (nat_lit 10093237280)), (nat_lit 574, Int.ofNat (nat_lit 7347075680)), (nat_lit 575, Int.ofNat (nat_lit 7882412160)), (nat_lit 590, Int.ofNat (nat_lit 6708730320)), (nat_lit 591, Int.ofNat (nat_lit 10927396240)), (nat_lit 592, Int.ofNat (nat_lit 8160306320)), (nat_lit 593, Int.ofNat (nat_lit 8967654960)), (nat_lit 609, Int.ofNat (nat_lit 3992019360)), (nat_lit 610, Int.ofNat (nat_lit 5176124800)), (nat_lit 611, Int.ofNat (nat_lit 5897774400)), (nat_lit 628, Int.ofNat (nat_lit 769123040)), (nat_lit 629, Int.ofNat (nat_lit 1724694720)), (nat_lit 647, Int.ofNat (nat_lit 333335520))]
theorem block005_data_flat159_step : block005_data_flat159 = (CoefficientMerge.trim block005_data_flat158) := by decide +kernel
theorem block005_data_flat159_original : block005_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5898088840 : Int) atom0335Coded) (CoefficientMerge.scale (6018711240 : Int) atom0336Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2000907360 : Int) atom0337Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3212404128 : Int) atom0338Coded) (CoefficientMerge.scale (2905871040 : Int) atom0339Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2903290560 : Int) atom0340Coded) (CoefficientMerge.scale (2951029440 : Int) atom0341Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3174733760 : Int) atom0342Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5883494400 : Int) atom0343Coded) (CoefficientMerge.scale (4456174040 : Int) atom0344Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6098833080 : Int) atom0345Coded) (CoefficientMerge.scale (5959982600 : Int) atom0346Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6391196200 : Int) atom0347Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6822409800 : Int) atom0348Coded) (CoefficientMerge.scale (2336973120 : Int) atom0349Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3943380288 : Int) atom0350Coded) (CoefficientMerge.scale (3334043520 : Int) atom0351Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3358235520 : Int) atom0352Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3558392960 : Int) atom0353Coded) (CoefficientMerge.scale (6159605760 : Int) atom0354Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4881594320 : Int) atom0355Coded) (CoefficientMerge.scale (6576221880 : Int) atom0356Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6516018800 : Int) atom0357Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7042158640 : Int) atom0358Coded) (CoefficientMerge.scale (7568298480 : Int) atom0359Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2731883520 : Int) atom0360Coded) (CoefficientMerge.scale (4672629120 : Int) atom0361Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3937045632 : Int) atom0362Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4045591040 : Int) atom0363Coded) (CoefficientMerge.scale (6538183680 : Int) atom0364Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5324168960 : Int) atom0365Coded) (CoefficientMerge.scale (7156077240 : Int) atom0366Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6966759680 : Int) atom0367Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7463345920 : Int) atom0368Coded) (CoefficientMerge.scale (8011165440 : Int) atom0369Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3038632320 : Int) atom0370Coded) (CoefficientMerge.scale (5210772480 : Int) atom0371Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4660776320 : Int) atom0372Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6904803360 : Int) atom0373Coded) (CoefficientMerge.scale (5640737120 : Int) atom0374Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7615402680 : Int) atom0375Coded) (CoefficientMerge.scale (7207039520 : Int) atom0376Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7686420640 : Int) atom0377Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8208003360 : Int) atom0378Coded) (CoefficientMerge.scale (3287337600 : Int) atom0379Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5911061120 : Int) atom0380Coded) (CoefficientMerge.scale (7349472480 : Int) atom0381Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5975361440 : Int) atom0382Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8125047480 : Int) atom0383Coded) (CoefficientMerge.scale (7310555360 : Int) atom0384Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7652744800 : Int) atom0385Coded) (CoefficientMerge.scale (8198641920 : Int) atom0386Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3794524160 : Int) atom0387Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850429440 : Int) atom0388Coded) (CoefficientMerge.scale (6205292800 : Int) atom0389Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8413864120 : Int) atom0390Coded) (CoefficientMerge.scale (7605570560 : Int) atom0391Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7277580800 : Int) atom0392Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8654338560 : Int) atom0393Coded) (CoefficientMerge.scale (5546741760 : Int) atom0394Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8918250880 : Int) atom0395Coded) (CoefficientMerge.scale (12516486840 : Int) atom0396Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11769116800 : Int) atom0397Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7645850240 : Int) atom0398Coded) (CoefficientMerge.scale (8873682720 : Int) atom0399Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3470027456 : Int) atom0400Coded) (CoefficientMerge.scale (9201418000 : Int) atom0401Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10093237280 : Int) atom0402Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7347075680 : Int) atom0403Coded) (CoefficientMerge.scale (7882412160 : Int) atom0404Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6708730320 : Int) atom0405Coded) (CoefficientMerge.scale (10927396240 : Int) atom0406Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8160306320 : Int) atom0407Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8967654960 : Int) atom0408Coded) (CoefficientMerge.scale (3992019360 : Int) atom0409Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5176124800 : Int) atom0410Coded) (CoefficientMerge.scale (5897774400 : Int) atom0411Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (769123040 : Int) atom0412Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1724694720 : Int) atom0413Coded) (CoefficientMerge.scale (333335520 : Int) atom0414Coded))))))))) := by
  rw [block005_data_flat159_step, block005_data_flat158_original]
theorem block005_data : block005 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5898088840 : Int) atom0335Coded) (CoefficientMerge.scale (6018711240 : Int) atom0336Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2000907360 : Int) atom0337Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3212404128 : Int) atom0338Coded) (CoefficientMerge.scale (2905871040 : Int) atom0339Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2903290560 : Int) atom0340Coded) (CoefficientMerge.scale (2951029440 : Int) atom0341Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3174733760 : Int) atom0342Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5883494400 : Int) atom0343Coded) (CoefficientMerge.scale (4456174040 : Int) atom0344Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6098833080 : Int) atom0345Coded) (CoefficientMerge.scale (5959982600 : Int) atom0346Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6391196200 : Int) atom0347Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6822409800 : Int) atom0348Coded) (CoefficientMerge.scale (2336973120 : Int) atom0349Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3943380288 : Int) atom0350Coded) (CoefficientMerge.scale (3334043520 : Int) atom0351Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3358235520 : Int) atom0352Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3558392960 : Int) atom0353Coded) (CoefficientMerge.scale (6159605760 : Int) atom0354Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4881594320 : Int) atom0355Coded) (CoefficientMerge.scale (6576221880 : Int) atom0356Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6516018800 : Int) atom0357Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7042158640 : Int) atom0358Coded) (CoefficientMerge.scale (7568298480 : Int) atom0359Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2731883520 : Int) atom0360Coded) (CoefficientMerge.scale (4672629120 : Int) atom0361Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3937045632 : Int) atom0362Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4045591040 : Int) atom0363Coded) (CoefficientMerge.scale (6538183680 : Int) atom0364Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5324168960 : Int) atom0365Coded) (CoefficientMerge.scale (7156077240 : Int) atom0366Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6966759680 : Int) atom0367Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7463345920 : Int) atom0368Coded) (CoefficientMerge.scale (8011165440 : Int) atom0369Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3038632320 : Int) atom0370Coded) (CoefficientMerge.scale (5210772480 : Int) atom0371Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4660776320 : Int) atom0372Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6904803360 : Int) atom0373Coded) (CoefficientMerge.scale (5640737120 : Int) atom0374Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7615402680 : Int) atom0375Coded) (CoefficientMerge.scale (7207039520 : Int) atom0376Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7686420640 : Int) atom0377Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8208003360 : Int) atom0378Coded) (CoefficientMerge.scale (3287337600 : Int) atom0379Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5911061120 : Int) atom0380Coded) (CoefficientMerge.scale (7349472480 : Int) atom0381Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5975361440 : Int) atom0382Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8125047480 : Int) atom0383Coded) (CoefficientMerge.scale (7310555360 : Int) atom0384Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7652744800 : Int) atom0385Coded) (CoefficientMerge.scale (8198641920 : Int) atom0386Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3794524160 : Int) atom0387Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7850429440 : Int) atom0388Coded) (CoefficientMerge.scale (6205292800 : Int) atom0389Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8413864120 : Int) atom0390Coded) (CoefficientMerge.scale (7605570560 : Int) atom0391Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7277580800 : Int) atom0392Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8654338560 : Int) atom0393Coded) (CoefficientMerge.scale (5546741760 : Int) atom0394Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8918250880 : Int) atom0395Coded) (CoefficientMerge.scale (12516486840 : Int) atom0396Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11769116800 : Int) atom0397Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7645850240 : Int) atom0398Coded) (CoefficientMerge.scale (8873682720 : Int) atom0399Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3470027456 : Int) atom0400Coded) (CoefficientMerge.scale (9201418000 : Int) atom0401Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10093237280 : Int) atom0402Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7347075680 : Int) atom0403Coded) (CoefficientMerge.scale (7882412160 : Int) atom0404Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6708730320 : Int) atom0405Coded) (CoefficientMerge.scale (10927396240 : Int) atom0406Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8160306320 : Int) atom0407Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8967654960 : Int) atom0408Coded) (CoefficientMerge.scale (3992019360 : Int) atom0409Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5176124800 : Int) atom0410Coded) (CoefficientMerge.scale (5897774400 : Int) atom0411Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (769123040 : Int) atom0412Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1724694720 : Int) atom0413Coded) (CoefficientMerge.scale (333335520 : Int) atom0414Coded)))))))) := by
  have h : block005 = block005_data_flat159 := by decide +kernel
  exact h.trans block005_data_flat159_original
theorem block005_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) block005 := by
  rw [block005_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0335Coded_nonneg g hg hA hB) (atom0336Coded_nonneg g hg hA hB)) (add_nonneg (atom0337Coded_nonneg g hg hA hB) (add_nonneg (atom0338Coded_nonneg g hg hA hB) (atom0339Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0340Coded_nonneg g hg hA hB) (atom0341Coded_nonneg g hg hA hB)) (add_nonneg (atom0342Coded_nonneg g hg hA hB) (add_nonneg (atom0343Coded_nonneg g hg hA hB) (atom0344Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0345Coded_nonneg g hg hA hB) (atom0346Coded_nonneg g hg hA hB)) (add_nonneg (atom0347Coded_nonneg g hg hA hB) (add_nonneg (atom0348Coded_nonneg g hg hA hB) (atom0349Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0350Coded_nonneg g hg hA hB) (atom0351Coded_nonneg g hg hA hB)) (add_nonneg (atom0352Coded_nonneg g hg hA hB) (add_nonneg (atom0353Coded_nonneg g hg hA hB) (atom0354Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0355Coded_nonneg g hg hA hB) (atom0356Coded_nonneg g hg hA hB)) (add_nonneg (atom0357Coded_nonneg g hg hA hB) (add_nonneg (atom0358Coded_nonneg g hg hA hB) (atom0359Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0360Coded_nonneg g hg hA hB) (atom0361Coded_nonneg g hg hA hB)) (add_nonneg (atom0362Coded_nonneg g hg hA hB) (add_nonneg (atom0363Coded_nonneg g hg hA hB) (atom0364Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0365Coded_nonneg g hg hA hB) (atom0366Coded_nonneg g hg hA hB)) (add_nonneg (atom0367Coded_nonneg g hg hA hB) (add_nonneg (atom0368Coded_nonneg g hg hA hB) (atom0369Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0370Coded_nonneg g hg hA hB) (atom0371Coded_nonneg g hg hA hB)) (add_nonneg (atom0372Coded_nonneg g hg hA hB) (add_nonneg (atom0373Coded_nonneg g hg hA hB) (atom0374Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0375Coded_nonneg g hg hA hB) (atom0376Coded_nonneg g hg hA hB)) (add_nonneg (atom0377Coded_nonneg g hg hA hB) (add_nonneg (atom0378Coded_nonneg g hg hA hB) (atom0379Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0380Coded_nonneg g hg hA hB) (atom0381Coded_nonneg g hg hA hB)) (add_nonneg (atom0382Coded_nonneg g hg hA hB) (add_nonneg (atom0383Coded_nonneg g hg hA hB) (atom0384Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0385Coded_nonneg g hg hA hB) (atom0386Coded_nonneg g hg hA hB)) (add_nonneg (atom0387Coded_nonneg g hg hA hB) (add_nonneg (atom0388Coded_nonneg g hg hA hB) (atom0389Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0390Coded_nonneg g hg hA hB) (atom0391Coded_nonneg g hg hA hB)) (add_nonneg (atom0392Coded_nonneg g hg hA hB) (add_nonneg (atom0393Coded_nonneg g hg hA hB) (atom0394Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0395Coded_nonneg g hg hA hB) (atom0396Coded_nonneg g hg hA hB)) (add_nonneg (atom0397Coded_nonneg g hg hA hB) (add_nonneg (atom0398Coded_nonneg g hg hA hB) (atom0399Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0400Coded_nonneg g hg hA hB) (atom0401Coded_nonneg g hg hA hB)) (add_nonneg (atom0402Coded_nonneg g hg hA hB) (add_nonneg (atom0403Coded_nonneg g hg hA hB) (atom0404Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0405Coded_nonneg g hg hA hB) (atom0406Coded_nonneg g hg hA hB)) (add_nonneg (atom0407Coded_nonneg g hg hA hB) (add_nonneg (atom0408Coded_nonneg g hg hA hB) (atom0409Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0410Coded_nonneg g hg hA hB) (atom0411Coded_nonneg g hg hA hB)) (add_nonneg (atom0412Coded_nonneg g hg hA hB) (add_nonneg (atom0413Coded_nonneg g hg hA hB) (atom0414Coded_nonneg g hg hA hB))))))))

end APPT.Finite18
