-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def atom0473 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0473 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0473 = ((g 4) * (g 9) * (g 11)) := by
  norm_num [atom0473, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0473_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (159550560 : Int) atom0473) := by
  rw [SparsePolynomial.eval_scale, eval_atom0473]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0473Coded : CoefficientMerge.Poly := [(nat_lit 1046, Int.ofNat (nat_lit 1))]
theorem atom0473Coded_decode : atom0473 = SparsePolynomial.decodeCubic 15 atom0473Coded := by decide +kernel
theorem atom0473Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (159550560 : Int) atom0473Coded) := by
  have h := atom0473_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0473Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0474 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0474 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0474 = ((g 4) * (g 9) * (g 12)) := by
  norm_num [atom0474, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0474_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175445640 : Int) atom0474) := by
  rw [SparsePolynomial.eval_scale, eval_atom0474]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0474Coded : CoefficientMerge.Poly := [(nat_lit 1047, Int.ofNat (nat_lit 1))]
theorem atom0474Coded_decode : atom0474 = SparsePolynomial.decodeCubic 15 atom0474Coded := by decide +kernel
theorem atom0474Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (175445640 : Int) atom0474Coded) := by
  have h := atom0474_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0474Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0475 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0475 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0475 = ((g 4) * (g 9) * (g 13)) := by
  norm_num [atom0475, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0475_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (116951400 : Int) atom0475) := by
  rw [SparsePolynomial.eval_scale, eval_atom0475]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0475Coded : CoefficientMerge.Poly := [(nat_lit 1048, Int.ofNat (nat_lit 1))]
theorem atom0475Coded_decode : atom0475 = SparsePolynomial.decodeCubic 15 atom0475Coded := by decide +kernel
theorem atom0475Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (116951400 : Int) atom0475Coded) := by
  have h := atom0475_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0475Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0476 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0476 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0476 = ((g 4) * (g 9) * (g 14)) := by
  norm_num [atom0476, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0476_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (194537160 : Int) atom0476) := by
  rw [SparsePolynomial.eval_scale, eval_atom0476]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0476Coded : CoefficientMerge.Poly := [(nat_lit 1049, Int.ofNat (nat_lit 1))]
theorem atom0476Coded_decode : atom0476 = SparsePolynomial.decodeCubic 15 atom0476Coded := by decide +kernel
theorem atom0476Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (194537160 : Int) atom0476Coded) := by
  have h := atom0476_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0476Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0477 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0477 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0477 = ((g 4) * (g 10) * (g 10)) := by
  norm_num [atom0477, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0477_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46998144 : Int) atom0477) := by
  rw [SparsePolynomial.eval_scale, eval_atom0477]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0477Coded : CoefficientMerge.Poly := [(nat_lit 1060, Int.ofNat (nat_lit 1))]
theorem atom0477Coded_decode : atom0477 = SparsePolynomial.decodeCubic 15 atom0477Coded := by decide +kernel
theorem atom0477Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (46998144 : Int) atom0477Coded) := by
  have h := atom0477_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0477Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0478 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0478 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0478 = ((g 4) * (g 10) * (g 11)) := by
  norm_num [atom0478, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0478_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129823920 : Int) atom0478) := by
  rw [SparsePolynomial.eval_scale, eval_atom0478]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0478Coded : CoefficientMerge.Poly := [(nat_lit 1061, Int.ofNat (nat_lit 1))]
theorem atom0478Coded_decode : atom0478 = SparsePolynomial.decodeCubic 15 atom0478Coded := by decide +kernel
theorem atom0478Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (129823920 : Int) atom0478Coded) := by
  have h := atom0478_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0478Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0479 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0479 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0479 = ((g 4) * (g 10) * (g 12)) := by
  norm_num [atom0479, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0479_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (162877500 : Int) atom0479) := by
  rw [SparsePolynomial.eval_scale, eval_atom0479]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0479Coded : CoefficientMerge.Poly := [(nat_lit 1062, Int.ofNat (nat_lit 1))]
theorem atom0479Coded_decode : atom0479 = SparsePolynomial.decodeCubic 15 atom0479Coded := by decide +kernel
theorem atom0479Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (162877500 : Int) atom0479Coded) := by
  have h := atom0479_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0479Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0480 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0480 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0480 = ((g 4) * (g 10) * (g 13)) := by
  norm_num [atom0480, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0480_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (119768400 : Int) atom0480) := by
  rw [SparsePolynomial.eval_scale, eval_atom0480]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0480Coded : CoefficientMerge.Poly := [(nat_lit 1063, Int.ofNat (nat_lit 1))]
theorem atom0480Coded_decode : atom0480 = SparsePolynomial.decodeCubic 15 atom0480Coded := by decide +kernel
theorem atom0480Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (119768400 : Int) atom0480Coded) := by
  have h := atom0480_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0480Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0481 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0481 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0481 = ((g 4) * (g 10) * (g 14)) := by
  norm_num [atom0481, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0481_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (159341850 : Int) atom0481) := by
  rw [SparsePolynomial.eval_scale, eval_atom0481]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0481Coded : CoefficientMerge.Poly := [(nat_lit 1064, Int.ofNat (nat_lit 1))]
theorem atom0481Coded_decode : atom0481 = SparsePolynomial.decodeCubic 15 atom0481Coded := by decide +kernel
theorem atom0481Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (159341850 : Int) atom0481Coded) := by
  have h := atom0481_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0481Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0482 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0482 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0482 = ((g 4) * (g 11) * (g 11)) := by
  norm_num [atom0482, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0482_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (94131720 : Int) atom0482) := by
  rw [SparsePolynomial.eval_scale, eval_atom0482]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0482Coded : CoefficientMerge.Poly := [(nat_lit 1076, Int.ofNat (nat_lit 1))]
theorem atom0482Coded_decode : atom0482 = SparsePolynomial.decodeCubic 15 atom0482Coded := by decide +kernel
theorem atom0482Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (94131720 : Int) atom0482Coded) := by
  have h := atom0482_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0482Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0483 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0483 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0483 = ((g 4) * (g 11) * (g 12)) := by
  norm_num [atom0483, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0483_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (168209280 : Int) atom0483) := by
  rw [SparsePolynomial.eval_scale, eval_atom0483]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0483Coded : CoefficientMerge.Poly := [(nat_lit 1077, Int.ofNat (nat_lit 1))]
theorem atom0483Coded_decode : atom0483 = SparsePolynomial.decodeCubic 15 atom0483Coded := by decide +kernel
theorem atom0483Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (168209280 : Int) atom0483Coded) := by
  have h := atom0483_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0483Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0484 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0484 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0484 = ((g 4) * (g 11) * (g 13)) := by
  norm_num [atom0484, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0484_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (124651080 : Int) atom0484) := by
  rw [SparsePolynomial.eval_scale, eval_atom0484]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0484Coded : CoefficientMerge.Poly := [(nat_lit 1078, Int.ofNat (nat_lit 1))]
theorem atom0484Coded_decode : atom0484 = SparsePolynomial.decodeCubic 15 atom0484Coded := by decide +kernel
theorem atom0484Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (124651080 : Int) atom0484Coded) := by
  have h := atom0484_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0484Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0485 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0485 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0485 = ((g 4) * (g 11) * (g 14)) := by
  norm_num [atom0485, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0485_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (182713320 : Int) atom0485) := by
  rw [SparsePolynomial.eval_scale, eval_atom0485]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0485Coded : CoefficientMerge.Poly := [(nat_lit 1079, Int.ofNat (nat_lit 1))]
theorem atom0485Coded_decode : atom0485 = SparsePolynomial.decodeCubic 15 atom0485Coded := by decide +kernel
theorem atom0485Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (182713320 : Int) atom0485Coded) := by
  have h := atom0485_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0485Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0486 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0486 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0486 = ((g 4) * (g 12) * (g 12)) := by
  norm_num [atom0486, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0486_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61220340 : Int) atom0486) := by
  rw [SparsePolynomial.eval_scale, eval_atom0486]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0486Coded : CoefficientMerge.Poly := [(nat_lit 1092, Int.ofNat (nat_lit 1))]
theorem atom0486Coded_decode : atom0486 = SparsePolynomial.decodeCubic 15 atom0486Coded := by decide +kernel
theorem atom0486Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (61220340 : Int) atom0486Coded) := by
  have h := atom0486_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0486Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0487 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0487 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0487 = ((g 4) * (g 12) * (g 13)) := by
  norm_num [atom0487, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0487_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (93601620 : Int) atom0487) := by
  rw [SparsePolynomial.eval_scale, eval_atom0487]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0487Coded : CoefficientMerge.Poly := [(nat_lit 1093, Int.ofNat (nat_lit 1))]
theorem atom0487Coded_decode : atom0487 = SparsePolynomial.decodeCubic 15 atom0487Coded := by decide +kernel
theorem atom0487Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (93601620 : Int) atom0487Coded) := by
  have h := atom0487_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0487Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0488 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0488 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0488 = ((g 4) * (g 12) * (g 14)) := by
  norm_num [atom0488, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0488_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (161695170 : Int) atom0488) := by
  rw [SparsePolynomial.eval_scale, eval_atom0488]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0488Coded : CoefficientMerge.Poly := [(nat_lit 1094, Int.ofNat (nat_lit 1))]
theorem atom0488Coded_decode : atom0488 = SparsePolynomial.decodeCubic 15 atom0488Coded := by decide +kernel
theorem atom0488Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (161695170 : Int) atom0488Coded) := by
  have h := atom0488_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0488Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0489 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0489 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0489 = ((g 4) * (g 13) * (g 13)) := by
  norm_num [atom0489, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0489_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15015600 : Int) atom0489) := by
  rw [SparsePolynomial.eval_scale, eval_atom0489]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0489Coded : CoefficientMerge.Poly := [(nat_lit 1108, Int.ofNat (nat_lit 1))]
theorem atom0489Coded_decode : atom0489 = SparsePolynomial.decodeCubic 15 atom0489Coded := by decide +kernel
theorem atom0489Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (15015600 : Int) atom0489Coded) := by
  have h := atom0489_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0489Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0490 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0490 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0490 = ((g 4) * (g 13) * (g 14)) := by
  norm_num [atom0490, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0490_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105901830 : Int) atom0490) := by
  rw [SparsePolynomial.eval_scale, eval_atom0490]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0490Coded : CoefficientMerge.Poly := [(nat_lit 1109, Int.ofNat (nat_lit 1))]
theorem atom0490Coded_decode : atom0490 = SparsePolynomial.decodeCubic 15 atom0490Coded := by decide +kernel
theorem atom0490Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (105901830 : Int) atom0490Coded) := by
  have h := atom0490_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0490Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0491 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0491 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0491 = ((g 4) * (g 14) * (g 14)) := by
  norm_num [atom0491, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0491_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84255390 : Int) atom0491) := by
  rw [SparsePolynomial.eval_scale, eval_atom0491]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0491Coded : CoefficientMerge.Poly := [(nat_lit 1124, Int.ofNat (nat_lit 1))]
theorem atom0491Coded_decode : atom0491 = SparsePolynomial.decodeCubic 15 atom0491Coded := by decide +kernel
theorem atom0491Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (84255390 : Int) atom0491Coded) := by
  have h := atom0491_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0491Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0492 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0492 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0492 = ((g 5) * (g 5) * (g 5)) := by
  norm_num [atom0492, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0492_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (633600 : Int) atom0492) := by
  rw [SparsePolynomial.eval_scale, eval_atom0492]
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 5) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0492Coded : CoefficientMerge.Poly := [(nat_lit 1205, Int.ofNat (nat_lit 1))]
theorem atom0492Coded_decode : atom0492 = SparsePolynomial.decodeCubic 15 atom0492Coded := by decide +kernel
theorem atom0492Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (633600 : Int) atom0492Coded) := by
  have h := atom0492_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0492Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0493 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0493 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0493 = ((g 5) * (g 5) * (g 9)) := by
  norm_num [atom0493, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0493_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11719440 : Int) atom0493) := by
  rw [SparsePolynomial.eval_scale, eval_atom0493]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0493Coded : CoefficientMerge.Poly := [(nat_lit 1209, Int.ofNat (nat_lit 1))]
theorem atom0493Coded_decode : atom0493 = SparsePolynomial.decodeCubic 15 atom0493Coded := by decide +kernel
theorem atom0493Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (11719440 : Int) atom0493Coded) := by
  have h := atom0493_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0493Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0494 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0494 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0494 = ((g 5) * (g 6) * (g 6)) := by
  norm_num [atom0494, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0494_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1664640 : Int) atom0494) := by
  rw [SparsePolynomial.eval_scale, eval_atom0494]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0494Coded : CoefficientMerge.Poly := [(nat_lit 1221, Int.ofNat (nat_lit 1))]
theorem atom0494Coded_decode : atom0494 = SparsePolynomial.decodeCubic 15 atom0494Coded := by decide +kernel
theorem atom0494Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1664640 : Int) atom0494Coded) := by
  have h := atom0494_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0494Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0495 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0495 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0495 = ((g 5) * (g 6) * (g 7)) := by
  norm_num [atom0495, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0495_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5230080 : Int) atom0495) := by
  rw [SparsePolynomial.eval_scale, eval_atom0495]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0495Coded : CoefficientMerge.Poly := [(nat_lit 1222, Int.ofNat (nat_lit 1))]
theorem atom0495Coded_decode : atom0495 = SparsePolynomial.decodeCubic 15 atom0495Coded := by decide +kernel
theorem atom0495Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (5230080 : Int) atom0495Coded) := by
  have h := atom0495_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0495Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0496 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0496 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0496 = ((g 5) * (g 6) * (g 8)) := by
  norm_num [atom0496, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0496_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7130880 : Int) atom0496) := by
  rw [SparsePolynomial.eval_scale, eval_atom0496]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0496Coded : CoefficientMerge.Poly := [(nat_lit 1223, Int.ofNat (nat_lit 1))]
theorem atom0496Coded_decode : atom0496 = SparsePolynomial.decodeCubic 15 atom0496Coded := by decide +kernel
theorem atom0496Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (7130880 : Int) atom0496Coded) := by
  have h := atom0496_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0496Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0497 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0497 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0497 = ((g 5) * (g 6) * (g 9)) := by
  norm_num [atom0497, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0497_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17790048 : Int) atom0497) := by
  rw [SparsePolynomial.eval_scale, eval_atom0497]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0497Coded : CoefficientMerge.Poly := [(nat_lit 1224, Int.ofNat (nat_lit 1))]
theorem atom0497Coded_decode : atom0497 = SparsePolynomial.decodeCubic 15 atom0497Coded := by decide +kernel
theorem atom0497Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (17790048 : Int) atom0497Coded) := by
  have h := atom0497_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0497Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0498 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0498 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0498 = ((g 5) * (g 6) * (g 12)) := by
  norm_num [atom0498, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0498_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15029280 : Int) atom0498) := by
  rw [SparsePolynomial.eval_scale, eval_atom0498]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0498Coded : CoefficientMerge.Poly := [(nat_lit 1227, Int.ofNat (nat_lit 1))]
theorem atom0498Coded_decode : atom0498 = SparsePolynomial.decodeCubic 15 atom0498Coded := by decide +kernel
theorem atom0498Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (15029280 : Int) atom0498Coded) := by
  have h := atom0498_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0498Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0499 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0499 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0499 = ((g 5) * (g 6) * (g 13)) := by
  norm_num [atom0499, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0499_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31033728 : Int) atom0499) := by
  rw [SparsePolynomial.eval_scale, eval_atom0499]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0499Coded : CoefficientMerge.Poly := [(nat_lit 1228, Int.ofNat (nat_lit 1))]
theorem atom0499Coded_decode : atom0499 = SparsePolynomial.decodeCubic 15 atom0499Coded := by decide +kernel
theorem atom0499Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (31033728 : Int) atom0499Coded) := by
  have h := atom0499_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0499Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0500 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0500 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0500 = ((g 5) * (g 6) * (g 14)) := by
  norm_num [atom0500, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0500_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50347440 : Int) atom0500) := by
  rw [SparsePolynomial.eval_scale, eval_atom0500]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0500Coded : CoefficientMerge.Poly := [(nat_lit 1229, Int.ofNat (nat_lit 1))]
theorem atom0500Coded_decode : atom0500 = SparsePolynomial.decodeCubic 15 atom0500Coded := by decide +kernel
theorem atom0500Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (50347440 : Int) atom0500Coded) := by
  have h := atom0500_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0500Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0501 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0501 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0501 = ((g 5) * (g 7) * (g 7)) := by
  norm_num [atom0501, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0501_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7777920 : Int) atom0501) := by
  rw [SparsePolynomial.eval_scale, eval_atom0501]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0501Coded : CoefficientMerge.Poly := [(nat_lit 1237, Int.ofNat (nat_lit 1))]
theorem atom0501Coded_decode : atom0501 = SparsePolynomial.decodeCubic 15 atom0501Coded := by decide +kernel
theorem atom0501Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (7777920 : Int) atom0501Coded) := by
  have h := atom0501_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0501Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0502 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0502 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0502 = ((g 5) * (g 7) * (g 8)) := by
  norm_num [atom0502, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0502_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18124800 : Int) atom0502) := by
  rw [SparsePolynomial.eval_scale, eval_atom0502]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0502Coded : CoefficientMerge.Poly := [(nat_lit 1238, Int.ofNat (nat_lit 1))]
theorem atom0502Coded_decode : atom0502 = SparsePolynomial.decodeCubic 15 atom0502Coded := by decide +kernel
theorem atom0502Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (18124800 : Int) atom0502Coded) := by
  have h := atom0502_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0502Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0503 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0503 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0503 = ((g 5) * (g 7) * (g 9)) := by
  norm_num [atom0503, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0503_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25904640 : Int) atom0503) := by
  rw [SparsePolynomial.eval_scale, eval_atom0503]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0503Coded : CoefficientMerge.Poly := [(nat_lit 1239, Int.ofNat (nat_lit 1))]
theorem atom0503Coded_decode : atom0503 = SparsePolynomial.decodeCubic 15 atom0503Coded := by decide +kernel
theorem atom0503Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (25904640 : Int) atom0503Coded) := by
  have h := atom0503_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0503Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0504 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0504 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0504 = ((g 5) * (g 7) * (g 10)) := by
  norm_num [atom0504, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0504_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16650960 : Int) atom0504) := by
  rw [SparsePolynomial.eval_scale, eval_atom0504]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0504Coded : CoefficientMerge.Poly := [(nat_lit 1240, Int.ofNat (nat_lit 1))]
theorem atom0504Coded_decode : atom0504 = SparsePolynomial.decodeCubic 15 atom0504Coded := by decide +kernel
theorem atom0504Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (16650960 : Int) atom0504Coded) := by
  have h := atom0504_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0504Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0505 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0505 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0505 = ((g 5) * (g 7) * (g 11)) := by
  norm_num [atom0505, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0505_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23597280 : Int) atom0505) := by
  rw [SparsePolynomial.eval_scale, eval_atom0505]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0505Coded : CoefficientMerge.Poly := [(nat_lit 1241, Int.ofNat (nat_lit 1))]
theorem atom0505Coded_decode : atom0505 = SparsePolynomial.decodeCubic 15 atom0505Coded := by decide +kernel
theorem atom0505Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (23597280 : Int) atom0505Coded) := by
  have h := atom0505_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0505Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0506 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0506 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0506 = ((g 5) * (g 7) * (g 12)) := by
  norm_num [atom0506, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0506_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40870320 : Int) atom0506) := by
  rw [SparsePolynomial.eval_scale, eval_atom0506]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0506Coded : CoefficientMerge.Poly := [(nat_lit 1242, Int.ofNat (nat_lit 1))]
theorem atom0506Coded_decode : atom0506 = SparsePolynomial.decodeCubic 15 atom0506Coded := by decide +kernel
theorem atom0506Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (40870320 : Int) atom0506Coded) := by
  have h := atom0506_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0506Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0507 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0507 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0507 = ((g 5) * (g 7) * (g 13)) := by
  norm_num [atom0507, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0507_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62623920 : Int) atom0507) := by
  rw [SparsePolynomial.eval_scale, eval_atom0507]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0507Coded : CoefficientMerge.Poly := [(nat_lit 1243, Int.ofNat (nat_lit 1))]
theorem atom0507Coded_decode : atom0507 = SparsePolynomial.decodeCubic 15 atom0507Coded := by decide +kernel
theorem atom0507Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (62623920 : Int) atom0507Coded) := by
  have h := atom0507_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0507Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0508 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0508 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0508 = ((g 5) * (g 7) * (g 14)) := by
  norm_num [atom0508, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0508_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87616080 : Int) atom0508) := by
  rw [SparsePolynomial.eval_scale, eval_atom0508]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0508Coded : CoefficientMerge.Poly := [(nat_lit 1244, Int.ofNat (nat_lit 1))]
theorem atom0508Coded_decode : atom0508 = SparsePolynomial.decodeCubic 15 atom0508Coded := by decide +kernel
theorem atom0508Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (87616080 : Int) atom0508Coded) := by
  have h := atom0508_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0508Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0509 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0509 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0509 = ((g 5) * (g 8) * (g 8)) := by
  norm_num [atom0509, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0509_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16473600 : Int) atom0509) := by
  rw [SparsePolynomial.eval_scale, eval_atom0509]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0509Coded : CoefficientMerge.Poly := [(nat_lit 1253, Int.ofNat (nat_lit 1))]
theorem atom0509Coded_decode : atom0509 = SparsePolynomial.decodeCubic 15 atom0509Coded := by decide +kernel
theorem atom0509Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (16473600 : Int) atom0509Coded) := by
  have h := atom0509_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0509Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0510 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0510 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0510 = ((g 5) * (g 8) * (g 9)) := by
  norm_num [atom0510, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0510_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43397280 : Int) atom0510) := by
  rw [SparsePolynomial.eval_scale, eval_atom0510]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0510Coded : CoefficientMerge.Poly := [(nat_lit 1254, Int.ofNat (nat_lit 1))]
theorem atom0510Coded_decode : atom0510 = SparsePolynomial.decodeCubic 15 atom0510Coded := by decide +kernel
theorem atom0510Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (43397280 : Int) atom0510Coded) := by
  have h := atom0510_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0510Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0511 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0511 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0511 = ((g 5) * (g 8) * (g 10)) := by
  norm_num [atom0511, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0511_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36727920 : Int) atom0511) := by
  rw [SparsePolynomial.eval_scale, eval_atom0511]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0511Coded : CoefficientMerge.Poly := [(nat_lit 1255, Int.ofNat (nat_lit 1))]
theorem atom0511Coded_decode : atom0511 = SparsePolynomial.decodeCubic 15 atom0511Coded := by decide +kernel
theorem atom0511Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (36727920 : Int) atom0511Coded) := by
  have h := atom0511_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0511Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0512 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0512 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0512 = ((g 5) * (g 8) * (g 11)) := by
  norm_num [atom0512, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0512_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52757280 : Int) atom0512) := by
  rw [SparsePolynomial.eval_scale, eval_atom0512]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0512Coded : CoefficientMerge.Poly := [(nat_lit 1256, Int.ofNat (nat_lit 1))]
theorem atom0512Coded_decode : atom0512 = SparsePolynomial.decodeCubic 15 atom0512Coded := by decide +kernel
theorem atom0512Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (52757280 : Int) atom0512Coded) := by
  have h := atom0512_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0512Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0513 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0513 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0513 = ((g 5) * (g 8) * (g 12)) := by
  norm_num [atom0513, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0513_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (73305360 : Int) atom0513) := by
  rw [SparsePolynomial.eval_scale, eval_atom0513]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0513Coded : CoefficientMerge.Poly := [(nat_lit 1257, Int.ofNat (nat_lit 1))]
theorem atom0513Coded_decode : atom0513 = SparsePolynomial.decodeCubic 15 atom0513Coded := by decide +kernel
theorem atom0513Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (73305360 : Int) atom0513Coded) := by
  have h := atom0513_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0513Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0514 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0514 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0514 = ((g 5) * (g 8) * (g 13)) := by
  norm_num [atom0514, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0514_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (86870160 : Int) atom0514) := by
  rw [SparsePolynomial.eval_scale, eval_atom0514]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0514Coded : CoefficientMerge.Poly := [(nat_lit 1258, Int.ofNat (nat_lit 1))]
theorem atom0514Coded_decode : atom0514 = SparsePolynomial.decodeCubic 15 atom0514Coded := by decide +kernel
theorem atom0514Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (86870160 : Int) atom0514Coded) := by
  have h := atom0514_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0514Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0515 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0515 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0515 = ((g 5) * (g 8) * (g 14)) := by
  norm_num [atom0515, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0515_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142287840 : Int) atom0515) := by
  rw [SparsePolynomial.eval_scale, eval_atom0515]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0515Coded : CoefficientMerge.Poly := [(nat_lit 1259, Int.ofNat (nat_lit 1))]
theorem atom0515Coded_decode : atom0515 = SparsePolynomial.decodeCubic 15 atom0515Coded := by decide +kernel
theorem atom0515Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (142287840 : Int) atom0515Coded) := by
  have h := atom0515_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0515Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0516 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0516 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0516 = ((g 5) * (g 9) * (g 9)) := by
  norm_num [atom0516, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0516_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44323200 : Int) atom0516) := by
  rw [SparsePolynomial.eval_scale, eval_atom0516]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0516Coded : CoefficientMerge.Poly := [(nat_lit 1269, Int.ofNat (nat_lit 1))]
theorem atom0516Coded_decode : atom0516 = SparsePolynomial.decodeCubic 15 atom0516Coded := by decide +kernel
theorem atom0516Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (44323200 : Int) atom0516Coded) := by
  have h := atom0516_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0516Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0517 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0517 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0517 = ((g 5) * (g 9) * (g 10)) := by
  norm_num [atom0517, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0517_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82846440 : Int) atom0517) := by
  rw [SparsePolynomial.eval_scale, eval_atom0517]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0517Coded : CoefficientMerge.Poly := [(nat_lit 1270, Int.ofNat (nat_lit 1))]
theorem atom0517Coded_decode : atom0517 = SparsePolynomial.decodeCubic 15 atom0517Coded := by decide +kernel
theorem atom0517Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (82846440 : Int) atom0517Coded) := by
  have h := atom0517_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0517Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0518 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0518 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0518 = ((g 5) * (g 9) * (g 11)) := by
  norm_num [atom0518, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0518_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142823520 : Int) atom0518) := by
  rw [SparsePolynomial.eval_scale, eval_atom0518]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0518Coded : CoefficientMerge.Poly := [(nat_lit 1271, Int.ofNat (nat_lit 1))]
theorem atom0518Coded_decode : atom0518 = SparsePolynomial.decodeCubic 15 atom0518Coded := by decide +kernel
theorem atom0518Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (142823520 : Int) atom0518Coded) := by
  have h := atom0518_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0518Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0519 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0519 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0519 = ((g 5) * (g 9) * (g 12)) := by
  norm_num [atom0519, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0519_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (167162040 : Int) atom0519) := by
  rw [SparsePolynomial.eval_scale, eval_atom0519]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0519Coded : CoefficientMerge.Poly := [(nat_lit 1272, Int.ofNat (nat_lit 1))]
theorem atom0519Coded_decode : atom0519 = SparsePolynomial.decodeCubic 15 atom0519Coded := by decide +kernel
theorem atom0519Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (167162040 : Int) atom0519Coded) := by
  have h := atom0519_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0519Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0520 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0520 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0520 = ((g 5) * (g 9) * (g 13)) := by
  norm_num [atom0520, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0520_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (115337880 : Int) atom0520) := by
  rw [SparsePolynomial.eval_scale, eval_atom0520]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0520Coded : CoefficientMerge.Poly := [(nat_lit 1273, Int.ofNat (nat_lit 1))]
theorem atom0520Coded_decode : atom0520 = SparsePolynomial.decodeCubic 15 atom0520Coded := by decide +kernel
theorem atom0520Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (115337880 : Int) atom0520Coded) := by
  have h := atom0520_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0520Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0521 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0521 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0521 = ((g 5) * (g 9) * (g 14)) := by
  norm_num [atom0521, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0521_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (199593720 : Int) atom0521) := by
  rw [SparsePolynomial.eval_scale, eval_atom0521]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0521Coded : CoefficientMerge.Poly := [(nat_lit 1274, Int.ofNat (nat_lit 1))]
theorem atom0521Coded_decode : atom0521 = SparsePolynomial.decodeCubic 15 atom0521Coded := by decide +kernel
theorem atom0521Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (199593720 : Int) atom0521Coded) := by
  have h := atom0521_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0521Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0522 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0522 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0522 = ((g 5) * (g 10) * (g 10)) := by
  norm_num [atom0522, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0522_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36733824 : Int) atom0522) := by
  rw [SparsePolynomial.eval_scale, eval_atom0522]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0522Coded : CoefficientMerge.Poly := [(nat_lit 1285, Int.ofNat (nat_lit 1))]
theorem atom0522Coded_decode : atom0522 = SparsePolynomial.decodeCubic 15 atom0522Coded := by decide +kernel
theorem atom0522Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (36733824 : Int) atom0522Coded) := by
  have h := atom0522_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0522Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0523 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0523 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0523 = ((g 5) * (g 10) * (g 11)) := by
  norm_num [atom0523, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0523_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (114498720 : Int) atom0523) := by
  rw [SparsePolynomial.eval_scale, eval_atom0523]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0523Coded : CoefficientMerge.Poly := [(nat_lit 1286, Int.ofNat (nat_lit 1))]
theorem atom0523Coded_decode : atom0523 = SparsePolynomial.decodeCubic 15 atom0523Coded := by decide +kernel
theorem atom0523Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (114498720 : Int) atom0523Coded) := by
  have h := atom0523_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0523Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0524 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0524 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0524 = ((g 5) * (g 10) * (g 12)) := by
  norm_num [atom0524, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0524_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154214820 : Int) atom0524) := by
  rw [SparsePolynomial.eval_scale, eval_atom0524]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0524Coded : CoefficientMerge.Poly := [(nat_lit 1287, Int.ofNat (nat_lit 1))]
theorem atom0524Coded_decode : atom0524 = SparsePolynomial.decodeCubic 15 atom0524Coded := by decide +kernel
theorem atom0524Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (154214820 : Int) atom0524Coded) := by
  have h := atom0524_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0524Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0525 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0525 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0525 = ((g 5) * (g 10) * (g 13)) := by
  norm_num [atom0525, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0525_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (117768240 : Int) atom0525) := by
  rw [SparsePolynomial.eval_scale, eval_atom0525]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0525Coded : CoefficientMerge.Poly := [(nat_lit 1288, Int.ofNat (nat_lit 1))]
theorem atom0525Coded_decode : atom0525 = SparsePolynomial.decodeCubic 15 atom0525Coded := by decide +kernel
theorem atom0525Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (117768240 : Int) atom0525Coded) := by
  have h := atom0525_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0525Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0526 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0526 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0526 = ((g 5) * (g 10) * (g 14)) := by
  norm_num [atom0526, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0526_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (164733750 : Int) atom0526) := by
  rw [SparsePolynomial.eval_scale, eval_atom0526]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0526Coded : CoefficientMerge.Poly := [(nat_lit 1289, Int.ofNat (nat_lit 1))]
theorem atom0526Coded_decode : atom0526 = SparsePolynomial.decodeCubic 15 atom0526Coded := by decide +kernel
theorem atom0526Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (164733750 : Int) atom0526Coded) := by
  have h := atom0526_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0526Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0527 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0527 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0527 = ((g 5) * (g 11) * (g 11)) := by
  norm_num [atom0527, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0527_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90088200 : Int) atom0527) := by
  rw [SparsePolynomial.eval_scale, eval_atom0527]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0527Coded : CoefficientMerge.Poly := [(nat_lit 1301, Int.ofNat (nat_lit 1))]
theorem atom0527Coded_decode : atom0527 = SparsePolynomial.decodeCubic 15 atom0527Coded := by decide +kernel
theorem atom0527Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (90088200 : Int) atom0527Coded) := by
  have h := atom0527_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0527Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0528 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0528 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0528 = ((g 5) * (g 11) * (g 12)) := by
  norm_num [atom0528, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0528_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (167922000 : Int) atom0528) := by
  rw [SparsePolynomial.eval_scale, eval_atom0528]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0528Coded : CoefficientMerge.Poly := [(nat_lit 1302, Int.ofNat (nat_lit 1))]
theorem atom0528Coded_decode : atom0528 = SparsePolynomial.decodeCubic 15 atom0528Coded := by decide +kernel
theorem atom0528Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (167922000 : Int) atom0528Coded) := by
  have h := atom0528_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0528Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0529 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0529 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0529 = ((g 5) * (g 11) * (g 13)) := by
  norm_num [atom0529, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0529_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (133936920 : Int) atom0529) := by
  rw [SparsePolynomial.eval_scale, eval_atom0529]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0529Coded : CoefficientMerge.Poly := [(nat_lit 1303, Int.ofNat (nat_lit 1))]
theorem atom0529Coded_decode : atom0529 = SparsePolynomial.decodeCubic 15 atom0529Coded := by decide +kernel
theorem atom0529Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (133936920 : Int) atom0529Coded) := by
  have h := atom0529_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0529Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0530 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0530 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0530 = ((g 5) * (g 11) * (g 14)) := by
  norm_num [atom0530, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0530_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (201572280 : Int) atom0530) := by
  rw [SparsePolynomial.eval_scale, eval_atom0530]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0530Coded : CoefficientMerge.Poly := [(nat_lit 1304, Int.ofNat (nat_lit 1))]
theorem atom0530Coded_decode : atom0530 = SparsePolynomial.decodeCubic 15 atom0530Coded := by decide +kernel
theorem atom0530Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (201572280 : Int) atom0530Coded) := by
  have h := atom0530_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0530Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0531 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0531 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0531 = ((g 5) * (g 12) * (g 12)) := by
  norm_num [atom0531, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0531_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62318700 : Int) atom0531) := by
  rw [SparsePolynomial.eval_scale, eval_atom0531]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0531Coded : CoefficientMerge.Poly := [(nat_lit 1317, Int.ofNat (nat_lit 1))]
theorem atom0531Coded_decode : atom0531 = SparsePolynomial.decodeCubic 15 atom0531Coded := by decide +kernel
theorem atom0531Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (62318700 : Int) atom0531Coded) := by
  have h := atom0531_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0531Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0532 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0532 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0532 = ((g 5) * (g 12) * (g 13)) := by
  norm_num [atom0532, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0532_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105936300 : Int) atom0532) := by
  rw [SparsePolynomial.eval_scale, eval_atom0532]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0532Coded : CoefficientMerge.Poly := [(nat_lit 1318, Int.ofNat (nat_lit 1))]
theorem atom0532Coded_decode : atom0532 = SparsePolynomial.decodeCubic 15 atom0532Coded := by decide +kernel
theorem atom0532Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (105936300 : Int) atom0532Coded) := by
  have h := atom0532_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0532Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0533 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0533 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0533 = ((g 5) * (g 12) * (g 14)) := by
  norm_num [atom0533, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0533_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (184546350 : Int) atom0533) := by
  rw [SparsePolynomial.eval_scale, eval_atom0533]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0533Coded : CoefficientMerge.Poly := [(nat_lit 1319, Int.ofNat (nat_lit 1))]
theorem atom0533Coded_decode : atom0533 = SparsePolynomial.decodeCubic 15 atom0533Coded := by decide +kernel
theorem atom0533Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (184546350 : Int) atom0533Coded) := by
  have h := atom0533_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0533Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0534 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0534 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0534 = ((g 5) * (g 13) * (g 13)) := by
  norm_num [atom0534, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0534_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24480720 : Int) atom0534) := by
  rw [SparsePolynomial.eval_scale, eval_atom0534]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0534Coded : CoefficientMerge.Poly := [(nat_lit 1333, Int.ofNat (nat_lit 1))]
theorem atom0534Coded_decode : atom0534 = SparsePolynomial.decodeCubic 15 atom0534Coded := by decide +kernel
theorem atom0534Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (24480720 : Int) atom0534Coded) := by
  have h := atom0534_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0534Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0535 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0535 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0535 = ((g 5) * (g 13) * (g 14)) := by
  norm_num [atom0535, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0535_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (136735290 : Int) atom0535) := by
  rw [SparsePolynomial.eval_scale, eval_atom0535]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0535Coded : CoefficientMerge.Poly := [(nat_lit 1334, Int.ofNat (nat_lit 1))]
theorem atom0535Coded_decode : atom0535 = SparsePolynomial.decodeCubic 15 atom0535Coded := by decide +kernel
theorem atom0535Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (136735290 : Int) atom0535Coded) := by
  have h := atom0535_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0535Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0536 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0536 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0536 = ((g 5) * (g 14) * (g 14)) := by
  norm_num [atom0536, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0536_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103787730 : Int) atom0536) := by
  rw [SparsePolynomial.eval_scale, eval_atom0536]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0536Coded : CoefficientMerge.Poly := [(nat_lit 1349, Int.ofNat (nat_lit 1))]
theorem atom0536Coded_decode : atom0536 = SparsePolynomial.decodeCubic 15 atom0536Coded := by decide +kernel
theorem atom0536Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (103787730 : Int) atom0536Coded) := by
  have h := atom0536_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0536Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0537 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0537 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0537 = ((g 6) * (g 6) * (g 9)) := by
  norm_num [atom0537, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0537_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5095440 : Int) atom0537) := by
  rw [SparsePolynomial.eval_scale, eval_atom0537]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0537Coded : CoefficientMerge.Poly := [(nat_lit 1449, Int.ofNat (nat_lit 1))]
theorem atom0537Coded_decode : atom0537 = SparsePolynomial.decodeCubic 15 atom0537Coded := by decide +kernel
theorem atom0537Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (5095440 : Int) atom0537Coded) := by
  have h := atom0537_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0537Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0538 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0538 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0538 = ((g 6) * (g 7) * (g 7)) := by
  norm_num [atom0538, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0538_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2311680 : Int) atom0538) := by
  rw [SparsePolynomial.eval_scale, eval_atom0538]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0538Coded : CoefficientMerge.Poly := [(nat_lit 1462, Int.ofNat (nat_lit 1))]
theorem atom0538Coded_decode : atom0538 = SparsePolynomial.decodeCubic 15 atom0538Coded := by decide +kernel
theorem atom0538Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (2311680 : Int) atom0538Coded) := by
  have h := atom0538_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0538Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0539 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0539 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0539 = ((g 6) * (g 7) * (g 8)) := by
  norm_num [atom0539, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0539_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6483840 : Int) atom0539) := by
  rw [SparsePolynomial.eval_scale, eval_atom0539]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0539Coded : CoefficientMerge.Poly := [(nat_lit 1463, Int.ofNat (nat_lit 1))]
theorem atom0539Coded_decode : atom0539 = SparsePolynomial.decodeCubic 15 atom0539Coded := by decide +kernel
theorem atom0539Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (6483840 : Int) atom0539Coded) := by
  have h := atom0539_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0539Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0540 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0540 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0540 = ((g 6) * (g 7) * (g 9)) := by
  norm_num [atom0540, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0540_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5747088 : Int) atom0540) := by
  rw [SparsePolynomial.eval_scale, eval_atom0540]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0540Coded : CoefficientMerge.Poly := [(nat_lit 1464, Int.ofNat (nat_lit 1))]
theorem atom0540Coded_decode : atom0540 = SparsePolynomial.decodeCubic 15 atom0540Coded := by decide +kernel
theorem atom0540Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (5747088 : Int) atom0540Coded) := by
  have h := atom0540_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0540Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0541 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0541 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0541 = ((g 6) * (g 7) * (g 11)) := by
  norm_num [atom0541, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0541_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (319440 : Int) atom0541) := by
  rw [SparsePolynomial.eval_scale, eval_atom0541]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0541Coded : CoefficientMerge.Poly := [(nat_lit 1466, Int.ofNat (nat_lit 1))]
theorem atom0541Coded_decode : atom0541 = SparsePolynomial.decodeCubic 15 atom0541Coded := by decide +kernel
theorem atom0541Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (319440 : Int) atom0541Coded) := by
  have h := atom0541_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0541Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0542 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0542 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0542 = ((g 6) * (g 7) * (g 12)) := by
  norm_num [atom0542, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0542_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15514560 : Int) atom0542) := by
  rw [SparsePolynomial.eval_scale, eval_atom0542]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0542Coded : CoefficientMerge.Poly := [(nat_lit 1467, Int.ofNat (nat_lit 1))]
theorem atom0542Coded_decode : atom0542 = SparsePolynomial.decodeCubic 15 atom0542Coded := by decide +kernel
theorem atom0542Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (15514560 : Int) atom0542Coded) := by
  have h := atom0542_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0542Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0543 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0543 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0543 = ((g 6) * (g 7) * (g 13)) := by
  norm_num [atom0543, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0543_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31680768 : Int) atom0543) := by
  rw [SparsePolynomial.eval_scale, eval_atom0543]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0543Coded : CoefficientMerge.Poly := [(nat_lit 1468, Int.ofNat (nat_lit 1))]
theorem atom0543Coded_decode : atom0543 = SparsePolynomial.decodeCubic 15 atom0543Coded := by decide +kernel
theorem atom0543Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (31680768 : Int) atom0543Coded) := by
  have h := atom0543_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0543Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0544 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0544 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0544 = ((g 6) * (g 7) * (g 14)) := by
  norm_num [atom0544, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0544_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51075360 : Int) atom0544) := by
  rw [SparsePolynomial.eval_scale, eval_atom0544]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0544Coded : CoefficientMerge.Poly := [(nat_lit 1469, Int.ofNat (nat_lit 1))]
theorem atom0544Coded_decode : atom0544 = SparsePolynomial.decodeCubic 15 atom0544Coded := by decide +kernel
theorem atom0544Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (51075360 : Int) atom0544Coded) := by
  have h := atom0544_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0544Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0545 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0545 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0545 = ((g 6) * (g 8) * (g 8)) := by
  norm_num [atom0545, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0545_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8398080 : Int) atom0545) := by
  rw [SparsePolynomial.eval_scale, eval_atom0545]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0545Coded : CoefficientMerge.Poly := [(nat_lit 1478, Int.ofNat (nat_lit 1))]
theorem atom0545Coded_decode : atom0545 = SparsePolynomial.decodeCubic 15 atom0545Coded := by decide +kernel
theorem atom0545Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (8398080 : Int) atom0545Coded) := by
  have h := atom0545_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0545Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0546 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0546 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0546 = ((g 6) * (g 8) * (g 9)) := by
  norm_num [atom0546, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0546_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16403040 : Int) atom0546) := by
  rw [SparsePolynomial.eval_scale, eval_atom0546]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0546Coded : CoefficientMerge.Poly := [(nat_lit 1479, Int.ofNat (nat_lit 1))]
theorem atom0546Coded_decode : atom0546 = SparsePolynomial.decodeCubic 15 atom0546Coded := by decide +kernel
theorem atom0546Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (16403040 : Int) atom0546Coded) := by
  have h := atom0546_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0546Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0547 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0547 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0547 = ((g 6) * (g 8) * (g 10)) := by
  norm_num [atom0547, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0547_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12962160 : Int) atom0547) := by
  rw [SparsePolynomial.eval_scale, eval_atom0547]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0547Coded : CoefficientMerge.Poly := [(nat_lit 1480, Int.ofNat (nat_lit 1))]
theorem atom0547Coded_decode : atom0547 = SparsePolynomial.decodeCubic 15 atom0547Coded := by decide +kernel
theorem atom0547Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (12962160 : Int) atom0547Coded) := by
  have h := atom0547_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0547Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0548 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0548 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0548 = ((g 6) * (g 8) * (g 11)) := by
  norm_num [atom0548, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0548_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26183520 : Int) atom0548) := by
  rw [SparsePolynomial.eval_scale, eval_atom0548]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0548Coded : CoefficientMerge.Poly := [(nat_lit 1481, Int.ofNat (nat_lit 1))]
theorem atom0548Coded_decode : atom0548 = SparsePolynomial.decodeCubic 15 atom0548Coded := by decide +kernel
theorem atom0548Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (26183520 : Int) atom0548Coded) := by
  have h := atom0548_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0548Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0549 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0549 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0549 = ((g 6) * (g 8) * (g 12)) := by
  norm_num [atom0549, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0549_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47159280 : Int) atom0549) := by
  rw [SparsePolynomial.eval_scale, eval_atom0549]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0549Coded : CoefficientMerge.Poly := [(nat_lit 1482, Int.ofNat (nat_lit 1))]
theorem atom0549Coded_decode : atom0549 = SparsePolynomial.decodeCubic 15 atom0549Coded := by decide +kernel
theorem atom0549Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (47159280 : Int) atom0549Coded) := by
  have h := atom0549_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0549Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0550 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0550 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0550 = ((g 6) * (g 8) * (g 13)) := by
  norm_num [atom0550, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0550_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61739280 : Int) atom0550) := by
  rw [SparsePolynomial.eval_scale, eval_atom0550]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0550Coded : CoefficientMerge.Poly := [(nat_lit 1483, Int.ofNat (nat_lit 1))]
theorem atom0550Coded_decode : atom0550 = SparsePolynomial.decodeCubic 15 atom0550Coded := by decide +kernel
theorem atom0550Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (61739280 : Int) atom0550Coded) := by
  have h := atom0550_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0550Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0551 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0551 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0551 = ((g 6) * (g 8) * (g 14)) := by
  norm_num [atom0551, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0551_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (119553840 : Int) atom0551) := by
  rw [SparsePolynomial.eval_scale, eval_atom0551]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0551Coded : CoefficientMerge.Poly := [(nat_lit 1484, Int.ofNat (nat_lit 1))]
theorem atom0551Coded_decode : atom0551 = SparsePolynomial.decodeCubic 15 atom0551Coded := by decide +kernel
theorem atom0551Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (119553840 : Int) atom0551Coded) := by
  have h := atom0551_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0551Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0552 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0552 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0552 = ((g 6) * (g 9) * (g 9)) := by
  norm_num [atom0552, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0552_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29030400 : Int) atom0552) := by
  rw [SparsePolynomial.eval_scale, eval_atom0552]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0552Coded : CoefficientMerge.Poly := [(nat_lit 1494, Int.ofNat (nat_lit 1))]
theorem atom0552Coded_decode : atom0552 = SparsePolynomial.decodeCubic 15 atom0552Coded := by decide +kernel
theorem atom0552Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (29030400 : Int) atom0552Coded) := by
  have h := atom0552_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0552Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block006 : CoefficientMerge.Poly := [(nat_lit 1046, Int.ofNat (nat_lit 159550560)), (nat_lit 1047, Int.ofNat (nat_lit 175445640)), (nat_lit 1048, Int.ofNat (nat_lit 116951400)), (nat_lit 1049, Int.ofNat (nat_lit 194537160)), (nat_lit 1060, Int.ofNat (nat_lit 46998144)), (nat_lit 1061, Int.ofNat (nat_lit 129823920)), (nat_lit 1062, Int.ofNat (nat_lit 162877500)), (nat_lit 1063, Int.ofNat (nat_lit 119768400)), (nat_lit 1064, Int.ofNat (nat_lit 159341850)), (nat_lit 1076, Int.ofNat (nat_lit 94131720)), (nat_lit 1077, Int.ofNat (nat_lit 168209280)), (nat_lit 1078, Int.ofNat (nat_lit 124651080)), (nat_lit 1079, Int.ofNat (nat_lit 182713320)), (nat_lit 1092, Int.ofNat (nat_lit 61220340)), (nat_lit 1093, Int.ofNat (nat_lit 93601620)), (nat_lit 1094, Int.ofNat (nat_lit 161695170)), (nat_lit 1108, Int.ofNat (nat_lit 15015600)), (nat_lit 1109, Int.ofNat (nat_lit 105901830)), (nat_lit 1124, Int.ofNat (nat_lit 84255390)), (nat_lit 1205, Int.ofNat (nat_lit 633600)), (nat_lit 1209, Int.ofNat (nat_lit 11719440)), (nat_lit 1221, Int.ofNat (nat_lit 1664640)), (nat_lit 1222, Int.ofNat (nat_lit 5230080)), (nat_lit 1223, Int.ofNat (nat_lit 7130880)), (nat_lit 1224, Int.ofNat (nat_lit 17790048)), (nat_lit 1227, Int.ofNat (nat_lit 15029280)), (nat_lit 1228, Int.ofNat (nat_lit 31033728)), (nat_lit 1229, Int.ofNat (nat_lit 50347440)), (nat_lit 1237, Int.ofNat (nat_lit 7777920)), (nat_lit 1238, Int.ofNat (nat_lit 18124800)), (nat_lit 1239, Int.ofNat (nat_lit 25904640)), (nat_lit 1240, Int.ofNat (nat_lit 16650960)), (nat_lit 1241, Int.ofNat (nat_lit 23597280)), (nat_lit 1242, Int.ofNat (nat_lit 40870320)), (nat_lit 1243, Int.ofNat (nat_lit 62623920)), (nat_lit 1244, Int.ofNat (nat_lit 87616080)), (nat_lit 1253, Int.ofNat (nat_lit 16473600)), (nat_lit 1254, Int.ofNat (nat_lit 43397280)), (nat_lit 1255, Int.ofNat (nat_lit 36727920)), (nat_lit 1256, Int.ofNat (nat_lit 52757280)), (nat_lit 1257, Int.ofNat (nat_lit 73305360)), (nat_lit 1258, Int.ofNat (nat_lit 86870160)), (nat_lit 1259, Int.ofNat (nat_lit 142287840)), (nat_lit 1269, Int.ofNat (nat_lit 44323200)), (nat_lit 1270, Int.ofNat (nat_lit 82846440)), (nat_lit 1271, Int.ofNat (nat_lit 142823520)), (nat_lit 1272, Int.ofNat (nat_lit 167162040)), (nat_lit 1273, Int.ofNat (nat_lit 115337880)), (nat_lit 1274, Int.ofNat (nat_lit 199593720)), (nat_lit 1285, Int.ofNat (nat_lit 36733824)), (nat_lit 1286, Int.ofNat (nat_lit 114498720)), (nat_lit 1287, Int.ofNat (nat_lit 154214820)), (nat_lit 1288, Int.ofNat (nat_lit 117768240)), (nat_lit 1289, Int.ofNat (nat_lit 164733750)), (nat_lit 1301, Int.ofNat (nat_lit 90088200)), (nat_lit 1302, Int.ofNat (nat_lit 167922000)), (nat_lit 1303, Int.ofNat (nat_lit 133936920)), (nat_lit 1304, Int.ofNat (nat_lit 201572280)), (nat_lit 1317, Int.ofNat (nat_lit 62318700)), (nat_lit 1318, Int.ofNat (nat_lit 105936300)), (nat_lit 1319, Int.ofNat (nat_lit 184546350)), (nat_lit 1333, Int.ofNat (nat_lit 24480720)), (nat_lit 1334, Int.ofNat (nat_lit 136735290)), (nat_lit 1349, Int.ofNat (nat_lit 103787730)), (nat_lit 1449, Int.ofNat (nat_lit 5095440)), (nat_lit 1462, Int.ofNat (nat_lit 2311680)), (nat_lit 1463, Int.ofNat (nat_lit 6483840)), (nat_lit 1464, Int.ofNat (nat_lit 5747088)), (nat_lit 1466, Int.ofNat (nat_lit 319440)), (nat_lit 1467, Int.ofNat (nat_lit 15514560)), (nat_lit 1468, Int.ofNat (nat_lit 31680768)), (nat_lit 1469, Int.ofNat (nat_lit 51075360)), (nat_lit 1478, Int.ofNat (nat_lit 8398080)), (nat_lit 1479, Int.ofNat (nat_lit 16403040)), (nat_lit 1480, Int.ofNat (nat_lit 12962160)), (nat_lit 1481, Int.ofNat (nat_lit 26183520)), (nat_lit 1482, Int.ofNat (nat_lit 47159280)), (nat_lit 1483, Int.ofNat (nat_lit 61739280)), (nat_lit 1484, Int.ofNat (nat_lit 119553840)), (nat_lit 1494, Int.ofNat (nat_lit 29030400))]
def block006_data_flat000 : CoefficientMerge.Poly := [(nat_lit 1046, Int.ofNat (nat_lit 159550560))]
theorem block006_data_flat000_step : block006_data_flat000 = (CoefficientMerge.scale (159550560 : Int) atom0473Coded) := by decide +kernel
theorem block006_data_flat000_original : block006_data_flat000 = (CoefficientMerge.scale (159550560 : Int) atom0473Coded) := by
  rw [block006_data_flat000_step]
def block006_data_flat001 : CoefficientMerge.Poly := [(nat_lit 1047, Int.ofNat (nat_lit 175445640))]
theorem block006_data_flat001_step : block006_data_flat001 = (CoefficientMerge.scale (175445640 : Int) atom0474Coded) := by decide +kernel
theorem block006_data_flat001_original : block006_data_flat001 = (CoefficientMerge.scale (175445640 : Int) atom0474Coded) := by
  rw [block006_data_flat001_step]
def block006_data_flat002 : CoefficientMerge.Poly := [(nat_lit 1046, Int.ofNat (nat_lit 159550560)), (nat_lit 1047, Int.ofNat (nat_lit 175445640))]
theorem block006_data_flat002_step : block006_data_flat002 = (CoefficientMerge.fastMerge block006_data_flat000 block006_data_flat001) := by decide +kernel
theorem block006_data_flat002_original : block006_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (159550560 : Int) atom0473Coded) (CoefficientMerge.scale (175445640 : Int) atom0474Coded)) := by
  rw [block006_data_flat002_step, block006_data_flat000_original, block006_data_flat001_original]
def block006_data_flat003 : CoefficientMerge.Poly := [(nat_lit 1048, Int.ofNat (nat_lit 116951400))]
theorem block006_data_flat003_step : block006_data_flat003 = (CoefficientMerge.scale (116951400 : Int) atom0475Coded) := by decide +kernel
theorem block006_data_flat003_original : block006_data_flat003 = (CoefficientMerge.scale (116951400 : Int) atom0475Coded) := by
  rw [block006_data_flat003_step]
def block006_data_flat004 : CoefficientMerge.Poly := [(nat_lit 1049, Int.ofNat (nat_lit 194537160))]
theorem block006_data_flat004_step : block006_data_flat004 = (CoefficientMerge.scale (194537160 : Int) atom0476Coded) := by decide +kernel
theorem block006_data_flat004_original : block006_data_flat004 = (CoefficientMerge.scale (194537160 : Int) atom0476Coded) := by
  rw [block006_data_flat004_step]
def block006_data_flat005 : CoefficientMerge.Poly := [(nat_lit 1060, Int.ofNat (nat_lit 46998144))]
theorem block006_data_flat005_step : block006_data_flat005 = (CoefficientMerge.scale (46998144 : Int) atom0477Coded) := by decide +kernel
theorem block006_data_flat005_original : block006_data_flat005 = (CoefficientMerge.scale (46998144 : Int) atom0477Coded) := by
  rw [block006_data_flat005_step]
def block006_data_flat006 : CoefficientMerge.Poly := [(nat_lit 1049, Int.ofNat (nat_lit 194537160)), (nat_lit 1060, Int.ofNat (nat_lit 46998144))]
theorem block006_data_flat006_step : block006_data_flat006 = (CoefficientMerge.fastMerge block006_data_flat004 block006_data_flat005) := by decide +kernel
theorem block006_data_flat006_original : block006_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (194537160 : Int) atom0476Coded) (CoefficientMerge.scale (46998144 : Int) atom0477Coded)) := by
  rw [block006_data_flat006_step, block006_data_flat004_original, block006_data_flat005_original]
def block006_data_flat007 : CoefficientMerge.Poly := [(nat_lit 1048, Int.ofNat (nat_lit 116951400)), (nat_lit 1049, Int.ofNat (nat_lit 194537160)), (nat_lit 1060, Int.ofNat (nat_lit 46998144))]
theorem block006_data_flat007_step : block006_data_flat007 = (CoefficientMerge.fastMerge block006_data_flat003 block006_data_flat006) := by decide +kernel
theorem block006_data_flat007_original : block006_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (116951400 : Int) atom0475Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (194537160 : Int) atom0476Coded) (CoefficientMerge.scale (46998144 : Int) atom0477Coded))) := by
  rw [block006_data_flat007_step, block006_data_flat003_original, block006_data_flat006_original]
def block006_data_flat008 : CoefficientMerge.Poly := [(nat_lit 1046, Int.ofNat (nat_lit 159550560)), (nat_lit 1047, Int.ofNat (nat_lit 175445640)), (nat_lit 1048, Int.ofNat (nat_lit 116951400)), (nat_lit 1049, Int.ofNat (nat_lit 194537160)), (nat_lit 1060, Int.ofNat (nat_lit 46998144))]
theorem block006_data_flat008_step : block006_data_flat008 = (CoefficientMerge.fastMerge block006_data_flat002 block006_data_flat007) := by decide +kernel
theorem block006_data_flat008_original : block006_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (159550560 : Int) atom0473Coded) (CoefficientMerge.scale (175445640 : Int) atom0474Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (116951400 : Int) atom0475Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (194537160 : Int) atom0476Coded) (CoefficientMerge.scale (46998144 : Int) atom0477Coded)))) := by
  rw [block006_data_flat008_step, block006_data_flat002_original, block006_data_flat007_original]
def block006_data_flat009 : CoefficientMerge.Poly := [(nat_lit 1061, Int.ofNat (nat_lit 129823920))]
theorem block006_data_flat009_step : block006_data_flat009 = (CoefficientMerge.scale (129823920 : Int) atom0478Coded) := by decide +kernel
theorem block006_data_flat009_original : block006_data_flat009 = (CoefficientMerge.scale (129823920 : Int) atom0478Coded) := by
  rw [block006_data_flat009_step]
def block006_data_flat010 : CoefficientMerge.Poly := [(nat_lit 1062, Int.ofNat (nat_lit 162877500))]
theorem block006_data_flat010_step : block006_data_flat010 = (CoefficientMerge.scale (162877500 : Int) atom0479Coded) := by decide +kernel
theorem block006_data_flat010_original : block006_data_flat010 = (CoefficientMerge.scale (162877500 : Int) atom0479Coded) := by
  rw [block006_data_flat010_step]
def block006_data_flat011 : CoefficientMerge.Poly := [(nat_lit 1061, Int.ofNat (nat_lit 129823920)), (nat_lit 1062, Int.ofNat (nat_lit 162877500))]
theorem block006_data_flat011_step : block006_data_flat011 = (CoefficientMerge.fastMerge block006_data_flat009 block006_data_flat010) := by decide +kernel
theorem block006_data_flat011_original : block006_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (129823920 : Int) atom0478Coded) (CoefficientMerge.scale (162877500 : Int) atom0479Coded)) := by
  rw [block006_data_flat011_step, block006_data_flat009_original, block006_data_flat010_original]
def block006_data_flat012 : CoefficientMerge.Poly := [(nat_lit 1063, Int.ofNat (nat_lit 119768400))]
theorem block006_data_flat012_step : block006_data_flat012 = (CoefficientMerge.scale (119768400 : Int) atom0480Coded) := by decide +kernel
theorem block006_data_flat012_original : block006_data_flat012 = (CoefficientMerge.scale (119768400 : Int) atom0480Coded) := by
  rw [block006_data_flat012_step]
def block006_data_flat013 : CoefficientMerge.Poly := [(nat_lit 1064, Int.ofNat (nat_lit 159341850))]
theorem block006_data_flat013_step : block006_data_flat013 = (CoefficientMerge.scale (159341850 : Int) atom0481Coded) := by decide +kernel
theorem block006_data_flat013_original : block006_data_flat013 = (CoefficientMerge.scale (159341850 : Int) atom0481Coded) := by
  rw [block006_data_flat013_step]
def block006_data_flat014 : CoefficientMerge.Poly := [(nat_lit 1076, Int.ofNat (nat_lit 94131720))]
theorem block006_data_flat014_step : block006_data_flat014 = (CoefficientMerge.scale (94131720 : Int) atom0482Coded) := by decide +kernel
theorem block006_data_flat014_original : block006_data_flat014 = (CoefficientMerge.scale (94131720 : Int) atom0482Coded) := by
  rw [block006_data_flat014_step]
def block006_data_flat015 : CoefficientMerge.Poly := [(nat_lit 1064, Int.ofNat (nat_lit 159341850)), (nat_lit 1076, Int.ofNat (nat_lit 94131720))]
theorem block006_data_flat015_step : block006_data_flat015 = (CoefficientMerge.fastMerge block006_data_flat013 block006_data_flat014) := by decide +kernel
theorem block006_data_flat015_original : block006_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (159341850 : Int) atom0481Coded) (CoefficientMerge.scale (94131720 : Int) atom0482Coded)) := by
  rw [block006_data_flat015_step, block006_data_flat013_original, block006_data_flat014_original]
def block006_data_flat016 : CoefficientMerge.Poly := [(nat_lit 1063, Int.ofNat (nat_lit 119768400)), (nat_lit 1064, Int.ofNat (nat_lit 159341850)), (nat_lit 1076, Int.ofNat (nat_lit 94131720))]
theorem block006_data_flat016_step : block006_data_flat016 = (CoefficientMerge.fastMerge block006_data_flat012 block006_data_flat015) := by decide +kernel
theorem block006_data_flat016_original : block006_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (119768400 : Int) atom0480Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (159341850 : Int) atom0481Coded) (CoefficientMerge.scale (94131720 : Int) atom0482Coded))) := by
  rw [block006_data_flat016_step, block006_data_flat012_original, block006_data_flat015_original]
def block006_data_flat017 : CoefficientMerge.Poly := [(nat_lit 1061, Int.ofNat (nat_lit 129823920)), (nat_lit 1062, Int.ofNat (nat_lit 162877500)), (nat_lit 1063, Int.ofNat (nat_lit 119768400)), (nat_lit 1064, Int.ofNat (nat_lit 159341850)), (nat_lit 1076, Int.ofNat (nat_lit 94131720))]
theorem block006_data_flat017_step : block006_data_flat017 = (CoefficientMerge.fastMerge block006_data_flat011 block006_data_flat016) := by decide +kernel
theorem block006_data_flat017_original : block006_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129823920 : Int) atom0478Coded) (CoefficientMerge.scale (162877500 : Int) atom0479Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119768400 : Int) atom0480Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (159341850 : Int) atom0481Coded) (CoefficientMerge.scale (94131720 : Int) atom0482Coded)))) := by
  rw [block006_data_flat017_step, block006_data_flat011_original, block006_data_flat016_original]
def block006_data_flat018 : CoefficientMerge.Poly := [(nat_lit 1046, Int.ofNat (nat_lit 159550560)), (nat_lit 1047, Int.ofNat (nat_lit 175445640)), (nat_lit 1048, Int.ofNat (nat_lit 116951400)), (nat_lit 1049, Int.ofNat (nat_lit 194537160)), (nat_lit 1060, Int.ofNat (nat_lit 46998144)), (nat_lit 1061, Int.ofNat (nat_lit 129823920)), (nat_lit 1062, Int.ofNat (nat_lit 162877500)), (nat_lit 1063, Int.ofNat (nat_lit 119768400)), (nat_lit 1064, Int.ofNat (nat_lit 159341850)), (nat_lit 1076, Int.ofNat (nat_lit 94131720))]
theorem block006_data_flat018_step : block006_data_flat018 = (CoefficientMerge.fastMerge block006_data_flat008 block006_data_flat017) := by decide +kernel
theorem block006_data_flat018_original : block006_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (159550560 : Int) atom0473Coded) (CoefficientMerge.scale (175445640 : Int) atom0474Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (116951400 : Int) atom0475Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (194537160 : Int) atom0476Coded) (CoefficientMerge.scale (46998144 : Int) atom0477Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129823920 : Int) atom0478Coded) (CoefficientMerge.scale (162877500 : Int) atom0479Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119768400 : Int) atom0480Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (159341850 : Int) atom0481Coded) (CoefficientMerge.scale (94131720 : Int) atom0482Coded))))) := by
  rw [block006_data_flat018_step, block006_data_flat008_original, block006_data_flat017_original]
def block006_data_flat019 : CoefficientMerge.Poly := [(nat_lit 1077, Int.ofNat (nat_lit 168209280))]
theorem block006_data_flat019_step : block006_data_flat019 = (CoefficientMerge.scale (168209280 : Int) atom0483Coded) := by decide +kernel
theorem block006_data_flat019_original : block006_data_flat019 = (CoefficientMerge.scale (168209280 : Int) atom0483Coded) := by
  rw [block006_data_flat019_step]
def block006_data_flat020 : CoefficientMerge.Poly := [(nat_lit 1078, Int.ofNat (nat_lit 124651080))]
theorem block006_data_flat020_step : block006_data_flat020 = (CoefficientMerge.scale (124651080 : Int) atom0484Coded) := by decide +kernel
theorem block006_data_flat020_original : block006_data_flat020 = (CoefficientMerge.scale (124651080 : Int) atom0484Coded) := by
  rw [block006_data_flat020_step]
def block006_data_flat021 : CoefficientMerge.Poly := [(nat_lit 1077, Int.ofNat (nat_lit 168209280)), (nat_lit 1078, Int.ofNat (nat_lit 124651080))]
theorem block006_data_flat021_step : block006_data_flat021 = (CoefficientMerge.fastMerge block006_data_flat019 block006_data_flat020) := by decide +kernel
theorem block006_data_flat021_original : block006_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (168209280 : Int) atom0483Coded) (CoefficientMerge.scale (124651080 : Int) atom0484Coded)) := by
  rw [block006_data_flat021_step, block006_data_flat019_original, block006_data_flat020_original]
def block006_data_flat022 : CoefficientMerge.Poly := [(nat_lit 1079, Int.ofNat (nat_lit 182713320))]
theorem block006_data_flat022_step : block006_data_flat022 = (CoefficientMerge.scale (182713320 : Int) atom0485Coded) := by decide +kernel
theorem block006_data_flat022_original : block006_data_flat022 = (CoefficientMerge.scale (182713320 : Int) atom0485Coded) := by
  rw [block006_data_flat022_step]
def block006_data_flat023 : CoefficientMerge.Poly := [(nat_lit 1092, Int.ofNat (nat_lit 61220340))]
theorem block006_data_flat023_step : block006_data_flat023 = (CoefficientMerge.scale (61220340 : Int) atom0486Coded) := by decide +kernel
theorem block006_data_flat023_original : block006_data_flat023 = (CoefficientMerge.scale (61220340 : Int) atom0486Coded) := by
  rw [block006_data_flat023_step]
def block006_data_flat024 : CoefficientMerge.Poly := [(nat_lit 1093, Int.ofNat (nat_lit 93601620))]
theorem block006_data_flat024_step : block006_data_flat024 = (CoefficientMerge.scale (93601620 : Int) atom0487Coded) := by decide +kernel
theorem block006_data_flat024_original : block006_data_flat024 = (CoefficientMerge.scale (93601620 : Int) atom0487Coded) := by
  rw [block006_data_flat024_step]
def block006_data_flat025 : CoefficientMerge.Poly := [(nat_lit 1092, Int.ofNat (nat_lit 61220340)), (nat_lit 1093, Int.ofNat (nat_lit 93601620))]
theorem block006_data_flat025_step : block006_data_flat025 = (CoefficientMerge.fastMerge block006_data_flat023 block006_data_flat024) := by decide +kernel
theorem block006_data_flat025_original : block006_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (61220340 : Int) atom0486Coded) (CoefficientMerge.scale (93601620 : Int) atom0487Coded)) := by
  rw [block006_data_flat025_step, block006_data_flat023_original, block006_data_flat024_original]
def block006_data_flat026 : CoefficientMerge.Poly := [(nat_lit 1079, Int.ofNat (nat_lit 182713320)), (nat_lit 1092, Int.ofNat (nat_lit 61220340)), (nat_lit 1093, Int.ofNat (nat_lit 93601620))]
theorem block006_data_flat026_step : block006_data_flat026 = (CoefficientMerge.fastMerge block006_data_flat022 block006_data_flat025) := by decide +kernel
theorem block006_data_flat026_original : block006_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (182713320 : Int) atom0485Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61220340 : Int) atom0486Coded) (CoefficientMerge.scale (93601620 : Int) atom0487Coded))) := by
  rw [block006_data_flat026_step, block006_data_flat022_original, block006_data_flat025_original]
def block006_data_flat027 : CoefficientMerge.Poly := [(nat_lit 1077, Int.ofNat (nat_lit 168209280)), (nat_lit 1078, Int.ofNat (nat_lit 124651080)), (nat_lit 1079, Int.ofNat (nat_lit 182713320)), (nat_lit 1092, Int.ofNat (nat_lit 61220340)), (nat_lit 1093, Int.ofNat (nat_lit 93601620))]
theorem block006_data_flat027_step : block006_data_flat027 = (CoefficientMerge.fastMerge block006_data_flat021 block006_data_flat026) := by decide +kernel
theorem block006_data_flat027_original : block006_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (168209280 : Int) atom0483Coded) (CoefficientMerge.scale (124651080 : Int) atom0484Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182713320 : Int) atom0485Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61220340 : Int) atom0486Coded) (CoefficientMerge.scale (93601620 : Int) atom0487Coded)))) := by
  rw [block006_data_flat027_step, block006_data_flat021_original, block006_data_flat026_original]
def block006_data_flat028 : CoefficientMerge.Poly := [(nat_lit 1094, Int.ofNat (nat_lit 161695170))]
theorem block006_data_flat028_step : block006_data_flat028 = (CoefficientMerge.scale (161695170 : Int) atom0488Coded) := by decide +kernel
theorem block006_data_flat028_original : block006_data_flat028 = (CoefficientMerge.scale (161695170 : Int) atom0488Coded) := by
  rw [block006_data_flat028_step]
def block006_data_flat029 : CoefficientMerge.Poly := [(nat_lit 1108, Int.ofNat (nat_lit 15015600))]
theorem block006_data_flat029_step : block006_data_flat029 = (CoefficientMerge.scale (15015600 : Int) atom0489Coded) := by decide +kernel
theorem block006_data_flat029_original : block006_data_flat029 = (CoefficientMerge.scale (15015600 : Int) atom0489Coded) := by
  rw [block006_data_flat029_step]
def block006_data_flat030 : CoefficientMerge.Poly := [(nat_lit 1094, Int.ofNat (nat_lit 161695170)), (nat_lit 1108, Int.ofNat (nat_lit 15015600))]
theorem block006_data_flat030_step : block006_data_flat030 = (CoefficientMerge.fastMerge block006_data_flat028 block006_data_flat029) := by decide +kernel
theorem block006_data_flat030_original : block006_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (161695170 : Int) atom0488Coded) (CoefficientMerge.scale (15015600 : Int) atom0489Coded)) := by
  rw [block006_data_flat030_step, block006_data_flat028_original, block006_data_flat029_original]
def block006_data_flat031 : CoefficientMerge.Poly := [(nat_lit 1109, Int.ofNat (nat_lit 105901830))]
theorem block006_data_flat031_step : block006_data_flat031 = (CoefficientMerge.scale (105901830 : Int) atom0490Coded) := by decide +kernel
theorem block006_data_flat031_original : block006_data_flat031 = (CoefficientMerge.scale (105901830 : Int) atom0490Coded) := by
  rw [block006_data_flat031_step]
def block006_data_flat032 : CoefficientMerge.Poly := [(nat_lit 1124, Int.ofNat (nat_lit 84255390))]
theorem block006_data_flat032_step : block006_data_flat032 = (CoefficientMerge.scale (84255390 : Int) atom0491Coded) := by decide +kernel
theorem block006_data_flat032_original : block006_data_flat032 = (CoefficientMerge.scale (84255390 : Int) atom0491Coded) := by
  rw [block006_data_flat032_step]
def block006_data_flat033 : CoefficientMerge.Poly := [(nat_lit 1205, Int.ofNat (nat_lit 633600))]
theorem block006_data_flat033_step : block006_data_flat033 = (CoefficientMerge.scale (633600 : Int) atom0492Coded) := by decide +kernel
theorem block006_data_flat033_original : block006_data_flat033 = (CoefficientMerge.scale (633600 : Int) atom0492Coded) := by
  rw [block006_data_flat033_step]
def block006_data_flat034 : CoefficientMerge.Poly := [(nat_lit 1124, Int.ofNat (nat_lit 84255390)), (nat_lit 1205, Int.ofNat (nat_lit 633600))]
theorem block006_data_flat034_step : block006_data_flat034 = (CoefficientMerge.fastMerge block006_data_flat032 block006_data_flat033) := by decide +kernel
theorem block006_data_flat034_original : block006_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (84255390 : Int) atom0491Coded) (CoefficientMerge.scale (633600 : Int) atom0492Coded)) := by
  rw [block006_data_flat034_step, block006_data_flat032_original, block006_data_flat033_original]
def block006_data_flat035 : CoefficientMerge.Poly := [(nat_lit 1109, Int.ofNat (nat_lit 105901830)), (nat_lit 1124, Int.ofNat (nat_lit 84255390)), (nat_lit 1205, Int.ofNat (nat_lit 633600))]
theorem block006_data_flat035_step : block006_data_flat035 = (CoefficientMerge.fastMerge block006_data_flat031 block006_data_flat034) := by decide +kernel
theorem block006_data_flat035_original : block006_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (105901830 : Int) atom0490Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84255390 : Int) atom0491Coded) (CoefficientMerge.scale (633600 : Int) atom0492Coded))) := by
  rw [block006_data_flat035_step, block006_data_flat031_original, block006_data_flat034_original]
def block006_data_flat036 : CoefficientMerge.Poly := [(nat_lit 1094, Int.ofNat (nat_lit 161695170)), (nat_lit 1108, Int.ofNat (nat_lit 15015600)), (nat_lit 1109, Int.ofNat (nat_lit 105901830)), (nat_lit 1124, Int.ofNat (nat_lit 84255390)), (nat_lit 1205, Int.ofNat (nat_lit 633600))]
theorem block006_data_flat036_step : block006_data_flat036 = (CoefficientMerge.fastMerge block006_data_flat030 block006_data_flat035) := by decide +kernel
theorem block006_data_flat036_original : block006_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (161695170 : Int) atom0488Coded) (CoefficientMerge.scale (15015600 : Int) atom0489Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105901830 : Int) atom0490Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84255390 : Int) atom0491Coded) (CoefficientMerge.scale (633600 : Int) atom0492Coded)))) := by
  rw [block006_data_flat036_step, block006_data_flat030_original, block006_data_flat035_original]
def block006_data_flat037 : CoefficientMerge.Poly := [(nat_lit 1077, Int.ofNat (nat_lit 168209280)), (nat_lit 1078, Int.ofNat (nat_lit 124651080)), (nat_lit 1079, Int.ofNat (nat_lit 182713320)), (nat_lit 1092, Int.ofNat (nat_lit 61220340)), (nat_lit 1093, Int.ofNat (nat_lit 93601620)), (nat_lit 1094, Int.ofNat (nat_lit 161695170)), (nat_lit 1108, Int.ofNat (nat_lit 15015600)), (nat_lit 1109, Int.ofNat (nat_lit 105901830)), (nat_lit 1124, Int.ofNat (nat_lit 84255390)), (nat_lit 1205, Int.ofNat (nat_lit 633600))]
theorem block006_data_flat037_step : block006_data_flat037 = (CoefficientMerge.fastMerge block006_data_flat027 block006_data_flat036) := by decide +kernel
theorem block006_data_flat037_original : block006_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (168209280 : Int) atom0483Coded) (CoefficientMerge.scale (124651080 : Int) atom0484Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182713320 : Int) atom0485Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61220340 : Int) atom0486Coded) (CoefficientMerge.scale (93601620 : Int) atom0487Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (161695170 : Int) atom0488Coded) (CoefficientMerge.scale (15015600 : Int) atom0489Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105901830 : Int) atom0490Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84255390 : Int) atom0491Coded) (CoefficientMerge.scale (633600 : Int) atom0492Coded))))) := by
  rw [block006_data_flat037_step, block006_data_flat027_original, block006_data_flat036_original]
def block006_data_flat038 : CoefficientMerge.Poly := [(nat_lit 1046, Int.ofNat (nat_lit 159550560)), (nat_lit 1047, Int.ofNat (nat_lit 175445640)), (nat_lit 1048, Int.ofNat (nat_lit 116951400)), (nat_lit 1049, Int.ofNat (nat_lit 194537160)), (nat_lit 1060, Int.ofNat (nat_lit 46998144)), (nat_lit 1061, Int.ofNat (nat_lit 129823920)), (nat_lit 1062, Int.ofNat (nat_lit 162877500)), (nat_lit 1063, Int.ofNat (nat_lit 119768400)), (nat_lit 1064, Int.ofNat (nat_lit 159341850)), (nat_lit 1076, Int.ofNat (nat_lit 94131720)), (nat_lit 1077, Int.ofNat (nat_lit 168209280)), (nat_lit 1078, Int.ofNat (nat_lit 124651080)), (nat_lit 1079, Int.ofNat (nat_lit 182713320)), (nat_lit 1092, Int.ofNat (nat_lit 61220340)), (nat_lit 1093, Int.ofNat (nat_lit 93601620)), (nat_lit 1094, Int.ofNat (nat_lit 161695170)), (nat_lit 1108, Int.ofNat (nat_lit 15015600)), (nat_lit 1109, Int.ofNat (nat_lit 105901830)), (nat_lit 1124, Int.ofNat (nat_lit 84255390)), (nat_lit 1205, Int.ofNat (nat_lit 633600))]
theorem block006_data_flat038_step : block006_data_flat038 = (CoefficientMerge.fastMerge block006_data_flat018 block006_data_flat037) := by decide +kernel
theorem block006_data_flat038_original : block006_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (159550560 : Int) atom0473Coded) (CoefficientMerge.scale (175445640 : Int) atom0474Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (116951400 : Int) atom0475Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (194537160 : Int) atom0476Coded) (CoefficientMerge.scale (46998144 : Int) atom0477Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129823920 : Int) atom0478Coded) (CoefficientMerge.scale (162877500 : Int) atom0479Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119768400 : Int) atom0480Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (159341850 : Int) atom0481Coded) (CoefficientMerge.scale (94131720 : Int) atom0482Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (168209280 : Int) atom0483Coded) (CoefficientMerge.scale (124651080 : Int) atom0484Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182713320 : Int) atom0485Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61220340 : Int) atom0486Coded) (CoefficientMerge.scale (93601620 : Int) atom0487Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (161695170 : Int) atom0488Coded) (CoefficientMerge.scale (15015600 : Int) atom0489Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105901830 : Int) atom0490Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84255390 : Int) atom0491Coded) (CoefficientMerge.scale (633600 : Int) atom0492Coded)))))) := by
  rw [block006_data_flat038_step, block006_data_flat018_original, block006_data_flat037_original]
def block006_data_flat039 : CoefficientMerge.Poly := [(nat_lit 1209, Int.ofNat (nat_lit 11719440))]
theorem block006_data_flat039_step : block006_data_flat039 = (CoefficientMerge.scale (11719440 : Int) atom0493Coded) := by decide +kernel
theorem block006_data_flat039_original : block006_data_flat039 = (CoefficientMerge.scale (11719440 : Int) atom0493Coded) := by
  rw [block006_data_flat039_step]
def block006_data_flat040 : CoefficientMerge.Poly := [(nat_lit 1221, Int.ofNat (nat_lit 1664640))]
theorem block006_data_flat040_step : block006_data_flat040 = (CoefficientMerge.scale (1664640 : Int) atom0494Coded) := by decide +kernel
theorem block006_data_flat040_original : block006_data_flat040 = (CoefficientMerge.scale (1664640 : Int) atom0494Coded) := by
  rw [block006_data_flat040_step]
def block006_data_flat041 : CoefficientMerge.Poly := [(nat_lit 1209, Int.ofNat (nat_lit 11719440)), (nat_lit 1221, Int.ofNat (nat_lit 1664640))]
theorem block006_data_flat041_step : block006_data_flat041 = (CoefficientMerge.fastMerge block006_data_flat039 block006_data_flat040) := by decide +kernel
theorem block006_data_flat041_original : block006_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11719440 : Int) atom0493Coded) (CoefficientMerge.scale (1664640 : Int) atom0494Coded)) := by
  rw [block006_data_flat041_step, block006_data_flat039_original, block006_data_flat040_original]
def block006_data_flat042 : CoefficientMerge.Poly := [(nat_lit 1222, Int.ofNat (nat_lit 5230080))]
theorem block006_data_flat042_step : block006_data_flat042 = (CoefficientMerge.scale (5230080 : Int) atom0495Coded) := by decide +kernel
theorem block006_data_flat042_original : block006_data_flat042 = (CoefficientMerge.scale (5230080 : Int) atom0495Coded) := by
  rw [block006_data_flat042_step]
def block006_data_flat043 : CoefficientMerge.Poly := [(nat_lit 1223, Int.ofNat (nat_lit 7130880))]
theorem block006_data_flat043_step : block006_data_flat043 = (CoefficientMerge.scale (7130880 : Int) atom0496Coded) := by decide +kernel
theorem block006_data_flat043_original : block006_data_flat043 = (CoefficientMerge.scale (7130880 : Int) atom0496Coded) := by
  rw [block006_data_flat043_step]
def block006_data_flat044 : CoefficientMerge.Poly := [(nat_lit 1224, Int.ofNat (nat_lit 17790048))]
theorem block006_data_flat044_step : block006_data_flat044 = (CoefficientMerge.scale (17790048 : Int) atom0497Coded) := by decide +kernel
theorem block006_data_flat044_original : block006_data_flat044 = (CoefficientMerge.scale (17790048 : Int) atom0497Coded) := by
  rw [block006_data_flat044_step]
def block006_data_flat045 : CoefficientMerge.Poly := [(nat_lit 1223, Int.ofNat (nat_lit 7130880)), (nat_lit 1224, Int.ofNat (nat_lit 17790048))]
theorem block006_data_flat045_step : block006_data_flat045 = (CoefficientMerge.fastMerge block006_data_flat043 block006_data_flat044) := by decide +kernel
theorem block006_data_flat045_original : block006_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7130880 : Int) atom0496Coded) (CoefficientMerge.scale (17790048 : Int) atom0497Coded)) := by
  rw [block006_data_flat045_step, block006_data_flat043_original, block006_data_flat044_original]
def block006_data_flat046 : CoefficientMerge.Poly := [(nat_lit 1222, Int.ofNat (nat_lit 5230080)), (nat_lit 1223, Int.ofNat (nat_lit 7130880)), (nat_lit 1224, Int.ofNat (nat_lit 17790048))]
theorem block006_data_flat046_step : block006_data_flat046 = (CoefficientMerge.fastMerge block006_data_flat042 block006_data_flat045) := by decide +kernel
theorem block006_data_flat046_original : block006_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5230080 : Int) atom0495Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7130880 : Int) atom0496Coded) (CoefficientMerge.scale (17790048 : Int) atom0497Coded))) := by
  rw [block006_data_flat046_step, block006_data_flat042_original, block006_data_flat045_original]
def block006_data_flat047 : CoefficientMerge.Poly := [(nat_lit 1209, Int.ofNat (nat_lit 11719440)), (nat_lit 1221, Int.ofNat (nat_lit 1664640)), (nat_lit 1222, Int.ofNat (nat_lit 5230080)), (nat_lit 1223, Int.ofNat (nat_lit 7130880)), (nat_lit 1224, Int.ofNat (nat_lit 17790048))]
theorem block006_data_flat047_step : block006_data_flat047 = (CoefficientMerge.fastMerge block006_data_flat041 block006_data_flat046) := by decide +kernel
theorem block006_data_flat047_original : block006_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11719440 : Int) atom0493Coded) (CoefficientMerge.scale (1664640 : Int) atom0494Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5230080 : Int) atom0495Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7130880 : Int) atom0496Coded) (CoefficientMerge.scale (17790048 : Int) atom0497Coded)))) := by
  rw [block006_data_flat047_step, block006_data_flat041_original, block006_data_flat046_original]
def block006_data_flat048 : CoefficientMerge.Poly := [(nat_lit 1227, Int.ofNat (nat_lit 15029280))]
theorem block006_data_flat048_step : block006_data_flat048 = (CoefficientMerge.scale (15029280 : Int) atom0498Coded) := by decide +kernel
theorem block006_data_flat048_original : block006_data_flat048 = (CoefficientMerge.scale (15029280 : Int) atom0498Coded) := by
  rw [block006_data_flat048_step]
def block006_data_flat049 : CoefficientMerge.Poly := [(nat_lit 1228, Int.ofNat (nat_lit 31033728))]
theorem block006_data_flat049_step : block006_data_flat049 = (CoefficientMerge.scale (31033728 : Int) atom0499Coded) := by decide +kernel
theorem block006_data_flat049_original : block006_data_flat049 = (CoefficientMerge.scale (31033728 : Int) atom0499Coded) := by
  rw [block006_data_flat049_step]
def block006_data_flat050 : CoefficientMerge.Poly := [(nat_lit 1227, Int.ofNat (nat_lit 15029280)), (nat_lit 1228, Int.ofNat (nat_lit 31033728))]
theorem block006_data_flat050_step : block006_data_flat050 = (CoefficientMerge.fastMerge block006_data_flat048 block006_data_flat049) := by decide +kernel
theorem block006_data_flat050_original : block006_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15029280 : Int) atom0498Coded) (CoefficientMerge.scale (31033728 : Int) atom0499Coded)) := by
  rw [block006_data_flat050_step, block006_data_flat048_original, block006_data_flat049_original]
def block006_data_flat051 : CoefficientMerge.Poly := [(nat_lit 1229, Int.ofNat (nat_lit 50347440))]
theorem block006_data_flat051_step : block006_data_flat051 = (CoefficientMerge.scale (50347440 : Int) atom0500Coded) := by decide +kernel
theorem block006_data_flat051_original : block006_data_flat051 = (CoefficientMerge.scale (50347440 : Int) atom0500Coded) := by
  rw [block006_data_flat051_step]
def block006_data_flat052 : CoefficientMerge.Poly := [(nat_lit 1237, Int.ofNat (nat_lit 7777920))]
theorem block006_data_flat052_step : block006_data_flat052 = (CoefficientMerge.scale (7777920 : Int) atom0501Coded) := by decide +kernel
theorem block006_data_flat052_original : block006_data_flat052 = (CoefficientMerge.scale (7777920 : Int) atom0501Coded) := by
  rw [block006_data_flat052_step]
def block006_data_flat053 : CoefficientMerge.Poly := [(nat_lit 1238, Int.ofNat (nat_lit 18124800))]
theorem block006_data_flat053_step : block006_data_flat053 = (CoefficientMerge.scale (18124800 : Int) atom0502Coded) := by decide +kernel
theorem block006_data_flat053_original : block006_data_flat053 = (CoefficientMerge.scale (18124800 : Int) atom0502Coded) := by
  rw [block006_data_flat053_step]
def block006_data_flat054 : CoefficientMerge.Poly := [(nat_lit 1237, Int.ofNat (nat_lit 7777920)), (nat_lit 1238, Int.ofNat (nat_lit 18124800))]
theorem block006_data_flat054_step : block006_data_flat054 = (CoefficientMerge.fastMerge block006_data_flat052 block006_data_flat053) := by decide +kernel
theorem block006_data_flat054_original : block006_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777920 : Int) atom0501Coded) (CoefficientMerge.scale (18124800 : Int) atom0502Coded)) := by
  rw [block006_data_flat054_step, block006_data_flat052_original, block006_data_flat053_original]
def block006_data_flat055 : CoefficientMerge.Poly := [(nat_lit 1229, Int.ofNat (nat_lit 50347440)), (nat_lit 1237, Int.ofNat (nat_lit 7777920)), (nat_lit 1238, Int.ofNat (nat_lit 18124800))]
theorem block006_data_flat055_step : block006_data_flat055 = (CoefficientMerge.fastMerge block006_data_flat051 block006_data_flat054) := by decide +kernel
theorem block006_data_flat055_original : block006_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (50347440 : Int) atom0500Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777920 : Int) atom0501Coded) (CoefficientMerge.scale (18124800 : Int) atom0502Coded))) := by
  rw [block006_data_flat055_step, block006_data_flat051_original, block006_data_flat054_original]
def block006_data_flat056 : CoefficientMerge.Poly := [(nat_lit 1227, Int.ofNat (nat_lit 15029280)), (nat_lit 1228, Int.ofNat (nat_lit 31033728)), (nat_lit 1229, Int.ofNat (nat_lit 50347440)), (nat_lit 1237, Int.ofNat (nat_lit 7777920)), (nat_lit 1238, Int.ofNat (nat_lit 18124800))]
theorem block006_data_flat056_step : block006_data_flat056 = (CoefficientMerge.fastMerge block006_data_flat050 block006_data_flat055) := by decide +kernel
theorem block006_data_flat056_original : block006_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15029280 : Int) atom0498Coded) (CoefficientMerge.scale (31033728 : Int) atom0499Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50347440 : Int) atom0500Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777920 : Int) atom0501Coded) (CoefficientMerge.scale (18124800 : Int) atom0502Coded)))) := by
  rw [block006_data_flat056_step, block006_data_flat050_original, block006_data_flat055_original]
def block006_data_flat057 : CoefficientMerge.Poly := [(nat_lit 1209, Int.ofNat (nat_lit 11719440)), (nat_lit 1221, Int.ofNat (nat_lit 1664640)), (nat_lit 1222, Int.ofNat (nat_lit 5230080)), (nat_lit 1223, Int.ofNat (nat_lit 7130880)), (nat_lit 1224, Int.ofNat (nat_lit 17790048)), (nat_lit 1227, Int.ofNat (nat_lit 15029280)), (nat_lit 1228, Int.ofNat (nat_lit 31033728)), (nat_lit 1229, Int.ofNat (nat_lit 50347440)), (nat_lit 1237, Int.ofNat (nat_lit 7777920)), (nat_lit 1238, Int.ofNat (nat_lit 18124800))]
theorem block006_data_flat057_step : block006_data_flat057 = (CoefficientMerge.fastMerge block006_data_flat047 block006_data_flat056) := by decide +kernel
theorem block006_data_flat057_original : block006_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11719440 : Int) atom0493Coded) (CoefficientMerge.scale (1664640 : Int) atom0494Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5230080 : Int) atom0495Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7130880 : Int) atom0496Coded) (CoefficientMerge.scale (17790048 : Int) atom0497Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15029280 : Int) atom0498Coded) (CoefficientMerge.scale (31033728 : Int) atom0499Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50347440 : Int) atom0500Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777920 : Int) atom0501Coded) (CoefficientMerge.scale (18124800 : Int) atom0502Coded))))) := by
  rw [block006_data_flat057_step, block006_data_flat047_original, block006_data_flat056_original]
def block006_data_flat058 : CoefficientMerge.Poly := [(nat_lit 1239, Int.ofNat (nat_lit 25904640))]
theorem block006_data_flat058_step : block006_data_flat058 = (CoefficientMerge.scale (25904640 : Int) atom0503Coded) := by decide +kernel
theorem block006_data_flat058_original : block006_data_flat058 = (CoefficientMerge.scale (25904640 : Int) atom0503Coded) := by
  rw [block006_data_flat058_step]
def block006_data_flat059 : CoefficientMerge.Poly := [(nat_lit 1240, Int.ofNat (nat_lit 16650960))]
theorem block006_data_flat059_step : block006_data_flat059 = (CoefficientMerge.scale (16650960 : Int) atom0504Coded) := by decide +kernel
theorem block006_data_flat059_original : block006_data_flat059 = (CoefficientMerge.scale (16650960 : Int) atom0504Coded) := by
  rw [block006_data_flat059_step]
def block006_data_flat060 : CoefficientMerge.Poly := [(nat_lit 1239, Int.ofNat (nat_lit 25904640)), (nat_lit 1240, Int.ofNat (nat_lit 16650960))]
theorem block006_data_flat060_step : block006_data_flat060 = (CoefficientMerge.fastMerge block006_data_flat058 block006_data_flat059) := by decide +kernel
theorem block006_data_flat060_original : block006_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25904640 : Int) atom0503Coded) (CoefficientMerge.scale (16650960 : Int) atom0504Coded)) := by
  rw [block006_data_flat060_step, block006_data_flat058_original, block006_data_flat059_original]
def block006_data_flat061 : CoefficientMerge.Poly := [(nat_lit 1241, Int.ofNat (nat_lit 23597280))]
theorem block006_data_flat061_step : block006_data_flat061 = (CoefficientMerge.scale (23597280 : Int) atom0505Coded) := by decide +kernel
theorem block006_data_flat061_original : block006_data_flat061 = (CoefficientMerge.scale (23597280 : Int) atom0505Coded) := by
  rw [block006_data_flat061_step]
def block006_data_flat062 : CoefficientMerge.Poly := [(nat_lit 1242, Int.ofNat (nat_lit 40870320))]
theorem block006_data_flat062_step : block006_data_flat062 = (CoefficientMerge.scale (40870320 : Int) atom0506Coded) := by decide +kernel
theorem block006_data_flat062_original : block006_data_flat062 = (CoefficientMerge.scale (40870320 : Int) atom0506Coded) := by
  rw [block006_data_flat062_step]
def block006_data_flat063 : CoefficientMerge.Poly := [(nat_lit 1243, Int.ofNat (nat_lit 62623920))]
theorem block006_data_flat063_step : block006_data_flat063 = (CoefficientMerge.scale (62623920 : Int) atom0507Coded) := by decide +kernel
theorem block006_data_flat063_original : block006_data_flat063 = (CoefficientMerge.scale (62623920 : Int) atom0507Coded) := by
  rw [block006_data_flat063_step]
def block006_data_flat064 : CoefficientMerge.Poly := [(nat_lit 1242, Int.ofNat (nat_lit 40870320)), (nat_lit 1243, Int.ofNat (nat_lit 62623920))]
theorem block006_data_flat064_step : block006_data_flat064 = (CoefficientMerge.fastMerge block006_data_flat062 block006_data_flat063) := by decide +kernel
theorem block006_data_flat064_original : block006_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40870320 : Int) atom0506Coded) (CoefficientMerge.scale (62623920 : Int) atom0507Coded)) := by
  rw [block006_data_flat064_step, block006_data_flat062_original, block006_data_flat063_original]
def block006_data_flat065 : CoefficientMerge.Poly := [(nat_lit 1241, Int.ofNat (nat_lit 23597280)), (nat_lit 1242, Int.ofNat (nat_lit 40870320)), (nat_lit 1243, Int.ofNat (nat_lit 62623920))]
theorem block006_data_flat065_step : block006_data_flat065 = (CoefficientMerge.fastMerge block006_data_flat061 block006_data_flat064) := by decide +kernel
theorem block006_data_flat065_original : block006_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23597280 : Int) atom0505Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40870320 : Int) atom0506Coded) (CoefficientMerge.scale (62623920 : Int) atom0507Coded))) := by
  rw [block006_data_flat065_step, block006_data_flat061_original, block006_data_flat064_original]
def block006_data_flat066 : CoefficientMerge.Poly := [(nat_lit 1239, Int.ofNat (nat_lit 25904640)), (nat_lit 1240, Int.ofNat (nat_lit 16650960)), (nat_lit 1241, Int.ofNat (nat_lit 23597280)), (nat_lit 1242, Int.ofNat (nat_lit 40870320)), (nat_lit 1243, Int.ofNat (nat_lit 62623920))]
theorem block006_data_flat066_step : block006_data_flat066 = (CoefficientMerge.fastMerge block006_data_flat060 block006_data_flat065) := by decide +kernel
theorem block006_data_flat066_original : block006_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25904640 : Int) atom0503Coded) (CoefficientMerge.scale (16650960 : Int) atom0504Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23597280 : Int) atom0505Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40870320 : Int) atom0506Coded) (CoefficientMerge.scale (62623920 : Int) atom0507Coded)))) := by
  rw [block006_data_flat066_step, block006_data_flat060_original, block006_data_flat065_original]
def block006_data_flat067 : CoefficientMerge.Poly := [(nat_lit 1244, Int.ofNat (nat_lit 87616080))]
theorem block006_data_flat067_step : block006_data_flat067 = (CoefficientMerge.scale (87616080 : Int) atom0508Coded) := by decide +kernel
theorem block006_data_flat067_original : block006_data_flat067 = (CoefficientMerge.scale (87616080 : Int) atom0508Coded) := by
  rw [block006_data_flat067_step]
def block006_data_flat068 : CoefficientMerge.Poly := [(nat_lit 1253, Int.ofNat (nat_lit 16473600))]
theorem block006_data_flat068_step : block006_data_flat068 = (CoefficientMerge.scale (16473600 : Int) atom0509Coded) := by decide +kernel
theorem block006_data_flat068_original : block006_data_flat068 = (CoefficientMerge.scale (16473600 : Int) atom0509Coded) := by
  rw [block006_data_flat068_step]
def block006_data_flat069 : CoefficientMerge.Poly := [(nat_lit 1244, Int.ofNat (nat_lit 87616080)), (nat_lit 1253, Int.ofNat (nat_lit 16473600))]
theorem block006_data_flat069_step : block006_data_flat069 = (CoefficientMerge.fastMerge block006_data_flat067 block006_data_flat068) := by decide +kernel
theorem block006_data_flat069_original : block006_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (87616080 : Int) atom0508Coded) (CoefficientMerge.scale (16473600 : Int) atom0509Coded)) := by
  rw [block006_data_flat069_step, block006_data_flat067_original, block006_data_flat068_original]
def block006_data_flat070 : CoefficientMerge.Poly := [(nat_lit 1254, Int.ofNat (nat_lit 43397280))]
theorem block006_data_flat070_step : block006_data_flat070 = (CoefficientMerge.scale (43397280 : Int) atom0510Coded) := by decide +kernel
theorem block006_data_flat070_original : block006_data_flat070 = (CoefficientMerge.scale (43397280 : Int) atom0510Coded) := by
  rw [block006_data_flat070_step]
def block006_data_flat071 : CoefficientMerge.Poly := [(nat_lit 1255, Int.ofNat (nat_lit 36727920))]
theorem block006_data_flat071_step : block006_data_flat071 = (CoefficientMerge.scale (36727920 : Int) atom0511Coded) := by decide +kernel
theorem block006_data_flat071_original : block006_data_flat071 = (CoefficientMerge.scale (36727920 : Int) atom0511Coded) := by
  rw [block006_data_flat071_step]
def block006_data_flat072 : CoefficientMerge.Poly := [(nat_lit 1256, Int.ofNat (nat_lit 52757280))]
theorem block006_data_flat072_step : block006_data_flat072 = (CoefficientMerge.scale (52757280 : Int) atom0512Coded) := by decide +kernel
theorem block006_data_flat072_original : block006_data_flat072 = (CoefficientMerge.scale (52757280 : Int) atom0512Coded) := by
  rw [block006_data_flat072_step]
def block006_data_flat073 : CoefficientMerge.Poly := [(nat_lit 1255, Int.ofNat (nat_lit 36727920)), (nat_lit 1256, Int.ofNat (nat_lit 52757280))]
theorem block006_data_flat073_step : block006_data_flat073 = (CoefficientMerge.fastMerge block006_data_flat071 block006_data_flat072) := by decide +kernel
theorem block006_data_flat073_original : block006_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36727920 : Int) atom0511Coded) (CoefficientMerge.scale (52757280 : Int) atom0512Coded)) := by
  rw [block006_data_flat073_step, block006_data_flat071_original, block006_data_flat072_original]
def block006_data_flat074 : CoefficientMerge.Poly := [(nat_lit 1254, Int.ofNat (nat_lit 43397280)), (nat_lit 1255, Int.ofNat (nat_lit 36727920)), (nat_lit 1256, Int.ofNat (nat_lit 52757280))]
theorem block006_data_flat074_step : block006_data_flat074 = (CoefficientMerge.fastMerge block006_data_flat070 block006_data_flat073) := by decide +kernel
theorem block006_data_flat074_original : block006_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (43397280 : Int) atom0510Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36727920 : Int) atom0511Coded) (CoefficientMerge.scale (52757280 : Int) atom0512Coded))) := by
  rw [block006_data_flat074_step, block006_data_flat070_original, block006_data_flat073_original]
def block006_data_flat075 : CoefficientMerge.Poly := [(nat_lit 1244, Int.ofNat (nat_lit 87616080)), (nat_lit 1253, Int.ofNat (nat_lit 16473600)), (nat_lit 1254, Int.ofNat (nat_lit 43397280)), (nat_lit 1255, Int.ofNat (nat_lit 36727920)), (nat_lit 1256, Int.ofNat (nat_lit 52757280))]
theorem block006_data_flat075_step : block006_data_flat075 = (CoefficientMerge.fastMerge block006_data_flat069 block006_data_flat074) := by decide +kernel
theorem block006_data_flat075_original : block006_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87616080 : Int) atom0508Coded) (CoefficientMerge.scale (16473600 : Int) atom0509Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43397280 : Int) atom0510Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36727920 : Int) atom0511Coded) (CoefficientMerge.scale (52757280 : Int) atom0512Coded)))) := by
  rw [block006_data_flat075_step, block006_data_flat069_original, block006_data_flat074_original]
def block006_data_flat076 : CoefficientMerge.Poly := [(nat_lit 1239, Int.ofNat (nat_lit 25904640)), (nat_lit 1240, Int.ofNat (nat_lit 16650960)), (nat_lit 1241, Int.ofNat (nat_lit 23597280)), (nat_lit 1242, Int.ofNat (nat_lit 40870320)), (nat_lit 1243, Int.ofNat (nat_lit 62623920)), (nat_lit 1244, Int.ofNat (nat_lit 87616080)), (nat_lit 1253, Int.ofNat (nat_lit 16473600)), (nat_lit 1254, Int.ofNat (nat_lit 43397280)), (nat_lit 1255, Int.ofNat (nat_lit 36727920)), (nat_lit 1256, Int.ofNat (nat_lit 52757280))]
theorem block006_data_flat076_step : block006_data_flat076 = (CoefficientMerge.fastMerge block006_data_flat066 block006_data_flat075) := by decide +kernel
theorem block006_data_flat076_original : block006_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25904640 : Int) atom0503Coded) (CoefficientMerge.scale (16650960 : Int) atom0504Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23597280 : Int) atom0505Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40870320 : Int) atom0506Coded) (CoefficientMerge.scale (62623920 : Int) atom0507Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87616080 : Int) atom0508Coded) (CoefficientMerge.scale (16473600 : Int) atom0509Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43397280 : Int) atom0510Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36727920 : Int) atom0511Coded) (CoefficientMerge.scale (52757280 : Int) atom0512Coded))))) := by
  rw [block006_data_flat076_step, block006_data_flat066_original, block006_data_flat075_original]
def block006_data_flat077 : CoefficientMerge.Poly := [(nat_lit 1209, Int.ofNat (nat_lit 11719440)), (nat_lit 1221, Int.ofNat (nat_lit 1664640)), (nat_lit 1222, Int.ofNat (nat_lit 5230080)), (nat_lit 1223, Int.ofNat (nat_lit 7130880)), (nat_lit 1224, Int.ofNat (nat_lit 17790048)), (nat_lit 1227, Int.ofNat (nat_lit 15029280)), (nat_lit 1228, Int.ofNat (nat_lit 31033728)), (nat_lit 1229, Int.ofNat (nat_lit 50347440)), (nat_lit 1237, Int.ofNat (nat_lit 7777920)), (nat_lit 1238, Int.ofNat (nat_lit 18124800)), (nat_lit 1239, Int.ofNat (nat_lit 25904640)), (nat_lit 1240, Int.ofNat (nat_lit 16650960)), (nat_lit 1241, Int.ofNat (nat_lit 23597280)), (nat_lit 1242, Int.ofNat (nat_lit 40870320)), (nat_lit 1243, Int.ofNat (nat_lit 62623920)), (nat_lit 1244, Int.ofNat (nat_lit 87616080)), (nat_lit 1253, Int.ofNat (nat_lit 16473600)), (nat_lit 1254, Int.ofNat (nat_lit 43397280)), (nat_lit 1255, Int.ofNat (nat_lit 36727920)), (nat_lit 1256, Int.ofNat (nat_lit 52757280))]
theorem block006_data_flat077_step : block006_data_flat077 = (CoefficientMerge.fastMerge block006_data_flat057 block006_data_flat076) := by decide +kernel
theorem block006_data_flat077_original : block006_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11719440 : Int) atom0493Coded) (CoefficientMerge.scale (1664640 : Int) atom0494Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5230080 : Int) atom0495Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7130880 : Int) atom0496Coded) (CoefficientMerge.scale (17790048 : Int) atom0497Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15029280 : Int) atom0498Coded) (CoefficientMerge.scale (31033728 : Int) atom0499Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50347440 : Int) atom0500Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777920 : Int) atom0501Coded) (CoefficientMerge.scale (18124800 : Int) atom0502Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25904640 : Int) atom0503Coded) (CoefficientMerge.scale (16650960 : Int) atom0504Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23597280 : Int) atom0505Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40870320 : Int) atom0506Coded) (CoefficientMerge.scale (62623920 : Int) atom0507Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87616080 : Int) atom0508Coded) (CoefficientMerge.scale (16473600 : Int) atom0509Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43397280 : Int) atom0510Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36727920 : Int) atom0511Coded) (CoefficientMerge.scale (52757280 : Int) atom0512Coded)))))) := by
  rw [block006_data_flat077_step, block006_data_flat057_original, block006_data_flat076_original]
def block006_data_flat078 : CoefficientMerge.Poly := [(nat_lit 1046, Int.ofNat (nat_lit 159550560)), (nat_lit 1047, Int.ofNat (nat_lit 175445640)), (nat_lit 1048, Int.ofNat (nat_lit 116951400)), (nat_lit 1049, Int.ofNat (nat_lit 194537160)), (nat_lit 1060, Int.ofNat (nat_lit 46998144)), (nat_lit 1061, Int.ofNat (nat_lit 129823920)), (nat_lit 1062, Int.ofNat (nat_lit 162877500)), (nat_lit 1063, Int.ofNat (nat_lit 119768400)), (nat_lit 1064, Int.ofNat (nat_lit 159341850)), (nat_lit 1076, Int.ofNat (nat_lit 94131720)), (nat_lit 1077, Int.ofNat (nat_lit 168209280)), (nat_lit 1078, Int.ofNat (nat_lit 124651080)), (nat_lit 1079, Int.ofNat (nat_lit 182713320)), (nat_lit 1092, Int.ofNat (nat_lit 61220340)), (nat_lit 1093, Int.ofNat (nat_lit 93601620)), (nat_lit 1094, Int.ofNat (nat_lit 161695170)), (nat_lit 1108, Int.ofNat (nat_lit 15015600)), (nat_lit 1109, Int.ofNat (nat_lit 105901830)), (nat_lit 1124, Int.ofNat (nat_lit 84255390)), (nat_lit 1205, Int.ofNat (nat_lit 633600)), (nat_lit 1209, Int.ofNat (nat_lit 11719440)), (nat_lit 1221, Int.ofNat (nat_lit 1664640)), (nat_lit 1222, Int.ofNat (nat_lit 5230080)), (nat_lit 1223, Int.ofNat (nat_lit 7130880)), (nat_lit 1224, Int.ofNat (nat_lit 17790048)), (nat_lit 1227, Int.ofNat (nat_lit 15029280)), (nat_lit 1228, Int.ofNat (nat_lit 31033728)), (nat_lit 1229, Int.ofNat (nat_lit 50347440)), (nat_lit 1237, Int.ofNat (nat_lit 7777920)), (nat_lit 1238, Int.ofNat (nat_lit 18124800)), (nat_lit 1239, Int.ofNat (nat_lit 25904640)), (nat_lit 1240, Int.ofNat (nat_lit 16650960)), (nat_lit 1241, Int.ofNat (nat_lit 23597280)), (nat_lit 1242, Int.ofNat (nat_lit 40870320)), (nat_lit 1243, Int.ofNat (nat_lit 62623920)), (nat_lit 1244, Int.ofNat (nat_lit 87616080)), (nat_lit 1253, Int.ofNat (nat_lit 16473600)), (nat_lit 1254, Int.ofNat (nat_lit 43397280)), (nat_lit 1255, Int.ofNat (nat_lit 36727920)), (nat_lit 1256, Int.ofNat (nat_lit 52757280))]
theorem block006_data_flat078_step : block006_data_flat078 = (CoefficientMerge.fastMerge block006_data_flat038 block006_data_flat077) := by decide +kernel
theorem block006_data_flat078_original : block006_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (159550560 : Int) atom0473Coded) (CoefficientMerge.scale (175445640 : Int) atom0474Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (116951400 : Int) atom0475Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (194537160 : Int) atom0476Coded) (CoefficientMerge.scale (46998144 : Int) atom0477Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129823920 : Int) atom0478Coded) (CoefficientMerge.scale (162877500 : Int) atom0479Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119768400 : Int) atom0480Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (159341850 : Int) atom0481Coded) (CoefficientMerge.scale (94131720 : Int) atom0482Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (168209280 : Int) atom0483Coded) (CoefficientMerge.scale (124651080 : Int) atom0484Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182713320 : Int) atom0485Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61220340 : Int) atom0486Coded) (CoefficientMerge.scale (93601620 : Int) atom0487Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (161695170 : Int) atom0488Coded) (CoefficientMerge.scale (15015600 : Int) atom0489Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105901830 : Int) atom0490Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84255390 : Int) atom0491Coded) (CoefficientMerge.scale (633600 : Int) atom0492Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11719440 : Int) atom0493Coded) (CoefficientMerge.scale (1664640 : Int) atom0494Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5230080 : Int) atom0495Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7130880 : Int) atom0496Coded) (CoefficientMerge.scale (17790048 : Int) atom0497Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15029280 : Int) atom0498Coded) (CoefficientMerge.scale (31033728 : Int) atom0499Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50347440 : Int) atom0500Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777920 : Int) atom0501Coded) (CoefficientMerge.scale (18124800 : Int) atom0502Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25904640 : Int) atom0503Coded) (CoefficientMerge.scale (16650960 : Int) atom0504Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23597280 : Int) atom0505Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40870320 : Int) atom0506Coded) (CoefficientMerge.scale (62623920 : Int) atom0507Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87616080 : Int) atom0508Coded) (CoefficientMerge.scale (16473600 : Int) atom0509Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43397280 : Int) atom0510Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36727920 : Int) atom0511Coded) (CoefficientMerge.scale (52757280 : Int) atom0512Coded))))))) := by
  rw [block006_data_flat078_step, block006_data_flat038_original, block006_data_flat077_original]
def block006_data_flat079 : CoefficientMerge.Poly := [(nat_lit 1257, Int.ofNat (nat_lit 73305360))]
theorem block006_data_flat079_step : block006_data_flat079 = (CoefficientMerge.scale (73305360 : Int) atom0513Coded) := by decide +kernel
theorem block006_data_flat079_original : block006_data_flat079 = (CoefficientMerge.scale (73305360 : Int) atom0513Coded) := by
  rw [block006_data_flat079_step]
def block006_data_flat080 : CoefficientMerge.Poly := [(nat_lit 1258, Int.ofNat (nat_lit 86870160))]
theorem block006_data_flat080_step : block006_data_flat080 = (CoefficientMerge.scale (86870160 : Int) atom0514Coded) := by decide +kernel
theorem block006_data_flat080_original : block006_data_flat080 = (CoefficientMerge.scale (86870160 : Int) atom0514Coded) := by
  rw [block006_data_flat080_step]
def block006_data_flat081 : CoefficientMerge.Poly := [(nat_lit 1257, Int.ofNat (nat_lit 73305360)), (nat_lit 1258, Int.ofNat (nat_lit 86870160))]
theorem block006_data_flat081_step : block006_data_flat081 = (CoefficientMerge.fastMerge block006_data_flat079 block006_data_flat080) := by decide +kernel
theorem block006_data_flat081_original : block006_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (73305360 : Int) atom0513Coded) (CoefficientMerge.scale (86870160 : Int) atom0514Coded)) := by
  rw [block006_data_flat081_step, block006_data_flat079_original, block006_data_flat080_original]
def block006_data_flat082 : CoefficientMerge.Poly := [(nat_lit 1259, Int.ofNat (nat_lit 142287840))]
theorem block006_data_flat082_step : block006_data_flat082 = (CoefficientMerge.scale (142287840 : Int) atom0515Coded) := by decide +kernel
theorem block006_data_flat082_original : block006_data_flat082 = (CoefficientMerge.scale (142287840 : Int) atom0515Coded) := by
  rw [block006_data_flat082_step]
def block006_data_flat083 : CoefficientMerge.Poly := [(nat_lit 1269, Int.ofNat (nat_lit 44323200))]
theorem block006_data_flat083_step : block006_data_flat083 = (CoefficientMerge.scale (44323200 : Int) atom0516Coded) := by decide +kernel
theorem block006_data_flat083_original : block006_data_flat083 = (CoefficientMerge.scale (44323200 : Int) atom0516Coded) := by
  rw [block006_data_flat083_step]
def block006_data_flat084 : CoefficientMerge.Poly := [(nat_lit 1270, Int.ofNat (nat_lit 82846440))]
theorem block006_data_flat084_step : block006_data_flat084 = (CoefficientMerge.scale (82846440 : Int) atom0517Coded) := by decide +kernel
theorem block006_data_flat084_original : block006_data_flat084 = (CoefficientMerge.scale (82846440 : Int) atom0517Coded) := by
  rw [block006_data_flat084_step]
def block006_data_flat085 : CoefficientMerge.Poly := [(nat_lit 1269, Int.ofNat (nat_lit 44323200)), (nat_lit 1270, Int.ofNat (nat_lit 82846440))]
theorem block006_data_flat085_step : block006_data_flat085 = (CoefficientMerge.fastMerge block006_data_flat083 block006_data_flat084) := by decide +kernel
theorem block006_data_flat085_original : block006_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (44323200 : Int) atom0516Coded) (CoefficientMerge.scale (82846440 : Int) atom0517Coded)) := by
  rw [block006_data_flat085_step, block006_data_flat083_original, block006_data_flat084_original]
def block006_data_flat086 : CoefficientMerge.Poly := [(nat_lit 1259, Int.ofNat (nat_lit 142287840)), (nat_lit 1269, Int.ofNat (nat_lit 44323200)), (nat_lit 1270, Int.ofNat (nat_lit 82846440))]
theorem block006_data_flat086_step : block006_data_flat086 = (CoefficientMerge.fastMerge block006_data_flat082 block006_data_flat085) := by decide +kernel
theorem block006_data_flat086_original : block006_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (142287840 : Int) atom0515Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44323200 : Int) atom0516Coded) (CoefficientMerge.scale (82846440 : Int) atom0517Coded))) := by
  rw [block006_data_flat086_step, block006_data_flat082_original, block006_data_flat085_original]
def block006_data_flat087 : CoefficientMerge.Poly := [(nat_lit 1257, Int.ofNat (nat_lit 73305360)), (nat_lit 1258, Int.ofNat (nat_lit 86870160)), (nat_lit 1259, Int.ofNat (nat_lit 142287840)), (nat_lit 1269, Int.ofNat (nat_lit 44323200)), (nat_lit 1270, Int.ofNat (nat_lit 82846440))]
theorem block006_data_flat087_step : block006_data_flat087 = (CoefficientMerge.fastMerge block006_data_flat081 block006_data_flat086) := by decide +kernel
theorem block006_data_flat087_original : block006_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (73305360 : Int) atom0513Coded) (CoefficientMerge.scale (86870160 : Int) atom0514Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (142287840 : Int) atom0515Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44323200 : Int) atom0516Coded) (CoefficientMerge.scale (82846440 : Int) atom0517Coded)))) := by
  rw [block006_data_flat087_step, block006_data_flat081_original, block006_data_flat086_original]
def block006_data_flat088 : CoefficientMerge.Poly := [(nat_lit 1271, Int.ofNat (nat_lit 142823520))]
theorem block006_data_flat088_step : block006_data_flat088 = (CoefficientMerge.scale (142823520 : Int) atom0518Coded) := by decide +kernel
theorem block006_data_flat088_original : block006_data_flat088 = (CoefficientMerge.scale (142823520 : Int) atom0518Coded) := by
  rw [block006_data_flat088_step]
def block006_data_flat089 : CoefficientMerge.Poly := [(nat_lit 1272, Int.ofNat (nat_lit 167162040))]
theorem block006_data_flat089_step : block006_data_flat089 = (CoefficientMerge.scale (167162040 : Int) atom0519Coded) := by decide +kernel
theorem block006_data_flat089_original : block006_data_flat089 = (CoefficientMerge.scale (167162040 : Int) atom0519Coded) := by
  rw [block006_data_flat089_step]
def block006_data_flat090 : CoefficientMerge.Poly := [(nat_lit 1271, Int.ofNat (nat_lit 142823520)), (nat_lit 1272, Int.ofNat (nat_lit 167162040))]
theorem block006_data_flat090_step : block006_data_flat090 = (CoefficientMerge.fastMerge block006_data_flat088 block006_data_flat089) := by decide +kernel
theorem block006_data_flat090_original : block006_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (142823520 : Int) atom0518Coded) (CoefficientMerge.scale (167162040 : Int) atom0519Coded)) := by
  rw [block006_data_flat090_step, block006_data_flat088_original, block006_data_flat089_original]
def block006_data_flat091 : CoefficientMerge.Poly := [(nat_lit 1273, Int.ofNat (nat_lit 115337880))]
theorem block006_data_flat091_step : block006_data_flat091 = (CoefficientMerge.scale (115337880 : Int) atom0520Coded) := by decide +kernel
theorem block006_data_flat091_original : block006_data_flat091 = (CoefficientMerge.scale (115337880 : Int) atom0520Coded) := by
  rw [block006_data_flat091_step]
def block006_data_flat092 : CoefficientMerge.Poly := [(nat_lit 1274, Int.ofNat (nat_lit 199593720))]
theorem block006_data_flat092_step : block006_data_flat092 = (CoefficientMerge.scale (199593720 : Int) atom0521Coded) := by decide +kernel
theorem block006_data_flat092_original : block006_data_flat092 = (CoefficientMerge.scale (199593720 : Int) atom0521Coded) := by
  rw [block006_data_flat092_step]
def block006_data_flat093 : CoefficientMerge.Poly := [(nat_lit 1285, Int.ofNat (nat_lit 36733824))]
theorem block006_data_flat093_step : block006_data_flat093 = (CoefficientMerge.scale (36733824 : Int) atom0522Coded) := by decide +kernel
theorem block006_data_flat093_original : block006_data_flat093 = (CoefficientMerge.scale (36733824 : Int) atom0522Coded) := by
  rw [block006_data_flat093_step]
def block006_data_flat094 : CoefficientMerge.Poly := [(nat_lit 1274, Int.ofNat (nat_lit 199593720)), (nat_lit 1285, Int.ofNat (nat_lit 36733824))]
theorem block006_data_flat094_step : block006_data_flat094 = (CoefficientMerge.fastMerge block006_data_flat092 block006_data_flat093) := by decide +kernel
theorem block006_data_flat094_original : block006_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (199593720 : Int) atom0521Coded) (CoefficientMerge.scale (36733824 : Int) atom0522Coded)) := by
  rw [block006_data_flat094_step, block006_data_flat092_original, block006_data_flat093_original]
def block006_data_flat095 : CoefficientMerge.Poly := [(nat_lit 1273, Int.ofNat (nat_lit 115337880)), (nat_lit 1274, Int.ofNat (nat_lit 199593720)), (nat_lit 1285, Int.ofNat (nat_lit 36733824))]
theorem block006_data_flat095_step : block006_data_flat095 = (CoefficientMerge.fastMerge block006_data_flat091 block006_data_flat094) := by decide +kernel
theorem block006_data_flat095_original : block006_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (115337880 : Int) atom0520Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199593720 : Int) atom0521Coded) (CoefficientMerge.scale (36733824 : Int) atom0522Coded))) := by
  rw [block006_data_flat095_step, block006_data_flat091_original, block006_data_flat094_original]
def block006_data_flat096 : CoefficientMerge.Poly := [(nat_lit 1271, Int.ofNat (nat_lit 142823520)), (nat_lit 1272, Int.ofNat (nat_lit 167162040)), (nat_lit 1273, Int.ofNat (nat_lit 115337880)), (nat_lit 1274, Int.ofNat (nat_lit 199593720)), (nat_lit 1285, Int.ofNat (nat_lit 36733824))]
theorem block006_data_flat096_step : block006_data_flat096 = (CoefficientMerge.fastMerge block006_data_flat090 block006_data_flat095) := by decide +kernel
theorem block006_data_flat096_original : block006_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142823520 : Int) atom0518Coded) (CoefficientMerge.scale (167162040 : Int) atom0519Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115337880 : Int) atom0520Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199593720 : Int) atom0521Coded) (CoefficientMerge.scale (36733824 : Int) atom0522Coded)))) := by
  rw [block006_data_flat096_step, block006_data_flat090_original, block006_data_flat095_original]
def block006_data_flat097 : CoefficientMerge.Poly := [(nat_lit 1257, Int.ofNat (nat_lit 73305360)), (nat_lit 1258, Int.ofNat (nat_lit 86870160)), (nat_lit 1259, Int.ofNat (nat_lit 142287840)), (nat_lit 1269, Int.ofNat (nat_lit 44323200)), (nat_lit 1270, Int.ofNat (nat_lit 82846440)), (nat_lit 1271, Int.ofNat (nat_lit 142823520)), (nat_lit 1272, Int.ofNat (nat_lit 167162040)), (nat_lit 1273, Int.ofNat (nat_lit 115337880)), (nat_lit 1274, Int.ofNat (nat_lit 199593720)), (nat_lit 1285, Int.ofNat (nat_lit 36733824))]
theorem block006_data_flat097_step : block006_data_flat097 = (CoefficientMerge.fastMerge block006_data_flat087 block006_data_flat096) := by decide +kernel
theorem block006_data_flat097_original : block006_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (73305360 : Int) atom0513Coded) (CoefficientMerge.scale (86870160 : Int) atom0514Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (142287840 : Int) atom0515Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44323200 : Int) atom0516Coded) (CoefficientMerge.scale (82846440 : Int) atom0517Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142823520 : Int) atom0518Coded) (CoefficientMerge.scale (167162040 : Int) atom0519Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115337880 : Int) atom0520Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199593720 : Int) atom0521Coded) (CoefficientMerge.scale (36733824 : Int) atom0522Coded))))) := by
  rw [block006_data_flat097_step, block006_data_flat087_original, block006_data_flat096_original]
def block006_data_flat098 : CoefficientMerge.Poly := [(nat_lit 1286, Int.ofNat (nat_lit 114498720))]
theorem block006_data_flat098_step : block006_data_flat098 = (CoefficientMerge.scale (114498720 : Int) atom0523Coded) := by decide +kernel
theorem block006_data_flat098_original : block006_data_flat098 = (CoefficientMerge.scale (114498720 : Int) atom0523Coded) := by
  rw [block006_data_flat098_step]
def block006_data_flat099 : CoefficientMerge.Poly := [(nat_lit 1287, Int.ofNat (nat_lit 154214820))]
theorem block006_data_flat099_step : block006_data_flat099 = (CoefficientMerge.scale (154214820 : Int) atom0524Coded) := by decide +kernel
theorem block006_data_flat099_original : block006_data_flat099 = (CoefficientMerge.scale (154214820 : Int) atom0524Coded) := by
  rw [block006_data_flat099_step]
def block006_data_flat100 : CoefficientMerge.Poly := [(nat_lit 1286, Int.ofNat (nat_lit 114498720)), (nat_lit 1287, Int.ofNat (nat_lit 154214820))]
theorem block006_data_flat100_step : block006_data_flat100 = (CoefficientMerge.fastMerge block006_data_flat098 block006_data_flat099) := by decide +kernel
theorem block006_data_flat100_original : block006_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (114498720 : Int) atom0523Coded) (CoefficientMerge.scale (154214820 : Int) atom0524Coded)) := by
  rw [block006_data_flat100_step, block006_data_flat098_original, block006_data_flat099_original]
def block006_data_flat101 : CoefficientMerge.Poly := [(nat_lit 1288, Int.ofNat (nat_lit 117768240))]
theorem block006_data_flat101_step : block006_data_flat101 = (CoefficientMerge.scale (117768240 : Int) atom0525Coded) := by decide +kernel
theorem block006_data_flat101_original : block006_data_flat101 = (CoefficientMerge.scale (117768240 : Int) atom0525Coded) := by
  rw [block006_data_flat101_step]
def block006_data_flat102 : CoefficientMerge.Poly := [(nat_lit 1289, Int.ofNat (nat_lit 164733750))]
theorem block006_data_flat102_step : block006_data_flat102 = (CoefficientMerge.scale (164733750 : Int) atom0526Coded) := by decide +kernel
theorem block006_data_flat102_original : block006_data_flat102 = (CoefficientMerge.scale (164733750 : Int) atom0526Coded) := by
  rw [block006_data_flat102_step]
def block006_data_flat103 : CoefficientMerge.Poly := [(nat_lit 1301, Int.ofNat (nat_lit 90088200))]
theorem block006_data_flat103_step : block006_data_flat103 = (CoefficientMerge.scale (90088200 : Int) atom0527Coded) := by decide +kernel
theorem block006_data_flat103_original : block006_data_flat103 = (CoefficientMerge.scale (90088200 : Int) atom0527Coded) := by
  rw [block006_data_flat103_step]
def block006_data_flat104 : CoefficientMerge.Poly := [(nat_lit 1289, Int.ofNat (nat_lit 164733750)), (nat_lit 1301, Int.ofNat (nat_lit 90088200))]
theorem block006_data_flat104_step : block006_data_flat104 = (CoefficientMerge.fastMerge block006_data_flat102 block006_data_flat103) := by decide +kernel
theorem block006_data_flat104_original : block006_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (164733750 : Int) atom0526Coded) (CoefficientMerge.scale (90088200 : Int) atom0527Coded)) := by
  rw [block006_data_flat104_step, block006_data_flat102_original, block006_data_flat103_original]
def block006_data_flat105 : CoefficientMerge.Poly := [(nat_lit 1288, Int.ofNat (nat_lit 117768240)), (nat_lit 1289, Int.ofNat (nat_lit 164733750)), (nat_lit 1301, Int.ofNat (nat_lit 90088200))]
theorem block006_data_flat105_step : block006_data_flat105 = (CoefficientMerge.fastMerge block006_data_flat101 block006_data_flat104) := by decide +kernel
theorem block006_data_flat105_original : block006_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (117768240 : Int) atom0525Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164733750 : Int) atom0526Coded) (CoefficientMerge.scale (90088200 : Int) atom0527Coded))) := by
  rw [block006_data_flat105_step, block006_data_flat101_original, block006_data_flat104_original]
def block006_data_flat106 : CoefficientMerge.Poly := [(nat_lit 1286, Int.ofNat (nat_lit 114498720)), (nat_lit 1287, Int.ofNat (nat_lit 154214820)), (nat_lit 1288, Int.ofNat (nat_lit 117768240)), (nat_lit 1289, Int.ofNat (nat_lit 164733750)), (nat_lit 1301, Int.ofNat (nat_lit 90088200))]
theorem block006_data_flat106_step : block006_data_flat106 = (CoefficientMerge.fastMerge block006_data_flat100 block006_data_flat105) := by decide +kernel
theorem block006_data_flat106_original : block006_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (114498720 : Int) atom0523Coded) (CoefficientMerge.scale (154214820 : Int) atom0524Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117768240 : Int) atom0525Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164733750 : Int) atom0526Coded) (CoefficientMerge.scale (90088200 : Int) atom0527Coded)))) := by
  rw [block006_data_flat106_step, block006_data_flat100_original, block006_data_flat105_original]
def block006_data_flat107 : CoefficientMerge.Poly := [(nat_lit 1302, Int.ofNat (nat_lit 167922000))]
theorem block006_data_flat107_step : block006_data_flat107 = (CoefficientMerge.scale (167922000 : Int) atom0528Coded) := by decide +kernel
theorem block006_data_flat107_original : block006_data_flat107 = (CoefficientMerge.scale (167922000 : Int) atom0528Coded) := by
  rw [block006_data_flat107_step]
def block006_data_flat108 : CoefficientMerge.Poly := [(nat_lit 1303, Int.ofNat (nat_lit 133936920))]
theorem block006_data_flat108_step : block006_data_flat108 = (CoefficientMerge.scale (133936920 : Int) atom0529Coded) := by decide +kernel
theorem block006_data_flat108_original : block006_data_flat108 = (CoefficientMerge.scale (133936920 : Int) atom0529Coded) := by
  rw [block006_data_flat108_step]
def block006_data_flat109 : CoefficientMerge.Poly := [(nat_lit 1302, Int.ofNat (nat_lit 167922000)), (nat_lit 1303, Int.ofNat (nat_lit 133936920))]
theorem block006_data_flat109_step : block006_data_flat109 = (CoefficientMerge.fastMerge block006_data_flat107 block006_data_flat108) := by decide +kernel
theorem block006_data_flat109_original : block006_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (167922000 : Int) atom0528Coded) (CoefficientMerge.scale (133936920 : Int) atom0529Coded)) := by
  rw [block006_data_flat109_step, block006_data_flat107_original, block006_data_flat108_original]
def block006_data_flat110 : CoefficientMerge.Poly := [(nat_lit 1304, Int.ofNat (nat_lit 201572280))]
theorem block006_data_flat110_step : block006_data_flat110 = (CoefficientMerge.scale (201572280 : Int) atom0530Coded) := by decide +kernel
theorem block006_data_flat110_original : block006_data_flat110 = (CoefficientMerge.scale (201572280 : Int) atom0530Coded) := by
  rw [block006_data_flat110_step]
def block006_data_flat111 : CoefficientMerge.Poly := [(nat_lit 1317, Int.ofNat (nat_lit 62318700))]
theorem block006_data_flat111_step : block006_data_flat111 = (CoefficientMerge.scale (62318700 : Int) atom0531Coded) := by decide +kernel
theorem block006_data_flat111_original : block006_data_flat111 = (CoefficientMerge.scale (62318700 : Int) atom0531Coded) := by
  rw [block006_data_flat111_step]
def block006_data_flat112 : CoefficientMerge.Poly := [(nat_lit 1318, Int.ofNat (nat_lit 105936300))]
theorem block006_data_flat112_step : block006_data_flat112 = (CoefficientMerge.scale (105936300 : Int) atom0532Coded) := by decide +kernel
theorem block006_data_flat112_original : block006_data_flat112 = (CoefficientMerge.scale (105936300 : Int) atom0532Coded) := by
  rw [block006_data_flat112_step]
def block006_data_flat113 : CoefficientMerge.Poly := [(nat_lit 1317, Int.ofNat (nat_lit 62318700)), (nat_lit 1318, Int.ofNat (nat_lit 105936300))]
theorem block006_data_flat113_step : block006_data_flat113 = (CoefficientMerge.fastMerge block006_data_flat111 block006_data_flat112) := by decide +kernel
theorem block006_data_flat113_original : block006_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (62318700 : Int) atom0531Coded) (CoefficientMerge.scale (105936300 : Int) atom0532Coded)) := by
  rw [block006_data_flat113_step, block006_data_flat111_original, block006_data_flat112_original]
def block006_data_flat114 : CoefficientMerge.Poly := [(nat_lit 1304, Int.ofNat (nat_lit 201572280)), (nat_lit 1317, Int.ofNat (nat_lit 62318700)), (nat_lit 1318, Int.ofNat (nat_lit 105936300))]
theorem block006_data_flat114_step : block006_data_flat114 = (CoefficientMerge.fastMerge block006_data_flat110 block006_data_flat113) := by decide +kernel
theorem block006_data_flat114_original : block006_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (201572280 : Int) atom0530Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62318700 : Int) atom0531Coded) (CoefficientMerge.scale (105936300 : Int) atom0532Coded))) := by
  rw [block006_data_flat114_step, block006_data_flat110_original, block006_data_flat113_original]
def block006_data_flat115 : CoefficientMerge.Poly := [(nat_lit 1302, Int.ofNat (nat_lit 167922000)), (nat_lit 1303, Int.ofNat (nat_lit 133936920)), (nat_lit 1304, Int.ofNat (nat_lit 201572280)), (nat_lit 1317, Int.ofNat (nat_lit 62318700)), (nat_lit 1318, Int.ofNat (nat_lit 105936300))]
theorem block006_data_flat115_step : block006_data_flat115 = (CoefficientMerge.fastMerge block006_data_flat109 block006_data_flat114) := by decide +kernel
theorem block006_data_flat115_original : block006_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (167922000 : Int) atom0528Coded) (CoefficientMerge.scale (133936920 : Int) atom0529Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (201572280 : Int) atom0530Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62318700 : Int) atom0531Coded) (CoefficientMerge.scale (105936300 : Int) atom0532Coded)))) := by
  rw [block006_data_flat115_step, block006_data_flat109_original, block006_data_flat114_original]
def block006_data_flat116 : CoefficientMerge.Poly := [(nat_lit 1286, Int.ofNat (nat_lit 114498720)), (nat_lit 1287, Int.ofNat (nat_lit 154214820)), (nat_lit 1288, Int.ofNat (nat_lit 117768240)), (nat_lit 1289, Int.ofNat (nat_lit 164733750)), (nat_lit 1301, Int.ofNat (nat_lit 90088200)), (nat_lit 1302, Int.ofNat (nat_lit 167922000)), (nat_lit 1303, Int.ofNat (nat_lit 133936920)), (nat_lit 1304, Int.ofNat (nat_lit 201572280)), (nat_lit 1317, Int.ofNat (nat_lit 62318700)), (nat_lit 1318, Int.ofNat (nat_lit 105936300))]
theorem block006_data_flat116_step : block006_data_flat116 = (CoefficientMerge.fastMerge block006_data_flat106 block006_data_flat115) := by decide +kernel
theorem block006_data_flat116_original : block006_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (114498720 : Int) atom0523Coded) (CoefficientMerge.scale (154214820 : Int) atom0524Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117768240 : Int) atom0525Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164733750 : Int) atom0526Coded) (CoefficientMerge.scale (90088200 : Int) atom0527Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (167922000 : Int) atom0528Coded) (CoefficientMerge.scale (133936920 : Int) atom0529Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (201572280 : Int) atom0530Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62318700 : Int) atom0531Coded) (CoefficientMerge.scale (105936300 : Int) atom0532Coded))))) := by
  rw [block006_data_flat116_step, block006_data_flat106_original, block006_data_flat115_original]
def block006_data_flat117 : CoefficientMerge.Poly := [(nat_lit 1257, Int.ofNat (nat_lit 73305360)), (nat_lit 1258, Int.ofNat (nat_lit 86870160)), (nat_lit 1259, Int.ofNat (nat_lit 142287840)), (nat_lit 1269, Int.ofNat (nat_lit 44323200)), (nat_lit 1270, Int.ofNat (nat_lit 82846440)), (nat_lit 1271, Int.ofNat (nat_lit 142823520)), (nat_lit 1272, Int.ofNat (nat_lit 167162040)), (nat_lit 1273, Int.ofNat (nat_lit 115337880)), (nat_lit 1274, Int.ofNat (nat_lit 199593720)), (nat_lit 1285, Int.ofNat (nat_lit 36733824)), (nat_lit 1286, Int.ofNat (nat_lit 114498720)), (nat_lit 1287, Int.ofNat (nat_lit 154214820)), (nat_lit 1288, Int.ofNat (nat_lit 117768240)), (nat_lit 1289, Int.ofNat (nat_lit 164733750)), (nat_lit 1301, Int.ofNat (nat_lit 90088200)), (nat_lit 1302, Int.ofNat (nat_lit 167922000)), (nat_lit 1303, Int.ofNat (nat_lit 133936920)), (nat_lit 1304, Int.ofNat (nat_lit 201572280)), (nat_lit 1317, Int.ofNat (nat_lit 62318700)), (nat_lit 1318, Int.ofNat (nat_lit 105936300))]
theorem block006_data_flat117_step : block006_data_flat117 = (CoefficientMerge.fastMerge block006_data_flat097 block006_data_flat116) := by decide +kernel
theorem block006_data_flat117_original : block006_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (73305360 : Int) atom0513Coded) (CoefficientMerge.scale (86870160 : Int) atom0514Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (142287840 : Int) atom0515Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44323200 : Int) atom0516Coded) (CoefficientMerge.scale (82846440 : Int) atom0517Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142823520 : Int) atom0518Coded) (CoefficientMerge.scale (167162040 : Int) atom0519Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115337880 : Int) atom0520Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199593720 : Int) atom0521Coded) (CoefficientMerge.scale (36733824 : Int) atom0522Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (114498720 : Int) atom0523Coded) (CoefficientMerge.scale (154214820 : Int) atom0524Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117768240 : Int) atom0525Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164733750 : Int) atom0526Coded) (CoefficientMerge.scale (90088200 : Int) atom0527Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (167922000 : Int) atom0528Coded) (CoefficientMerge.scale (133936920 : Int) atom0529Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (201572280 : Int) atom0530Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62318700 : Int) atom0531Coded) (CoefficientMerge.scale (105936300 : Int) atom0532Coded)))))) := by
  rw [block006_data_flat117_step, block006_data_flat097_original, block006_data_flat116_original]
def block006_data_flat118 : CoefficientMerge.Poly := [(nat_lit 1319, Int.ofNat (nat_lit 184546350))]
theorem block006_data_flat118_step : block006_data_flat118 = (CoefficientMerge.scale (184546350 : Int) atom0533Coded) := by decide +kernel
theorem block006_data_flat118_original : block006_data_flat118 = (CoefficientMerge.scale (184546350 : Int) atom0533Coded) := by
  rw [block006_data_flat118_step]
def block006_data_flat119 : CoefficientMerge.Poly := [(nat_lit 1333, Int.ofNat (nat_lit 24480720))]
theorem block006_data_flat119_step : block006_data_flat119 = (CoefficientMerge.scale (24480720 : Int) atom0534Coded) := by decide +kernel
theorem block006_data_flat119_original : block006_data_flat119 = (CoefficientMerge.scale (24480720 : Int) atom0534Coded) := by
  rw [block006_data_flat119_step]
def block006_data_flat120 : CoefficientMerge.Poly := [(nat_lit 1319, Int.ofNat (nat_lit 184546350)), (nat_lit 1333, Int.ofNat (nat_lit 24480720))]
theorem block006_data_flat120_step : block006_data_flat120 = (CoefficientMerge.fastMerge block006_data_flat118 block006_data_flat119) := by decide +kernel
theorem block006_data_flat120_original : block006_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (184546350 : Int) atom0533Coded) (CoefficientMerge.scale (24480720 : Int) atom0534Coded)) := by
  rw [block006_data_flat120_step, block006_data_flat118_original, block006_data_flat119_original]
def block006_data_flat121 : CoefficientMerge.Poly := [(nat_lit 1334, Int.ofNat (nat_lit 136735290))]
theorem block006_data_flat121_step : block006_data_flat121 = (CoefficientMerge.scale (136735290 : Int) atom0535Coded) := by decide +kernel
theorem block006_data_flat121_original : block006_data_flat121 = (CoefficientMerge.scale (136735290 : Int) atom0535Coded) := by
  rw [block006_data_flat121_step]
def block006_data_flat122 : CoefficientMerge.Poly := [(nat_lit 1349, Int.ofNat (nat_lit 103787730))]
theorem block006_data_flat122_step : block006_data_flat122 = (CoefficientMerge.scale (103787730 : Int) atom0536Coded) := by decide +kernel
theorem block006_data_flat122_original : block006_data_flat122 = (CoefficientMerge.scale (103787730 : Int) atom0536Coded) := by
  rw [block006_data_flat122_step]
def block006_data_flat123 : CoefficientMerge.Poly := [(nat_lit 1449, Int.ofNat (nat_lit 5095440))]
theorem block006_data_flat123_step : block006_data_flat123 = (CoefficientMerge.scale (5095440 : Int) atom0537Coded) := by decide +kernel
theorem block006_data_flat123_original : block006_data_flat123 = (CoefficientMerge.scale (5095440 : Int) atom0537Coded) := by
  rw [block006_data_flat123_step]
def block006_data_flat124 : CoefficientMerge.Poly := [(nat_lit 1349, Int.ofNat (nat_lit 103787730)), (nat_lit 1449, Int.ofNat (nat_lit 5095440))]
theorem block006_data_flat124_step : block006_data_flat124 = (CoefficientMerge.fastMerge block006_data_flat122 block006_data_flat123) := by decide +kernel
theorem block006_data_flat124_original : block006_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (103787730 : Int) atom0536Coded) (CoefficientMerge.scale (5095440 : Int) atom0537Coded)) := by
  rw [block006_data_flat124_step, block006_data_flat122_original, block006_data_flat123_original]
def block006_data_flat125 : CoefficientMerge.Poly := [(nat_lit 1334, Int.ofNat (nat_lit 136735290)), (nat_lit 1349, Int.ofNat (nat_lit 103787730)), (nat_lit 1449, Int.ofNat (nat_lit 5095440))]
theorem block006_data_flat125_step : block006_data_flat125 = (CoefficientMerge.fastMerge block006_data_flat121 block006_data_flat124) := by decide +kernel
theorem block006_data_flat125_original : block006_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (136735290 : Int) atom0535Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103787730 : Int) atom0536Coded) (CoefficientMerge.scale (5095440 : Int) atom0537Coded))) := by
  rw [block006_data_flat125_step, block006_data_flat121_original, block006_data_flat124_original]
def block006_data_flat126 : CoefficientMerge.Poly := [(nat_lit 1319, Int.ofNat (nat_lit 184546350)), (nat_lit 1333, Int.ofNat (nat_lit 24480720)), (nat_lit 1334, Int.ofNat (nat_lit 136735290)), (nat_lit 1349, Int.ofNat (nat_lit 103787730)), (nat_lit 1449, Int.ofNat (nat_lit 5095440))]
theorem block006_data_flat126_step : block006_data_flat126 = (CoefficientMerge.fastMerge block006_data_flat120 block006_data_flat125) := by decide +kernel
theorem block006_data_flat126_original : block006_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (184546350 : Int) atom0533Coded) (CoefficientMerge.scale (24480720 : Int) atom0534Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136735290 : Int) atom0535Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103787730 : Int) atom0536Coded) (CoefficientMerge.scale (5095440 : Int) atom0537Coded)))) := by
  rw [block006_data_flat126_step, block006_data_flat120_original, block006_data_flat125_original]
def block006_data_flat127 : CoefficientMerge.Poly := [(nat_lit 1462, Int.ofNat (nat_lit 2311680))]
theorem block006_data_flat127_step : block006_data_flat127 = (CoefficientMerge.scale (2311680 : Int) atom0538Coded) := by decide +kernel
theorem block006_data_flat127_original : block006_data_flat127 = (CoefficientMerge.scale (2311680 : Int) atom0538Coded) := by
  rw [block006_data_flat127_step]
def block006_data_flat128 : CoefficientMerge.Poly := [(nat_lit 1463, Int.ofNat (nat_lit 6483840))]
theorem block006_data_flat128_step : block006_data_flat128 = (CoefficientMerge.scale (6483840 : Int) atom0539Coded) := by decide +kernel
theorem block006_data_flat128_original : block006_data_flat128 = (CoefficientMerge.scale (6483840 : Int) atom0539Coded) := by
  rw [block006_data_flat128_step]
def block006_data_flat129 : CoefficientMerge.Poly := [(nat_lit 1462, Int.ofNat (nat_lit 2311680)), (nat_lit 1463, Int.ofNat (nat_lit 6483840))]
theorem block006_data_flat129_step : block006_data_flat129 = (CoefficientMerge.fastMerge block006_data_flat127 block006_data_flat128) := by decide +kernel
theorem block006_data_flat129_original : block006_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2311680 : Int) atom0538Coded) (CoefficientMerge.scale (6483840 : Int) atom0539Coded)) := by
  rw [block006_data_flat129_step, block006_data_flat127_original, block006_data_flat128_original]
def block006_data_flat130 : CoefficientMerge.Poly := [(nat_lit 1464, Int.ofNat (nat_lit 5747088))]
theorem block006_data_flat130_step : block006_data_flat130 = (CoefficientMerge.scale (5747088 : Int) atom0540Coded) := by decide +kernel
theorem block006_data_flat130_original : block006_data_flat130 = (CoefficientMerge.scale (5747088 : Int) atom0540Coded) := by
  rw [block006_data_flat130_step]
def block006_data_flat131 : CoefficientMerge.Poly := [(nat_lit 1466, Int.ofNat (nat_lit 319440))]
theorem block006_data_flat131_step : block006_data_flat131 = (CoefficientMerge.scale (319440 : Int) atom0541Coded) := by decide +kernel
theorem block006_data_flat131_original : block006_data_flat131 = (CoefficientMerge.scale (319440 : Int) atom0541Coded) := by
  rw [block006_data_flat131_step]
def block006_data_flat132 : CoefficientMerge.Poly := [(nat_lit 1467, Int.ofNat (nat_lit 15514560))]
theorem block006_data_flat132_step : block006_data_flat132 = (CoefficientMerge.scale (15514560 : Int) atom0542Coded) := by decide +kernel
theorem block006_data_flat132_original : block006_data_flat132 = (CoefficientMerge.scale (15514560 : Int) atom0542Coded) := by
  rw [block006_data_flat132_step]
def block006_data_flat133 : CoefficientMerge.Poly := [(nat_lit 1466, Int.ofNat (nat_lit 319440)), (nat_lit 1467, Int.ofNat (nat_lit 15514560))]
theorem block006_data_flat133_step : block006_data_flat133 = (CoefficientMerge.fastMerge block006_data_flat131 block006_data_flat132) := by decide +kernel
theorem block006_data_flat133_original : block006_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (319440 : Int) atom0541Coded) (CoefficientMerge.scale (15514560 : Int) atom0542Coded)) := by
  rw [block006_data_flat133_step, block006_data_flat131_original, block006_data_flat132_original]
def block006_data_flat134 : CoefficientMerge.Poly := [(nat_lit 1464, Int.ofNat (nat_lit 5747088)), (nat_lit 1466, Int.ofNat (nat_lit 319440)), (nat_lit 1467, Int.ofNat (nat_lit 15514560))]
theorem block006_data_flat134_step : block006_data_flat134 = (CoefficientMerge.fastMerge block006_data_flat130 block006_data_flat133) := by decide +kernel
theorem block006_data_flat134_original : block006_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5747088 : Int) atom0540Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (319440 : Int) atom0541Coded) (CoefficientMerge.scale (15514560 : Int) atom0542Coded))) := by
  rw [block006_data_flat134_step, block006_data_flat130_original, block006_data_flat133_original]
def block006_data_flat135 : CoefficientMerge.Poly := [(nat_lit 1462, Int.ofNat (nat_lit 2311680)), (nat_lit 1463, Int.ofNat (nat_lit 6483840)), (nat_lit 1464, Int.ofNat (nat_lit 5747088)), (nat_lit 1466, Int.ofNat (nat_lit 319440)), (nat_lit 1467, Int.ofNat (nat_lit 15514560))]
theorem block006_data_flat135_step : block006_data_flat135 = (CoefficientMerge.fastMerge block006_data_flat129 block006_data_flat134) := by decide +kernel
theorem block006_data_flat135_original : block006_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2311680 : Int) atom0538Coded) (CoefficientMerge.scale (6483840 : Int) atom0539Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5747088 : Int) atom0540Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (319440 : Int) atom0541Coded) (CoefficientMerge.scale (15514560 : Int) atom0542Coded)))) := by
  rw [block006_data_flat135_step, block006_data_flat129_original, block006_data_flat134_original]
def block006_data_flat136 : CoefficientMerge.Poly := [(nat_lit 1319, Int.ofNat (nat_lit 184546350)), (nat_lit 1333, Int.ofNat (nat_lit 24480720)), (nat_lit 1334, Int.ofNat (nat_lit 136735290)), (nat_lit 1349, Int.ofNat (nat_lit 103787730)), (nat_lit 1449, Int.ofNat (nat_lit 5095440)), (nat_lit 1462, Int.ofNat (nat_lit 2311680)), (nat_lit 1463, Int.ofNat (nat_lit 6483840)), (nat_lit 1464, Int.ofNat (nat_lit 5747088)), (nat_lit 1466, Int.ofNat (nat_lit 319440)), (nat_lit 1467, Int.ofNat (nat_lit 15514560))]
theorem block006_data_flat136_step : block006_data_flat136 = (CoefficientMerge.fastMerge block006_data_flat126 block006_data_flat135) := by decide +kernel
theorem block006_data_flat136_original : block006_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (184546350 : Int) atom0533Coded) (CoefficientMerge.scale (24480720 : Int) atom0534Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136735290 : Int) atom0535Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103787730 : Int) atom0536Coded) (CoefficientMerge.scale (5095440 : Int) atom0537Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2311680 : Int) atom0538Coded) (CoefficientMerge.scale (6483840 : Int) atom0539Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5747088 : Int) atom0540Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (319440 : Int) atom0541Coded) (CoefficientMerge.scale (15514560 : Int) atom0542Coded))))) := by
  rw [block006_data_flat136_step, block006_data_flat126_original, block006_data_flat135_original]
def block006_data_flat137 : CoefficientMerge.Poly := [(nat_lit 1468, Int.ofNat (nat_lit 31680768))]
theorem block006_data_flat137_step : block006_data_flat137 = (CoefficientMerge.scale (31680768 : Int) atom0543Coded) := by decide +kernel
theorem block006_data_flat137_original : block006_data_flat137 = (CoefficientMerge.scale (31680768 : Int) atom0543Coded) := by
  rw [block006_data_flat137_step]
def block006_data_flat138 : CoefficientMerge.Poly := [(nat_lit 1469, Int.ofNat (nat_lit 51075360))]
theorem block006_data_flat138_step : block006_data_flat138 = (CoefficientMerge.scale (51075360 : Int) atom0544Coded) := by decide +kernel
theorem block006_data_flat138_original : block006_data_flat138 = (CoefficientMerge.scale (51075360 : Int) atom0544Coded) := by
  rw [block006_data_flat138_step]
def block006_data_flat139 : CoefficientMerge.Poly := [(nat_lit 1468, Int.ofNat (nat_lit 31680768)), (nat_lit 1469, Int.ofNat (nat_lit 51075360))]
theorem block006_data_flat139_step : block006_data_flat139 = (CoefficientMerge.fastMerge block006_data_flat137 block006_data_flat138) := by decide +kernel
theorem block006_data_flat139_original : block006_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31680768 : Int) atom0543Coded) (CoefficientMerge.scale (51075360 : Int) atom0544Coded)) := by
  rw [block006_data_flat139_step, block006_data_flat137_original, block006_data_flat138_original]
def block006_data_flat140 : CoefficientMerge.Poly := [(nat_lit 1478, Int.ofNat (nat_lit 8398080))]
theorem block006_data_flat140_step : block006_data_flat140 = (CoefficientMerge.scale (8398080 : Int) atom0545Coded) := by decide +kernel
theorem block006_data_flat140_original : block006_data_flat140 = (CoefficientMerge.scale (8398080 : Int) atom0545Coded) := by
  rw [block006_data_flat140_step]
def block006_data_flat141 : CoefficientMerge.Poly := [(nat_lit 1479, Int.ofNat (nat_lit 16403040))]
theorem block006_data_flat141_step : block006_data_flat141 = (CoefficientMerge.scale (16403040 : Int) atom0546Coded) := by decide +kernel
theorem block006_data_flat141_original : block006_data_flat141 = (CoefficientMerge.scale (16403040 : Int) atom0546Coded) := by
  rw [block006_data_flat141_step]
def block006_data_flat142 : CoefficientMerge.Poly := [(nat_lit 1480, Int.ofNat (nat_lit 12962160))]
theorem block006_data_flat142_step : block006_data_flat142 = (CoefficientMerge.scale (12962160 : Int) atom0547Coded) := by decide +kernel
theorem block006_data_flat142_original : block006_data_flat142 = (CoefficientMerge.scale (12962160 : Int) atom0547Coded) := by
  rw [block006_data_flat142_step]
def block006_data_flat143 : CoefficientMerge.Poly := [(nat_lit 1479, Int.ofNat (nat_lit 16403040)), (nat_lit 1480, Int.ofNat (nat_lit 12962160))]
theorem block006_data_flat143_step : block006_data_flat143 = (CoefficientMerge.fastMerge block006_data_flat141 block006_data_flat142) := by decide +kernel
theorem block006_data_flat143_original : block006_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16403040 : Int) atom0546Coded) (CoefficientMerge.scale (12962160 : Int) atom0547Coded)) := by
  rw [block006_data_flat143_step, block006_data_flat141_original, block006_data_flat142_original]
def block006_data_flat144 : CoefficientMerge.Poly := [(nat_lit 1478, Int.ofNat (nat_lit 8398080)), (nat_lit 1479, Int.ofNat (nat_lit 16403040)), (nat_lit 1480, Int.ofNat (nat_lit 12962160))]
theorem block006_data_flat144_step : block006_data_flat144 = (CoefficientMerge.fastMerge block006_data_flat140 block006_data_flat143) := by decide +kernel
theorem block006_data_flat144_original : block006_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8398080 : Int) atom0545Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16403040 : Int) atom0546Coded) (CoefficientMerge.scale (12962160 : Int) atom0547Coded))) := by
  rw [block006_data_flat144_step, block006_data_flat140_original, block006_data_flat143_original]
def block006_data_flat145 : CoefficientMerge.Poly := [(nat_lit 1468, Int.ofNat (nat_lit 31680768)), (nat_lit 1469, Int.ofNat (nat_lit 51075360)), (nat_lit 1478, Int.ofNat (nat_lit 8398080)), (nat_lit 1479, Int.ofNat (nat_lit 16403040)), (nat_lit 1480, Int.ofNat (nat_lit 12962160))]
theorem block006_data_flat145_step : block006_data_flat145 = (CoefficientMerge.fastMerge block006_data_flat139 block006_data_flat144) := by decide +kernel
theorem block006_data_flat145_original : block006_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31680768 : Int) atom0543Coded) (CoefficientMerge.scale (51075360 : Int) atom0544Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8398080 : Int) atom0545Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16403040 : Int) atom0546Coded) (CoefficientMerge.scale (12962160 : Int) atom0547Coded)))) := by
  rw [block006_data_flat145_step, block006_data_flat139_original, block006_data_flat144_original]
def block006_data_flat146 : CoefficientMerge.Poly := [(nat_lit 1481, Int.ofNat (nat_lit 26183520))]
theorem block006_data_flat146_step : block006_data_flat146 = (CoefficientMerge.scale (26183520 : Int) atom0548Coded) := by decide +kernel
theorem block006_data_flat146_original : block006_data_flat146 = (CoefficientMerge.scale (26183520 : Int) atom0548Coded) := by
  rw [block006_data_flat146_step]
def block006_data_flat147 : CoefficientMerge.Poly := [(nat_lit 1482, Int.ofNat (nat_lit 47159280))]
theorem block006_data_flat147_step : block006_data_flat147 = (CoefficientMerge.scale (47159280 : Int) atom0549Coded) := by decide +kernel
theorem block006_data_flat147_original : block006_data_flat147 = (CoefficientMerge.scale (47159280 : Int) atom0549Coded) := by
  rw [block006_data_flat147_step]
def block006_data_flat148 : CoefficientMerge.Poly := [(nat_lit 1481, Int.ofNat (nat_lit 26183520)), (nat_lit 1482, Int.ofNat (nat_lit 47159280))]
theorem block006_data_flat148_step : block006_data_flat148 = (CoefficientMerge.fastMerge block006_data_flat146 block006_data_flat147) := by decide +kernel
theorem block006_data_flat148_original : block006_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26183520 : Int) atom0548Coded) (CoefficientMerge.scale (47159280 : Int) atom0549Coded)) := by
  rw [block006_data_flat148_step, block006_data_flat146_original, block006_data_flat147_original]
def block006_data_flat149 : CoefficientMerge.Poly := [(nat_lit 1483, Int.ofNat (nat_lit 61739280))]
theorem block006_data_flat149_step : block006_data_flat149 = (CoefficientMerge.scale (61739280 : Int) atom0550Coded) := by decide +kernel
theorem block006_data_flat149_original : block006_data_flat149 = (CoefficientMerge.scale (61739280 : Int) atom0550Coded) := by
  rw [block006_data_flat149_step]
def block006_data_flat150 : CoefficientMerge.Poly := [(nat_lit 1484, Int.ofNat (nat_lit 119553840))]
theorem block006_data_flat150_step : block006_data_flat150 = (CoefficientMerge.scale (119553840 : Int) atom0551Coded) := by decide +kernel
theorem block006_data_flat150_original : block006_data_flat150 = (CoefficientMerge.scale (119553840 : Int) atom0551Coded) := by
  rw [block006_data_flat150_step]
def block006_data_flat151 : CoefficientMerge.Poly := [(nat_lit 1494, Int.ofNat (nat_lit 29030400))]
theorem block006_data_flat151_step : block006_data_flat151 = (CoefficientMerge.scale (29030400 : Int) atom0552Coded) := by decide +kernel
theorem block006_data_flat151_original : block006_data_flat151 = (CoefficientMerge.scale (29030400 : Int) atom0552Coded) := by
  rw [block006_data_flat151_step]
def block006_data_flat152 : CoefficientMerge.Poly := [(nat_lit 1484, Int.ofNat (nat_lit 119553840)), (nat_lit 1494, Int.ofNat (nat_lit 29030400))]
theorem block006_data_flat152_step : block006_data_flat152 = (CoefficientMerge.fastMerge block006_data_flat150 block006_data_flat151) := by decide +kernel
theorem block006_data_flat152_original : block006_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (119553840 : Int) atom0551Coded) (CoefficientMerge.scale (29030400 : Int) atom0552Coded)) := by
  rw [block006_data_flat152_step, block006_data_flat150_original, block006_data_flat151_original]
def block006_data_flat153 : CoefficientMerge.Poly := [(nat_lit 1483, Int.ofNat (nat_lit 61739280)), (nat_lit 1484, Int.ofNat (nat_lit 119553840)), (nat_lit 1494, Int.ofNat (nat_lit 29030400))]
theorem block006_data_flat153_step : block006_data_flat153 = (CoefficientMerge.fastMerge block006_data_flat149 block006_data_flat152) := by decide +kernel
theorem block006_data_flat153_original : block006_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (61739280 : Int) atom0550Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119553840 : Int) atom0551Coded) (CoefficientMerge.scale (29030400 : Int) atom0552Coded))) := by
  rw [block006_data_flat153_step, block006_data_flat149_original, block006_data_flat152_original]
def block006_data_flat154 : CoefficientMerge.Poly := [(nat_lit 1481, Int.ofNat (nat_lit 26183520)), (nat_lit 1482, Int.ofNat (nat_lit 47159280)), (nat_lit 1483, Int.ofNat (nat_lit 61739280)), (nat_lit 1484, Int.ofNat (nat_lit 119553840)), (nat_lit 1494, Int.ofNat (nat_lit 29030400))]
theorem block006_data_flat154_step : block006_data_flat154 = (CoefficientMerge.fastMerge block006_data_flat148 block006_data_flat153) := by decide +kernel
theorem block006_data_flat154_original : block006_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26183520 : Int) atom0548Coded) (CoefficientMerge.scale (47159280 : Int) atom0549Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61739280 : Int) atom0550Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119553840 : Int) atom0551Coded) (CoefficientMerge.scale (29030400 : Int) atom0552Coded)))) := by
  rw [block006_data_flat154_step, block006_data_flat148_original, block006_data_flat153_original]
def block006_data_flat155 : CoefficientMerge.Poly := [(nat_lit 1468, Int.ofNat (nat_lit 31680768)), (nat_lit 1469, Int.ofNat (nat_lit 51075360)), (nat_lit 1478, Int.ofNat (nat_lit 8398080)), (nat_lit 1479, Int.ofNat (nat_lit 16403040)), (nat_lit 1480, Int.ofNat (nat_lit 12962160)), (nat_lit 1481, Int.ofNat (nat_lit 26183520)), (nat_lit 1482, Int.ofNat (nat_lit 47159280)), (nat_lit 1483, Int.ofNat (nat_lit 61739280)), (nat_lit 1484, Int.ofNat (nat_lit 119553840)), (nat_lit 1494, Int.ofNat (nat_lit 29030400))]
theorem block006_data_flat155_step : block006_data_flat155 = (CoefficientMerge.fastMerge block006_data_flat145 block006_data_flat154) := by decide +kernel
theorem block006_data_flat155_original : block006_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31680768 : Int) atom0543Coded) (CoefficientMerge.scale (51075360 : Int) atom0544Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8398080 : Int) atom0545Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16403040 : Int) atom0546Coded) (CoefficientMerge.scale (12962160 : Int) atom0547Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26183520 : Int) atom0548Coded) (CoefficientMerge.scale (47159280 : Int) atom0549Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61739280 : Int) atom0550Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119553840 : Int) atom0551Coded) (CoefficientMerge.scale (29030400 : Int) atom0552Coded))))) := by
  rw [block006_data_flat155_step, block006_data_flat145_original, block006_data_flat154_original]
def block006_data_flat156 : CoefficientMerge.Poly := [(nat_lit 1319, Int.ofNat (nat_lit 184546350)), (nat_lit 1333, Int.ofNat (nat_lit 24480720)), (nat_lit 1334, Int.ofNat (nat_lit 136735290)), (nat_lit 1349, Int.ofNat (nat_lit 103787730)), (nat_lit 1449, Int.ofNat (nat_lit 5095440)), (nat_lit 1462, Int.ofNat (nat_lit 2311680)), (nat_lit 1463, Int.ofNat (nat_lit 6483840)), (nat_lit 1464, Int.ofNat (nat_lit 5747088)), (nat_lit 1466, Int.ofNat (nat_lit 319440)), (nat_lit 1467, Int.ofNat (nat_lit 15514560)), (nat_lit 1468, Int.ofNat (nat_lit 31680768)), (nat_lit 1469, Int.ofNat (nat_lit 51075360)), (nat_lit 1478, Int.ofNat (nat_lit 8398080)), (nat_lit 1479, Int.ofNat (nat_lit 16403040)), (nat_lit 1480, Int.ofNat (nat_lit 12962160)), (nat_lit 1481, Int.ofNat (nat_lit 26183520)), (nat_lit 1482, Int.ofNat (nat_lit 47159280)), (nat_lit 1483, Int.ofNat (nat_lit 61739280)), (nat_lit 1484, Int.ofNat (nat_lit 119553840)), (nat_lit 1494, Int.ofNat (nat_lit 29030400))]
theorem block006_data_flat156_step : block006_data_flat156 = (CoefficientMerge.fastMerge block006_data_flat136 block006_data_flat155) := by decide +kernel
theorem block006_data_flat156_original : block006_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (184546350 : Int) atom0533Coded) (CoefficientMerge.scale (24480720 : Int) atom0534Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136735290 : Int) atom0535Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103787730 : Int) atom0536Coded) (CoefficientMerge.scale (5095440 : Int) atom0537Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2311680 : Int) atom0538Coded) (CoefficientMerge.scale (6483840 : Int) atom0539Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5747088 : Int) atom0540Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (319440 : Int) atom0541Coded) (CoefficientMerge.scale (15514560 : Int) atom0542Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31680768 : Int) atom0543Coded) (CoefficientMerge.scale (51075360 : Int) atom0544Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8398080 : Int) atom0545Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16403040 : Int) atom0546Coded) (CoefficientMerge.scale (12962160 : Int) atom0547Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26183520 : Int) atom0548Coded) (CoefficientMerge.scale (47159280 : Int) atom0549Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61739280 : Int) atom0550Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119553840 : Int) atom0551Coded) (CoefficientMerge.scale (29030400 : Int) atom0552Coded)))))) := by
  rw [block006_data_flat156_step, block006_data_flat136_original, block006_data_flat155_original]
def block006_data_flat157 : CoefficientMerge.Poly := [(nat_lit 1257, Int.ofNat (nat_lit 73305360)), (nat_lit 1258, Int.ofNat (nat_lit 86870160)), (nat_lit 1259, Int.ofNat (nat_lit 142287840)), (nat_lit 1269, Int.ofNat (nat_lit 44323200)), (nat_lit 1270, Int.ofNat (nat_lit 82846440)), (nat_lit 1271, Int.ofNat (nat_lit 142823520)), (nat_lit 1272, Int.ofNat (nat_lit 167162040)), (nat_lit 1273, Int.ofNat (nat_lit 115337880)), (nat_lit 1274, Int.ofNat (nat_lit 199593720)), (nat_lit 1285, Int.ofNat (nat_lit 36733824)), (nat_lit 1286, Int.ofNat (nat_lit 114498720)), (nat_lit 1287, Int.ofNat (nat_lit 154214820)), (nat_lit 1288, Int.ofNat (nat_lit 117768240)), (nat_lit 1289, Int.ofNat (nat_lit 164733750)), (nat_lit 1301, Int.ofNat (nat_lit 90088200)), (nat_lit 1302, Int.ofNat (nat_lit 167922000)), (nat_lit 1303, Int.ofNat (nat_lit 133936920)), (nat_lit 1304, Int.ofNat (nat_lit 201572280)), (nat_lit 1317, Int.ofNat (nat_lit 62318700)), (nat_lit 1318, Int.ofNat (nat_lit 105936300)), (nat_lit 1319, Int.ofNat (nat_lit 184546350)), (nat_lit 1333, Int.ofNat (nat_lit 24480720)), (nat_lit 1334, Int.ofNat (nat_lit 136735290)), (nat_lit 1349, Int.ofNat (nat_lit 103787730)), (nat_lit 1449, Int.ofNat (nat_lit 5095440)), (nat_lit 1462, Int.ofNat (nat_lit 2311680)), (nat_lit 1463, Int.ofNat (nat_lit 6483840)), (nat_lit 1464, Int.ofNat (nat_lit 5747088)), (nat_lit 1466, Int.ofNat (nat_lit 319440)), (nat_lit 1467, Int.ofNat (nat_lit 15514560)), (nat_lit 1468, Int.ofNat (nat_lit 31680768)), (nat_lit 1469, Int.ofNat (nat_lit 51075360)), (nat_lit 1478, Int.ofNat (nat_lit 8398080)), (nat_lit 1479, Int.ofNat (nat_lit 16403040)), (nat_lit 1480, Int.ofNat (nat_lit 12962160)), (nat_lit 1481, Int.ofNat (nat_lit 26183520)), (nat_lit 1482, Int.ofNat (nat_lit 47159280)), (nat_lit 1483, Int.ofNat (nat_lit 61739280)), (nat_lit 1484, Int.ofNat (nat_lit 119553840)), (nat_lit 1494, Int.ofNat (nat_lit 29030400))]
theorem block006_data_flat157_step : block006_data_flat157 = (CoefficientMerge.fastMerge block006_data_flat117 block006_data_flat156) := by decide +kernel
theorem block006_data_flat157_original : block006_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (73305360 : Int) atom0513Coded) (CoefficientMerge.scale (86870160 : Int) atom0514Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (142287840 : Int) atom0515Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44323200 : Int) atom0516Coded) (CoefficientMerge.scale (82846440 : Int) atom0517Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142823520 : Int) atom0518Coded) (CoefficientMerge.scale (167162040 : Int) atom0519Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115337880 : Int) atom0520Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199593720 : Int) atom0521Coded) (CoefficientMerge.scale (36733824 : Int) atom0522Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (114498720 : Int) atom0523Coded) (CoefficientMerge.scale (154214820 : Int) atom0524Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117768240 : Int) atom0525Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164733750 : Int) atom0526Coded) (CoefficientMerge.scale (90088200 : Int) atom0527Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (167922000 : Int) atom0528Coded) (CoefficientMerge.scale (133936920 : Int) atom0529Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (201572280 : Int) atom0530Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62318700 : Int) atom0531Coded) (CoefficientMerge.scale (105936300 : Int) atom0532Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (184546350 : Int) atom0533Coded) (CoefficientMerge.scale (24480720 : Int) atom0534Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136735290 : Int) atom0535Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103787730 : Int) atom0536Coded) (CoefficientMerge.scale (5095440 : Int) atom0537Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2311680 : Int) atom0538Coded) (CoefficientMerge.scale (6483840 : Int) atom0539Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5747088 : Int) atom0540Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (319440 : Int) atom0541Coded) (CoefficientMerge.scale (15514560 : Int) atom0542Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31680768 : Int) atom0543Coded) (CoefficientMerge.scale (51075360 : Int) atom0544Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8398080 : Int) atom0545Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16403040 : Int) atom0546Coded) (CoefficientMerge.scale (12962160 : Int) atom0547Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26183520 : Int) atom0548Coded) (CoefficientMerge.scale (47159280 : Int) atom0549Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61739280 : Int) atom0550Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119553840 : Int) atom0551Coded) (CoefficientMerge.scale (29030400 : Int) atom0552Coded))))))) := by
  rw [block006_data_flat157_step, block006_data_flat117_original, block006_data_flat156_original]
def block006_data_flat158 : CoefficientMerge.Poly := [(nat_lit 1046, Int.ofNat (nat_lit 159550560)), (nat_lit 1047, Int.ofNat (nat_lit 175445640)), (nat_lit 1048, Int.ofNat (nat_lit 116951400)), (nat_lit 1049, Int.ofNat (nat_lit 194537160)), (nat_lit 1060, Int.ofNat (nat_lit 46998144)), (nat_lit 1061, Int.ofNat (nat_lit 129823920)), (nat_lit 1062, Int.ofNat (nat_lit 162877500)), (nat_lit 1063, Int.ofNat (nat_lit 119768400)), (nat_lit 1064, Int.ofNat (nat_lit 159341850)), (nat_lit 1076, Int.ofNat (nat_lit 94131720)), (nat_lit 1077, Int.ofNat (nat_lit 168209280)), (nat_lit 1078, Int.ofNat (nat_lit 124651080)), (nat_lit 1079, Int.ofNat (nat_lit 182713320)), (nat_lit 1092, Int.ofNat (nat_lit 61220340)), (nat_lit 1093, Int.ofNat (nat_lit 93601620)), (nat_lit 1094, Int.ofNat (nat_lit 161695170)), (nat_lit 1108, Int.ofNat (nat_lit 15015600)), (nat_lit 1109, Int.ofNat (nat_lit 105901830)), (nat_lit 1124, Int.ofNat (nat_lit 84255390)), (nat_lit 1205, Int.ofNat (nat_lit 633600)), (nat_lit 1209, Int.ofNat (nat_lit 11719440)), (nat_lit 1221, Int.ofNat (nat_lit 1664640)), (nat_lit 1222, Int.ofNat (nat_lit 5230080)), (nat_lit 1223, Int.ofNat (nat_lit 7130880)), (nat_lit 1224, Int.ofNat (nat_lit 17790048)), (nat_lit 1227, Int.ofNat (nat_lit 15029280)), (nat_lit 1228, Int.ofNat (nat_lit 31033728)), (nat_lit 1229, Int.ofNat (nat_lit 50347440)), (nat_lit 1237, Int.ofNat (nat_lit 7777920)), (nat_lit 1238, Int.ofNat (nat_lit 18124800)), (nat_lit 1239, Int.ofNat (nat_lit 25904640)), (nat_lit 1240, Int.ofNat (nat_lit 16650960)), (nat_lit 1241, Int.ofNat (nat_lit 23597280)), (nat_lit 1242, Int.ofNat (nat_lit 40870320)), (nat_lit 1243, Int.ofNat (nat_lit 62623920)), (nat_lit 1244, Int.ofNat (nat_lit 87616080)), (nat_lit 1253, Int.ofNat (nat_lit 16473600)), (nat_lit 1254, Int.ofNat (nat_lit 43397280)), (nat_lit 1255, Int.ofNat (nat_lit 36727920)), (nat_lit 1256, Int.ofNat (nat_lit 52757280)), (nat_lit 1257, Int.ofNat (nat_lit 73305360)), (nat_lit 1258, Int.ofNat (nat_lit 86870160)), (nat_lit 1259, Int.ofNat (nat_lit 142287840)), (nat_lit 1269, Int.ofNat (nat_lit 44323200)), (nat_lit 1270, Int.ofNat (nat_lit 82846440)), (nat_lit 1271, Int.ofNat (nat_lit 142823520)), (nat_lit 1272, Int.ofNat (nat_lit 167162040)), (nat_lit 1273, Int.ofNat (nat_lit 115337880)), (nat_lit 1274, Int.ofNat (nat_lit 199593720)), (nat_lit 1285, Int.ofNat (nat_lit 36733824)), (nat_lit 1286, Int.ofNat (nat_lit 114498720)), (nat_lit 1287, Int.ofNat (nat_lit 154214820)), (nat_lit 1288, Int.ofNat (nat_lit 117768240)), (nat_lit 1289, Int.ofNat (nat_lit 164733750)), (nat_lit 1301, Int.ofNat (nat_lit 90088200)), (nat_lit 1302, Int.ofNat (nat_lit 167922000)), (nat_lit 1303, Int.ofNat (nat_lit 133936920)), (nat_lit 1304, Int.ofNat (nat_lit 201572280)), (nat_lit 1317, Int.ofNat (nat_lit 62318700)), (nat_lit 1318, Int.ofNat (nat_lit 105936300)), (nat_lit 1319, Int.ofNat (nat_lit 184546350)), (nat_lit 1333, Int.ofNat (nat_lit 24480720)), (nat_lit 1334, Int.ofNat (nat_lit 136735290)), (nat_lit 1349, Int.ofNat (nat_lit 103787730)), (nat_lit 1449, Int.ofNat (nat_lit 5095440)), (nat_lit 1462, Int.ofNat (nat_lit 2311680)), (nat_lit 1463, Int.ofNat (nat_lit 6483840)), (nat_lit 1464, Int.ofNat (nat_lit 5747088)), (nat_lit 1466, Int.ofNat (nat_lit 319440)), (nat_lit 1467, Int.ofNat (nat_lit 15514560)), (nat_lit 1468, Int.ofNat (nat_lit 31680768)), (nat_lit 1469, Int.ofNat (nat_lit 51075360)), (nat_lit 1478, Int.ofNat (nat_lit 8398080)), (nat_lit 1479, Int.ofNat (nat_lit 16403040)), (nat_lit 1480, Int.ofNat (nat_lit 12962160)), (nat_lit 1481, Int.ofNat (nat_lit 26183520)), (nat_lit 1482, Int.ofNat (nat_lit 47159280)), (nat_lit 1483, Int.ofNat (nat_lit 61739280)), (nat_lit 1484, Int.ofNat (nat_lit 119553840)), (nat_lit 1494, Int.ofNat (nat_lit 29030400))]
theorem block006_data_flat158_step : block006_data_flat158 = (CoefficientMerge.fastMerge block006_data_flat078 block006_data_flat157) := by decide +kernel
theorem block006_data_flat158_original : block006_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (159550560 : Int) atom0473Coded) (CoefficientMerge.scale (175445640 : Int) atom0474Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (116951400 : Int) atom0475Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (194537160 : Int) atom0476Coded) (CoefficientMerge.scale (46998144 : Int) atom0477Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129823920 : Int) atom0478Coded) (CoefficientMerge.scale (162877500 : Int) atom0479Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119768400 : Int) atom0480Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (159341850 : Int) atom0481Coded) (CoefficientMerge.scale (94131720 : Int) atom0482Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (168209280 : Int) atom0483Coded) (CoefficientMerge.scale (124651080 : Int) atom0484Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182713320 : Int) atom0485Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61220340 : Int) atom0486Coded) (CoefficientMerge.scale (93601620 : Int) atom0487Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (161695170 : Int) atom0488Coded) (CoefficientMerge.scale (15015600 : Int) atom0489Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105901830 : Int) atom0490Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84255390 : Int) atom0491Coded) (CoefficientMerge.scale (633600 : Int) atom0492Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11719440 : Int) atom0493Coded) (CoefficientMerge.scale (1664640 : Int) atom0494Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5230080 : Int) atom0495Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7130880 : Int) atom0496Coded) (CoefficientMerge.scale (17790048 : Int) atom0497Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15029280 : Int) atom0498Coded) (CoefficientMerge.scale (31033728 : Int) atom0499Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50347440 : Int) atom0500Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777920 : Int) atom0501Coded) (CoefficientMerge.scale (18124800 : Int) atom0502Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25904640 : Int) atom0503Coded) (CoefficientMerge.scale (16650960 : Int) atom0504Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23597280 : Int) atom0505Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40870320 : Int) atom0506Coded) (CoefficientMerge.scale (62623920 : Int) atom0507Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87616080 : Int) atom0508Coded) (CoefficientMerge.scale (16473600 : Int) atom0509Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43397280 : Int) atom0510Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36727920 : Int) atom0511Coded) (CoefficientMerge.scale (52757280 : Int) atom0512Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (73305360 : Int) atom0513Coded) (CoefficientMerge.scale (86870160 : Int) atom0514Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (142287840 : Int) atom0515Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44323200 : Int) atom0516Coded) (CoefficientMerge.scale (82846440 : Int) atom0517Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142823520 : Int) atom0518Coded) (CoefficientMerge.scale (167162040 : Int) atom0519Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115337880 : Int) atom0520Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199593720 : Int) atom0521Coded) (CoefficientMerge.scale (36733824 : Int) atom0522Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (114498720 : Int) atom0523Coded) (CoefficientMerge.scale (154214820 : Int) atom0524Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117768240 : Int) atom0525Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164733750 : Int) atom0526Coded) (CoefficientMerge.scale (90088200 : Int) atom0527Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (167922000 : Int) atom0528Coded) (CoefficientMerge.scale (133936920 : Int) atom0529Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (201572280 : Int) atom0530Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62318700 : Int) atom0531Coded) (CoefficientMerge.scale (105936300 : Int) atom0532Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (184546350 : Int) atom0533Coded) (CoefficientMerge.scale (24480720 : Int) atom0534Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136735290 : Int) atom0535Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103787730 : Int) atom0536Coded) (CoefficientMerge.scale (5095440 : Int) atom0537Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2311680 : Int) atom0538Coded) (CoefficientMerge.scale (6483840 : Int) atom0539Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5747088 : Int) atom0540Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (319440 : Int) atom0541Coded) (CoefficientMerge.scale (15514560 : Int) atom0542Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31680768 : Int) atom0543Coded) (CoefficientMerge.scale (51075360 : Int) atom0544Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8398080 : Int) atom0545Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16403040 : Int) atom0546Coded) (CoefficientMerge.scale (12962160 : Int) atom0547Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26183520 : Int) atom0548Coded) (CoefficientMerge.scale (47159280 : Int) atom0549Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61739280 : Int) atom0550Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119553840 : Int) atom0551Coded) (CoefficientMerge.scale (29030400 : Int) atom0552Coded)))))))) := by
  rw [block006_data_flat158_step, block006_data_flat078_original, block006_data_flat157_original]
def block006_data_flat159 : CoefficientMerge.Poly := [(nat_lit 1046, Int.ofNat (nat_lit 159550560)), (nat_lit 1047, Int.ofNat (nat_lit 175445640)), (nat_lit 1048, Int.ofNat (nat_lit 116951400)), (nat_lit 1049, Int.ofNat (nat_lit 194537160)), (nat_lit 1060, Int.ofNat (nat_lit 46998144)), (nat_lit 1061, Int.ofNat (nat_lit 129823920)), (nat_lit 1062, Int.ofNat (nat_lit 162877500)), (nat_lit 1063, Int.ofNat (nat_lit 119768400)), (nat_lit 1064, Int.ofNat (nat_lit 159341850)), (nat_lit 1076, Int.ofNat (nat_lit 94131720)), (nat_lit 1077, Int.ofNat (nat_lit 168209280)), (nat_lit 1078, Int.ofNat (nat_lit 124651080)), (nat_lit 1079, Int.ofNat (nat_lit 182713320)), (nat_lit 1092, Int.ofNat (nat_lit 61220340)), (nat_lit 1093, Int.ofNat (nat_lit 93601620)), (nat_lit 1094, Int.ofNat (nat_lit 161695170)), (nat_lit 1108, Int.ofNat (nat_lit 15015600)), (nat_lit 1109, Int.ofNat (nat_lit 105901830)), (nat_lit 1124, Int.ofNat (nat_lit 84255390)), (nat_lit 1205, Int.ofNat (nat_lit 633600)), (nat_lit 1209, Int.ofNat (nat_lit 11719440)), (nat_lit 1221, Int.ofNat (nat_lit 1664640)), (nat_lit 1222, Int.ofNat (nat_lit 5230080)), (nat_lit 1223, Int.ofNat (nat_lit 7130880)), (nat_lit 1224, Int.ofNat (nat_lit 17790048)), (nat_lit 1227, Int.ofNat (nat_lit 15029280)), (nat_lit 1228, Int.ofNat (nat_lit 31033728)), (nat_lit 1229, Int.ofNat (nat_lit 50347440)), (nat_lit 1237, Int.ofNat (nat_lit 7777920)), (nat_lit 1238, Int.ofNat (nat_lit 18124800)), (nat_lit 1239, Int.ofNat (nat_lit 25904640)), (nat_lit 1240, Int.ofNat (nat_lit 16650960)), (nat_lit 1241, Int.ofNat (nat_lit 23597280)), (nat_lit 1242, Int.ofNat (nat_lit 40870320)), (nat_lit 1243, Int.ofNat (nat_lit 62623920)), (nat_lit 1244, Int.ofNat (nat_lit 87616080)), (nat_lit 1253, Int.ofNat (nat_lit 16473600)), (nat_lit 1254, Int.ofNat (nat_lit 43397280)), (nat_lit 1255, Int.ofNat (nat_lit 36727920)), (nat_lit 1256, Int.ofNat (nat_lit 52757280)), (nat_lit 1257, Int.ofNat (nat_lit 73305360)), (nat_lit 1258, Int.ofNat (nat_lit 86870160)), (nat_lit 1259, Int.ofNat (nat_lit 142287840)), (nat_lit 1269, Int.ofNat (nat_lit 44323200)), (nat_lit 1270, Int.ofNat (nat_lit 82846440)), (nat_lit 1271, Int.ofNat (nat_lit 142823520)), (nat_lit 1272, Int.ofNat (nat_lit 167162040)), (nat_lit 1273, Int.ofNat (nat_lit 115337880)), (nat_lit 1274, Int.ofNat (nat_lit 199593720)), (nat_lit 1285, Int.ofNat (nat_lit 36733824)), (nat_lit 1286, Int.ofNat (nat_lit 114498720)), (nat_lit 1287, Int.ofNat (nat_lit 154214820)), (nat_lit 1288, Int.ofNat (nat_lit 117768240)), (nat_lit 1289, Int.ofNat (nat_lit 164733750)), (nat_lit 1301, Int.ofNat (nat_lit 90088200)), (nat_lit 1302, Int.ofNat (nat_lit 167922000)), (nat_lit 1303, Int.ofNat (nat_lit 133936920)), (nat_lit 1304, Int.ofNat (nat_lit 201572280)), (nat_lit 1317, Int.ofNat (nat_lit 62318700)), (nat_lit 1318, Int.ofNat (nat_lit 105936300)), (nat_lit 1319, Int.ofNat (nat_lit 184546350)), (nat_lit 1333, Int.ofNat (nat_lit 24480720)), (nat_lit 1334, Int.ofNat (nat_lit 136735290)), (nat_lit 1349, Int.ofNat (nat_lit 103787730)), (nat_lit 1449, Int.ofNat (nat_lit 5095440)), (nat_lit 1462, Int.ofNat (nat_lit 2311680)), (nat_lit 1463, Int.ofNat (nat_lit 6483840)), (nat_lit 1464, Int.ofNat (nat_lit 5747088)), (nat_lit 1466, Int.ofNat (nat_lit 319440)), (nat_lit 1467, Int.ofNat (nat_lit 15514560)), (nat_lit 1468, Int.ofNat (nat_lit 31680768)), (nat_lit 1469, Int.ofNat (nat_lit 51075360)), (nat_lit 1478, Int.ofNat (nat_lit 8398080)), (nat_lit 1479, Int.ofNat (nat_lit 16403040)), (nat_lit 1480, Int.ofNat (nat_lit 12962160)), (nat_lit 1481, Int.ofNat (nat_lit 26183520)), (nat_lit 1482, Int.ofNat (nat_lit 47159280)), (nat_lit 1483, Int.ofNat (nat_lit 61739280)), (nat_lit 1484, Int.ofNat (nat_lit 119553840)), (nat_lit 1494, Int.ofNat (nat_lit 29030400))]
theorem block006_data_flat159_step : block006_data_flat159 = (CoefficientMerge.trim block006_data_flat158) := by decide +kernel
theorem block006_data_flat159_original : block006_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (159550560 : Int) atom0473Coded) (CoefficientMerge.scale (175445640 : Int) atom0474Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (116951400 : Int) atom0475Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (194537160 : Int) atom0476Coded) (CoefficientMerge.scale (46998144 : Int) atom0477Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129823920 : Int) atom0478Coded) (CoefficientMerge.scale (162877500 : Int) atom0479Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119768400 : Int) atom0480Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (159341850 : Int) atom0481Coded) (CoefficientMerge.scale (94131720 : Int) atom0482Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (168209280 : Int) atom0483Coded) (CoefficientMerge.scale (124651080 : Int) atom0484Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182713320 : Int) atom0485Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61220340 : Int) atom0486Coded) (CoefficientMerge.scale (93601620 : Int) atom0487Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (161695170 : Int) atom0488Coded) (CoefficientMerge.scale (15015600 : Int) atom0489Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105901830 : Int) atom0490Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84255390 : Int) atom0491Coded) (CoefficientMerge.scale (633600 : Int) atom0492Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11719440 : Int) atom0493Coded) (CoefficientMerge.scale (1664640 : Int) atom0494Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5230080 : Int) atom0495Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7130880 : Int) atom0496Coded) (CoefficientMerge.scale (17790048 : Int) atom0497Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15029280 : Int) atom0498Coded) (CoefficientMerge.scale (31033728 : Int) atom0499Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50347440 : Int) atom0500Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777920 : Int) atom0501Coded) (CoefficientMerge.scale (18124800 : Int) atom0502Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25904640 : Int) atom0503Coded) (CoefficientMerge.scale (16650960 : Int) atom0504Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23597280 : Int) atom0505Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40870320 : Int) atom0506Coded) (CoefficientMerge.scale (62623920 : Int) atom0507Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87616080 : Int) atom0508Coded) (CoefficientMerge.scale (16473600 : Int) atom0509Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43397280 : Int) atom0510Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36727920 : Int) atom0511Coded) (CoefficientMerge.scale (52757280 : Int) atom0512Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (73305360 : Int) atom0513Coded) (CoefficientMerge.scale (86870160 : Int) atom0514Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (142287840 : Int) atom0515Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44323200 : Int) atom0516Coded) (CoefficientMerge.scale (82846440 : Int) atom0517Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142823520 : Int) atom0518Coded) (CoefficientMerge.scale (167162040 : Int) atom0519Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115337880 : Int) atom0520Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199593720 : Int) atom0521Coded) (CoefficientMerge.scale (36733824 : Int) atom0522Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (114498720 : Int) atom0523Coded) (CoefficientMerge.scale (154214820 : Int) atom0524Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117768240 : Int) atom0525Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164733750 : Int) atom0526Coded) (CoefficientMerge.scale (90088200 : Int) atom0527Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (167922000 : Int) atom0528Coded) (CoefficientMerge.scale (133936920 : Int) atom0529Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (201572280 : Int) atom0530Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62318700 : Int) atom0531Coded) (CoefficientMerge.scale (105936300 : Int) atom0532Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (184546350 : Int) atom0533Coded) (CoefficientMerge.scale (24480720 : Int) atom0534Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136735290 : Int) atom0535Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103787730 : Int) atom0536Coded) (CoefficientMerge.scale (5095440 : Int) atom0537Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2311680 : Int) atom0538Coded) (CoefficientMerge.scale (6483840 : Int) atom0539Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5747088 : Int) atom0540Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (319440 : Int) atom0541Coded) (CoefficientMerge.scale (15514560 : Int) atom0542Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31680768 : Int) atom0543Coded) (CoefficientMerge.scale (51075360 : Int) atom0544Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8398080 : Int) atom0545Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16403040 : Int) atom0546Coded) (CoefficientMerge.scale (12962160 : Int) atom0547Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26183520 : Int) atom0548Coded) (CoefficientMerge.scale (47159280 : Int) atom0549Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61739280 : Int) atom0550Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119553840 : Int) atom0551Coded) (CoefficientMerge.scale (29030400 : Int) atom0552Coded))))))))) := by
  rw [block006_data_flat159_step, block006_data_flat158_original]
theorem block006_data : block006 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (159550560 : Int) atom0473Coded) (CoefficientMerge.scale (175445640 : Int) atom0474Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (116951400 : Int) atom0475Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (194537160 : Int) atom0476Coded) (CoefficientMerge.scale (46998144 : Int) atom0477Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129823920 : Int) atom0478Coded) (CoefficientMerge.scale (162877500 : Int) atom0479Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119768400 : Int) atom0480Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (159341850 : Int) atom0481Coded) (CoefficientMerge.scale (94131720 : Int) atom0482Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (168209280 : Int) atom0483Coded) (CoefficientMerge.scale (124651080 : Int) atom0484Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182713320 : Int) atom0485Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61220340 : Int) atom0486Coded) (CoefficientMerge.scale (93601620 : Int) atom0487Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (161695170 : Int) atom0488Coded) (CoefficientMerge.scale (15015600 : Int) atom0489Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105901830 : Int) atom0490Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84255390 : Int) atom0491Coded) (CoefficientMerge.scale (633600 : Int) atom0492Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11719440 : Int) atom0493Coded) (CoefficientMerge.scale (1664640 : Int) atom0494Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5230080 : Int) atom0495Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7130880 : Int) atom0496Coded) (CoefficientMerge.scale (17790048 : Int) atom0497Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15029280 : Int) atom0498Coded) (CoefficientMerge.scale (31033728 : Int) atom0499Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50347440 : Int) atom0500Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7777920 : Int) atom0501Coded) (CoefficientMerge.scale (18124800 : Int) atom0502Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25904640 : Int) atom0503Coded) (CoefficientMerge.scale (16650960 : Int) atom0504Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23597280 : Int) atom0505Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40870320 : Int) atom0506Coded) (CoefficientMerge.scale (62623920 : Int) atom0507Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87616080 : Int) atom0508Coded) (CoefficientMerge.scale (16473600 : Int) atom0509Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43397280 : Int) atom0510Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36727920 : Int) atom0511Coded) (CoefficientMerge.scale (52757280 : Int) atom0512Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (73305360 : Int) atom0513Coded) (CoefficientMerge.scale (86870160 : Int) atom0514Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (142287840 : Int) atom0515Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44323200 : Int) atom0516Coded) (CoefficientMerge.scale (82846440 : Int) atom0517Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142823520 : Int) atom0518Coded) (CoefficientMerge.scale (167162040 : Int) atom0519Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (115337880 : Int) atom0520Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (199593720 : Int) atom0521Coded) (CoefficientMerge.scale (36733824 : Int) atom0522Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (114498720 : Int) atom0523Coded) (CoefficientMerge.scale (154214820 : Int) atom0524Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (117768240 : Int) atom0525Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164733750 : Int) atom0526Coded) (CoefficientMerge.scale (90088200 : Int) atom0527Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (167922000 : Int) atom0528Coded) (CoefficientMerge.scale (133936920 : Int) atom0529Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (201572280 : Int) atom0530Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (62318700 : Int) atom0531Coded) (CoefficientMerge.scale (105936300 : Int) atom0532Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (184546350 : Int) atom0533Coded) (CoefficientMerge.scale (24480720 : Int) atom0534Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136735290 : Int) atom0535Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103787730 : Int) atom0536Coded) (CoefficientMerge.scale (5095440 : Int) atom0537Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2311680 : Int) atom0538Coded) (CoefficientMerge.scale (6483840 : Int) atom0539Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5747088 : Int) atom0540Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (319440 : Int) atom0541Coded) (CoefficientMerge.scale (15514560 : Int) atom0542Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31680768 : Int) atom0543Coded) (CoefficientMerge.scale (51075360 : Int) atom0544Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8398080 : Int) atom0545Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16403040 : Int) atom0546Coded) (CoefficientMerge.scale (12962160 : Int) atom0547Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26183520 : Int) atom0548Coded) (CoefficientMerge.scale (47159280 : Int) atom0549Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61739280 : Int) atom0550Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (119553840 : Int) atom0551Coded) (CoefficientMerge.scale (29030400 : Int) atom0552Coded)))))))) := by
  have h : block006 = block006_data_flat159 := by decide +kernel
  exact h.trans block006_data_flat159_original
theorem block006_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) block006 := by
  rw [block006_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0473Coded_nonneg g hg hA hB) (atom0474Coded_nonneg g hg hA hB)) (add_nonneg (atom0475Coded_nonneg g hg hA hB) (add_nonneg (atom0476Coded_nonneg g hg hA hB) (atom0477Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0478Coded_nonneg g hg hA hB) (atom0479Coded_nonneg g hg hA hB)) (add_nonneg (atom0480Coded_nonneg g hg hA hB) (add_nonneg (atom0481Coded_nonneg g hg hA hB) (atom0482Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0483Coded_nonneg g hg hA hB) (atom0484Coded_nonneg g hg hA hB)) (add_nonneg (atom0485Coded_nonneg g hg hA hB) (add_nonneg (atom0486Coded_nonneg g hg hA hB) (atom0487Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0488Coded_nonneg g hg hA hB) (atom0489Coded_nonneg g hg hA hB)) (add_nonneg (atom0490Coded_nonneg g hg hA hB) (add_nonneg (atom0491Coded_nonneg g hg hA hB) (atom0492Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0493Coded_nonneg g hg hA hB) (atom0494Coded_nonneg g hg hA hB)) (add_nonneg (atom0495Coded_nonneg g hg hA hB) (add_nonneg (atom0496Coded_nonneg g hg hA hB) (atom0497Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0498Coded_nonneg g hg hA hB) (atom0499Coded_nonneg g hg hA hB)) (add_nonneg (atom0500Coded_nonneg g hg hA hB) (add_nonneg (atom0501Coded_nonneg g hg hA hB) (atom0502Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0503Coded_nonneg g hg hA hB) (atom0504Coded_nonneg g hg hA hB)) (add_nonneg (atom0505Coded_nonneg g hg hA hB) (add_nonneg (atom0506Coded_nonneg g hg hA hB) (atom0507Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0508Coded_nonneg g hg hA hB) (atom0509Coded_nonneg g hg hA hB)) (add_nonneg (atom0510Coded_nonneg g hg hA hB) (add_nonneg (atom0511Coded_nonneg g hg hA hB) (atom0512Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0513Coded_nonneg g hg hA hB) (atom0514Coded_nonneg g hg hA hB)) (add_nonneg (atom0515Coded_nonneg g hg hA hB) (add_nonneg (atom0516Coded_nonneg g hg hA hB) (atom0517Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0518Coded_nonneg g hg hA hB) (atom0519Coded_nonneg g hg hA hB)) (add_nonneg (atom0520Coded_nonneg g hg hA hB) (add_nonneg (atom0521Coded_nonneg g hg hA hB) (atom0522Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0523Coded_nonneg g hg hA hB) (atom0524Coded_nonneg g hg hA hB)) (add_nonneg (atom0525Coded_nonneg g hg hA hB) (add_nonneg (atom0526Coded_nonneg g hg hA hB) (atom0527Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0528Coded_nonneg g hg hA hB) (atom0529Coded_nonneg g hg hA hB)) (add_nonneg (atom0530Coded_nonneg g hg hA hB) (add_nonneg (atom0531Coded_nonneg g hg hA hB) (atom0532Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0533Coded_nonneg g hg hA hB) (atom0534Coded_nonneg g hg hA hB)) (add_nonneg (atom0535Coded_nonneg g hg hA hB) (add_nonneg (atom0536Coded_nonneg g hg hA hB) (atom0537Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0538Coded_nonneg g hg hA hB) (atom0539Coded_nonneg g hg hA hB)) (add_nonneg (atom0540Coded_nonneg g hg hA hB) (add_nonneg (atom0541Coded_nonneg g hg hA hB) (atom0542Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0543Coded_nonneg g hg hA hB) (atom0544Coded_nonneg g hg hA hB)) (add_nonneg (atom0545Coded_nonneg g hg hA hB) (add_nonneg (atom0546Coded_nonneg g hg hA hB) (atom0547Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0548Coded_nonneg g hg hA hB) (atom0549Coded_nonneg g hg hA hB)) (add_nonneg (atom0550Coded_nonneg g hg hA hB) (add_nonneg (atom0551Coded_nonneg g hg hA hB) (atom0552Coded_nonneg g hg hA hB))))))))

end APPT.Finite15
