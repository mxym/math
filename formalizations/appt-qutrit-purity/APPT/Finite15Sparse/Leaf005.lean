-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def atom0393 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0393 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0393 = ((g 3) * (g 6) * (g 8)) := by
  norm_num [atom0393, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0393_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35700480 : Int) atom0393) := by
  rw [SparsePolynomial.eval_scale, eval_atom0393]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0393Coded : CoefficientMerge.Poly := [(nat_lit 773, Int.ofNat (nat_lit 1))]
theorem atom0393Coded_decode : atom0393 = SparsePolynomial.decodeCubic 15 atom0393Coded := by decide +kernel
theorem atom0393Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (35700480 : Int) atom0393Coded) := by
  have h := atom0393_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0393Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0394 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0394 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0394 = ((g 3) * (g 6) * (g 9)) := by
  norm_num [atom0394, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0394_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72161280 : Int) atom0394) := by
  rw [SparsePolynomial.eval_scale, eval_atom0394]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0394Coded : CoefficientMerge.Poly := [(nat_lit 774, Int.ofNat (nat_lit 1))]
theorem atom0394Coded_decode : atom0394 = SparsePolynomial.decodeCubic 15 atom0394Coded := by decide +kernel
theorem atom0394Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (72161280 : Int) atom0394Coded) := by
  have h := atom0394_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0394Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0395 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0395 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0395 = ((g 3) * (g 6) * (g 10)) := by
  norm_num [atom0395, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0395_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50591520 : Int) atom0395) := by
  rw [SparsePolynomial.eval_scale, eval_atom0395]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0395Coded : CoefficientMerge.Poly := [(nat_lit 775, Int.ofNat (nat_lit 1))]
theorem atom0395Coded_decode : atom0395 = SparsePolynomial.decodeCubic 15 atom0395Coded := by decide +kernel
theorem atom0395Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (50591520 : Int) atom0395Coded) := by
  have h := atom0395_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0395Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0396 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0396 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0396 = ((g 3) * (g 6) * (g 11)) := by
  norm_num [atom0396, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0396_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (70005600 : Int) atom0396) := by
  rw [SparsePolynomial.eval_scale, eval_atom0396]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0396Coded : CoefficientMerge.Poly := [(nat_lit 776, Int.ofNat (nat_lit 1))]
theorem atom0396Coded_decode : atom0396 = SparsePolynomial.decodeCubic 15 atom0396Coded := by decide +kernel
theorem atom0396Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (70005600 : Int) atom0396Coded) := by
  have h := atom0396_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0396Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0397 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0397 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0397 = ((g 3) * (g 6) * (g 12)) := by
  norm_num [atom0397, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0397_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76122720 : Int) atom0397) := by
  rw [SparsePolynomial.eval_scale, eval_atom0397]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0397Coded : CoefficientMerge.Poly := [(nat_lit 777, Int.ofNat (nat_lit 1))]
theorem atom0397Coded_decode : atom0397 = SparsePolynomial.decodeCubic 15 atom0397Coded := by decide +kernel
theorem atom0397Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (76122720 : Int) atom0397Coded) := by
  have h := atom0397_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0397Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0398 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0398 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0398 = ((g 3) * (g 6) * (g 13)) := by
  norm_num [atom0398, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0398_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (92435040 : Int) atom0398) := by
  rw [SparsePolynomial.eval_scale, eval_atom0398]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0398Coded : CoefficientMerge.Poly := [(nat_lit 778, Int.ofNat (nat_lit 1))]
theorem atom0398Coded_decode : atom0398 = SparsePolynomial.decodeCubic 15 atom0398Coded := by decide +kernel
theorem atom0398Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (92435040 : Int) atom0398Coded) := by
  have h := atom0398_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0398Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0399 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0399 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0399 = ((g 3) * (g 6) * (g 14)) := by
  norm_num [atom0399, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0399_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108747360 : Int) atom0399) := by
  rw [SparsePolynomial.eval_scale, eval_atom0399]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0399Coded : CoefficientMerge.Poly := [(nat_lit 779, Int.ofNat (nat_lit 1))]
theorem atom0399Coded_decode : atom0399 = SparsePolynomial.decodeCubic 15 atom0399Coded := by decide +kernel
theorem atom0399Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (108747360 : Int) atom0399Coded) := by
  have h := atom0399_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0399Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0400 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0400 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0400 = ((g 3) * (g 7) * (g 7)) := by
  norm_num [atom0400, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0400_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25864320 : Int) atom0400) := by
  rw [SparsePolynomial.eval_scale, eval_atom0400]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0400Coded : CoefficientMerge.Poly := [(nat_lit 787, Int.ofNat (nat_lit 1))]
theorem atom0400Coded_decode : atom0400 = SparsePolynomial.decodeCubic 15 atom0400Coded := by decide +kernel
theorem atom0400Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (25864320 : Int) atom0400Coded) := by
  have h := atom0400_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0400Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0401 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0401 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0401 = ((g 3) * (g 7) * (g 8)) := by
  norm_num [atom0401, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0401_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52137600 : Int) atom0401) := by
  rw [SparsePolynomial.eval_scale, eval_atom0401]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0401Coded : CoefficientMerge.Poly := [(nat_lit 788, Int.ofNat (nat_lit 1))]
theorem atom0401Coded_decode : atom0401 = SparsePolynomial.decodeCubic 15 atom0401Coded := by decide +kernel
theorem atom0401Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (52137600 : Int) atom0401Coded) := by
  have h := atom0401_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0401Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0402 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0402 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0402 = ((g 3) * (g 7) * (g 9)) := by
  norm_num [atom0402, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0402_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82087680 : Int) atom0402) := by
  rw [SparsePolynomial.eval_scale, eval_atom0402]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0402Coded : CoefficientMerge.Poly := [(nat_lit 789, Int.ofNat (nat_lit 1))]
theorem atom0402Coded_decode : atom0402 = SparsePolynomial.decodeCubic 15 atom0402Coded := by decide +kernel
theorem atom0402Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (82087680 : Int) atom0402Coded) := by
  have h := atom0402_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0402Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0403 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0403 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0403 = ((g 3) * (g 7) * (g 10)) := by
  norm_num [atom0403, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0403_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64683600 : Int) atom0403) := by
  rw [SparsePolynomial.eval_scale, eval_atom0403]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0403Coded : CoefficientMerge.Poly := [(nat_lit 790, Int.ofNat (nat_lit 1))]
theorem atom0403Coded_decode : atom0403 = SparsePolynomial.decodeCubic 15 atom0403Coded := by decide +kernel
theorem atom0403Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (64683600 : Int) atom0403Coded) := by
  have h := atom0403_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0403Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0404 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0404 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0404 = ((g 3) * (g 7) * (g 11)) := by
  norm_num [atom0404, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0404_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87060960 : Int) atom0404) := by
  rw [SparsePolynomial.eval_scale, eval_atom0404]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0404Coded : CoefficientMerge.Poly := [(nat_lit 791, Int.ofNat (nat_lit 1))]
theorem atom0404Coded_decode : atom0404 = SparsePolynomial.decodeCubic 15 atom0404Coded := by decide +kernel
theorem atom0404Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (87060960 : Int) atom0404Coded) := by
  have h := atom0404_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0404Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0405 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0405 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0405 = ((g 3) * (g 7) * (g 12)) := by
  norm_num [atom0405, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0405_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89438640 : Int) atom0405) := by
  rw [SparsePolynomial.eval_scale, eval_atom0405]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0405Coded : CoefficientMerge.Poly := [(nat_lit 792, Int.ofNat (nat_lit 1))]
theorem atom0405Coded_decode : atom0405 = SparsePolynomial.decodeCubic 15 atom0405Coded := by decide +kernel
theorem atom0405Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (89438640 : Int) atom0405Coded) := by
  have h := atom0405_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0405Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0406 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0406 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0406 = ((g 3) * (g 7) * (g 13)) := by
  norm_num [atom0406, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0406_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105904560 : Int) atom0406) := by
  rw [SparsePolynomial.eval_scale, eval_atom0406]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0406Coded : CoefficientMerge.Poly := [(nat_lit 793, Int.ofNat (nat_lit 1))]
theorem atom0406Coded_decode : atom0406 = SparsePolynomial.decodeCubic 15 atom0406Coded := by decide +kernel
theorem atom0406Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (105904560 : Int) atom0406Coded) := by
  have h := atom0406_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0406Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0407 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0407 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0407 = ((g 3) * (g 7) * (g 14)) := by
  norm_num [atom0407, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0407_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (122426640 : Int) atom0407) := by
  rw [SparsePolynomial.eval_scale, eval_atom0407]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0407Coded : CoefficientMerge.Poly := [(nat_lit 794, Int.ofNat (nat_lit 1))]
theorem atom0407Coded_decode : atom0407 = SparsePolynomial.decodeCubic 15 atom0407Coded := by decide +kernel
theorem atom0407Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (122426640 : Int) atom0407Coded) := by
  have h := atom0407_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0407Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0408 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0408 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0408 = ((g 3) * (g 8) * (g 8)) := by
  norm_num [atom0408, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0408_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36201600 : Int) atom0408) := by
  rw [SparsePolynomial.eval_scale, eval_atom0408]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0408Coded : CoefficientMerge.Poly := [(nat_lit 803, Int.ofNat (nat_lit 1))]
theorem atom0408Coded_decode : atom0408 = SparsePolynomial.decodeCubic 15 atom0408Coded := by decide +kernel
theorem atom0408Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (36201600 : Int) atom0408Coded) := by
  have h := atom0408_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0408Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0409 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0409 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0409 = ((g 3) * (g 8) * (g 9)) := by
  norm_num [atom0409, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0409_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (99174240 : Int) atom0409) := by
  rw [SparsePolynomial.eval_scale, eval_atom0409]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0409Coded : CoefficientMerge.Poly := [(nat_lit 804, Int.ofNat (nat_lit 1))]
theorem atom0409Coded_decode : atom0409 = SparsePolynomial.decodeCubic 15 atom0409Coded := by decide +kernel
theorem atom0409Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (99174240 : Int) atom0409Coded) := by
  have h := atom0409_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0409Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0410 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0410 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0410 = ((g 3) * (g 8) * (g 10)) := by
  norm_num [atom0410, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0410_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78505200 : Int) atom0410) := by
  rw [SparsePolynomial.eval_scale, eval_atom0410]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0410Coded : CoefficientMerge.Poly := [(nat_lit 805, Int.ofNat (nat_lit 1))]
theorem atom0410Coded_decode : atom0410 = SparsePolynomial.decodeCubic 15 atom0410Coded := by decide +kernel
theorem atom0410Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (78505200 : Int) atom0410Coded) := by
  have h := atom0410_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0410Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0411 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0411 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0411 = ((g 3) * (g 8) * (g 11)) := by
  norm_num [atom0411, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0411_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (104116320 : Int) atom0411) := by
  rw [SparsePolynomial.eval_scale, eval_atom0411]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0411Coded : CoefficientMerge.Poly := [(nat_lit 806, Int.ofNat (nat_lit 1))]
theorem atom0411Coded_decode : atom0411 = SparsePolynomial.decodeCubic 15 atom0411Coded := by decide +kernel
theorem atom0411Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (104116320 : Int) atom0411Coded) := by
  have h := atom0411_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0411Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0412 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0412 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0412 = ((g 3) * (g 8) * (g 12)) := by
  norm_num [atom0412, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0412_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105652080 : Int) atom0412) := by
  rw [SparsePolynomial.eval_scale, eval_atom0412]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0412Coded : CoefficientMerge.Poly := [(nat_lit 807, Int.ofNat (nat_lit 1))]
theorem atom0412Coded_decode : atom0412 = SparsePolynomial.decodeCubic 15 atom0412Coded := by decide +kernel
theorem atom0412Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (105652080 : Int) atom0412Coded) := by
  have h := atom0412_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0412Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0413 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0413 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0413 = ((g 3) * (g 8) * (g 13)) := by
  norm_num [atom0413, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0413_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (109812240 : Int) atom0413) := by
  rw [SparsePolynomial.eval_scale, eval_atom0413]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0413Coded : CoefficientMerge.Poly := [(nat_lit 808, Int.ofNat (nat_lit 1))]
theorem atom0413Coded_decode : atom0413 = SparsePolynomial.decodeCubic 15 atom0413Coded := by decide +kernel
theorem atom0413Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (109812240 : Int) atom0413Coded) := by
  have h := atom0413_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0413Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0414 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0414 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0414 = ((g 3) * (g 8) * (g 14)) := by
  norm_num [atom0414, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0414_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153509040 : Int) atom0414) := by
  rw [SparsePolynomial.eval_scale, eval_atom0414]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0414Coded : CoefficientMerge.Poly := [(nat_lit 809, Int.ofNat (nat_lit 1))]
theorem atom0414Coded_decode : atom0414 = SparsePolynomial.decodeCubic 15 atom0414Coded := by decide +kernel
theorem atom0414Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (153509040 : Int) atom0414Coded) := by
  have h := atom0414_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0414Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0415 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0415 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0415 = ((g 3) * (g 9) * (g 9)) := by
  norm_num [atom0415, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0415_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74908800 : Int) atom0415) := by
  rw [SparsePolynomial.eval_scale, eval_atom0415]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0415Coded : CoefficientMerge.Poly := [(nat_lit 819, Int.ofNat (nat_lit 1))]
theorem atom0415Coded_decode : atom0415 = SparsePolynomial.decodeCubic 15 atom0415Coded := by decide +kernel
theorem atom0415Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (74908800 : Int) atom0415Coded) := by
  have h := atom0415_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0415Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0416 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0416 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0416 = ((g 3) * (g 9) * (g 10)) := by
  norm_num [atom0416, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0416_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (124263720 : Int) atom0416) := by
  rw [SparsePolynomial.eval_scale, eval_atom0416]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0416Coded : CoefficientMerge.Poly := [(nat_lit 820, Int.ofNat (nat_lit 1))]
theorem atom0416Coded_decode : atom0416 = SparsePolynomial.decodeCubic 15 atom0416Coded := by decide +kernel
theorem atom0416Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (124263720 : Int) atom0416Coded) := by
  have h := atom0416_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0416Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0417 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0417 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0417 = ((g 3) * (g 9) * (g 11)) := by
  norm_num [atom0417, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0417_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (176277600 : Int) atom0417) := by
  rw [SparsePolynomial.eval_scale, eval_atom0417]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0417Coded : CoefficientMerge.Poly := [(nat_lit 821, Int.ofNat (nat_lit 1))]
theorem atom0417Coded_decode : atom0417 = SparsePolynomial.decodeCubic 15 atom0417Coded := by decide +kernel
theorem atom0417Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (176277600 : Int) atom0417Coded) := by
  have h := atom0417_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0417Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0418 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0418 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0418 = ((g 3) * (g 9) * (g 12)) := by
  norm_num [atom0418, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0418_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (180672120 : Int) atom0418) := by
  rw [SparsePolynomial.eval_scale, eval_atom0418]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0418Coded : CoefficientMerge.Poly := [(nat_lit 822, Int.ofNat (nat_lit 1))]
theorem atom0418Coded_decode : atom0418 = SparsePolynomial.decodeCubic 15 atom0418Coded := by decide +kernel
theorem atom0418Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (180672120 : Int) atom0418Coded) := by
  have h := atom0418_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0418Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0419 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0419 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0419 = ((g 3) * (g 9) * (g 13)) := by
  norm_num [atom0419, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0419_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (113707800 : Int) atom0419) := by
  rw [SparsePolynomial.eval_scale, eval_atom0419]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0419Coded : CoefficientMerge.Poly := [(nat_lit 823, Int.ofNat (nat_lit 1))]
theorem atom0419Coded_decode : atom0419 = SparsePolynomial.decodeCubic 15 atom0419Coded := by decide +kernel
theorem atom0419Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (113707800 : Int) atom0419Coded) := by
  have h := atom0419_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0419Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0420 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0420 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0420 = ((g 3) * (g 9) * (g 14)) := by
  norm_num [atom0420, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0420_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (182823480 : Int) atom0420) := by
  rw [SparsePolynomial.eval_scale, eval_atom0420]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0420Coded : CoefficientMerge.Poly := [(nat_lit 824, Int.ofNat (nat_lit 1))]
theorem atom0420Coded_decode : atom0420 = SparsePolynomial.decodeCubic 15 atom0420Coded := by decide +kernel
theorem atom0420Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (182823480 : Int) atom0420Coded) := by
  have h := atom0420_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0420Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0421 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0421 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0421 = ((g 3) * (g 10) * (g 10)) := by
  norm_num [atom0421, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0421_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57262464 : Int) atom0421) := by
  rw [SparsePolynomial.eval_scale, eval_atom0421]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0421Coded : CoefficientMerge.Poly := [(nat_lit 835, Int.ofNat (nat_lit 1))]
theorem atom0421Coded_decode : atom0421 = SparsePolynomial.decodeCubic 15 atom0421Coded := by decide +kernel
theorem atom0421Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (57262464 : Int) atom0421Coded) := by
  have h := atom0421_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0421Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0422 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0422 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0422 = ((g 3) * (g 10) * (g 11)) := by
  norm_num [atom0422, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0422_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (145208160 : Int) atom0422) := by
  rw [SparsePolynomial.eval_scale, eval_atom0422]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0422Coded : CoefficientMerge.Poly := [(nat_lit 836, Int.ofNat (nat_lit 1))]
theorem atom0422Coded_decode : atom0422 = SparsePolynomial.decodeCubic 15 atom0422Coded := by decide +kernel
theorem atom0422Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (145208160 : Int) atom0422Coded) := by
  have h := atom0422_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0422Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0423 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0423 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0423 = ((g 3) * (g 10) * (g 12)) := by
  norm_num [atom0423, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0423_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (171628740 : Int) atom0423) := by
  rw [SparsePolynomial.eval_scale, eval_atom0423]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0423Coded : CoefficientMerge.Poly := [(nat_lit 837, Int.ofNat (nat_lit 1))]
theorem atom0423Coded_decode : atom0423 = SparsePolynomial.decodeCubic 15 atom0423Coded := by decide +kernel
theorem atom0423Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (171628740 : Int) atom0423Coded) := by
  have h := atom0423_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0423Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0424 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0424 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0424 = ((g 3) * (g 10) * (g 13)) := by
  norm_num [atom0424, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0424_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121886640 : Int) atom0424) := by
  rw [SparsePolynomial.eval_scale, eval_atom0424]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0424Coded : CoefficientMerge.Poly := [(nat_lit 838, Int.ofNat (nat_lit 1))]
theorem atom0424Coded_decode : atom0424 = SparsePolynomial.decodeCubic 15 atom0424Coded := by decide +kernel
theorem atom0424Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (121886640 : Int) atom0424Coded) := by
  have h := atom0424_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0424Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0425 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0425 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0425 = ((g 3) * (g 10) * (g 14)) := by
  norm_num [atom0425, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0425_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154082790 : Int) atom0425) := by
  rw [SparsePolynomial.eval_scale, eval_atom0425]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0425Coded : CoefficientMerge.Poly := [(nat_lit 839, Int.ofNat (nat_lit 1))]
theorem atom0425Coded_decode : atom0425 = SparsePolynomial.decodeCubic 15 atom0425Coded := by decide +kernel
theorem atom0425Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (154082790 : Int) atom0425Coded) := by
  have h := atom0425_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0425Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0426 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0426 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0426 = ((g 3) * (g 11) * (g 11)) := by
  norm_num [atom0426, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0426_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98175240 : Int) atom0426) := by
  rw [SparsePolynomial.eval_scale, eval_atom0426]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0426Coded : CoefficientMerge.Poly := [(nat_lit 851, Int.ofNat (nat_lit 1))]
theorem atom0426Coded_decode : atom0426 = SparsePolynomial.decodeCubic 15 atom0426Coded := by decide +kernel
theorem atom0426Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (98175240 : Int) atom0426Coded) := by
  have h := atom0426_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0426Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0427 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0427 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0427 = ((g 3) * (g 11) * (g 12)) := by
  norm_num [atom0427, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0427_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (171553680 : Int) atom0427) := by
  rw [SparsePolynomial.eval_scale, eval_atom0427]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0427Coded : CoefficientMerge.Poly := [(nat_lit 852, Int.ofNat (nat_lit 1))]
theorem atom0427Coded_decode : atom0427 = SparsePolynomial.decodeCubic 15 atom0427Coded := by decide +kernel
theorem atom0427Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (171553680 : Int) atom0427Coded) := by
  have h := atom0427_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0427Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0428 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0428 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0428 = ((g 3) * (g 11) * (g 13)) := by
  norm_num [atom0428, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0428_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (120222360 : Int) atom0428) := by
  rw [SparsePolynomial.eval_scale, eval_atom0428]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0428Coded : CoefficientMerge.Poly := [(nat_lit 853, Int.ofNat (nat_lit 1))]
theorem atom0428Coded_decode : atom0428 = SparsePolynomial.decodeCubic 15 atom0428Coded := by decide +kernel
theorem atom0428Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (120222360 : Int) atom0428Coded) := by
  have h := atom0428_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0428Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0429 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0429 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0429 = ((g 3) * (g 11) * (g 14)) := by
  norm_num [atom0429, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0429_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (170511480 : Int) atom0429) := by
  rw [SparsePolynomial.eval_scale, eval_atom0429]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0429Coded : CoefficientMerge.Poly := [(nat_lit 854, Int.ofNat (nat_lit 1))]
theorem atom0429Coded_decode : atom0429 = SparsePolynomial.decodeCubic 15 atom0429Coded := by decide +kernel
theorem atom0429Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (170511480 : Int) atom0429Coded) := by
  have h := atom0429_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0429Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0430 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0430 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0430 = ((g 3) * (g 12) * (g 12)) := by
  norm_num [atom0430, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0430_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64707660 : Int) atom0430) := by
  rw [SparsePolynomial.eval_scale, eval_atom0430]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0430Coded : CoefficientMerge.Poly := [(nat_lit 867, Int.ofNat (nat_lit 1))]
theorem atom0430Coded_decode : atom0430 = SparsePolynomial.decodeCubic 15 atom0430Coded := by decide +kernel
theorem atom0430Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (64707660 : Int) atom0430Coded) := by
  have h := atom0430_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0430Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0431 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0431 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0431 = ((g 3) * (g 12) * (g 13)) := by
  norm_num [atom0431, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0431_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (94666860 : Int) atom0431) := by
  rw [SparsePolynomial.eval_scale, eval_atom0431]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0431Coded : CoefficientMerge.Poly := [(nat_lit 868, Int.ofNat (nat_lit 1))]
theorem atom0431Coded_decode : atom0431 = SparsePolynomial.decodeCubic 15 atom0431Coded := by decide +kernel
theorem atom0431Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (94666860 : Int) atom0431Coded) := by
  have h := atom0431_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0431Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0432 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0432 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0432 = ((g 3) * (g 12) * (g 14)) := by
  norm_num [atom0432, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0432_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (155708190 : Int) atom0432) := by
  rw [SparsePolynomial.eval_scale, eval_atom0432]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0432Coded : CoefficientMerge.Poly := [(nat_lit 869, Int.ofNat (nat_lit 1))]
theorem atom0432Coded_decode : atom0432 = SparsePolynomial.decodeCubic 15 atom0432Coded := by decide +kernel
theorem atom0432Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (155708190 : Int) atom0432Coded) := by
  have h := atom0432_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0432Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0433 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0433 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0433 = ((g 3) * (g 13) * (g 13)) := by
  norm_num [atom0433, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0433_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15264720 : Int) atom0433) := by
  rw [SparsePolynomial.eval_scale, eval_atom0433]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0433Coded : CoefficientMerge.Poly := [(nat_lit 883, Int.ofNat (nat_lit 1))]
theorem atom0433Coded_decode : atom0433 = SparsePolynomial.decodeCubic 15 atom0433Coded := by decide +kernel
theorem atom0433Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (15264720 : Int) atom0433Coded) := by
  have h := atom0433_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0433Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0434 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0434 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0434 = ((g 3) * (g 13) * (g 14)) := by
  norm_num [atom0434, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0434_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (99311130 : Int) atom0434) := by
  rw [SparsePolynomial.eval_scale, eval_atom0434]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0434Coded : CoefficientMerge.Poly := [(nat_lit 884, Int.ofNat (nat_lit 1))]
theorem atom0434Coded_decode : atom0434 = SparsePolynomial.decodeCubic 15 atom0434Coded := by decide +kernel
theorem atom0434Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (99311130 : Int) atom0434Coded) := by
  have h := atom0434_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0434Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0435 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0435 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0435 = ((g 3) * (g 14) * (g 14)) := by
  norm_num [atom0435, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0435_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79701570 : Int) atom0435) := by
  rw [SparsePolynomial.eval_scale, eval_atom0435]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0435Coded : CoefficientMerge.Poly := [(nat_lit 899, Int.ofNat (nat_lit 1))]
theorem atom0435Coded_decode : atom0435 = SparsePolynomial.decodeCubic 15 atom0435Coded := by decide +kernel
theorem atom0435Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (79701570 : Int) atom0435Coded) := by
  have h := atom0435_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0435Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0436 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0436 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0436 = ((g 4) * (g 4) * (g 4)) := by
  norm_num [atom0436, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0436_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2931840 : Int) atom0436) := by
  rw [SparsePolynomial.eval_scale, eval_atom0436]
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 4) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0436Coded : CoefficientMerge.Poly := [(nat_lit 964, Int.ofNat (nat_lit 1))]
theorem atom0436Coded_decode : atom0436 = SparsePolynomial.decodeCubic 15 atom0436Coded := by decide +kernel
theorem atom0436Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (2931840 : Int) atom0436Coded) := by
  have h := atom0436_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0436Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0437 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0437 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0437 = ((g 4) * (g 4) * (g 9)) := by
  norm_num [atom0437, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0437_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19845360 : Int) atom0437) := by
  rw [SparsePolynomial.eval_scale, eval_atom0437]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0437Coded : CoefficientMerge.Poly := [(nat_lit 969, Int.ofNat (nat_lit 1))]
theorem atom0437Coded_decode : atom0437 = SparsePolynomial.decodeCubic 15 atom0437Coded := by decide +kernel
theorem atom0437Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (19845360 : Int) atom0437Coded) := by
  have h := atom0437_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0437Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0438 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0438 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0438 = ((g 4) * (g 4) * (g 11)) := by
  norm_num [atom0438, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0438_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (221760 : Int) atom0438) := by
  rw [SparsePolynomial.eval_scale, eval_atom0438]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0438Coded : CoefficientMerge.Poly := [(nat_lit 971, Int.ofNat (nat_lit 1))]
theorem atom0438Coded_decode : atom0438 = SparsePolynomial.decodeCubic 15 atom0438Coded := by decide +kernel
theorem atom0438Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (221760 : Int) atom0438Coded) := by
  have h := atom0438_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0438Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0439 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0439 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0439 = ((g 4) * (g 5) * (g 7)) := by
  norm_num [atom0439, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0439_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1900800 : Int) atom0439) := by
  rw [SparsePolynomial.eval_scale, eval_atom0439]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0439Coded : CoefficientMerge.Poly := [(nat_lit 982, Int.ofNat (nat_lit 1))]
theorem atom0439Coded_decode : atom0439 = SparsePolynomial.decodeCubic 15 atom0439Coded := by decide +kernel
theorem atom0439Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1900800 : Int) atom0439Coded) := by
  have h := atom0439_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0439Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0440 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0440 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0440 = ((g 4) * (g 5) * (g 8)) := by
  norm_num [atom0440, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0440_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3801600 : Int) atom0440) := by
  rw [SparsePolynomial.eval_scale, eval_atom0440]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0440Coded : CoefficientMerge.Poly := [(nat_lit 983, Int.ofNat (nat_lit 1))]
theorem atom0440Coded_decode : atom0440 = SparsePolynomial.decodeCubic 15 atom0440Coded := by decide +kernel
theorem atom0440Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (3801600 : Int) atom0440Coded) := by
  have h := atom0440_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0440Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0441 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0441 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0441 = ((g 4) * (g 5) * (g 9)) := by
  norm_num [atom0441, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0441_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33785280 : Int) atom0441) := by
  rw [SparsePolynomial.eval_scale, eval_atom0441]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0441Coded : CoefficientMerge.Poly := [(nat_lit 984, Int.ofNat (nat_lit 1))]
theorem atom0441Coded_decode : atom0441 = SparsePolynomial.decodeCubic 15 atom0441Coded := by decide +kernel
theorem atom0441Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (33785280 : Int) atom0441Coded) := by
  have h := atom0441_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0441Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0442 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0442 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0442 = ((g 4) * (g 5) * (g 10)) := by
  norm_num [atom0442, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0442_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4849920 : Int) atom0442) := by
  rw [SparsePolynomial.eval_scale, eval_atom0442]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0442Coded : CoefficientMerge.Poly := [(nat_lit 985, Int.ofNat (nat_lit 1))]
theorem atom0442Coded_decode : atom0442 = SparsePolynomial.decodeCubic 15 atom0442Coded := by decide +kernel
theorem atom0442Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (4849920 : Int) atom0442Coded) := by
  have h := atom0442_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0442Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0443 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0443 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0443 = ((g 4) * (g 5) * (g 11)) := by
  norm_num [atom0443, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0443_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11026080 : Int) atom0443) := by
  rw [SparsePolynomial.eval_scale, eval_atom0443]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0443Coded : CoefficientMerge.Poly := [(nat_lit 986, Int.ofNat (nat_lit 1))]
theorem atom0443Coded_decode : atom0443 = SparsePolynomial.decodeCubic 15 atom0443Coded := by decide +kernel
theorem atom0443Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (11026080 : Int) atom0443Coded) := by
  have h := atom0443_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0443Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0444 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0444 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0444 = ((g 4) * (g 5) * (g 12)) := by
  norm_num [atom0444, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0444_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22376160 : Int) atom0444) := by
  rw [SparsePolynomial.eval_scale, eval_atom0444]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0444Coded : CoefficientMerge.Poly := [(nat_lit 987, Int.ofNat (nat_lit 1))]
theorem atom0444Coded_decode : atom0444 = SparsePolynomial.decodeCubic 15 atom0444Coded := by decide +kernel
theorem atom0444Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (22376160 : Int) atom0444Coded) := by
  have h := atom0444_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0444Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0445 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0445 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0445 = ((g 4) * (g 5) * (g 13)) := by
  norm_num [atom0445, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0445_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37272960 : Int) atom0445) := by
  rw [SparsePolynomial.eval_scale, eval_atom0445]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0445Coded : CoefficientMerge.Poly := [(nat_lit 988, Int.ofNat (nat_lit 1))]
theorem atom0445Coded_decode : atom0445 = SparsePolynomial.decodeCubic 15 atom0445Coded := by decide +kernel
theorem atom0445Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (37272960 : Int) atom0445Coded) := by
  have h := atom0445_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0445Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0446 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0446 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0446 = ((g 4) * (g 5) * (g 14)) := by
  norm_num [atom0446, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0446_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54092880 : Int) atom0446) := by
  rw [SparsePolynomial.eval_scale, eval_atom0446]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0446Coded : CoefficientMerge.Poly := [(nat_lit 989, Int.ofNat (nat_lit 1))]
theorem atom0446Coded_decode : atom0446 = SparsePolynomial.decodeCubic 15 atom0446Coded := by decide +kernel
theorem atom0446Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (54092880 : Int) atom0446Coded) := by
  have h := atom0446_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0446Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0447 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0447 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0447 = ((g 4) * (g 6) * (g 6)) := by
  norm_num [atom0447, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0447_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5466240 : Int) atom0447) := by
  rw [SparsePolynomial.eval_scale, eval_atom0447]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0447Coded : CoefficientMerge.Poly := [(nat_lit 996, Int.ofNat (nat_lit 1))]
theorem atom0447Coded_decode : atom0447 = SparsePolynomial.decodeCubic 15 atom0447Coded := by decide +kernel
theorem atom0447Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (5466240 : Int) atom0447Coded) := by
  have h := atom0447_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0447Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0448 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0448 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0448 = ((g 4) * (g 6) * (g 7)) := by
  norm_num [atom0448, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0448_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13541760 : Int) atom0448) := by
  rw [SparsePolynomial.eval_scale, eval_atom0448]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0448Coded : CoefficientMerge.Poly := [(nat_lit 997, Int.ofNat (nat_lit 1))]
theorem atom0448Coded_decode : atom0448 = SparsePolynomial.decodeCubic 15 atom0448Coded := by decide +kernel
theorem atom0448Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (13541760 : Int) atom0448Coded) := by
  have h := atom0448_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0448Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0449 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0449 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0449 = ((g 4) * (g 6) * (g 8)) := by
  norm_num [atom0449, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0449_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16151040 : Int) atom0449) := by
  rw [SparsePolynomial.eval_scale, eval_atom0449]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0449Coded : CoefficientMerge.Poly := [(nat_lit 998, Int.ofNat (nat_lit 1))]
theorem atom0449Coded_decode : atom0449 = SparsePolynomial.decodeCubic 15 atom0449Coded := by decide +kernel
theorem atom0449Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (16151040 : Int) atom0449Coded) := by
  have h := atom0449_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0449Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0450 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0450 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0450 = ((g 4) * (g 6) * (g 9)) := by
  norm_num [atom0450, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0450_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42252480 : Int) atom0450) := by
  rw [SparsePolynomial.eval_scale, eval_atom0450]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0450Coded : CoefficientMerge.Poly := [(nat_lit 999, Int.ofNat (nat_lit 1))]
theorem atom0450Coded_decode : atom0450 = SparsePolynomial.decodeCubic 15 atom0450Coded := by decide +kernel
theorem atom0450Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (42252480 : Int) atom0450Coded) := by
  have h := atom0450_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0450Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0451 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0451 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0451 = ((g 4) * (g 6) * (g 10)) := by
  norm_num [atom0451, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0451_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23506560 : Int) atom0451) := by
  rw [SparsePolynomial.eval_scale, eval_atom0451]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0451Coded : CoefficientMerge.Poly := [(nat_lit 1000, Int.ofNat (nat_lit 1))]
theorem atom0451Coded_decode : atom0451 = SparsePolynomial.decodeCubic 15 atom0451Coded := by decide +kernel
theorem atom0451Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (23506560 : Int) atom0451Coded) := by
  have h := atom0451_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0451Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0452 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0452 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0452 = ((g 4) * (g 6) * (g 11)) := by
  norm_num [atom0452, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0452_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33835680 : Int) atom0452) := by
  rw [SparsePolynomial.eval_scale, eval_atom0452]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0452Coded : CoefficientMerge.Poly := [(nat_lit 1001, Int.ofNat (nat_lit 1))]
theorem atom0452Coded_decode : atom0452 = SparsePolynomial.decodeCubic 15 atom0452Coded := by decide +kernel
theorem atom0452Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (33835680 : Int) atom0452Coded) := by
  have h := atom0452_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0452Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0453 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0453 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0453 = ((g 4) * (g 6) * (g 12)) := by
  norm_num [atom0453, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0453_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49206240 : Int) atom0453) := by
  rw [SparsePolynomial.eval_scale, eval_atom0453]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0453Coded : CoefficientMerge.Poly := [(nat_lit 1002, Int.ofNat (nat_lit 1))]
theorem atom0453Coded_decode : atom0453 = SparsePolynomial.decodeCubic 15 atom0453Coded := by decide +kernel
theorem atom0453Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (49206240 : Int) atom0453Coded) := by
  have h := atom0453_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0453Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0454 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0454 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0454 = ((g 4) * (g 6) * (g 13)) := by
  norm_num [atom0454, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0454_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68711040 : Int) atom0454) := by
  rw [SparsePolynomial.eval_scale, eval_atom0454]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0454Coded : CoefficientMerge.Poly := [(nat_lit 1003, Int.ofNat (nat_lit 1))]
theorem atom0454Coded_decode : atom0454 = SparsePolynomial.decodeCubic 15 atom0454Coded := by decide +kernel
theorem atom0454Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (68711040 : Int) atom0454Coded) := by
  have h := atom0454_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0454Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0455 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0455 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0455 = ((g 4) * (g 6) * (g 14)) := by
  norm_num [atom0455, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0455_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89836560 : Int) atom0455) := by
  rw [SparsePolynomial.eval_scale, eval_atom0455]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0455Coded : CoefficientMerge.Poly := [(nat_lit 1004, Int.ofNat (nat_lit 1))]
theorem atom0455Coded_decode : atom0455 = SparsePolynomial.decodeCubic 15 atom0455Coded := by decide +kernel
theorem atom0455Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (89836560 : Int) atom0455Coded) := by
  have h := atom0455_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0455Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0456 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0456 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0456 = ((g 4) * (g 7) * (g 7)) := by
  norm_num [atom0456, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0456_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14188800 : Int) atom0456) := by
  rw [SparsePolynomial.eval_scale, eval_atom0456]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0456Coded : CoefficientMerge.Poly := [(nat_lit 1012, Int.ofNat (nat_lit 1))]
theorem atom0456Coded_decode : atom0456 = SparsePolynomial.decodeCubic 15 atom0456Coded := by decide +kernel
theorem atom0456Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (14188800 : Int) atom0456Coded) := by
  have h := atom0456_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0456Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0457 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0457 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0457 = ((g 4) * (g 7) * (g 8)) := by
  norm_num [atom0457, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0457_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30462720 : Int) atom0457) := by
  rw [SparsePolynomial.eval_scale, eval_atom0457]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0457Coded : CoefficientMerge.Poly := [(nat_lit 1013, Int.ofNat (nat_lit 1))]
theorem atom0457Coded_decode : atom0457 = SparsePolynomial.decodeCubic 15 atom0457Coded := by decide +kernel
theorem atom0457Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (30462720 : Int) atom0457Coded) := by
  have h := atom0457_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0457Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0458 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0458 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0458 = ((g 4) * (g 7) * (g 9)) := by
  norm_num [atom0458, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0458_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52680000 : Int) atom0458) := by
  rw [SparsePolynomial.eval_scale, eval_atom0458]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0458Coded : CoefficientMerge.Poly := [(nat_lit 1014, Int.ofNat (nat_lit 1))]
theorem atom0458Coded_decode : atom0458 = SparsePolynomial.decodeCubic 15 atom0458Coded := by decide +kernel
theorem atom0458Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (52680000 : Int) atom0458Coded) := by
  have h := atom0458_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0458Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0459 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0459 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0459 = ((g 4) * (g 7) * (g 10)) := by
  norm_num [atom0459, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0459_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40726320 : Int) atom0459) := by
  rw [SparsePolynomial.eval_scale, eval_atom0459]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0459Coded : CoefficientMerge.Poly := [(nat_lit 1015, Int.ofNat (nat_lit 1))]
theorem atom0459Coded_decode : atom0459 = SparsePolynomial.decodeCubic 15 atom0459Coded := by decide +kernel
theorem atom0459Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (40726320 : Int) atom0459Coded) := by
  have h := atom0459_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0459Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0460 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0460 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0460 = ((g 4) * (g 7) * (g 11)) := by
  norm_num [atom0460, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0460_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56645280 : Int) atom0460) := by
  rw [SparsePolynomial.eval_scale, eval_atom0460]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0460Coded : CoefficientMerge.Poly := [(nat_lit 1016, Int.ofNat (nat_lit 1))]
theorem atom0460Coded_decode : atom0460 = SparsePolynomial.decodeCubic 15 atom0460Coded := by decide +kernel
theorem atom0460Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (56645280 : Int) atom0460Coded) := by
  have h := atom0460_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0460Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0461 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0461 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0461 = ((g 4) * (g 7) * (g 12)) := by
  norm_num [atom0461, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0461_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (70185840 : Int) atom0461) := by
  rw [SparsePolynomial.eval_scale, eval_atom0461]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0461Coded : CoefficientMerge.Poly := [(nat_lit 1017, Int.ofNat (nat_lit 1))]
theorem atom0461Coded_decode : atom0461 = SparsePolynomial.decodeCubic 15 atom0461Coded := by decide +kernel
theorem atom0461Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (70185840 : Int) atom0461Coded) := by
  have h := atom0461_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0461Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0462 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0462 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0462 = ((g 4) * (g 7) * (g 13)) := by
  norm_num [atom0462, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0462_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (91753680 : Int) atom0462) := by
  rw [SparsePolynomial.eval_scale, eval_atom0462]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0462Coded : CoefficientMerge.Poly := [(nat_lit 1018, Int.ofNat (nat_lit 1))]
theorem atom0462Coded_decode : atom0462 = SparsePolynomial.decodeCubic 15 atom0462Coded := by decide +kernel
theorem atom0462Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (91753680 : Int) atom0462Coded) := by
  have h := atom0462_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0462Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0463 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0463 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0463 = ((g 4) * (g 7) * (g 14)) := by
  norm_num [atom0463, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0463_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (114639840 : Int) atom0463) := by
  rw [SparsePolynomial.eval_scale, eval_atom0463]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0463Coded : CoefficientMerge.Poly := [(nat_lit 1019, Int.ofNat (nat_lit 1))]
theorem atom0463Coded_decode : atom0463 = SparsePolynomial.decodeCubic 15 atom0463Coded := by decide +kernel
theorem atom0463Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (114639840 : Int) atom0463Coded) := by
  have h := atom0463_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0463Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0464 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0464 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0464 = ((g 4) * (g 8) * (g 8)) := by
  norm_num [atom0464, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0464_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24301440 : Int) atom0464) := by
  rw [SparsePolynomial.eval_scale, eval_atom0464]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0464Coded : CoefficientMerge.Poly := [(nat_lit 1028, Int.ofNat (nat_lit 1))]
theorem atom0464Coded_decode : atom0464 = SparsePolynomial.decodeCubic 15 atom0464Coded := by decide +kernel
theorem atom0464Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (24301440 : Int) atom0464Coded) := by
  have h := atom0464_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0464Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0465 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0465 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0465 = ((g 4) * (g 8) * (g 9)) := by
  norm_num [atom0465, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0465_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (70267680 : Int) atom0465) := by
  rw [SparsePolynomial.eval_scale, eval_atom0465]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0465Coded : CoefficientMerge.Poly := [(nat_lit 1029, Int.ofNat (nat_lit 1))]
theorem atom0465Coded_decode : atom0465 = SparsePolynomial.decodeCubic 15 atom0465Coded := by decide +kernel
theorem atom0465Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (70267680 : Int) atom0465Coded) := by
  have h := atom0465_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0465Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0466 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0466 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0466 = ((g 4) * (g 8) * (g 10)) := by
  norm_num [atom0466, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0466_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57675600 : Int) atom0466) := by
  rw [SparsePolynomial.eval_scale, eval_atom0466]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0466Coded : CoefficientMerge.Poly := [(nat_lit 1030, Int.ofNat (nat_lit 1))]
theorem atom0466Coded_decode : atom0466 = SparsePolynomial.decodeCubic 15 atom0466Coded := by decide +kernel
theorem atom0466Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (57675600 : Int) atom0466Coded) := by
  have h := atom0466_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0466Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0467 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0467 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0467 = ((g 4) * (g 8) * (g 11)) := by
  norm_num [atom0467, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0467_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79454880 : Int) atom0467) := by
  rw [SparsePolynomial.eval_scale, eval_atom0467]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0467Coded : CoefficientMerge.Poly := [(nat_lit 1031, Int.ofNat (nat_lit 1))]
theorem atom0467Coded_decode : atom0467 = SparsePolynomial.decodeCubic 15 atom0467Coded := by decide +kernel
theorem atom0467Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (79454880 : Int) atom0467Coded) := by
  have h := atom0467_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0467Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0468 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0468 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0468 = ((g 4) * (g 8) * (g 12)) := by
  norm_num [atom0468, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0468_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (94062960 : Int) atom0468) := by
  rw [SparsePolynomial.eval_scale, eval_atom0468]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0468Coded : CoefficientMerge.Poly := [(nat_lit 1032, Int.ofNat (nat_lit 1))]
theorem atom0468Coded_decode : atom0468 = SparsePolynomial.decodeCubic 15 atom0468Coded := by decide +kernel
theorem atom0468Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (94062960 : Int) atom0468Coded) := by
  have h := atom0468_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0468Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0469 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0469 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0469 = ((g 4) * (g 8) * (g 13)) := by
  norm_num [atom0469, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0469_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105234480 : Int) atom0469) := by
  rw [SparsePolynomial.eval_scale, eval_atom0469]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0469Coded : CoefficientMerge.Poly := [(nat_lit 1033, Int.ofNat (nat_lit 1))]
theorem atom0469Coded_decode : atom0469 = SparsePolynomial.decodeCubic 15 atom0469Coded := by decide +kernel
theorem atom0469Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (105234480 : Int) atom0469Coded) := by
  have h := atom0469_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0469Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0470 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0470 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0470 = ((g 4) * (g 8) * (g 14)) := by
  norm_num [atom0470, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0470_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (156846240 : Int) atom0470) := by
  rw [SparsePolynomial.eval_scale, eval_atom0470]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0470Coded : CoefficientMerge.Poly := [(nat_lit 1034, Int.ofNat (nat_lit 1))]
theorem atom0470Coded_decode : atom0470 = SparsePolynomial.decodeCubic 15 atom0470Coded := by decide +kernel
theorem atom0470Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (156846240 : Int) atom0470Coded) := by
  have h := atom0470_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0470Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0471 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0471 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0471 = ((g 4) * (g 9) * (g 9)) := by
  norm_num [atom0471, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0471_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59616000 : Int) atom0471) := by
  rw [SparsePolynomial.eval_scale, eval_atom0471]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0471Coded : CoefficientMerge.Poly := [(nat_lit 1044, Int.ofNat (nat_lit 1))]
theorem atom0471Coded_decode : atom0471 = SparsePolynomial.decodeCubic 15 atom0471Coded := by decide +kernel
theorem atom0471Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (59616000 : Int) atom0471Coded) := by
  have h := atom0471_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0471Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0472 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0472 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0472 = ((g 4) * (g 9) * (g 10)) := by
  norm_num [atom0472, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0472_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103584600 : Int) atom0472) := by
  rw [SparsePolynomial.eval_scale, eval_atom0472]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0472Coded : CoefficientMerge.Poly := [(nat_lit 1045, Int.ofNat (nat_lit 1))]
theorem atom0472Coded_decode : atom0472 = SparsePolynomial.decodeCubic 15 atom0472Coded := by decide +kernel
theorem atom0472Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (103584600 : Int) atom0472Coded) := by
  have h := atom0472_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0472Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block005 : CoefficientMerge.Poly := [(nat_lit 773, Int.ofNat (nat_lit 35700480)), (nat_lit 774, Int.ofNat (nat_lit 72161280)), (nat_lit 775, Int.ofNat (nat_lit 50591520)), (nat_lit 776, Int.ofNat (nat_lit 70005600)), (nat_lit 777, Int.ofNat (nat_lit 76122720)), (nat_lit 778, Int.ofNat (nat_lit 92435040)), (nat_lit 779, Int.ofNat (nat_lit 108747360)), (nat_lit 787, Int.ofNat (nat_lit 25864320)), (nat_lit 788, Int.ofNat (nat_lit 52137600)), (nat_lit 789, Int.ofNat (nat_lit 82087680)), (nat_lit 790, Int.ofNat (nat_lit 64683600)), (nat_lit 791, Int.ofNat (nat_lit 87060960)), (nat_lit 792, Int.ofNat (nat_lit 89438640)), (nat_lit 793, Int.ofNat (nat_lit 105904560)), (nat_lit 794, Int.ofNat (nat_lit 122426640)), (nat_lit 803, Int.ofNat (nat_lit 36201600)), (nat_lit 804, Int.ofNat (nat_lit 99174240)), (nat_lit 805, Int.ofNat (nat_lit 78505200)), (nat_lit 806, Int.ofNat (nat_lit 104116320)), (nat_lit 807, Int.ofNat (nat_lit 105652080)), (nat_lit 808, Int.ofNat (nat_lit 109812240)), (nat_lit 809, Int.ofNat (nat_lit 153509040)), (nat_lit 819, Int.ofNat (nat_lit 74908800)), (nat_lit 820, Int.ofNat (nat_lit 124263720)), (nat_lit 821, Int.ofNat (nat_lit 176277600)), (nat_lit 822, Int.ofNat (nat_lit 180672120)), (nat_lit 823, Int.ofNat (nat_lit 113707800)), (nat_lit 824, Int.ofNat (nat_lit 182823480)), (nat_lit 835, Int.ofNat (nat_lit 57262464)), (nat_lit 836, Int.ofNat (nat_lit 145208160)), (nat_lit 837, Int.ofNat (nat_lit 171628740)), (nat_lit 838, Int.ofNat (nat_lit 121886640)), (nat_lit 839, Int.ofNat (nat_lit 154082790)), (nat_lit 851, Int.ofNat (nat_lit 98175240)), (nat_lit 852, Int.ofNat (nat_lit 171553680)), (nat_lit 853, Int.ofNat (nat_lit 120222360)), (nat_lit 854, Int.ofNat (nat_lit 170511480)), (nat_lit 867, Int.ofNat (nat_lit 64707660)), (nat_lit 868, Int.ofNat (nat_lit 94666860)), (nat_lit 869, Int.ofNat (nat_lit 155708190)), (nat_lit 883, Int.ofNat (nat_lit 15264720)), (nat_lit 884, Int.ofNat (nat_lit 99311130)), (nat_lit 899, Int.ofNat (nat_lit 79701570)), (nat_lit 964, Int.ofNat (nat_lit 2931840)), (nat_lit 969, Int.ofNat (nat_lit 19845360)), (nat_lit 971, Int.ofNat (nat_lit 221760)), (nat_lit 982, Int.ofNat (nat_lit 1900800)), (nat_lit 983, Int.ofNat (nat_lit 3801600)), (nat_lit 984, Int.ofNat (nat_lit 33785280)), (nat_lit 985, Int.ofNat (nat_lit 4849920)), (nat_lit 986, Int.ofNat (nat_lit 11026080)), (nat_lit 987, Int.ofNat (nat_lit 22376160)), (nat_lit 988, Int.ofNat (nat_lit 37272960)), (nat_lit 989, Int.ofNat (nat_lit 54092880)), (nat_lit 996, Int.ofNat (nat_lit 5466240)), (nat_lit 997, Int.ofNat (nat_lit 13541760)), (nat_lit 998, Int.ofNat (nat_lit 16151040)), (nat_lit 999, Int.ofNat (nat_lit 42252480)), (nat_lit 1000, Int.ofNat (nat_lit 23506560)), (nat_lit 1001, Int.ofNat (nat_lit 33835680)), (nat_lit 1002, Int.ofNat (nat_lit 49206240)), (nat_lit 1003, Int.ofNat (nat_lit 68711040)), (nat_lit 1004, Int.ofNat (nat_lit 89836560)), (nat_lit 1012, Int.ofNat (nat_lit 14188800)), (nat_lit 1013, Int.ofNat (nat_lit 30462720)), (nat_lit 1014, Int.ofNat (nat_lit 52680000)), (nat_lit 1015, Int.ofNat (nat_lit 40726320)), (nat_lit 1016, Int.ofNat (nat_lit 56645280)), (nat_lit 1017, Int.ofNat (nat_lit 70185840)), (nat_lit 1018, Int.ofNat (nat_lit 91753680)), (nat_lit 1019, Int.ofNat (nat_lit 114639840)), (nat_lit 1028, Int.ofNat (nat_lit 24301440)), (nat_lit 1029, Int.ofNat (nat_lit 70267680)), (nat_lit 1030, Int.ofNat (nat_lit 57675600)), (nat_lit 1031, Int.ofNat (nat_lit 79454880)), (nat_lit 1032, Int.ofNat (nat_lit 94062960)), (nat_lit 1033, Int.ofNat (nat_lit 105234480)), (nat_lit 1034, Int.ofNat (nat_lit 156846240)), (nat_lit 1044, Int.ofNat (nat_lit 59616000)), (nat_lit 1045, Int.ofNat (nat_lit 103584600))]
def block005_data_flat000 : CoefficientMerge.Poly := [(nat_lit 773, Int.ofNat (nat_lit 35700480))]
theorem block005_data_flat000_step : block005_data_flat000 = (CoefficientMerge.scale (35700480 : Int) atom0393Coded) := by decide +kernel
theorem block005_data_flat000_original : block005_data_flat000 = (CoefficientMerge.scale (35700480 : Int) atom0393Coded) := by
  rw [block005_data_flat000_step]
def block005_data_flat001 : CoefficientMerge.Poly := [(nat_lit 774, Int.ofNat (nat_lit 72161280))]
theorem block005_data_flat001_step : block005_data_flat001 = (CoefficientMerge.scale (72161280 : Int) atom0394Coded) := by decide +kernel
theorem block005_data_flat001_original : block005_data_flat001 = (CoefficientMerge.scale (72161280 : Int) atom0394Coded) := by
  rw [block005_data_flat001_step]
def block005_data_flat002 : CoefficientMerge.Poly := [(nat_lit 773, Int.ofNat (nat_lit 35700480)), (nat_lit 774, Int.ofNat (nat_lit 72161280))]
theorem block005_data_flat002_step : block005_data_flat002 = (CoefficientMerge.fastMerge block005_data_flat000 block005_data_flat001) := by decide +kernel
theorem block005_data_flat002_original : block005_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35700480 : Int) atom0393Coded) (CoefficientMerge.scale (72161280 : Int) atom0394Coded)) := by
  rw [block005_data_flat002_step, block005_data_flat000_original, block005_data_flat001_original]
def block005_data_flat003 : CoefficientMerge.Poly := [(nat_lit 775, Int.ofNat (nat_lit 50591520))]
theorem block005_data_flat003_step : block005_data_flat003 = (CoefficientMerge.scale (50591520 : Int) atom0395Coded) := by decide +kernel
theorem block005_data_flat003_original : block005_data_flat003 = (CoefficientMerge.scale (50591520 : Int) atom0395Coded) := by
  rw [block005_data_flat003_step]
def block005_data_flat004 : CoefficientMerge.Poly := [(nat_lit 776, Int.ofNat (nat_lit 70005600))]
theorem block005_data_flat004_step : block005_data_flat004 = (CoefficientMerge.scale (70005600 : Int) atom0396Coded) := by decide +kernel
theorem block005_data_flat004_original : block005_data_flat004 = (CoefficientMerge.scale (70005600 : Int) atom0396Coded) := by
  rw [block005_data_flat004_step]
def block005_data_flat005 : CoefficientMerge.Poly := [(nat_lit 777, Int.ofNat (nat_lit 76122720))]
theorem block005_data_flat005_step : block005_data_flat005 = (CoefficientMerge.scale (76122720 : Int) atom0397Coded) := by decide +kernel
theorem block005_data_flat005_original : block005_data_flat005 = (CoefficientMerge.scale (76122720 : Int) atom0397Coded) := by
  rw [block005_data_flat005_step]
def block005_data_flat006 : CoefficientMerge.Poly := [(nat_lit 776, Int.ofNat (nat_lit 70005600)), (nat_lit 777, Int.ofNat (nat_lit 76122720))]
theorem block005_data_flat006_step : block005_data_flat006 = (CoefficientMerge.fastMerge block005_data_flat004 block005_data_flat005) := by decide +kernel
theorem block005_data_flat006_original : block005_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (70005600 : Int) atom0396Coded) (CoefficientMerge.scale (76122720 : Int) atom0397Coded)) := by
  rw [block005_data_flat006_step, block005_data_flat004_original, block005_data_flat005_original]
def block005_data_flat007 : CoefficientMerge.Poly := [(nat_lit 775, Int.ofNat (nat_lit 50591520)), (nat_lit 776, Int.ofNat (nat_lit 70005600)), (nat_lit 777, Int.ofNat (nat_lit 76122720))]
theorem block005_data_flat007_step : block005_data_flat007 = (CoefficientMerge.fastMerge block005_data_flat003 block005_data_flat006) := by decide +kernel
theorem block005_data_flat007_original : block005_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (50591520 : Int) atom0395Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70005600 : Int) atom0396Coded) (CoefficientMerge.scale (76122720 : Int) atom0397Coded))) := by
  rw [block005_data_flat007_step, block005_data_flat003_original, block005_data_flat006_original]
def block005_data_flat008 : CoefficientMerge.Poly := [(nat_lit 773, Int.ofNat (nat_lit 35700480)), (nat_lit 774, Int.ofNat (nat_lit 72161280)), (nat_lit 775, Int.ofNat (nat_lit 50591520)), (nat_lit 776, Int.ofNat (nat_lit 70005600)), (nat_lit 777, Int.ofNat (nat_lit 76122720))]
theorem block005_data_flat008_step : block005_data_flat008 = (CoefficientMerge.fastMerge block005_data_flat002 block005_data_flat007) := by decide +kernel
theorem block005_data_flat008_original : block005_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35700480 : Int) atom0393Coded) (CoefficientMerge.scale (72161280 : Int) atom0394Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50591520 : Int) atom0395Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70005600 : Int) atom0396Coded) (CoefficientMerge.scale (76122720 : Int) atom0397Coded)))) := by
  rw [block005_data_flat008_step, block005_data_flat002_original, block005_data_flat007_original]
def block005_data_flat009 : CoefficientMerge.Poly := [(nat_lit 778, Int.ofNat (nat_lit 92435040))]
theorem block005_data_flat009_step : block005_data_flat009 = (CoefficientMerge.scale (92435040 : Int) atom0398Coded) := by decide +kernel
theorem block005_data_flat009_original : block005_data_flat009 = (CoefficientMerge.scale (92435040 : Int) atom0398Coded) := by
  rw [block005_data_flat009_step]
def block005_data_flat010 : CoefficientMerge.Poly := [(nat_lit 779, Int.ofNat (nat_lit 108747360))]
theorem block005_data_flat010_step : block005_data_flat010 = (CoefficientMerge.scale (108747360 : Int) atom0399Coded) := by decide +kernel
theorem block005_data_flat010_original : block005_data_flat010 = (CoefficientMerge.scale (108747360 : Int) atom0399Coded) := by
  rw [block005_data_flat010_step]
def block005_data_flat011 : CoefficientMerge.Poly := [(nat_lit 778, Int.ofNat (nat_lit 92435040)), (nat_lit 779, Int.ofNat (nat_lit 108747360))]
theorem block005_data_flat011_step : block005_data_flat011 = (CoefficientMerge.fastMerge block005_data_flat009 block005_data_flat010) := by decide +kernel
theorem block005_data_flat011_original : block005_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (92435040 : Int) atom0398Coded) (CoefficientMerge.scale (108747360 : Int) atom0399Coded)) := by
  rw [block005_data_flat011_step, block005_data_flat009_original, block005_data_flat010_original]
def block005_data_flat012 : CoefficientMerge.Poly := [(nat_lit 787, Int.ofNat (nat_lit 25864320))]
theorem block005_data_flat012_step : block005_data_flat012 = (CoefficientMerge.scale (25864320 : Int) atom0400Coded) := by decide +kernel
theorem block005_data_flat012_original : block005_data_flat012 = (CoefficientMerge.scale (25864320 : Int) atom0400Coded) := by
  rw [block005_data_flat012_step]
def block005_data_flat013 : CoefficientMerge.Poly := [(nat_lit 788, Int.ofNat (nat_lit 52137600))]
theorem block005_data_flat013_step : block005_data_flat013 = (CoefficientMerge.scale (52137600 : Int) atom0401Coded) := by decide +kernel
theorem block005_data_flat013_original : block005_data_flat013 = (CoefficientMerge.scale (52137600 : Int) atom0401Coded) := by
  rw [block005_data_flat013_step]
def block005_data_flat014 : CoefficientMerge.Poly := [(nat_lit 789, Int.ofNat (nat_lit 82087680))]
theorem block005_data_flat014_step : block005_data_flat014 = (CoefficientMerge.scale (82087680 : Int) atom0402Coded) := by decide +kernel
theorem block005_data_flat014_original : block005_data_flat014 = (CoefficientMerge.scale (82087680 : Int) atom0402Coded) := by
  rw [block005_data_flat014_step]
def block005_data_flat015 : CoefficientMerge.Poly := [(nat_lit 788, Int.ofNat (nat_lit 52137600)), (nat_lit 789, Int.ofNat (nat_lit 82087680))]
theorem block005_data_flat015_step : block005_data_flat015 = (CoefficientMerge.fastMerge block005_data_flat013 block005_data_flat014) := by decide +kernel
theorem block005_data_flat015_original : block005_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (52137600 : Int) atom0401Coded) (CoefficientMerge.scale (82087680 : Int) atom0402Coded)) := by
  rw [block005_data_flat015_step, block005_data_flat013_original, block005_data_flat014_original]
def block005_data_flat016 : CoefficientMerge.Poly := [(nat_lit 787, Int.ofNat (nat_lit 25864320)), (nat_lit 788, Int.ofNat (nat_lit 52137600)), (nat_lit 789, Int.ofNat (nat_lit 82087680))]
theorem block005_data_flat016_step : block005_data_flat016 = (CoefficientMerge.fastMerge block005_data_flat012 block005_data_flat015) := by decide +kernel
theorem block005_data_flat016_original : block005_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25864320 : Int) atom0400Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52137600 : Int) atom0401Coded) (CoefficientMerge.scale (82087680 : Int) atom0402Coded))) := by
  rw [block005_data_flat016_step, block005_data_flat012_original, block005_data_flat015_original]
def block005_data_flat017 : CoefficientMerge.Poly := [(nat_lit 778, Int.ofNat (nat_lit 92435040)), (nat_lit 779, Int.ofNat (nat_lit 108747360)), (nat_lit 787, Int.ofNat (nat_lit 25864320)), (nat_lit 788, Int.ofNat (nat_lit 52137600)), (nat_lit 789, Int.ofNat (nat_lit 82087680))]
theorem block005_data_flat017_step : block005_data_flat017 = (CoefficientMerge.fastMerge block005_data_flat011 block005_data_flat016) := by decide +kernel
theorem block005_data_flat017_original : block005_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (92435040 : Int) atom0398Coded) (CoefficientMerge.scale (108747360 : Int) atom0399Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25864320 : Int) atom0400Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52137600 : Int) atom0401Coded) (CoefficientMerge.scale (82087680 : Int) atom0402Coded)))) := by
  rw [block005_data_flat017_step, block005_data_flat011_original, block005_data_flat016_original]
def block005_data_flat018 : CoefficientMerge.Poly := [(nat_lit 773, Int.ofNat (nat_lit 35700480)), (nat_lit 774, Int.ofNat (nat_lit 72161280)), (nat_lit 775, Int.ofNat (nat_lit 50591520)), (nat_lit 776, Int.ofNat (nat_lit 70005600)), (nat_lit 777, Int.ofNat (nat_lit 76122720)), (nat_lit 778, Int.ofNat (nat_lit 92435040)), (nat_lit 779, Int.ofNat (nat_lit 108747360)), (nat_lit 787, Int.ofNat (nat_lit 25864320)), (nat_lit 788, Int.ofNat (nat_lit 52137600)), (nat_lit 789, Int.ofNat (nat_lit 82087680))]
theorem block005_data_flat018_step : block005_data_flat018 = (CoefficientMerge.fastMerge block005_data_flat008 block005_data_flat017) := by decide +kernel
theorem block005_data_flat018_original : block005_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35700480 : Int) atom0393Coded) (CoefficientMerge.scale (72161280 : Int) atom0394Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50591520 : Int) atom0395Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70005600 : Int) atom0396Coded) (CoefficientMerge.scale (76122720 : Int) atom0397Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (92435040 : Int) atom0398Coded) (CoefficientMerge.scale (108747360 : Int) atom0399Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25864320 : Int) atom0400Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52137600 : Int) atom0401Coded) (CoefficientMerge.scale (82087680 : Int) atom0402Coded))))) := by
  rw [block005_data_flat018_step, block005_data_flat008_original, block005_data_flat017_original]
def block005_data_flat019 : CoefficientMerge.Poly := [(nat_lit 790, Int.ofNat (nat_lit 64683600))]
theorem block005_data_flat019_step : block005_data_flat019 = (CoefficientMerge.scale (64683600 : Int) atom0403Coded) := by decide +kernel
theorem block005_data_flat019_original : block005_data_flat019 = (CoefficientMerge.scale (64683600 : Int) atom0403Coded) := by
  rw [block005_data_flat019_step]
def block005_data_flat020 : CoefficientMerge.Poly := [(nat_lit 791, Int.ofNat (nat_lit 87060960))]
theorem block005_data_flat020_step : block005_data_flat020 = (CoefficientMerge.scale (87060960 : Int) atom0404Coded) := by decide +kernel
theorem block005_data_flat020_original : block005_data_flat020 = (CoefficientMerge.scale (87060960 : Int) atom0404Coded) := by
  rw [block005_data_flat020_step]
def block005_data_flat021 : CoefficientMerge.Poly := [(nat_lit 790, Int.ofNat (nat_lit 64683600)), (nat_lit 791, Int.ofNat (nat_lit 87060960))]
theorem block005_data_flat021_step : block005_data_flat021 = (CoefficientMerge.fastMerge block005_data_flat019 block005_data_flat020) := by decide +kernel
theorem block005_data_flat021_original : block005_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (64683600 : Int) atom0403Coded) (CoefficientMerge.scale (87060960 : Int) atom0404Coded)) := by
  rw [block005_data_flat021_step, block005_data_flat019_original, block005_data_flat020_original]
def block005_data_flat022 : CoefficientMerge.Poly := [(nat_lit 792, Int.ofNat (nat_lit 89438640))]
theorem block005_data_flat022_step : block005_data_flat022 = (CoefficientMerge.scale (89438640 : Int) atom0405Coded) := by decide +kernel
theorem block005_data_flat022_original : block005_data_flat022 = (CoefficientMerge.scale (89438640 : Int) atom0405Coded) := by
  rw [block005_data_flat022_step]
def block005_data_flat023 : CoefficientMerge.Poly := [(nat_lit 793, Int.ofNat (nat_lit 105904560))]
theorem block005_data_flat023_step : block005_data_flat023 = (CoefficientMerge.scale (105904560 : Int) atom0406Coded) := by decide +kernel
theorem block005_data_flat023_original : block005_data_flat023 = (CoefficientMerge.scale (105904560 : Int) atom0406Coded) := by
  rw [block005_data_flat023_step]
def block005_data_flat024 : CoefficientMerge.Poly := [(nat_lit 794, Int.ofNat (nat_lit 122426640))]
theorem block005_data_flat024_step : block005_data_flat024 = (CoefficientMerge.scale (122426640 : Int) atom0407Coded) := by decide +kernel
theorem block005_data_flat024_original : block005_data_flat024 = (CoefficientMerge.scale (122426640 : Int) atom0407Coded) := by
  rw [block005_data_flat024_step]
def block005_data_flat025 : CoefficientMerge.Poly := [(nat_lit 793, Int.ofNat (nat_lit 105904560)), (nat_lit 794, Int.ofNat (nat_lit 122426640))]
theorem block005_data_flat025_step : block005_data_flat025 = (CoefficientMerge.fastMerge block005_data_flat023 block005_data_flat024) := by decide +kernel
theorem block005_data_flat025_original : block005_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (105904560 : Int) atom0406Coded) (CoefficientMerge.scale (122426640 : Int) atom0407Coded)) := by
  rw [block005_data_flat025_step, block005_data_flat023_original, block005_data_flat024_original]
def block005_data_flat026 : CoefficientMerge.Poly := [(nat_lit 792, Int.ofNat (nat_lit 89438640)), (nat_lit 793, Int.ofNat (nat_lit 105904560)), (nat_lit 794, Int.ofNat (nat_lit 122426640))]
theorem block005_data_flat026_step : block005_data_flat026 = (CoefficientMerge.fastMerge block005_data_flat022 block005_data_flat025) := by decide +kernel
theorem block005_data_flat026_original : block005_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (89438640 : Int) atom0405Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105904560 : Int) atom0406Coded) (CoefficientMerge.scale (122426640 : Int) atom0407Coded))) := by
  rw [block005_data_flat026_step, block005_data_flat022_original, block005_data_flat025_original]
def block005_data_flat027 : CoefficientMerge.Poly := [(nat_lit 790, Int.ofNat (nat_lit 64683600)), (nat_lit 791, Int.ofNat (nat_lit 87060960)), (nat_lit 792, Int.ofNat (nat_lit 89438640)), (nat_lit 793, Int.ofNat (nat_lit 105904560)), (nat_lit 794, Int.ofNat (nat_lit 122426640))]
theorem block005_data_flat027_step : block005_data_flat027 = (CoefficientMerge.fastMerge block005_data_flat021 block005_data_flat026) := by decide +kernel
theorem block005_data_flat027_original : block005_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64683600 : Int) atom0403Coded) (CoefficientMerge.scale (87060960 : Int) atom0404Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89438640 : Int) atom0405Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105904560 : Int) atom0406Coded) (CoefficientMerge.scale (122426640 : Int) atom0407Coded)))) := by
  rw [block005_data_flat027_step, block005_data_flat021_original, block005_data_flat026_original]
def block005_data_flat028 : CoefficientMerge.Poly := [(nat_lit 803, Int.ofNat (nat_lit 36201600))]
theorem block005_data_flat028_step : block005_data_flat028 = (CoefficientMerge.scale (36201600 : Int) atom0408Coded) := by decide +kernel
theorem block005_data_flat028_original : block005_data_flat028 = (CoefficientMerge.scale (36201600 : Int) atom0408Coded) := by
  rw [block005_data_flat028_step]
def block005_data_flat029 : CoefficientMerge.Poly := [(nat_lit 804, Int.ofNat (nat_lit 99174240))]
theorem block005_data_flat029_step : block005_data_flat029 = (CoefficientMerge.scale (99174240 : Int) atom0409Coded) := by decide +kernel
theorem block005_data_flat029_original : block005_data_flat029 = (CoefficientMerge.scale (99174240 : Int) atom0409Coded) := by
  rw [block005_data_flat029_step]
def block005_data_flat030 : CoefficientMerge.Poly := [(nat_lit 803, Int.ofNat (nat_lit 36201600)), (nat_lit 804, Int.ofNat (nat_lit 99174240))]
theorem block005_data_flat030_step : block005_data_flat030 = (CoefficientMerge.fastMerge block005_data_flat028 block005_data_flat029) := by decide +kernel
theorem block005_data_flat030_original : block005_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36201600 : Int) atom0408Coded) (CoefficientMerge.scale (99174240 : Int) atom0409Coded)) := by
  rw [block005_data_flat030_step, block005_data_flat028_original, block005_data_flat029_original]
def block005_data_flat031 : CoefficientMerge.Poly := [(nat_lit 805, Int.ofNat (nat_lit 78505200))]
theorem block005_data_flat031_step : block005_data_flat031 = (CoefficientMerge.scale (78505200 : Int) atom0410Coded) := by decide +kernel
theorem block005_data_flat031_original : block005_data_flat031 = (CoefficientMerge.scale (78505200 : Int) atom0410Coded) := by
  rw [block005_data_flat031_step]
def block005_data_flat032 : CoefficientMerge.Poly := [(nat_lit 806, Int.ofNat (nat_lit 104116320))]
theorem block005_data_flat032_step : block005_data_flat032 = (CoefficientMerge.scale (104116320 : Int) atom0411Coded) := by decide +kernel
theorem block005_data_flat032_original : block005_data_flat032 = (CoefficientMerge.scale (104116320 : Int) atom0411Coded) := by
  rw [block005_data_flat032_step]
def block005_data_flat033 : CoefficientMerge.Poly := [(nat_lit 807, Int.ofNat (nat_lit 105652080))]
theorem block005_data_flat033_step : block005_data_flat033 = (CoefficientMerge.scale (105652080 : Int) atom0412Coded) := by decide +kernel
theorem block005_data_flat033_original : block005_data_flat033 = (CoefficientMerge.scale (105652080 : Int) atom0412Coded) := by
  rw [block005_data_flat033_step]
def block005_data_flat034 : CoefficientMerge.Poly := [(nat_lit 806, Int.ofNat (nat_lit 104116320)), (nat_lit 807, Int.ofNat (nat_lit 105652080))]
theorem block005_data_flat034_step : block005_data_flat034 = (CoefficientMerge.fastMerge block005_data_flat032 block005_data_flat033) := by decide +kernel
theorem block005_data_flat034_original : block005_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (104116320 : Int) atom0411Coded) (CoefficientMerge.scale (105652080 : Int) atom0412Coded)) := by
  rw [block005_data_flat034_step, block005_data_flat032_original, block005_data_flat033_original]
def block005_data_flat035 : CoefficientMerge.Poly := [(nat_lit 805, Int.ofNat (nat_lit 78505200)), (nat_lit 806, Int.ofNat (nat_lit 104116320)), (nat_lit 807, Int.ofNat (nat_lit 105652080))]
theorem block005_data_flat035_step : block005_data_flat035 = (CoefficientMerge.fastMerge block005_data_flat031 block005_data_flat034) := by decide +kernel
theorem block005_data_flat035_original : block005_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (78505200 : Int) atom0410Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104116320 : Int) atom0411Coded) (CoefficientMerge.scale (105652080 : Int) atom0412Coded))) := by
  rw [block005_data_flat035_step, block005_data_flat031_original, block005_data_flat034_original]
def block005_data_flat036 : CoefficientMerge.Poly := [(nat_lit 803, Int.ofNat (nat_lit 36201600)), (nat_lit 804, Int.ofNat (nat_lit 99174240)), (nat_lit 805, Int.ofNat (nat_lit 78505200)), (nat_lit 806, Int.ofNat (nat_lit 104116320)), (nat_lit 807, Int.ofNat (nat_lit 105652080))]
theorem block005_data_flat036_step : block005_data_flat036 = (CoefficientMerge.fastMerge block005_data_flat030 block005_data_flat035) := by decide +kernel
theorem block005_data_flat036_original : block005_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36201600 : Int) atom0408Coded) (CoefficientMerge.scale (99174240 : Int) atom0409Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (78505200 : Int) atom0410Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104116320 : Int) atom0411Coded) (CoefficientMerge.scale (105652080 : Int) atom0412Coded)))) := by
  rw [block005_data_flat036_step, block005_data_flat030_original, block005_data_flat035_original]
def block005_data_flat037 : CoefficientMerge.Poly := [(nat_lit 790, Int.ofNat (nat_lit 64683600)), (nat_lit 791, Int.ofNat (nat_lit 87060960)), (nat_lit 792, Int.ofNat (nat_lit 89438640)), (nat_lit 793, Int.ofNat (nat_lit 105904560)), (nat_lit 794, Int.ofNat (nat_lit 122426640)), (nat_lit 803, Int.ofNat (nat_lit 36201600)), (nat_lit 804, Int.ofNat (nat_lit 99174240)), (nat_lit 805, Int.ofNat (nat_lit 78505200)), (nat_lit 806, Int.ofNat (nat_lit 104116320)), (nat_lit 807, Int.ofNat (nat_lit 105652080))]
theorem block005_data_flat037_step : block005_data_flat037 = (CoefficientMerge.fastMerge block005_data_flat027 block005_data_flat036) := by decide +kernel
theorem block005_data_flat037_original : block005_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64683600 : Int) atom0403Coded) (CoefficientMerge.scale (87060960 : Int) atom0404Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89438640 : Int) atom0405Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105904560 : Int) atom0406Coded) (CoefficientMerge.scale (122426640 : Int) atom0407Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36201600 : Int) atom0408Coded) (CoefficientMerge.scale (99174240 : Int) atom0409Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (78505200 : Int) atom0410Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104116320 : Int) atom0411Coded) (CoefficientMerge.scale (105652080 : Int) atom0412Coded))))) := by
  rw [block005_data_flat037_step, block005_data_flat027_original, block005_data_flat036_original]
def block005_data_flat038 : CoefficientMerge.Poly := [(nat_lit 773, Int.ofNat (nat_lit 35700480)), (nat_lit 774, Int.ofNat (nat_lit 72161280)), (nat_lit 775, Int.ofNat (nat_lit 50591520)), (nat_lit 776, Int.ofNat (nat_lit 70005600)), (nat_lit 777, Int.ofNat (nat_lit 76122720)), (nat_lit 778, Int.ofNat (nat_lit 92435040)), (nat_lit 779, Int.ofNat (nat_lit 108747360)), (nat_lit 787, Int.ofNat (nat_lit 25864320)), (nat_lit 788, Int.ofNat (nat_lit 52137600)), (nat_lit 789, Int.ofNat (nat_lit 82087680)), (nat_lit 790, Int.ofNat (nat_lit 64683600)), (nat_lit 791, Int.ofNat (nat_lit 87060960)), (nat_lit 792, Int.ofNat (nat_lit 89438640)), (nat_lit 793, Int.ofNat (nat_lit 105904560)), (nat_lit 794, Int.ofNat (nat_lit 122426640)), (nat_lit 803, Int.ofNat (nat_lit 36201600)), (nat_lit 804, Int.ofNat (nat_lit 99174240)), (nat_lit 805, Int.ofNat (nat_lit 78505200)), (nat_lit 806, Int.ofNat (nat_lit 104116320)), (nat_lit 807, Int.ofNat (nat_lit 105652080))]
theorem block005_data_flat038_step : block005_data_flat038 = (CoefficientMerge.fastMerge block005_data_flat018 block005_data_flat037) := by decide +kernel
theorem block005_data_flat038_original : block005_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35700480 : Int) atom0393Coded) (CoefficientMerge.scale (72161280 : Int) atom0394Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50591520 : Int) atom0395Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70005600 : Int) atom0396Coded) (CoefficientMerge.scale (76122720 : Int) atom0397Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (92435040 : Int) atom0398Coded) (CoefficientMerge.scale (108747360 : Int) atom0399Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25864320 : Int) atom0400Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52137600 : Int) atom0401Coded) (CoefficientMerge.scale (82087680 : Int) atom0402Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64683600 : Int) atom0403Coded) (CoefficientMerge.scale (87060960 : Int) atom0404Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89438640 : Int) atom0405Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105904560 : Int) atom0406Coded) (CoefficientMerge.scale (122426640 : Int) atom0407Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36201600 : Int) atom0408Coded) (CoefficientMerge.scale (99174240 : Int) atom0409Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (78505200 : Int) atom0410Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104116320 : Int) atom0411Coded) (CoefficientMerge.scale (105652080 : Int) atom0412Coded)))))) := by
  rw [block005_data_flat038_step, block005_data_flat018_original, block005_data_flat037_original]
def block005_data_flat039 : CoefficientMerge.Poly := [(nat_lit 808, Int.ofNat (nat_lit 109812240))]
theorem block005_data_flat039_step : block005_data_flat039 = (CoefficientMerge.scale (109812240 : Int) atom0413Coded) := by decide +kernel
theorem block005_data_flat039_original : block005_data_flat039 = (CoefficientMerge.scale (109812240 : Int) atom0413Coded) := by
  rw [block005_data_flat039_step]
def block005_data_flat040 : CoefficientMerge.Poly := [(nat_lit 809, Int.ofNat (nat_lit 153509040))]
theorem block005_data_flat040_step : block005_data_flat040 = (CoefficientMerge.scale (153509040 : Int) atom0414Coded) := by decide +kernel
theorem block005_data_flat040_original : block005_data_flat040 = (CoefficientMerge.scale (153509040 : Int) atom0414Coded) := by
  rw [block005_data_flat040_step]
def block005_data_flat041 : CoefficientMerge.Poly := [(nat_lit 808, Int.ofNat (nat_lit 109812240)), (nat_lit 809, Int.ofNat (nat_lit 153509040))]
theorem block005_data_flat041_step : block005_data_flat041 = (CoefficientMerge.fastMerge block005_data_flat039 block005_data_flat040) := by decide +kernel
theorem block005_data_flat041_original : block005_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (109812240 : Int) atom0413Coded) (CoefficientMerge.scale (153509040 : Int) atom0414Coded)) := by
  rw [block005_data_flat041_step, block005_data_flat039_original, block005_data_flat040_original]
def block005_data_flat042 : CoefficientMerge.Poly := [(nat_lit 819, Int.ofNat (nat_lit 74908800))]
theorem block005_data_flat042_step : block005_data_flat042 = (CoefficientMerge.scale (74908800 : Int) atom0415Coded) := by decide +kernel
theorem block005_data_flat042_original : block005_data_flat042 = (CoefficientMerge.scale (74908800 : Int) atom0415Coded) := by
  rw [block005_data_flat042_step]
def block005_data_flat043 : CoefficientMerge.Poly := [(nat_lit 820, Int.ofNat (nat_lit 124263720))]
theorem block005_data_flat043_step : block005_data_flat043 = (CoefficientMerge.scale (124263720 : Int) atom0416Coded) := by decide +kernel
theorem block005_data_flat043_original : block005_data_flat043 = (CoefficientMerge.scale (124263720 : Int) atom0416Coded) := by
  rw [block005_data_flat043_step]
def block005_data_flat044 : CoefficientMerge.Poly := [(nat_lit 821, Int.ofNat (nat_lit 176277600))]
theorem block005_data_flat044_step : block005_data_flat044 = (CoefficientMerge.scale (176277600 : Int) atom0417Coded) := by decide +kernel
theorem block005_data_flat044_original : block005_data_flat044 = (CoefficientMerge.scale (176277600 : Int) atom0417Coded) := by
  rw [block005_data_flat044_step]
def block005_data_flat045 : CoefficientMerge.Poly := [(nat_lit 820, Int.ofNat (nat_lit 124263720)), (nat_lit 821, Int.ofNat (nat_lit 176277600))]
theorem block005_data_flat045_step : block005_data_flat045 = (CoefficientMerge.fastMerge block005_data_flat043 block005_data_flat044) := by decide +kernel
theorem block005_data_flat045_original : block005_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (124263720 : Int) atom0416Coded) (CoefficientMerge.scale (176277600 : Int) atom0417Coded)) := by
  rw [block005_data_flat045_step, block005_data_flat043_original, block005_data_flat044_original]
def block005_data_flat046 : CoefficientMerge.Poly := [(nat_lit 819, Int.ofNat (nat_lit 74908800)), (nat_lit 820, Int.ofNat (nat_lit 124263720)), (nat_lit 821, Int.ofNat (nat_lit 176277600))]
theorem block005_data_flat046_step : block005_data_flat046 = (CoefficientMerge.fastMerge block005_data_flat042 block005_data_flat045) := by decide +kernel
theorem block005_data_flat046_original : block005_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (74908800 : Int) atom0415Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (124263720 : Int) atom0416Coded) (CoefficientMerge.scale (176277600 : Int) atom0417Coded))) := by
  rw [block005_data_flat046_step, block005_data_flat042_original, block005_data_flat045_original]
def block005_data_flat047 : CoefficientMerge.Poly := [(nat_lit 808, Int.ofNat (nat_lit 109812240)), (nat_lit 809, Int.ofNat (nat_lit 153509040)), (nat_lit 819, Int.ofNat (nat_lit 74908800)), (nat_lit 820, Int.ofNat (nat_lit 124263720)), (nat_lit 821, Int.ofNat (nat_lit 176277600))]
theorem block005_data_flat047_step : block005_data_flat047 = (CoefficientMerge.fastMerge block005_data_flat041 block005_data_flat046) := by decide +kernel
theorem block005_data_flat047_original : block005_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (109812240 : Int) atom0413Coded) (CoefficientMerge.scale (153509040 : Int) atom0414Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74908800 : Int) atom0415Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (124263720 : Int) atom0416Coded) (CoefficientMerge.scale (176277600 : Int) atom0417Coded)))) := by
  rw [block005_data_flat047_step, block005_data_flat041_original, block005_data_flat046_original]
def block005_data_flat048 : CoefficientMerge.Poly := [(nat_lit 822, Int.ofNat (nat_lit 180672120))]
theorem block005_data_flat048_step : block005_data_flat048 = (CoefficientMerge.scale (180672120 : Int) atom0418Coded) := by decide +kernel
theorem block005_data_flat048_original : block005_data_flat048 = (CoefficientMerge.scale (180672120 : Int) atom0418Coded) := by
  rw [block005_data_flat048_step]
def block005_data_flat049 : CoefficientMerge.Poly := [(nat_lit 823, Int.ofNat (nat_lit 113707800))]
theorem block005_data_flat049_step : block005_data_flat049 = (CoefficientMerge.scale (113707800 : Int) atom0419Coded) := by decide +kernel
theorem block005_data_flat049_original : block005_data_flat049 = (CoefficientMerge.scale (113707800 : Int) atom0419Coded) := by
  rw [block005_data_flat049_step]
def block005_data_flat050 : CoefficientMerge.Poly := [(nat_lit 822, Int.ofNat (nat_lit 180672120)), (nat_lit 823, Int.ofNat (nat_lit 113707800))]
theorem block005_data_flat050_step : block005_data_flat050 = (CoefficientMerge.fastMerge block005_data_flat048 block005_data_flat049) := by decide +kernel
theorem block005_data_flat050_original : block005_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (180672120 : Int) atom0418Coded) (CoefficientMerge.scale (113707800 : Int) atom0419Coded)) := by
  rw [block005_data_flat050_step, block005_data_flat048_original, block005_data_flat049_original]
def block005_data_flat051 : CoefficientMerge.Poly := [(nat_lit 824, Int.ofNat (nat_lit 182823480))]
theorem block005_data_flat051_step : block005_data_flat051 = (CoefficientMerge.scale (182823480 : Int) atom0420Coded) := by decide +kernel
theorem block005_data_flat051_original : block005_data_flat051 = (CoefficientMerge.scale (182823480 : Int) atom0420Coded) := by
  rw [block005_data_flat051_step]
def block005_data_flat052 : CoefficientMerge.Poly := [(nat_lit 835, Int.ofNat (nat_lit 57262464))]
theorem block005_data_flat052_step : block005_data_flat052 = (CoefficientMerge.scale (57262464 : Int) atom0421Coded) := by decide +kernel
theorem block005_data_flat052_original : block005_data_flat052 = (CoefficientMerge.scale (57262464 : Int) atom0421Coded) := by
  rw [block005_data_flat052_step]
def block005_data_flat053 : CoefficientMerge.Poly := [(nat_lit 836, Int.ofNat (nat_lit 145208160))]
theorem block005_data_flat053_step : block005_data_flat053 = (CoefficientMerge.scale (145208160 : Int) atom0422Coded) := by decide +kernel
theorem block005_data_flat053_original : block005_data_flat053 = (CoefficientMerge.scale (145208160 : Int) atom0422Coded) := by
  rw [block005_data_flat053_step]
def block005_data_flat054 : CoefficientMerge.Poly := [(nat_lit 835, Int.ofNat (nat_lit 57262464)), (nat_lit 836, Int.ofNat (nat_lit 145208160))]
theorem block005_data_flat054_step : block005_data_flat054 = (CoefficientMerge.fastMerge block005_data_flat052 block005_data_flat053) := by decide +kernel
theorem block005_data_flat054_original : block005_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (57262464 : Int) atom0421Coded) (CoefficientMerge.scale (145208160 : Int) atom0422Coded)) := by
  rw [block005_data_flat054_step, block005_data_flat052_original, block005_data_flat053_original]
def block005_data_flat055 : CoefficientMerge.Poly := [(nat_lit 824, Int.ofNat (nat_lit 182823480)), (nat_lit 835, Int.ofNat (nat_lit 57262464)), (nat_lit 836, Int.ofNat (nat_lit 145208160))]
theorem block005_data_flat055_step : block005_data_flat055 = (CoefficientMerge.fastMerge block005_data_flat051 block005_data_flat054) := by decide +kernel
theorem block005_data_flat055_original : block005_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (182823480 : Int) atom0420Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57262464 : Int) atom0421Coded) (CoefficientMerge.scale (145208160 : Int) atom0422Coded))) := by
  rw [block005_data_flat055_step, block005_data_flat051_original, block005_data_flat054_original]
def block005_data_flat056 : CoefficientMerge.Poly := [(nat_lit 822, Int.ofNat (nat_lit 180672120)), (nat_lit 823, Int.ofNat (nat_lit 113707800)), (nat_lit 824, Int.ofNat (nat_lit 182823480)), (nat_lit 835, Int.ofNat (nat_lit 57262464)), (nat_lit 836, Int.ofNat (nat_lit 145208160))]
theorem block005_data_flat056_step : block005_data_flat056 = (CoefficientMerge.fastMerge block005_data_flat050 block005_data_flat055) := by decide +kernel
theorem block005_data_flat056_original : block005_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (180672120 : Int) atom0418Coded) (CoefficientMerge.scale (113707800 : Int) atom0419Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182823480 : Int) atom0420Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57262464 : Int) atom0421Coded) (CoefficientMerge.scale (145208160 : Int) atom0422Coded)))) := by
  rw [block005_data_flat056_step, block005_data_flat050_original, block005_data_flat055_original]
def block005_data_flat057 : CoefficientMerge.Poly := [(nat_lit 808, Int.ofNat (nat_lit 109812240)), (nat_lit 809, Int.ofNat (nat_lit 153509040)), (nat_lit 819, Int.ofNat (nat_lit 74908800)), (nat_lit 820, Int.ofNat (nat_lit 124263720)), (nat_lit 821, Int.ofNat (nat_lit 176277600)), (nat_lit 822, Int.ofNat (nat_lit 180672120)), (nat_lit 823, Int.ofNat (nat_lit 113707800)), (nat_lit 824, Int.ofNat (nat_lit 182823480)), (nat_lit 835, Int.ofNat (nat_lit 57262464)), (nat_lit 836, Int.ofNat (nat_lit 145208160))]
theorem block005_data_flat057_step : block005_data_flat057 = (CoefficientMerge.fastMerge block005_data_flat047 block005_data_flat056) := by decide +kernel
theorem block005_data_flat057_original : block005_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (109812240 : Int) atom0413Coded) (CoefficientMerge.scale (153509040 : Int) atom0414Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74908800 : Int) atom0415Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (124263720 : Int) atom0416Coded) (CoefficientMerge.scale (176277600 : Int) atom0417Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (180672120 : Int) atom0418Coded) (CoefficientMerge.scale (113707800 : Int) atom0419Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182823480 : Int) atom0420Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57262464 : Int) atom0421Coded) (CoefficientMerge.scale (145208160 : Int) atom0422Coded))))) := by
  rw [block005_data_flat057_step, block005_data_flat047_original, block005_data_flat056_original]
def block005_data_flat058 : CoefficientMerge.Poly := [(nat_lit 837, Int.ofNat (nat_lit 171628740))]
theorem block005_data_flat058_step : block005_data_flat058 = (CoefficientMerge.scale (171628740 : Int) atom0423Coded) := by decide +kernel
theorem block005_data_flat058_original : block005_data_flat058 = (CoefficientMerge.scale (171628740 : Int) atom0423Coded) := by
  rw [block005_data_flat058_step]
def block005_data_flat059 : CoefficientMerge.Poly := [(nat_lit 838, Int.ofNat (nat_lit 121886640))]
theorem block005_data_flat059_step : block005_data_flat059 = (CoefficientMerge.scale (121886640 : Int) atom0424Coded) := by decide +kernel
theorem block005_data_flat059_original : block005_data_flat059 = (CoefficientMerge.scale (121886640 : Int) atom0424Coded) := by
  rw [block005_data_flat059_step]
def block005_data_flat060 : CoefficientMerge.Poly := [(nat_lit 837, Int.ofNat (nat_lit 171628740)), (nat_lit 838, Int.ofNat (nat_lit 121886640))]
theorem block005_data_flat060_step : block005_data_flat060 = (CoefficientMerge.fastMerge block005_data_flat058 block005_data_flat059) := by decide +kernel
theorem block005_data_flat060_original : block005_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (171628740 : Int) atom0423Coded) (CoefficientMerge.scale (121886640 : Int) atom0424Coded)) := by
  rw [block005_data_flat060_step, block005_data_flat058_original, block005_data_flat059_original]
def block005_data_flat061 : CoefficientMerge.Poly := [(nat_lit 839, Int.ofNat (nat_lit 154082790))]
theorem block005_data_flat061_step : block005_data_flat061 = (CoefficientMerge.scale (154082790 : Int) atom0425Coded) := by decide +kernel
theorem block005_data_flat061_original : block005_data_flat061 = (CoefficientMerge.scale (154082790 : Int) atom0425Coded) := by
  rw [block005_data_flat061_step]
def block005_data_flat062 : CoefficientMerge.Poly := [(nat_lit 851, Int.ofNat (nat_lit 98175240))]
theorem block005_data_flat062_step : block005_data_flat062 = (CoefficientMerge.scale (98175240 : Int) atom0426Coded) := by decide +kernel
theorem block005_data_flat062_original : block005_data_flat062 = (CoefficientMerge.scale (98175240 : Int) atom0426Coded) := by
  rw [block005_data_flat062_step]
def block005_data_flat063 : CoefficientMerge.Poly := [(nat_lit 852, Int.ofNat (nat_lit 171553680))]
theorem block005_data_flat063_step : block005_data_flat063 = (CoefficientMerge.scale (171553680 : Int) atom0427Coded) := by decide +kernel
theorem block005_data_flat063_original : block005_data_flat063 = (CoefficientMerge.scale (171553680 : Int) atom0427Coded) := by
  rw [block005_data_flat063_step]
def block005_data_flat064 : CoefficientMerge.Poly := [(nat_lit 851, Int.ofNat (nat_lit 98175240)), (nat_lit 852, Int.ofNat (nat_lit 171553680))]
theorem block005_data_flat064_step : block005_data_flat064 = (CoefficientMerge.fastMerge block005_data_flat062 block005_data_flat063) := by decide +kernel
theorem block005_data_flat064_original : block005_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (98175240 : Int) atom0426Coded) (CoefficientMerge.scale (171553680 : Int) atom0427Coded)) := by
  rw [block005_data_flat064_step, block005_data_flat062_original, block005_data_flat063_original]
def block005_data_flat065 : CoefficientMerge.Poly := [(nat_lit 839, Int.ofNat (nat_lit 154082790)), (nat_lit 851, Int.ofNat (nat_lit 98175240)), (nat_lit 852, Int.ofNat (nat_lit 171553680))]
theorem block005_data_flat065_step : block005_data_flat065 = (CoefficientMerge.fastMerge block005_data_flat061 block005_data_flat064) := by decide +kernel
theorem block005_data_flat065_original : block005_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (154082790 : Int) atom0425Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98175240 : Int) atom0426Coded) (CoefficientMerge.scale (171553680 : Int) atom0427Coded))) := by
  rw [block005_data_flat065_step, block005_data_flat061_original, block005_data_flat064_original]
def block005_data_flat066 : CoefficientMerge.Poly := [(nat_lit 837, Int.ofNat (nat_lit 171628740)), (nat_lit 838, Int.ofNat (nat_lit 121886640)), (nat_lit 839, Int.ofNat (nat_lit 154082790)), (nat_lit 851, Int.ofNat (nat_lit 98175240)), (nat_lit 852, Int.ofNat (nat_lit 171553680))]
theorem block005_data_flat066_step : block005_data_flat066 = (CoefficientMerge.fastMerge block005_data_flat060 block005_data_flat065) := by decide +kernel
theorem block005_data_flat066_original : block005_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (171628740 : Int) atom0423Coded) (CoefficientMerge.scale (121886640 : Int) atom0424Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154082790 : Int) atom0425Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98175240 : Int) atom0426Coded) (CoefficientMerge.scale (171553680 : Int) atom0427Coded)))) := by
  rw [block005_data_flat066_step, block005_data_flat060_original, block005_data_flat065_original]
def block005_data_flat067 : CoefficientMerge.Poly := [(nat_lit 853, Int.ofNat (nat_lit 120222360))]
theorem block005_data_flat067_step : block005_data_flat067 = (CoefficientMerge.scale (120222360 : Int) atom0428Coded) := by decide +kernel
theorem block005_data_flat067_original : block005_data_flat067 = (CoefficientMerge.scale (120222360 : Int) atom0428Coded) := by
  rw [block005_data_flat067_step]
def block005_data_flat068 : CoefficientMerge.Poly := [(nat_lit 854, Int.ofNat (nat_lit 170511480))]
theorem block005_data_flat068_step : block005_data_flat068 = (CoefficientMerge.scale (170511480 : Int) atom0429Coded) := by decide +kernel
theorem block005_data_flat068_original : block005_data_flat068 = (CoefficientMerge.scale (170511480 : Int) atom0429Coded) := by
  rw [block005_data_flat068_step]
def block005_data_flat069 : CoefficientMerge.Poly := [(nat_lit 853, Int.ofNat (nat_lit 120222360)), (nat_lit 854, Int.ofNat (nat_lit 170511480))]
theorem block005_data_flat069_step : block005_data_flat069 = (CoefficientMerge.fastMerge block005_data_flat067 block005_data_flat068) := by decide +kernel
theorem block005_data_flat069_original : block005_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (120222360 : Int) atom0428Coded) (CoefficientMerge.scale (170511480 : Int) atom0429Coded)) := by
  rw [block005_data_flat069_step, block005_data_flat067_original, block005_data_flat068_original]
def block005_data_flat070 : CoefficientMerge.Poly := [(nat_lit 867, Int.ofNat (nat_lit 64707660))]
theorem block005_data_flat070_step : block005_data_flat070 = (CoefficientMerge.scale (64707660 : Int) atom0430Coded) := by decide +kernel
theorem block005_data_flat070_original : block005_data_flat070 = (CoefficientMerge.scale (64707660 : Int) atom0430Coded) := by
  rw [block005_data_flat070_step]
def block005_data_flat071 : CoefficientMerge.Poly := [(nat_lit 868, Int.ofNat (nat_lit 94666860))]
theorem block005_data_flat071_step : block005_data_flat071 = (CoefficientMerge.scale (94666860 : Int) atom0431Coded) := by decide +kernel
theorem block005_data_flat071_original : block005_data_flat071 = (CoefficientMerge.scale (94666860 : Int) atom0431Coded) := by
  rw [block005_data_flat071_step]
def block005_data_flat072 : CoefficientMerge.Poly := [(nat_lit 869, Int.ofNat (nat_lit 155708190))]
theorem block005_data_flat072_step : block005_data_flat072 = (CoefficientMerge.scale (155708190 : Int) atom0432Coded) := by decide +kernel
theorem block005_data_flat072_original : block005_data_flat072 = (CoefficientMerge.scale (155708190 : Int) atom0432Coded) := by
  rw [block005_data_flat072_step]
def block005_data_flat073 : CoefficientMerge.Poly := [(nat_lit 868, Int.ofNat (nat_lit 94666860)), (nat_lit 869, Int.ofNat (nat_lit 155708190))]
theorem block005_data_flat073_step : block005_data_flat073 = (CoefficientMerge.fastMerge block005_data_flat071 block005_data_flat072) := by decide +kernel
theorem block005_data_flat073_original : block005_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (94666860 : Int) atom0431Coded) (CoefficientMerge.scale (155708190 : Int) atom0432Coded)) := by
  rw [block005_data_flat073_step, block005_data_flat071_original, block005_data_flat072_original]
def block005_data_flat074 : CoefficientMerge.Poly := [(nat_lit 867, Int.ofNat (nat_lit 64707660)), (nat_lit 868, Int.ofNat (nat_lit 94666860)), (nat_lit 869, Int.ofNat (nat_lit 155708190))]
theorem block005_data_flat074_step : block005_data_flat074 = (CoefficientMerge.fastMerge block005_data_flat070 block005_data_flat073) := by decide +kernel
theorem block005_data_flat074_original : block005_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (64707660 : Int) atom0430Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94666860 : Int) atom0431Coded) (CoefficientMerge.scale (155708190 : Int) atom0432Coded))) := by
  rw [block005_data_flat074_step, block005_data_flat070_original, block005_data_flat073_original]
def block005_data_flat075 : CoefficientMerge.Poly := [(nat_lit 853, Int.ofNat (nat_lit 120222360)), (nat_lit 854, Int.ofNat (nat_lit 170511480)), (nat_lit 867, Int.ofNat (nat_lit 64707660)), (nat_lit 868, Int.ofNat (nat_lit 94666860)), (nat_lit 869, Int.ofNat (nat_lit 155708190))]
theorem block005_data_flat075_step : block005_data_flat075 = (CoefficientMerge.fastMerge block005_data_flat069 block005_data_flat074) := by decide +kernel
theorem block005_data_flat075_original : block005_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120222360 : Int) atom0428Coded) (CoefficientMerge.scale (170511480 : Int) atom0429Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64707660 : Int) atom0430Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94666860 : Int) atom0431Coded) (CoefficientMerge.scale (155708190 : Int) atom0432Coded)))) := by
  rw [block005_data_flat075_step, block005_data_flat069_original, block005_data_flat074_original]
def block005_data_flat076 : CoefficientMerge.Poly := [(nat_lit 837, Int.ofNat (nat_lit 171628740)), (nat_lit 838, Int.ofNat (nat_lit 121886640)), (nat_lit 839, Int.ofNat (nat_lit 154082790)), (nat_lit 851, Int.ofNat (nat_lit 98175240)), (nat_lit 852, Int.ofNat (nat_lit 171553680)), (nat_lit 853, Int.ofNat (nat_lit 120222360)), (nat_lit 854, Int.ofNat (nat_lit 170511480)), (nat_lit 867, Int.ofNat (nat_lit 64707660)), (nat_lit 868, Int.ofNat (nat_lit 94666860)), (nat_lit 869, Int.ofNat (nat_lit 155708190))]
theorem block005_data_flat076_step : block005_data_flat076 = (CoefficientMerge.fastMerge block005_data_flat066 block005_data_flat075) := by decide +kernel
theorem block005_data_flat076_original : block005_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (171628740 : Int) atom0423Coded) (CoefficientMerge.scale (121886640 : Int) atom0424Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154082790 : Int) atom0425Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98175240 : Int) atom0426Coded) (CoefficientMerge.scale (171553680 : Int) atom0427Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120222360 : Int) atom0428Coded) (CoefficientMerge.scale (170511480 : Int) atom0429Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64707660 : Int) atom0430Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94666860 : Int) atom0431Coded) (CoefficientMerge.scale (155708190 : Int) atom0432Coded))))) := by
  rw [block005_data_flat076_step, block005_data_flat066_original, block005_data_flat075_original]
def block005_data_flat077 : CoefficientMerge.Poly := [(nat_lit 808, Int.ofNat (nat_lit 109812240)), (nat_lit 809, Int.ofNat (nat_lit 153509040)), (nat_lit 819, Int.ofNat (nat_lit 74908800)), (nat_lit 820, Int.ofNat (nat_lit 124263720)), (nat_lit 821, Int.ofNat (nat_lit 176277600)), (nat_lit 822, Int.ofNat (nat_lit 180672120)), (nat_lit 823, Int.ofNat (nat_lit 113707800)), (nat_lit 824, Int.ofNat (nat_lit 182823480)), (nat_lit 835, Int.ofNat (nat_lit 57262464)), (nat_lit 836, Int.ofNat (nat_lit 145208160)), (nat_lit 837, Int.ofNat (nat_lit 171628740)), (nat_lit 838, Int.ofNat (nat_lit 121886640)), (nat_lit 839, Int.ofNat (nat_lit 154082790)), (nat_lit 851, Int.ofNat (nat_lit 98175240)), (nat_lit 852, Int.ofNat (nat_lit 171553680)), (nat_lit 853, Int.ofNat (nat_lit 120222360)), (nat_lit 854, Int.ofNat (nat_lit 170511480)), (nat_lit 867, Int.ofNat (nat_lit 64707660)), (nat_lit 868, Int.ofNat (nat_lit 94666860)), (nat_lit 869, Int.ofNat (nat_lit 155708190))]
theorem block005_data_flat077_step : block005_data_flat077 = (CoefficientMerge.fastMerge block005_data_flat057 block005_data_flat076) := by decide +kernel
theorem block005_data_flat077_original : block005_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (109812240 : Int) atom0413Coded) (CoefficientMerge.scale (153509040 : Int) atom0414Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74908800 : Int) atom0415Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (124263720 : Int) atom0416Coded) (CoefficientMerge.scale (176277600 : Int) atom0417Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (180672120 : Int) atom0418Coded) (CoefficientMerge.scale (113707800 : Int) atom0419Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182823480 : Int) atom0420Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57262464 : Int) atom0421Coded) (CoefficientMerge.scale (145208160 : Int) atom0422Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (171628740 : Int) atom0423Coded) (CoefficientMerge.scale (121886640 : Int) atom0424Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154082790 : Int) atom0425Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98175240 : Int) atom0426Coded) (CoefficientMerge.scale (171553680 : Int) atom0427Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120222360 : Int) atom0428Coded) (CoefficientMerge.scale (170511480 : Int) atom0429Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64707660 : Int) atom0430Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94666860 : Int) atom0431Coded) (CoefficientMerge.scale (155708190 : Int) atom0432Coded)))))) := by
  rw [block005_data_flat077_step, block005_data_flat057_original, block005_data_flat076_original]
def block005_data_flat078 : CoefficientMerge.Poly := [(nat_lit 773, Int.ofNat (nat_lit 35700480)), (nat_lit 774, Int.ofNat (nat_lit 72161280)), (nat_lit 775, Int.ofNat (nat_lit 50591520)), (nat_lit 776, Int.ofNat (nat_lit 70005600)), (nat_lit 777, Int.ofNat (nat_lit 76122720)), (nat_lit 778, Int.ofNat (nat_lit 92435040)), (nat_lit 779, Int.ofNat (nat_lit 108747360)), (nat_lit 787, Int.ofNat (nat_lit 25864320)), (nat_lit 788, Int.ofNat (nat_lit 52137600)), (nat_lit 789, Int.ofNat (nat_lit 82087680)), (nat_lit 790, Int.ofNat (nat_lit 64683600)), (nat_lit 791, Int.ofNat (nat_lit 87060960)), (nat_lit 792, Int.ofNat (nat_lit 89438640)), (nat_lit 793, Int.ofNat (nat_lit 105904560)), (nat_lit 794, Int.ofNat (nat_lit 122426640)), (nat_lit 803, Int.ofNat (nat_lit 36201600)), (nat_lit 804, Int.ofNat (nat_lit 99174240)), (nat_lit 805, Int.ofNat (nat_lit 78505200)), (nat_lit 806, Int.ofNat (nat_lit 104116320)), (nat_lit 807, Int.ofNat (nat_lit 105652080)), (nat_lit 808, Int.ofNat (nat_lit 109812240)), (nat_lit 809, Int.ofNat (nat_lit 153509040)), (nat_lit 819, Int.ofNat (nat_lit 74908800)), (nat_lit 820, Int.ofNat (nat_lit 124263720)), (nat_lit 821, Int.ofNat (nat_lit 176277600)), (nat_lit 822, Int.ofNat (nat_lit 180672120)), (nat_lit 823, Int.ofNat (nat_lit 113707800)), (nat_lit 824, Int.ofNat (nat_lit 182823480)), (nat_lit 835, Int.ofNat (nat_lit 57262464)), (nat_lit 836, Int.ofNat (nat_lit 145208160)), (nat_lit 837, Int.ofNat (nat_lit 171628740)), (nat_lit 838, Int.ofNat (nat_lit 121886640)), (nat_lit 839, Int.ofNat (nat_lit 154082790)), (nat_lit 851, Int.ofNat (nat_lit 98175240)), (nat_lit 852, Int.ofNat (nat_lit 171553680)), (nat_lit 853, Int.ofNat (nat_lit 120222360)), (nat_lit 854, Int.ofNat (nat_lit 170511480)), (nat_lit 867, Int.ofNat (nat_lit 64707660)), (nat_lit 868, Int.ofNat (nat_lit 94666860)), (nat_lit 869, Int.ofNat (nat_lit 155708190))]
theorem block005_data_flat078_step : block005_data_flat078 = (CoefficientMerge.fastMerge block005_data_flat038 block005_data_flat077) := by decide +kernel
theorem block005_data_flat078_original : block005_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35700480 : Int) atom0393Coded) (CoefficientMerge.scale (72161280 : Int) atom0394Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50591520 : Int) atom0395Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70005600 : Int) atom0396Coded) (CoefficientMerge.scale (76122720 : Int) atom0397Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (92435040 : Int) atom0398Coded) (CoefficientMerge.scale (108747360 : Int) atom0399Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25864320 : Int) atom0400Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52137600 : Int) atom0401Coded) (CoefficientMerge.scale (82087680 : Int) atom0402Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64683600 : Int) atom0403Coded) (CoefficientMerge.scale (87060960 : Int) atom0404Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89438640 : Int) atom0405Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105904560 : Int) atom0406Coded) (CoefficientMerge.scale (122426640 : Int) atom0407Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36201600 : Int) atom0408Coded) (CoefficientMerge.scale (99174240 : Int) atom0409Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (78505200 : Int) atom0410Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104116320 : Int) atom0411Coded) (CoefficientMerge.scale (105652080 : Int) atom0412Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (109812240 : Int) atom0413Coded) (CoefficientMerge.scale (153509040 : Int) atom0414Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74908800 : Int) atom0415Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (124263720 : Int) atom0416Coded) (CoefficientMerge.scale (176277600 : Int) atom0417Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (180672120 : Int) atom0418Coded) (CoefficientMerge.scale (113707800 : Int) atom0419Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182823480 : Int) atom0420Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57262464 : Int) atom0421Coded) (CoefficientMerge.scale (145208160 : Int) atom0422Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (171628740 : Int) atom0423Coded) (CoefficientMerge.scale (121886640 : Int) atom0424Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154082790 : Int) atom0425Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98175240 : Int) atom0426Coded) (CoefficientMerge.scale (171553680 : Int) atom0427Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120222360 : Int) atom0428Coded) (CoefficientMerge.scale (170511480 : Int) atom0429Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64707660 : Int) atom0430Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94666860 : Int) atom0431Coded) (CoefficientMerge.scale (155708190 : Int) atom0432Coded))))))) := by
  rw [block005_data_flat078_step, block005_data_flat038_original, block005_data_flat077_original]
def block005_data_flat079 : CoefficientMerge.Poly := [(nat_lit 883, Int.ofNat (nat_lit 15264720))]
theorem block005_data_flat079_step : block005_data_flat079 = (CoefficientMerge.scale (15264720 : Int) atom0433Coded) := by decide +kernel
theorem block005_data_flat079_original : block005_data_flat079 = (CoefficientMerge.scale (15264720 : Int) atom0433Coded) := by
  rw [block005_data_flat079_step]
def block005_data_flat080 : CoefficientMerge.Poly := [(nat_lit 884, Int.ofNat (nat_lit 99311130))]
theorem block005_data_flat080_step : block005_data_flat080 = (CoefficientMerge.scale (99311130 : Int) atom0434Coded) := by decide +kernel
theorem block005_data_flat080_original : block005_data_flat080 = (CoefficientMerge.scale (99311130 : Int) atom0434Coded) := by
  rw [block005_data_flat080_step]
def block005_data_flat081 : CoefficientMerge.Poly := [(nat_lit 883, Int.ofNat (nat_lit 15264720)), (nat_lit 884, Int.ofNat (nat_lit 99311130))]
theorem block005_data_flat081_step : block005_data_flat081 = (CoefficientMerge.fastMerge block005_data_flat079 block005_data_flat080) := by decide +kernel
theorem block005_data_flat081_original : block005_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15264720 : Int) atom0433Coded) (CoefficientMerge.scale (99311130 : Int) atom0434Coded)) := by
  rw [block005_data_flat081_step, block005_data_flat079_original, block005_data_flat080_original]
def block005_data_flat082 : CoefficientMerge.Poly := [(nat_lit 899, Int.ofNat (nat_lit 79701570))]
theorem block005_data_flat082_step : block005_data_flat082 = (CoefficientMerge.scale (79701570 : Int) atom0435Coded) := by decide +kernel
theorem block005_data_flat082_original : block005_data_flat082 = (CoefficientMerge.scale (79701570 : Int) atom0435Coded) := by
  rw [block005_data_flat082_step]
def block005_data_flat083 : CoefficientMerge.Poly := [(nat_lit 964, Int.ofNat (nat_lit 2931840))]
theorem block005_data_flat083_step : block005_data_flat083 = (CoefficientMerge.scale (2931840 : Int) atom0436Coded) := by decide +kernel
theorem block005_data_flat083_original : block005_data_flat083 = (CoefficientMerge.scale (2931840 : Int) atom0436Coded) := by
  rw [block005_data_flat083_step]
def block005_data_flat084 : CoefficientMerge.Poly := [(nat_lit 969, Int.ofNat (nat_lit 19845360))]
theorem block005_data_flat084_step : block005_data_flat084 = (CoefficientMerge.scale (19845360 : Int) atom0437Coded) := by decide +kernel
theorem block005_data_flat084_original : block005_data_flat084 = (CoefficientMerge.scale (19845360 : Int) atom0437Coded) := by
  rw [block005_data_flat084_step]
def block005_data_flat085 : CoefficientMerge.Poly := [(nat_lit 964, Int.ofNat (nat_lit 2931840)), (nat_lit 969, Int.ofNat (nat_lit 19845360))]
theorem block005_data_flat085_step : block005_data_flat085 = (CoefficientMerge.fastMerge block005_data_flat083 block005_data_flat084) := by decide +kernel
theorem block005_data_flat085_original : block005_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2931840 : Int) atom0436Coded) (CoefficientMerge.scale (19845360 : Int) atom0437Coded)) := by
  rw [block005_data_flat085_step, block005_data_flat083_original, block005_data_flat084_original]
def block005_data_flat086 : CoefficientMerge.Poly := [(nat_lit 899, Int.ofNat (nat_lit 79701570)), (nat_lit 964, Int.ofNat (nat_lit 2931840)), (nat_lit 969, Int.ofNat (nat_lit 19845360))]
theorem block005_data_flat086_step : block005_data_flat086 = (CoefficientMerge.fastMerge block005_data_flat082 block005_data_flat085) := by decide +kernel
theorem block005_data_flat086_original : block005_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (79701570 : Int) atom0435Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2931840 : Int) atom0436Coded) (CoefficientMerge.scale (19845360 : Int) atom0437Coded))) := by
  rw [block005_data_flat086_step, block005_data_flat082_original, block005_data_flat085_original]
def block005_data_flat087 : CoefficientMerge.Poly := [(nat_lit 883, Int.ofNat (nat_lit 15264720)), (nat_lit 884, Int.ofNat (nat_lit 99311130)), (nat_lit 899, Int.ofNat (nat_lit 79701570)), (nat_lit 964, Int.ofNat (nat_lit 2931840)), (nat_lit 969, Int.ofNat (nat_lit 19845360))]
theorem block005_data_flat087_step : block005_data_flat087 = (CoefficientMerge.fastMerge block005_data_flat081 block005_data_flat086) := by decide +kernel
theorem block005_data_flat087_original : block005_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15264720 : Int) atom0433Coded) (CoefficientMerge.scale (99311130 : Int) atom0434Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79701570 : Int) atom0435Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2931840 : Int) atom0436Coded) (CoefficientMerge.scale (19845360 : Int) atom0437Coded)))) := by
  rw [block005_data_flat087_step, block005_data_flat081_original, block005_data_flat086_original]
def block005_data_flat088 : CoefficientMerge.Poly := [(nat_lit 971, Int.ofNat (nat_lit 221760))]
theorem block005_data_flat088_step : block005_data_flat088 = (CoefficientMerge.scale (221760 : Int) atom0438Coded) := by decide +kernel
theorem block005_data_flat088_original : block005_data_flat088 = (CoefficientMerge.scale (221760 : Int) atom0438Coded) := by
  rw [block005_data_flat088_step]
def block005_data_flat089 : CoefficientMerge.Poly := [(nat_lit 982, Int.ofNat (nat_lit 1900800))]
theorem block005_data_flat089_step : block005_data_flat089 = (CoefficientMerge.scale (1900800 : Int) atom0439Coded) := by decide +kernel
theorem block005_data_flat089_original : block005_data_flat089 = (CoefficientMerge.scale (1900800 : Int) atom0439Coded) := by
  rw [block005_data_flat089_step]
def block005_data_flat090 : CoefficientMerge.Poly := [(nat_lit 971, Int.ofNat (nat_lit 221760)), (nat_lit 982, Int.ofNat (nat_lit 1900800))]
theorem block005_data_flat090_step : block005_data_flat090 = (CoefficientMerge.fastMerge block005_data_flat088 block005_data_flat089) := by decide +kernel
theorem block005_data_flat090_original : block005_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (221760 : Int) atom0438Coded) (CoefficientMerge.scale (1900800 : Int) atom0439Coded)) := by
  rw [block005_data_flat090_step, block005_data_flat088_original, block005_data_flat089_original]
def block005_data_flat091 : CoefficientMerge.Poly := [(nat_lit 983, Int.ofNat (nat_lit 3801600))]
theorem block005_data_flat091_step : block005_data_flat091 = (CoefficientMerge.scale (3801600 : Int) atom0440Coded) := by decide +kernel
theorem block005_data_flat091_original : block005_data_flat091 = (CoefficientMerge.scale (3801600 : Int) atom0440Coded) := by
  rw [block005_data_flat091_step]
def block005_data_flat092 : CoefficientMerge.Poly := [(nat_lit 984, Int.ofNat (nat_lit 33785280))]
theorem block005_data_flat092_step : block005_data_flat092 = (CoefficientMerge.scale (33785280 : Int) atom0441Coded) := by decide +kernel
theorem block005_data_flat092_original : block005_data_flat092 = (CoefficientMerge.scale (33785280 : Int) atom0441Coded) := by
  rw [block005_data_flat092_step]
def block005_data_flat093 : CoefficientMerge.Poly := [(nat_lit 985, Int.ofNat (nat_lit 4849920))]
theorem block005_data_flat093_step : block005_data_flat093 = (CoefficientMerge.scale (4849920 : Int) atom0442Coded) := by decide +kernel
theorem block005_data_flat093_original : block005_data_flat093 = (CoefficientMerge.scale (4849920 : Int) atom0442Coded) := by
  rw [block005_data_flat093_step]
def block005_data_flat094 : CoefficientMerge.Poly := [(nat_lit 984, Int.ofNat (nat_lit 33785280)), (nat_lit 985, Int.ofNat (nat_lit 4849920))]
theorem block005_data_flat094_step : block005_data_flat094 = (CoefficientMerge.fastMerge block005_data_flat092 block005_data_flat093) := by decide +kernel
theorem block005_data_flat094_original : block005_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (33785280 : Int) atom0441Coded) (CoefficientMerge.scale (4849920 : Int) atom0442Coded)) := by
  rw [block005_data_flat094_step, block005_data_flat092_original, block005_data_flat093_original]
def block005_data_flat095 : CoefficientMerge.Poly := [(nat_lit 983, Int.ofNat (nat_lit 3801600)), (nat_lit 984, Int.ofNat (nat_lit 33785280)), (nat_lit 985, Int.ofNat (nat_lit 4849920))]
theorem block005_data_flat095_step : block005_data_flat095 = (CoefficientMerge.fastMerge block005_data_flat091 block005_data_flat094) := by decide +kernel
theorem block005_data_flat095_original : block005_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3801600 : Int) atom0440Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33785280 : Int) atom0441Coded) (CoefficientMerge.scale (4849920 : Int) atom0442Coded))) := by
  rw [block005_data_flat095_step, block005_data_flat091_original, block005_data_flat094_original]
def block005_data_flat096 : CoefficientMerge.Poly := [(nat_lit 971, Int.ofNat (nat_lit 221760)), (nat_lit 982, Int.ofNat (nat_lit 1900800)), (nat_lit 983, Int.ofNat (nat_lit 3801600)), (nat_lit 984, Int.ofNat (nat_lit 33785280)), (nat_lit 985, Int.ofNat (nat_lit 4849920))]
theorem block005_data_flat096_step : block005_data_flat096 = (CoefficientMerge.fastMerge block005_data_flat090 block005_data_flat095) := by decide +kernel
theorem block005_data_flat096_original : block005_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (221760 : Int) atom0438Coded) (CoefficientMerge.scale (1900800 : Int) atom0439Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3801600 : Int) atom0440Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33785280 : Int) atom0441Coded) (CoefficientMerge.scale (4849920 : Int) atom0442Coded)))) := by
  rw [block005_data_flat096_step, block005_data_flat090_original, block005_data_flat095_original]
def block005_data_flat097 : CoefficientMerge.Poly := [(nat_lit 883, Int.ofNat (nat_lit 15264720)), (nat_lit 884, Int.ofNat (nat_lit 99311130)), (nat_lit 899, Int.ofNat (nat_lit 79701570)), (nat_lit 964, Int.ofNat (nat_lit 2931840)), (nat_lit 969, Int.ofNat (nat_lit 19845360)), (nat_lit 971, Int.ofNat (nat_lit 221760)), (nat_lit 982, Int.ofNat (nat_lit 1900800)), (nat_lit 983, Int.ofNat (nat_lit 3801600)), (nat_lit 984, Int.ofNat (nat_lit 33785280)), (nat_lit 985, Int.ofNat (nat_lit 4849920))]
theorem block005_data_flat097_step : block005_data_flat097 = (CoefficientMerge.fastMerge block005_data_flat087 block005_data_flat096) := by decide +kernel
theorem block005_data_flat097_original : block005_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15264720 : Int) atom0433Coded) (CoefficientMerge.scale (99311130 : Int) atom0434Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79701570 : Int) atom0435Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2931840 : Int) atom0436Coded) (CoefficientMerge.scale (19845360 : Int) atom0437Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (221760 : Int) atom0438Coded) (CoefficientMerge.scale (1900800 : Int) atom0439Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3801600 : Int) atom0440Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33785280 : Int) atom0441Coded) (CoefficientMerge.scale (4849920 : Int) atom0442Coded))))) := by
  rw [block005_data_flat097_step, block005_data_flat087_original, block005_data_flat096_original]
def block005_data_flat098 : CoefficientMerge.Poly := [(nat_lit 986, Int.ofNat (nat_lit 11026080))]
theorem block005_data_flat098_step : block005_data_flat098 = (CoefficientMerge.scale (11026080 : Int) atom0443Coded) := by decide +kernel
theorem block005_data_flat098_original : block005_data_flat098 = (CoefficientMerge.scale (11026080 : Int) atom0443Coded) := by
  rw [block005_data_flat098_step]
def block005_data_flat099 : CoefficientMerge.Poly := [(nat_lit 987, Int.ofNat (nat_lit 22376160))]
theorem block005_data_flat099_step : block005_data_flat099 = (CoefficientMerge.scale (22376160 : Int) atom0444Coded) := by decide +kernel
theorem block005_data_flat099_original : block005_data_flat099 = (CoefficientMerge.scale (22376160 : Int) atom0444Coded) := by
  rw [block005_data_flat099_step]
def block005_data_flat100 : CoefficientMerge.Poly := [(nat_lit 986, Int.ofNat (nat_lit 11026080)), (nat_lit 987, Int.ofNat (nat_lit 22376160))]
theorem block005_data_flat100_step : block005_data_flat100 = (CoefficientMerge.fastMerge block005_data_flat098 block005_data_flat099) := by decide +kernel
theorem block005_data_flat100_original : block005_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11026080 : Int) atom0443Coded) (CoefficientMerge.scale (22376160 : Int) atom0444Coded)) := by
  rw [block005_data_flat100_step, block005_data_flat098_original, block005_data_flat099_original]
def block005_data_flat101 : CoefficientMerge.Poly := [(nat_lit 988, Int.ofNat (nat_lit 37272960))]
theorem block005_data_flat101_step : block005_data_flat101 = (CoefficientMerge.scale (37272960 : Int) atom0445Coded) := by decide +kernel
theorem block005_data_flat101_original : block005_data_flat101 = (CoefficientMerge.scale (37272960 : Int) atom0445Coded) := by
  rw [block005_data_flat101_step]
def block005_data_flat102 : CoefficientMerge.Poly := [(nat_lit 989, Int.ofNat (nat_lit 54092880))]
theorem block005_data_flat102_step : block005_data_flat102 = (CoefficientMerge.scale (54092880 : Int) atom0446Coded) := by decide +kernel
theorem block005_data_flat102_original : block005_data_flat102 = (CoefficientMerge.scale (54092880 : Int) atom0446Coded) := by
  rw [block005_data_flat102_step]
def block005_data_flat103 : CoefficientMerge.Poly := [(nat_lit 996, Int.ofNat (nat_lit 5466240))]
theorem block005_data_flat103_step : block005_data_flat103 = (CoefficientMerge.scale (5466240 : Int) atom0447Coded) := by decide +kernel
theorem block005_data_flat103_original : block005_data_flat103 = (CoefficientMerge.scale (5466240 : Int) atom0447Coded) := by
  rw [block005_data_flat103_step]
def block005_data_flat104 : CoefficientMerge.Poly := [(nat_lit 989, Int.ofNat (nat_lit 54092880)), (nat_lit 996, Int.ofNat (nat_lit 5466240))]
theorem block005_data_flat104_step : block005_data_flat104 = (CoefficientMerge.fastMerge block005_data_flat102 block005_data_flat103) := by decide +kernel
theorem block005_data_flat104_original : block005_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (54092880 : Int) atom0446Coded) (CoefficientMerge.scale (5466240 : Int) atom0447Coded)) := by
  rw [block005_data_flat104_step, block005_data_flat102_original, block005_data_flat103_original]
def block005_data_flat105 : CoefficientMerge.Poly := [(nat_lit 988, Int.ofNat (nat_lit 37272960)), (nat_lit 989, Int.ofNat (nat_lit 54092880)), (nat_lit 996, Int.ofNat (nat_lit 5466240))]
theorem block005_data_flat105_step : block005_data_flat105 = (CoefficientMerge.fastMerge block005_data_flat101 block005_data_flat104) := by decide +kernel
theorem block005_data_flat105_original : block005_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (37272960 : Int) atom0445Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54092880 : Int) atom0446Coded) (CoefficientMerge.scale (5466240 : Int) atom0447Coded))) := by
  rw [block005_data_flat105_step, block005_data_flat101_original, block005_data_flat104_original]
def block005_data_flat106 : CoefficientMerge.Poly := [(nat_lit 986, Int.ofNat (nat_lit 11026080)), (nat_lit 987, Int.ofNat (nat_lit 22376160)), (nat_lit 988, Int.ofNat (nat_lit 37272960)), (nat_lit 989, Int.ofNat (nat_lit 54092880)), (nat_lit 996, Int.ofNat (nat_lit 5466240))]
theorem block005_data_flat106_step : block005_data_flat106 = (CoefficientMerge.fastMerge block005_data_flat100 block005_data_flat105) := by decide +kernel
theorem block005_data_flat106_original : block005_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11026080 : Int) atom0443Coded) (CoefficientMerge.scale (22376160 : Int) atom0444Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37272960 : Int) atom0445Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54092880 : Int) atom0446Coded) (CoefficientMerge.scale (5466240 : Int) atom0447Coded)))) := by
  rw [block005_data_flat106_step, block005_data_flat100_original, block005_data_flat105_original]
def block005_data_flat107 : CoefficientMerge.Poly := [(nat_lit 997, Int.ofNat (nat_lit 13541760))]
theorem block005_data_flat107_step : block005_data_flat107 = (CoefficientMerge.scale (13541760 : Int) atom0448Coded) := by decide +kernel
theorem block005_data_flat107_original : block005_data_flat107 = (CoefficientMerge.scale (13541760 : Int) atom0448Coded) := by
  rw [block005_data_flat107_step]
def block005_data_flat108 : CoefficientMerge.Poly := [(nat_lit 998, Int.ofNat (nat_lit 16151040))]
theorem block005_data_flat108_step : block005_data_flat108 = (CoefficientMerge.scale (16151040 : Int) atom0449Coded) := by decide +kernel
theorem block005_data_flat108_original : block005_data_flat108 = (CoefficientMerge.scale (16151040 : Int) atom0449Coded) := by
  rw [block005_data_flat108_step]
def block005_data_flat109 : CoefficientMerge.Poly := [(nat_lit 997, Int.ofNat (nat_lit 13541760)), (nat_lit 998, Int.ofNat (nat_lit 16151040))]
theorem block005_data_flat109_step : block005_data_flat109 = (CoefficientMerge.fastMerge block005_data_flat107 block005_data_flat108) := by decide +kernel
theorem block005_data_flat109_original : block005_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13541760 : Int) atom0448Coded) (CoefficientMerge.scale (16151040 : Int) atom0449Coded)) := by
  rw [block005_data_flat109_step, block005_data_flat107_original, block005_data_flat108_original]
def block005_data_flat110 : CoefficientMerge.Poly := [(nat_lit 999, Int.ofNat (nat_lit 42252480))]
theorem block005_data_flat110_step : block005_data_flat110 = (CoefficientMerge.scale (42252480 : Int) atom0450Coded) := by decide +kernel
theorem block005_data_flat110_original : block005_data_flat110 = (CoefficientMerge.scale (42252480 : Int) atom0450Coded) := by
  rw [block005_data_flat110_step]
def block005_data_flat111 : CoefficientMerge.Poly := [(nat_lit 1000, Int.ofNat (nat_lit 23506560))]
theorem block005_data_flat111_step : block005_data_flat111 = (CoefficientMerge.scale (23506560 : Int) atom0451Coded) := by decide +kernel
theorem block005_data_flat111_original : block005_data_flat111 = (CoefficientMerge.scale (23506560 : Int) atom0451Coded) := by
  rw [block005_data_flat111_step]
def block005_data_flat112 : CoefficientMerge.Poly := [(nat_lit 1001, Int.ofNat (nat_lit 33835680))]
theorem block005_data_flat112_step : block005_data_flat112 = (CoefficientMerge.scale (33835680 : Int) atom0452Coded) := by decide +kernel
theorem block005_data_flat112_original : block005_data_flat112 = (CoefficientMerge.scale (33835680 : Int) atom0452Coded) := by
  rw [block005_data_flat112_step]
def block005_data_flat113 : CoefficientMerge.Poly := [(nat_lit 1000, Int.ofNat (nat_lit 23506560)), (nat_lit 1001, Int.ofNat (nat_lit 33835680))]
theorem block005_data_flat113_step : block005_data_flat113 = (CoefficientMerge.fastMerge block005_data_flat111 block005_data_flat112) := by decide +kernel
theorem block005_data_flat113_original : block005_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23506560 : Int) atom0451Coded) (CoefficientMerge.scale (33835680 : Int) atom0452Coded)) := by
  rw [block005_data_flat113_step, block005_data_flat111_original, block005_data_flat112_original]
def block005_data_flat114 : CoefficientMerge.Poly := [(nat_lit 999, Int.ofNat (nat_lit 42252480)), (nat_lit 1000, Int.ofNat (nat_lit 23506560)), (nat_lit 1001, Int.ofNat (nat_lit 33835680))]
theorem block005_data_flat114_step : block005_data_flat114 = (CoefficientMerge.fastMerge block005_data_flat110 block005_data_flat113) := by decide +kernel
theorem block005_data_flat114_original : block005_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (42252480 : Int) atom0450Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23506560 : Int) atom0451Coded) (CoefficientMerge.scale (33835680 : Int) atom0452Coded))) := by
  rw [block005_data_flat114_step, block005_data_flat110_original, block005_data_flat113_original]
def block005_data_flat115 : CoefficientMerge.Poly := [(nat_lit 997, Int.ofNat (nat_lit 13541760)), (nat_lit 998, Int.ofNat (nat_lit 16151040)), (nat_lit 999, Int.ofNat (nat_lit 42252480)), (nat_lit 1000, Int.ofNat (nat_lit 23506560)), (nat_lit 1001, Int.ofNat (nat_lit 33835680))]
theorem block005_data_flat115_step : block005_data_flat115 = (CoefficientMerge.fastMerge block005_data_flat109 block005_data_flat114) := by decide +kernel
theorem block005_data_flat115_original : block005_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13541760 : Int) atom0448Coded) (CoefficientMerge.scale (16151040 : Int) atom0449Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42252480 : Int) atom0450Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23506560 : Int) atom0451Coded) (CoefficientMerge.scale (33835680 : Int) atom0452Coded)))) := by
  rw [block005_data_flat115_step, block005_data_flat109_original, block005_data_flat114_original]
def block005_data_flat116 : CoefficientMerge.Poly := [(nat_lit 986, Int.ofNat (nat_lit 11026080)), (nat_lit 987, Int.ofNat (nat_lit 22376160)), (nat_lit 988, Int.ofNat (nat_lit 37272960)), (nat_lit 989, Int.ofNat (nat_lit 54092880)), (nat_lit 996, Int.ofNat (nat_lit 5466240)), (nat_lit 997, Int.ofNat (nat_lit 13541760)), (nat_lit 998, Int.ofNat (nat_lit 16151040)), (nat_lit 999, Int.ofNat (nat_lit 42252480)), (nat_lit 1000, Int.ofNat (nat_lit 23506560)), (nat_lit 1001, Int.ofNat (nat_lit 33835680))]
theorem block005_data_flat116_step : block005_data_flat116 = (CoefficientMerge.fastMerge block005_data_flat106 block005_data_flat115) := by decide +kernel
theorem block005_data_flat116_original : block005_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11026080 : Int) atom0443Coded) (CoefficientMerge.scale (22376160 : Int) atom0444Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37272960 : Int) atom0445Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54092880 : Int) atom0446Coded) (CoefficientMerge.scale (5466240 : Int) atom0447Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13541760 : Int) atom0448Coded) (CoefficientMerge.scale (16151040 : Int) atom0449Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42252480 : Int) atom0450Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23506560 : Int) atom0451Coded) (CoefficientMerge.scale (33835680 : Int) atom0452Coded))))) := by
  rw [block005_data_flat116_step, block005_data_flat106_original, block005_data_flat115_original]
def block005_data_flat117 : CoefficientMerge.Poly := [(nat_lit 883, Int.ofNat (nat_lit 15264720)), (nat_lit 884, Int.ofNat (nat_lit 99311130)), (nat_lit 899, Int.ofNat (nat_lit 79701570)), (nat_lit 964, Int.ofNat (nat_lit 2931840)), (nat_lit 969, Int.ofNat (nat_lit 19845360)), (nat_lit 971, Int.ofNat (nat_lit 221760)), (nat_lit 982, Int.ofNat (nat_lit 1900800)), (nat_lit 983, Int.ofNat (nat_lit 3801600)), (nat_lit 984, Int.ofNat (nat_lit 33785280)), (nat_lit 985, Int.ofNat (nat_lit 4849920)), (nat_lit 986, Int.ofNat (nat_lit 11026080)), (nat_lit 987, Int.ofNat (nat_lit 22376160)), (nat_lit 988, Int.ofNat (nat_lit 37272960)), (nat_lit 989, Int.ofNat (nat_lit 54092880)), (nat_lit 996, Int.ofNat (nat_lit 5466240)), (nat_lit 997, Int.ofNat (nat_lit 13541760)), (nat_lit 998, Int.ofNat (nat_lit 16151040)), (nat_lit 999, Int.ofNat (nat_lit 42252480)), (nat_lit 1000, Int.ofNat (nat_lit 23506560)), (nat_lit 1001, Int.ofNat (nat_lit 33835680))]
theorem block005_data_flat117_step : block005_data_flat117 = (CoefficientMerge.fastMerge block005_data_flat097 block005_data_flat116) := by decide +kernel
theorem block005_data_flat117_original : block005_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15264720 : Int) atom0433Coded) (CoefficientMerge.scale (99311130 : Int) atom0434Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79701570 : Int) atom0435Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2931840 : Int) atom0436Coded) (CoefficientMerge.scale (19845360 : Int) atom0437Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (221760 : Int) atom0438Coded) (CoefficientMerge.scale (1900800 : Int) atom0439Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3801600 : Int) atom0440Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33785280 : Int) atom0441Coded) (CoefficientMerge.scale (4849920 : Int) atom0442Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11026080 : Int) atom0443Coded) (CoefficientMerge.scale (22376160 : Int) atom0444Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37272960 : Int) atom0445Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54092880 : Int) atom0446Coded) (CoefficientMerge.scale (5466240 : Int) atom0447Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13541760 : Int) atom0448Coded) (CoefficientMerge.scale (16151040 : Int) atom0449Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42252480 : Int) atom0450Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23506560 : Int) atom0451Coded) (CoefficientMerge.scale (33835680 : Int) atom0452Coded)))))) := by
  rw [block005_data_flat117_step, block005_data_flat097_original, block005_data_flat116_original]
def block005_data_flat118 : CoefficientMerge.Poly := [(nat_lit 1002, Int.ofNat (nat_lit 49206240))]
theorem block005_data_flat118_step : block005_data_flat118 = (CoefficientMerge.scale (49206240 : Int) atom0453Coded) := by decide +kernel
theorem block005_data_flat118_original : block005_data_flat118 = (CoefficientMerge.scale (49206240 : Int) atom0453Coded) := by
  rw [block005_data_flat118_step]
def block005_data_flat119 : CoefficientMerge.Poly := [(nat_lit 1003, Int.ofNat (nat_lit 68711040))]
theorem block005_data_flat119_step : block005_data_flat119 = (CoefficientMerge.scale (68711040 : Int) atom0454Coded) := by decide +kernel
theorem block005_data_flat119_original : block005_data_flat119 = (CoefficientMerge.scale (68711040 : Int) atom0454Coded) := by
  rw [block005_data_flat119_step]
def block005_data_flat120 : CoefficientMerge.Poly := [(nat_lit 1002, Int.ofNat (nat_lit 49206240)), (nat_lit 1003, Int.ofNat (nat_lit 68711040))]
theorem block005_data_flat120_step : block005_data_flat120 = (CoefficientMerge.fastMerge block005_data_flat118 block005_data_flat119) := by decide +kernel
theorem block005_data_flat120_original : block005_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (49206240 : Int) atom0453Coded) (CoefficientMerge.scale (68711040 : Int) atom0454Coded)) := by
  rw [block005_data_flat120_step, block005_data_flat118_original, block005_data_flat119_original]
def block005_data_flat121 : CoefficientMerge.Poly := [(nat_lit 1004, Int.ofNat (nat_lit 89836560))]
theorem block005_data_flat121_step : block005_data_flat121 = (CoefficientMerge.scale (89836560 : Int) atom0455Coded) := by decide +kernel
theorem block005_data_flat121_original : block005_data_flat121 = (CoefficientMerge.scale (89836560 : Int) atom0455Coded) := by
  rw [block005_data_flat121_step]
def block005_data_flat122 : CoefficientMerge.Poly := [(nat_lit 1012, Int.ofNat (nat_lit 14188800))]
theorem block005_data_flat122_step : block005_data_flat122 = (CoefficientMerge.scale (14188800 : Int) atom0456Coded) := by decide +kernel
theorem block005_data_flat122_original : block005_data_flat122 = (CoefficientMerge.scale (14188800 : Int) atom0456Coded) := by
  rw [block005_data_flat122_step]
def block005_data_flat123 : CoefficientMerge.Poly := [(nat_lit 1013, Int.ofNat (nat_lit 30462720))]
theorem block005_data_flat123_step : block005_data_flat123 = (CoefficientMerge.scale (30462720 : Int) atom0457Coded) := by decide +kernel
theorem block005_data_flat123_original : block005_data_flat123 = (CoefficientMerge.scale (30462720 : Int) atom0457Coded) := by
  rw [block005_data_flat123_step]
def block005_data_flat124 : CoefficientMerge.Poly := [(nat_lit 1012, Int.ofNat (nat_lit 14188800)), (nat_lit 1013, Int.ofNat (nat_lit 30462720))]
theorem block005_data_flat124_step : block005_data_flat124 = (CoefficientMerge.fastMerge block005_data_flat122 block005_data_flat123) := by decide +kernel
theorem block005_data_flat124_original : block005_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14188800 : Int) atom0456Coded) (CoefficientMerge.scale (30462720 : Int) atom0457Coded)) := by
  rw [block005_data_flat124_step, block005_data_flat122_original, block005_data_flat123_original]
def block005_data_flat125 : CoefficientMerge.Poly := [(nat_lit 1004, Int.ofNat (nat_lit 89836560)), (nat_lit 1012, Int.ofNat (nat_lit 14188800)), (nat_lit 1013, Int.ofNat (nat_lit 30462720))]
theorem block005_data_flat125_step : block005_data_flat125 = (CoefficientMerge.fastMerge block005_data_flat121 block005_data_flat124) := by decide +kernel
theorem block005_data_flat125_original : block005_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (89836560 : Int) atom0455Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14188800 : Int) atom0456Coded) (CoefficientMerge.scale (30462720 : Int) atom0457Coded))) := by
  rw [block005_data_flat125_step, block005_data_flat121_original, block005_data_flat124_original]
def block005_data_flat126 : CoefficientMerge.Poly := [(nat_lit 1002, Int.ofNat (nat_lit 49206240)), (nat_lit 1003, Int.ofNat (nat_lit 68711040)), (nat_lit 1004, Int.ofNat (nat_lit 89836560)), (nat_lit 1012, Int.ofNat (nat_lit 14188800)), (nat_lit 1013, Int.ofNat (nat_lit 30462720))]
theorem block005_data_flat126_step : block005_data_flat126 = (CoefficientMerge.fastMerge block005_data_flat120 block005_data_flat125) := by decide +kernel
theorem block005_data_flat126_original : block005_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49206240 : Int) atom0453Coded) (CoefficientMerge.scale (68711040 : Int) atom0454Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89836560 : Int) atom0455Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14188800 : Int) atom0456Coded) (CoefficientMerge.scale (30462720 : Int) atom0457Coded)))) := by
  rw [block005_data_flat126_step, block005_data_flat120_original, block005_data_flat125_original]
def block005_data_flat127 : CoefficientMerge.Poly := [(nat_lit 1014, Int.ofNat (nat_lit 52680000))]
theorem block005_data_flat127_step : block005_data_flat127 = (CoefficientMerge.scale (52680000 : Int) atom0458Coded) := by decide +kernel
theorem block005_data_flat127_original : block005_data_flat127 = (CoefficientMerge.scale (52680000 : Int) atom0458Coded) := by
  rw [block005_data_flat127_step]
def block005_data_flat128 : CoefficientMerge.Poly := [(nat_lit 1015, Int.ofNat (nat_lit 40726320))]
theorem block005_data_flat128_step : block005_data_flat128 = (CoefficientMerge.scale (40726320 : Int) atom0459Coded) := by decide +kernel
theorem block005_data_flat128_original : block005_data_flat128 = (CoefficientMerge.scale (40726320 : Int) atom0459Coded) := by
  rw [block005_data_flat128_step]
def block005_data_flat129 : CoefficientMerge.Poly := [(nat_lit 1014, Int.ofNat (nat_lit 52680000)), (nat_lit 1015, Int.ofNat (nat_lit 40726320))]
theorem block005_data_flat129_step : block005_data_flat129 = (CoefficientMerge.fastMerge block005_data_flat127 block005_data_flat128) := by decide +kernel
theorem block005_data_flat129_original : block005_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (52680000 : Int) atom0458Coded) (CoefficientMerge.scale (40726320 : Int) atom0459Coded)) := by
  rw [block005_data_flat129_step, block005_data_flat127_original, block005_data_flat128_original]
def block005_data_flat130 : CoefficientMerge.Poly := [(nat_lit 1016, Int.ofNat (nat_lit 56645280))]
theorem block005_data_flat130_step : block005_data_flat130 = (CoefficientMerge.scale (56645280 : Int) atom0460Coded) := by decide +kernel
theorem block005_data_flat130_original : block005_data_flat130 = (CoefficientMerge.scale (56645280 : Int) atom0460Coded) := by
  rw [block005_data_flat130_step]
def block005_data_flat131 : CoefficientMerge.Poly := [(nat_lit 1017, Int.ofNat (nat_lit 70185840))]
theorem block005_data_flat131_step : block005_data_flat131 = (CoefficientMerge.scale (70185840 : Int) atom0461Coded) := by decide +kernel
theorem block005_data_flat131_original : block005_data_flat131 = (CoefficientMerge.scale (70185840 : Int) atom0461Coded) := by
  rw [block005_data_flat131_step]
def block005_data_flat132 : CoefficientMerge.Poly := [(nat_lit 1018, Int.ofNat (nat_lit 91753680))]
theorem block005_data_flat132_step : block005_data_flat132 = (CoefficientMerge.scale (91753680 : Int) atom0462Coded) := by decide +kernel
theorem block005_data_flat132_original : block005_data_flat132 = (CoefficientMerge.scale (91753680 : Int) atom0462Coded) := by
  rw [block005_data_flat132_step]
def block005_data_flat133 : CoefficientMerge.Poly := [(nat_lit 1017, Int.ofNat (nat_lit 70185840)), (nat_lit 1018, Int.ofNat (nat_lit 91753680))]
theorem block005_data_flat133_step : block005_data_flat133 = (CoefficientMerge.fastMerge block005_data_flat131 block005_data_flat132) := by decide +kernel
theorem block005_data_flat133_original : block005_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (70185840 : Int) atom0461Coded) (CoefficientMerge.scale (91753680 : Int) atom0462Coded)) := by
  rw [block005_data_flat133_step, block005_data_flat131_original, block005_data_flat132_original]
def block005_data_flat134 : CoefficientMerge.Poly := [(nat_lit 1016, Int.ofNat (nat_lit 56645280)), (nat_lit 1017, Int.ofNat (nat_lit 70185840)), (nat_lit 1018, Int.ofNat (nat_lit 91753680))]
theorem block005_data_flat134_step : block005_data_flat134 = (CoefficientMerge.fastMerge block005_data_flat130 block005_data_flat133) := by decide +kernel
theorem block005_data_flat134_original : block005_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (56645280 : Int) atom0460Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70185840 : Int) atom0461Coded) (CoefficientMerge.scale (91753680 : Int) atom0462Coded))) := by
  rw [block005_data_flat134_step, block005_data_flat130_original, block005_data_flat133_original]
def block005_data_flat135 : CoefficientMerge.Poly := [(nat_lit 1014, Int.ofNat (nat_lit 52680000)), (nat_lit 1015, Int.ofNat (nat_lit 40726320)), (nat_lit 1016, Int.ofNat (nat_lit 56645280)), (nat_lit 1017, Int.ofNat (nat_lit 70185840)), (nat_lit 1018, Int.ofNat (nat_lit 91753680))]
theorem block005_data_flat135_step : block005_data_flat135 = (CoefficientMerge.fastMerge block005_data_flat129 block005_data_flat134) := by decide +kernel
theorem block005_data_flat135_original : block005_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52680000 : Int) atom0458Coded) (CoefficientMerge.scale (40726320 : Int) atom0459Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56645280 : Int) atom0460Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70185840 : Int) atom0461Coded) (CoefficientMerge.scale (91753680 : Int) atom0462Coded)))) := by
  rw [block005_data_flat135_step, block005_data_flat129_original, block005_data_flat134_original]
def block005_data_flat136 : CoefficientMerge.Poly := [(nat_lit 1002, Int.ofNat (nat_lit 49206240)), (nat_lit 1003, Int.ofNat (nat_lit 68711040)), (nat_lit 1004, Int.ofNat (nat_lit 89836560)), (nat_lit 1012, Int.ofNat (nat_lit 14188800)), (nat_lit 1013, Int.ofNat (nat_lit 30462720)), (nat_lit 1014, Int.ofNat (nat_lit 52680000)), (nat_lit 1015, Int.ofNat (nat_lit 40726320)), (nat_lit 1016, Int.ofNat (nat_lit 56645280)), (nat_lit 1017, Int.ofNat (nat_lit 70185840)), (nat_lit 1018, Int.ofNat (nat_lit 91753680))]
theorem block005_data_flat136_step : block005_data_flat136 = (CoefficientMerge.fastMerge block005_data_flat126 block005_data_flat135) := by decide +kernel
theorem block005_data_flat136_original : block005_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49206240 : Int) atom0453Coded) (CoefficientMerge.scale (68711040 : Int) atom0454Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89836560 : Int) atom0455Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14188800 : Int) atom0456Coded) (CoefficientMerge.scale (30462720 : Int) atom0457Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52680000 : Int) atom0458Coded) (CoefficientMerge.scale (40726320 : Int) atom0459Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56645280 : Int) atom0460Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70185840 : Int) atom0461Coded) (CoefficientMerge.scale (91753680 : Int) atom0462Coded))))) := by
  rw [block005_data_flat136_step, block005_data_flat126_original, block005_data_flat135_original]
def block005_data_flat137 : CoefficientMerge.Poly := [(nat_lit 1019, Int.ofNat (nat_lit 114639840))]
theorem block005_data_flat137_step : block005_data_flat137 = (CoefficientMerge.scale (114639840 : Int) atom0463Coded) := by decide +kernel
theorem block005_data_flat137_original : block005_data_flat137 = (CoefficientMerge.scale (114639840 : Int) atom0463Coded) := by
  rw [block005_data_flat137_step]
def block005_data_flat138 : CoefficientMerge.Poly := [(nat_lit 1028, Int.ofNat (nat_lit 24301440))]
theorem block005_data_flat138_step : block005_data_flat138 = (CoefficientMerge.scale (24301440 : Int) atom0464Coded) := by decide +kernel
theorem block005_data_flat138_original : block005_data_flat138 = (CoefficientMerge.scale (24301440 : Int) atom0464Coded) := by
  rw [block005_data_flat138_step]
def block005_data_flat139 : CoefficientMerge.Poly := [(nat_lit 1019, Int.ofNat (nat_lit 114639840)), (nat_lit 1028, Int.ofNat (nat_lit 24301440))]
theorem block005_data_flat139_step : block005_data_flat139 = (CoefficientMerge.fastMerge block005_data_flat137 block005_data_flat138) := by decide +kernel
theorem block005_data_flat139_original : block005_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (114639840 : Int) atom0463Coded) (CoefficientMerge.scale (24301440 : Int) atom0464Coded)) := by
  rw [block005_data_flat139_step, block005_data_flat137_original, block005_data_flat138_original]
def block005_data_flat140 : CoefficientMerge.Poly := [(nat_lit 1029, Int.ofNat (nat_lit 70267680))]
theorem block005_data_flat140_step : block005_data_flat140 = (CoefficientMerge.scale (70267680 : Int) atom0465Coded) := by decide +kernel
theorem block005_data_flat140_original : block005_data_flat140 = (CoefficientMerge.scale (70267680 : Int) atom0465Coded) := by
  rw [block005_data_flat140_step]
def block005_data_flat141 : CoefficientMerge.Poly := [(nat_lit 1030, Int.ofNat (nat_lit 57675600))]
theorem block005_data_flat141_step : block005_data_flat141 = (CoefficientMerge.scale (57675600 : Int) atom0466Coded) := by decide +kernel
theorem block005_data_flat141_original : block005_data_flat141 = (CoefficientMerge.scale (57675600 : Int) atom0466Coded) := by
  rw [block005_data_flat141_step]
def block005_data_flat142 : CoefficientMerge.Poly := [(nat_lit 1031, Int.ofNat (nat_lit 79454880))]
theorem block005_data_flat142_step : block005_data_flat142 = (CoefficientMerge.scale (79454880 : Int) atom0467Coded) := by decide +kernel
theorem block005_data_flat142_original : block005_data_flat142 = (CoefficientMerge.scale (79454880 : Int) atom0467Coded) := by
  rw [block005_data_flat142_step]
def block005_data_flat143 : CoefficientMerge.Poly := [(nat_lit 1030, Int.ofNat (nat_lit 57675600)), (nat_lit 1031, Int.ofNat (nat_lit 79454880))]
theorem block005_data_flat143_step : block005_data_flat143 = (CoefficientMerge.fastMerge block005_data_flat141 block005_data_flat142) := by decide +kernel
theorem block005_data_flat143_original : block005_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (57675600 : Int) atom0466Coded) (CoefficientMerge.scale (79454880 : Int) atom0467Coded)) := by
  rw [block005_data_flat143_step, block005_data_flat141_original, block005_data_flat142_original]
def block005_data_flat144 : CoefficientMerge.Poly := [(nat_lit 1029, Int.ofNat (nat_lit 70267680)), (nat_lit 1030, Int.ofNat (nat_lit 57675600)), (nat_lit 1031, Int.ofNat (nat_lit 79454880))]
theorem block005_data_flat144_step : block005_data_flat144 = (CoefficientMerge.fastMerge block005_data_flat140 block005_data_flat143) := by decide +kernel
theorem block005_data_flat144_original : block005_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (70267680 : Int) atom0465Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57675600 : Int) atom0466Coded) (CoefficientMerge.scale (79454880 : Int) atom0467Coded))) := by
  rw [block005_data_flat144_step, block005_data_flat140_original, block005_data_flat143_original]
def block005_data_flat145 : CoefficientMerge.Poly := [(nat_lit 1019, Int.ofNat (nat_lit 114639840)), (nat_lit 1028, Int.ofNat (nat_lit 24301440)), (nat_lit 1029, Int.ofNat (nat_lit 70267680)), (nat_lit 1030, Int.ofNat (nat_lit 57675600)), (nat_lit 1031, Int.ofNat (nat_lit 79454880))]
theorem block005_data_flat145_step : block005_data_flat145 = (CoefficientMerge.fastMerge block005_data_flat139 block005_data_flat144) := by decide +kernel
theorem block005_data_flat145_original : block005_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (114639840 : Int) atom0463Coded) (CoefficientMerge.scale (24301440 : Int) atom0464Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70267680 : Int) atom0465Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57675600 : Int) atom0466Coded) (CoefficientMerge.scale (79454880 : Int) atom0467Coded)))) := by
  rw [block005_data_flat145_step, block005_data_flat139_original, block005_data_flat144_original]
def block005_data_flat146 : CoefficientMerge.Poly := [(nat_lit 1032, Int.ofNat (nat_lit 94062960))]
theorem block005_data_flat146_step : block005_data_flat146 = (CoefficientMerge.scale (94062960 : Int) atom0468Coded) := by decide +kernel
theorem block005_data_flat146_original : block005_data_flat146 = (CoefficientMerge.scale (94062960 : Int) atom0468Coded) := by
  rw [block005_data_flat146_step]
def block005_data_flat147 : CoefficientMerge.Poly := [(nat_lit 1033, Int.ofNat (nat_lit 105234480))]
theorem block005_data_flat147_step : block005_data_flat147 = (CoefficientMerge.scale (105234480 : Int) atom0469Coded) := by decide +kernel
theorem block005_data_flat147_original : block005_data_flat147 = (CoefficientMerge.scale (105234480 : Int) atom0469Coded) := by
  rw [block005_data_flat147_step]
def block005_data_flat148 : CoefficientMerge.Poly := [(nat_lit 1032, Int.ofNat (nat_lit 94062960)), (nat_lit 1033, Int.ofNat (nat_lit 105234480))]
theorem block005_data_flat148_step : block005_data_flat148 = (CoefficientMerge.fastMerge block005_data_flat146 block005_data_flat147) := by decide +kernel
theorem block005_data_flat148_original : block005_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (94062960 : Int) atom0468Coded) (CoefficientMerge.scale (105234480 : Int) atom0469Coded)) := by
  rw [block005_data_flat148_step, block005_data_flat146_original, block005_data_flat147_original]
def block005_data_flat149 : CoefficientMerge.Poly := [(nat_lit 1034, Int.ofNat (nat_lit 156846240))]
theorem block005_data_flat149_step : block005_data_flat149 = (CoefficientMerge.scale (156846240 : Int) atom0470Coded) := by decide +kernel
theorem block005_data_flat149_original : block005_data_flat149 = (CoefficientMerge.scale (156846240 : Int) atom0470Coded) := by
  rw [block005_data_flat149_step]
def block005_data_flat150 : CoefficientMerge.Poly := [(nat_lit 1044, Int.ofNat (nat_lit 59616000))]
theorem block005_data_flat150_step : block005_data_flat150 = (CoefficientMerge.scale (59616000 : Int) atom0471Coded) := by decide +kernel
theorem block005_data_flat150_original : block005_data_flat150 = (CoefficientMerge.scale (59616000 : Int) atom0471Coded) := by
  rw [block005_data_flat150_step]
def block005_data_flat151 : CoefficientMerge.Poly := [(nat_lit 1045, Int.ofNat (nat_lit 103584600))]
theorem block005_data_flat151_step : block005_data_flat151 = (CoefficientMerge.scale (103584600 : Int) atom0472Coded) := by decide +kernel
theorem block005_data_flat151_original : block005_data_flat151 = (CoefficientMerge.scale (103584600 : Int) atom0472Coded) := by
  rw [block005_data_flat151_step]
def block005_data_flat152 : CoefficientMerge.Poly := [(nat_lit 1044, Int.ofNat (nat_lit 59616000)), (nat_lit 1045, Int.ofNat (nat_lit 103584600))]
theorem block005_data_flat152_step : block005_data_flat152 = (CoefficientMerge.fastMerge block005_data_flat150 block005_data_flat151) := by decide +kernel
theorem block005_data_flat152_original : block005_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (59616000 : Int) atom0471Coded) (CoefficientMerge.scale (103584600 : Int) atom0472Coded)) := by
  rw [block005_data_flat152_step, block005_data_flat150_original, block005_data_flat151_original]
def block005_data_flat153 : CoefficientMerge.Poly := [(nat_lit 1034, Int.ofNat (nat_lit 156846240)), (nat_lit 1044, Int.ofNat (nat_lit 59616000)), (nat_lit 1045, Int.ofNat (nat_lit 103584600))]
theorem block005_data_flat153_step : block005_data_flat153 = (CoefficientMerge.fastMerge block005_data_flat149 block005_data_flat152) := by decide +kernel
theorem block005_data_flat153_original : block005_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (156846240 : Int) atom0470Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59616000 : Int) atom0471Coded) (CoefficientMerge.scale (103584600 : Int) atom0472Coded))) := by
  rw [block005_data_flat153_step, block005_data_flat149_original, block005_data_flat152_original]
def block005_data_flat154 : CoefficientMerge.Poly := [(nat_lit 1032, Int.ofNat (nat_lit 94062960)), (nat_lit 1033, Int.ofNat (nat_lit 105234480)), (nat_lit 1034, Int.ofNat (nat_lit 156846240)), (nat_lit 1044, Int.ofNat (nat_lit 59616000)), (nat_lit 1045, Int.ofNat (nat_lit 103584600))]
theorem block005_data_flat154_step : block005_data_flat154 = (CoefficientMerge.fastMerge block005_data_flat148 block005_data_flat153) := by decide +kernel
theorem block005_data_flat154_original : block005_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (94062960 : Int) atom0468Coded) (CoefficientMerge.scale (105234480 : Int) atom0469Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156846240 : Int) atom0470Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59616000 : Int) atom0471Coded) (CoefficientMerge.scale (103584600 : Int) atom0472Coded)))) := by
  rw [block005_data_flat154_step, block005_data_flat148_original, block005_data_flat153_original]
def block005_data_flat155 : CoefficientMerge.Poly := [(nat_lit 1019, Int.ofNat (nat_lit 114639840)), (nat_lit 1028, Int.ofNat (nat_lit 24301440)), (nat_lit 1029, Int.ofNat (nat_lit 70267680)), (nat_lit 1030, Int.ofNat (nat_lit 57675600)), (nat_lit 1031, Int.ofNat (nat_lit 79454880)), (nat_lit 1032, Int.ofNat (nat_lit 94062960)), (nat_lit 1033, Int.ofNat (nat_lit 105234480)), (nat_lit 1034, Int.ofNat (nat_lit 156846240)), (nat_lit 1044, Int.ofNat (nat_lit 59616000)), (nat_lit 1045, Int.ofNat (nat_lit 103584600))]
theorem block005_data_flat155_step : block005_data_flat155 = (CoefficientMerge.fastMerge block005_data_flat145 block005_data_flat154) := by decide +kernel
theorem block005_data_flat155_original : block005_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (114639840 : Int) atom0463Coded) (CoefficientMerge.scale (24301440 : Int) atom0464Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70267680 : Int) atom0465Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57675600 : Int) atom0466Coded) (CoefficientMerge.scale (79454880 : Int) atom0467Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (94062960 : Int) atom0468Coded) (CoefficientMerge.scale (105234480 : Int) atom0469Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156846240 : Int) atom0470Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59616000 : Int) atom0471Coded) (CoefficientMerge.scale (103584600 : Int) atom0472Coded))))) := by
  rw [block005_data_flat155_step, block005_data_flat145_original, block005_data_flat154_original]
def block005_data_flat156 : CoefficientMerge.Poly := [(nat_lit 1002, Int.ofNat (nat_lit 49206240)), (nat_lit 1003, Int.ofNat (nat_lit 68711040)), (nat_lit 1004, Int.ofNat (nat_lit 89836560)), (nat_lit 1012, Int.ofNat (nat_lit 14188800)), (nat_lit 1013, Int.ofNat (nat_lit 30462720)), (nat_lit 1014, Int.ofNat (nat_lit 52680000)), (nat_lit 1015, Int.ofNat (nat_lit 40726320)), (nat_lit 1016, Int.ofNat (nat_lit 56645280)), (nat_lit 1017, Int.ofNat (nat_lit 70185840)), (nat_lit 1018, Int.ofNat (nat_lit 91753680)), (nat_lit 1019, Int.ofNat (nat_lit 114639840)), (nat_lit 1028, Int.ofNat (nat_lit 24301440)), (nat_lit 1029, Int.ofNat (nat_lit 70267680)), (nat_lit 1030, Int.ofNat (nat_lit 57675600)), (nat_lit 1031, Int.ofNat (nat_lit 79454880)), (nat_lit 1032, Int.ofNat (nat_lit 94062960)), (nat_lit 1033, Int.ofNat (nat_lit 105234480)), (nat_lit 1034, Int.ofNat (nat_lit 156846240)), (nat_lit 1044, Int.ofNat (nat_lit 59616000)), (nat_lit 1045, Int.ofNat (nat_lit 103584600))]
theorem block005_data_flat156_step : block005_data_flat156 = (CoefficientMerge.fastMerge block005_data_flat136 block005_data_flat155) := by decide +kernel
theorem block005_data_flat156_original : block005_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49206240 : Int) atom0453Coded) (CoefficientMerge.scale (68711040 : Int) atom0454Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89836560 : Int) atom0455Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14188800 : Int) atom0456Coded) (CoefficientMerge.scale (30462720 : Int) atom0457Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52680000 : Int) atom0458Coded) (CoefficientMerge.scale (40726320 : Int) atom0459Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56645280 : Int) atom0460Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70185840 : Int) atom0461Coded) (CoefficientMerge.scale (91753680 : Int) atom0462Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (114639840 : Int) atom0463Coded) (CoefficientMerge.scale (24301440 : Int) atom0464Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70267680 : Int) atom0465Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57675600 : Int) atom0466Coded) (CoefficientMerge.scale (79454880 : Int) atom0467Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (94062960 : Int) atom0468Coded) (CoefficientMerge.scale (105234480 : Int) atom0469Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156846240 : Int) atom0470Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59616000 : Int) atom0471Coded) (CoefficientMerge.scale (103584600 : Int) atom0472Coded)))))) := by
  rw [block005_data_flat156_step, block005_data_flat136_original, block005_data_flat155_original]
def block005_data_flat157 : CoefficientMerge.Poly := [(nat_lit 883, Int.ofNat (nat_lit 15264720)), (nat_lit 884, Int.ofNat (nat_lit 99311130)), (nat_lit 899, Int.ofNat (nat_lit 79701570)), (nat_lit 964, Int.ofNat (nat_lit 2931840)), (nat_lit 969, Int.ofNat (nat_lit 19845360)), (nat_lit 971, Int.ofNat (nat_lit 221760)), (nat_lit 982, Int.ofNat (nat_lit 1900800)), (nat_lit 983, Int.ofNat (nat_lit 3801600)), (nat_lit 984, Int.ofNat (nat_lit 33785280)), (nat_lit 985, Int.ofNat (nat_lit 4849920)), (nat_lit 986, Int.ofNat (nat_lit 11026080)), (nat_lit 987, Int.ofNat (nat_lit 22376160)), (nat_lit 988, Int.ofNat (nat_lit 37272960)), (nat_lit 989, Int.ofNat (nat_lit 54092880)), (nat_lit 996, Int.ofNat (nat_lit 5466240)), (nat_lit 997, Int.ofNat (nat_lit 13541760)), (nat_lit 998, Int.ofNat (nat_lit 16151040)), (nat_lit 999, Int.ofNat (nat_lit 42252480)), (nat_lit 1000, Int.ofNat (nat_lit 23506560)), (nat_lit 1001, Int.ofNat (nat_lit 33835680)), (nat_lit 1002, Int.ofNat (nat_lit 49206240)), (nat_lit 1003, Int.ofNat (nat_lit 68711040)), (nat_lit 1004, Int.ofNat (nat_lit 89836560)), (nat_lit 1012, Int.ofNat (nat_lit 14188800)), (nat_lit 1013, Int.ofNat (nat_lit 30462720)), (nat_lit 1014, Int.ofNat (nat_lit 52680000)), (nat_lit 1015, Int.ofNat (nat_lit 40726320)), (nat_lit 1016, Int.ofNat (nat_lit 56645280)), (nat_lit 1017, Int.ofNat (nat_lit 70185840)), (nat_lit 1018, Int.ofNat (nat_lit 91753680)), (nat_lit 1019, Int.ofNat (nat_lit 114639840)), (nat_lit 1028, Int.ofNat (nat_lit 24301440)), (nat_lit 1029, Int.ofNat (nat_lit 70267680)), (nat_lit 1030, Int.ofNat (nat_lit 57675600)), (nat_lit 1031, Int.ofNat (nat_lit 79454880)), (nat_lit 1032, Int.ofNat (nat_lit 94062960)), (nat_lit 1033, Int.ofNat (nat_lit 105234480)), (nat_lit 1034, Int.ofNat (nat_lit 156846240)), (nat_lit 1044, Int.ofNat (nat_lit 59616000)), (nat_lit 1045, Int.ofNat (nat_lit 103584600))]
theorem block005_data_flat157_step : block005_data_flat157 = (CoefficientMerge.fastMerge block005_data_flat117 block005_data_flat156) := by decide +kernel
theorem block005_data_flat157_original : block005_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15264720 : Int) atom0433Coded) (CoefficientMerge.scale (99311130 : Int) atom0434Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79701570 : Int) atom0435Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2931840 : Int) atom0436Coded) (CoefficientMerge.scale (19845360 : Int) atom0437Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (221760 : Int) atom0438Coded) (CoefficientMerge.scale (1900800 : Int) atom0439Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3801600 : Int) atom0440Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33785280 : Int) atom0441Coded) (CoefficientMerge.scale (4849920 : Int) atom0442Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11026080 : Int) atom0443Coded) (CoefficientMerge.scale (22376160 : Int) atom0444Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37272960 : Int) atom0445Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54092880 : Int) atom0446Coded) (CoefficientMerge.scale (5466240 : Int) atom0447Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13541760 : Int) atom0448Coded) (CoefficientMerge.scale (16151040 : Int) atom0449Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42252480 : Int) atom0450Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23506560 : Int) atom0451Coded) (CoefficientMerge.scale (33835680 : Int) atom0452Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49206240 : Int) atom0453Coded) (CoefficientMerge.scale (68711040 : Int) atom0454Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89836560 : Int) atom0455Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14188800 : Int) atom0456Coded) (CoefficientMerge.scale (30462720 : Int) atom0457Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52680000 : Int) atom0458Coded) (CoefficientMerge.scale (40726320 : Int) atom0459Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56645280 : Int) atom0460Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70185840 : Int) atom0461Coded) (CoefficientMerge.scale (91753680 : Int) atom0462Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (114639840 : Int) atom0463Coded) (CoefficientMerge.scale (24301440 : Int) atom0464Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70267680 : Int) atom0465Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57675600 : Int) atom0466Coded) (CoefficientMerge.scale (79454880 : Int) atom0467Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (94062960 : Int) atom0468Coded) (CoefficientMerge.scale (105234480 : Int) atom0469Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156846240 : Int) atom0470Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59616000 : Int) atom0471Coded) (CoefficientMerge.scale (103584600 : Int) atom0472Coded))))))) := by
  rw [block005_data_flat157_step, block005_data_flat117_original, block005_data_flat156_original]
def block005_data_flat158 : CoefficientMerge.Poly := [(nat_lit 773, Int.ofNat (nat_lit 35700480)), (nat_lit 774, Int.ofNat (nat_lit 72161280)), (nat_lit 775, Int.ofNat (nat_lit 50591520)), (nat_lit 776, Int.ofNat (nat_lit 70005600)), (nat_lit 777, Int.ofNat (nat_lit 76122720)), (nat_lit 778, Int.ofNat (nat_lit 92435040)), (nat_lit 779, Int.ofNat (nat_lit 108747360)), (nat_lit 787, Int.ofNat (nat_lit 25864320)), (nat_lit 788, Int.ofNat (nat_lit 52137600)), (nat_lit 789, Int.ofNat (nat_lit 82087680)), (nat_lit 790, Int.ofNat (nat_lit 64683600)), (nat_lit 791, Int.ofNat (nat_lit 87060960)), (nat_lit 792, Int.ofNat (nat_lit 89438640)), (nat_lit 793, Int.ofNat (nat_lit 105904560)), (nat_lit 794, Int.ofNat (nat_lit 122426640)), (nat_lit 803, Int.ofNat (nat_lit 36201600)), (nat_lit 804, Int.ofNat (nat_lit 99174240)), (nat_lit 805, Int.ofNat (nat_lit 78505200)), (nat_lit 806, Int.ofNat (nat_lit 104116320)), (nat_lit 807, Int.ofNat (nat_lit 105652080)), (nat_lit 808, Int.ofNat (nat_lit 109812240)), (nat_lit 809, Int.ofNat (nat_lit 153509040)), (nat_lit 819, Int.ofNat (nat_lit 74908800)), (nat_lit 820, Int.ofNat (nat_lit 124263720)), (nat_lit 821, Int.ofNat (nat_lit 176277600)), (nat_lit 822, Int.ofNat (nat_lit 180672120)), (nat_lit 823, Int.ofNat (nat_lit 113707800)), (nat_lit 824, Int.ofNat (nat_lit 182823480)), (nat_lit 835, Int.ofNat (nat_lit 57262464)), (nat_lit 836, Int.ofNat (nat_lit 145208160)), (nat_lit 837, Int.ofNat (nat_lit 171628740)), (nat_lit 838, Int.ofNat (nat_lit 121886640)), (nat_lit 839, Int.ofNat (nat_lit 154082790)), (nat_lit 851, Int.ofNat (nat_lit 98175240)), (nat_lit 852, Int.ofNat (nat_lit 171553680)), (nat_lit 853, Int.ofNat (nat_lit 120222360)), (nat_lit 854, Int.ofNat (nat_lit 170511480)), (nat_lit 867, Int.ofNat (nat_lit 64707660)), (nat_lit 868, Int.ofNat (nat_lit 94666860)), (nat_lit 869, Int.ofNat (nat_lit 155708190)), (nat_lit 883, Int.ofNat (nat_lit 15264720)), (nat_lit 884, Int.ofNat (nat_lit 99311130)), (nat_lit 899, Int.ofNat (nat_lit 79701570)), (nat_lit 964, Int.ofNat (nat_lit 2931840)), (nat_lit 969, Int.ofNat (nat_lit 19845360)), (nat_lit 971, Int.ofNat (nat_lit 221760)), (nat_lit 982, Int.ofNat (nat_lit 1900800)), (nat_lit 983, Int.ofNat (nat_lit 3801600)), (nat_lit 984, Int.ofNat (nat_lit 33785280)), (nat_lit 985, Int.ofNat (nat_lit 4849920)), (nat_lit 986, Int.ofNat (nat_lit 11026080)), (nat_lit 987, Int.ofNat (nat_lit 22376160)), (nat_lit 988, Int.ofNat (nat_lit 37272960)), (nat_lit 989, Int.ofNat (nat_lit 54092880)), (nat_lit 996, Int.ofNat (nat_lit 5466240)), (nat_lit 997, Int.ofNat (nat_lit 13541760)), (nat_lit 998, Int.ofNat (nat_lit 16151040)), (nat_lit 999, Int.ofNat (nat_lit 42252480)), (nat_lit 1000, Int.ofNat (nat_lit 23506560)), (nat_lit 1001, Int.ofNat (nat_lit 33835680)), (nat_lit 1002, Int.ofNat (nat_lit 49206240)), (nat_lit 1003, Int.ofNat (nat_lit 68711040)), (nat_lit 1004, Int.ofNat (nat_lit 89836560)), (nat_lit 1012, Int.ofNat (nat_lit 14188800)), (nat_lit 1013, Int.ofNat (nat_lit 30462720)), (nat_lit 1014, Int.ofNat (nat_lit 52680000)), (nat_lit 1015, Int.ofNat (nat_lit 40726320)), (nat_lit 1016, Int.ofNat (nat_lit 56645280)), (nat_lit 1017, Int.ofNat (nat_lit 70185840)), (nat_lit 1018, Int.ofNat (nat_lit 91753680)), (nat_lit 1019, Int.ofNat (nat_lit 114639840)), (nat_lit 1028, Int.ofNat (nat_lit 24301440)), (nat_lit 1029, Int.ofNat (nat_lit 70267680)), (nat_lit 1030, Int.ofNat (nat_lit 57675600)), (nat_lit 1031, Int.ofNat (nat_lit 79454880)), (nat_lit 1032, Int.ofNat (nat_lit 94062960)), (nat_lit 1033, Int.ofNat (nat_lit 105234480)), (nat_lit 1034, Int.ofNat (nat_lit 156846240)), (nat_lit 1044, Int.ofNat (nat_lit 59616000)), (nat_lit 1045, Int.ofNat (nat_lit 103584600))]
theorem block005_data_flat158_step : block005_data_flat158 = (CoefficientMerge.fastMerge block005_data_flat078 block005_data_flat157) := by decide +kernel
theorem block005_data_flat158_original : block005_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35700480 : Int) atom0393Coded) (CoefficientMerge.scale (72161280 : Int) atom0394Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50591520 : Int) atom0395Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70005600 : Int) atom0396Coded) (CoefficientMerge.scale (76122720 : Int) atom0397Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (92435040 : Int) atom0398Coded) (CoefficientMerge.scale (108747360 : Int) atom0399Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25864320 : Int) atom0400Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52137600 : Int) atom0401Coded) (CoefficientMerge.scale (82087680 : Int) atom0402Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64683600 : Int) atom0403Coded) (CoefficientMerge.scale (87060960 : Int) atom0404Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89438640 : Int) atom0405Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105904560 : Int) atom0406Coded) (CoefficientMerge.scale (122426640 : Int) atom0407Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36201600 : Int) atom0408Coded) (CoefficientMerge.scale (99174240 : Int) atom0409Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (78505200 : Int) atom0410Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104116320 : Int) atom0411Coded) (CoefficientMerge.scale (105652080 : Int) atom0412Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (109812240 : Int) atom0413Coded) (CoefficientMerge.scale (153509040 : Int) atom0414Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74908800 : Int) atom0415Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (124263720 : Int) atom0416Coded) (CoefficientMerge.scale (176277600 : Int) atom0417Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (180672120 : Int) atom0418Coded) (CoefficientMerge.scale (113707800 : Int) atom0419Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182823480 : Int) atom0420Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57262464 : Int) atom0421Coded) (CoefficientMerge.scale (145208160 : Int) atom0422Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (171628740 : Int) atom0423Coded) (CoefficientMerge.scale (121886640 : Int) atom0424Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154082790 : Int) atom0425Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98175240 : Int) atom0426Coded) (CoefficientMerge.scale (171553680 : Int) atom0427Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120222360 : Int) atom0428Coded) (CoefficientMerge.scale (170511480 : Int) atom0429Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64707660 : Int) atom0430Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94666860 : Int) atom0431Coded) (CoefficientMerge.scale (155708190 : Int) atom0432Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15264720 : Int) atom0433Coded) (CoefficientMerge.scale (99311130 : Int) atom0434Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79701570 : Int) atom0435Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2931840 : Int) atom0436Coded) (CoefficientMerge.scale (19845360 : Int) atom0437Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (221760 : Int) atom0438Coded) (CoefficientMerge.scale (1900800 : Int) atom0439Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3801600 : Int) atom0440Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33785280 : Int) atom0441Coded) (CoefficientMerge.scale (4849920 : Int) atom0442Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11026080 : Int) atom0443Coded) (CoefficientMerge.scale (22376160 : Int) atom0444Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37272960 : Int) atom0445Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54092880 : Int) atom0446Coded) (CoefficientMerge.scale (5466240 : Int) atom0447Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13541760 : Int) atom0448Coded) (CoefficientMerge.scale (16151040 : Int) atom0449Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42252480 : Int) atom0450Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23506560 : Int) atom0451Coded) (CoefficientMerge.scale (33835680 : Int) atom0452Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49206240 : Int) atom0453Coded) (CoefficientMerge.scale (68711040 : Int) atom0454Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89836560 : Int) atom0455Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14188800 : Int) atom0456Coded) (CoefficientMerge.scale (30462720 : Int) atom0457Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52680000 : Int) atom0458Coded) (CoefficientMerge.scale (40726320 : Int) atom0459Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56645280 : Int) atom0460Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70185840 : Int) atom0461Coded) (CoefficientMerge.scale (91753680 : Int) atom0462Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (114639840 : Int) atom0463Coded) (CoefficientMerge.scale (24301440 : Int) atom0464Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70267680 : Int) atom0465Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57675600 : Int) atom0466Coded) (CoefficientMerge.scale (79454880 : Int) atom0467Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (94062960 : Int) atom0468Coded) (CoefficientMerge.scale (105234480 : Int) atom0469Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156846240 : Int) atom0470Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59616000 : Int) atom0471Coded) (CoefficientMerge.scale (103584600 : Int) atom0472Coded)))))))) := by
  rw [block005_data_flat158_step, block005_data_flat078_original, block005_data_flat157_original]
def block005_data_flat159 : CoefficientMerge.Poly := [(nat_lit 773, Int.ofNat (nat_lit 35700480)), (nat_lit 774, Int.ofNat (nat_lit 72161280)), (nat_lit 775, Int.ofNat (nat_lit 50591520)), (nat_lit 776, Int.ofNat (nat_lit 70005600)), (nat_lit 777, Int.ofNat (nat_lit 76122720)), (nat_lit 778, Int.ofNat (nat_lit 92435040)), (nat_lit 779, Int.ofNat (nat_lit 108747360)), (nat_lit 787, Int.ofNat (nat_lit 25864320)), (nat_lit 788, Int.ofNat (nat_lit 52137600)), (nat_lit 789, Int.ofNat (nat_lit 82087680)), (nat_lit 790, Int.ofNat (nat_lit 64683600)), (nat_lit 791, Int.ofNat (nat_lit 87060960)), (nat_lit 792, Int.ofNat (nat_lit 89438640)), (nat_lit 793, Int.ofNat (nat_lit 105904560)), (nat_lit 794, Int.ofNat (nat_lit 122426640)), (nat_lit 803, Int.ofNat (nat_lit 36201600)), (nat_lit 804, Int.ofNat (nat_lit 99174240)), (nat_lit 805, Int.ofNat (nat_lit 78505200)), (nat_lit 806, Int.ofNat (nat_lit 104116320)), (nat_lit 807, Int.ofNat (nat_lit 105652080)), (nat_lit 808, Int.ofNat (nat_lit 109812240)), (nat_lit 809, Int.ofNat (nat_lit 153509040)), (nat_lit 819, Int.ofNat (nat_lit 74908800)), (nat_lit 820, Int.ofNat (nat_lit 124263720)), (nat_lit 821, Int.ofNat (nat_lit 176277600)), (nat_lit 822, Int.ofNat (nat_lit 180672120)), (nat_lit 823, Int.ofNat (nat_lit 113707800)), (nat_lit 824, Int.ofNat (nat_lit 182823480)), (nat_lit 835, Int.ofNat (nat_lit 57262464)), (nat_lit 836, Int.ofNat (nat_lit 145208160)), (nat_lit 837, Int.ofNat (nat_lit 171628740)), (nat_lit 838, Int.ofNat (nat_lit 121886640)), (nat_lit 839, Int.ofNat (nat_lit 154082790)), (nat_lit 851, Int.ofNat (nat_lit 98175240)), (nat_lit 852, Int.ofNat (nat_lit 171553680)), (nat_lit 853, Int.ofNat (nat_lit 120222360)), (nat_lit 854, Int.ofNat (nat_lit 170511480)), (nat_lit 867, Int.ofNat (nat_lit 64707660)), (nat_lit 868, Int.ofNat (nat_lit 94666860)), (nat_lit 869, Int.ofNat (nat_lit 155708190)), (nat_lit 883, Int.ofNat (nat_lit 15264720)), (nat_lit 884, Int.ofNat (nat_lit 99311130)), (nat_lit 899, Int.ofNat (nat_lit 79701570)), (nat_lit 964, Int.ofNat (nat_lit 2931840)), (nat_lit 969, Int.ofNat (nat_lit 19845360)), (nat_lit 971, Int.ofNat (nat_lit 221760)), (nat_lit 982, Int.ofNat (nat_lit 1900800)), (nat_lit 983, Int.ofNat (nat_lit 3801600)), (nat_lit 984, Int.ofNat (nat_lit 33785280)), (nat_lit 985, Int.ofNat (nat_lit 4849920)), (nat_lit 986, Int.ofNat (nat_lit 11026080)), (nat_lit 987, Int.ofNat (nat_lit 22376160)), (nat_lit 988, Int.ofNat (nat_lit 37272960)), (nat_lit 989, Int.ofNat (nat_lit 54092880)), (nat_lit 996, Int.ofNat (nat_lit 5466240)), (nat_lit 997, Int.ofNat (nat_lit 13541760)), (nat_lit 998, Int.ofNat (nat_lit 16151040)), (nat_lit 999, Int.ofNat (nat_lit 42252480)), (nat_lit 1000, Int.ofNat (nat_lit 23506560)), (nat_lit 1001, Int.ofNat (nat_lit 33835680)), (nat_lit 1002, Int.ofNat (nat_lit 49206240)), (nat_lit 1003, Int.ofNat (nat_lit 68711040)), (nat_lit 1004, Int.ofNat (nat_lit 89836560)), (nat_lit 1012, Int.ofNat (nat_lit 14188800)), (nat_lit 1013, Int.ofNat (nat_lit 30462720)), (nat_lit 1014, Int.ofNat (nat_lit 52680000)), (nat_lit 1015, Int.ofNat (nat_lit 40726320)), (nat_lit 1016, Int.ofNat (nat_lit 56645280)), (nat_lit 1017, Int.ofNat (nat_lit 70185840)), (nat_lit 1018, Int.ofNat (nat_lit 91753680)), (nat_lit 1019, Int.ofNat (nat_lit 114639840)), (nat_lit 1028, Int.ofNat (nat_lit 24301440)), (nat_lit 1029, Int.ofNat (nat_lit 70267680)), (nat_lit 1030, Int.ofNat (nat_lit 57675600)), (nat_lit 1031, Int.ofNat (nat_lit 79454880)), (nat_lit 1032, Int.ofNat (nat_lit 94062960)), (nat_lit 1033, Int.ofNat (nat_lit 105234480)), (nat_lit 1034, Int.ofNat (nat_lit 156846240)), (nat_lit 1044, Int.ofNat (nat_lit 59616000)), (nat_lit 1045, Int.ofNat (nat_lit 103584600))]
theorem block005_data_flat159_step : block005_data_flat159 = (CoefficientMerge.trim block005_data_flat158) := by decide +kernel
theorem block005_data_flat159_original : block005_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35700480 : Int) atom0393Coded) (CoefficientMerge.scale (72161280 : Int) atom0394Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50591520 : Int) atom0395Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70005600 : Int) atom0396Coded) (CoefficientMerge.scale (76122720 : Int) atom0397Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (92435040 : Int) atom0398Coded) (CoefficientMerge.scale (108747360 : Int) atom0399Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25864320 : Int) atom0400Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52137600 : Int) atom0401Coded) (CoefficientMerge.scale (82087680 : Int) atom0402Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64683600 : Int) atom0403Coded) (CoefficientMerge.scale (87060960 : Int) atom0404Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89438640 : Int) atom0405Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105904560 : Int) atom0406Coded) (CoefficientMerge.scale (122426640 : Int) atom0407Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36201600 : Int) atom0408Coded) (CoefficientMerge.scale (99174240 : Int) atom0409Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (78505200 : Int) atom0410Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104116320 : Int) atom0411Coded) (CoefficientMerge.scale (105652080 : Int) atom0412Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (109812240 : Int) atom0413Coded) (CoefficientMerge.scale (153509040 : Int) atom0414Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74908800 : Int) atom0415Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (124263720 : Int) atom0416Coded) (CoefficientMerge.scale (176277600 : Int) atom0417Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (180672120 : Int) atom0418Coded) (CoefficientMerge.scale (113707800 : Int) atom0419Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182823480 : Int) atom0420Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57262464 : Int) atom0421Coded) (CoefficientMerge.scale (145208160 : Int) atom0422Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (171628740 : Int) atom0423Coded) (CoefficientMerge.scale (121886640 : Int) atom0424Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154082790 : Int) atom0425Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98175240 : Int) atom0426Coded) (CoefficientMerge.scale (171553680 : Int) atom0427Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120222360 : Int) atom0428Coded) (CoefficientMerge.scale (170511480 : Int) atom0429Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64707660 : Int) atom0430Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94666860 : Int) atom0431Coded) (CoefficientMerge.scale (155708190 : Int) atom0432Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15264720 : Int) atom0433Coded) (CoefficientMerge.scale (99311130 : Int) atom0434Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79701570 : Int) atom0435Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2931840 : Int) atom0436Coded) (CoefficientMerge.scale (19845360 : Int) atom0437Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (221760 : Int) atom0438Coded) (CoefficientMerge.scale (1900800 : Int) atom0439Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3801600 : Int) atom0440Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33785280 : Int) atom0441Coded) (CoefficientMerge.scale (4849920 : Int) atom0442Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11026080 : Int) atom0443Coded) (CoefficientMerge.scale (22376160 : Int) atom0444Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37272960 : Int) atom0445Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54092880 : Int) atom0446Coded) (CoefficientMerge.scale (5466240 : Int) atom0447Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13541760 : Int) atom0448Coded) (CoefficientMerge.scale (16151040 : Int) atom0449Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42252480 : Int) atom0450Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23506560 : Int) atom0451Coded) (CoefficientMerge.scale (33835680 : Int) atom0452Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49206240 : Int) atom0453Coded) (CoefficientMerge.scale (68711040 : Int) atom0454Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89836560 : Int) atom0455Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14188800 : Int) atom0456Coded) (CoefficientMerge.scale (30462720 : Int) atom0457Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52680000 : Int) atom0458Coded) (CoefficientMerge.scale (40726320 : Int) atom0459Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56645280 : Int) atom0460Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70185840 : Int) atom0461Coded) (CoefficientMerge.scale (91753680 : Int) atom0462Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (114639840 : Int) atom0463Coded) (CoefficientMerge.scale (24301440 : Int) atom0464Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70267680 : Int) atom0465Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57675600 : Int) atom0466Coded) (CoefficientMerge.scale (79454880 : Int) atom0467Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (94062960 : Int) atom0468Coded) (CoefficientMerge.scale (105234480 : Int) atom0469Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156846240 : Int) atom0470Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59616000 : Int) atom0471Coded) (CoefficientMerge.scale (103584600 : Int) atom0472Coded))))))))) := by
  rw [block005_data_flat159_step, block005_data_flat158_original]
theorem block005_data : block005 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35700480 : Int) atom0393Coded) (CoefficientMerge.scale (72161280 : Int) atom0394Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50591520 : Int) atom0395Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70005600 : Int) atom0396Coded) (CoefficientMerge.scale (76122720 : Int) atom0397Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (92435040 : Int) atom0398Coded) (CoefficientMerge.scale (108747360 : Int) atom0399Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25864320 : Int) atom0400Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52137600 : Int) atom0401Coded) (CoefficientMerge.scale (82087680 : Int) atom0402Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (64683600 : Int) atom0403Coded) (CoefficientMerge.scale (87060960 : Int) atom0404Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89438640 : Int) atom0405Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (105904560 : Int) atom0406Coded) (CoefficientMerge.scale (122426640 : Int) atom0407Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36201600 : Int) atom0408Coded) (CoefficientMerge.scale (99174240 : Int) atom0409Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (78505200 : Int) atom0410Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104116320 : Int) atom0411Coded) (CoefficientMerge.scale (105652080 : Int) atom0412Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (109812240 : Int) atom0413Coded) (CoefficientMerge.scale (153509040 : Int) atom0414Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74908800 : Int) atom0415Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (124263720 : Int) atom0416Coded) (CoefficientMerge.scale (176277600 : Int) atom0417Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (180672120 : Int) atom0418Coded) (CoefficientMerge.scale (113707800 : Int) atom0419Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (182823480 : Int) atom0420Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57262464 : Int) atom0421Coded) (CoefficientMerge.scale (145208160 : Int) atom0422Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (171628740 : Int) atom0423Coded) (CoefficientMerge.scale (121886640 : Int) atom0424Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154082790 : Int) atom0425Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (98175240 : Int) atom0426Coded) (CoefficientMerge.scale (171553680 : Int) atom0427Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (120222360 : Int) atom0428Coded) (CoefficientMerge.scale (170511480 : Int) atom0429Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (64707660 : Int) atom0430Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (94666860 : Int) atom0431Coded) (CoefficientMerge.scale (155708190 : Int) atom0432Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15264720 : Int) atom0433Coded) (CoefficientMerge.scale (99311130 : Int) atom0434Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79701570 : Int) atom0435Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2931840 : Int) atom0436Coded) (CoefficientMerge.scale (19845360 : Int) atom0437Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (221760 : Int) atom0438Coded) (CoefficientMerge.scale (1900800 : Int) atom0439Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3801600 : Int) atom0440Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33785280 : Int) atom0441Coded) (CoefficientMerge.scale (4849920 : Int) atom0442Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11026080 : Int) atom0443Coded) (CoefficientMerge.scale (22376160 : Int) atom0444Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37272960 : Int) atom0445Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54092880 : Int) atom0446Coded) (CoefficientMerge.scale (5466240 : Int) atom0447Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13541760 : Int) atom0448Coded) (CoefficientMerge.scale (16151040 : Int) atom0449Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42252480 : Int) atom0450Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23506560 : Int) atom0451Coded) (CoefficientMerge.scale (33835680 : Int) atom0452Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49206240 : Int) atom0453Coded) (CoefficientMerge.scale (68711040 : Int) atom0454Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89836560 : Int) atom0455Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14188800 : Int) atom0456Coded) (CoefficientMerge.scale (30462720 : Int) atom0457Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52680000 : Int) atom0458Coded) (CoefficientMerge.scale (40726320 : Int) atom0459Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56645280 : Int) atom0460Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70185840 : Int) atom0461Coded) (CoefficientMerge.scale (91753680 : Int) atom0462Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (114639840 : Int) atom0463Coded) (CoefficientMerge.scale (24301440 : Int) atom0464Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70267680 : Int) atom0465Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57675600 : Int) atom0466Coded) (CoefficientMerge.scale (79454880 : Int) atom0467Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (94062960 : Int) atom0468Coded) (CoefficientMerge.scale (105234480 : Int) atom0469Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156846240 : Int) atom0470Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59616000 : Int) atom0471Coded) (CoefficientMerge.scale (103584600 : Int) atom0472Coded)))))))) := by
  have h : block005 = block005_data_flat159 := by decide +kernel
  exact h.trans block005_data_flat159_original
theorem block005_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) block005 := by
  rw [block005_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0393Coded_nonneg g hg hA hB) (atom0394Coded_nonneg g hg hA hB)) (add_nonneg (atom0395Coded_nonneg g hg hA hB) (add_nonneg (atom0396Coded_nonneg g hg hA hB) (atom0397Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0398Coded_nonneg g hg hA hB) (atom0399Coded_nonneg g hg hA hB)) (add_nonneg (atom0400Coded_nonneg g hg hA hB) (add_nonneg (atom0401Coded_nonneg g hg hA hB) (atom0402Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0403Coded_nonneg g hg hA hB) (atom0404Coded_nonneg g hg hA hB)) (add_nonneg (atom0405Coded_nonneg g hg hA hB) (add_nonneg (atom0406Coded_nonneg g hg hA hB) (atom0407Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0408Coded_nonneg g hg hA hB) (atom0409Coded_nonneg g hg hA hB)) (add_nonneg (atom0410Coded_nonneg g hg hA hB) (add_nonneg (atom0411Coded_nonneg g hg hA hB) (atom0412Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0413Coded_nonneg g hg hA hB) (atom0414Coded_nonneg g hg hA hB)) (add_nonneg (atom0415Coded_nonneg g hg hA hB) (add_nonneg (atom0416Coded_nonneg g hg hA hB) (atom0417Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0418Coded_nonneg g hg hA hB) (atom0419Coded_nonneg g hg hA hB)) (add_nonneg (atom0420Coded_nonneg g hg hA hB) (add_nonneg (atom0421Coded_nonneg g hg hA hB) (atom0422Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0423Coded_nonneg g hg hA hB) (atom0424Coded_nonneg g hg hA hB)) (add_nonneg (atom0425Coded_nonneg g hg hA hB) (add_nonneg (atom0426Coded_nonneg g hg hA hB) (atom0427Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0428Coded_nonneg g hg hA hB) (atom0429Coded_nonneg g hg hA hB)) (add_nonneg (atom0430Coded_nonneg g hg hA hB) (add_nonneg (atom0431Coded_nonneg g hg hA hB) (atom0432Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0433Coded_nonneg g hg hA hB) (atom0434Coded_nonneg g hg hA hB)) (add_nonneg (atom0435Coded_nonneg g hg hA hB) (add_nonneg (atom0436Coded_nonneg g hg hA hB) (atom0437Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0438Coded_nonneg g hg hA hB) (atom0439Coded_nonneg g hg hA hB)) (add_nonneg (atom0440Coded_nonneg g hg hA hB) (add_nonneg (atom0441Coded_nonneg g hg hA hB) (atom0442Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0443Coded_nonneg g hg hA hB) (atom0444Coded_nonneg g hg hA hB)) (add_nonneg (atom0445Coded_nonneg g hg hA hB) (add_nonneg (atom0446Coded_nonneg g hg hA hB) (atom0447Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0448Coded_nonneg g hg hA hB) (atom0449Coded_nonneg g hg hA hB)) (add_nonneg (atom0450Coded_nonneg g hg hA hB) (add_nonneg (atom0451Coded_nonneg g hg hA hB) (atom0452Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0453Coded_nonneg g hg hA hB) (atom0454Coded_nonneg g hg hA hB)) (add_nonneg (atom0455Coded_nonneg g hg hA hB) (add_nonneg (atom0456Coded_nonneg g hg hA hB) (atom0457Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0458Coded_nonneg g hg hA hB) (atom0459Coded_nonneg g hg hA hB)) (add_nonneg (atom0460Coded_nonneg g hg hA hB) (add_nonneg (atom0461Coded_nonneg g hg hA hB) (atom0462Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0463Coded_nonneg g hg hA hB) (atom0464Coded_nonneg g hg hA hB)) (add_nonneg (atom0465Coded_nonneg g hg hA hB) (add_nonneg (atom0466Coded_nonneg g hg hA hB) (atom0467Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0468Coded_nonneg g hg hA hB) (atom0469Coded_nonneg g hg hA hB)) (add_nonneg (atom0470Coded_nonneg g hg hA hB) (add_nonneg (atom0471Coded_nonneg g hg hA hB) (atom0472Coded_nonneg g hg hA hB))))))))

end APPT.Finite15
