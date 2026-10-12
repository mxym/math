-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def atom0633 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0633 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0633 = ((g 9) * (g 10) * (g 12)) := by
  norm_num [atom0633, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0633_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (202089600 : Int) atom0633) := by
  rw [SparsePolynomial.eval_scale, eval_atom0633]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0633Coded : CoefficientMerge.Poly := [(nat_lit 2187, Int.ofNat (nat_lit 1))]
theorem atom0633Coded_decode : atom0633 = SparsePolynomial.decodeCubic 15 atom0633Coded := by decide +kernel
theorem atom0633Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (202089600 : Int) atom0633Coded) := by
  have h := atom0633_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0633Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0634 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0634 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0634 = ((g 9) * (g 10) * (g 13)) := by
  norm_num [atom0634, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0634_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (147225600 : Int) atom0634) := by
  rw [SparsePolynomial.eval_scale, eval_atom0634]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0634Coded : CoefficientMerge.Poly := [(nat_lit 2188, Int.ofNat (nat_lit 1))]
theorem atom0634Coded_decode : atom0634 = SparsePolynomial.decodeCubic 15 atom0634Coded := by decide +kernel
theorem atom0634Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (147225600 : Int) atom0634Coded) := by
  have h := atom0634_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0634Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0635 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0635 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0635 = ((g 9) * (g 10) * (g 14)) := by
  norm_num [atom0635, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0635_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (228441600 : Int) atom0635) := by
  rw [SparsePolynomial.eval_scale, eval_atom0635]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0635Coded : CoefficientMerge.Poly := [(nat_lit 2189, Int.ofNat (nat_lit 1))]
theorem atom0635Coded_decode : atom0635 = SparsePolynomial.decodeCubic 15 atom0635Coded := by decide +kernel
theorem atom0635Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (228441600 : Int) atom0635Coded) := by
  have h := atom0635_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0635Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0636 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0636 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0636 = ((g 9) * (g 11) * (g 11)) := by
  norm_num [atom0636, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0636_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101130120 : Int) atom0636) := by
  rw [SparsePolynomial.eval_scale, eval_atom0636]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0636Coded : CoefficientMerge.Poly := [(nat_lit 2201, Int.ofNat (nat_lit 1))]
theorem atom0636Coded_decode : atom0636 = SparsePolynomial.decodeCubic 15 atom0636Coded := by decide +kernel
theorem atom0636Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (101130120 : Int) atom0636Coded) := by
  have h := atom0636_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0636Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0637 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0637 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0637 = ((g 9) * (g 11) * (g 12)) := by
  norm_num [atom0637, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0637_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (235482120 : Int) atom0637) := by
  rw [SparsePolynomial.eval_scale, eval_atom0637]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0637Coded : CoefficientMerge.Poly := [(nat_lit 2202, Int.ofNat (nat_lit 1))]
theorem atom0637Coded_decode : atom0637 = SparsePolynomial.decodeCubic 15 atom0637Coded := by decide +kernel
theorem atom0637Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (235482120 : Int) atom0637Coded) := by
  have h := atom0637_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0637Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0638 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0638 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0638 = ((g 9) * (g 11) * (g 13)) := by
  norm_num [atom0638, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0638_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (199784880 : Int) atom0638) := by
  rw [SparsePolynomial.eval_scale, eval_atom0638]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0638Coded : CoefficientMerge.Poly := [(nat_lit 2203, Int.ofNat (nat_lit 1))]
theorem atom0638Coded_decode : atom0638 = SparsePolynomial.decodeCubic 15 atom0638Coded := by decide +kernel
theorem atom0638Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (199784880 : Int) atom0638Coded) := by
  have h := atom0638_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0638Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0639 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0639 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0639 = ((g 9) * (g 11) * (g 14)) := by
  norm_num [atom0639, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0639_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (213034320 : Int) atom0639) := by
  rw [SparsePolynomial.eval_scale, eval_atom0639]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0639Coded : CoefficientMerge.Poly := [(nat_lit 2204, Int.ofNat (nat_lit 1))]
theorem atom0639Coded_decode : atom0639 = SparsePolynomial.decodeCubic 15 atom0639Coded := by decide +kernel
theorem atom0639Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (213034320 : Int) atom0639Coded) := by
  have h := atom0639_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0639Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0640 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0640 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0640 = ((g 9) * (g 12) * (g 12)) := by
  norm_num [atom0640, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0640_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (115344000 : Int) atom0640) := by
  rw [SparsePolynomial.eval_scale, eval_atom0640]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0640Coded : CoefficientMerge.Poly := [(nat_lit 2217, Int.ofNat (nat_lit 1))]
theorem atom0640Coded_decode : atom0640 = SparsePolynomial.decodeCubic 15 atom0640Coded := by decide +kernel
theorem atom0640Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (115344000 : Int) atom0640Coded) := by
  have h := atom0640_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0640Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0641 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0641 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0641 = ((g 9) * (g 12) * (g 13)) := by
  norm_num [atom0641, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0641_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (226886400 : Int) atom0641) := by
  rw [SparsePolynomial.eval_scale, eval_atom0641]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0641Coded : CoefficientMerge.Poly := [(nat_lit 2218, Int.ofNat (nat_lit 1))]
theorem atom0641Coded_decode : atom0641 = SparsePolynomial.decodeCubic 15 atom0641Coded := by decide +kernel
theorem atom0641Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (226886400 : Int) atom0641Coded) := by
  have h := atom0641_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0641Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0642 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0642 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0642 = ((g 9) * (g 12) * (g 14)) := by
  norm_num [atom0642, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0642_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (223084800 : Int) atom0642) := by
  rw [SparsePolynomial.eval_scale, eval_atom0642]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0642Coded : CoefficientMerge.Poly := [(nat_lit 2219, Int.ofNat (nat_lit 1))]
theorem atom0642Coded_decode : atom0642 = SparsePolynomial.decodeCubic 15 atom0642Coded := by decide +kernel
theorem atom0642Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (223084800 : Int) atom0642Coded) := by
  have h := atom0642_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0642Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0643 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0643 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0643 = ((g 9) * (g 13) * (g 13)) := by
  norm_num [atom0643, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0643_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (119750400 : Int) atom0643) := by
  rw [SparsePolynomial.eval_scale, eval_atom0643]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0643Coded : CoefficientMerge.Poly := [(nat_lit 2233, Int.ofNat (nat_lit 1))]
theorem atom0643Coded_decode : atom0643 = SparsePolynomial.decodeCubic 15 atom0643Coded := by decide +kernel
theorem atom0643Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (119750400 : Int) atom0643Coded) := by
  have h := atom0643_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0643Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0644 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0644 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0644 = ((g 9) * (g 13) * (g 14)) := by
  norm_num [atom0644, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0644_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (247622400 : Int) atom0644) := by
  rw [SparsePolynomial.eval_scale, eval_atom0644]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0644Coded : CoefficientMerge.Poly := [(nat_lit 2234, Int.ofNat (nat_lit 1))]
theorem atom0644Coded_decode : atom0644 = SparsePolynomial.decodeCubic 15 atom0644Coded := by decide +kernel
theorem atom0644Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (247622400 : Int) atom0644Coded) := by
  have h := atom0644_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0644Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0645 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0645 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0645 = ((g 9) * (g 14) * (g 14)) := by
  norm_num [atom0645, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0645_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108864000 : Int) atom0645) := by
  rw [SparsePolynomial.eval_scale, eval_atom0645]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0645Coded : CoefficientMerge.Poly := [(nat_lit 2249, Int.ofNat (nat_lit 1))]
theorem atom0645Coded_decode : atom0645 = SparsePolynomial.decodeCubic 15 atom0645Coded := by decide +kernel
theorem atom0645Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (108864000 : Int) atom0645Coded) := by
  have h := atom0645_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0645Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0646 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0646 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0646 = ((g 10) * (g 10) * (g 11)) := by
  norm_num [atom0646, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0646_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35465688 : Int) atom0646) := by
  rw [SparsePolynomial.eval_scale, eval_atom0646]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0646Coded : CoefficientMerge.Poly := [(nat_lit 2411, Int.ofNat (nat_lit 1))]
theorem atom0646Coded_decode : atom0646 = SparsePolynomial.decodeCubic 15 atom0646Coded := by decide +kernel
theorem atom0646Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (35465688 : Int) atom0646Coded) := by
  have h := atom0646_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0646Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0647 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0647 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0647 = ((g 10) * (g 10) * (g 12)) := by
  norm_num [atom0647, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0647_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83210112 : Int) atom0647) := by
  rw [SparsePolynomial.eval_scale, eval_atom0647]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 10) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0647Coded : CoefficientMerge.Poly := [(nat_lit 2412, Int.ofNat (nat_lit 1))]
theorem atom0647Coded_decode : atom0647 = SparsePolynomial.decodeCubic 15 atom0647Coded := by decide +kernel
theorem atom0647Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (83210112 : Int) atom0647Coded) := by
  have h := atom0647_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0647Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0648 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0648 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0648 = ((g 10) * (g 10) * (g 13)) := by
  norm_num [atom0648, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0648_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65111040 : Int) atom0648) := by
  rw [SparsePolynomial.eval_scale, eval_atom0648]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0648Coded : CoefficientMerge.Poly := [(nat_lit 2413, Int.ofNat (nat_lit 1))]
theorem atom0648Coded_decode : atom0648 = SparsePolynomial.decodeCubic 15 atom0648Coded := by decide +kernel
theorem atom0648Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (65111040 : Int) atom0648Coded) := by
  have h := atom0648_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0648Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0649 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0649 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0649 = ((g 10) * (g 10) * (g 14)) := by
  norm_num [atom0649, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0649_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101443968 : Int) atom0649) := by
  rw [SparsePolynomial.eval_scale, eval_atom0649]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0649Coded : CoefficientMerge.Poly := [(nat_lit 2414, Int.ofNat (nat_lit 1))]
theorem atom0649Coded_decode : atom0649 = SparsePolynomial.decodeCubic 15 atom0649Coded := by decide +kernel
theorem atom0649Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (101443968 : Int) atom0649Coded) := by
  have h := atom0649_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0649Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0650 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0650 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0650 = ((g 10) * (g 11) * (g 11)) := by
  norm_num [atom0650, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0650_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77114160 : Int) atom0650) := by
  rw [SparsePolynomial.eval_scale, eval_atom0650]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 10) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0650Coded : CoefficientMerge.Poly := [(nat_lit 2426, Int.ofNat (nat_lit 1))]
theorem atom0650Coded_decode : atom0650 = SparsePolynomial.decodeCubic 15 atom0650Coded := by decide +kernel
theorem atom0650Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (77114160 : Int) atom0650Coded) := by
  have h := atom0650_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0650Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0651 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0651 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0651 = ((g 10) * (g 11) * (g 12)) := by
  norm_num [atom0651, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0651_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (216736560 : Int) atom0651) := by
  rw [SparsePolynomial.eval_scale, eval_atom0651]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 10) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0651Coded : CoefficientMerge.Poly := [(nat_lit 2427, Int.ofNat (nat_lit 1))]
theorem atom0651Coded_decode : atom0651 = SparsePolynomial.decodeCubic 15 atom0651Coded := by decide +kernel
theorem atom0651Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (216736560 : Int) atom0651Coded) := by
  have h := atom0651_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0651Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0652 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0652 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0652 = ((g 10) * (g 11) * (g 13)) := by
  norm_num [atom0652, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0652_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (210325680 : Int) atom0652) := by
  rw [SparsePolynomial.eval_scale, eval_atom0652]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0652Coded : CoefficientMerge.Poly := [(nat_lit 2428, Int.ofNat (nat_lit 1))]
theorem atom0652Coded_decode : atom0652 = SparsePolynomial.decodeCubic 15 atom0652Coded := by decide +kernel
theorem atom0652Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (210325680 : Int) atom0652Coded) := by
  have h := atom0652_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0652Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0653 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0653 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0653 = ((g 10) * (g 11) * (g 14)) := by
  norm_num [atom0653, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0653_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (232889040 : Int) atom0653) := by
  rw [SparsePolynomial.eval_scale, eval_atom0653]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0653Coded : CoefficientMerge.Poly := [(nat_lit 2429, Int.ofNat (nat_lit 1))]
theorem atom0653Coded_decode : atom0653 = SparsePolynomial.decodeCubic 15 atom0653Coded := by decide +kernel
theorem atom0653Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (232889040 : Int) atom0653Coded) := by
  have h := atom0653_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0653Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0654 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0654 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0654 = ((g 10) * (g 12) * (g 12)) := by
  norm_num [atom0654, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0654_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (118713600 : Int) atom0654) := by
  rw [SparsePolynomial.eval_scale, eval_atom0654]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 10) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0654Coded : CoefficientMerge.Poly := [(nat_lit 2442, Int.ofNat (nat_lit 1))]
theorem atom0654Coded_decode : atom0654 = SparsePolynomial.decodeCubic 15 atom0654Coded := by decide +kernel
theorem atom0654Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (118713600 : Int) atom0654Coded) := by
  have h := atom0654_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0654Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0655 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0655 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0655 = ((g 10) * (g 12) * (g 13)) := by
  norm_num [atom0655, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0655_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (244131840 : Int) atom0655) := by
  rw [SparsePolynomial.eval_scale, eval_atom0655]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0655Coded : CoefficientMerge.Poly := [(nat_lit 2443, Int.ofNat (nat_lit 1))]
theorem atom0655Coded_decode : atom0655 = SparsePolynomial.decodeCubic 15 atom0655Coded := by decide +kernel
theorem atom0655Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (244131840 : Int) atom0655Coded) := by
  have h := atom0655_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0655Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0656 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0656 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0656 = ((g 10) * (g 12) * (g 14)) := by
  norm_num [atom0656, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0656_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (250836480 : Int) atom0656) := by
  rw [SparsePolynomial.eval_scale, eval_atom0656]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0656Coded : CoefficientMerge.Poly := [(nat_lit 2444, Int.ofNat (nat_lit 1))]
theorem atom0656Coded_decode : atom0656 = SparsePolynomial.decodeCubic 15 atom0656Coded := by decide +kernel
theorem atom0656Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (250836480 : Int) atom0656Coded) := by
  have h := atom0656_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0656Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0657 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0657 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0657 = ((g 10) * (g 13) * (g 13)) := by
  norm_num [atom0657, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0657_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (131725440 : Int) atom0657) := by
  rw [SparsePolynomial.eval_scale, eval_atom0657]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 10) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0657Coded : CoefficientMerge.Poly := [(nat_lit 2458, Int.ofNat (nat_lit 1))]
theorem atom0657Coded_decode : atom0657 = SparsePolynomial.decodeCubic 15 atom0657Coded := by decide +kernel
theorem atom0657Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (131725440 : Int) atom0657Coded) := by
  have h := atom0657_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0657Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0658 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0658 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0658 = ((g 10) * (g 13) * (g 14)) := by
  norm_num [atom0658, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0658_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283271040 : Int) atom0658) := by
  rw [SparsePolynomial.eval_scale, eval_atom0658]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0658Coded : CoefficientMerge.Poly := [(nat_lit 2459, Int.ofNat (nat_lit 1))]
theorem atom0658Coded_decode : atom0658 = SparsePolynomial.decodeCubic 15 atom0658Coded := by decide +kernel
theorem atom0658Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (283271040 : Int) atom0658Coded) := by
  have h := atom0658_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0658Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0659 : SparsePolynomial.Poly := [([nat_lit 10, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0659 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0659 = ((g 10) * (g 14) * (g 14)) := by
  norm_num [atom0659, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0659_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (130636800 : Int) atom0659) := by
  rw [SparsePolynomial.eval_scale, eval_atom0659]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 10) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0659Coded : CoefficientMerge.Poly := [(nat_lit 2474, Int.ofNat (nat_lit 1))]
theorem atom0659Coded_decode : atom0659 = SparsePolynomial.decodeCubic 15 atom0659Coded := by decide +kernel
theorem atom0659Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (130636800 : Int) atom0659Coded) := by
  have h := atom0659_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0659Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0660 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0660 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0660 = ((g 11) * (g 11) * (g 11)) := by
  norm_num [atom0660, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0660_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31014360 : Int) atom0660) := by
  rw [SparsePolynomial.eval_scale, eval_atom0660]
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 11) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0660Coded : CoefficientMerge.Poly := [(nat_lit 2651, Int.ofNat (nat_lit 1))]
theorem atom0660Coded_decode : atom0660 = SparsePolynomial.decodeCubic 15 atom0660Coded := by decide +kernel
theorem atom0660Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (31014360 : Int) atom0660Coded) := by
  have h := atom0660_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0660Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0661 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0661 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0661 = ((g 11) * (g 11) * (g 12)) := by
  norm_num [atom0661, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0661_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108981720 : Int) atom0661) := by
  rw [SparsePolynomial.eval_scale, eval_atom0661]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 11) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0661Coded : CoefficientMerge.Poly := [(nat_lit 2652, Int.ofNat (nat_lit 1))]
theorem atom0661Coded_decode : atom0661 = SparsePolynomial.decodeCubic 15 atom0661Coded := by decide +kernel
theorem atom0661Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (108981720 : Int) atom0661Coded) := by
  have h := atom0661_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0661Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0662 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0662 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0662 = ((g 11) * (g 11) * (g 13)) := by
  norm_num [atom0662, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0662_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110433240 : Int) atom0662) := by
  rw [SparsePolynomial.eval_scale, eval_atom0662]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0662Coded : CoefficientMerge.Poly := [(nat_lit 2653, Int.ofNat (nat_lit 1))]
theorem atom0662Coded_decode : atom0662 = SparsePolynomial.decodeCubic 15 atom0662Coded := by decide +kernel
theorem atom0662Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (110433240 : Int) atom0662Coded) := by
  have h := atom0662_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0662Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0663 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0663 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0663 = ((g 11) * (g 11) * (g 14)) := by
  norm_num [atom0663, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0663_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (86427000 : Int) atom0663) := by
  rw [SparsePolynomial.eval_scale, eval_atom0663]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0663Coded : CoefficientMerge.Poly := [(nat_lit 2654, Int.ofNat (nat_lit 1))]
theorem atom0663Coded_decode : atom0663 = SparsePolynomial.decodeCubic 15 atom0663Coded := by decide +kernel
theorem atom0663Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (86427000 : Int) atom0663Coded) := by
  have h := atom0663_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0663Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0664 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0664 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0664 = ((g 11) * (g 12) * (g 12)) := by
  norm_num [atom0664, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0664_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (122083200 : Int) atom0664) := by
  rw [SparsePolynomial.eval_scale, eval_atom0664]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 11) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0664Coded : CoefficientMerge.Poly := [(nat_lit 2667, Int.ofNat (nat_lit 1))]
theorem atom0664Coded_decode : atom0664 = SparsePolynomial.decodeCubic 15 atom0664Coded := by decide +kernel
theorem atom0664Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (122083200 : Int) atom0664Coded) := by
  have h := atom0664_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0664Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0665 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0665 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0665 = ((g 11) * (g 12) * (g 13)) := by
  norm_num [atom0665, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0665_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (261377280 : Int) atom0665) := by
  rw [SparsePolynomial.eval_scale, eval_atom0665]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0665Coded : CoefficientMerge.Poly := [(nat_lit 2668, Int.ofNat (nat_lit 1))]
theorem atom0665Coded_decode : atom0665 = SparsePolynomial.decodeCubic 15 atom0665Coded := by decide +kernel
theorem atom0665Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (261377280 : Int) atom0665Coded) := by
  have h := atom0665_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0665Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0666 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0666 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0666 = ((g 11) * (g 12) * (g 14)) := by
  norm_num [atom0666, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0666_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (198698400 : Int) atom0666) := by
  rw [SparsePolynomial.eval_scale, eval_atom0666]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0666Coded : CoefficientMerge.Poly := [(nat_lit 2669, Int.ofNat (nat_lit 1))]
theorem atom0666Coded_decode : atom0666 = SparsePolynomial.decodeCubic 15 atom0666Coded := by decide +kernel
theorem atom0666Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (198698400 : Int) atom0666Coded) := by
  have h := atom0666_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0666Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0667 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0667 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0667 = ((g 11) * (g 13) * (g 13)) := by
  norm_num [atom0667, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0667_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (143700480 : Int) atom0667) := by
  rw [SparsePolynomial.eval_scale, eval_atom0667]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0667Coded : CoefficientMerge.Poly := [(nat_lit 2683, Int.ofNat (nat_lit 1))]
theorem atom0667Coded_decode : atom0667 = SparsePolynomial.decodeCubic 15 atom0667Coded := by decide +kernel
theorem atom0667Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (143700480 : Int) atom0667Coded) := by
  have h := atom0667_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0667Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0668 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0668 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0668 = ((g 11) * (g 13) * (g 14)) := by
  norm_num [atom0668, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0668_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (239029920 : Int) atom0668) := by
  rw [SparsePolynomial.eval_scale, eval_atom0668]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0668Coded : CoefficientMerge.Poly := [(nat_lit 2684, Int.ofNat (nat_lit 1))]
theorem atom0668Coded_decode : atom0668 = SparsePolynomial.decodeCubic 15 atom0668Coded := by decide +kernel
theorem atom0668Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (239029920 : Int) atom0668Coded) := by
  have h := atom0668_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0668Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0669 : SparsePolynomial.Poly := [([nat_lit 11, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0669 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0669 = ((g 11) * (g 14) * (g 14)) := by
  norm_num [atom0669, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0669_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72519840 : Int) atom0669) := by
  rw [SparsePolynomial.eval_scale, eval_atom0669]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0669Coded : CoefficientMerge.Poly := [(nat_lit 2699, Int.ofNat (nat_lit 1))]
theorem atom0669Coded_decode : atom0669 = SparsePolynomial.decodeCubic 15 atom0669Coded := by decide +kernel
theorem atom0669Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (72519840 : Int) atom0669Coded) := by
  have h := atom0669_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0669Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0670 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0670 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0670 = ((g 12) * (g 12) * (g 12)) := by
  norm_num [atom0670, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0670_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41817600 : Int) atom0670) := by
  rw [SparsePolynomial.eval_scale, eval_atom0670]
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 12) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0670Coded : CoefficientMerge.Poly := [(nat_lit 2892, Int.ofNat (nat_lit 1))]
theorem atom0670Coded_decode : atom0670 = SparsePolynomial.decodeCubic 15 atom0670Coded := by decide +kernel
theorem atom0670Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (41817600 : Int) atom0670Coded) := by
  have h := atom0670_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0670Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0671 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0671 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0671 = ((g 12) * (g 12) * (g 13)) := by
  norm_num [atom0671, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0671_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (139311360 : Int) atom0671) := by
  rw [SparsePolynomial.eval_scale, eval_atom0671]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 12) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0671Coded : CoefficientMerge.Poly := [(nat_lit 2893, Int.ofNat (nat_lit 1))]
theorem atom0671Coded_decode : atom0671 = SparsePolynomial.decodeCubic 15 atom0671Coded := by decide +kernel
theorem atom0671Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (139311360 : Int) atom0671Coded) := by
  have h := atom0671_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0671Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0672 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0672 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0672 = ((g 12) * (g 12) * (g 14)) := by
  norm_num [atom0672, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0672_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98737920 : Int) atom0672) := by
  rw [SparsePolynomial.eval_scale, eval_atom0672]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0672Coded : CoefficientMerge.Poly := [(nat_lit 2894, Int.ofNat (nat_lit 1))]
theorem atom0672Coded_decode : atom0672 = SparsePolynomial.decodeCubic 15 atom0672Coded := by decide +kernel
theorem atom0672Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (98737920 : Int) atom0672Coded) := by
  have h := atom0672_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0672Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0673 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0673 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0673 = ((g 12) * (g 13) * (g 13)) := by
  norm_num [atom0673, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0673_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (155675520 : Int) atom0673) := by
  rw [SparsePolynomial.eval_scale, eval_atom0673]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 12) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0673Coded : CoefficientMerge.Poly := [(nat_lit 2908, Int.ofNat (nat_lit 1))]
theorem atom0673Coded_decode : atom0673 = SparsePolynomial.decodeCubic 15 atom0673Coded := by decide +kernel
theorem atom0673Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (155675520 : Int) atom0673Coded) := by
  have h := atom0673_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0673Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0674 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0674 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0674 = ((g 12) * (g 13) * (g 14)) := by
  norm_num [atom0674, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0674_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (245704320 : Int) atom0674) := by
  rw [SparsePolynomial.eval_scale, eval_atom0674]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0674Coded : CoefficientMerge.Poly := [(nat_lit 2909, Int.ofNat (nat_lit 1))]
theorem atom0674Coded_decode : atom0674 = SparsePolynomial.decodeCubic 15 atom0674Coded := by decide +kernel
theorem atom0674Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (245704320 : Int) atom0674Coded) := by
  have h := atom0674_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0674Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0675 : SparsePolynomial.Poly := [([nat_lit 12, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0675 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0675 = ((g 12) * (g 14) * (g 14)) := by
  norm_num [atom0675, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0675_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65318400 : Int) atom0675) := by
  rw [SparsePolynomial.eval_scale, eval_atom0675]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0675Coded : CoefficientMerge.Poly := [(nat_lit 2924, Int.ofNat (nat_lit 1))]
theorem atom0675Coded_decode : atom0675 = SparsePolynomial.decodeCubic 15 atom0675Coded := by decide +kernel
theorem atom0675Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (65318400 : Int) atom0675Coded) := by
  have h := atom0675_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0675Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0676 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0676 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0676 = ((g 13) * (g 13) * (g 13)) := by
  norm_num [atom0676, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0676_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55883520 : Int) atom0676) := by
  rw [SparsePolynomial.eval_scale, eval_atom0676]
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 13) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0676Coded : CoefficientMerge.Poly := [(nat_lit 3133, Int.ofNat (nat_lit 1))]
theorem atom0676Coded_decode : atom0676 = SparsePolynomial.decodeCubic 15 atom0676Coded := by decide +kernel
theorem atom0676Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (55883520 : Int) atom0676Coded) := by
  have h := atom0676_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0676Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0677 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0677 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0677 = ((g 13) * (g 13) * (g 14)) := by
  norm_num [atom0677, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0677_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140676480 : Int) atom0677) := by
  rw [SparsePolynomial.eval_scale, eval_atom0677]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 13) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0677Coded : CoefficientMerge.Poly := [(nat_lit 3134, Int.ofNat (nat_lit 1))]
theorem atom0677Coded_decode : atom0677 = SparsePolynomial.decodeCubic 15 atom0677Coded := by decide +kernel
theorem atom0677Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (140676480 : Int) atom0677Coded) := by
  have h := atom0677_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0677Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0678 : SparsePolynomial.Poly := [([nat_lit 13, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0678 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0678 = ((g 13) * (g 14) * (g 14)) := by
  norm_num [atom0678, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0678_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87091200 : Int) atom0678) := by
  rw [SparsePolynomial.eval_scale, eval_atom0678]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 13) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0678Coded : CoefficientMerge.Poly := [(nat_lit 3149, Int.ofNat (nat_lit 1))]
theorem atom0678Coded_decode : atom0678 = SparsePolynomial.decodeCubic 15 atom0678Coded := by decide +kernel
theorem atom0678Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (87091200 : Int) atom0678Coded) := by
  have h := atom0678_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0678Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block008 : CoefficientMerge.Poly := [(nat_lit 2187, Int.ofNat (nat_lit 202089600)), (nat_lit 2188, Int.ofNat (nat_lit 147225600)), (nat_lit 2189, Int.ofNat (nat_lit 228441600)), (nat_lit 2201, Int.ofNat (nat_lit 101130120)), (nat_lit 2202, Int.ofNat (nat_lit 235482120)), (nat_lit 2203, Int.ofNat (nat_lit 199784880)), (nat_lit 2204, Int.ofNat (nat_lit 213034320)), (nat_lit 2217, Int.ofNat (nat_lit 115344000)), (nat_lit 2218, Int.ofNat (nat_lit 226886400)), (nat_lit 2219, Int.ofNat (nat_lit 223084800)), (nat_lit 2233, Int.ofNat (nat_lit 119750400)), (nat_lit 2234, Int.ofNat (nat_lit 247622400)), (nat_lit 2249, Int.ofNat (nat_lit 108864000)), (nat_lit 2411, Int.ofNat (nat_lit 35465688)), (nat_lit 2412, Int.ofNat (nat_lit 83210112)), (nat_lit 2413, Int.ofNat (nat_lit 65111040)), (nat_lit 2414, Int.ofNat (nat_lit 101443968)), (nat_lit 2426, Int.ofNat (nat_lit 77114160)), (nat_lit 2427, Int.ofNat (nat_lit 216736560)), (nat_lit 2428, Int.ofNat (nat_lit 210325680)), (nat_lit 2429, Int.ofNat (nat_lit 232889040)), (nat_lit 2442, Int.ofNat (nat_lit 118713600)), (nat_lit 2443, Int.ofNat (nat_lit 244131840)), (nat_lit 2444, Int.ofNat (nat_lit 250836480)), (nat_lit 2458, Int.ofNat (nat_lit 131725440)), (nat_lit 2459, Int.ofNat (nat_lit 283271040)), (nat_lit 2474, Int.ofNat (nat_lit 130636800)), (nat_lit 2651, Int.ofNat (nat_lit 31014360)), (nat_lit 2652, Int.ofNat (nat_lit 108981720)), (nat_lit 2653, Int.ofNat (nat_lit 110433240)), (nat_lit 2654, Int.ofNat (nat_lit 86427000)), (nat_lit 2667, Int.ofNat (nat_lit 122083200)), (nat_lit 2668, Int.ofNat (nat_lit 261377280)), (nat_lit 2669, Int.ofNat (nat_lit 198698400)), (nat_lit 2683, Int.ofNat (nat_lit 143700480)), (nat_lit 2684, Int.ofNat (nat_lit 239029920)), (nat_lit 2699, Int.ofNat (nat_lit 72519840)), (nat_lit 2892, Int.ofNat (nat_lit 41817600)), (nat_lit 2893, Int.ofNat (nat_lit 139311360)), (nat_lit 2894, Int.ofNat (nat_lit 98737920)), (nat_lit 2908, Int.ofNat (nat_lit 155675520)), (nat_lit 2909, Int.ofNat (nat_lit 245704320)), (nat_lit 2924, Int.ofNat (nat_lit 65318400)), (nat_lit 3133, Int.ofNat (nat_lit 55883520)), (nat_lit 3134, Int.ofNat (nat_lit 140676480)), (nat_lit 3149, Int.ofNat (nat_lit 87091200))]
def block008_data_flat000 : CoefficientMerge.Poly := [(nat_lit 2187, Int.ofNat (nat_lit 202089600))]
theorem block008_data_flat000_step : block008_data_flat000 = (CoefficientMerge.scale (202089600 : Int) atom0633Coded) := by decide +kernel
theorem block008_data_flat000_original : block008_data_flat000 = (CoefficientMerge.scale (202089600 : Int) atom0633Coded) := by
  rw [block008_data_flat000_step]
def block008_data_flat001 : CoefficientMerge.Poly := [(nat_lit 2188, Int.ofNat (nat_lit 147225600))]
theorem block008_data_flat001_step : block008_data_flat001 = (CoefficientMerge.scale (147225600 : Int) atom0634Coded) := by decide +kernel
theorem block008_data_flat001_original : block008_data_flat001 = (CoefficientMerge.scale (147225600 : Int) atom0634Coded) := by
  rw [block008_data_flat001_step]
def block008_data_flat002 : CoefficientMerge.Poly := [(nat_lit 2187, Int.ofNat (nat_lit 202089600)), (nat_lit 2188, Int.ofNat (nat_lit 147225600))]
theorem block008_data_flat002_step : block008_data_flat002 = (CoefficientMerge.fastMerge block008_data_flat000 block008_data_flat001) := by decide +kernel
theorem block008_data_flat002_original : block008_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (202089600 : Int) atom0633Coded) (CoefficientMerge.scale (147225600 : Int) atom0634Coded)) := by
  rw [block008_data_flat002_step, block008_data_flat000_original, block008_data_flat001_original]
def block008_data_flat003 : CoefficientMerge.Poly := [(nat_lit 2189, Int.ofNat (nat_lit 228441600))]
theorem block008_data_flat003_step : block008_data_flat003 = (CoefficientMerge.scale (228441600 : Int) atom0635Coded) := by decide +kernel
theorem block008_data_flat003_original : block008_data_flat003 = (CoefficientMerge.scale (228441600 : Int) atom0635Coded) := by
  rw [block008_data_flat003_step]
def block008_data_flat004 : CoefficientMerge.Poly := [(nat_lit 2201, Int.ofNat (nat_lit 101130120))]
theorem block008_data_flat004_step : block008_data_flat004 = (CoefficientMerge.scale (101130120 : Int) atom0636Coded) := by decide +kernel
theorem block008_data_flat004_original : block008_data_flat004 = (CoefficientMerge.scale (101130120 : Int) atom0636Coded) := by
  rw [block008_data_flat004_step]
def block008_data_flat005 : CoefficientMerge.Poly := [(nat_lit 2202, Int.ofNat (nat_lit 235482120))]
theorem block008_data_flat005_step : block008_data_flat005 = (CoefficientMerge.scale (235482120 : Int) atom0637Coded) := by decide +kernel
theorem block008_data_flat005_original : block008_data_flat005 = (CoefficientMerge.scale (235482120 : Int) atom0637Coded) := by
  rw [block008_data_flat005_step]
def block008_data_flat006 : CoefficientMerge.Poly := [(nat_lit 2201, Int.ofNat (nat_lit 101130120)), (nat_lit 2202, Int.ofNat (nat_lit 235482120))]
theorem block008_data_flat006_step : block008_data_flat006 = (CoefficientMerge.fastMerge block008_data_flat004 block008_data_flat005) := by decide +kernel
theorem block008_data_flat006_original : block008_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (101130120 : Int) atom0636Coded) (CoefficientMerge.scale (235482120 : Int) atom0637Coded)) := by
  rw [block008_data_flat006_step, block008_data_flat004_original, block008_data_flat005_original]
def block008_data_flat007 : CoefficientMerge.Poly := [(nat_lit 2189, Int.ofNat (nat_lit 228441600)), (nat_lit 2201, Int.ofNat (nat_lit 101130120)), (nat_lit 2202, Int.ofNat (nat_lit 235482120))]
theorem block008_data_flat007_step : block008_data_flat007 = (CoefficientMerge.fastMerge block008_data_flat003 block008_data_flat006) := by decide +kernel
theorem block008_data_flat007_original : block008_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (228441600 : Int) atom0635Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101130120 : Int) atom0636Coded) (CoefficientMerge.scale (235482120 : Int) atom0637Coded))) := by
  rw [block008_data_flat007_step, block008_data_flat003_original, block008_data_flat006_original]
def block008_data_flat008 : CoefficientMerge.Poly := [(nat_lit 2187, Int.ofNat (nat_lit 202089600)), (nat_lit 2188, Int.ofNat (nat_lit 147225600)), (nat_lit 2189, Int.ofNat (nat_lit 228441600)), (nat_lit 2201, Int.ofNat (nat_lit 101130120)), (nat_lit 2202, Int.ofNat (nat_lit 235482120))]
theorem block008_data_flat008_step : block008_data_flat008 = (CoefficientMerge.fastMerge block008_data_flat002 block008_data_flat007) := by decide +kernel
theorem block008_data_flat008_original : block008_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (202089600 : Int) atom0633Coded) (CoefficientMerge.scale (147225600 : Int) atom0634Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (228441600 : Int) atom0635Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101130120 : Int) atom0636Coded) (CoefficientMerge.scale (235482120 : Int) atom0637Coded)))) := by
  rw [block008_data_flat008_step, block008_data_flat002_original, block008_data_flat007_original]
def block008_data_flat009 : CoefficientMerge.Poly := [(nat_lit 2203, Int.ofNat (nat_lit 199784880))]
theorem block008_data_flat009_step : block008_data_flat009 = (CoefficientMerge.scale (199784880 : Int) atom0638Coded) := by decide +kernel
theorem block008_data_flat009_original : block008_data_flat009 = (CoefficientMerge.scale (199784880 : Int) atom0638Coded) := by
  rw [block008_data_flat009_step]
def block008_data_flat010 : CoefficientMerge.Poly := [(nat_lit 2204, Int.ofNat (nat_lit 213034320))]
theorem block008_data_flat010_step : block008_data_flat010 = (CoefficientMerge.scale (213034320 : Int) atom0639Coded) := by decide +kernel
theorem block008_data_flat010_original : block008_data_flat010 = (CoefficientMerge.scale (213034320 : Int) atom0639Coded) := by
  rw [block008_data_flat010_step]
def block008_data_flat011 : CoefficientMerge.Poly := [(nat_lit 2217, Int.ofNat (nat_lit 115344000))]
theorem block008_data_flat011_step : block008_data_flat011 = (CoefficientMerge.scale (115344000 : Int) atom0640Coded) := by decide +kernel
theorem block008_data_flat011_original : block008_data_flat011 = (CoefficientMerge.scale (115344000 : Int) atom0640Coded) := by
  rw [block008_data_flat011_step]
def block008_data_flat012 : CoefficientMerge.Poly := [(nat_lit 2204, Int.ofNat (nat_lit 213034320)), (nat_lit 2217, Int.ofNat (nat_lit 115344000))]
theorem block008_data_flat012_step : block008_data_flat012 = (CoefficientMerge.fastMerge block008_data_flat010 block008_data_flat011) := by decide +kernel
theorem block008_data_flat012_original : block008_data_flat012 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (213034320 : Int) atom0639Coded) (CoefficientMerge.scale (115344000 : Int) atom0640Coded)) := by
  rw [block008_data_flat012_step, block008_data_flat010_original, block008_data_flat011_original]
def block008_data_flat013 : CoefficientMerge.Poly := [(nat_lit 2203, Int.ofNat (nat_lit 199784880)), (nat_lit 2204, Int.ofNat (nat_lit 213034320)), (nat_lit 2217, Int.ofNat (nat_lit 115344000))]
theorem block008_data_flat013_step : block008_data_flat013 = (CoefficientMerge.fastMerge block008_data_flat009 block008_data_flat012) := by decide +kernel
theorem block008_data_flat013_original : block008_data_flat013 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (199784880 : Int) atom0638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (213034320 : Int) atom0639Coded) (CoefficientMerge.scale (115344000 : Int) atom0640Coded))) := by
  rw [block008_data_flat013_step, block008_data_flat009_original, block008_data_flat012_original]
def block008_data_flat014 : CoefficientMerge.Poly := [(nat_lit 2218, Int.ofNat (nat_lit 226886400))]
theorem block008_data_flat014_step : block008_data_flat014 = (CoefficientMerge.scale (226886400 : Int) atom0641Coded) := by decide +kernel
theorem block008_data_flat014_original : block008_data_flat014 = (CoefficientMerge.scale (226886400 : Int) atom0641Coded) := by
  rw [block008_data_flat014_step]
def block008_data_flat015 : CoefficientMerge.Poly := [(nat_lit 2219, Int.ofNat (nat_lit 223084800))]
theorem block008_data_flat015_step : block008_data_flat015 = (CoefficientMerge.scale (223084800 : Int) atom0642Coded) := by decide +kernel
theorem block008_data_flat015_original : block008_data_flat015 = (CoefficientMerge.scale (223084800 : Int) atom0642Coded) := by
  rw [block008_data_flat015_step]
def block008_data_flat016 : CoefficientMerge.Poly := [(nat_lit 2233, Int.ofNat (nat_lit 119750400))]
theorem block008_data_flat016_step : block008_data_flat016 = (CoefficientMerge.scale (119750400 : Int) atom0643Coded) := by decide +kernel
theorem block008_data_flat016_original : block008_data_flat016 = (CoefficientMerge.scale (119750400 : Int) atom0643Coded) := by
  rw [block008_data_flat016_step]
def block008_data_flat017 : CoefficientMerge.Poly := [(nat_lit 2219, Int.ofNat (nat_lit 223084800)), (nat_lit 2233, Int.ofNat (nat_lit 119750400))]
theorem block008_data_flat017_step : block008_data_flat017 = (CoefficientMerge.fastMerge block008_data_flat015 block008_data_flat016) := by decide +kernel
theorem block008_data_flat017_original : block008_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (223084800 : Int) atom0642Coded) (CoefficientMerge.scale (119750400 : Int) atom0643Coded)) := by
  rw [block008_data_flat017_step, block008_data_flat015_original, block008_data_flat016_original]
def block008_data_flat018 : CoefficientMerge.Poly := [(nat_lit 2218, Int.ofNat (nat_lit 226886400)), (nat_lit 2219, Int.ofNat (nat_lit 223084800)), (nat_lit 2233, Int.ofNat (nat_lit 119750400))]
theorem block008_data_flat018_step : block008_data_flat018 = (CoefficientMerge.fastMerge block008_data_flat014 block008_data_flat017) := by decide +kernel
theorem block008_data_flat018_original : block008_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (226886400 : Int) atom0641Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (223084800 : Int) atom0642Coded) (CoefficientMerge.scale (119750400 : Int) atom0643Coded))) := by
  rw [block008_data_flat018_step, block008_data_flat014_original, block008_data_flat017_original]
def block008_data_flat019 : CoefficientMerge.Poly := [(nat_lit 2203, Int.ofNat (nat_lit 199784880)), (nat_lit 2204, Int.ofNat (nat_lit 213034320)), (nat_lit 2217, Int.ofNat (nat_lit 115344000)), (nat_lit 2218, Int.ofNat (nat_lit 226886400)), (nat_lit 2219, Int.ofNat (nat_lit 223084800)), (nat_lit 2233, Int.ofNat (nat_lit 119750400))]
theorem block008_data_flat019_step : block008_data_flat019 = (CoefficientMerge.fastMerge block008_data_flat013 block008_data_flat018) := by decide +kernel
theorem block008_data_flat019_original : block008_data_flat019 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (199784880 : Int) atom0638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (213034320 : Int) atom0639Coded) (CoefficientMerge.scale (115344000 : Int) atom0640Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226886400 : Int) atom0641Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (223084800 : Int) atom0642Coded) (CoefficientMerge.scale (119750400 : Int) atom0643Coded)))) := by
  rw [block008_data_flat019_step, block008_data_flat013_original, block008_data_flat018_original]
def block008_data_flat020 : CoefficientMerge.Poly := [(nat_lit 2187, Int.ofNat (nat_lit 202089600)), (nat_lit 2188, Int.ofNat (nat_lit 147225600)), (nat_lit 2189, Int.ofNat (nat_lit 228441600)), (nat_lit 2201, Int.ofNat (nat_lit 101130120)), (nat_lit 2202, Int.ofNat (nat_lit 235482120)), (nat_lit 2203, Int.ofNat (nat_lit 199784880)), (nat_lit 2204, Int.ofNat (nat_lit 213034320)), (nat_lit 2217, Int.ofNat (nat_lit 115344000)), (nat_lit 2218, Int.ofNat (nat_lit 226886400)), (nat_lit 2219, Int.ofNat (nat_lit 223084800)), (nat_lit 2233, Int.ofNat (nat_lit 119750400))]
theorem block008_data_flat020_step : block008_data_flat020 = (CoefficientMerge.fastMerge block008_data_flat008 block008_data_flat019) := by decide +kernel
theorem block008_data_flat020_original : block008_data_flat020 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (202089600 : Int) atom0633Coded) (CoefficientMerge.scale (147225600 : Int) atom0634Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (228441600 : Int) atom0635Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101130120 : Int) atom0636Coded) (CoefficientMerge.scale (235482120 : Int) atom0637Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (199784880 : Int) atom0638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (213034320 : Int) atom0639Coded) (CoefficientMerge.scale (115344000 : Int) atom0640Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226886400 : Int) atom0641Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (223084800 : Int) atom0642Coded) (CoefficientMerge.scale (119750400 : Int) atom0643Coded))))) := by
  rw [block008_data_flat020_step, block008_data_flat008_original, block008_data_flat019_original]
def block008_data_flat021 : CoefficientMerge.Poly := [(nat_lit 2234, Int.ofNat (nat_lit 247622400))]
theorem block008_data_flat021_step : block008_data_flat021 = (CoefficientMerge.scale (247622400 : Int) atom0644Coded) := by decide +kernel
theorem block008_data_flat021_original : block008_data_flat021 = (CoefficientMerge.scale (247622400 : Int) atom0644Coded) := by
  rw [block008_data_flat021_step]
def block008_data_flat022 : CoefficientMerge.Poly := [(nat_lit 2249, Int.ofNat (nat_lit 108864000))]
theorem block008_data_flat022_step : block008_data_flat022 = (CoefficientMerge.scale (108864000 : Int) atom0645Coded) := by decide +kernel
theorem block008_data_flat022_original : block008_data_flat022 = (CoefficientMerge.scale (108864000 : Int) atom0645Coded) := by
  rw [block008_data_flat022_step]
def block008_data_flat023 : CoefficientMerge.Poly := [(nat_lit 2411, Int.ofNat (nat_lit 35465688))]
theorem block008_data_flat023_step : block008_data_flat023 = (CoefficientMerge.scale (35465688 : Int) atom0646Coded) := by decide +kernel
theorem block008_data_flat023_original : block008_data_flat023 = (CoefficientMerge.scale (35465688 : Int) atom0646Coded) := by
  rw [block008_data_flat023_step]
def block008_data_flat024 : CoefficientMerge.Poly := [(nat_lit 2249, Int.ofNat (nat_lit 108864000)), (nat_lit 2411, Int.ofNat (nat_lit 35465688))]
theorem block008_data_flat024_step : block008_data_flat024 = (CoefficientMerge.fastMerge block008_data_flat022 block008_data_flat023) := by decide +kernel
theorem block008_data_flat024_original : block008_data_flat024 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (108864000 : Int) atom0645Coded) (CoefficientMerge.scale (35465688 : Int) atom0646Coded)) := by
  rw [block008_data_flat024_step, block008_data_flat022_original, block008_data_flat023_original]
def block008_data_flat025 : CoefficientMerge.Poly := [(nat_lit 2234, Int.ofNat (nat_lit 247622400)), (nat_lit 2249, Int.ofNat (nat_lit 108864000)), (nat_lit 2411, Int.ofNat (nat_lit 35465688))]
theorem block008_data_flat025_step : block008_data_flat025 = (CoefficientMerge.fastMerge block008_data_flat021 block008_data_flat024) := by decide +kernel
theorem block008_data_flat025_original : block008_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (247622400 : Int) atom0644Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (108864000 : Int) atom0645Coded) (CoefficientMerge.scale (35465688 : Int) atom0646Coded))) := by
  rw [block008_data_flat025_step, block008_data_flat021_original, block008_data_flat024_original]
def block008_data_flat026 : CoefficientMerge.Poly := [(nat_lit 2412, Int.ofNat (nat_lit 83210112))]
theorem block008_data_flat026_step : block008_data_flat026 = (CoefficientMerge.scale (83210112 : Int) atom0647Coded) := by decide +kernel
theorem block008_data_flat026_original : block008_data_flat026 = (CoefficientMerge.scale (83210112 : Int) atom0647Coded) := by
  rw [block008_data_flat026_step]
def block008_data_flat027 : CoefficientMerge.Poly := [(nat_lit 2413, Int.ofNat (nat_lit 65111040))]
theorem block008_data_flat027_step : block008_data_flat027 = (CoefficientMerge.scale (65111040 : Int) atom0648Coded) := by decide +kernel
theorem block008_data_flat027_original : block008_data_flat027 = (CoefficientMerge.scale (65111040 : Int) atom0648Coded) := by
  rw [block008_data_flat027_step]
def block008_data_flat028 : CoefficientMerge.Poly := [(nat_lit 2414, Int.ofNat (nat_lit 101443968))]
theorem block008_data_flat028_step : block008_data_flat028 = (CoefficientMerge.scale (101443968 : Int) atom0649Coded) := by decide +kernel
theorem block008_data_flat028_original : block008_data_flat028 = (CoefficientMerge.scale (101443968 : Int) atom0649Coded) := by
  rw [block008_data_flat028_step]
def block008_data_flat029 : CoefficientMerge.Poly := [(nat_lit 2413, Int.ofNat (nat_lit 65111040)), (nat_lit 2414, Int.ofNat (nat_lit 101443968))]
theorem block008_data_flat029_step : block008_data_flat029 = (CoefficientMerge.fastMerge block008_data_flat027 block008_data_flat028) := by decide +kernel
theorem block008_data_flat029_original : block008_data_flat029 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (65111040 : Int) atom0648Coded) (CoefficientMerge.scale (101443968 : Int) atom0649Coded)) := by
  rw [block008_data_flat029_step, block008_data_flat027_original, block008_data_flat028_original]
def block008_data_flat030 : CoefficientMerge.Poly := [(nat_lit 2412, Int.ofNat (nat_lit 83210112)), (nat_lit 2413, Int.ofNat (nat_lit 65111040)), (nat_lit 2414, Int.ofNat (nat_lit 101443968))]
theorem block008_data_flat030_step : block008_data_flat030 = (CoefficientMerge.fastMerge block008_data_flat026 block008_data_flat029) := by decide +kernel
theorem block008_data_flat030_original : block008_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (83210112 : Int) atom0647Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65111040 : Int) atom0648Coded) (CoefficientMerge.scale (101443968 : Int) atom0649Coded))) := by
  rw [block008_data_flat030_step, block008_data_flat026_original, block008_data_flat029_original]
def block008_data_flat031 : CoefficientMerge.Poly := [(nat_lit 2234, Int.ofNat (nat_lit 247622400)), (nat_lit 2249, Int.ofNat (nat_lit 108864000)), (nat_lit 2411, Int.ofNat (nat_lit 35465688)), (nat_lit 2412, Int.ofNat (nat_lit 83210112)), (nat_lit 2413, Int.ofNat (nat_lit 65111040)), (nat_lit 2414, Int.ofNat (nat_lit 101443968))]
theorem block008_data_flat031_step : block008_data_flat031 = (CoefficientMerge.fastMerge block008_data_flat025 block008_data_flat030) := by decide +kernel
theorem block008_data_flat031_original : block008_data_flat031 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (247622400 : Int) atom0644Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (108864000 : Int) atom0645Coded) (CoefficientMerge.scale (35465688 : Int) atom0646Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83210112 : Int) atom0647Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65111040 : Int) atom0648Coded) (CoefficientMerge.scale (101443968 : Int) atom0649Coded)))) := by
  rw [block008_data_flat031_step, block008_data_flat025_original, block008_data_flat030_original]
def block008_data_flat032 : CoefficientMerge.Poly := [(nat_lit 2426, Int.ofNat (nat_lit 77114160))]
theorem block008_data_flat032_step : block008_data_flat032 = (CoefficientMerge.scale (77114160 : Int) atom0650Coded) := by decide +kernel
theorem block008_data_flat032_original : block008_data_flat032 = (CoefficientMerge.scale (77114160 : Int) atom0650Coded) := by
  rw [block008_data_flat032_step]
def block008_data_flat033 : CoefficientMerge.Poly := [(nat_lit 2427, Int.ofNat (nat_lit 216736560))]
theorem block008_data_flat033_step : block008_data_flat033 = (CoefficientMerge.scale (216736560 : Int) atom0651Coded) := by decide +kernel
theorem block008_data_flat033_original : block008_data_flat033 = (CoefficientMerge.scale (216736560 : Int) atom0651Coded) := by
  rw [block008_data_flat033_step]
def block008_data_flat034 : CoefficientMerge.Poly := [(nat_lit 2428, Int.ofNat (nat_lit 210325680))]
theorem block008_data_flat034_step : block008_data_flat034 = (CoefficientMerge.scale (210325680 : Int) atom0652Coded) := by decide +kernel
theorem block008_data_flat034_original : block008_data_flat034 = (CoefficientMerge.scale (210325680 : Int) atom0652Coded) := by
  rw [block008_data_flat034_step]
def block008_data_flat035 : CoefficientMerge.Poly := [(nat_lit 2427, Int.ofNat (nat_lit 216736560)), (nat_lit 2428, Int.ofNat (nat_lit 210325680))]
theorem block008_data_flat035_step : block008_data_flat035 = (CoefficientMerge.fastMerge block008_data_flat033 block008_data_flat034) := by decide +kernel
theorem block008_data_flat035_original : block008_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (216736560 : Int) atom0651Coded) (CoefficientMerge.scale (210325680 : Int) atom0652Coded)) := by
  rw [block008_data_flat035_step, block008_data_flat033_original, block008_data_flat034_original]
def block008_data_flat036 : CoefficientMerge.Poly := [(nat_lit 2426, Int.ofNat (nat_lit 77114160)), (nat_lit 2427, Int.ofNat (nat_lit 216736560)), (nat_lit 2428, Int.ofNat (nat_lit 210325680))]
theorem block008_data_flat036_step : block008_data_flat036 = (CoefficientMerge.fastMerge block008_data_flat032 block008_data_flat035) := by decide +kernel
theorem block008_data_flat036_original : block008_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (77114160 : Int) atom0650Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (216736560 : Int) atom0651Coded) (CoefficientMerge.scale (210325680 : Int) atom0652Coded))) := by
  rw [block008_data_flat036_step, block008_data_flat032_original, block008_data_flat035_original]
def block008_data_flat037 : CoefficientMerge.Poly := [(nat_lit 2429, Int.ofNat (nat_lit 232889040))]
theorem block008_data_flat037_step : block008_data_flat037 = (CoefficientMerge.scale (232889040 : Int) atom0653Coded) := by decide +kernel
theorem block008_data_flat037_original : block008_data_flat037 = (CoefficientMerge.scale (232889040 : Int) atom0653Coded) := by
  rw [block008_data_flat037_step]
def block008_data_flat038 : CoefficientMerge.Poly := [(nat_lit 2442, Int.ofNat (nat_lit 118713600))]
theorem block008_data_flat038_step : block008_data_flat038 = (CoefficientMerge.scale (118713600 : Int) atom0654Coded) := by decide +kernel
theorem block008_data_flat038_original : block008_data_flat038 = (CoefficientMerge.scale (118713600 : Int) atom0654Coded) := by
  rw [block008_data_flat038_step]
def block008_data_flat039 : CoefficientMerge.Poly := [(nat_lit 2443, Int.ofNat (nat_lit 244131840))]
theorem block008_data_flat039_step : block008_data_flat039 = (CoefficientMerge.scale (244131840 : Int) atom0655Coded) := by decide +kernel
theorem block008_data_flat039_original : block008_data_flat039 = (CoefficientMerge.scale (244131840 : Int) atom0655Coded) := by
  rw [block008_data_flat039_step]
def block008_data_flat040 : CoefficientMerge.Poly := [(nat_lit 2442, Int.ofNat (nat_lit 118713600)), (nat_lit 2443, Int.ofNat (nat_lit 244131840))]
theorem block008_data_flat040_step : block008_data_flat040 = (CoefficientMerge.fastMerge block008_data_flat038 block008_data_flat039) := by decide +kernel
theorem block008_data_flat040_original : block008_data_flat040 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (118713600 : Int) atom0654Coded) (CoefficientMerge.scale (244131840 : Int) atom0655Coded)) := by
  rw [block008_data_flat040_step, block008_data_flat038_original, block008_data_flat039_original]
def block008_data_flat041 : CoefficientMerge.Poly := [(nat_lit 2429, Int.ofNat (nat_lit 232889040)), (nat_lit 2442, Int.ofNat (nat_lit 118713600)), (nat_lit 2443, Int.ofNat (nat_lit 244131840))]
theorem block008_data_flat041_step : block008_data_flat041 = (CoefficientMerge.fastMerge block008_data_flat037 block008_data_flat040) := by decide +kernel
theorem block008_data_flat041_original : block008_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (232889040 : Int) atom0653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118713600 : Int) atom0654Coded) (CoefficientMerge.scale (244131840 : Int) atom0655Coded))) := by
  rw [block008_data_flat041_step, block008_data_flat037_original, block008_data_flat040_original]
def block008_data_flat042 : CoefficientMerge.Poly := [(nat_lit 2426, Int.ofNat (nat_lit 77114160)), (nat_lit 2427, Int.ofNat (nat_lit 216736560)), (nat_lit 2428, Int.ofNat (nat_lit 210325680)), (nat_lit 2429, Int.ofNat (nat_lit 232889040)), (nat_lit 2442, Int.ofNat (nat_lit 118713600)), (nat_lit 2443, Int.ofNat (nat_lit 244131840))]
theorem block008_data_flat042_step : block008_data_flat042 = (CoefficientMerge.fastMerge block008_data_flat036 block008_data_flat041) := by decide +kernel
theorem block008_data_flat042_original : block008_data_flat042 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77114160 : Int) atom0650Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (216736560 : Int) atom0651Coded) (CoefficientMerge.scale (210325680 : Int) atom0652Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (232889040 : Int) atom0653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118713600 : Int) atom0654Coded) (CoefficientMerge.scale (244131840 : Int) atom0655Coded)))) := by
  rw [block008_data_flat042_step, block008_data_flat036_original, block008_data_flat041_original]
def block008_data_flat043 : CoefficientMerge.Poly := [(nat_lit 2234, Int.ofNat (nat_lit 247622400)), (nat_lit 2249, Int.ofNat (nat_lit 108864000)), (nat_lit 2411, Int.ofNat (nat_lit 35465688)), (nat_lit 2412, Int.ofNat (nat_lit 83210112)), (nat_lit 2413, Int.ofNat (nat_lit 65111040)), (nat_lit 2414, Int.ofNat (nat_lit 101443968)), (nat_lit 2426, Int.ofNat (nat_lit 77114160)), (nat_lit 2427, Int.ofNat (nat_lit 216736560)), (nat_lit 2428, Int.ofNat (nat_lit 210325680)), (nat_lit 2429, Int.ofNat (nat_lit 232889040)), (nat_lit 2442, Int.ofNat (nat_lit 118713600)), (nat_lit 2443, Int.ofNat (nat_lit 244131840))]
theorem block008_data_flat043_step : block008_data_flat043 = (CoefficientMerge.fastMerge block008_data_flat031 block008_data_flat042) := by decide +kernel
theorem block008_data_flat043_original : block008_data_flat043 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (247622400 : Int) atom0644Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (108864000 : Int) atom0645Coded) (CoefficientMerge.scale (35465688 : Int) atom0646Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83210112 : Int) atom0647Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65111040 : Int) atom0648Coded) (CoefficientMerge.scale (101443968 : Int) atom0649Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77114160 : Int) atom0650Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (216736560 : Int) atom0651Coded) (CoefficientMerge.scale (210325680 : Int) atom0652Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (232889040 : Int) atom0653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118713600 : Int) atom0654Coded) (CoefficientMerge.scale (244131840 : Int) atom0655Coded))))) := by
  rw [block008_data_flat043_step, block008_data_flat031_original, block008_data_flat042_original]
def block008_data_flat044 : CoefficientMerge.Poly := [(nat_lit 2187, Int.ofNat (nat_lit 202089600)), (nat_lit 2188, Int.ofNat (nat_lit 147225600)), (nat_lit 2189, Int.ofNat (nat_lit 228441600)), (nat_lit 2201, Int.ofNat (nat_lit 101130120)), (nat_lit 2202, Int.ofNat (nat_lit 235482120)), (nat_lit 2203, Int.ofNat (nat_lit 199784880)), (nat_lit 2204, Int.ofNat (nat_lit 213034320)), (nat_lit 2217, Int.ofNat (nat_lit 115344000)), (nat_lit 2218, Int.ofNat (nat_lit 226886400)), (nat_lit 2219, Int.ofNat (nat_lit 223084800)), (nat_lit 2233, Int.ofNat (nat_lit 119750400)), (nat_lit 2234, Int.ofNat (nat_lit 247622400)), (nat_lit 2249, Int.ofNat (nat_lit 108864000)), (nat_lit 2411, Int.ofNat (nat_lit 35465688)), (nat_lit 2412, Int.ofNat (nat_lit 83210112)), (nat_lit 2413, Int.ofNat (nat_lit 65111040)), (nat_lit 2414, Int.ofNat (nat_lit 101443968)), (nat_lit 2426, Int.ofNat (nat_lit 77114160)), (nat_lit 2427, Int.ofNat (nat_lit 216736560)), (nat_lit 2428, Int.ofNat (nat_lit 210325680)), (nat_lit 2429, Int.ofNat (nat_lit 232889040)), (nat_lit 2442, Int.ofNat (nat_lit 118713600)), (nat_lit 2443, Int.ofNat (nat_lit 244131840))]
theorem block008_data_flat044_step : block008_data_flat044 = (CoefficientMerge.fastMerge block008_data_flat020 block008_data_flat043) := by decide +kernel
theorem block008_data_flat044_original : block008_data_flat044 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (202089600 : Int) atom0633Coded) (CoefficientMerge.scale (147225600 : Int) atom0634Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (228441600 : Int) atom0635Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101130120 : Int) atom0636Coded) (CoefficientMerge.scale (235482120 : Int) atom0637Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (199784880 : Int) atom0638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (213034320 : Int) atom0639Coded) (CoefficientMerge.scale (115344000 : Int) atom0640Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226886400 : Int) atom0641Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (223084800 : Int) atom0642Coded) (CoefficientMerge.scale (119750400 : Int) atom0643Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (247622400 : Int) atom0644Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (108864000 : Int) atom0645Coded) (CoefficientMerge.scale (35465688 : Int) atom0646Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83210112 : Int) atom0647Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65111040 : Int) atom0648Coded) (CoefficientMerge.scale (101443968 : Int) atom0649Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77114160 : Int) atom0650Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (216736560 : Int) atom0651Coded) (CoefficientMerge.scale (210325680 : Int) atom0652Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (232889040 : Int) atom0653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118713600 : Int) atom0654Coded) (CoefficientMerge.scale (244131840 : Int) atom0655Coded)))))) := by
  rw [block008_data_flat044_step, block008_data_flat020_original, block008_data_flat043_original]
def block008_data_flat045 : CoefficientMerge.Poly := [(nat_lit 2444, Int.ofNat (nat_lit 250836480))]
theorem block008_data_flat045_step : block008_data_flat045 = (CoefficientMerge.scale (250836480 : Int) atom0656Coded) := by decide +kernel
theorem block008_data_flat045_original : block008_data_flat045 = (CoefficientMerge.scale (250836480 : Int) atom0656Coded) := by
  rw [block008_data_flat045_step]
def block008_data_flat046 : CoefficientMerge.Poly := [(nat_lit 2458, Int.ofNat (nat_lit 131725440))]
theorem block008_data_flat046_step : block008_data_flat046 = (CoefficientMerge.scale (131725440 : Int) atom0657Coded) := by decide +kernel
theorem block008_data_flat046_original : block008_data_flat046 = (CoefficientMerge.scale (131725440 : Int) atom0657Coded) := by
  rw [block008_data_flat046_step]
def block008_data_flat047 : CoefficientMerge.Poly := [(nat_lit 2444, Int.ofNat (nat_lit 250836480)), (nat_lit 2458, Int.ofNat (nat_lit 131725440))]
theorem block008_data_flat047_step : block008_data_flat047 = (CoefficientMerge.fastMerge block008_data_flat045 block008_data_flat046) := by decide +kernel
theorem block008_data_flat047_original : block008_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (250836480 : Int) atom0656Coded) (CoefficientMerge.scale (131725440 : Int) atom0657Coded)) := by
  rw [block008_data_flat047_step, block008_data_flat045_original, block008_data_flat046_original]
def block008_data_flat048 : CoefficientMerge.Poly := [(nat_lit 2459, Int.ofNat (nat_lit 283271040))]
theorem block008_data_flat048_step : block008_data_flat048 = (CoefficientMerge.scale (283271040 : Int) atom0658Coded) := by decide +kernel
theorem block008_data_flat048_original : block008_data_flat048 = (CoefficientMerge.scale (283271040 : Int) atom0658Coded) := by
  rw [block008_data_flat048_step]
def block008_data_flat049 : CoefficientMerge.Poly := [(nat_lit 2474, Int.ofNat (nat_lit 130636800))]
theorem block008_data_flat049_step : block008_data_flat049 = (CoefficientMerge.scale (130636800 : Int) atom0659Coded) := by decide +kernel
theorem block008_data_flat049_original : block008_data_flat049 = (CoefficientMerge.scale (130636800 : Int) atom0659Coded) := by
  rw [block008_data_flat049_step]
def block008_data_flat050 : CoefficientMerge.Poly := [(nat_lit 2651, Int.ofNat (nat_lit 31014360))]
theorem block008_data_flat050_step : block008_data_flat050 = (CoefficientMerge.scale (31014360 : Int) atom0660Coded) := by decide +kernel
theorem block008_data_flat050_original : block008_data_flat050 = (CoefficientMerge.scale (31014360 : Int) atom0660Coded) := by
  rw [block008_data_flat050_step]
def block008_data_flat051 : CoefficientMerge.Poly := [(nat_lit 2474, Int.ofNat (nat_lit 130636800)), (nat_lit 2651, Int.ofNat (nat_lit 31014360))]
theorem block008_data_flat051_step : block008_data_flat051 = (CoefficientMerge.fastMerge block008_data_flat049 block008_data_flat050) := by decide +kernel
theorem block008_data_flat051_original : block008_data_flat051 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (130636800 : Int) atom0659Coded) (CoefficientMerge.scale (31014360 : Int) atom0660Coded)) := by
  rw [block008_data_flat051_step, block008_data_flat049_original, block008_data_flat050_original]
def block008_data_flat052 : CoefficientMerge.Poly := [(nat_lit 2459, Int.ofNat (nat_lit 283271040)), (nat_lit 2474, Int.ofNat (nat_lit 130636800)), (nat_lit 2651, Int.ofNat (nat_lit 31014360))]
theorem block008_data_flat052_step : block008_data_flat052 = (CoefficientMerge.fastMerge block008_data_flat048 block008_data_flat051) := by decide +kernel
theorem block008_data_flat052_original : block008_data_flat052 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (283271040 : Int) atom0658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (130636800 : Int) atom0659Coded) (CoefficientMerge.scale (31014360 : Int) atom0660Coded))) := by
  rw [block008_data_flat052_step, block008_data_flat048_original, block008_data_flat051_original]
def block008_data_flat053 : CoefficientMerge.Poly := [(nat_lit 2444, Int.ofNat (nat_lit 250836480)), (nat_lit 2458, Int.ofNat (nat_lit 131725440)), (nat_lit 2459, Int.ofNat (nat_lit 283271040)), (nat_lit 2474, Int.ofNat (nat_lit 130636800)), (nat_lit 2651, Int.ofNat (nat_lit 31014360))]
theorem block008_data_flat053_step : block008_data_flat053 = (CoefficientMerge.fastMerge block008_data_flat047 block008_data_flat052) := by decide +kernel
theorem block008_data_flat053_original : block008_data_flat053 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250836480 : Int) atom0656Coded) (CoefficientMerge.scale (131725440 : Int) atom0657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283271040 : Int) atom0658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (130636800 : Int) atom0659Coded) (CoefficientMerge.scale (31014360 : Int) atom0660Coded)))) := by
  rw [block008_data_flat053_step, block008_data_flat047_original, block008_data_flat052_original]
def block008_data_flat054 : CoefficientMerge.Poly := [(nat_lit 2652, Int.ofNat (nat_lit 108981720))]
theorem block008_data_flat054_step : block008_data_flat054 = (CoefficientMerge.scale (108981720 : Int) atom0661Coded) := by decide +kernel
theorem block008_data_flat054_original : block008_data_flat054 = (CoefficientMerge.scale (108981720 : Int) atom0661Coded) := by
  rw [block008_data_flat054_step]
def block008_data_flat055 : CoefficientMerge.Poly := [(nat_lit 2653, Int.ofNat (nat_lit 110433240))]
theorem block008_data_flat055_step : block008_data_flat055 = (CoefficientMerge.scale (110433240 : Int) atom0662Coded) := by decide +kernel
theorem block008_data_flat055_original : block008_data_flat055 = (CoefficientMerge.scale (110433240 : Int) atom0662Coded) := by
  rw [block008_data_flat055_step]
def block008_data_flat056 : CoefficientMerge.Poly := [(nat_lit 2654, Int.ofNat (nat_lit 86427000))]
theorem block008_data_flat056_step : block008_data_flat056 = (CoefficientMerge.scale (86427000 : Int) atom0663Coded) := by decide +kernel
theorem block008_data_flat056_original : block008_data_flat056 = (CoefficientMerge.scale (86427000 : Int) atom0663Coded) := by
  rw [block008_data_flat056_step]
def block008_data_flat057 : CoefficientMerge.Poly := [(nat_lit 2653, Int.ofNat (nat_lit 110433240)), (nat_lit 2654, Int.ofNat (nat_lit 86427000))]
theorem block008_data_flat057_step : block008_data_flat057 = (CoefficientMerge.fastMerge block008_data_flat055 block008_data_flat056) := by decide +kernel
theorem block008_data_flat057_original : block008_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (110433240 : Int) atom0662Coded) (CoefficientMerge.scale (86427000 : Int) atom0663Coded)) := by
  rw [block008_data_flat057_step, block008_data_flat055_original, block008_data_flat056_original]
def block008_data_flat058 : CoefficientMerge.Poly := [(nat_lit 2652, Int.ofNat (nat_lit 108981720)), (nat_lit 2653, Int.ofNat (nat_lit 110433240)), (nat_lit 2654, Int.ofNat (nat_lit 86427000))]
theorem block008_data_flat058_step : block008_data_flat058 = (CoefficientMerge.fastMerge block008_data_flat054 block008_data_flat057) := by decide +kernel
theorem block008_data_flat058_original : block008_data_flat058 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (108981720 : Int) atom0661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110433240 : Int) atom0662Coded) (CoefficientMerge.scale (86427000 : Int) atom0663Coded))) := by
  rw [block008_data_flat058_step, block008_data_flat054_original, block008_data_flat057_original]
def block008_data_flat059 : CoefficientMerge.Poly := [(nat_lit 2667, Int.ofNat (nat_lit 122083200))]
theorem block008_data_flat059_step : block008_data_flat059 = (CoefficientMerge.scale (122083200 : Int) atom0664Coded) := by decide +kernel
theorem block008_data_flat059_original : block008_data_flat059 = (CoefficientMerge.scale (122083200 : Int) atom0664Coded) := by
  rw [block008_data_flat059_step]
def block008_data_flat060 : CoefficientMerge.Poly := [(nat_lit 2668, Int.ofNat (nat_lit 261377280))]
theorem block008_data_flat060_step : block008_data_flat060 = (CoefficientMerge.scale (261377280 : Int) atom0665Coded) := by decide +kernel
theorem block008_data_flat060_original : block008_data_flat060 = (CoefficientMerge.scale (261377280 : Int) atom0665Coded) := by
  rw [block008_data_flat060_step]
def block008_data_flat061 : CoefficientMerge.Poly := [(nat_lit 2669, Int.ofNat (nat_lit 198698400))]
theorem block008_data_flat061_step : block008_data_flat061 = (CoefficientMerge.scale (198698400 : Int) atom0666Coded) := by decide +kernel
theorem block008_data_flat061_original : block008_data_flat061 = (CoefficientMerge.scale (198698400 : Int) atom0666Coded) := by
  rw [block008_data_flat061_step]
def block008_data_flat062 : CoefficientMerge.Poly := [(nat_lit 2668, Int.ofNat (nat_lit 261377280)), (nat_lit 2669, Int.ofNat (nat_lit 198698400))]
theorem block008_data_flat062_step : block008_data_flat062 = (CoefficientMerge.fastMerge block008_data_flat060 block008_data_flat061) := by decide +kernel
theorem block008_data_flat062_original : block008_data_flat062 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (261377280 : Int) atom0665Coded) (CoefficientMerge.scale (198698400 : Int) atom0666Coded)) := by
  rw [block008_data_flat062_step, block008_data_flat060_original, block008_data_flat061_original]
def block008_data_flat063 : CoefficientMerge.Poly := [(nat_lit 2667, Int.ofNat (nat_lit 122083200)), (nat_lit 2668, Int.ofNat (nat_lit 261377280)), (nat_lit 2669, Int.ofNat (nat_lit 198698400))]
theorem block008_data_flat063_step : block008_data_flat063 = (CoefficientMerge.fastMerge block008_data_flat059 block008_data_flat062) := by decide +kernel
theorem block008_data_flat063_original : block008_data_flat063 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (122083200 : Int) atom0664Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (261377280 : Int) atom0665Coded) (CoefficientMerge.scale (198698400 : Int) atom0666Coded))) := by
  rw [block008_data_flat063_step, block008_data_flat059_original, block008_data_flat062_original]
def block008_data_flat064 : CoefficientMerge.Poly := [(nat_lit 2652, Int.ofNat (nat_lit 108981720)), (nat_lit 2653, Int.ofNat (nat_lit 110433240)), (nat_lit 2654, Int.ofNat (nat_lit 86427000)), (nat_lit 2667, Int.ofNat (nat_lit 122083200)), (nat_lit 2668, Int.ofNat (nat_lit 261377280)), (nat_lit 2669, Int.ofNat (nat_lit 198698400))]
theorem block008_data_flat064_step : block008_data_flat064 = (CoefficientMerge.fastMerge block008_data_flat058 block008_data_flat063) := by decide +kernel
theorem block008_data_flat064_original : block008_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (108981720 : Int) atom0661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110433240 : Int) atom0662Coded) (CoefficientMerge.scale (86427000 : Int) atom0663Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122083200 : Int) atom0664Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (261377280 : Int) atom0665Coded) (CoefficientMerge.scale (198698400 : Int) atom0666Coded)))) := by
  rw [block008_data_flat064_step, block008_data_flat058_original, block008_data_flat063_original]
def block008_data_flat065 : CoefficientMerge.Poly := [(nat_lit 2444, Int.ofNat (nat_lit 250836480)), (nat_lit 2458, Int.ofNat (nat_lit 131725440)), (nat_lit 2459, Int.ofNat (nat_lit 283271040)), (nat_lit 2474, Int.ofNat (nat_lit 130636800)), (nat_lit 2651, Int.ofNat (nat_lit 31014360)), (nat_lit 2652, Int.ofNat (nat_lit 108981720)), (nat_lit 2653, Int.ofNat (nat_lit 110433240)), (nat_lit 2654, Int.ofNat (nat_lit 86427000)), (nat_lit 2667, Int.ofNat (nat_lit 122083200)), (nat_lit 2668, Int.ofNat (nat_lit 261377280)), (nat_lit 2669, Int.ofNat (nat_lit 198698400))]
theorem block008_data_flat065_step : block008_data_flat065 = (CoefficientMerge.fastMerge block008_data_flat053 block008_data_flat064) := by decide +kernel
theorem block008_data_flat065_original : block008_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250836480 : Int) atom0656Coded) (CoefficientMerge.scale (131725440 : Int) atom0657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283271040 : Int) atom0658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (130636800 : Int) atom0659Coded) (CoefficientMerge.scale (31014360 : Int) atom0660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (108981720 : Int) atom0661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110433240 : Int) atom0662Coded) (CoefficientMerge.scale (86427000 : Int) atom0663Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122083200 : Int) atom0664Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (261377280 : Int) atom0665Coded) (CoefficientMerge.scale (198698400 : Int) atom0666Coded))))) := by
  rw [block008_data_flat065_step, block008_data_flat053_original, block008_data_flat064_original]
def block008_data_flat066 : CoefficientMerge.Poly := [(nat_lit 2683, Int.ofNat (nat_lit 143700480))]
theorem block008_data_flat066_step : block008_data_flat066 = (CoefficientMerge.scale (143700480 : Int) atom0667Coded) := by decide +kernel
theorem block008_data_flat066_original : block008_data_flat066 = (CoefficientMerge.scale (143700480 : Int) atom0667Coded) := by
  rw [block008_data_flat066_step]
def block008_data_flat067 : CoefficientMerge.Poly := [(nat_lit 2684, Int.ofNat (nat_lit 239029920))]
theorem block008_data_flat067_step : block008_data_flat067 = (CoefficientMerge.scale (239029920 : Int) atom0668Coded) := by decide +kernel
theorem block008_data_flat067_original : block008_data_flat067 = (CoefficientMerge.scale (239029920 : Int) atom0668Coded) := by
  rw [block008_data_flat067_step]
def block008_data_flat068 : CoefficientMerge.Poly := [(nat_lit 2699, Int.ofNat (nat_lit 72519840))]
theorem block008_data_flat068_step : block008_data_flat068 = (CoefficientMerge.scale (72519840 : Int) atom0669Coded) := by decide +kernel
theorem block008_data_flat068_original : block008_data_flat068 = (CoefficientMerge.scale (72519840 : Int) atom0669Coded) := by
  rw [block008_data_flat068_step]
def block008_data_flat069 : CoefficientMerge.Poly := [(nat_lit 2684, Int.ofNat (nat_lit 239029920)), (nat_lit 2699, Int.ofNat (nat_lit 72519840))]
theorem block008_data_flat069_step : block008_data_flat069 = (CoefficientMerge.fastMerge block008_data_flat067 block008_data_flat068) := by decide +kernel
theorem block008_data_flat069_original : block008_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (239029920 : Int) atom0668Coded) (CoefficientMerge.scale (72519840 : Int) atom0669Coded)) := by
  rw [block008_data_flat069_step, block008_data_flat067_original, block008_data_flat068_original]
def block008_data_flat070 : CoefficientMerge.Poly := [(nat_lit 2683, Int.ofNat (nat_lit 143700480)), (nat_lit 2684, Int.ofNat (nat_lit 239029920)), (nat_lit 2699, Int.ofNat (nat_lit 72519840))]
theorem block008_data_flat070_step : block008_data_flat070 = (CoefficientMerge.fastMerge block008_data_flat066 block008_data_flat069) := by decide +kernel
theorem block008_data_flat070_original : block008_data_flat070 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (143700480 : Int) atom0667Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (239029920 : Int) atom0668Coded) (CoefficientMerge.scale (72519840 : Int) atom0669Coded))) := by
  rw [block008_data_flat070_step, block008_data_flat066_original, block008_data_flat069_original]
def block008_data_flat071 : CoefficientMerge.Poly := [(nat_lit 2892, Int.ofNat (nat_lit 41817600))]
theorem block008_data_flat071_step : block008_data_flat071 = (CoefficientMerge.scale (41817600 : Int) atom0670Coded) := by decide +kernel
theorem block008_data_flat071_original : block008_data_flat071 = (CoefficientMerge.scale (41817600 : Int) atom0670Coded) := by
  rw [block008_data_flat071_step]
def block008_data_flat072 : CoefficientMerge.Poly := [(nat_lit 2893, Int.ofNat (nat_lit 139311360))]
theorem block008_data_flat072_step : block008_data_flat072 = (CoefficientMerge.scale (139311360 : Int) atom0671Coded) := by decide +kernel
theorem block008_data_flat072_original : block008_data_flat072 = (CoefficientMerge.scale (139311360 : Int) atom0671Coded) := by
  rw [block008_data_flat072_step]
def block008_data_flat073 : CoefficientMerge.Poly := [(nat_lit 2894, Int.ofNat (nat_lit 98737920))]
theorem block008_data_flat073_step : block008_data_flat073 = (CoefficientMerge.scale (98737920 : Int) atom0672Coded) := by decide +kernel
theorem block008_data_flat073_original : block008_data_flat073 = (CoefficientMerge.scale (98737920 : Int) atom0672Coded) := by
  rw [block008_data_flat073_step]
def block008_data_flat074 : CoefficientMerge.Poly := [(nat_lit 2893, Int.ofNat (nat_lit 139311360)), (nat_lit 2894, Int.ofNat (nat_lit 98737920))]
theorem block008_data_flat074_step : block008_data_flat074 = (CoefficientMerge.fastMerge block008_data_flat072 block008_data_flat073) := by decide +kernel
theorem block008_data_flat074_original : block008_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (139311360 : Int) atom0671Coded) (CoefficientMerge.scale (98737920 : Int) atom0672Coded)) := by
  rw [block008_data_flat074_step, block008_data_flat072_original, block008_data_flat073_original]
def block008_data_flat075 : CoefficientMerge.Poly := [(nat_lit 2892, Int.ofNat (nat_lit 41817600)), (nat_lit 2893, Int.ofNat (nat_lit 139311360)), (nat_lit 2894, Int.ofNat (nat_lit 98737920))]
theorem block008_data_flat075_step : block008_data_flat075 = (CoefficientMerge.fastMerge block008_data_flat071 block008_data_flat074) := by decide +kernel
theorem block008_data_flat075_original : block008_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (41817600 : Int) atom0670Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (139311360 : Int) atom0671Coded) (CoefficientMerge.scale (98737920 : Int) atom0672Coded))) := by
  rw [block008_data_flat075_step, block008_data_flat071_original, block008_data_flat074_original]
def block008_data_flat076 : CoefficientMerge.Poly := [(nat_lit 2683, Int.ofNat (nat_lit 143700480)), (nat_lit 2684, Int.ofNat (nat_lit 239029920)), (nat_lit 2699, Int.ofNat (nat_lit 72519840)), (nat_lit 2892, Int.ofNat (nat_lit 41817600)), (nat_lit 2893, Int.ofNat (nat_lit 139311360)), (nat_lit 2894, Int.ofNat (nat_lit 98737920))]
theorem block008_data_flat076_step : block008_data_flat076 = (CoefficientMerge.fastMerge block008_data_flat070 block008_data_flat075) := by decide +kernel
theorem block008_data_flat076_original : block008_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (143700480 : Int) atom0667Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (239029920 : Int) atom0668Coded) (CoefficientMerge.scale (72519840 : Int) atom0669Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41817600 : Int) atom0670Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (139311360 : Int) atom0671Coded) (CoefficientMerge.scale (98737920 : Int) atom0672Coded)))) := by
  rw [block008_data_flat076_step, block008_data_flat070_original, block008_data_flat075_original]
def block008_data_flat077 : CoefficientMerge.Poly := [(nat_lit 2908, Int.ofNat (nat_lit 155675520))]
theorem block008_data_flat077_step : block008_data_flat077 = (CoefficientMerge.scale (155675520 : Int) atom0673Coded) := by decide +kernel
theorem block008_data_flat077_original : block008_data_flat077 = (CoefficientMerge.scale (155675520 : Int) atom0673Coded) := by
  rw [block008_data_flat077_step]
def block008_data_flat078 : CoefficientMerge.Poly := [(nat_lit 2909, Int.ofNat (nat_lit 245704320))]
theorem block008_data_flat078_step : block008_data_flat078 = (CoefficientMerge.scale (245704320 : Int) atom0674Coded) := by decide +kernel
theorem block008_data_flat078_original : block008_data_flat078 = (CoefficientMerge.scale (245704320 : Int) atom0674Coded) := by
  rw [block008_data_flat078_step]
def block008_data_flat079 : CoefficientMerge.Poly := [(nat_lit 2924, Int.ofNat (nat_lit 65318400))]
theorem block008_data_flat079_step : block008_data_flat079 = (CoefficientMerge.scale (65318400 : Int) atom0675Coded) := by decide +kernel
theorem block008_data_flat079_original : block008_data_flat079 = (CoefficientMerge.scale (65318400 : Int) atom0675Coded) := by
  rw [block008_data_flat079_step]
def block008_data_flat080 : CoefficientMerge.Poly := [(nat_lit 2909, Int.ofNat (nat_lit 245704320)), (nat_lit 2924, Int.ofNat (nat_lit 65318400))]
theorem block008_data_flat080_step : block008_data_flat080 = (CoefficientMerge.fastMerge block008_data_flat078 block008_data_flat079) := by decide +kernel
theorem block008_data_flat080_original : block008_data_flat080 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (245704320 : Int) atom0674Coded) (CoefficientMerge.scale (65318400 : Int) atom0675Coded)) := by
  rw [block008_data_flat080_step, block008_data_flat078_original, block008_data_flat079_original]
def block008_data_flat081 : CoefficientMerge.Poly := [(nat_lit 2908, Int.ofNat (nat_lit 155675520)), (nat_lit 2909, Int.ofNat (nat_lit 245704320)), (nat_lit 2924, Int.ofNat (nat_lit 65318400))]
theorem block008_data_flat081_step : block008_data_flat081 = (CoefficientMerge.fastMerge block008_data_flat077 block008_data_flat080) := by decide +kernel
theorem block008_data_flat081_original : block008_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (155675520 : Int) atom0673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245704320 : Int) atom0674Coded) (CoefficientMerge.scale (65318400 : Int) atom0675Coded))) := by
  rw [block008_data_flat081_step, block008_data_flat077_original, block008_data_flat080_original]
def block008_data_flat082 : CoefficientMerge.Poly := [(nat_lit 3133, Int.ofNat (nat_lit 55883520))]
theorem block008_data_flat082_step : block008_data_flat082 = (CoefficientMerge.scale (55883520 : Int) atom0676Coded) := by decide +kernel
theorem block008_data_flat082_original : block008_data_flat082 = (CoefficientMerge.scale (55883520 : Int) atom0676Coded) := by
  rw [block008_data_flat082_step]
def block008_data_flat083 : CoefficientMerge.Poly := [(nat_lit 3134, Int.ofNat (nat_lit 140676480))]
theorem block008_data_flat083_step : block008_data_flat083 = (CoefficientMerge.scale (140676480 : Int) atom0677Coded) := by decide +kernel
theorem block008_data_flat083_original : block008_data_flat083 = (CoefficientMerge.scale (140676480 : Int) atom0677Coded) := by
  rw [block008_data_flat083_step]
def block008_data_flat084 : CoefficientMerge.Poly := [(nat_lit 3149, Int.ofNat (nat_lit 87091200))]
theorem block008_data_flat084_step : block008_data_flat084 = (CoefficientMerge.scale (87091200 : Int) atom0678Coded) := by decide +kernel
theorem block008_data_flat084_original : block008_data_flat084 = (CoefficientMerge.scale (87091200 : Int) atom0678Coded) := by
  rw [block008_data_flat084_step]
def block008_data_flat085 : CoefficientMerge.Poly := [(nat_lit 3134, Int.ofNat (nat_lit 140676480)), (nat_lit 3149, Int.ofNat (nat_lit 87091200))]
theorem block008_data_flat085_step : block008_data_flat085 = (CoefficientMerge.fastMerge block008_data_flat083 block008_data_flat084) := by decide +kernel
theorem block008_data_flat085_original : block008_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (140676480 : Int) atom0677Coded) (CoefficientMerge.scale (87091200 : Int) atom0678Coded)) := by
  rw [block008_data_flat085_step, block008_data_flat083_original, block008_data_flat084_original]
def block008_data_flat086 : CoefficientMerge.Poly := [(nat_lit 3133, Int.ofNat (nat_lit 55883520)), (nat_lit 3134, Int.ofNat (nat_lit 140676480)), (nat_lit 3149, Int.ofNat (nat_lit 87091200))]
theorem block008_data_flat086_step : block008_data_flat086 = (CoefficientMerge.fastMerge block008_data_flat082 block008_data_flat085) := by decide +kernel
theorem block008_data_flat086_original : block008_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (55883520 : Int) atom0676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140676480 : Int) atom0677Coded) (CoefficientMerge.scale (87091200 : Int) atom0678Coded))) := by
  rw [block008_data_flat086_step, block008_data_flat082_original, block008_data_flat085_original]
def block008_data_flat087 : CoefficientMerge.Poly := [(nat_lit 2908, Int.ofNat (nat_lit 155675520)), (nat_lit 2909, Int.ofNat (nat_lit 245704320)), (nat_lit 2924, Int.ofNat (nat_lit 65318400)), (nat_lit 3133, Int.ofNat (nat_lit 55883520)), (nat_lit 3134, Int.ofNat (nat_lit 140676480)), (nat_lit 3149, Int.ofNat (nat_lit 87091200))]
theorem block008_data_flat087_step : block008_data_flat087 = (CoefficientMerge.fastMerge block008_data_flat081 block008_data_flat086) := by decide +kernel
theorem block008_data_flat087_original : block008_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (155675520 : Int) atom0673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245704320 : Int) atom0674Coded) (CoefficientMerge.scale (65318400 : Int) atom0675Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55883520 : Int) atom0676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140676480 : Int) atom0677Coded) (CoefficientMerge.scale (87091200 : Int) atom0678Coded)))) := by
  rw [block008_data_flat087_step, block008_data_flat081_original, block008_data_flat086_original]
def block008_data_flat088 : CoefficientMerge.Poly := [(nat_lit 2683, Int.ofNat (nat_lit 143700480)), (nat_lit 2684, Int.ofNat (nat_lit 239029920)), (nat_lit 2699, Int.ofNat (nat_lit 72519840)), (nat_lit 2892, Int.ofNat (nat_lit 41817600)), (nat_lit 2893, Int.ofNat (nat_lit 139311360)), (nat_lit 2894, Int.ofNat (nat_lit 98737920)), (nat_lit 2908, Int.ofNat (nat_lit 155675520)), (nat_lit 2909, Int.ofNat (nat_lit 245704320)), (nat_lit 2924, Int.ofNat (nat_lit 65318400)), (nat_lit 3133, Int.ofNat (nat_lit 55883520)), (nat_lit 3134, Int.ofNat (nat_lit 140676480)), (nat_lit 3149, Int.ofNat (nat_lit 87091200))]
theorem block008_data_flat088_step : block008_data_flat088 = (CoefficientMerge.fastMerge block008_data_flat076 block008_data_flat087) := by decide +kernel
theorem block008_data_flat088_original : block008_data_flat088 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (143700480 : Int) atom0667Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (239029920 : Int) atom0668Coded) (CoefficientMerge.scale (72519840 : Int) atom0669Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41817600 : Int) atom0670Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (139311360 : Int) atom0671Coded) (CoefficientMerge.scale (98737920 : Int) atom0672Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (155675520 : Int) atom0673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245704320 : Int) atom0674Coded) (CoefficientMerge.scale (65318400 : Int) atom0675Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55883520 : Int) atom0676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140676480 : Int) atom0677Coded) (CoefficientMerge.scale (87091200 : Int) atom0678Coded))))) := by
  rw [block008_data_flat088_step, block008_data_flat076_original, block008_data_flat087_original]
def block008_data_flat089 : CoefficientMerge.Poly := [(nat_lit 2444, Int.ofNat (nat_lit 250836480)), (nat_lit 2458, Int.ofNat (nat_lit 131725440)), (nat_lit 2459, Int.ofNat (nat_lit 283271040)), (nat_lit 2474, Int.ofNat (nat_lit 130636800)), (nat_lit 2651, Int.ofNat (nat_lit 31014360)), (nat_lit 2652, Int.ofNat (nat_lit 108981720)), (nat_lit 2653, Int.ofNat (nat_lit 110433240)), (nat_lit 2654, Int.ofNat (nat_lit 86427000)), (nat_lit 2667, Int.ofNat (nat_lit 122083200)), (nat_lit 2668, Int.ofNat (nat_lit 261377280)), (nat_lit 2669, Int.ofNat (nat_lit 198698400)), (nat_lit 2683, Int.ofNat (nat_lit 143700480)), (nat_lit 2684, Int.ofNat (nat_lit 239029920)), (nat_lit 2699, Int.ofNat (nat_lit 72519840)), (nat_lit 2892, Int.ofNat (nat_lit 41817600)), (nat_lit 2893, Int.ofNat (nat_lit 139311360)), (nat_lit 2894, Int.ofNat (nat_lit 98737920)), (nat_lit 2908, Int.ofNat (nat_lit 155675520)), (nat_lit 2909, Int.ofNat (nat_lit 245704320)), (nat_lit 2924, Int.ofNat (nat_lit 65318400)), (nat_lit 3133, Int.ofNat (nat_lit 55883520)), (nat_lit 3134, Int.ofNat (nat_lit 140676480)), (nat_lit 3149, Int.ofNat (nat_lit 87091200))]
theorem block008_data_flat089_step : block008_data_flat089 = (CoefficientMerge.fastMerge block008_data_flat065 block008_data_flat088) := by decide +kernel
theorem block008_data_flat089_original : block008_data_flat089 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250836480 : Int) atom0656Coded) (CoefficientMerge.scale (131725440 : Int) atom0657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283271040 : Int) atom0658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (130636800 : Int) atom0659Coded) (CoefficientMerge.scale (31014360 : Int) atom0660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (108981720 : Int) atom0661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110433240 : Int) atom0662Coded) (CoefficientMerge.scale (86427000 : Int) atom0663Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122083200 : Int) atom0664Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (261377280 : Int) atom0665Coded) (CoefficientMerge.scale (198698400 : Int) atom0666Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (143700480 : Int) atom0667Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (239029920 : Int) atom0668Coded) (CoefficientMerge.scale (72519840 : Int) atom0669Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41817600 : Int) atom0670Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (139311360 : Int) atom0671Coded) (CoefficientMerge.scale (98737920 : Int) atom0672Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (155675520 : Int) atom0673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245704320 : Int) atom0674Coded) (CoefficientMerge.scale (65318400 : Int) atom0675Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55883520 : Int) atom0676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140676480 : Int) atom0677Coded) (CoefficientMerge.scale (87091200 : Int) atom0678Coded)))))) := by
  rw [block008_data_flat089_step, block008_data_flat065_original, block008_data_flat088_original]
def block008_data_flat090 : CoefficientMerge.Poly := [(nat_lit 2187, Int.ofNat (nat_lit 202089600)), (nat_lit 2188, Int.ofNat (nat_lit 147225600)), (nat_lit 2189, Int.ofNat (nat_lit 228441600)), (nat_lit 2201, Int.ofNat (nat_lit 101130120)), (nat_lit 2202, Int.ofNat (nat_lit 235482120)), (nat_lit 2203, Int.ofNat (nat_lit 199784880)), (nat_lit 2204, Int.ofNat (nat_lit 213034320)), (nat_lit 2217, Int.ofNat (nat_lit 115344000)), (nat_lit 2218, Int.ofNat (nat_lit 226886400)), (nat_lit 2219, Int.ofNat (nat_lit 223084800)), (nat_lit 2233, Int.ofNat (nat_lit 119750400)), (nat_lit 2234, Int.ofNat (nat_lit 247622400)), (nat_lit 2249, Int.ofNat (nat_lit 108864000)), (nat_lit 2411, Int.ofNat (nat_lit 35465688)), (nat_lit 2412, Int.ofNat (nat_lit 83210112)), (nat_lit 2413, Int.ofNat (nat_lit 65111040)), (nat_lit 2414, Int.ofNat (nat_lit 101443968)), (nat_lit 2426, Int.ofNat (nat_lit 77114160)), (nat_lit 2427, Int.ofNat (nat_lit 216736560)), (nat_lit 2428, Int.ofNat (nat_lit 210325680)), (nat_lit 2429, Int.ofNat (nat_lit 232889040)), (nat_lit 2442, Int.ofNat (nat_lit 118713600)), (nat_lit 2443, Int.ofNat (nat_lit 244131840)), (nat_lit 2444, Int.ofNat (nat_lit 250836480)), (nat_lit 2458, Int.ofNat (nat_lit 131725440)), (nat_lit 2459, Int.ofNat (nat_lit 283271040)), (nat_lit 2474, Int.ofNat (nat_lit 130636800)), (nat_lit 2651, Int.ofNat (nat_lit 31014360)), (nat_lit 2652, Int.ofNat (nat_lit 108981720)), (nat_lit 2653, Int.ofNat (nat_lit 110433240)), (nat_lit 2654, Int.ofNat (nat_lit 86427000)), (nat_lit 2667, Int.ofNat (nat_lit 122083200)), (nat_lit 2668, Int.ofNat (nat_lit 261377280)), (nat_lit 2669, Int.ofNat (nat_lit 198698400)), (nat_lit 2683, Int.ofNat (nat_lit 143700480)), (nat_lit 2684, Int.ofNat (nat_lit 239029920)), (nat_lit 2699, Int.ofNat (nat_lit 72519840)), (nat_lit 2892, Int.ofNat (nat_lit 41817600)), (nat_lit 2893, Int.ofNat (nat_lit 139311360)), (nat_lit 2894, Int.ofNat (nat_lit 98737920)), (nat_lit 2908, Int.ofNat (nat_lit 155675520)), (nat_lit 2909, Int.ofNat (nat_lit 245704320)), (nat_lit 2924, Int.ofNat (nat_lit 65318400)), (nat_lit 3133, Int.ofNat (nat_lit 55883520)), (nat_lit 3134, Int.ofNat (nat_lit 140676480)), (nat_lit 3149, Int.ofNat (nat_lit 87091200))]
theorem block008_data_flat090_step : block008_data_flat090 = (CoefficientMerge.fastMerge block008_data_flat044 block008_data_flat089) := by decide +kernel
theorem block008_data_flat090_original : block008_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (202089600 : Int) atom0633Coded) (CoefficientMerge.scale (147225600 : Int) atom0634Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (228441600 : Int) atom0635Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101130120 : Int) atom0636Coded) (CoefficientMerge.scale (235482120 : Int) atom0637Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (199784880 : Int) atom0638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (213034320 : Int) atom0639Coded) (CoefficientMerge.scale (115344000 : Int) atom0640Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226886400 : Int) atom0641Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (223084800 : Int) atom0642Coded) (CoefficientMerge.scale (119750400 : Int) atom0643Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (247622400 : Int) atom0644Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (108864000 : Int) atom0645Coded) (CoefficientMerge.scale (35465688 : Int) atom0646Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83210112 : Int) atom0647Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65111040 : Int) atom0648Coded) (CoefficientMerge.scale (101443968 : Int) atom0649Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77114160 : Int) atom0650Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (216736560 : Int) atom0651Coded) (CoefficientMerge.scale (210325680 : Int) atom0652Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (232889040 : Int) atom0653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118713600 : Int) atom0654Coded) (CoefficientMerge.scale (244131840 : Int) atom0655Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250836480 : Int) atom0656Coded) (CoefficientMerge.scale (131725440 : Int) atom0657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283271040 : Int) atom0658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (130636800 : Int) atom0659Coded) (CoefficientMerge.scale (31014360 : Int) atom0660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (108981720 : Int) atom0661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110433240 : Int) atom0662Coded) (CoefficientMerge.scale (86427000 : Int) atom0663Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122083200 : Int) atom0664Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (261377280 : Int) atom0665Coded) (CoefficientMerge.scale (198698400 : Int) atom0666Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (143700480 : Int) atom0667Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (239029920 : Int) atom0668Coded) (CoefficientMerge.scale (72519840 : Int) atom0669Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41817600 : Int) atom0670Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (139311360 : Int) atom0671Coded) (CoefficientMerge.scale (98737920 : Int) atom0672Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (155675520 : Int) atom0673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245704320 : Int) atom0674Coded) (CoefficientMerge.scale (65318400 : Int) atom0675Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55883520 : Int) atom0676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140676480 : Int) atom0677Coded) (CoefficientMerge.scale (87091200 : Int) atom0678Coded))))))) := by
  rw [block008_data_flat090_step, block008_data_flat044_original, block008_data_flat089_original]
def block008_data_flat091 : CoefficientMerge.Poly := [(nat_lit 2187, Int.ofNat (nat_lit 202089600)), (nat_lit 2188, Int.ofNat (nat_lit 147225600)), (nat_lit 2189, Int.ofNat (nat_lit 228441600)), (nat_lit 2201, Int.ofNat (nat_lit 101130120)), (nat_lit 2202, Int.ofNat (nat_lit 235482120)), (nat_lit 2203, Int.ofNat (nat_lit 199784880)), (nat_lit 2204, Int.ofNat (nat_lit 213034320)), (nat_lit 2217, Int.ofNat (nat_lit 115344000)), (nat_lit 2218, Int.ofNat (nat_lit 226886400)), (nat_lit 2219, Int.ofNat (nat_lit 223084800)), (nat_lit 2233, Int.ofNat (nat_lit 119750400)), (nat_lit 2234, Int.ofNat (nat_lit 247622400)), (nat_lit 2249, Int.ofNat (nat_lit 108864000)), (nat_lit 2411, Int.ofNat (nat_lit 35465688)), (nat_lit 2412, Int.ofNat (nat_lit 83210112)), (nat_lit 2413, Int.ofNat (nat_lit 65111040)), (nat_lit 2414, Int.ofNat (nat_lit 101443968)), (nat_lit 2426, Int.ofNat (nat_lit 77114160)), (nat_lit 2427, Int.ofNat (nat_lit 216736560)), (nat_lit 2428, Int.ofNat (nat_lit 210325680)), (nat_lit 2429, Int.ofNat (nat_lit 232889040)), (nat_lit 2442, Int.ofNat (nat_lit 118713600)), (nat_lit 2443, Int.ofNat (nat_lit 244131840)), (nat_lit 2444, Int.ofNat (nat_lit 250836480)), (nat_lit 2458, Int.ofNat (nat_lit 131725440)), (nat_lit 2459, Int.ofNat (nat_lit 283271040)), (nat_lit 2474, Int.ofNat (nat_lit 130636800)), (nat_lit 2651, Int.ofNat (nat_lit 31014360)), (nat_lit 2652, Int.ofNat (nat_lit 108981720)), (nat_lit 2653, Int.ofNat (nat_lit 110433240)), (nat_lit 2654, Int.ofNat (nat_lit 86427000)), (nat_lit 2667, Int.ofNat (nat_lit 122083200)), (nat_lit 2668, Int.ofNat (nat_lit 261377280)), (nat_lit 2669, Int.ofNat (nat_lit 198698400)), (nat_lit 2683, Int.ofNat (nat_lit 143700480)), (nat_lit 2684, Int.ofNat (nat_lit 239029920)), (nat_lit 2699, Int.ofNat (nat_lit 72519840)), (nat_lit 2892, Int.ofNat (nat_lit 41817600)), (nat_lit 2893, Int.ofNat (nat_lit 139311360)), (nat_lit 2894, Int.ofNat (nat_lit 98737920)), (nat_lit 2908, Int.ofNat (nat_lit 155675520)), (nat_lit 2909, Int.ofNat (nat_lit 245704320)), (nat_lit 2924, Int.ofNat (nat_lit 65318400)), (nat_lit 3133, Int.ofNat (nat_lit 55883520)), (nat_lit 3134, Int.ofNat (nat_lit 140676480)), (nat_lit 3149, Int.ofNat (nat_lit 87091200))]
theorem block008_data_flat091_step : block008_data_flat091 = (CoefficientMerge.trim block008_data_flat090) := by decide +kernel
theorem block008_data_flat091_original : block008_data_flat091 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (202089600 : Int) atom0633Coded) (CoefficientMerge.scale (147225600 : Int) atom0634Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (228441600 : Int) atom0635Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101130120 : Int) atom0636Coded) (CoefficientMerge.scale (235482120 : Int) atom0637Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (199784880 : Int) atom0638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (213034320 : Int) atom0639Coded) (CoefficientMerge.scale (115344000 : Int) atom0640Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226886400 : Int) atom0641Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (223084800 : Int) atom0642Coded) (CoefficientMerge.scale (119750400 : Int) atom0643Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (247622400 : Int) atom0644Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (108864000 : Int) atom0645Coded) (CoefficientMerge.scale (35465688 : Int) atom0646Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83210112 : Int) atom0647Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65111040 : Int) atom0648Coded) (CoefficientMerge.scale (101443968 : Int) atom0649Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77114160 : Int) atom0650Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (216736560 : Int) atom0651Coded) (CoefficientMerge.scale (210325680 : Int) atom0652Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (232889040 : Int) atom0653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118713600 : Int) atom0654Coded) (CoefficientMerge.scale (244131840 : Int) atom0655Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250836480 : Int) atom0656Coded) (CoefficientMerge.scale (131725440 : Int) atom0657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283271040 : Int) atom0658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (130636800 : Int) atom0659Coded) (CoefficientMerge.scale (31014360 : Int) atom0660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (108981720 : Int) atom0661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110433240 : Int) atom0662Coded) (CoefficientMerge.scale (86427000 : Int) atom0663Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122083200 : Int) atom0664Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (261377280 : Int) atom0665Coded) (CoefficientMerge.scale (198698400 : Int) atom0666Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (143700480 : Int) atom0667Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (239029920 : Int) atom0668Coded) (CoefficientMerge.scale (72519840 : Int) atom0669Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41817600 : Int) atom0670Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (139311360 : Int) atom0671Coded) (CoefficientMerge.scale (98737920 : Int) atom0672Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (155675520 : Int) atom0673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245704320 : Int) atom0674Coded) (CoefficientMerge.scale (65318400 : Int) atom0675Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55883520 : Int) atom0676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140676480 : Int) atom0677Coded) (CoefficientMerge.scale (87091200 : Int) atom0678Coded)))))))) := by
  rw [block008_data_flat091_step, block008_data_flat090_original]
theorem block008_data : block008 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (202089600 : Int) atom0633Coded) (CoefficientMerge.scale (147225600 : Int) atom0634Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (228441600 : Int) atom0635Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101130120 : Int) atom0636Coded) (CoefficientMerge.scale (235482120 : Int) atom0637Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (199784880 : Int) atom0638Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (213034320 : Int) atom0639Coded) (CoefficientMerge.scale (115344000 : Int) atom0640Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (226886400 : Int) atom0641Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (223084800 : Int) atom0642Coded) (CoefficientMerge.scale (119750400 : Int) atom0643Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (247622400 : Int) atom0644Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (108864000 : Int) atom0645Coded) (CoefficientMerge.scale (35465688 : Int) atom0646Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (83210112 : Int) atom0647Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (65111040 : Int) atom0648Coded) (CoefficientMerge.scale (101443968 : Int) atom0649Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (77114160 : Int) atom0650Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (216736560 : Int) atom0651Coded) (CoefficientMerge.scale (210325680 : Int) atom0652Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (232889040 : Int) atom0653Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118713600 : Int) atom0654Coded) (CoefficientMerge.scale (244131840 : Int) atom0655Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (250836480 : Int) atom0656Coded) (CoefficientMerge.scale (131725440 : Int) atom0657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283271040 : Int) atom0658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (130636800 : Int) atom0659Coded) (CoefficientMerge.scale (31014360 : Int) atom0660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (108981720 : Int) atom0661Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110433240 : Int) atom0662Coded) (CoefficientMerge.scale (86427000 : Int) atom0663Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122083200 : Int) atom0664Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (261377280 : Int) atom0665Coded) (CoefficientMerge.scale (198698400 : Int) atom0666Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (143700480 : Int) atom0667Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (239029920 : Int) atom0668Coded) (CoefficientMerge.scale (72519840 : Int) atom0669Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41817600 : Int) atom0670Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (139311360 : Int) atom0671Coded) (CoefficientMerge.scale (98737920 : Int) atom0672Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (155675520 : Int) atom0673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245704320 : Int) atom0674Coded) (CoefficientMerge.scale (65318400 : Int) atom0675Coded))) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55883520 : Int) atom0676Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140676480 : Int) atom0677Coded) (CoefficientMerge.scale (87091200 : Int) atom0678Coded))))))) := by
  have h : block008 = block008_data_flat091 := by decide +kernel
  exact h.trans block008_data_flat091_original
theorem block008_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) block008 := by
  rw [block008_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0633Coded_nonneg g hg hA hB) (atom0634Coded_nonneg g hg hA hB)) (add_nonneg (atom0635Coded_nonneg g hg hA hB) (add_nonneg (atom0636Coded_nonneg g hg hA hB) (atom0637Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0638Coded_nonneg g hg hA hB) (add_nonneg (atom0639Coded_nonneg g hg hA hB) (atom0640Coded_nonneg g hg hA hB))) (add_nonneg (atom0641Coded_nonneg g hg hA hB) (add_nonneg (atom0642Coded_nonneg g hg hA hB) (atom0643Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0644Coded_nonneg g hg hA hB) (add_nonneg (atom0645Coded_nonneg g hg hA hB) (atom0646Coded_nonneg g hg hA hB))) (add_nonneg (atom0647Coded_nonneg g hg hA hB) (add_nonneg (atom0648Coded_nonneg g hg hA hB) (atom0649Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0650Coded_nonneg g hg hA hB) (add_nonneg (atom0651Coded_nonneg g hg hA hB) (atom0652Coded_nonneg g hg hA hB))) (add_nonneg (atom0653Coded_nonneg g hg hA hB) (add_nonneg (atom0654Coded_nonneg g hg hA hB) (atom0655Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0656Coded_nonneg g hg hA hB) (atom0657Coded_nonneg g hg hA hB)) (add_nonneg (atom0658Coded_nonneg g hg hA hB) (add_nonneg (atom0659Coded_nonneg g hg hA hB) (atom0660Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0661Coded_nonneg g hg hA hB) (add_nonneg (atom0662Coded_nonneg g hg hA hB) (atom0663Coded_nonneg g hg hA hB))) (add_nonneg (atom0664Coded_nonneg g hg hA hB) (add_nonneg (atom0665Coded_nonneg g hg hA hB) (atom0666Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0667Coded_nonneg g hg hA hB) (add_nonneg (atom0668Coded_nonneg g hg hA hB) (atom0669Coded_nonneg g hg hA hB))) (add_nonneg (atom0670Coded_nonneg g hg hA hB) (add_nonneg (atom0671Coded_nonneg g hg hA hB) (atom0672Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0673Coded_nonneg g hg hA hB) (add_nonneg (atom0674Coded_nonneg g hg hA hB) (atom0675Coded_nonneg g hg hA hB))) (add_nonneg (atom0676Coded_nonneg g hg hA hB) (add_nonneg (atom0677Coded_nonneg g hg hA hB) (atom0678Coded_nonneg g hg hA hB)))))))

end APPT.Finite15
