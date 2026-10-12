-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0656 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0656 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0656 = ((g 2) * (g 7) * (g 8)) := by
  norm_num [atom0656, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0656_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37423734021504 : Int) atom0656) := by
  rw [SparsePolynomial.eval_scale, eval_atom0656]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0656Coded : CoefficientMerge.Poly := [(nat_lit 1037, Int.ofNat (nat_lit 1))]
theorem atom0656Coded_decode : atom0656 = SparsePolynomial.decodeCubic 21 atom0656Coded := by decide +kernel
theorem atom0656Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37423734021504 : Int) atom0656Coded) := by
  have h := atom0656_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0656Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0657 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0657 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0657 = ((g 2) * (g 7) * (g 9)) := by
  norm_num [atom0657, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0657_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34748060719104 : Int) atom0657) := by
  rw [SparsePolynomial.eval_scale, eval_atom0657]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0657Coded : CoefficientMerge.Poly := [(nat_lit 1038, Int.ofNat (nat_lit 1))]
theorem atom0657Coded_decode : atom0657 = SparsePolynomial.decodeCubic 21 atom0657Coded := by decide +kernel
theorem atom0657Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34748060719104 : Int) atom0657Coded) := by
  have h := atom0657_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0657Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0658 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0658 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0658 = ((g 2) * (g 7) * (g 10)) := by
  norm_num [atom0658, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0658_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34509342530304 : Int) atom0658) := by
  rw [SparsePolynomial.eval_scale, eval_atom0658]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0658Coded : CoefficientMerge.Poly := [(nat_lit 1039, Int.ofNat (nat_lit 1))]
theorem atom0658Coded_decode : atom0658 = SparsePolynomial.decodeCubic 21 atom0658Coded := by decide +kernel
theorem atom0658Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34509342530304 : Int) atom0658Coded) := by
  have h := atom0658_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0658Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0659 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0659 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0659 = ((g 2) * (g 7) * (g 11)) := by
  norm_num [atom0659, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0659_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34217714824704 : Int) atom0659) := by
  rw [SparsePolynomial.eval_scale, eval_atom0659]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0659Coded : CoefficientMerge.Poly := [(nat_lit 1040, Int.ofNat (nat_lit 1))]
theorem atom0659Coded_decode : atom0659 = SparsePolynomial.decodeCubic 21 atom0659Coded := by decide +kernel
theorem atom0659Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34217714824704 : Int) atom0659Coded) := by
  have h := atom0659_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0659Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0660 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0660 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0660 = ((g 2) * (g 7) * (g 12)) := by
  norm_num [atom0660, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0660_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31960616904704 : Int) atom0660) := by
  rw [SparsePolynomial.eval_scale, eval_atom0660]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0660Coded : CoefficientMerge.Poly := [(nat_lit 1041, Int.ofNat (nat_lit 1))]
theorem atom0660Coded_decode : atom0660 = SparsePolynomial.decodeCubic 21 atom0660Coded := by decide +kernel
theorem atom0660Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31960616904704 : Int) atom0660Coded) := by
  have h := atom0660_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0660Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0661 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0661 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0661 = ((g 2) * (g 7) * (g 13)) := by
  norm_num [atom0661, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0661_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31446597832704 : Int) atom0661) := by
  rw [SparsePolynomial.eval_scale, eval_atom0661]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0661Coded : CoefficientMerge.Poly := [(nat_lit 1042, Int.ofNat (nat_lit 1))]
theorem atom0661Coded_decode : atom0661 = SparsePolynomial.decodeCubic 21 atom0661Coded := by decide +kernel
theorem atom0661Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31446597832704 : Int) atom0661Coded) := by
  have h := atom0661_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0661Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0662 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0662 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0662 = ((g 2) * (g 7) * (g 14)) := by
  norm_num [atom0662, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0662_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31809990703104 : Int) atom0662) := by
  rw [SparsePolynomial.eval_scale, eval_atom0662]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0662Coded : CoefficientMerge.Poly := [(nat_lit 1043, Int.ofNat (nat_lit 1))]
theorem atom0662Coded_decode : atom0662 = SparsePolynomial.decodeCubic 21 atom0662Coded := by decide +kernel
theorem atom0662Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31809990703104 : Int) atom0662Coded) := by
  have h := atom0662_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0662Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0663 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0663 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0663 = ((g 2) * (g 7) * (g 15)) := by
  norm_num [atom0663, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0663_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41404370635008 : Int) atom0663) := by
  rw [SparsePolynomial.eval_scale, eval_atom0663]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0663Coded : CoefficientMerge.Poly := [(nat_lit 1044, Int.ofNat (nat_lit 1))]
theorem atom0663Coded_decode : atom0663 = SparsePolynomial.decodeCubic 21 atom0663Coded := by decide +kernel
theorem atom0663Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41404370635008 : Int) atom0663Coded) := by
  have h := atom0663_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0663Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0664 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0664 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0664 = ((g 2) * (g 7) * (g 16)) := by
  norm_num [atom0664, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0664_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31000486141440 : Int) atom0664) := by
  rw [SparsePolynomial.eval_scale, eval_atom0664]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0664Coded : CoefficientMerge.Poly := [(nat_lit 1045, Int.ofNat (nat_lit 1))]
theorem atom0664Coded_decode : atom0664 = SparsePolynomial.decodeCubic 21 atom0664Coded := by decide +kernel
theorem atom0664Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31000486141440 : Int) atom0664Coded) := by
  have h := atom0664_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0664Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0665 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0665 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0665 = ((g 2) * (g 7) * (g 17)) := by
  norm_num [atom0665, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0665_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41272519396608 : Int) atom0665) := by
  rw [SparsePolynomial.eval_scale, eval_atom0665]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0665Coded : CoefficientMerge.Poly := [(nat_lit 1046, Int.ofNat (nat_lit 1))]
theorem atom0665Coded_decode : atom0665 = SparsePolynomial.decodeCubic 21 atom0665Coded := by decide +kernel
theorem atom0665Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41272519396608 : Int) atom0665Coded) := by
  have h := atom0665_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0665Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0666 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0666 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0666 = ((g 2) * (g 7) * (g 18)) := by
  norm_num [atom0666, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0666_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36889019085312 : Int) atom0666) := by
  rw [SparsePolynomial.eval_scale, eval_atom0666]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0666Coded : CoefficientMerge.Poly := [(nat_lit 1047, Int.ofNat (nat_lit 1))]
theorem atom0666Coded_decode : atom0666 = SparsePolynomial.decodeCubic 21 atom0666Coded := by decide +kernel
theorem atom0666Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36889019085312 : Int) atom0666Coded) := by
  have h := atom0666_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0666Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0667 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0667 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0667 = ((g 2) * (g 7) * (g 19)) := by
  norm_num [atom0667, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0667_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40093076482560 : Int) atom0667) := by
  rw [SparsePolynomial.eval_scale, eval_atom0667]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0667Coded : CoefficientMerge.Poly := [(nat_lit 1048, Int.ofNat (nat_lit 1))]
theorem atom0667Coded_decode : atom0667 = SparsePolynomial.decodeCubic 21 atom0667Coded := by decide +kernel
theorem atom0667Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40093076482560 : Int) atom0667Coded) := by
  have h := atom0667_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0667Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0668 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 7, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0668 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0668 = ((g 2) * (g 7) * (g 20)) := by
  norm_num [atom0668, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0668_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47967118852608 : Int) atom0668) := by
  rw [SparsePolynomial.eval_scale, eval_atom0668]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0668Coded : CoefficientMerge.Poly := [(nat_lit 1049, Int.ofNat (nat_lit 1))]
theorem atom0668Coded_decode : atom0668 = SparsePolynomial.decodeCubic 21 atom0668Coded := by decide +kernel
theorem atom0668Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47967118852608 : Int) atom0668Coded) := by
  have h := atom0668_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0668Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0669 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0669 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0669 = ((g 2) * (g 8) * (g 8)) := by
  norm_num [atom0669, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0669_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22303076342400 : Int) atom0669) := by
  rw [SparsePolynomial.eval_scale, eval_atom0669]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0669Coded : CoefficientMerge.Poly := [(nat_lit 1058, Int.ofNat (nat_lit 1))]
theorem atom0669Coded_decode : atom0669 = SparsePolynomial.decodeCubic 21 atom0669Coded := by decide +kernel
theorem atom0669Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22303076342400 : Int) atom0669Coded) := by
  have h := atom0669_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0669Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0670 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0670 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0670 = ((g 2) * (g 8) * (g 9)) := by
  norm_num [atom0670, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0670_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41607678268800 : Int) atom0670) := by
  rw [SparsePolynomial.eval_scale, eval_atom0670]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0670Coded : CoefficientMerge.Poly := [(nat_lit 1059, Int.ofNat (nat_lit 1))]
theorem atom0670Coded_decode : atom0670 = SparsePolynomial.decodeCubic 21 atom0670Coded := by decide +kernel
theorem atom0670Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41607678268800 : Int) atom0670Coded) := by
  have h := atom0670_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0670Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0671 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0671 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0671 = ((g 2) * (g 8) * (g 10)) := by
  norm_num [atom0671, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0671_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40696296681600 : Int) atom0671) := by
  rw [SparsePolynomial.eval_scale, eval_atom0671]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0671Coded : CoefficientMerge.Poly := [(nat_lit 1060, Int.ofNat (nat_lit 1))]
theorem atom0671Coded_decode : atom0671 = SparsePolynomial.decodeCubic 21 atom0671Coded := by decide +kernel
theorem atom0671Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40696296681600 : Int) atom0671Coded) := by
  have h := atom0671_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0671Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0672 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0672 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0672 = ((g 2) * (g 8) * (g 11)) := by
  norm_num [atom0672, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0672_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39732005577600 : Int) atom0672) := by
  rw [SparsePolynomial.eval_scale, eval_atom0672]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0672Coded : CoefficientMerge.Poly := [(nat_lit 1061, Int.ofNat (nat_lit 1))]
theorem atom0672Coded_decode : atom0672 = SparsePolynomial.decodeCubic 21 atom0672Coded := by decide +kernel
theorem atom0672Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39732005577600 : Int) atom0672Coded) := by
  have h := atom0672_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0672Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0673 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0673 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0673 = ((g 2) * (g 8) * (g 12)) := by
  norm_num [atom0673, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0673_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36634078409600 : Int) atom0673) := by
  rw [SparsePolynomial.eval_scale, eval_atom0673]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0673Coded : CoefficientMerge.Poly := [(nat_lit 1062, Int.ofNat (nat_lit 1))]
theorem atom0673Coded_decode : atom0673 = SparsePolynomial.decodeCubic 21 atom0673Coded := by decide +kernel
theorem atom0673Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36634078409600 : Int) atom0673Coded) := by
  have h := atom0673_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0673Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0674 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0674 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0674 = ((g 2) * (g 8) * (g 13)) := by
  norm_num [atom0674, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0674_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35706410006400 : Int) atom0674) := by
  rw [SparsePolynomial.eval_scale, eval_atom0674]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0674Coded : CoefficientMerge.Poly := [(nat_lit 1063, Int.ofNat (nat_lit 1))]
theorem atom0674Coded_decode : atom0674 = SparsePolynomial.decodeCubic 21 atom0674Coded := by decide +kernel
theorem atom0674Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35706410006400 : Int) atom0674Coded) := by
  have h := atom0674_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0674Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0675 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0675 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0675 = ((g 2) * (g 8) * (g 14)) := by
  norm_num [atom0675, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0675_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35656153545600 : Int) atom0675) := by
  rw [SparsePolynomial.eval_scale, eval_atom0675]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0675Coded : CoefficientMerge.Poly := [(nat_lit 1064, Int.ofNat (nat_lit 1))]
theorem atom0675Coded_decode : atom0675 = SparsePolynomial.decodeCubic 21 atom0675Coded := by decide +kernel
theorem atom0675Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35656153545600 : Int) atom0675Coded) := by
  have h := atom0675_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0675Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0676 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0676 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0676 = ((g 2) * (g 8) * (g 15)) := by
  norm_num [atom0676, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0676_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44345527833600 : Int) atom0676) := by
  rw [SparsePolynomial.eval_scale, eval_atom0676]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0676Coded : CoefficientMerge.Poly := [(nat_lit 1065, Int.ofNat (nat_lit 1))]
theorem atom0676Coded_decode : atom0676 = SparsePolynomial.decodeCubic 21 atom0676Coded := by decide +kernel
theorem atom0676Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44345527833600 : Int) atom0676Coded) := by
  have h := atom0676_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0676Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0677 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0677 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0677 = ((g 2) * (g 8) * (g 16)) := by
  norm_num [atom0677, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0677_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34468180210800 : Int) atom0677) := by
  rw [SparsePolynomial.eval_scale, eval_atom0677]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0677Coded : CoefficientMerge.Poly := [(nat_lit 1066, Int.ofNat (nat_lit 1))]
theorem atom0677Coded_decode : atom0677 = SparsePolynomial.decodeCubic 21 atom0677Coded := by decide +kernel
theorem atom0677Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34468180210800 : Int) atom0677Coded) := by
  have h := atom0677_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0677Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0678 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0678 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0678 = ((g 2) * (g 8) * (g 17)) := by
  norm_num [atom0678, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0678_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45222671692800 : Int) atom0678) := by
  rw [SparsePolynomial.eval_scale, eval_atom0678]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0678Coded : CoefficientMerge.Poly := [(nat_lit 1067, Int.ofNat (nat_lit 1))]
theorem atom0678Coded_decode : atom0678 = SparsePolynomial.decodeCubic 21 atom0678Coded := by decide +kernel
theorem atom0678Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (45222671692800 : Int) atom0678Coded) := by
  have h := atom0678_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0678Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0679 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0679 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0679 = ((g 2) * (g 8) * (g 18)) := by
  norm_num [atom0679, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0679_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40427074270800 : Int) atom0679) := by
  rw [SparsePolynomial.eval_scale, eval_atom0679]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0679Coded : CoefficientMerge.Poly := [(nat_lit 1068, Int.ofNat (nat_lit 1))]
theorem atom0679Coded_decode : atom0679 = SparsePolynomial.decodeCubic 21 atom0679Coded := by decide +kernel
theorem atom0679Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40427074270800 : Int) atom0679Coded) := by
  have h := atom0679_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0679Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0680 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0680 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0680 = ((g 2) * (g 8) * (g 19)) := by
  norm_num [atom0680, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0680_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43815922189200 : Int) atom0680) := by
  rw [SparsePolynomial.eval_scale, eval_atom0680]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0680Coded : CoefficientMerge.Poly := [(nat_lit 1069, Int.ofNat (nat_lit 1))]
theorem atom0680Coded_decode : atom0680 = SparsePolynomial.decodeCubic 21 atom0680Coded := by decide +kernel
theorem atom0680Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43815922189200 : Int) atom0680Coded) := by
  have h := atom0680_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0680Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0681 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0681 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0681 = ((g 2) * (g 8) * (g 20)) := by
  norm_num [atom0681, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0681_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51874755080400 : Int) atom0681) := by
  rw [SparsePolynomial.eval_scale, eval_atom0681]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0681Coded : CoefficientMerge.Poly := [(nat_lit 1070, Int.ofNat (nat_lit 1))]
theorem atom0681Coded_decode : atom0681 = SparsePolynomial.decodeCubic 21 atom0681Coded := by decide +kernel
theorem atom0681Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (51874755080400 : Int) atom0681Coded) := by
  have h := atom0681_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0681Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0682 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0682 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0682 = ((g 2) * (g 9) * (g 9)) := by
  norm_num [atom0682, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0682_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24598926777600 : Int) atom0682) := by
  rw [SparsePolynomial.eval_scale, eval_atom0682]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0682Coded : CoefficientMerge.Poly := [(nat_lit 1080, Int.ofNat (nat_lit 1))]
theorem atom0682Coded_decode : atom0682 = SparsePolynomial.decodeCubic 21 atom0682Coded := by decide +kernel
theorem atom0682Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24598926777600 : Int) atom0682Coded) := by
  have h := atom0682_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0682Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0683 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0683 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0683 = ((g 2) * (g 9) * (g 10)) := by
  norm_num [atom0683, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0683_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46170868262400 : Int) atom0683) := by
  rw [SparsePolynomial.eval_scale, eval_atom0683]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0683Coded : CoefficientMerge.Poly := [(nat_lit 1081, Int.ofNat (nat_lit 1))]
theorem atom0683Coded_decode : atom0683 = SparsePolynomial.decodeCubic 21 atom0683Coded := by decide +kernel
theorem atom0683Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46170868262400 : Int) atom0683Coded) := by
  have h := atom0683_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0683Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0684 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0684 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0684 = ((g 2) * (g 9) * (g 11)) := by
  norm_num [atom0684, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0684_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44365747910400 : Int) atom0684) := by
  rw [SparsePolynomial.eval_scale, eval_atom0684]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0684Coded : CoefficientMerge.Poly := [(nat_lit 1082, Int.ofNat (nat_lit 1))]
theorem atom0684Coded_decode : atom0684 = SparsePolynomial.decodeCubic 21 atom0684Coded := by decide +kernel
theorem atom0684Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44365747910400 : Int) atom0684Coded) := by
  have h := atom0684_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0684Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0685 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0685 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0685 = ((g 2) * (g 9) * (g 12)) := by
  norm_num [atom0685, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0685_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41113185478400 : Int) atom0685) := by
  rw [SparsePolynomial.eval_scale, eval_atom0685]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0685Coded : CoefficientMerge.Poly := [(nat_lit 1083, Int.ofNat (nat_lit 1))]
theorem atom0685Coded_decode : atom0685 = SparsePolynomial.decodeCubic 21 atom0685Coded := by decide +kernel
theorem atom0685Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41113185478400 : Int) atom0685Coded) := by
  have h := atom0685_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0685Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0686 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0686 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0686 = ((g 2) * (g 9) * (g 13)) := by
  norm_num [atom0686, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0686_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39603701894400 : Int) atom0686) := by
  rw [SparsePolynomial.eval_scale, eval_atom0686]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0686Coded : CoefficientMerge.Poly := [(nat_lit 1084, Int.ofNat (nat_lit 1))]
theorem atom0686Coded_decode : atom0686 = SparsePolynomial.decodeCubic 21 atom0686Coded := by decide +kernel
theorem atom0686Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39603701894400 : Int) atom0686Coded) := by
  have h := atom0686_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0686Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0687 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0687 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0687 = ((g 2) * (g 9) * (g 14)) := by
  norm_num [atom0687, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0687_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38971630252800 : Int) atom0687) := by
  rw [SparsePolynomial.eval_scale, eval_atom0687]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0687Coded : CoefficientMerge.Poly := [(nat_lit 1085, Int.ofNat (nat_lit 1))]
theorem atom0687Coded_decode : atom0687 = SparsePolynomial.decodeCubic 21 atom0687Coded := by decide +kernel
theorem atom0687Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38971630252800 : Int) atom0687Coded) := by
  have h := atom0687_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0687Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0688 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0688 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0688 = ((g 2) * (g 9) * (g 15)) := by
  norm_num [atom0688, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0688_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47136694348800 : Int) atom0688) := by
  rw [SparsePolynomial.eval_scale, eval_atom0688]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0688Coded : CoefficientMerge.Poly := [(nat_lit 1086, Int.ofNat (nat_lit 1))]
theorem atom0688Coded_decode : atom0688 = SparsePolynomial.decodeCubic 21 atom0688Coded := by decide +kernel
theorem atom0688Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47136694348800 : Int) atom0688Coded) := by
  have h := atom0688_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0688Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0689 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0689 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0689 = ((g 2) * (g 9) * (g 16)) := by
  norm_num [atom0689, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0689_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37088825104800 : Int) atom0689) := by
  rw [SparsePolynomial.eval_scale, eval_atom0689]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0689Coded : CoefficientMerge.Poly := [(nat_lit 1087, Int.ofNat (nat_lit 1))]
theorem atom0689Coded_decode : atom0689 = SparsePolynomial.decodeCubic 21 atom0689Coded := by decide +kernel
theorem atom0689Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37088825104800 : Int) atom0689Coded) := by
  have h := atom0689_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0689Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0690 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0690 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0690 = ((g 2) * (g 9) * (g 17)) := by
  norm_num [atom0690, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0690_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49022833305600 : Int) atom0690) := by
  rw [SparsePolynomial.eval_scale, eval_atom0690]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0690Coded : CoefficientMerge.Poly := [(nat_lit 1088, Int.ofNat (nat_lit 1))]
theorem atom0690Coded_decode : atom0690 = SparsePolynomial.decodeCubic 21 atom0690Coded := by decide +kernel
theorem atom0690Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49022833305600 : Int) atom0690Coded) := by
  have h := atom0690_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0690Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0691 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0691 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0691 = ((g 2) * (g 9) * (g 18)) := by
  norm_num [atom0691, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0691_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42821685900000 : Int) atom0691) := by
  rw [SparsePolynomial.eval_scale, eval_atom0691]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0691Coded : CoefficientMerge.Poly := [(nat_lit 1089, Int.ofNat (nat_lit 1))]
theorem atom0691Coded_decode : atom0691 = SparsePolynomial.decodeCubic 21 atom0691Coded := by decide +kernel
theorem atom0691Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42821685900000 : Int) atom0691Coded) := by
  have h := atom0691_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0691Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0692 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0692 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0692 = ((g 2) * (g 9) * (g 19)) := by
  norm_num [atom0692, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0692_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46253783368800 : Int) atom0692) := by
  rw [SparsePolynomial.eval_scale, eval_atom0692]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0692Coded : CoefficientMerge.Poly := [(nat_lit 1090, Int.ofNat (nat_lit 1))]
theorem atom0692Coded_decode : atom0692 = SparsePolynomial.decodeCubic 21 atom0692Coded := by decide +kernel
theorem atom0692Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46253783368800 : Int) atom0692Coded) := by
  have h := atom0692_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0692Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0693 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0693 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0693 = ((g 2) * (g 9) * (g 20)) := by
  norm_num [atom0693, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0693_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54355865810400 : Int) atom0693) := by
  rw [SparsePolynomial.eval_scale, eval_atom0693]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0693Coded : CoefficientMerge.Poly := [(nat_lit 1091, Int.ofNat (nat_lit 1))]
theorem atom0693Coded_decode : atom0693 = SparsePolynomial.decodeCubic 21 atom0693Coded := by decide +kernel
theorem atom0693Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (54355865810400 : Int) atom0693Coded) := by
  have h := atom0693_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0693Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0694 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0694 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0694 = ((g 2) * (g 10) * (g 10)) := by
  norm_num [atom0694, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0694_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26866266336000 : Int) atom0694) := by
  rw [SparsePolynomial.eval_scale, eval_atom0694]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0694Coded : CoefficientMerge.Poly := [(nat_lit 1102, Int.ofNat (nat_lit 1))]
theorem atom0694Coded_decode : atom0694 = SparsePolynomial.decodeCubic 21 atom0694Coded := by decide +kernel
theorem atom0694Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26866266336000 : Int) atom0694Coded) := by
  have h := atom0694_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0694Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0695 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0695 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0695 = ((g 2) * (g 10) * (g 11)) := by
  norm_num [atom0695, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0695_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50413919673600 : Int) atom0695) := by
  rw [SparsePolynomial.eval_scale, eval_atom0695]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0695Coded : CoefficientMerge.Poly := [(nat_lit 1103, Int.ofNat (nat_lit 1))]
theorem atom0695Coded_decode : atom0695 = SparsePolynomial.decodeCubic 21 atom0695Coded := by decide +kernel
theorem atom0695Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50413919673600 : Int) atom0695Coded) := by
  have h := atom0695_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0695Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0696 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0696 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0696 = ((g 2) * (g 10) * (g 12)) := by
  norm_num [atom0696, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0696_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45984196294400 : Int) atom0696) := by
  rw [SparsePolynomial.eval_scale, eval_atom0696]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0696Coded : CoefficientMerge.Poly := [(nat_lit 1104, Int.ofNat (nat_lit 1))]
theorem atom0696Coded_decode : atom0696 = SparsePolynomial.decodeCubic 21 atom0696Coded := by decide +kernel
theorem atom0696Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (45984196294400 : Int) atom0696Coded) := by
  have h := atom0696_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0696Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0697 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0697 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0697 = ((g 2) * (g 10) * (g 13)) := by
  norm_num [atom0697, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0697_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43724731680000 : Int) atom0697) := by
  rw [SparsePolynomial.eval_scale, eval_atom0697]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0697Coded : CoefficientMerge.Poly := [(nat_lit 1105, Int.ofNat (nat_lit 1))]
theorem atom0697Coded_decode : atom0697 = SparsePolynomial.decodeCubic 21 atom0697Coded := by decide +kernel
theorem atom0697Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43724731680000 : Int) atom0697Coded) := by
  have h := atom0697_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0697Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0698 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0698 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0698 = ((g 2) * (g 10) * (g 14)) := by
  norm_num [atom0698, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0698_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42342679008000 : Int) atom0698) := by
  rw [SparsePolynomial.eval_scale, eval_atom0698]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0698Coded : CoefficientMerge.Poly := [(nat_lit 1106, Int.ofNat (nat_lit 1))]
theorem atom0698Coded_decode : atom0698 = SparsePolynomial.decodeCubic 21 atom0698Coded := by decide +kernel
theorem atom0698Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42342679008000 : Int) atom0698Coded) := by
  have h := atom0698_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0698Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0699 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0699 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0699 = ((g 2) * (g 10) * (g 15)) := by
  norm_num [atom0699, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0699_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49927860864000 : Int) atom0699) := by
  rw [SparsePolynomial.eval_scale, eval_atom0699]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0699Coded : CoefficientMerge.Poly := [(nat_lit 1107, Int.ofNat (nat_lit 1))]
theorem atom0699Coded_decode : atom0699 = SparsePolynomial.decodeCubic 21 atom0699Coded := by decide +kernel
theorem atom0699Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49927860864000 : Int) atom0699Coded) := by
  have h := atom0699_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0699Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0700 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0700 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0700 = ((g 2) * (g 10) * (g 16)) := by
  norm_num [atom0700, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0700_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39228832188000 : Int) atom0700) := by
  rw [SparsePolynomial.eval_scale, eval_atom0700]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0700Coded : CoefficientMerge.Poly := [(nat_lit 1108, Int.ofNat (nat_lit 1))]
theorem atom0700Coded_decode : atom0700 = SparsePolynomial.decodeCubic 21 atom0700Coded := by decide +kernel
theorem atom0700Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39228832188000 : Int) atom0700Coded) := by
  have h := atom0700_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0700Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0701 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0701 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0701 = ((g 2) * (g 10) * (g 17)) := by
  norm_num [atom0701, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0701_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52822994918400 : Int) atom0701) := by
  rw [SparsePolynomial.eval_scale, eval_atom0701]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0701Coded : CoefficientMerge.Poly := [(nat_lit 1109, Int.ofNat (nat_lit 1))]
theorem atom0701Coded_decode : atom0701 = SparsePolynomial.decodeCubic 21 atom0701Coded := by decide +kernel
theorem atom0701Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52822994918400 : Int) atom0701Coded) := by
  have h := atom0701_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0701Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0702 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0702 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0702 = ((g 2) * (g 10) * (g 18)) := by
  norm_num [atom0702, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0702_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43999571700000 : Int) atom0702) := by
  rw [SparsePolynomial.eval_scale, eval_atom0702]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0702Coded : CoefficientMerge.Poly := [(nat_lit 1110, Int.ofNat (nat_lit 1))]
theorem atom0702Coded_decode : atom0702 = SparsePolynomial.decodeCubic 21 atom0702Coded := by decide +kernel
theorem atom0702Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43999571700000 : Int) atom0702Coded) := by
  have h := atom0702_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0702Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0703 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0703 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0703 = ((g 2) * (g 10) * (g 19)) := by
  norm_num [atom0703, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0703_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47040248656800 : Int) atom0703) := by
  rw [SparsePolynomial.eval_scale, eval_atom0703]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0703Coded : CoefficientMerge.Poly := [(nat_lit 1111, Int.ofNat (nat_lit 1))]
theorem atom0703Coded_decode : atom0703 = SparsePolynomial.decodeCubic 21 atom0703Coded := by decide +kernel
theorem atom0703Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47040248656800 : Int) atom0703Coded) := by
  have h := atom0703_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0703Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0704 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0704 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0704 = ((g 2) * (g 10) * (g 20)) := by
  norm_num [atom0704, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0704_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54750910586400 : Int) atom0704) := by
  rw [SparsePolynomial.eval_scale, eval_atom0704]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0704Coded : CoefficientMerge.Poly := [(nat_lit 1112, Int.ofNat (nat_lit 1))]
theorem atom0704Coded_decode : atom0704 = SparsePolynomial.decodeCubic 21 atom0704Coded := by decide +kernel
theorem atom0704Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (54750910586400 : Int) atom0704Coded) := by
  have h := atom0704_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0704Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0705 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0705 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0705 = ((g 2) * (g 11) * (g 11)) := by
  norm_num [atom0705, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0705_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28841978188800 : Int) atom0705) := by
  rw [SparsePolynomial.eval_scale, eval_atom0705]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0705Coded : CoefficientMerge.Poly := [(nat_lit 1124, Int.ofNat (nat_lit 1))]
theorem atom0705Coded_decode : atom0705 = SparsePolynomial.decodeCubic 21 atom0705Coded := by decide +kernel
theorem atom0705Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28841978188800 : Int) atom0705Coded) := by
  have h := atom0705_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0705Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0706 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0706 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0706 = ((g 2) * (g 11) * (g 12)) := by
  norm_num [atom0706, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0706_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50886380518400 : Int) atom0706) := by
  rw [SparsePolynomial.eval_scale, eval_atom0706]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0706Coded : CoefficientMerge.Poly := [(nat_lit 1125, Int.ofNat (nat_lit 1))]
theorem atom0706Coded_decode : atom0706 = SparsePolynomial.decodeCubic 21 atom0706Coded := by decide +kernel
theorem atom0706Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50886380518400 : Int) atom0706Coded) := by
  have h := atom0706_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0706Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0707 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0707 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0707 = ((g 2) * (g 11) * (g 13)) := by
  norm_num [atom0707, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0707_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47708769024000 : Int) atom0707) := by
  rw [SparsePolynomial.eval_scale, eval_atom0707]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0707Coded : CoefficientMerge.Poly := [(nat_lit 1126, Int.ofNat (nat_lit 1))]
theorem atom0707Coded_decode : atom0707 = SparsePolynomial.decodeCubic 21 atom0707Coded := by decide +kernel
theorem atom0707Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47708769024000 : Int) atom0707Coded) := by
  have h := atom0707_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0707Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0708 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0708 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0708 = ((g 2) * (g 11) * (g 14)) := by
  norm_num [atom0708, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0708_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45408569472000 : Int) atom0708) := by
  rw [SparsePolynomial.eval_scale, eval_atom0708]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0708Coded : CoefficientMerge.Poly := [(nat_lit 1127, Int.ofNat (nat_lit 1))]
theorem atom0708Coded_decode : atom0708 = SparsePolynomial.decodeCubic 21 atom0708Coded := by decide +kernel
theorem atom0708Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (45408569472000 : Int) atom0708Coded) := by
  have h := atom0708_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0708Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0709 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0709 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0709 = ((g 2) * (g 11) * (g 15)) := by
  norm_num [atom0709, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0709_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52095180211200 : Int) atom0709) := by
  rw [SparsePolynomial.eval_scale, eval_atom0709]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0709Coded : CoefficientMerge.Poly := [(nat_lit 1128, Int.ofNat (nat_lit 1))]
theorem atom0709Coded_decode : atom0709 = SparsePolynomial.decodeCubic 21 atom0709Coded := by decide +kernel
theorem atom0709Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52095180211200 : Int) atom0709Coded) := by
  have h := atom0709_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0709Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0710 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0710 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0710 = ((g 2) * (g 11) * (g 16)) := by
  norm_num [atom0710, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0710_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40662744998400 : Int) atom0710) := by
  rw [SparsePolynomial.eval_scale, eval_atom0710]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0710Coded : CoefficientMerge.Poly := [(nat_lit 1129, Int.ofNat (nat_lit 1))]
theorem atom0710Coded_decode : atom0710 = SparsePolynomial.decodeCubic 21 atom0710Coded := by decide +kernel
theorem atom0710Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40662744998400 : Int) atom0710Coded) := by
  have h := atom0710_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0710Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0711 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0711 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0711 = ((g 2) * (g 11) * (g 17)) := by
  norm_num [atom0711, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0711_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55999309363200 : Int) atom0711) := by
  rw [SparsePolynomial.eval_scale, eval_atom0711]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0711Coded : CoefficientMerge.Poly := [(nat_lit 1130, Int.ofNat (nat_lit 1))]
theorem atom0711Coded_decode : atom0711 = SparsePolynomial.decodeCubic 21 atom0711Coded := by decide +kernel
theorem atom0711Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55999309363200 : Int) atom0711Coded) := by
  have h := atom0711_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0711Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0712 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0712 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0712 = ((g 2) * (g 11) * (g 18)) := by
  norm_num [atom0712, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0712_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44005822963200 : Int) atom0712) := by
  rw [SparsePolynomial.eval_scale, eval_atom0712]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0712Coded : CoefficientMerge.Poly := [(nat_lit 1131, Int.ofNat (nat_lit 1))]
theorem atom0712Coded_decode : atom0712 = SparsePolynomial.decodeCubic 21 atom0712Coded := by decide +kernel
theorem atom0712Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44005822963200 : Int) atom0712Coded) := by
  have h := atom0712_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0712Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0713 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0713 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0713 = ((g 2) * (g 11) * (g 19)) := by
  norm_num [atom0713, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0713_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46400774515200 : Int) atom0713) := by
  rw [SparsePolynomial.eval_scale, eval_atom0713]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0713Coded : CoefficientMerge.Poly := [(nat_lit 1132, Int.ofNat (nat_lit 1))]
theorem atom0713Coded_decode : atom0713 = SparsePolynomial.decodeCubic 21 atom0713Coded := by decide +kernel
theorem atom0713Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46400774515200 : Int) atom0713Coded) := by
  have h := atom0713_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0713Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0714 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0714 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0714 = ((g 2) * (g 11) * (g 20)) := by
  norm_num [atom0714, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0714_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53465711040000 : Int) atom0714) := by
  rw [SparsePolynomial.eval_scale, eval_atom0714]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0714Coded : CoefficientMerge.Poly := [(nat_lit 1133, Int.ofNat (nat_lit 1))]
theorem atom0714Coded_decode : atom0714 = SparsePolynomial.decodeCubic 21 atom0714Coded := by decide +kernel
theorem atom0714Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53465711040000 : Int) atom0714Coded) := by
  have h := atom0714_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0714Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0715 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0715 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0715 = ((g 2) * (g 12) * (g 12)) := by
  norm_num [atom0715, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0715_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27765907097600 : Int) atom0715) := by
  rw [SparsePolynomial.eval_scale, eval_atom0715]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0715Coded : CoefficientMerge.Poly := [(nat_lit 1146, Int.ofNat (nat_lit 1))]
theorem atom0715Coded_decode : atom0715 = SparsePolynomial.decodeCubic 21 atom0715Coded := by decide +kernel
theorem atom0715Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27765907097600 : Int) atom0715Coded) := by
  have h := atom0715_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0715Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0716 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0716 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0716 = ((g 2) * (g 12) * (g 13)) := by
  norm_num [atom0716, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0716_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50840710054400 : Int) atom0716) := by
  rw [SparsePolynomial.eval_scale, eval_atom0716]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0716Coded : CoefficientMerge.Poly := [(nat_lit 1147, Int.ofNat (nat_lit 1))]
theorem atom0716Coded_decode : atom0716 = SparsePolynomial.decodeCubic 21 atom0716Coded := by decide +kernel
theorem atom0716Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50840710054400 : Int) atom0716Coded) := by
  have h := atom0716_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0716Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0717 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0717 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0717 = ((g 2) * (g 12) * (g 14)) := by
  norm_num [atom0717, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0717_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47454197772800 : Int) atom0717) := by
  rw [SparsePolynomial.eval_scale, eval_atom0717]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0717Coded : CoefficientMerge.Poly := [(nat_lit 1148, Int.ofNat (nat_lit 1))]
theorem atom0717Coded_decode : atom0717 = SparsePolynomial.decodeCubic 21 atom0717Coded := by decide +kernel
theorem atom0717Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47454197772800 : Int) atom0717Coded) := by
  have h := atom0717_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0717Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0718 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0718 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0718 = ((g 2) * (g 12) * (g 15)) := by
  norm_num [atom0718, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0718_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50163393280000 : Int) atom0718) := by
  rw [SparsePolynomial.eval_scale, eval_atom0718]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0718Coded : CoefficientMerge.Poly := [(nat_lit 1149, Int.ofNat (nat_lit 1))]
theorem atom0718Coded_decode : atom0718 = SparsePolynomial.decodeCubic 21 atom0718Coded := by decide +kernel
theorem atom0718Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50163393280000 : Int) atom0718Coded) := by
  have h := atom0718_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0718Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0719 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0719 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0719 = ((g 2) * (g 12) * (g 16)) := by
  norm_num [atom0719, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0719_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40943623616000 : Int) atom0719) := by
  rw [SparsePolynomial.eval_scale, eval_atom0719]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0719Coded : CoefficientMerge.Poly := [(nat_lit 1150, Int.ofNat (nat_lit 1))]
theorem atom0719Coded_decode : atom0719 = SparsePolynomial.decodeCubic 21 atom0719Coded := by decide +kernel
theorem atom0719Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40943623616000 : Int) atom0719Coded) := by
  have h := atom0719_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0719Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0720 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0720 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0720 = ((g 2) * (g 12) * (g 17)) := by
  norm_num [atom0720, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0720_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55076517529600 : Int) atom0720) := by
  rw [SparsePolynomial.eval_scale, eval_atom0720]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0720Coded : CoefficientMerge.Poly := [(nat_lit 1151, Int.ofNat (nat_lit 1))]
theorem atom0720Coded_decode : atom0720 = SparsePolynomial.decodeCubic 21 atom0720Coded := by decide +kernel
theorem atom0720Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55076517529600 : Int) atom0720Coded) := by
  have h := atom0720_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0720Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0721 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0721 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0721 = ((g 2) * (g 12) * (g 18)) := by
  norm_num [atom0721, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0721_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43587528678400 : Int) atom0721) := by
  rw [SparsePolynomial.eval_scale, eval_atom0721]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0721Coded : CoefficientMerge.Poly := [(nat_lit 1152, Int.ofNat (nat_lit 1))]
theorem atom0721Coded_decode : atom0721 = SparsePolynomial.decodeCubic 21 atom0721Coded := by decide +kernel
theorem atom0721Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43587528678400 : Int) atom0721Coded) := by
  have h := atom0721_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0721Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0722 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0722 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0722 = ((g 2) * (g 12) * (g 19)) := by
  norm_num [atom0722, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0722_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44782300864000 : Int) atom0722) := by
  rw [SparsePolynomial.eval_scale, eval_atom0722]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0722Coded : CoefficientMerge.Poly := [(nat_lit 1153, Int.ofNat (nat_lit 1))]
theorem atom0722Coded_decode : atom0722 = SparsePolynomial.decodeCubic 21 atom0722Coded := by decide +kernel
theorem atom0722Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44782300864000 : Int) atom0722Coded) := by
  have h := atom0722_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0722Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0723 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0723 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0723 = ((g 2) * (g 12) * (g 20)) := by
  norm_num [atom0723, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0723_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51304759027200 : Int) atom0723) := by
  rw [SparsePolynomial.eval_scale, eval_atom0723]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0723Coded : CoefficientMerge.Poly := [(nat_lit 1154, Int.ofNat (nat_lit 1))]
theorem atom0723Coded_decode : atom0723 = SparsePolynomial.decodeCubic 21 atom0723Coded := by decide +kernel
theorem atom0723Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (51304759027200 : Int) atom0723Coded) := by
  have h := atom0723_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0723Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0724 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0724 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0724 = ((g 2) * (g 13) * (g 13)) := by
  norm_num [atom0724, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0724_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28504801843200 : Int) atom0724) := by
  rw [SparsePolynomial.eval_scale, eval_atom0724]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0724Coded : CoefficientMerge.Poly := [(nat_lit 1168, Int.ofNat (nat_lit 1))]
theorem atom0724Coded_decode : atom0724 = SparsePolynomial.decodeCubic 21 atom0724Coded := by decide +kernel
theorem atom0724Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28504801843200 : Int) atom0724Coded) := by
  have h := atom0724_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0724Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0725 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0725 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0725 = ((g 2) * (g 13) * (g 14)) := by
  norm_num [atom0725, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0725_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51198079104000 : Int) atom0725) := by
  rw [SparsePolynomial.eval_scale, eval_atom0725]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0725Coded : CoefficientMerge.Poly := [(nat_lit 1169, Int.ofNat (nat_lit 1))]
theorem atom0725Coded_decode : atom0725 = SparsePolynomial.decodeCubic 21 atom0725Coded := by decide +kernel
theorem atom0725Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (51198079104000 : Int) atom0725Coded) := by
  have h := atom0725_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0725Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0726 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0726 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0726 = ((g 2) * (g 13) * (g 15)) := by
  norm_num [atom0726, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0726_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52516793448000 : Int) atom0726) := by
  rw [SparsePolynomial.eval_scale, eval_atom0726]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0726Coded : CoefficientMerge.Poly := [(nat_lit 1170, Int.ofNat (nat_lit 1))]
theorem atom0726Coded_decode : atom0726 = SparsePolynomial.decodeCubic 21 atom0726Coded := by decide +kernel
theorem atom0726Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52516793448000 : Int) atom0726Coded) := by
  have h := atom0726_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0726Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0727 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0727 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0727 = ((g 2) * (g 13) * (g 16)) := by
  norm_num [atom0727, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0727_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41770540036800 : Int) atom0727) := by
  rw [SparsePolynomial.eval_scale, eval_atom0727]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0727Coded : CoefficientMerge.Poly := [(nat_lit 1171, Int.ofNat (nat_lit 1))]
theorem atom0727Coded_decode : atom0727 = SparsePolynomial.decodeCubic 21 atom0727Coded := by decide +kernel
theorem atom0727Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41770540036800 : Int) atom0727Coded) := by
  have h := atom0727_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0727Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0728 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0728 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0728 = ((g 2) * (g 13) * (g 17)) := by
  norm_num [atom0728, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0728_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57639883392000 : Int) atom0728) := by
  rw [SparsePolynomial.eval_scale, eval_atom0728]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0728Coded : CoefficientMerge.Poly := [(nat_lit 1172, Int.ofNat (nat_lit 1))]
theorem atom0728Coded_decode : atom0728 = SparsePolynomial.decodeCubic 21 atom0728Coded := by decide +kernel
theorem atom0728Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (57639883392000 : Int) atom0728Coded) := by
  have h := atom0728_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0728Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0729 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0729 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0729 = ((g 2) * (g 13) * (g 18)) := by
  norm_num [atom0729, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0729_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46655392089600 : Int) atom0729) := by
  rw [SparsePolynomial.eval_scale, eval_atom0729]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0729Coded : CoefficientMerge.Poly := [(nat_lit 1173, Int.ofNat (nat_lit 1))]
theorem atom0729Coded_decode : atom0729 = SparsePolynomial.decodeCubic 21 atom0729Coded := by decide +kernel
theorem atom0729Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46655392089600 : Int) atom0729Coded) := by
  have h := atom0729_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0729Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0730 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0730 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0730 = ((g 2) * (g 13) * (g 19)) := by
  norm_num [atom0730, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0730_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40485755707200 : Int) atom0730) := by
  rw [SparsePolynomial.eval_scale, eval_atom0730]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0730Coded : CoefficientMerge.Poly := [(nat_lit 1174, Int.ofNat (nat_lit 1))]
theorem atom0730Coded_decode : atom0730 = SparsePolynomial.decodeCubic 21 atom0730Coded := by decide +kernel
theorem atom0730Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40485755707200 : Int) atom0730Coded) := by
  have h := atom0730_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0730Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0731 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0731 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0731 = ((g 2) * (g 13) * (g 20)) := by
  norm_num [atom0731, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0731_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52168139251200 : Int) atom0731) := by
  rw [SparsePolynomial.eval_scale, eval_atom0731]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0731Coded : CoefficientMerge.Poly := [(nat_lit 1175, Int.ofNat (nat_lit 1))]
theorem atom0731Coded_decode : atom0731 = SparsePolynomial.decodeCubic 21 atom0731Coded := by decide +kernel
theorem atom0731Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52168139251200 : Int) atom0731Coded) := by
  have h := atom0731_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0731Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0732 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0732 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0732 = ((g 2) * (g 14) * (g 14)) := by
  norm_num [atom0732, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0732_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30391628198400 : Int) atom0732) := by
  rw [SparsePolynomial.eval_scale, eval_atom0732]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0732Coded : CoefficientMerge.Poly := [(nat_lit 1190, Int.ofNat (nat_lit 1))]
theorem atom0732Coded_decode : atom0732 = SparsePolynomial.decodeCubic 21 atom0732Coded := by decide +kernel
theorem atom0732Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30391628198400 : Int) atom0732Coded) := by
  have h := atom0732_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0732Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0733 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0733 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0733 = ((g 2) * (g 14) * (g 15)) := by
  norm_num [atom0733, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0733_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55197057484800 : Int) atom0733) := by
  rw [SparsePolynomial.eval_scale, eval_atom0733]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0733Coded : CoefficientMerge.Poly := [(nat_lit 1191, Int.ofNat (nat_lit 1))]
theorem atom0733Coded_decode : atom0733 = SparsePolynomial.decodeCubic 21 atom0733Coded := by decide +kernel
theorem atom0733Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55197057484800 : Int) atom0733Coded) := by
  have h := atom0733_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0733Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0734 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0734 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0734 = ((g 2) * (g 14) * (g 16)) := by
  norm_num [atom0734, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0734_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42478307020800 : Int) atom0734) := by
  rw [SparsePolynomial.eval_scale, eval_atom0734]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0734Coded : CoefficientMerge.Poly := [(nat_lit 1192, Int.ofNat (nat_lit 1))]
theorem atom0734Coded_decode : atom0734 = SparsePolynomial.decodeCubic 21 atom0734Coded := by decide +kernel
theorem atom0734Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42478307020800 : Int) atom0734Coded) := by
  have h := atom0734_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0734Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0735 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0735 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0735 = ((g 2) * (g 14) * (g 17)) := by
  norm_num [atom0735, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0735_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61958073139200 : Int) atom0735) := by
  rw [SparsePolynomial.eval_scale, eval_atom0735]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0735Coded : CoefficientMerge.Poly := [(nat_lit 1193, Int.ofNat (nat_lit 1))]
theorem atom0735Coded_decode : atom0735 = SparsePolynomial.decodeCubic 21 atom0735Coded := by decide +kernel
theorem atom0735Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (61958073139200 : Int) atom0735Coded) := by
  have h := atom0735_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0735Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block010 : CoefficientMerge.Poly := [(nat_lit 1037, Int.ofNat (nat_lit 37423734021504)), (nat_lit 1038, Int.ofNat (nat_lit 34748060719104)), (nat_lit 1039, Int.ofNat (nat_lit 34509342530304)), (nat_lit 1040, Int.ofNat (nat_lit 34217714824704)), (nat_lit 1041, Int.ofNat (nat_lit 31960616904704)), (nat_lit 1042, Int.ofNat (nat_lit 31446597832704)), (nat_lit 1043, Int.ofNat (nat_lit 31809990703104)), (nat_lit 1044, Int.ofNat (nat_lit 41404370635008)), (nat_lit 1045, Int.ofNat (nat_lit 31000486141440)), (nat_lit 1046, Int.ofNat (nat_lit 41272519396608)), (nat_lit 1047, Int.ofNat (nat_lit 36889019085312)), (nat_lit 1048, Int.ofNat (nat_lit 40093076482560)), (nat_lit 1049, Int.ofNat (nat_lit 47967118852608)), (nat_lit 1058, Int.ofNat (nat_lit 22303076342400)), (nat_lit 1059, Int.ofNat (nat_lit 41607678268800)), (nat_lit 1060, Int.ofNat (nat_lit 40696296681600)), (nat_lit 1061, Int.ofNat (nat_lit 39732005577600)), (nat_lit 1062, Int.ofNat (nat_lit 36634078409600)), (nat_lit 1063, Int.ofNat (nat_lit 35706410006400)), (nat_lit 1064, Int.ofNat (nat_lit 35656153545600)), (nat_lit 1065, Int.ofNat (nat_lit 44345527833600)), (nat_lit 1066, Int.ofNat (nat_lit 34468180210800)), (nat_lit 1067, Int.ofNat (nat_lit 45222671692800)), (nat_lit 1068, Int.ofNat (nat_lit 40427074270800)), (nat_lit 1069, Int.ofNat (nat_lit 43815922189200)), (nat_lit 1070, Int.ofNat (nat_lit 51874755080400)), (nat_lit 1080, Int.ofNat (nat_lit 24598926777600)), (nat_lit 1081, Int.ofNat (nat_lit 46170868262400)), (nat_lit 1082, Int.ofNat (nat_lit 44365747910400)), (nat_lit 1083, Int.ofNat (nat_lit 41113185478400)), (nat_lit 1084, Int.ofNat (nat_lit 39603701894400)), (nat_lit 1085, Int.ofNat (nat_lit 38971630252800)), (nat_lit 1086, Int.ofNat (nat_lit 47136694348800)), (nat_lit 1087, Int.ofNat (nat_lit 37088825104800)), (nat_lit 1088, Int.ofNat (nat_lit 49022833305600)), (nat_lit 1089, Int.ofNat (nat_lit 42821685900000)), (nat_lit 1090, Int.ofNat (nat_lit 46253783368800)), (nat_lit 1091, Int.ofNat (nat_lit 54355865810400)), (nat_lit 1102, Int.ofNat (nat_lit 26866266336000)), (nat_lit 1103, Int.ofNat (nat_lit 50413919673600)), (nat_lit 1104, Int.ofNat (nat_lit 45984196294400)), (nat_lit 1105, Int.ofNat (nat_lit 43724731680000)), (nat_lit 1106, Int.ofNat (nat_lit 42342679008000)), (nat_lit 1107, Int.ofNat (nat_lit 49927860864000)), (nat_lit 1108, Int.ofNat (nat_lit 39228832188000)), (nat_lit 1109, Int.ofNat (nat_lit 52822994918400)), (nat_lit 1110, Int.ofNat (nat_lit 43999571700000)), (nat_lit 1111, Int.ofNat (nat_lit 47040248656800)), (nat_lit 1112, Int.ofNat (nat_lit 54750910586400)), (nat_lit 1124, Int.ofNat (nat_lit 28841978188800)), (nat_lit 1125, Int.ofNat (nat_lit 50886380518400)), (nat_lit 1126, Int.ofNat (nat_lit 47708769024000)), (nat_lit 1127, Int.ofNat (nat_lit 45408569472000)), (nat_lit 1128, Int.ofNat (nat_lit 52095180211200)), (nat_lit 1129, Int.ofNat (nat_lit 40662744998400)), (nat_lit 1130, Int.ofNat (nat_lit 55999309363200)), (nat_lit 1131, Int.ofNat (nat_lit 44005822963200)), (nat_lit 1132, Int.ofNat (nat_lit 46400774515200)), (nat_lit 1133, Int.ofNat (nat_lit 53465711040000)), (nat_lit 1146, Int.ofNat (nat_lit 27765907097600)), (nat_lit 1147, Int.ofNat (nat_lit 50840710054400)), (nat_lit 1148, Int.ofNat (nat_lit 47454197772800)), (nat_lit 1149, Int.ofNat (nat_lit 50163393280000)), (nat_lit 1150, Int.ofNat (nat_lit 40943623616000)), (nat_lit 1151, Int.ofNat (nat_lit 55076517529600)), (nat_lit 1152, Int.ofNat (nat_lit 43587528678400)), (nat_lit 1153, Int.ofNat (nat_lit 44782300864000)), (nat_lit 1154, Int.ofNat (nat_lit 51304759027200)), (nat_lit 1168, Int.ofNat (nat_lit 28504801843200)), (nat_lit 1169, Int.ofNat (nat_lit 51198079104000)), (nat_lit 1170, Int.ofNat (nat_lit 52516793448000)), (nat_lit 1171, Int.ofNat (nat_lit 41770540036800)), (nat_lit 1172, Int.ofNat (nat_lit 57639883392000)), (nat_lit 1173, Int.ofNat (nat_lit 46655392089600)), (nat_lit 1174, Int.ofNat (nat_lit 40485755707200)), (nat_lit 1175, Int.ofNat (nat_lit 52168139251200)), (nat_lit 1190, Int.ofNat (nat_lit 30391628198400)), (nat_lit 1191, Int.ofNat (nat_lit 55197057484800)), (nat_lit 1192, Int.ofNat (nat_lit 42478307020800)), (nat_lit 1193, Int.ofNat (nat_lit 61958073139200))]
def block010_data_flat000 : CoefficientMerge.Poly := [(nat_lit 1037, Int.ofNat (nat_lit 37423734021504))]
theorem block010_data_flat000_step : block010_data_flat000 = (CoefficientMerge.scale (37423734021504 : Int) atom0656Coded) := by decide +kernel
theorem block010_data_flat000_original : block010_data_flat000 = (CoefficientMerge.scale (37423734021504 : Int) atom0656Coded) := by
  rw [block010_data_flat000_step]
def block010_data_flat001 : CoefficientMerge.Poly := [(nat_lit 1038, Int.ofNat (nat_lit 34748060719104))]
theorem block010_data_flat001_step : block010_data_flat001 = (CoefficientMerge.scale (34748060719104 : Int) atom0657Coded) := by decide +kernel
theorem block010_data_flat001_original : block010_data_flat001 = (CoefficientMerge.scale (34748060719104 : Int) atom0657Coded) := by
  rw [block010_data_flat001_step]
def block010_data_flat002 : CoefficientMerge.Poly := [(nat_lit 1037, Int.ofNat (nat_lit 37423734021504)), (nat_lit 1038, Int.ofNat (nat_lit 34748060719104))]
theorem block010_data_flat002_step : block010_data_flat002 = (CoefficientMerge.fastMerge block010_data_flat000 block010_data_flat001) := by decide +kernel
theorem block010_data_flat002_original : block010_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (37423734021504 : Int) atom0656Coded) (CoefficientMerge.scale (34748060719104 : Int) atom0657Coded)) := by
  rw [block010_data_flat002_step, block010_data_flat000_original, block010_data_flat001_original]
def block010_data_flat003 : CoefficientMerge.Poly := [(nat_lit 1039, Int.ofNat (nat_lit 34509342530304))]
theorem block010_data_flat003_step : block010_data_flat003 = (CoefficientMerge.scale (34509342530304 : Int) atom0658Coded) := by decide +kernel
theorem block010_data_flat003_original : block010_data_flat003 = (CoefficientMerge.scale (34509342530304 : Int) atom0658Coded) := by
  rw [block010_data_flat003_step]
def block010_data_flat004 : CoefficientMerge.Poly := [(nat_lit 1040, Int.ofNat (nat_lit 34217714824704))]
theorem block010_data_flat004_step : block010_data_flat004 = (CoefficientMerge.scale (34217714824704 : Int) atom0659Coded) := by decide +kernel
theorem block010_data_flat004_original : block010_data_flat004 = (CoefficientMerge.scale (34217714824704 : Int) atom0659Coded) := by
  rw [block010_data_flat004_step]
def block010_data_flat005 : CoefficientMerge.Poly := [(nat_lit 1041, Int.ofNat (nat_lit 31960616904704))]
theorem block010_data_flat005_step : block010_data_flat005 = (CoefficientMerge.scale (31960616904704 : Int) atom0660Coded) := by decide +kernel
theorem block010_data_flat005_original : block010_data_flat005 = (CoefficientMerge.scale (31960616904704 : Int) atom0660Coded) := by
  rw [block010_data_flat005_step]
def block010_data_flat006 : CoefficientMerge.Poly := [(nat_lit 1040, Int.ofNat (nat_lit 34217714824704)), (nat_lit 1041, Int.ofNat (nat_lit 31960616904704))]
theorem block010_data_flat006_step : block010_data_flat006 = (CoefficientMerge.fastMerge block010_data_flat004 block010_data_flat005) := by decide +kernel
theorem block010_data_flat006_original : block010_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34217714824704 : Int) atom0659Coded) (CoefficientMerge.scale (31960616904704 : Int) atom0660Coded)) := by
  rw [block010_data_flat006_step, block010_data_flat004_original, block010_data_flat005_original]
def block010_data_flat007 : CoefficientMerge.Poly := [(nat_lit 1039, Int.ofNat (nat_lit 34509342530304)), (nat_lit 1040, Int.ofNat (nat_lit 34217714824704)), (nat_lit 1041, Int.ofNat (nat_lit 31960616904704))]
theorem block010_data_flat007_step : block010_data_flat007 = (CoefficientMerge.fastMerge block010_data_flat003 block010_data_flat006) := by decide +kernel
theorem block010_data_flat007_original : block010_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34509342530304 : Int) atom0658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34217714824704 : Int) atom0659Coded) (CoefficientMerge.scale (31960616904704 : Int) atom0660Coded))) := by
  rw [block010_data_flat007_step, block010_data_flat003_original, block010_data_flat006_original]
def block010_data_flat008 : CoefficientMerge.Poly := [(nat_lit 1037, Int.ofNat (nat_lit 37423734021504)), (nat_lit 1038, Int.ofNat (nat_lit 34748060719104)), (nat_lit 1039, Int.ofNat (nat_lit 34509342530304)), (nat_lit 1040, Int.ofNat (nat_lit 34217714824704)), (nat_lit 1041, Int.ofNat (nat_lit 31960616904704))]
theorem block010_data_flat008_step : block010_data_flat008 = (CoefficientMerge.fastMerge block010_data_flat002 block010_data_flat007) := by decide +kernel
theorem block010_data_flat008_original : block010_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37423734021504 : Int) atom0656Coded) (CoefficientMerge.scale (34748060719104 : Int) atom0657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34509342530304 : Int) atom0658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34217714824704 : Int) atom0659Coded) (CoefficientMerge.scale (31960616904704 : Int) atom0660Coded)))) := by
  rw [block010_data_flat008_step, block010_data_flat002_original, block010_data_flat007_original]
def block010_data_flat009 : CoefficientMerge.Poly := [(nat_lit 1042, Int.ofNat (nat_lit 31446597832704))]
theorem block010_data_flat009_step : block010_data_flat009 = (CoefficientMerge.scale (31446597832704 : Int) atom0661Coded) := by decide +kernel
theorem block010_data_flat009_original : block010_data_flat009 = (CoefficientMerge.scale (31446597832704 : Int) atom0661Coded) := by
  rw [block010_data_flat009_step]
def block010_data_flat010 : CoefficientMerge.Poly := [(nat_lit 1043, Int.ofNat (nat_lit 31809990703104))]
theorem block010_data_flat010_step : block010_data_flat010 = (CoefficientMerge.scale (31809990703104 : Int) atom0662Coded) := by decide +kernel
theorem block010_data_flat010_original : block010_data_flat010 = (CoefficientMerge.scale (31809990703104 : Int) atom0662Coded) := by
  rw [block010_data_flat010_step]
def block010_data_flat011 : CoefficientMerge.Poly := [(nat_lit 1042, Int.ofNat (nat_lit 31446597832704)), (nat_lit 1043, Int.ofNat (nat_lit 31809990703104))]
theorem block010_data_flat011_step : block010_data_flat011 = (CoefficientMerge.fastMerge block010_data_flat009 block010_data_flat010) := by decide +kernel
theorem block010_data_flat011_original : block010_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31446597832704 : Int) atom0661Coded) (CoefficientMerge.scale (31809990703104 : Int) atom0662Coded)) := by
  rw [block010_data_flat011_step, block010_data_flat009_original, block010_data_flat010_original]
def block010_data_flat012 : CoefficientMerge.Poly := [(nat_lit 1044, Int.ofNat (nat_lit 41404370635008))]
theorem block010_data_flat012_step : block010_data_flat012 = (CoefficientMerge.scale (41404370635008 : Int) atom0663Coded) := by decide +kernel
theorem block010_data_flat012_original : block010_data_flat012 = (CoefficientMerge.scale (41404370635008 : Int) atom0663Coded) := by
  rw [block010_data_flat012_step]
def block010_data_flat013 : CoefficientMerge.Poly := [(nat_lit 1045, Int.ofNat (nat_lit 31000486141440))]
theorem block010_data_flat013_step : block010_data_flat013 = (CoefficientMerge.scale (31000486141440 : Int) atom0664Coded) := by decide +kernel
theorem block010_data_flat013_original : block010_data_flat013 = (CoefficientMerge.scale (31000486141440 : Int) atom0664Coded) := by
  rw [block010_data_flat013_step]
def block010_data_flat014 : CoefficientMerge.Poly := [(nat_lit 1046, Int.ofNat (nat_lit 41272519396608))]
theorem block010_data_flat014_step : block010_data_flat014 = (CoefficientMerge.scale (41272519396608 : Int) atom0665Coded) := by decide +kernel
theorem block010_data_flat014_original : block010_data_flat014 = (CoefficientMerge.scale (41272519396608 : Int) atom0665Coded) := by
  rw [block010_data_flat014_step]
def block010_data_flat015 : CoefficientMerge.Poly := [(nat_lit 1045, Int.ofNat (nat_lit 31000486141440)), (nat_lit 1046, Int.ofNat (nat_lit 41272519396608))]
theorem block010_data_flat015_step : block010_data_flat015 = (CoefficientMerge.fastMerge block010_data_flat013 block010_data_flat014) := by decide +kernel
theorem block010_data_flat015_original : block010_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31000486141440 : Int) atom0664Coded) (CoefficientMerge.scale (41272519396608 : Int) atom0665Coded)) := by
  rw [block010_data_flat015_step, block010_data_flat013_original, block010_data_flat014_original]
def block010_data_flat016 : CoefficientMerge.Poly := [(nat_lit 1044, Int.ofNat (nat_lit 41404370635008)), (nat_lit 1045, Int.ofNat (nat_lit 31000486141440)), (nat_lit 1046, Int.ofNat (nat_lit 41272519396608))]
theorem block010_data_flat016_step : block010_data_flat016 = (CoefficientMerge.fastMerge block010_data_flat012 block010_data_flat015) := by decide +kernel
theorem block010_data_flat016_original : block010_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (41404370635008 : Int) atom0663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31000486141440 : Int) atom0664Coded) (CoefficientMerge.scale (41272519396608 : Int) atom0665Coded))) := by
  rw [block010_data_flat016_step, block010_data_flat012_original, block010_data_flat015_original]
def block010_data_flat017 : CoefficientMerge.Poly := [(nat_lit 1042, Int.ofNat (nat_lit 31446597832704)), (nat_lit 1043, Int.ofNat (nat_lit 31809990703104)), (nat_lit 1044, Int.ofNat (nat_lit 41404370635008)), (nat_lit 1045, Int.ofNat (nat_lit 31000486141440)), (nat_lit 1046, Int.ofNat (nat_lit 41272519396608))]
theorem block010_data_flat017_step : block010_data_flat017 = (CoefficientMerge.fastMerge block010_data_flat011 block010_data_flat016) := by decide +kernel
theorem block010_data_flat017_original : block010_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31446597832704 : Int) atom0661Coded) (CoefficientMerge.scale (31809990703104 : Int) atom0662Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41404370635008 : Int) atom0663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31000486141440 : Int) atom0664Coded) (CoefficientMerge.scale (41272519396608 : Int) atom0665Coded)))) := by
  rw [block010_data_flat017_step, block010_data_flat011_original, block010_data_flat016_original]
def block010_data_flat018 : CoefficientMerge.Poly := [(nat_lit 1037, Int.ofNat (nat_lit 37423734021504)), (nat_lit 1038, Int.ofNat (nat_lit 34748060719104)), (nat_lit 1039, Int.ofNat (nat_lit 34509342530304)), (nat_lit 1040, Int.ofNat (nat_lit 34217714824704)), (nat_lit 1041, Int.ofNat (nat_lit 31960616904704)), (nat_lit 1042, Int.ofNat (nat_lit 31446597832704)), (nat_lit 1043, Int.ofNat (nat_lit 31809990703104)), (nat_lit 1044, Int.ofNat (nat_lit 41404370635008)), (nat_lit 1045, Int.ofNat (nat_lit 31000486141440)), (nat_lit 1046, Int.ofNat (nat_lit 41272519396608))]
theorem block010_data_flat018_step : block010_data_flat018 = (CoefficientMerge.fastMerge block010_data_flat008 block010_data_flat017) := by decide +kernel
theorem block010_data_flat018_original : block010_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37423734021504 : Int) atom0656Coded) (CoefficientMerge.scale (34748060719104 : Int) atom0657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34509342530304 : Int) atom0658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34217714824704 : Int) atom0659Coded) (CoefficientMerge.scale (31960616904704 : Int) atom0660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31446597832704 : Int) atom0661Coded) (CoefficientMerge.scale (31809990703104 : Int) atom0662Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41404370635008 : Int) atom0663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31000486141440 : Int) atom0664Coded) (CoefficientMerge.scale (41272519396608 : Int) atom0665Coded))))) := by
  rw [block010_data_flat018_step, block010_data_flat008_original, block010_data_flat017_original]
def block010_data_flat019 : CoefficientMerge.Poly := [(nat_lit 1047, Int.ofNat (nat_lit 36889019085312))]
theorem block010_data_flat019_step : block010_data_flat019 = (CoefficientMerge.scale (36889019085312 : Int) atom0666Coded) := by decide +kernel
theorem block010_data_flat019_original : block010_data_flat019 = (CoefficientMerge.scale (36889019085312 : Int) atom0666Coded) := by
  rw [block010_data_flat019_step]
def block010_data_flat020 : CoefficientMerge.Poly := [(nat_lit 1048, Int.ofNat (nat_lit 40093076482560))]
theorem block010_data_flat020_step : block010_data_flat020 = (CoefficientMerge.scale (40093076482560 : Int) atom0667Coded) := by decide +kernel
theorem block010_data_flat020_original : block010_data_flat020 = (CoefficientMerge.scale (40093076482560 : Int) atom0667Coded) := by
  rw [block010_data_flat020_step]
def block010_data_flat021 : CoefficientMerge.Poly := [(nat_lit 1047, Int.ofNat (nat_lit 36889019085312)), (nat_lit 1048, Int.ofNat (nat_lit 40093076482560))]
theorem block010_data_flat021_step : block010_data_flat021 = (CoefficientMerge.fastMerge block010_data_flat019 block010_data_flat020) := by decide +kernel
theorem block010_data_flat021_original : block010_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36889019085312 : Int) atom0666Coded) (CoefficientMerge.scale (40093076482560 : Int) atom0667Coded)) := by
  rw [block010_data_flat021_step, block010_data_flat019_original, block010_data_flat020_original]
def block010_data_flat022 : CoefficientMerge.Poly := [(nat_lit 1049, Int.ofNat (nat_lit 47967118852608))]
theorem block010_data_flat022_step : block010_data_flat022 = (CoefficientMerge.scale (47967118852608 : Int) atom0668Coded) := by decide +kernel
theorem block010_data_flat022_original : block010_data_flat022 = (CoefficientMerge.scale (47967118852608 : Int) atom0668Coded) := by
  rw [block010_data_flat022_step]
def block010_data_flat023 : CoefficientMerge.Poly := [(nat_lit 1058, Int.ofNat (nat_lit 22303076342400))]
theorem block010_data_flat023_step : block010_data_flat023 = (CoefficientMerge.scale (22303076342400 : Int) atom0669Coded) := by decide +kernel
theorem block010_data_flat023_original : block010_data_flat023 = (CoefficientMerge.scale (22303076342400 : Int) atom0669Coded) := by
  rw [block010_data_flat023_step]
def block010_data_flat024 : CoefficientMerge.Poly := [(nat_lit 1059, Int.ofNat (nat_lit 41607678268800))]
theorem block010_data_flat024_step : block010_data_flat024 = (CoefficientMerge.scale (41607678268800 : Int) atom0670Coded) := by decide +kernel
theorem block010_data_flat024_original : block010_data_flat024 = (CoefficientMerge.scale (41607678268800 : Int) atom0670Coded) := by
  rw [block010_data_flat024_step]
def block010_data_flat025 : CoefficientMerge.Poly := [(nat_lit 1058, Int.ofNat (nat_lit 22303076342400)), (nat_lit 1059, Int.ofNat (nat_lit 41607678268800))]
theorem block010_data_flat025_step : block010_data_flat025 = (CoefficientMerge.fastMerge block010_data_flat023 block010_data_flat024) := by decide +kernel
theorem block010_data_flat025_original : block010_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22303076342400 : Int) atom0669Coded) (CoefficientMerge.scale (41607678268800 : Int) atom0670Coded)) := by
  rw [block010_data_flat025_step, block010_data_flat023_original, block010_data_flat024_original]
def block010_data_flat026 : CoefficientMerge.Poly := [(nat_lit 1049, Int.ofNat (nat_lit 47967118852608)), (nat_lit 1058, Int.ofNat (nat_lit 22303076342400)), (nat_lit 1059, Int.ofNat (nat_lit 41607678268800))]
theorem block010_data_flat026_step : block010_data_flat026 = (CoefficientMerge.fastMerge block010_data_flat022 block010_data_flat025) := by decide +kernel
theorem block010_data_flat026_original : block010_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (47967118852608 : Int) atom0668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22303076342400 : Int) atom0669Coded) (CoefficientMerge.scale (41607678268800 : Int) atom0670Coded))) := by
  rw [block010_data_flat026_step, block010_data_flat022_original, block010_data_flat025_original]
def block010_data_flat027 : CoefficientMerge.Poly := [(nat_lit 1047, Int.ofNat (nat_lit 36889019085312)), (nat_lit 1048, Int.ofNat (nat_lit 40093076482560)), (nat_lit 1049, Int.ofNat (nat_lit 47967118852608)), (nat_lit 1058, Int.ofNat (nat_lit 22303076342400)), (nat_lit 1059, Int.ofNat (nat_lit 41607678268800))]
theorem block010_data_flat027_step : block010_data_flat027 = (CoefficientMerge.fastMerge block010_data_flat021 block010_data_flat026) := by decide +kernel
theorem block010_data_flat027_original : block010_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36889019085312 : Int) atom0666Coded) (CoefficientMerge.scale (40093076482560 : Int) atom0667Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47967118852608 : Int) atom0668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22303076342400 : Int) atom0669Coded) (CoefficientMerge.scale (41607678268800 : Int) atom0670Coded)))) := by
  rw [block010_data_flat027_step, block010_data_flat021_original, block010_data_flat026_original]
def block010_data_flat028 : CoefficientMerge.Poly := [(nat_lit 1060, Int.ofNat (nat_lit 40696296681600))]
theorem block010_data_flat028_step : block010_data_flat028 = (CoefficientMerge.scale (40696296681600 : Int) atom0671Coded) := by decide +kernel
theorem block010_data_flat028_original : block010_data_flat028 = (CoefficientMerge.scale (40696296681600 : Int) atom0671Coded) := by
  rw [block010_data_flat028_step]
def block010_data_flat029 : CoefficientMerge.Poly := [(nat_lit 1061, Int.ofNat (nat_lit 39732005577600))]
theorem block010_data_flat029_step : block010_data_flat029 = (CoefficientMerge.scale (39732005577600 : Int) atom0672Coded) := by decide +kernel
theorem block010_data_flat029_original : block010_data_flat029 = (CoefficientMerge.scale (39732005577600 : Int) atom0672Coded) := by
  rw [block010_data_flat029_step]
def block010_data_flat030 : CoefficientMerge.Poly := [(nat_lit 1060, Int.ofNat (nat_lit 40696296681600)), (nat_lit 1061, Int.ofNat (nat_lit 39732005577600))]
theorem block010_data_flat030_step : block010_data_flat030 = (CoefficientMerge.fastMerge block010_data_flat028 block010_data_flat029) := by decide +kernel
theorem block010_data_flat030_original : block010_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40696296681600 : Int) atom0671Coded) (CoefficientMerge.scale (39732005577600 : Int) atom0672Coded)) := by
  rw [block010_data_flat030_step, block010_data_flat028_original, block010_data_flat029_original]
def block010_data_flat031 : CoefficientMerge.Poly := [(nat_lit 1062, Int.ofNat (nat_lit 36634078409600))]
theorem block010_data_flat031_step : block010_data_flat031 = (CoefficientMerge.scale (36634078409600 : Int) atom0673Coded) := by decide +kernel
theorem block010_data_flat031_original : block010_data_flat031 = (CoefficientMerge.scale (36634078409600 : Int) atom0673Coded) := by
  rw [block010_data_flat031_step]
def block010_data_flat032 : CoefficientMerge.Poly := [(nat_lit 1063, Int.ofNat (nat_lit 35706410006400))]
theorem block010_data_flat032_step : block010_data_flat032 = (CoefficientMerge.scale (35706410006400 : Int) atom0674Coded) := by decide +kernel
theorem block010_data_flat032_original : block010_data_flat032 = (CoefficientMerge.scale (35706410006400 : Int) atom0674Coded) := by
  rw [block010_data_flat032_step]
def block010_data_flat033 : CoefficientMerge.Poly := [(nat_lit 1064, Int.ofNat (nat_lit 35656153545600))]
theorem block010_data_flat033_step : block010_data_flat033 = (CoefficientMerge.scale (35656153545600 : Int) atom0675Coded) := by decide +kernel
theorem block010_data_flat033_original : block010_data_flat033 = (CoefficientMerge.scale (35656153545600 : Int) atom0675Coded) := by
  rw [block010_data_flat033_step]
def block010_data_flat034 : CoefficientMerge.Poly := [(nat_lit 1063, Int.ofNat (nat_lit 35706410006400)), (nat_lit 1064, Int.ofNat (nat_lit 35656153545600))]
theorem block010_data_flat034_step : block010_data_flat034 = (CoefficientMerge.fastMerge block010_data_flat032 block010_data_flat033) := by decide +kernel
theorem block010_data_flat034_original : block010_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35706410006400 : Int) atom0674Coded) (CoefficientMerge.scale (35656153545600 : Int) atom0675Coded)) := by
  rw [block010_data_flat034_step, block010_data_flat032_original, block010_data_flat033_original]
def block010_data_flat035 : CoefficientMerge.Poly := [(nat_lit 1062, Int.ofNat (nat_lit 36634078409600)), (nat_lit 1063, Int.ofNat (nat_lit 35706410006400)), (nat_lit 1064, Int.ofNat (nat_lit 35656153545600))]
theorem block010_data_flat035_step : block010_data_flat035 = (CoefficientMerge.fastMerge block010_data_flat031 block010_data_flat034) := by decide +kernel
theorem block010_data_flat035_original : block010_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36634078409600 : Int) atom0673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35706410006400 : Int) atom0674Coded) (CoefficientMerge.scale (35656153545600 : Int) atom0675Coded))) := by
  rw [block010_data_flat035_step, block010_data_flat031_original, block010_data_flat034_original]
def block010_data_flat036 : CoefficientMerge.Poly := [(nat_lit 1060, Int.ofNat (nat_lit 40696296681600)), (nat_lit 1061, Int.ofNat (nat_lit 39732005577600)), (nat_lit 1062, Int.ofNat (nat_lit 36634078409600)), (nat_lit 1063, Int.ofNat (nat_lit 35706410006400)), (nat_lit 1064, Int.ofNat (nat_lit 35656153545600))]
theorem block010_data_flat036_step : block010_data_flat036 = (CoefficientMerge.fastMerge block010_data_flat030 block010_data_flat035) := by decide +kernel
theorem block010_data_flat036_original : block010_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40696296681600 : Int) atom0671Coded) (CoefficientMerge.scale (39732005577600 : Int) atom0672Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36634078409600 : Int) atom0673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35706410006400 : Int) atom0674Coded) (CoefficientMerge.scale (35656153545600 : Int) atom0675Coded)))) := by
  rw [block010_data_flat036_step, block010_data_flat030_original, block010_data_flat035_original]
def block010_data_flat037 : CoefficientMerge.Poly := [(nat_lit 1047, Int.ofNat (nat_lit 36889019085312)), (nat_lit 1048, Int.ofNat (nat_lit 40093076482560)), (nat_lit 1049, Int.ofNat (nat_lit 47967118852608)), (nat_lit 1058, Int.ofNat (nat_lit 22303076342400)), (nat_lit 1059, Int.ofNat (nat_lit 41607678268800)), (nat_lit 1060, Int.ofNat (nat_lit 40696296681600)), (nat_lit 1061, Int.ofNat (nat_lit 39732005577600)), (nat_lit 1062, Int.ofNat (nat_lit 36634078409600)), (nat_lit 1063, Int.ofNat (nat_lit 35706410006400)), (nat_lit 1064, Int.ofNat (nat_lit 35656153545600))]
theorem block010_data_flat037_step : block010_data_flat037 = (CoefficientMerge.fastMerge block010_data_flat027 block010_data_flat036) := by decide +kernel
theorem block010_data_flat037_original : block010_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36889019085312 : Int) atom0666Coded) (CoefficientMerge.scale (40093076482560 : Int) atom0667Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47967118852608 : Int) atom0668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22303076342400 : Int) atom0669Coded) (CoefficientMerge.scale (41607678268800 : Int) atom0670Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40696296681600 : Int) atom0671Coded) (CoefficientMerge.scale (39732005577600 : Int) atom0672Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36634078409600 : Int) atom0673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35706410006400 : Int) atom0674Coded) (CoefficientMerge.scale (35656153545600 : Int) atom0675Coded))))) := by
  rw [block010_data_flat037_step, block010_data_flat027_original, block010_data_flat036_original]
def block010_data_flat038 : CoefficientMerge.Poly := [(nat_lit 1037, Int.ofNat (nat_lit 37423734021504)), (nat_lit 1038, Int.ofNat (nat_lit 34748060719104)), (nat_lit 1039, Int.ofNat (nat_lit 34509342530304)), (nat_lit 1040, Int.ofNat (nat_lit 34217714824704)), (nat_lit 1041, Int.ofNat (nat_lit 31960616904704)), (nat_lit 1042, Int.ofNat (nat_lit 31446597832704)), (nat_lit 1043, Int.ofNat (nat_lit 31809990703104)), (nat_lit 1044, Int.ofNat (nat_lit 41404370635008)), (nat_lit 1045, Int.ofNat (nat_lit 31000486141440)), (nat_lit 1046, Int.ofNat (nat_lit 41272519396608)), (nat_lit 1047, Int.ofNat (nat_lit 36889019085312)), (nat_lit 1048, Int.ofNat (nat_lit 40093076482560)), (nat_lit 1049, Int.ofNat (nat_lit 47967118852608)), (nat_lit 1058, Int.ofNat (nat_lit 22303076342400)), (nat_lit 1059, Int.ofNat (nat_lit 41607678268800)), (nat_lit 1060, Int.ofNat (nat_lit 40696296681600)), (nat_lit 1061, Int.ofNat (nat_lit 39732005577600)), (nat_lit 1062, Int.ofNat (nat_lit 36634078409600)), (nat_lit 1063, Int.ofNat (nat_lit 35706410006400)), (nat_lit 1064, Int.ofNat (nat_lit 35656153545600))]
theorem block010_data_flat038_step : block010_data_flat038 = (CoefficientMerge.fastMerge block010_data_flat018 block010_data_flat037) := by decide +kernel
theorem block010_data_flat038_original : block010_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37423734021504 : Int) atom0656Coded) (CoefficientMerge.scale (34748060719104 : Int) atom0657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34509342530304 : Int) atom0658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34217714824704 : Int) atom0659Coded) (CoefficientMerge.scale (31960616904704 : Int) atom0660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31446597832704 : Int) atom0661Coded) (CoefficientMerge.scale (31809990703104 : Int) atom0662Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41404370635008 : Int) atom0663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31000486141440 : Int) atom0664Coded) (CoefficientMerge.scale (41272519396608 : Int) atom0665Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36889019085312 : Int) atom0666Coded) (CoefficientMerge.scale (40093076482560 : Int) atom0667Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47967118852608 : Int) atom0668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22303076342400 : Int) atom0669Coded) (CoefficientMerge.scale (41607678268800 : Int) atom0670Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40696296681600 : Int) atom0671Coded) (CoefficientMerge.scale (39732005577600 : Int) atom0672Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36634078409600 : Int) atom0673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35706410006400 : Int) atom0674Coded) (CoefficientMerge.scale (35656153545600 : Int) atom0675Coded)))))) := by
  rw [block010_data_flat038_step, block010_data_flat018_original, block010_data_flat037_original]
def block010_data_flat039 : CoefficientMerge.Poly := [(nat_lit 1065, Int.ofNat (nat_lit 44345527833600))]
theorem block010_data_flat039_step : block010_data_flat039 = (CoefficientMerge.scale (44345527833600 : Int) atom0676Coded) := by decide +kernel
theorem block010_data_flat039_original : block010_data_flat039 = (CoefficientMerge.scale (44345527833600 : Int) atom0676Coded) := by
  rw [block010_data_flat039_step]
def block010_data_flat040 : CoefficientMerge.Poly := [(nat_lit 1066, Int.ofNat (nat_lit 34468180210800))]
theorem block010_data_flat040_step : block010_data_flat040 = (CoefficientMerge.scale (34468180210800 : Int) atom0677Coded) := by decide +kernel
theorem block010_data_flat040_original : block010_data_flat040 = (CoefficientMerge.scale (34468180210800 : Int) atom0677Coded) := by
  rw [block010_data_flat040_step]
def block010_data_flat041 : CoefficientMerge.Poly := [(nat_lit 1065, Int.ofNat (nat_lit 44345527833600)), (nat_lit 1066, Int.ofNat (nat_lit 34468180210800))]
theorem block010_data_flat041_step : block010_data_flat041 = (CoefficientMerge.fastMerge block010_data_flat039 block010_data_flat040) := by decide +kernel
theorem block010_data_flat041_original : block010_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (44345527833600 : Int) atom0676Coded) (CoefficientMerge.scale (34468180210800 : Int) atom0677Coded)) := by
  rw [block010_data_flat041_step, block010_data_flat039_original, block010_data_flat040_original]
def block010_data_flat042 : CoefficientMerge.Poly := [(nat_lit 1067, Int.ofNat (nat_lit 45222671692800))]
theorem block010_data_flat042_step : block010_data_flat042 = (CoefficientMerge.scale (45222671692800 : Int) atom0678Coded) := by decide +kernel
theorem block010_data_flat042_original : block010_data_flat042 = (CoefficientMerge.scale (45222671692800 : Int) atom0678Coded) := by
  rw [block010_data_flat042_step]
def block010_data_flat043 : CoefficientMerge.Poly := [(nat_lit 1068, Int.ofNat (nat_lit 40427074270800))]
theorem block010_data_flat043_step : block010_data_flat043 = (CoefficientMerge.scale (40427074270800 : Int) atom0679Coded) := by decide +kernel
theorem block010_data_flat043_original : block010_data_flat043 = (CoefficientMerge.scale (40427074270800 : Int) atom0679Coded) := by
  rw [block010_data_flat043_step]
def block010_data_flat044 : CoefficientMerge.Poly := [(nat_lit 1069, Int.ofNat (nat_lit 43815922189200))]
theorem block010_data_flat044_step : block010_data_flat044 = (CoefficientMerge.scale (43815922189200 : Int) atom0680Coded) := by decide +kernel
theorem block010_data_flat044_original : block010_data_flat044 = (CoefficientMerge.scale (43815922189200 : Int) atom0680Coded) := by
  rw [block010_data_flat044_step]
def block010_data_flat045 : CoefficientMerge.Poly := [(nat_lit 1068, Int.ofNat (nat_lit 40427074270800)), (nat_lit 1069, Int.ofNat (nat_lit 43815922189200))]
theorem block010_data_flat045_step : block010_data_flat045 = (CoefficientMerge.fastMerge block010_data_flat043 block010_data_flat044) := by decide +kernel
theorem block010_data_flat045_original : block010_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40427074270800 : Int) atom0679Coded) (CoefficientMerge.scale (43815922189200 : Int) atom0680Coded)) := by
  rw [block010_data_flat045_step, block010_data_flat043_original, block010_data_flat044_original]
def block010_data_flat046 : CoefficientMerge.Poly := [(nat_lit 1067, Int.ofNat (nat_lit 45222671692800)), (nat_lit 1068, Int.ofNat (nat_lit 40427074270800)), (nat_lit 1069, Int.ofNat (nat_lit 43815922189200))]
theorem block010_data_flat046_step : block010_data_flat046 = (CoefficientMerge.fastMerge block010_data_flat042 block010_data_flat045) := by decide +kernel
theorem block010_data_flat046_original : block010_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (45222671692800 : Int) atom0678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40427074270800 : Int) atom0679Coded) (CoefficientMerge.scale (43815922189200 : Int) atom0680Coded))) := by
  rw [block010_data_flat046_step, block010_data_flat042_original, block010_data_flat045_original]
def block010_data_flat047 : CoefficientMerge.Poly := [(nat_lit 1065, Int.ofNat (nat_lit 44345527833600)), (nat_lit 1066, Int.ofNat (nat_lit 34468180210800)), (nat_lit 1067, Int.ofNat (nat_lit 45222671692800)), (nat_lit 1068, Int.ofNat (nat_lit 40427074270800)), (nat_lit 1069, Int.ofNat (nat_lit 43815922189200))]
theorem block010_data_flat047_step : block010_data_flat047 = (CoefficientMerge.fastMerge block010_data_flat041 block010_data_flat046) := by decide +kernel
theorem block010_data_flat047_original : block010_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44345527833600 : Int) atom0676Coded) (CoefficientMerge.scale (34468180210800 : Int) atom0677Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45222671692800 : Int) atom0678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40427074270800 : Int) atom0679Coded) (CoefficientMerge.scale (43815922189200 : Int) atom0680Coded)))) := by
  rw [block010_data_flat047_step, block010_data_flat041_original, block010_data_flat046_original]
def block010_data_flat048 : CoefficientMerge.Poly := [(nat_lit 1070, Int.ofNat (nat_lit 51874755080400))]
theorem block010_data_flat048_step : block010_data_flat048 = (CoefficientMerge.scale (51874755080400 : Int) atom0681Coded) := by decide +kernel
theorem block010_data_flat048_original : block010_data_flat048 = (CoefficientMerge.scale (51874755080400 : Int) atom0681Coded) := by
  rw [block010_data_flat048_step]
def block010_data_flat049 : CoefficientMerge.Poly := [(nat_lit 1080, Int.ofNat (nat_lit 24598926777600))]
theorem block010_data_flat049_step : block010_data_flat049 = (CoefficientMerge.scale (24598926777600 : Int) atom0682Coded) := by decide +kernel
theorem block010_data_flat049_original : block010_data_flat049 = (CoefficientMerge.scale (24598926777600 : Int) atom0682Coded) := by
  rw [block010_data_flat049_step]
def block010_data_flat050 : CoefficientMerge.Poly := [(nat_lit 1070, Int.ofNat (nat_lit 51874755080400)), (nat_lit 1080, Int.ofNat (nat_lit 24598926777600))]
theorem block010_data_flat050_step : block010_data_flat050 = (CoefficientMerge.fastMerge block010_data_flat048 block010_data_flat049) := by decide +kernel
theorem block010_data_flat050_original : block010_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (51874755080400 : Int) atom0681Coded) (CoefficientMerge.scale (24598926777600 : Int) atom0682Coded)) := by
  rw [block010_data_flat050_step, block010_data_flat048_original, block010_data_flat049_original]
def block010_data_flat051 : CoefficientMerge.Poly := [(nat_lit 1081, Int.ofNat (nat_lit 46170868262400))]
theorem block010_data_flat051_step : block010_data_flat051 = (CoefficientMerge.scale (46170868262400 : Int) atom0683Coded) := by decide +kernel
theorem block010_data_flat051_original : block010_data_flat051 = (CoefficientMerge.scale (46170868262400 : Int) atom0683Coded) := by
  rw [block010_data_flat051_step]
def block010_data_flat052 : CoefficientMerge.Poly := [(nat_lit 1082, Int.ofNat (nat_lit 44365747910400))]
theorem block010_data_flat052_step : block010_data_flat052 = (CoefficientMerge.scale (44365747910400 : Int) atom0684Coded) := by decide +kernel
theorem block010_data_flat052_original : block010_data_flat052 = (CoefficientMerge.scale (44365747910400 : Int) atom0684Coded) := by
  rw [block010_data_flat052_step]
def block010_data_flat053 : CoefficientMerge.Poly := [(nat_lit 1083, Int.ofNat (nat_lit 41113185478400))]
theorem block010_data_flat053_step : block010_data_flat053 = (CoefficientMerge.scale (41113185478400 : Int) atom0685Coded) := by decide +kernel
theorem block010_data_flat053_original : block010_data_flat053 = (CoefficientMerge.scale (41113185478400 : Int) atom0685Coded) := by
  rw [block010_data_flat053_step]
def block010_data_flat054 : CoefficientMerge.Poly := [(nat_lit 1082, Int.ofNat (nat_lit 44365747910400)), (nat_lit 1083, Int.ofNat (nat_lit 41113185478400))]
theorem block010_data_flat054_step : block010_data_flat054 = (CoefficientMerge.fastMerge block010_data_flat052 block010_data_flat053) := by decide +kernel
theorem block010_data_flat054_original : block010_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (44365747910400 : Int) atom0684Coded) (CoefficientMerge.scale (41113185478400 : Int) atom0685Coded)) := by
  rw [block010_data_flat054_step, block010_data_flat052_original, block010_data_flat053_original]
def block010_data_flat055 : CoefficientMerge.Poly := [(nat_lit 1081, Int.ofNat (nat_lit 46170868262400)), (nat_lit 1082, Int.ofNat (nat_lit 44365747910400)), (nat_lit 1083, Int.ofNat (nat_lit 41113185478400))]
theorem block010_data_flat055_step : block010_data_flat055 = (CoefficientMerge.fastMerge block010_data_flat051 block010_data_flat054) := by decide +kernel
theorem block010_data_flat055_original : block010_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46170868262400 : Int) atom0683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44365747910400 : Int) atom0684Coded) (CoefficientMerge.scale (41113185478400 : Int) atom0685Coded))) := by
  rw [block010_data_flat055_step, block010_data_flat051_original, block010_data_flat054_original]
def block010_data_flat056 : CoefficientMerge.Poly := [(nat_lit 1070, Int.ofNat (nat_lit 51874755080400)), (nat_lit 1080, Int.ofNat (nat_lit 24598926777600)), (nat_lit 1081, Int.ofNat (nat_lit 46170868262400)), (nat_lit 1082, Int.ofNat (nat_lit 44365747910400)), (nat_lit 1083, Int.ofNat (nat_lit 41113185478400))]
theorem block010_data_flat056_step : block010_data_flat056 = (CoefficientMerge.fastMerge block010_data_flat050 block010_data_flat055) := by decide +kernel
theorem block010_data_flat056_original : block010_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (51874755080400 : Int) atom0681Coded) (CoefficientMerge.scale (24598926777600 : Int) atom0682Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46170868262400 : Int) atom0683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44365747910400 : Int) atom0684Coded) (CoefficientMerge.scale (41113185478400 : Int) atom0685Coded)))) := by
  rw [block010_data_flat056_step, block010_data_flat050_original, block010_data_flat055_original]
def block010_data_flat057 : CoefficientMerge.Poly := [(nat_lit 1065, Int.ofNat (nat_lit 44345527833600)), (nat_lit 1066, Int.ofNat (nat_lit 34468180210800)), (nat_lit 1067, Int.ofNat (nat_lit 45222671692800)), (nat_lit 1068, Int.ofNat (nat_lit 40427074270800)), (nat_lit 1069, Int.ofNat (nat_lit 43815922189200)), (nat_lit 1070, Int.ofNat (nat_lit 51874755080400)), (nat_lit 1080, Int.ofNat (nat_lit 24598926777600)), (nat_lit 1081, Int.ofNat (nat_lit 46170868262400)), (nat_lit 1082, Int.ofNat (nat_lit 44365747910400)), (nat_lit 1083, Int.ofNat (nat_lit 41113185478400))]
theorem block010_data_flat057_step : block010_data_flat057 = (CoefficientMerge.fastMerge block010_data_flat047 block010_data_flat056) := by decide +kernel
theorem block010_data_flat057_original : block010_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44345527833600 : Int) atom0676Coded) (CoefficientMerge.scale (34468180210800 : Int) atom0677Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45222671692800 : Int) atom0678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40427074270800 : Int) atom0679Coded) (CoefficientMerge.scale (43815922189200 : Int) atom0680Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (51874755080400 : Int) atom0681Coded) (CoefficientMerge.scale (24598926777600 : Int) atom0682Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46170868262400 : Int) atom0683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44365747910400 : Int) atom0684Coded) (CoefficientMerge.scale (41113185478400 : Int) atom0685Coded))))) := by
  rw [block010_data_flat057_step, block010_data_flat047_original, block010_data_flat056_original]
def block010_data_flat058 : CoefficientMerge.Poly := [(nat_lit 1084, Int.ofNat (nat_lit 39603701894400))]
theorem block010_data_flat058_step : block010_data_flat058 = (CoefficientMerge.scale (39603701894400 : Int) atom0686Coded) := by decide +kernel
theorem block010_data_flat058_original : block010_data_flat058 = (CoefficientMerge.scale (39603701894400 : Int) atom0686Coded) := by
  rw [block010_data_flat058_step]
def block010_data_flat059 : CoefficientMerge.Poly := [(nat_lit 1085, Int.ofNat (nat_lit 38971630252800))]
theorem block010_data_flat059_step : block010_data_flat059 = (CoefficientMerge.scale (38971630252800 : Int) atom0687Coded) := by decide +kernel
theorem block010_data_flat059_original : block010_data_flat059 = (CoefficientMerge.scale (38971630252800 : Int) atom0687Coded) := by
  rw [block010_data_flat059_step]
def block010_data_flat060 : CoefficientMerge.Poly := [(nat_lit 1084, Int.ofNat (nat_lit 39603701894400)), (nat_lit 1085, Int.ofNat (nat_lit 38971630252800))]
theorem block010_data_flat060_step : block010_data_flat060 = (CoefficientMerge.fastMerge block010_data_flat058 block010_data_flat059) := by decide +kernel
theorem block010_data_flat060_original : block010_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (39603701894400 : Int) atom0686Coded) (CoefficientMerge.scale (38971630252800 : Int) atom0687Coded)) := by
  rw [block010_data_flat060_step, block010_data_flat058_original, block010_data_flat059_original]
def block010_data_flat061 : CoefficientMerge.Poly := [(nat_lit 1086, Int.ofNat (nat_lit 47136694348800))]
theorem block010_data_flat061_step : block010_data_flat061 = (CoefficientMerge.scale (47136694348800 : Int) atom0688Coded) := by decide +kernel
theorem block010_data_flat061_original : block010_data_flat061 = (CoefficientMerge.scale (47136694348800 : Int) atom0688Coded) := by
  rw [block010_data_flat061_step]
def block010_data_flat062 : CoefficientMerge.Poly := [(nat_lit 1087, Int.ofNat (nat_lit 37088825104800))]
theorem block010_data_flat062_step : block010_data_flat062 = (CoefficientMerge.scale (37088825104800 : Int) atom0689Coded) := by decide +kernel
theorem block010_data_flat062_original : block010_data_flat062 = (CoefficientMerge.scale (37088825104800 : Int) atom0689Coded) := by
  rw [block010_data_flat062_step]
def block010_data_flat063 : CoefficientMerge.Poly := [(nat_lit 1088, Int.ofNat (nat_lit 49022833305600))]
theorem block010_data_flat063_step : block010_data_flat063 = (CoefficientMerge.scale (49022833305600 : Int) atom0690Coded) := by decide +kernel
theorem block010_data_flat063_original : block010_data_flat063 = (CoefficientMerge.scale (49022833305600 : Int) atom0690Coded) := by
  rw [block010_data_flat063_step]
def block010_data_flat064 : CoefficientMerge.Poly := [(nat_lit 1087, Int.ofNat (nat_lit 37088825104800)), (nat_lit 1088, Int.ofNat (nat_lit 49022833305600))]
theorem block010_data_flat064_step : block010_data_flat064 = (CoefficientMerge.fastMerge block010_data_flat062 block010_data_flat063) := by decide +kernel
theorem block010_data_flat064_original : block010_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (37088825104800 : Int) atom0689Coded) (CoefficientMerge.scale (49022833305600 : Int) atom0690Coded)) := by
  rw [block010_data_flat064_step, block010_data_flat062_original, block010_data_flat063_original]
def block010_data_flat065 : CoefficientMerge.Poly := [(nat_lit 1086, Int.ofNat (nat_lit 47136694348800)), (nat_lit 1087, Int.ofNat (nat_lit 37088825104800)), (nat_lit 1088, Int.ofNat (nat_lit 49022833305600))]
theorem block010_data_flat065_step : block010_data_flat065 = (CoefficientMerge.fastMerge block010_data_flat061 block010_data_flat064) := by decide +kernel
theorem block010_data_flat065_original : block010_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (47136694348800 : Int) atom0688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37088825104800 : Int) atom0689Coded) (CoefficientMerge.scale (49022833305600 : Int) atom0690Coded))) := by
  rw [block010_data_flat065_step, block010_data_flat061_original, block010_data_flat064_original]
def block010_data_flat066 : CoefficientMerge.Poly := [(nat_lit 1084, Int.ofNat (nat_lit 39603701894400)), (nat_lit 1085, Int.ofNat (nat_lit 38971630252800)), (nat_lit 1086, Int.ofNat (nat_lit 47136694348800)), (nat_lit 1087, Int.ofNat (nat_lit 37088825104800)), (nat_lit 1088, Int.ofNat (nat_lit 49022833305600))]
theorem block010_data_flat066_step : block010_data_flat066 = (CoefficientMerge.fastMerge block010_data_flat060 block010_data_flat065) := by decide +kernel
theorem block010_data_flat066_original : block010_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39603701894400 : Int) atom0686Coded) (CoefficientMerge.scale (38971630252800 : Int) atom0687Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47136694348800 : Int) atom0688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37088825104800 : Int) atom0689Coded) (CoefficientMerge.scale (49022833305600 : Int) atom0690Coded)))) := by
  rw [block010_data_flat066_step, block010_data_flat060_original, block010_data_flat065_original]
def block010_data_flat067 : CoefficientMerge.Poly := [(nat_lit 1089, Int.ofNat (nat_lit 42821685900000))]
theorem block010_data_flat067_step : block010_data_flat067 = (CoefficientMerge.scale (42821685900000 : Int) atom0691Coded) := by decide +kernel
theorem block010_data_flat067_original : block010_data_flat067 = (CoefficientMerge.scale (42821685900000 : Int) atom0691Coded) := by
  rw [block010_data_flat067_step]
def block010_data_flat068 : CoefficientMerge.Poly := [(nat_lit 1090, Int.ofNat (nat_lit 46253783368800))]
theorem block010_data_flat068_step : block010_data_flat068 = (CoefficientMerge.scale (46253783368800 : Int) atom0692Coded) := by decide +kernel
theorem block010_data_flat068_original : block010_data_flat068 = (CoefficientMerge.scale (46253783368800 : Int) atom0692Coded) := by
  rw [block010_data_flat068_step]
def block010_data_flat069 : CoefficientMerge.Poly := [(nat_lit 1089, Int.ofNat (nat_lit 42821685900000)), (nat_lit 1090, Int.ofNat (nat_lit 46253783368800))]
theorem block010_data_flat069_step : block010_data_flat069 = (CoefficientMerge.fastMerge block010_data_flat067 block010_data_flat068) := by decide +kernel
theorem block010_data_flat069_original : block010_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (42821685900000 : Int) atom0691Coded) (CoefficientMerge.scale (46253783368800 : Int) atom0692Coded)) := by
  rw [block010_data_flat069_step, block010_data_flat067_original, block010_data_flat068_original]
def block010_data_flat070 : CoefficientMerge.Poly := [(nat_lit 1091, Int.ofNat (nat_lit 54355865810400))]
theorem block010_data_flat070_step : block010_data_flat070 = (CoefficientMerge.scale (54355865810400 : Int) atom0693Coded) := by decide +kernel
theorem block010_data_flat070_original : block010_data_flat070 = (CoefficientMerge.scale (54355865810400 : Int) atom0693Coded) := by
  rw [block010_data_flat070_step]
def block010_data_flat071 : CoefficientMerge.Poly := [(nat_lit 1102, Int.ofNat (nat_lit 26866266336000))]
theorem block010_data_flat071_step : block010_data_flat071 = (CoefficientMerge.scale (26866266336000 : Int) atom0694Coded) := by decide +kernel
theorem block010_data_flat071_original : block010_data_flat071 = (CoefficientMerge.scale (26866266336000 : Int) atom0694Coded) := by
  rw [block010_data_flat071_step]
def block010_data_flat072 : CoefficientMerge.Poly := [(nat_lit 1103, Int.ofNat (nat_lit 50413919673600))]
theorem block010_data_flat072_step : block010_data_flat072 = (CoefficientMerge.scale (50413919673600 : Int) atom0695Coded) := by decide +kernel
theorem block010_data_flat072_original : block010_data_flat072 = (CoefficientMerge.scale (50413919673600 : Int) atom0695Coded) := by
  rw [block010_data_flat072_step]
def block010_data_flat073 : CoefficientMerge.Poly := [(nat_lit 1102, Int.ofNat (nat_lit 26866266336000)), (nat_lit 1103, Int.ofNat (nat_lit 50413919673600))]
theorem block010_data_flat073_step : block010_data_flat073 = (CoefficientMerge.fastMerge block010_data_flat071 block010_data_flat072) := by decide +kernel
theorem block010_data_flat073_original : block010_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26866266336000 : Int) atom0694Coded) (CoefficientMerge.scale (50413919673600 : Int) atom0695Coded)) := by
  rw [block010_data_flat073_step, block010_data_flat071_original, block010_data_flat072_original]
def block010_data_flat074 : CoefficientMerge.Poly := [(nat_lit 1091, Int.ofNat (nat_lit 54355865810400)), (nat_lit 1102, Int.ofNat (nat_lit 26866266336000)), (nat_lit 1103, Int.ofNat (nat_lit 50413919673600))]
theorem block010_data_flat074_step : block010_data_flat074 = (CoefficientMerge.fastMerge block010_data_flat070 block010_data_flat073) := by decide +kernel
theorem block010_data_flat074_original : block010_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (54355865810400 : Int) atom0693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26866266336000 : Int) atom0694Coded) (CoefficientMerge.scale (50413919673600 : Int) atom0695Coded))) := by
  rw [block010_data_flat074_step, block010_data_flat070_original, block010_data_flat073_original]
def block010_data_flat075 : CoefficientMerge.Poly := [(nat_lit 1089, Int.ofNat (nat_lit 42821685900000)), (nat_lit 1090, Int.ofNat (nat_lit 46253783368800)), (nat_lit 1091, Int.ofNat (nat_lit 54355865810400)), (nat_lit 1102, Int.ofNat (nat_lit 26866266336000)), (nat_lit 1103, Int.ofNat (nat_lit 50413919673600))]
theorem block010_data_flat075_step : block010_data_flat075 = (CoefficientMerge.fastMerge block010_data_flat069 block010_data_flat074) := by decide +kernel
theorem block010_data_flat075_original : block010_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42821685900000 : Int) atom0691Coded) (CoefficientMerge.scale (46253783368800 : Int) atom0692Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54355865810400 : Int) atom0693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26866266336000 : Int) atom0694Coded) (CoefficientMerge.scale (50413919673600 : Int) atom0695Coded)))) := by
  rw [block010_data_flat075_step, block010_data_flat069_original, block010_data_flat074_original]
def block010_data_flat076 : CoefficientMerge.Poly := [(nat_lit 1084, Int.ofNat (nat_lit 39603701894400)), (nat_lit 1085, Int.ofNat (nat_lit 38971630252800)), (nat_lit 1086, Int.ofNat (nat_lit 47136694348800)), (nat_lit 1087, Int.ofNat (nat_lit 37088825104800)), (nat_lit 1088, Int.ofNat (nat_lit 49022833305600)), (nat_lit 1089, Int.ofNat (nat_lit 42821685900000)), (nat_lit 1090, Int.ofNat (nat_lit 46253783368800)), (nat_lit 1091, Int.ofNat (nat_lit 54355865810400)), (nat_lit 1102, Int.ofNat (nat_lit 26866266336000)), (nat_lit 1103, Int.ofNat (nat_lit 50413919673600))]
theorem block010_data_flat076_step : block010_data_flat076 = (CoefficientMerge.fastMerge block010_data_flat066 block010_data_flat075) := by decide +kernel
theorem block010_data_flat076_original : block010_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39603701894400 : Int) atom0686Coded) (CoefficientMerge.scale (38971630252800 : Int) atom0687Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47136694348800 : Int) atom0688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37088825104800 : Int) atom0689Coded) (CoefficientMerge.scale (49022833305600 : Int) atom0690Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42821685900000 : Int) atom0691Coded) (CoefficientMerge.scale (46253783368800 : Int) atom0692Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54355865810400 : Int) atom0693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26866266336000 : Int) atom0694Coded) (CoefficientMerge.scale (50413919673600 : Int) atom0695Coded))))) := by
  rw [block010_data_flat076_step, block010_data_flat066_original, block010_data_flat075_original]
def block010_data_flat077 : CoefficientMerge.Poly := [(nat_lit 1065, Int.ofNat (nat_lit 44345527833600)), (nat_lit 1066, Int.ofNat (nat_lit 34468180210800)), (nat_lit 1067, Int.ofNat (nat_lit 45222671692800)), (nat_lit 1068, Int.ofNat (nat_lit 40427074270800)), (nat_lit 1069, Int.ofNat (nat_lit 43815922189200)), (nat_lit 1070, Int.ofNat (nat_lit 51874755080400)), (nat_lit 1080, Int.ofNat (nat_lit 24598926777600)), (nat_lit 1081, Int.ofNat (nat_lit 46170868262400)), (nat_lit 1082, Int.ofNat (nat_lit 44365747910400)), (nat_lit 1083, Int.ofNat (nat_lit 41113185478400)), (nat_lit 1084, Int.ofNat (nat_lit 39603701894400)), (nat_lit 1085, Int.ofNat (nat_lit 38971630252800)), (nat_lit 1086, Int.ofNat (nat_lit 47136694348800)), (nat_lit 1087, Int.ofNat (nat_lit 37088825104800)), (nat_lit 1088, Int.ofNat (nat_lit 49022833305600)), (nat_lit 1089, Int.ofNat (nat_lit 42821685900000)), (nat_lit 1090, Int.ofNat (nat_lit 46253783368800)), (nat_lit 1091, Int.ofNat (nat_lit 54355865810400)), (nat_lit 1102, Int.ofNat (nat_lit 26866266336000)), (nat_lit 1103, Int.ofNat (nat_lit 50413919673600))]
theorem block010_data_flat077_step : block010_data_flat077 = (CoefficientMerge.fastMerge block010_data_flat057 block010_data_flat076) := by decide +kernel
theorem block010_data_flat077_original : block010_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44345527833600 : Int) atom0676Coded) (CoefficientMerge.scale (34468180210800 : Int) atom0677Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45222671692800 : Int) atom0678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40427074270800 : Int) atom0679Coded) (CoefficientMerge.scale (43815922189200 : Int) atom0680Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (51874755080400 : Int) atom0681Coded) (CoefficientMerge.scale (24598926777600 : Int) atom0682Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46170868262400 : Int) atom0683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44365747910400 : Int) atom0684Coded) (CoefficientMerge.scale (41113185478400 : Int) atom0685Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39603701894400 : Int) atom0686Coded) (CoefficientMerge.scale (38971630252800 : Int) atom0687Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47136694348800 : Int) atom0688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37088825104800 : Int) atom0689Coded) (CoefficientMerge.scale (49022833305600 : Int) atom0690Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42821685900000 : Int) atom0691Coded) (CoefficientMerge.scale (46253783368800 : Int) atom0692Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54355865810400 : Int) atom0693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26866266336000 : Int) atom0694Coded) (CoefficientMerge.scale (50413919673600 : Int) atom0695Coded)))))) := by
  rw [block010_data_flat077_step, block010_data_flat057_original, block010_data_flat076_original]
def block010_data_flat078 : CoefficientMerge.Poly := [(nat_lit 1037, Int.ofNat (nat_lit 37423734021504)), (nat_lit 1038, Int.ofNat (nat_lit 34748060719104)), (nat_lit 1039, Int.ofNat (nat_lit 34509342530304)), (nat_lit 1040, Int.ofNat (nat_lit 34217714824704)), (nat_lit 1041, Int.ofNat (nat_lit 31960616904704)), (nat_lit 1042, Int.ofNat (nat_lit 31446597832704)), (nat_lit 1043, Int.ofNat (nat_lit 31809990703104)), (nat_lit 1044, Int.ofNat (nat_lit 41404370635008)), (nat_lit 1045, Int.ofNat (nat_lit 31000486141440)), (nat_lit 1046, Int.ofNat (nat_lit 41272519396608)), (nat_lit 1047, Int.ofNat (nat_lit 36889019085312)), (nat_lit 1048, Int.ofNat (nat_lit 40093076482560)), (nat_lit 1049, Int.ofNat (nat_lit 47967118852608)), (nat_lit 1058, Int.ofNat (nat_lit 22303076342400)), (nat_lit 1059, Int.ofNat (nat_lit 41607678268800)), (nat_lit 1060, Int.ofNat (nat_lit 40696296681600)), (nat_lit 1061, Int.ofNat (nat_lit 39732005577600)), (nat_lit 1062, Int.ofNat (nat_lit 36634078409600)), (nat_lit 1063, Int.ofNat (nat_lit 35706410006400)), (nat_lit 1064, Int.ofNat (nat_lit 35656153545600)), (nat_lit 1065, Int.ofNat (nat_lit 44345527833600)), (nat_lit 1066, Int.ofNat (nat_lit 34468180210800)), (nat_lit 1067, Int.ofNat (nat_lit 45222671692800)), (nat_lit 1068, Int.ofNat (nat_lit 40427074270800)), (nat_lit 1069, Int.ofNat (nat_lit 43815922189200)), (nat_lit 1070, Int.ofNat (nat_lit 51874755080400)), (nat_lit 1080, Int.ofNat (nat_lit 24598926777600)), (nat_lit 1081, Int.ofNat (nat_lit 46170868262400)), (nat_lit 1082, Int.ofNat (nat_lit 44365747910400)), (nat_lit 1083, Int.ofNat (nat_lit 41113185478400)), (nat_lit 1084, Int.ofNat (nat_lit 39603701894400)), (nat_lit 1085, Int.ofNat (nat_lit 38971630252800)), (nat_lit 1086, Int.ofNat (nat_lit 47136694348800)), (nat_lit 1087, Int.ofNat (nat_lit 37088825104800)), (nat_lit 1088, Int.ofNat (nat_lit 49022833305600)), (nat_lit 1089, Int.ofNat (nat_lit 42821685900000)), (nat_lit 1090, Int.ofNat (nat_lit 46253783368800)), (nat_lit 1091, Int.ofNat (nat_lit 54355865810400)), (nat_lit 1102, Int.ofNat (nat_lit 26866266336000)), (nat_lit 1103, Int.ofNat (nat_lit 50413919673600))]
theorem block010_data_flat078_step : block010_data_flat078 = (CoefficientMerge.fastMerge block010_data_flat038 block010_data_flat077) := by decide +kernel
theorem block010_data_flat078_original : block010_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37423734021504 : Int) atom0656Coded) (CoefficientMerge.scale (34748060719104 : Int) atom0657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34509342530304 : Int) atom0658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34217714824704 : Int) atom0659Coded) (CoefficientMerge.scale (31960616904704 : Int) atom0660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31446597832704 : Int) atom0661Coded) (CoefficientMerge.scale (31809990703104 : Int) atom0662Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41404370635008 : Int) atom0663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31000486141440 : Int) atom0664Coded) (CoefficientMerge.scale (41272519396608 : Int) atom0665Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36889019085312 : Int) atom0666Coded) (CoefficientMerge.scale (40093076482560 : Int) atom0667Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47967118852608 : Int) atom0668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22303076342400 : Int) atom0669Coded) (CoefficientMerge.scale (41607678268800 : Int) atom0670Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40696296681600 : Int) atom0671Coded) (CoefficientMerge.scale (39732005577600 : Int) atom0672Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36634078409600 : Int) atom0673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35706410006400 : Int) atom0674Coded) (CoefficientMerge.scale (35656153545600 : Int) atom0675Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44345527833600 : Int) atom0676Coded) (CoefficientMerge.scale (34468180210800 : Int) atom0677Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45222671692800 : Int) atom0678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40427074270800 : Int) atom0679Coded) (CoefficientMerge.scale (43815922189200 : Int) atom0680Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (51874755080400 : Int) atom0681Coded) (CoefficientMerge.scale (24598926777600 : Int) atom0682Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46170868262400 : Int) atom0683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44365747910400 : Int) atom0684Coded) (CoefficientMerge.scale (41113185478400 : Int) atom0685Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39603701894400 : Int) atom0686Coded) (CoefficientMerge.scale (38971630252800 : Int) atom0687Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47136694348800 : Int) atom0688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37088825104800 : Int) atom0689Coded) (CoefficientMerge.scale (49022833305600 : Int) atom0690Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42821685900000 : Int) atom0691Coded) (CoefficientMerge.scale (46253783368800 : Int) atom0692Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54355865810400 : Int) atom0693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26866266336000 : Int) atom0694Coded) (CoefficientMerge.scale (50413919673600 : Int) atom0695Coded))))))) := by
  rw [block010_data_flat078_step, block010_data_flat038_original, block010_data_flat077_original]
def block010_data_flat079 : CoefficientMerge.Poly := [(nat_lit 1104, Int.ofNat (nat_lit 45984196294400))]
theorem block010_data_flat079_step : block010_data_flat079 = (CoefficientMerge.scale (45984196294400 : Int) atom0696Coded) := by decide +kernel
theorem block010_data_flat079_original : block010_data_flat079 = (CoefficientMerge.scale (45984196294400 : Int) atom0696Coded) := by
  rw [block010_data_flat079_step]
def block010_data_flat080 : CoefficientMerge.Poly := [(nat_lit 1105, Int.ofNat (nat_lit 43724731680000))]
theorem block010_data_flat080_step : block010_data_flat080 = (CoefficientMerge.scale (43724731680000 : Int) atom0697Coded) := by decide +kernel
theorem block010_data_flat080_original : block010_data_flat080 = (CoefficientMerge.scale (43724731680000 : Int) atom0697Coded) := by
  rw [block010_data_flat080_step]
def block010_data_flat081 : CoefficientMerge.Poly := [(nat_lit 1104, Int.ofNat (nat_lit 45984196294400)), (nat_lit 1105, Int.ofNat (nat_lit 43724731680000))]
theorem block010_data_flat081_step : block010_data_flat081 = (CoefficientMerge.fastMerge block010_data_flat079 block010_data_flat080) := by decide +kernel
theorem block010_data_flat081_original : block010_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (45984196294400 : Int) atom0696Coded) (CoefficientMerge.scale (43724731680000 : Int) atom0697Coded)) := by
  rw [block010_data_flat081_step, block010_data_flat079_original, block010_data_flat080_original]
def block010_data_flat082 : CoefficientMerge.Poly := [(nat_lit 1106, Int.ofNat (nat_lit 42342679008000))]
theorem block010_data_flat082_step : block010_data_flat082 = (CoefficientMerge.scale (42342679008000 : Int) atom0698Coded) := by decide +kernel
theorem block010_data_flat082_original : block010_data_flat082 = (CoefficientMerge.scale (42342679008000 : Int) atom0698Coded) := by
  rw [block010_data_flat082_step]
def block010_data_flat083 : CoefficientMerge.Poly := [(nat_lit 1107, Int.ofNat (nat_lit 49927860864000))]
theorem block010_data_flat083_step : block010_data_flat083 = (CoefficientMerge.scale (49927860864000 : Int) atom0699Coded) := by decide +kernel
theorem block010_data_flat083_original : block010_data_flat083 = (CoefficientMerge.scale (49927860864000 : Int) atom0699Coded) := by
  rw [block010_data_flat083_step]
def block010_data_flat084 : CoefficientMerge.Poly := [(nat_lit 1108, Int.ofNat (nat_lit 39228832188000))]
theorem block010_data_flat084_step : block010_data_flat084 = (CoefficientMerge.scale (39228832188000 : Int) atom0700Coded) := by decide +kernel
theorem block010_data_flat084_original : block010_data_flat084 = (CoefficientMerge.scale (39228832188000 : Int) atom0700Coded) := by
  rw [block010_data_flat084_step]
def block010_data_flat085 : CoefficientMerge.Poly := [(nat_lit 1107, Int.ofNat (nat_lit 49927860864000)), (nat_lit 1108, Int.ofNat (nat_lit 39228832188000))]
theorem block010_data_flat085_step : block010_data_flat085 = (CoefficientMerge.fastMerge block010_data_flat083 block010_data_flat084) := by decide +kernel
theorem block010_data_flat085_original : block010_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (49927860864000 : Int) atom0699Coded) (CoefficientMerge.scale (39228832188000 : Int) atom0700Coded)) := by
  rw [block010_data_flat085_step, block010_data_flat083_original, block010_data_flat084_original]
def block010_data_flat086 : CoefficientMerge.Poly := [(nat_lit 1106, Int.ofNat (nat_lit 42342679008000)), (nat_lit 1107, Int.ofNat (nat_lit 49927860864000)), (nat_lit 1108, Int.ofNat (nat_lit 39228832188000))]
theorem block010_data_flat086_step : block010_data_flat086 = (CoefficientMerge.fastMerge block010_data_flat082 block010_data_flat085) := by decide +kernel
theorem block010_data_flat086_original : block010_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (42342679008000 : Int) atom0698Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49927860864000 : Int) atom0699Coded) (CoefficientMerge.scale (39228832188000 : Int) atom0700Coded))) := by
  rw [block010_data_flat086_step, block010_data_flat082_original, block010_data_flat085_original]
def block010_data_flat087 : CoefficientMerge.Poly := [(nat_lit 1104, Int.ofNat (nat_lit 45984196294400)), (nat_lit 1105, Int.ofNat (nat_lit 43724731680000)), (nat_lit 1106, Int.ofNat (nat_lit 42342679008000)), (nat_lit 1107, Int.ofNat (nat_lit 49927860864000)), (nat_lit 1108, Int.ofNat (nat_lit 39228832188000))]
theorem block010_data_flat087_step : block010_data_flat087 = (CoefficientMerge.fastMerge block010_data_flat081 block010_data_flat086) := by decide +kernel
theorem block010_data_flat087_original : block010_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45984196294400 : Int) atom0696Coded) (CoefficientMerge.scale (43724731680000 : Int) atom0697Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42342679008000 : Int) atom0698Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49927860864000 : Int) atom0699Coded) (CoefficientMerge.scale (39228832188000 : Int) atom0700Coded)))) := by
  rw [block010_data_flat087_step, block010_data_flat081_original, block010_data_flat086_original]
def block010_data_flat088 : CoefficientMerge.Poly := [(nat_lit 1109, Int.ofNat (nat_lit 52822994918400))]
theorem block010_data_flat088_step : block010_data_flat088 = (CoefficientMerge.scale (52822994918400 : Int) atom0701Coded) := by decide +kernel
theorem block010_data_flat088_original : block010_data_flat088 = (CoefficientMerge.scale (52822994918400 : Int) atom0701Coded) := by
  rw [block010_data_flat088_step]
def block010_data_flat089 : CoefficientMerge.Poly := [(nat_lit 1110, Int.ofNat (nat_lit 43999571700000))]
theorem block010_data_flat089_step : block010_data_flat089 = (CoefficientMerge.scale (43999571700000 : Int) atom0702Coded) := by decide +kernel
theorem block010_data_flat089_original : block010_data_flat089 = (CoefficientMerge.scale (43999571700000 : Int) atom0702Coded) := by
  rw [block010_data_flat089_step]
def block010_data_flat090 : CoefficientMerge.Poly := [(nat_lit 1109, Int.ofNat (nat_lit 52822994918400)), (nat_lit 1110, Int.ofNat (nat_lit 43999571700000))]
theorem block010_data_flat090_step : block010_data_flat090 = (CoefficientMerge.fastMerge block010_data_flat088 block010_data_flat089) := by decide +kernel
theorem block010_data_flat090_original : block010_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (52822994918400 : Int) atom0701Coded) (CoefficientMerge.scale (43999571700000 : Int) atom0702Coded)) := by
  rw [block010_data_flat090_step, block010_data_flat088_original, block010_data_flat089_original]
def block010_data_flat091 : CoefficientMerge.Poly := [(nat_lit 1111, Int.ofNat (nat_lit 47040248656800))]
theorem block010_data_flat091_step : block010_data_flat091 = (CoefficientMerge.scale (47040248656800 : Int) atom0703Coded) := by decide +kernel
theorem block010_data_flat091_original : block010_data_flat091 = (CoefficientMerge.scale (47040248656800 : Int) atom0703Coded) := by
  rw [block010_data_flat091_step]
def block010_data_flat092 : CoefficientMerge.Poly := [(nat_lit 1112, Int.ofNat (nat_lit 54750910586400))]
theorem block010_data_flat092_step : block010_data_flat092 = (CoefficientMerge.scale (54750910586400 : Int) atom0704Coded) := by decide +kernel
theorem block010_data_flat092_original : block010_data_flat092 = (CoefficientMerge.scale (54750910586400 : Int) atom0704Coded) := by
  rw [block010_data_flat092_step]
def block010_data_flat093 : CoefficientMerge.Poly := [(nat_lit 1124, Int.ofNat (nat_lit 28841978188800))]
theorem block010_data_flat093_step : block010_data_flat093 = (CoefficientMerge.scale (28841978188800 : Int) atom0705Coded) := by decide +kernel
theorem block010_data_flat093_original : block010_data_flat093 = (CoefficientMerge.scale (28841978188800 : Int) atom0705Coded) := by
  rw [block010_data_flat093_step]
def block010_data_flat094 : CoefficientMerge.Poly := [(nat_lit 1112, Int.ofNat (nat_lit 54750910586400)), (nat_lit 1124, Int.ofNat (nat_lit 28841978188800))]
theorem block010_data_flat094_step : block010_data_flat094 = (CoefficientMerge.fastMerge block010_data_flat092 block010_data_flat093) := by decide +kernel
theorem block010_data_flat094_original : block010_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (54750910586400 : Int) atom0704Coded) (CoefficientMerge.scale (28841978188800 : Int) atom0705Coded)) := by
  rw [block010_data_flat094_step, block010_data_flat092_original, block010_data_flat093_original]
def block010_data_flat095 : CoefficientMerge.Poly := [(nat_lit 1111, Int.ofNat (nat_lit 47040248656800)), (nat_lit 1112, Int.ofNat (nat_lit 54750910586400)), (nat_lit 1124, Int.ofNat (nat_lit 28841978188800))]
theorem block010_data_flat095_step : block010_data_flat095 = (CoefficientMerge.fastMerge block010_data_flat091 block010_data_flat094) := by decide +kernel
theorem block010_data_flat095_original : block010_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (47040248656800 : Int) atom0703Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54750910586400 : Int) atom0704Coded) (CoefficientMerge.scale (28841978188800 : Int) atom0705Coded))) := by
  rw [block010_data_flat095_step, block010_data_flat091_original, block010_data_flat094_original]
def block010_data_flat096 : CoefficientMerge.Poly := [(nat_lit 1109, Int.ofNat (nat_lit 52822994918400)), (nat_lit 1110, Int.ofNat (nat_lit 43999571700000)), (nat_lit 1111, Int.ofNat (nat_lit 47040248656800)), (nat_lit 1112, Int.ofNat (nat_lit 54750910586400)), (nat_lit 1124, Int.ofNat (nat_lit 28841978188800))]
theorem block010_data_flat096_step : block010_data_flat096 = (CoefficientMerge.fastMerge block010_data_flat090 block010_data_flat095) := by decide +kernel
theorem block010_data_flat096_original : block010_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52822994918400 : Int) atom0701Coded) (CoefficientMerge.scale (43999571700000 : Int) atom0702Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47040248656800 : Int) atom0703Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54750910586400 : Int) atom0704Coded) (CoefficientMerge.scale (28841978188800 : Int) atom0705Coded)))) := by
  rw [block010_data_flat096_step, block010_data_flat090_original, block010_data_flat095_original]
def block010_data_flat097 : CoefficientMerge.Poly := [(nat_lit 1104, Int.ofNat (nat_lit 45984196294400)), (nat_lit 1105, Int.ofNat (nat_lit 43724731680000)), (nat_lit 1106, Int.ofNat (nat_lit 42342679008000)), (nat_lit 1107, Int.ofNat (nat_lit 49927860864000)), (nat_lit 1108, Int.ofNat (nat_lit 39228832188000)), (nat_lit 1109, Int.ofNat (nat_lit 52822994918400)), (nat_lit 1110, Int.ofNat (nat_lit 43999571700000)), (nat_lit 1111, Int.ofNat (nat_lit 47040248656800)), (nat_lit 1112, Int.ofNat (nat_lit 54750910586400)), (nat_lit 1124, Int.ofNat (nat_lit 28841978188800))]
theorem block010_data_flat097_step : block010_data_flat097 = (CoefficientMerge.fastMerge block010_data_flat087 block010_data_flat096) := by decide +kernel
theorem block010_data_flat097_original : block010_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45984196294400 : Int) atom0696Coded) (CoefficientMerge.scale (43724731680000 : Int) atom0697Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42342679008000 : Int) atom0698Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49927860864000 : Int) atom0699Coded) (CoefficientMerge.scale (39228832188000 : Int) atom0700Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52822994918400 : Int) atom0701Coded) (CoefficientMerge.scale (43999571700000 : Int) atom0702Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47040248656800 : Int) atom0703Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54750910586400 : Int) atom0704Coded) (CoefficientMerge.scale (28841978188800 : Int) atom0705Coded))))) := by
  rw [block010_data_flat097_step, block010_data_flat087_original, block010_data_flat096_original]
def block010_data_flat098 : CoefficientMerge.Poly := [(nat_lit 1125, Int.ofNat (nat_lit 50886380518400))]
theorem block010_data_flat098_step : block010_data_flat098 = (CoefficientMerge.scale (50886380518400 : Int) atom0706Coded) := by decide +kernel
theorem block010_data_flat098_original : block010_data_flat098 = (CoefficientMerge.scale (50886380518400 : Int) atom0706Coded) := by
  rw [block010_data_flat098_step]
def block010_data_flat099 : CoefficientMerge.Poly := [(nat_lit 1126, Int.ofNat (nat_lit 47708769024000))]
theorem block010_data_flat099_step : block010_data_flat099 = (CoefficientMerge.scale (47708769024000 : Int) atom0707Coded) := by decide +kernel
theorem block010_data_flat099_original : block010_data_flat099 = (CoefficientMerge.scale (47708769024000 : Int) atom0707Coded) := by
  rw [block010_data_flat099_step]
def block010_data_flat100 : CoefficientMerge.Poly := [(nat_lit 1125, Int.ofNat (nat_lit 50886380518400)), (nat_lit 1126, Int.ofNat (nat_lit 47708769024000))]
theorem block010_data_flat100_step : block010_data_flat100 = (CoefficientMerge.fastMerge block010_data_flat098 block010_data_flat099) := by decide +kernel
theorem block010_data_flat100_original : block010_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (50886380518400 : Int) atom0706Coded) (CoefficientMerge.scale (47708769024000 : Int) atom0707Coded)) := by
  rw [block010_data_flat100_step, block010_data_flat098_original, block010_data_flat099_original]
def block010_data_flat101 : CoefficientMerge.Poly := [(nat_lit 1127, Int.ofNat (nat_lit 45408569472000))]
theorem block010_data_flat101_step : block010_data_flat101 = (CoefficientMerge.scale (45408569472000 : Int) atom0708Coded) := by decide +kernel
theorem block010_data_flat101_original : block010_data_flat101 = (CoefficientMerge.scale (45408569472000 : Int) atom0708Coded) := by
  rw [block010_data_flat101_step]
def block010_data_flat102 : CoefficientMerge.Poly := [(nat_lit 1128, Int.ofNat (nat_lit 52095180211200))]
theorem block010_data_flat102_step : block010_data_flat102 = (CoefficientMerge.scale (52095180211200 : Int) atom0709Coded) := by decide +kernel
theorem block010_data_flat102_original : block010_data_flat102 = (CoefficientMerge.scale (52095180211200 : Int) atom0709Coded) := by
  rw [block010_data_flat102_step]
def block010_data_flat103 : CoefficientMerge.Poly := [(nat_lit 1129, Int.ofNat (nat_lit 40662744998400))]
theorem block010_data_flat103_step : block010_data_flat103 = (CoefficientMerge.scale (40662744998400 : Int) atom0710Coded) := by decide +kernel
theorem block010_data_flat103_original : block010_data_flat103 = (CoefficientMerge.scale (40662744998400 : Int) atom0710Coded) := by
  rw [block010_data_flat103_step]
def block010_data_flat104 : CoefficientMerge.Poly := [(nat_lit 1128, Int.ofNat (nat_lit 52095180211200)), (nat_lit 1129, Int.ofNat (nat_lit 40662744998400))]
theorem block010_data_flat104_step : block010_data_flat104 = (CoefficientMerge.fastMerge block010_data_flat102 block010_data_flat103) := by decide +kernel
theorem block010_data_flat104_original : block010_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (52095180211200 : Int) atom0709Coded) (CoefficientMerge.scale (40662744998400 : Int) atom0710Coded)) := by
  rw [block010_data_flat104_step, block010_data_flat102_original, block010_data_flat103_original]
def block010_data_flat105 : CoefficientMerge.Poly := [(nat_lit 1127, Int.ofNat (nat_lit 45408569472000)), (nat_lit 1128, Int.ofNat (nat_lit 52095180211200)), (nat_lit 1129, Int.ofNat (nat_lit 40662744998400))]
theorem block010_data_flat105_step : block010_data_flat105 = (CoefficientMerge.fastMerge block010_data_flat101 block010_data_flat104) := by decide +kernel
theorem block010_data_flat105_original : block010_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (45408569472000 : Int) atom0708Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52095180211200 : Int) atom0709Coded) (CoefficientMerge.scale (40662744998400 : Int) atom0710Coded))) := by
  rw [block010_data_flat105_step, block010_data_flat101_original, block010_data_flat104_original]
def block010_data_flat106 : CoefficientMerge.Poly := [(nat_lit 1125, Int.ofNat (nat_lit 50886380518400)), (nat_lit 1126, Int.ofNat (nat_lit 47708769024000)), (nat_lit 1127, Int.ofNat (nat_lit 45408569472000)), (nat_lit 1128, Int.ofNat (nat_lit 52095180211200)), (nat_lit 1129, Int.ofNat (nat_lit 40662744998400))]
theorem block010_data_flat106_step : block010_data_flat106 = (CoefficientMerge.fastMerge block010_data_flat100 block010_data_flat105) := by decide +kernel
theorem block010_data_flat106_original : block010_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50886380518400 : Int) atom0706Coded) (CoefficientMerge.scale (47708769024000 : Int) atom0707Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45408569472000 : Int) atom0708Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52095180211200 : Int) atom0709Coded) (CoefficientMerge.scale (40662744998400 : Int) atom0710Coded)))) := by
  rw [block010_data_flat106_step, block010_data_flat100_original, block010_data_flat105_original]
def block010_data_flat107 : CoefficientMerge.Poly := [(nat_lit 1130, Int.ofNat (nat_lit 55999309363200))]
theorem block010_data_flat107_step : block010_data_flat107 = (CoefficientMerge.scale (55999309363200 : Int) atom0711Coded) := by decide +kernel
theorem block010_data_flat107_original : block010_data_flat107 = (CoefficientMerge.scale (55999309363200 : Int) atom0711Coded) := by
  rw [block010_data_flat107_step]
def block010_data_flat108 : CoefficientMerge.Poly := [(nat_lit 1131, Int.ofNat (nat_lit 44005822963200))]
theorem block010_data_flat108_step : block010_data_flat108 = (CoefficientMerge.scale (44005822963200 : Int) atom0712Coded) := by decide +kernel
theorem block010_data_flat108_original : block010_data_flat108 = (CoefficientMerge.scale (44005822963200 : Int) atom0712Coded) := by
  rw [block010_data_flat108_step]
def block010_data_flat109 : CoefficientMerge.Poly := [(nat_lit 1130, Int.ofNat (nat_lit 55999309363200)), (nat_lit 1131, Int.ofNat (nat_lit 44005822963200))]
theorem block010_data_flat109_step : block010_data_flat109 = (CoefficientMerge.fastMerge block010_data_flat107 block010_data_flat108) := by decide +kernel
theorem block010_data_flat109_original : block010_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (55999309363200 : Int) atom0711Coded) (CoefficientMerge.scale (44005822963200 : Int) atom0712Coded)) := by
  rw [block010_data_flat109_step, block010_data_flat107_original, block010_data_flat108_original]
def block010_data_flat110 : CoefficientMerge.Poly := [(nat_lit 1132, Int.ofNat (nat_lit 46400774515200))]
theorem block010_data_flat110_step : block010_data_flat110 = (CoefficientMerge.scale (46400774515200 : Int) atom0713Coded) := by decide +kernel
theorem block010_data_flat110_original : block010_data_flat110 = (CoefficientMerge.scale (46400774515200 : Int) atom0713Coded) := by
  rw [block010_data_flat110_step]
def block010_data_flat111 : CoefficientMerge.Poly := [(nat_lit 1133, Int.ofNat (nat_lit 53465711040000))]
theorem block010_data_flat111_step : block010_data_flat111 = (CoefficientMerge.scale (53465711040000 : Int) atom0714Coded) := by decide +kernel
theorem block010_data_flat111_original : block010_data_flat111 = (CoefficientMerge.scale (53465711040000 : Int) atom0714Coded) := by
  rw [block010_data_flat111_step]
def block010_data_flat112 : CoefficientMerge.Poly := [(nat_lit 1146, Int.ofNat (nat_lit 27765907097600))]
theorem block010_data_flat112_step : block010_data_flat112 = (CoefficientMerge.scale (27765907097600 : Int) atom0715Coded) := by decide +kernel
theorem block010_data_flat112_original : block010_data_flat112 = (CoefficientMerge.scale (27765907097600 : Int) atom0715Coded) := by
  rw [block010_data_flat112_step]
def block010_data_flat113 : CoefficientMerge.Poly := [(nat_lit 1133, Int.ofNat (nat_lit 53465711040000)), (nat_lit 1146, Int.ofNat (nat_lit 27765907097600))]
theorem block010_data_flat113_step : block010_data_flat113 = (CoefficientMerge.fastMerge block010_data_flat111 block010_data_flat112) := by decide +kernel
theorem block010_data_flat113_original : block010_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (53465711040000 : Int) atom0714Coded) (CoefficientMerge.scale (27765907097600 : Int) atom0715Coded)) := by
  rw [block010_data_flat113_step, block010_data_flat111_original, block010_data_flat112_original]
def block010_data_flat114 : CoefficientMerge.Poly := [(nat_lit 1132, Int.ofNat (nat_lit 46400774515200)), (nat_lit 1133, Int.ofNat (nat_lit 53465711040000)), (nat_lit 1146, Int.ofNat (nat_lit 27765907097600))]
theorem block010_data_flat114_step : block010_data_flat114 = (CoefficientMerge.fastMerge block010_data_flat110 block010_data_flat113) := by decide +kernel
theorem block010_data_flat114_original : block010_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46400774515200 : Int) atom0713Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53465711040000 : Int) atom0714Coded) (CoefficientMerge.scale (27765907097600 : Int) atom0715Coded))) := by
  rw [block010_data_flat114_step, block010_data_flat110_original, block010_data_flat113_original]
def block010_data_flat115 : CoefficientMerge.Poly := [(nat_lit 1130, Int.ofNat (nat_lit 55999309363200)), (nat_lit 1131, Int.ofNat (nat_lit 44005822963200)), (nat_lit 1132, Int.ofNat (nat_lit 46400774515200)), (nat_lit 1133, Int.ofNat (nat_lit 53465711040000)), (nat_lit 1146, Int.ofNat (nat_lit 27765907097600))]
theorem block010_data_flat115_step : block010_data_flat115 = (CoefficientMerge.fastMerge block010_data_flat109 block010_data_flat114) := by decide +kernel
theorem block010_data_flat115_original : block010_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55999309363200 : Int) atom0711Coded) (CoefficientMerge.scale (44005822963200 : Int) atom0712Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46400774515200 : Int) atom0713Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53465711040000 : Int) atom0714Coded) (CoefficientMerge.scale (27765907097600 : Int) atom0715Coded)))) := by
  rw [block010_data_flat115_step, block010_data_flat109_original, block010_data_flat114_original]
def block010_data_flat116 : CoefficientMerge.Poly := [(nat_lit 1125, Int.ofNat (nat_lit 50886380518400)), (nat_lit 1126, Int.ofNat (nat_lit 47708769024000)), (nat_lit 1127, Int.ofNat (nat_lit 45408569472000)), (nat_lit 1128, Int.ofNat (nat_lit 52095180211200)), (nat_lit 1129, Int.ofNat (nat_lit 40662744998400)), (nat_lit 1130, Int.ofNat (nat_lit 55999309363200)), (nat_lit 1131, Int.ofNat (nat_lit 44005822963200)), (nat_lit 1132, Int.ofNat (nat_lit 46400774515200)), (nat_lit 1133, Int.ofNat (nat_lit 53465711040000)), (nat_lit 1146, Int.ofNat (nat_lit 27765907097600))]
theorem block010_data_flat116_step : block010_data_flat116 = (CoefficientMerge.fastMerge block010_data_flat106 block010_data_flat115) := by decide +kernel
theorem block010_data_flat116_original : block010_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50886380518400 : Int) atom0706Coded) (CoefficientMerge.scale (47708769024000 : Int) atom0707Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45408569472000 : Int) atom0708Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52095180211200 : Int) atom0709Coded) (CoefficientMerge.scale (40662744998400 : Int) atom0710Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55999309363200 : Int) atom0711Coded) (CoefficientMerge.scale (44005822963200 : Int) atom0712Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46400774515200 : Int) atom0713Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53465711040000 : Int) atom0714Coded) (CoefficientMerge.scale (27765907097600 : Int) atom0715Coded))))) := by
  rw [block010_data_flat116_step, block010_data_flat106_original, block010_data_flat115_original]
def block010_data_flat117 : CoefficientMerge.Poly := [(nat_lit 1104, Int.ofNat (nat_lit 45984196294400)), (nat_lit 1105, Int.ofNat (nat_lit 43724731680000)), (nat_lit 1106, Int.ofNat (nat_lit 42342679008000)), (nat_lit 1107, Int.ofNat (nat_lit 49927860864000)), (nat_lit 1108, Int.ofNat (nat_lit 39228832188000)), (nat_lit 1109, Int.ofNat (nat_lit 52822994918400)), (nat_lit 1110, Int.ofNat (nat_lit 43999571700000)), (nat_lit 1111, Int.ofNat (nat_lit 47040248656800)), (nat_lit 1112, Int.ofNat (nat_lit 54750910586400)), (nat_lit 1124, Int.ofNat (nat_lit 28841978188800)), (nat_lit 1125, Int.ofNat (nat_lit 50886380518400)), (nat_lit 1126, Int.ofNat (nat_lit 47708769024000)), (nat_lit 1127, Int.ofNat (nat_lit 45408569472000)), (nat_lit 1128, Int.ofNat (nat_lit 52095180211200)), (nat_lit 1129, Int.ofNat (nat_lit 40662744998400)), (nat_lit 1130, Int.ofNat (nat_lit 55999309363200)), (nat_lit 1131, Int.ofNat (nat_lit 44005822963200)), (nat_lit 1132, Int.ofNat (nat_lit 46400774515200)), (nat_lit 1133, Int.ofNat (nat_lit 53465711040000)), (nat_lit 1146, Int.ofNat (nat_lit 27765907097600))]
theorem block010_data_flat117_step : block010_data_flat117 = (CoefficientMerge.fastMerge block010_data_flat097 block010_data_flat116) := by decide +kernel
theorem block010_data_flat117_original : block010_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45984196294400 : Int) atom0696Coded) (CoefficientMerge.scale (43724731680000 : Int) atom0697Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42342679008000 : Int) atom0698Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49927860864000 : Int) atom0699Coded) (CoefficientMerge.scale (39228832188000 : Int) atom0700Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52822994918400 : Int) atom0701Coded) (CoefficientMerge.scale (43999571700000 : Int) atom0702Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47040248656800 : Int) atom0703Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54750910586400 : Int) atom0704Coded) (CoefficientMerge.scale (28841978188800 : Int) atom0705Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50886380518400 : Int) atom0706Coded) (CoefficientMerge.scale (47708769024000 : Int) atom0707Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45408569472000 : Int) atom0708Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52095180211200 : Int) atom0709Coded) (CoefficientMerge.scale (40662744998400 : Int) atom0710Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55999309363200 : Int) atom0711Coded) (CoefficientMerge.scale (44005822963200 : Int) atom0712Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46400774515200 : Int) atom0713Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53465711040000 : Int) atom0714Coded) (CoefficientMerge.scale (27765907097600 : Int) atom0715Coded)))))) := by
  rw [block010_data_flat117_step, block010_data_flat097_original, block010_data_flat116_original]
def block010_data_flat118 : CoefficientMerge.Poly := [(nat_lit 1147, Int.ofNat (nat_lit 50840710054400))]
theorem block010_data_flat118_step : block010_data_flat118 = (CoefficientMerge.scale (50840710054400 : Int) atom0716Coded) := by decide +kernel
theorem block010_data_flat118_original : block010_data_flat118 = (CoefficientMerge.scale (50840710054400 : Int) atom0716Coded) := by
  rw [block010_data_flat118_step]
def block010_data_flat119 : CoefficientMerge.Poly := [(nat_lit 1148, Int.ofNat (nat_lit 47454197772800))]
theorem block010_data_flat119_step : block010_data_flat119 = (CoefficientMerge.scale (47454197772800 : Int) atom0717Coded) := by decide +kernel
theorem block010_data_flat119_original : block010_data_flat119 = (CoefficientMerge.scale (47454197772800 : Int) atom0717Coded) := by
  rw [block010_data_flat119_step]
def block010_data_flat120 : CoefficientMerge.Poly := [(nat_lit 1147, Int.ofNat (nat_lit 50840710054400)), (nat_lit 1148, Int.ofNat (nat_lit 47454197772800))]
theorem block010_data_flat120_step : block010_data_flat120 = (CoefficientMerge.fastMerge block010_data_flat118 block010_data_flat119) := by decide +kernel
theorem block010_data_flat120_original : block010_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (50840710054400 : Int) atom0716Coded) (CoefficientMerge.scale (47454197772800 : Int) atom0717Coded)) := by
  rw [block010_data_flat120_step, block010_data_flat118_original, block010_data_flat119_original]
def block010_data_flat121 : CoefficientMerge.Poly := [(nat_lit 1149, Int.ofNat (nat_lit 50163393280000))]
theorem block010_data_flat121_step : block010_data_flat121 = (CoefficientMerge.scale (50163393280000 : Int) atom0718Coded) := by decide +kernel
theorem block010_data_flat121_original : block010_data_flat121 = (CoefficientMerge.scale (50163393280000 : Int) atom0718Coded) := by
  rw [block010_data_flat121_step]
def block010_data_flat122 : CoefficientMerge.Poly := [(nat_lit 1150, Int.ofNat (nat_lit 40943623616000))]
theorem block010_data_flat122_step : block010_data_flat122 = (CoefficientMerge.scale (40943623616000 : Int) atom0719Coded) := by decide +kernel
theorem block010_data_flat122_original : block010_data_flat122 = (CoefficientMerge.scale (40943623616000 : Int) atom0719Coded) := by
  rw [block010_data_flat122_step]
def block010_data_flat123 : CoefficientMerge.Poly := [(nat_lit 1151, Int.ofNat (nat_lit 55076517529600))]
theorem block010_data_flat123_step : block010_data_flat123 = (CoefficientMerge.scale (55076517529600 : Int) atom0720Coded) := by decide +kernel
theorem block010_data_flat123_original : block010_data_flat123 = (CoefficientMerge.scale (55076517529600 : Int) atom0720Coded) := by
  rw [block010_data_flat123_step]
def block010_data_flat124 : CoefficientMerge.Poly := [(nat_lit 1150, Int.ofNat (nat_lit 40943623616000)), (nat_lit 1151, Int.ofNat (nat_lit 55076517529600))]
theorem block010_data_flat124_step : block010_data_flat124 = (CoefficientMerge.fastMerge block010_data_flat122 block010_data_flat123) := by decide +kernel
theorem block010_data_flat124_original : block010_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40943623616000 : Int) atom0719Coded) (CoefficientMerge.scale (55076517529600 : Int) atom0720Coded)) := by
  rw [block010_data_flat124_step, block010_data_flat122_original, block010_data_flat123_original]
def block010_data_flat125 : CoefficientMerge.Poly := [(nat_lit 1149, Int.ofNat (nat_lit 50163393280000)), (nat_lit 1150, Int.ofNat (nat_lit 40943623616000)), (nat_lit 1151, Int.ofNat (nat_lit 55076517529600))]
theorem block010_data_flat125_step : block010_data_flat125 = (CoefficientMerge.fastMerge block010_data_flat121 block010_data_flat124) := by decide +kernel
theorem block010_data_flat125_original : block010_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (50163393280000 : Int) atom0718Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40943623616000 : Int) atom0719Coded) (CoefficientMerge.scale (55076517529600 : Int) atom0720Coded))) := by
  rw [block010_data_flat125_step, block010_data_flat121_original, block010_data_flat124_original]
def block010_data_flat126 : CoefficientMerge.Poly := [(nat_lit 1147, Int.ofNat (nat_lit 50840710054400)), (nat_lit 1148, Int.ofNat (nat_lit 47454197772800)), (nat_lit 1149, Int.ofNat (nat_lit 50163393280000)), (nat_lit 1150, Int.ofNat (nat_lit 40943623616000)), (nat_lit 1151, Int.ofNat (nat_lit 55076517529600))]
theorem block010_data_flat126_step : block010_data_flat126 = (CoefficientMerge.fastMerge block010_data_flat120 block010_data_flat125) := by decide +kernel
theorem block010_data_flat126_original : block010_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50840710054400 : Int) atom0716Coded) (CoefficientMerge.scale (47454197772800 : Int) atom0717Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50163393280000 : Int) atom0718Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40943623616000 : Int) atom0719Coded) (CoefficientMerge.scale (55076517529600 : Int) atom0720Coded)))) := by
  rw [block010_data_flat126_step, block010_data_flat120_original, block010_data_flat125_original]
def block010_data_flat127 : CoefficientMerge.Poly := [(nat_lit 1152, Int.ofNat (nat_lit 43587528678400))]
theorem block010_data_flat127_step : block010_data_flat127 = (CoefficientMerge.scale (43587528678400 : Int) atom0721Coded) := by decide +kernel
theorem block010_data_flat127_original : block010_data_flat127 = (CoefficientMerge.scale (43587528678400 : Int) atom0721Coded) := by
  rw [block010_data_flat127_step]
def block010_data_flat128 : CoefficientMerge.Poly := [(nat_lit 1153, Int.ofNat (nat_lit 44782300864000))]
theorem block010_data_flat128_step : block010_data_flat128 = (CoefficientMerge.scale (44782300864000 : Int) atom0722Coded) := by decide +kernel
theorem block010_data_flat128_original : block010_data_flat128 = (CoefficientMerge.scale (44782300864000 : Int) atom0722Coded) := by
  rw [block010_data_flat128_step]
def block010_data_flat129 : CoefficientMerge.Poly := [(nat_lit 1152, Int.ofNat (nat_lit 43587528678400)), (nat_lit 1153, Int.ofNat (nat_lit 44782300864000))]
theorem block010_data_flat129_step : block010_data_flat129 = (CoefficientMerge.fastMerge block010_data_flat127 block010_data_flat128) := by decide +kernel
theorem block010_data_flat129_original : block010_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (43587528678400 : Int) atom0721Coded) (CoefficientMerge.scale (44782300864000 : Int) atom0722Coded)) := by
  rw [block010_data_flat129_step, block010_data_flat127_original, block010_data_flat128_original]
def block010_data_flat130 : CoefficientMerge.Poly := [(nat_lit 1154, Int.ofNat (nat_lit 51304759027200))]
theorem block010_data_flat130_step : block010_data_flat130 = (CoefficientMerge.scale (51304759027200 : Int) atom0723Coded) := by decide +kernel
theorem block010_data_flat130_original : block010_data_flat130 = (CoefficientMerge.scale (51304759027200 : Int) atom0723Coded) := by
  rw [block010_data_flat130_step]
def block010_data_flat131 : CoefficientMerge.Poly := [(nat_lit 1168, Int.ofNat (nat_lit 28504801843200))]
theorem block010_data_flat131_step : block010_data_flat131 = (CoefficientMerge.scale (28504801843200 : Int) atom0724Coded) := by decide +kernel
theorem block010_data_flat131_original : block010_data_flat131 = (CoefficientMerge.scale (28504801843200 : Int) atom0724Coded) := by
  rw [block010_data_flat131_step]
def block010_data_flat132 : CoefficientMerge.Poly := [(nat_lit 1169, Int.ofNat (nat_lit 51198079104000))]
theorem block010_data_flat132_step : block010_data_flat132 = (CoefficientMerge.scale (51198079104000 : Int) atom0725Coded) := by decide +kernel
theorem block010_data_flat132_original : block010_data_flat132 = (CoefficientMerge.scale (51198079104000 : Int) atom0725Coded) := by
  rw [block010_data_flat132_step]
def block010_data_flat133 : CoefficientMerge.Poly := [(nat_lit 1168, Int.ofNat (nat_lit 28504801843200)), (nat_lit 1169, Int.ofNat (nat_lit 51198079104000))]
theorem block010_data_flat133_step : block010_data_flat133 = (CoefficientMerge.fastMerge block010_data_flat131 block010_data_flat132) := by decide +kernel
theorem block010_data_flat133_original : block010_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28504801843200 : Int) atom0724Coded) (CoefficientMerge.scale (51198079104000 : Int) atom0725Coded)) := by
  rw [block010_data_flat133_step, block010_data_flat131_original, block010_data_flat132_original]
def block010_data_flat134 : CoefficientMerge.Poly := [(nat_lit 1154, Int.ofNat (nat_lit 51304759027200)), (nat_lit 1168, Int.ofNat (nat_lit 28504801843200)), (nat_lit 1169, Int.ofNat (nat_lit 51198079104000))]
theorem block010_data_flat134_step : block010_data_flat134 = (CoefficientMerge.fastMerge block010_data_flat130 block010_data_flat133) := by decide +kernel
theorem block010_data_flat134_original : block010_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (51304759027200 : Int) atom0723Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28504801843200 : Int) atom0724Coded) (CoefficientMerge.scale (51198079104000 : Int) atom0725Coded))) := by
  rw [block010_data_flat134_step, block010_data_flat130_original, block010_data_flat133_original]
def block010_data_flat135 : CoefficientMerge.Poly := [(nat_lit 1152, Int.ofNat (nat_lit 43587528678400)), (nat_lit 1153, Int.ofNat (nat_lit 44782300864000)), (nat_lit 1154, Int.ofNat (nat_lit 51304759027200)), (nat_lit 1168, Int.ofNat (nat_lit 28504801843200)), (nat_lit 1169, Int.ofNat (nat_lit 51198079104000))]
theorem block010_data_flat135_step : block010_data_flat135 = (CoefficientMerge.fastMerge block010_data_flat129 block010_data_flat134) := by decide +kernel
theorem block010_data_flat135_original : block010_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43587528678400 : Int) atom0721Coded) (CoefficientMerge.scale (44782300864000 : Int) atom0722Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51304759027200 : Int) atom0723Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28504801843200 : Int) atom0724Coded) (CoefficientMerge.scale (51198079104000 : Int) atom0725Coded)))) := by
  rw [block010_data_flat135_step, block010_data_flat129_original, block010_data_flat134_original]
def block010_data_flat136 : CoefficientMerge.Poly := [(nat_lit 1147, Int.ofNat (nat_lit 50840710054400)), (nat_lit 1148, Int.ofNat (nat_lit 47454197772800)), (nat_lit 1149, Int.ofNat (nat_lit 50163393280000)), (nat_lit 1150, Int.ofNat (nat_lit 40943623616000)), (nat_lit 1151, Int.ofNat (nat_lit 55076517529600)), (nat_lit 1152, Int.ofNat (nat_lit 43587528678400)), (nat_lit 1153, Int.ofNat (nat_lit 44782300864000)), (nat_lit 1154, Int.ofNat (nat_lit 51304759027200)), (nat_lit 1168, Int.ofNat (nat_lit 28504801843200)), (nat_lit 1169, Int.ofNat (nat_lit 51198079104000))]
theorem block010_data_flat136_step : block010_data_flat136 = (CoefficientMerge.fastMerge block010_data_flat126 block010_data_flat135) := by decide +kernel
theorem block010_data_flat136_original : block010_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50840710054400 : Int) atom0716Coded) (CoefficientMerge.scale (47454197772800 : Int) atom0717Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50163393280000 : Int) atom0718Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40943623616000 : Int) atom0719Coded) (CoefficientMerge.scale (55076517529600 : Int) atom0720Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43587528678400 : Int) atom0721Coded) (CoefficientMerge.scale (44782300864000 : Int) atom0722Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51304759027200 : Int) atom0723Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28504801843200 : Int) atom0724Coded) (CoefficientMerge.scale (51198079104000 : Int) atom0725Coded))))) := by
  rw [block010_data_flat136_step, block010_data_flat126_original, block010_data_flat135_original]
def block010_data_flat137 : CoefficientMerge.Poly := [(nat_lit 1170, Int.ofNat (nat_lit 52516793448000))]
theorem block010_data_flat137_step : block010_data_flat137 = (CoefficientMerge.scale (52516793448000 : Int) atom0726Coded) := by decide +kernel
theorem block010_data_flat137_original : block010_data_flat137 = (CoefficientMerge.scale (52516793448000 : Int) atom0726Coded) := by
  rw [block010_data_flat137_step]
def block010_data_flat138 : CoefficientMerge.Poly := [(nat_lit 1171, Int.ofNat (nat_lit 41770540036800))]
theorem block010_data_flat138_step : block010_data_flat138 = (CoefficientMerge.scale (41770540036800 : Int) atom0727Coded) := by decide +kernel
theorem block010_data_flat138_original : block010_data_flat138 = (CoefficientMerge.scale (41770540036800 : Int) atom0727Coded) := by
  rw [block010_data_flat138_step]
def block010_data_flat139 : CoefficientMerge.Poly := [(nat_lit 1170, Int.ofNat (nat_lit 52516793448000)), (nat_lit 1171, Int.ofNat (nat_lit 41770540036800))]
theorem block010_data_flat139_step : block010_data_flat139 = (CoefficientMerge.fastMerge block010_data_flat137 block010_data_flat138) := by decide +kernel
theorem block010_data_flat139_original : block010_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (52516793448000 : Int) atom0726Coded) (CoefficientMerge.scale (41770540036800 : Int) atom0727Coded)) := by
  rw [block010_data_flat139_step, block010_data_flat137_original, block010_data_flat138_original]
def block010_data_flat140 : CoefficientMerge.Poly := [(nat_lit 1172, Int.ofNat (nat_lit 57639883392000))]
theorem block010_data_flat140_step : block010_data_flat140 = (CoefficientMerge.scale (57639883392000 : Int) atom0728Coded) := by decide +kernel
theorem block010_data_flat140_original : block010_data_flat140 = (CoefficientMerge.scale (57639883392000 : Int) atom0728Coded) := by
  rw [block010_data_flat140_step]
def block010_data_flat141 : CoefficientMerge.Poly := [(nat_lit 1173, Int.ofNat (nat_lit 46655392089600))]
theorem block010_data_flat141_step : block010_data_flat141 = (CoefficientMerge.scale (46655392089600 : Int) atom0729Coded) := by decide +kernel
theorem block010_data_flat141_original : block010_data_flat141 = (CoefficientMerge.scale (46655392089600 : Int) atom0729Coded) := by
  rw [block010_data_flat141_step]
def block010_data_flat142 : CoefficientMerge.Poly := [(nat_lit 1174, Int.ofNat (nat_lit 40485755707200))]
theorem block010_data_flat142_step : block010_data_flat142 = (CoefficientMerge.scale (40485755707200 : Int) atom0730Coded) := by decide +kernel
theorem block010_data_flat142_original : block010_data_flat142 = (CoefficientMerge.scale (40485755707200 : Int) atom0730Coded) := by
  rw [block010_data_flat142_step]
def block010_data_flat143 : CoefficientMerge.Poly := [(nat_lit 1173, Int.ofNat (nat_lit 46655392089600)), (nat_lit 1174, Int.ofNat (nat_lit 40485755707200))]
theorem block010_data_flat143_step : block010_data_flat143 = (CoefficientMerge.fastMerge block010_data_flat141 block010_data_flat142) := by decide +kernel
theorem block010_data_flat143_original : block010_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46655392089600 : Int) atom0729Coded) (CoefficientMerge.scale (40485755707200 : Int) atom0730Coded)) := by
  rw [block010_data_flat143_step, block010_data_flat141_original, block010_data_flat142_original]
def block010_data_flat144 : CoefficientMerge.Poly := [(nat_lit 1172, Int.ofNat (nat_lit 57639883392000)), (nat_lit 1173, Int.ofNat (nat_lit 46655392089600)), (nat_lit 1174, Int.ofNat (nat_lit 40485755707200))]
theorem block010_data_flat144_step : block010_data_flat144 = (CoefficientMerge.fastMerge block010_data_flat140 block010_data_flat143) := by decide +kernel
theorem block010_data_flat144_original : block010_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (57639883392000 : Int) atom0728Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46655392089600 : Int) atom0729Coded) (CoefficientMerge.scale (40485755707200 : Int) atom0730Coded))) := by
  rw [block010_data_flat144_step, block010_data_flat140_original, block010_data_flat143_original]
def block010_data_flat145 : CoefficientMerge.Poly := [(nat_lit 1170, Int.ofNat (nat_lit 52516793448000)), (nat_lit 1171, Int.ofNat (nat_lit 41770540036800)), (nat_lit 1172, Int.ofNat (nat_lit 57639883392000)), (nat_lit 1173, Int.ofNat (nat_lit 46655392089600)), (nat_lit 1174, Int.ofNat (nat_lit 40485755707200))]
theorem block010_data_flat145_step : block010_data_flat145 = (CoefficientMerge.fastMerge block010_data_flat139 block010_data_flat144) := by decide +kernel
theorem block010_data_flat145_original : block010_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52516793448000 : Int) atom0726Coded) (CoefficientMerge.scale (41770540036800 : Int) atom0727Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57639883392000 : Int) atom0728Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46655392089600 : Int) atom0729Coded) (CoefficientMerge.scale (40485755707200 : Int) atom0730Coded)))) := by
  rw [block010_data_flat145_step, block010_data_flat139_original, block010_data_flat144_original]
def block010_data_flat146 : CoefficientMerge.Poly := [(nat_lit 1175, Int.ofNat (nat_lit 52168139251200))]
theorem block010_data_flat146_step : block010_data_flat146 = (CoefficientMerge.scale (52168139251200 : Int) atom0731Coded) := by decide +kernel
theorem block010_data_flat146_original : block010_data_flat146 = (CoefficientMerge.scale (52168139251200 : Int) atom0731Coded) := by
  rw [block010_data_flat146_step]
def block010_data_flat147 : CoefficientMerge.Poly := [(nat_lit 1190, Int.ofNat (nat_lit 30391628198400))]
theorem block010_data_flat147_step : block010_data_flat147 = (CoefficientMerge.scale (30391628198400 : Int) atom0732Coded) := by decide +kernel
theorem block010_data_flat147_original : block010_data_flat147 = (CoefficientMerge.scale (30391628198400 : Int) atom0732Coded) := by
  rw [block010_data_flat147_step]
def block010_data_flat148 : CoefficientMerge.Poly := [(nat_lit 1175, Int.ofNat (nat_lit 52168139251200)), (nat_lit 1190, Int.ofNat (nat_lit 30391628198400))]
theorem block010_data_flat148_step : block010_data_flat148 = (CoefficientMerge.fastMerge block010_data_flat146 block010_data_flat147) := by decide +kernel
theorem block010_data_flat148_original : block010_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (52168139251200 : Int) atom0731Coded) (CoefficientMerge.scale (30391628198400 : Int) atom0732Coded)) := by
  rw [block010_data_flat148_step, block010_data_flat146_original, block010_data_flat147_original]
def block010_data_flat149 : CoefficientMerge.Poly := [(nat_lit 1191, Int.ofNat (nat_lit 55197057484800))]
theorem block010_data_flat149_step : block010_data_flat149 = (CoefficientMerge.scale (55197057484800 : Int) atom0733Coded) := by decide +kernel
theorem block010_data_flat149_original : block010_data_flat149 = (CoefficientMerge.scale (55197057484800 : Int) atom0733Coded) := by
  rw [block010_data_flat149_step]
def block010_data_flat150 : CoefficientMerge.Poly := [(nat_lit 1192, Int.ofNat (nat_lit 42478307020800))]
theorem block010_data_flat150_step : block010_data_flat150 = (CoefficientMerge.scale (42478307020800 : Int) atom0734Coded) := by decide +kernel
theorem block010_data_flat150_original : block010_data_flat150 = (CoefficientMerge.scale (42478307020800 : Int) atom0734Coded) := by
  rw [block010_data_flat150_step]
def block010_data_flat151 : CoefficientMerge.Poly := [(nat_lit 1193, Int.ofNat (nat_lit 61958073139200))]
theorem block010_data_flat151_step : block010_data_flat151 = (CoefficientMerge.scale (61958073139200 : Int) atom0735Coded) := by decide +kernel
theorem block010_data_flat151_original : block010_data_flat151 = (CoefficientMerge.scale (61958073139200 : Int) atom0735Coded) := by
  rw [block010_data_flat151_step]
def block010_data_flat152 : CoefficientMerge.Poly := [(nat_lit 1192, Int.ofNat (nat_lit 42478307020800)), (nat_lit 1193, Int.ofNat (nat_lit 61958073139200))]
theorem block010_data_flat152_step : block010_data_flat152 = (CoefficientMerge.fastMerge block010_data_flat150 block010_data_flat151) := by decide +kernel
theorem block010_data_flat152_original : block010_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (42478307020800 : Int) atom0734Coded) (CoefficientMerge.scale (61958073139200 : Int) atom0735Coded)) := by
  rw [block010_data_flat152_step, block010_data_flat150_original, block010_data_flat151_original]
def block010_data_flat153 : CoefficientMerge.Poly := [(nat_lit 1191, Int.ofNat (nat_lit 55197057484800)), (nat_lit 1192, Int.ofNat (nat_lit 42478307020800)), (nat_lit 1193, Int.ofNat (nat_lit 61958073139200))]
theorem block010_data_flat153_step : block010_data_flat153 = (CoefficientMerge.fastMerge block010_data_flat149 block010_data_flat152) := by decide +kernel
theorem block010_data_flat153_original : block010_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (55197057484800 : Int) atom0733Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42478307020800 : Int) atom0734Coded) (CoefficientMerge.scale (61958073139200 : Int) atom0735Coded))) := by
  rw [block010_data_flat153_step, block010_data_flat149_original, block010_data_flat152_original]
def block010_data_flat154 : CoefficientMerge.Poly := [(nat_lit 1175, Int.ofNat (nat_lit 52168139251200)), (nat_lit 1190, Int.ofNat (nat_lit 30391628198400)), (nat_lit 1191, Int.ofNat (nat_lit 55197057484800)), (nat_lit 1192, Int.ofNat (nat_lit 42478307020800)), (nat_lit 1193, Int.ofNat (nat_lit 61958073139200))]
theorem block010_data_flat154_step : block010_data_flat154 = (CoefficientMerge.fastMerge block010_data_flat148 block010_data_flat153) := by decide +kernel
theorem block010_data_flat154_original : block010_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52168139251200 : Int) atom0731Coded) (CoefficientMerge.scale (30391628198400 : Int) atom0732Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55197057484800 : Int) atom0733Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42478307020800 : Int) atom0734Coded) (CoefficientMerge.scale (61958073139200 : Int) atom0735Coded)))) := by
  rw [block010_data_flat154_step, block010_data_flat148_original, block010_data_flat153_original]
def block010_data_flat155 : CoefficientMerge.Poly := [(nat_lit 1170, Int.ofNat (nat_lit 52516793448000)), (nat_lit 1171, Int.ofNat (nat_lit 41770540036800)), (nat_lit 1172, Int.ofNat (nat_lit 57639883392000)), (nat_lit 1173, Int.ofNat (nat_lit 46655392089600)), (nat_lit 1174, Int.ofNat (nat_lit 40485755707200)), (nat_lit 1175, Int.ofNat (nat_lit 52168139251200)), (nat_lit 1190, Int.ofNat (nat_lit 30391628198400)), (nat_lit 1191, Int.ofNat (nat_lit 55197057484800)), (nat_lit 1192, Int.ofNat (nat_lit 42478307020800)), (nat_lit 1193, Int.ofNat (nat_lit 61958073139200))]
theorem block010_data_flat155_step : block010_data_flat155 = (CoefficientMerge.fastMerge block010_data_flat145 block010_data_flat154) := by decide +kernel
theorem block010_data_flat155_original : block010_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52516793448000 : Int) atom0726Coded) (CoefficientMerge.scale (41770540036800 : Int) atom0727Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57639883392000 : Int) atom0728Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46655392089600 : Int) atom0729Coded) (CoefficientMerge.scale (40485755707200 : Int) atom0730Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52168139251200 : Int) atom0731Coded) (CoefficientMerge.scale (30391628198400 : Int) atom0732Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55197057484800 : Int) atom0733Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42478307020800 : Int) atom0734Coded) (CoefficientMerge.scale (61958073139200 : Int) atom0735Coded))))) := by
  rw [block010_data_flat155_step, block010_data_flat145_original, block010_data_flat154_original]
def block010_data_flat156 : CoefficientMerge.Poly := [(nat_lit 1147, Int.ofNat (nat_lit 50840710054400)), (nat_lit 1148, Int.ofNat (nat_lit 47454197772800)), (nat_lit 1149, Int.ofNat (nat_lit 50163393280000)), (nat_lit 1150, Int.ofNat (nat_lit 40943623616000)), (nat_lit 1151, Int.ofNat (nat_lit 55076517529600)), (nat_lit 1152, Int.ofNat (nat_lit 43587528678400)), (nat_lit 1153, Int.ofNat (nat_lit 44782300864000)), (nat_lit 1154, Int.ofNat (nat_lit 51304759027200)), (nat_lit 1168, Int.ofNat (nat_lit 28504801843200)), (nat_lit 1169, Int.ofNat (nat_lit 51198079104000)), (nat_lit 1170, Int.ofNat (nat_lit 52516793448000)), (nat_lit 1171, Int.ofNat (nat_lit 41770540036800)), (nat_lit 1172, Int.ofNat (nat_lit 57639883392000)), (nat_lit 1173, Int.ofNat (nat_lit 46655392089600)), (nat_lit 1174, Int.ofNat (nat_lit 40485755707200)), (nat_lit 1175, Int.ofNat (nat_lit 52168139251200)), (nat_lit 1190, Int.ofNat (nat_lit 30391628198400)), (nat_lit 1191, Int.ofNat (nat_lit 55197057484800)), (nat_lit 1192, Int.ofNat (nat_lit 42478307020800)), (nat_lit 1193, Int.ofNat (nat_lit 61958073139200))]
theorem block010_data_flat156_step : block010_data_flat156 = (CoefficientMerge.fastMerge block010_data_flat136 block010_data_flat155) := by decide +kernel
theorem block010_data_flat156_original : block010_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50840710054400 : Int) atom0716Coded) (CoefficientMerge.scale (47454197772800 : Int) atom0717Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50163393280000 : Int) atom0718Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40943623616000 : Int) atom0719Coded) (CoefficientMerge.scale (55076517529600 : Int) atom0720Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43587528678400 : Int) atom0721Coded) (CoefficientMerge.scale (44782300864000 : Int) atom0722Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51304759027200 : Int) atom0723Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28504801843200 : Int) atom0724Coded) (CoefficientMerge.scale (51198079104000 : Int) atom0725Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52516793448000 : Int) atom0726Coded) (CoefficientMerge.scale (41770540036800 : Int) atom0727Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57639883392000 : Int) atom0728Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46655392089600 : Int) atom0729Coded) (CoefficientMerge.scale (40485755707200 : Int) atom0730Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52168139251200 : Int) atom0731Coded) (CoefficientMerge.scale (30391628198400 : Int) atom0732Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55197057484800 : Int) atom0733Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42478307020800 : Int) atom0734Coded) (CoefficientMerge.scale (61958073139200 : Int) atom0735Coded)))))) := by
  rw [block010_data_flat156_step, block010_data_flat136_original, block010_data_flat155_original]
def block010_data_flat157 : CoefficientMerge.Poly := [(nat_lit 1104, Int.ofNat (nat_lit 45984196294400)), (nat_lit 1105, Int.ofNat (nat_lit 43724731680000)), (nat_lit 1106, Int.ofNat (nat_lit 42342679008000)), (nat_lit 1107, Int.ofNat (nat_lit 49927860864000)), (nat_lit 1108, Int.ofNat (nat_lit 39228832188000)), (nat_lit 1109, Int.ofNat (nat_lit 52822994918400)), (nat_lit 1110, Int.ofNat (nat_lit 43999571700000)), (nat_lit 1111, Int.ofNat (nat_lit 47040248656800)), (nat_lit 1112, Int.ofNat (nat_lit 54750910586400)), (nat_lit 1124, Int.ofNat (nat_lit 28841978188800)), (nat_lit 1125, Int.ofNat (nat_lit 50886380518400)), (nat_lit 1126, Int.ofNat (nat_lit 47708769024000)), (nat_lit 1127, Int.ofNat (nat_lit 45408569472000)), (nat_lit 1128, Int.ofNat (nat_lit 52095180211200)), (nat_lit 1129, Int.ofNat (nat_lit 40662744998400)), (nat_lit 1130, Int.ofNat (nat_lit 55999309363200)), (nat_lit 1131, Int.ofNat (nat_lit 44005822963200)), (nat_lit 1132, Int.ofNat (nat_lit 46400774515200)), (nat_lit 1133, Int.ofNat (nat_lit 53465711040000)), (nat_lit 1146, Int.ofNat (nat_lit 27765907097600)), (nat_lit 1147, Int.ofNat (nat_lit 50840710054400)), (nat_lit 1148, Int.ofNat (nat_lit 47454197772800)), (nat_lit 1149, Int.ofNat (nat_lit 50163393280000)), (nat_lit 1150, Int.ofNat (nat_lit 40943623616000)), (nat_lit 1151, Int.ofNat (nat_lit 55076517529600)), (nat_lit 1152, Int.ofNat (nat_lit 43587528678400)), (nat_lit 1153, Int.ofNat (nat_lit 44782300864000)), (nat_lit 1154, Int.ofNat (nat_lit 51304759027200)), (nat_lit 1168, Int.ofNat (nat_lit 28504801843200)), (nat_lit 1169, Int.ofNat (nat_lit 51198079104000)), (nat_lit 1170, Int.ofNat (nat_lit 52516793448000)), (nat_lit 1171, Int.ofNat (nat_lit 41770540036800)), (nat_lit 1172, Int.ofNat (nat_lit 57639883392000)), (nat_lit 1173, Int.ofNat (nat_lit 46655392089600)), (nat_lit 1174, Int.ofNat (nat_lit 40485755707200)), (nat_lit 1175, Int.ofNat (nat_lit 52168139251200)), (nat_lit 1190, Int.ofNat (nat_lit 30391628198400)), (nat_lit 1191, Int.ofNat (nat_lit 55197057484800)), (nat_lit 1192, Int.ofNat (nat_lit 42478307020800)), (nat_lit 1193, Int.ofNat (nat_lit 61958073139200))]
theorem block010_data_flat157_step : block010_data_flat157 = (CoefficientMerge.fastMerge block010_data_flat117 block010_data_flat156) := by decide +kernel
theorem block010_data_flat157_original : block010_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45984196294400 : Int) atom0696Coded) (CoefficientMerge.scale (43724731680000 : Int) atom0697Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42342679008000 : Int) atom0698Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49927860864000 : Int) atom0699Coded) (CoefficientMerge.scale (39228832188000 : Int) atom0700Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52822994918400 : Int) atom0701Coded) (CoefficientMerge.scale (43999571700000 : Int) atom0702Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47040248656800 : Int) atom0703Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54750910586400 : Int) atom0704Coded) (CoefficientMerge.scale (28841978188800 : Int) atom0705Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50886380518400 : Int) atom0706Coded) (CoefficientMerge.scale (47708769024000 : Int) atom0707Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45408569472000 : Int) atom0708Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52095180211200 : Int) atom0709Coded) (CoefficientMerge.scale (40662744998400 : Int) atom0710Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55999309363200 : Int) atom0711Coded) (CoefficientMerge.scale (44005822963200 : Int) atom0712Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46400774515200 : Int) atom0713Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53465711040000 : Int) atom0714Coded) (CoefficientMerge.scale (27765907097600 : Int) atom0715Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50840710054400 : Int) atom0716Coded) (CoefficientMerge.scale (47454197772800 : Int) atom0717Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50163393280000 : Int) atom0718Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40943623616000 : Int) atom0719Coded) (CoefficientMerge.scale (55076517529600 : Int) atom0720Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43587528678400 : Int) atom0721Coded) (CoefficientMerge.scale (44782300864000 : Int) atom0722Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51304759027200 : Int) atom0723Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28504801843200 : Int) atom0724Coded) (CoefficientMerge.scale (51198079104000 : Int) atom0725Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52516793448000 : Int) atom0726Coded) (CoefficientMerge.scale (41770540036800 : Int) atom0727Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57639883392000 : Int) atom0728Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46655392089600 : Int) atom0729Coded) (CoefficientMerge.scale (40485755707200 : Int) atom0730Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52168139251200 : Int) atom0731Coded) (CoefficientMerge.scale (30391628198400 : Int) atom0732Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55197057484800 : Int) atom0733Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42478307020800 : Int) atom0734Coded) (CoefficientMerge.scale (61958073139200 : Int) atom0735Coded))))))) := by
  rw [block010_data_flat157_step, block010_data_flat117_original, block010_data_flat156_original]
def block010_data_flat158 : CoefficientMerge.Poly := [(nat_lit 1037, Int.ofNat (nat_lit 37423734021504)), (nat_lit 1038, Int.ofNat (nat_lit 34748060719104)), (nat_lit 1039, Int.ofNat (nat_lit 34509342530304)), (nat_lit 1040, Int.ofNat (nat_lit 34217714824704)), (nat_lit 1041, Int.ofNat (nat_lit 31960616904704)), (nat_lit 1042, Int.ofNat (nat_lit 31446597832704)), (nat_lit 1043, Int.ofNat (nat_lit 31809990703104)), (nat_lit 1044, Int.ofNat (nat_lit 41404370635008)), (nat_lit 1045, Int.ofNat (nat_lit 31000486141440)), (nat_lit 1046, Int.ofNat (nat_lit 41272519396608)), (nat_lit 1047, Int.ofNat (nat_lit 36889019085312)), (nat_lit 1048, Int.ofNat (nat_lit 40093076482560)), (nat_lit 1049, Int.ofNat (nat_lit 47967118852608)), (nat_lit 1058, Int.ofNat (nat_lit 22303076342400)), (nat_lit 1059, Int.ofNat (nat_lit 41607678268800)), (nat_lit 1060, Int.ofNat (nat_lit 40696296681600)), (nat_lit 1061, Int.ofNat (nat_lit 39732005577600)), (nat_lit 1062, Int.ofNat (nat_lit 36634078409600)), (nat_lit 1063, Int.ofNat (nat_lit 35706410006400)), (nat_lit 1064, Int.ofNat (nat_lit 35656153545600)), (nat_lit 1065, Int.ofNat (nat_lit 44345527833600)), (nat_lit 1066, Int.ofNat (nat_lit 34468180210800)), (nat_lit 1067, Int.ofNat (nat_lit 45222671692800)), (nat_lit 1068, Int.ofNat (nat_lit 40427074270800)), (nat_lit 1069, Int.ofNat (nat_lit 43815922189200)), (nat_lit 1070, Int.ofNat (nat_lit 51874755080400)), (nat_lit 1080, Int.ofNat (nat_lit 24598926777600)), (nat_lit 1081, Int.ofNat (nat_lit 46170868262400)), (nat_lit 1082, Int.ofNat (nat_lit 44365747910400)), (nat_lit 1083, Int.ofNat (nat_lit 41113185478400)), (nat_lit 1084, Int.ofNat (nat_lit 39603701894400)), (nat_lit 1085, Int.ofNat (nat_lit 38971630252800)), (nat_lit 1086, Int.ofNat (nat_lit 47136694348800)), (nat_lit 1087, Int.ofNat (nat_lit 37088825104800)), (nat_lit 1088, Int.ofNat (nat_lit 49022833305600)), (nat_lit 1089, Int.ofNat (nat_lit 42821685900000)), (nat_lit 1090, Int.ofNat (nat_lit 46253783368800)), (nat_lit 1091, Int.ofNat (nat_lit 54355865810400)), (nat_lit 1102, Int.ofNat (nat_lit 26866266336000)), (nat_lit 1103, Int.ofNat (nat_lit 50413919673600)), (nat_lit 1104, Int.ofNat (nat_lit 45984196294400)), (nat_lit 1105, Int.ofNat (nat_lit 43724731680000)), (nat_lit 1106, Int.ofNat (nat_lit 42342679008000)), (nat_lit 1107, Int.ofNat (nat_lit 49927860864000)), (nat_lit 1108, Int.ofNat (nat_lit 39228832188000)), (nat_lit 1109, Int.ofNat (nat_lit 52822994918400)), (nat_lit 1110, Int.ofNat (nat_lit 43999571700000)), (nat_lit 1111, Int.ofNat (nat_lit 47040248656800)), (nat_lit 1112, Int.ofNat (nat_lit 54750910586400)), (nat_lit 1124, Int.ofNat (nat_lit 28841978188800)), (nat_lit 1125, Int.ofNat (nat_lit 50886380518400)), (nat_lit 1126, Int.ofNat (nat_lit 47708769024000)), (nat_lit 1127, Int.ofNat (nat_lit 45408569472000)), (nat_lit 1128, Int.ofNat (nat_lit 52095180211200)), (nat_lit 1129, Int.ofNat (nat_lit 40662744998400)), (nat_lit 1130, Int.ofNat (nat_lit 55999309363200)), (nat_lit 1131, Int.ofNat (nat_lit 44005822963200)), (nat_lit 1132, Int.ofNat (nat_lit 46400774515200)), (nat_lit 1133, Int.ofNat (nat_lit 53465711040000)), (nat_lit 1146, Int.ofNat (nat_lit 27765907097600)), (nat_lit 1147, Int.ofNat (nat_lit 50840710054400)), (nat_lit 1148, Int.ofNat (nat_lit 47454197772800)), (nat_lit 1149, Int.ofNat (nat_lit 50163393280000)), (nat_lit 1150, Int.ofNat (nat_lit 40943623616000)), (nat_lit 1151, Int.ofNat (nat_lit 55076517529600)), (nat_lit 1152, Int.ofNat (nat_lit 43587528678400)), (nat_lit 1153, Int.ofNat (nat_lit 44782300864000)), (nat_lit 1154, Int.ofNat (nat_lit 51304759027200)), (nat_lit 1168, Int.ofNat (nat_lit 28504801843200)), (nat_lit 1169, Int.ofNat (nat_lit 51198079104000)), (nat_lit 1170, Int.ofNat (nat_lit 52516793448000)), (nat_lit 1171, Int.ofNat (nat_lit 41770540036800)), (nat_lit 1172, Int.ofNat (nat_lit 57639883392000)), (nat_lit 1173, Int.ofNat (nat_lit 46655392089600)), (nat_lit 1174, Int.ofNat (nat_lit 40485755707200)), (nat_lit 1175, Int.ofNat (nat_lit 52168139251200)), (nat_lit 1190, Int.ofNat (nat_lit 30391628198400)), (nat_lit 1191, Int.ofNat (nat_lit 55197057484800)), (nat_lit 1192, Int.ofNat (nat_lit 42478307020800)), (nat_lit 1193, Int.ofNat (nat_lit 61958073139200))]
theorem block010_data_flat158_step : block010_data_flat158 = (CoefficientMerge.fastMerge block010_data_flat078 block010_data_flat157) := by decide +kernel
theorem block010_data_flat158_original : block010_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37423734021504 : Int) atom0656Coded) (CoefficientMerge.scale (34748060719104 : Int) atom0657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34509342530304 : Int) atom0658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34217714824704 : Int) atom0659Coded) (CoefficientMerge.scale (31960616904704 : Int) atom0660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31446597832704 : Int) atom0661Coded) (CoefficientMerge.scale (31809990703104 : Int) atom0662Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41404370635008 : Int) atom0663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31000486141440 : Int) atom0664Coded) (CoefficientMerge.scale (41272519396608 : Int) atom0665Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36889019085312 : Int) atom0666Coded) (CoefficientMerge.scale (40093076482560 : Int) atom0667Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47967118852608 : Int) atom0668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22303076342400 : Int) atom0669Coded) (CoefficientMerge.scale (41607678268800 : Int) atom0670Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40696296681600 : Int) atom0671Coded) (CoefficientMerge.scale (39732005577600 : Int) atom0672Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36634078409600 : Int) atom0673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35706410006400 : Int) atom0674Coded) (CoefficientMerge.scale (35656153545600 : Int) atom0675Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44345527833600 : Int) atom0676Coded) (CoefficientMerge.scale (34468180210800 : Int) atom0677Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45222671692800 : Int) atom0678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40427074270800 : Int) atom0679Coded) (CoefficientMerge.scale (43815922189200 : Int) atom0680Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (51874755080400 : Int) atom0681Coded) (CoefficientMerge.scale (24598926777600 : Int) atom0682Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46170868262400 : Int) atom0683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44365747910400 : Int) atom0684Coded) (CoefficientMerge.scale (41113185478400 : Int) atom0685Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39603701894400 : Int) atom0686Coded) (CoefficientMerge.scale (38971630252800 : Int) atom0687Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47136694348800 : Int) atom0688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37088825104800 : Int) atom0689Coded) (CoefficientMerge.scale (49022833305600 : Int) atom0690Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42821685900000 : Int) atom0691Coded) (CoefficientMerge.scale (46253783368800 : Int) atom0692Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54355865810400 : Int) atom0693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26866266336000 : Int) atom0694Coded) (CoefficientMerge.scale (50413919673600 : Int) atom0695Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45984196294400 : Int) atom0696Coded) (CoefficientMerge.scale (43724731680000 : Int) atom0697Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42342679008000 : Int) atom0698Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49927860864000 : Int) atom0699Coded) (CoefficientMerge.scale (39228832188000 : Int) atom0700Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52822994918400 : Int) atom0701Coded) (CoefficientMerge.scale (43999571700000 : Int) atom0702Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47040248656800 : Int) atom0703Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54750910586400 : Int) atom0704Coded) (CoefficientMerge.scale (28841978188800 : Int) atom0705Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50886380518400 : Int) atom0706Coded) (CoefficientMerge.scale (47708769024000 : Int) atom0707Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45408569472000 : Int) atom0708Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52095180211200 : Int) atom0709Coded) (CoefficientMerge.scale (40662744998400 : Int) atom0710Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55999309363200 : Int) atom0711Coded) (CoefficientMerge.scale (44005822963200 : Int) atom0712Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46400774515200 : Int) atom0713Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53465711040000 : Int) atom0714Coded) (CoefficientMerge.scale (27765907097600 : Int) atom0715Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50840710054400 : Int) atom0716Coded) (CoefficientMerge.scale (47454197772800 : Int) atom0717Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50163393280000 : Int) atom0718Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40943623616000 : Int) atom0719Coded) (CoefficientMerge.scale (55076517529600 : Int) atom0720Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43587528678400 : Int) atom0721Coded) (CoefficientMerge.scale (44782300864000 : Int) atom0722Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51304759027200 : Int) atom0723Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28504801843200 : Int) atom0724Coded) (CoefficientMerge.scale (51198079104000 : Int) atom0725Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52516793448000 : Int) atom0726Coded) (CoefficientMerge.scale (41770540036800 : Int) atom0727Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57639883392000 : Int) atom0728Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46655392089600 : Int) atom0729Coded) (CoefficientMerge.scale (40485755707200 : Int) atom0730Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52168139251200 : Int) atom0731Coded) (CoefficientMerge.scale (30391628198400 : Int) atom0732Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55197057484800 : Int) atom0733Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42478307020800 : Int) atom0734Coded) (CoefficientMerge.scale (61958073139200 : Int) atom0735Coded)))))))) := by
  rw [block010_data_flat158_step, block010_data_flat078_original, block010_data_flat157_original]
def block010_data_flat159 : CoefficientMerge.Poly := [(nat_lit 1037, Int.ofNat (nat_lit 37423734021504)), (nat_lit 1038, Int.ofNat (nat_lit 34748060719104)), (nat_lit 1039, Int.ofNat (nat_lit 34509342530304)), (nat_lit 1040, Int.ofNat (nat_lit 34217714824704)), (nat_lit 1041, Int.ofNat (nat_lit 31960616904704)), (nat_lit 1042, Int.ofNat (nat_lit 31446597832704)), (nat_lit 1043, Int.ofNat (nat_lit 31809990703104)), (nat_lit 1044, Int.ofNat (nat_lit 41404370635008)), (nat_lit 1045, Int.ofNat (nat_lit 31000486141440)), (nat_lit 1046, Int.ofNat (nat_lit 41272519396608)), (nat_lit 1047, Int.ofNat (nat_lit 36889019085312)), (nat_lit 1048, Int.ofNat (nat_lit 40093076482560)), (nat_lit 1049, Int.ofNat (nat_lit 47967118852608)), (nat_lit 1058, Int.ofNat (nat_lit 22303076342400)), (nat_lit 1059, Int.ofNat (nat_lit 41607678268800)), (nat_lit 1060, Int.ofNat (nat_lit 40696296681600)), (nat_lit 1061, Int.ofNat (nat_lit 39732005577600)), (nat_lit 1062, Int.ofNat (nat_lit 36634078409600)), (nat_lit 1063, Int.ofNat (nat_lit 35706410006400)), (nat_lit 1064, Int.ofNat (nat_lit 35656153545600)), (nat_lit 1065, Int.ofNat (nat_lit 44345527833600)), (nat_lit 1066, Int.ofNat (nat_lit 34468180210800)), (nat_lit 1067, Int.ofNat (nat_lit 45222671692800)), (nat_lit 1068, Int.ofNat (nat_lit 40427074270800)), (nat_lit 1069, Int.ofNat (nat_lit 43815922189200)), (nat_lit 1070, Int.ofNat (nat_lit 51874755080400)), (nat_lit 1080, Int.ofNat (nat_lit 24598926777600)), (nat_lit 1081, Int.ofNat (nat_lit 46170868262400)), (nat_lit 1082, Int.ofNat (nat_lit 44365747910400)), (nat_lit 1083, Int.ofNat (nat_lit 41113185478400)), (nat_lit 1084, Int.ofNat (nat_lit 39603701894400)), (nat_lit 1085, Int.ofNat (nat_lit 38971630252800)), (nat_lit 1086, Int.ofNat (nat_lit 47136694348800)), (nat_lit 1087, Int.ofNat (nat_lit 37088825104800)), (nat_lit 1088, Int.ofNat (nat_lit 49022833305600)), (nat_lit 1089, Int.ofNat (nat_lit 42821685900000)), (nat_lit 1090, Int.ofNat (nat_lit 46253783368800)), (nat_lit 1091, Int.ofNat (nat_lit 54355865810400)), (nat_lit 1102, Int.ofNat (nat_lit 26866266336000)), (nat_lit 1103, Int.ofNat (nat_lit 50413919673600)), (nat_lit 1104, Int.ofNat (nat_lit 45984196294400)), (nat_lit 1105, Int.ofNat (nat_lit 43724731680000)), (nat_lit 1106, Int.ofNat (nat_lit 42342679008000)), (nat_lit 1107, Int.ofNat (nat_lit 49927860864000)), (nat_lit 1108, Int.ofNat (nat_lit 39228832188000)), (nat_lit 1109, Int.ofNat (nat_lit 52822994918400)), (nat_lit 1110, Int.ofNat (nat_lit 43999571700000)), (nat_lit 1111, Int.ofNat (nat_lit 47040248656800)), (nat_lit 1112, Int.ofNat (nat_lit 54750910586400)), (nat_lit 1124, Int.ofNat (nat_lit 28841978188800)), (nat_lit 1125, Int.ofNat (nat_lit 50886380518400)), (nat_lit 1126, Int.ofNat (nat_lit 47708769024000)), (nat_lit 1127, Int.ofNat (nat_lit 45408569472000)), (nat_lit 1128, Int.ofNat (nat_lit 52095180211200)), (nat_lit 1129, Int.ofNat (nat_lit 40662744998400)), (nat_lit 1130, Int.ofNat (nat_lit 55999309363200)), (nat_lit 1131, Int.ofNat (nat_lit 44005822963200)), (nat_lit 1132, Int.ofNat (nat_lit 46400774515200)), (nat_lit 1133, Int.ofNat (nat_lit 53465711040000)), (nat_lit 1146, Int.ofNat (nat_lit 27765907097600)), (nat_lit 1147, Int.ofNat (nat_lit 50840710054400)), (nat_lit 1148, Int.ofNat (nat_lit 47454197772800)), (nat_lit 1149, Int.ofNat (nat_lit 50163393280000)), (nat_lit 1150, Int.ofNat (nat_lit 40943623616000)), (nat_lit 1151, Int.ofNat (nat_lit 55076517529600)), (nat_lit 1152, Int.ofNat (nat_lit 43587528678400)), (nat_lit 1153, Int.ofNat (nat_lit 44782300864000)), (nat_lit 1154, Int.ofNat (nat_lit 51304759027200)), (nat_lit 1168, Int.ofNat (nat_lit 28504801843200)), (nat_lit 1169, Int.ofNat (nat_lit 51198079104000)), (nat_lit 1170, Int.ofNat (nat_lit 52516793448000)), (nat_lit 1171, Int.ofNat (nat_lit 41770540036800)), (nat_lit 1172, Int.ofNat (nat_lit 57639883392000)), (nat_lit 1173, Int.ofNat (nat_lit 46655392089600)), (nat_lit 1174, Int.ofNat (nat_lit 40485755707200)), (nat_lit 1175, Int.ofNat (nat_lit 52168139251200)), (nat_lit 1190, Int.ofNat (nat_lit 30391628198400)), (nat_lit 1191, Int.ofNat (nat_lit 55197057484800)), (nat_lit 1192, Int.ofNat (nat_lit 42478307020800)), (nat_lit 1193, Int.ofNat (nat_lit 61958073139200))]
theorem block010_data_flat159_step : block010_data_flat159 = (CoefficientMerge.trim block010_data_flat158) := by decide +kernel
theorem block010_data_flat159_original : block010_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37423734021504 : Int) atom0656Coded) (CoefficientMerge.scale (34748060719104 : Int) atom0657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34509342530304 : Int) atom0658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34217714824704 : Int) atom0659Coded) (CoefficientMerge.scale (31960616904704 : Int) atom0660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31446597832704 : Int) atom0661Coded) (CoefficientMerge.scale (31809990703104 : Int) atom0662Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41404370635008 : Int) atom0663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31000486141440 : Int) atom0664Coded) (CoefficientMerge.scale (41272519396608 : Int) atom0665Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36889019085312 : Int) atom0666Coded) (CoefficientMerge.scale (40093076482560 : Int) atom0667Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47967118852608 : Int) atom0668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22303076342400 : Int) atom0669Coded) (CoefficientMerge.scale (41607678268800 : Int) atom0670Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40696296681600 : Int) atom0671Coded) (CoefficientMerge.scale (39732005577600 : Int) atom0672Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36634078409600 : Int) atom0673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35706410006400 : Int) atom0674Coded) (CoefficientMerge.scale (35656153545600 : Int) atom0675Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44345527833600 : Int) atom0676Coded) (CoefficientMerge.scale (34468180210800 : Int) atom0677Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45222671692800 : Int) atom0678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40427074270800 : Int) atom0679Coded) (CoefficientMerge.scale (43815922189200 : Int) atom0680Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (51874755080400 : Int) atom0681Coded) (CoefficientMerge.scale (24598926777600 : Int) atom0682Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46170868262400 : Int) atom0683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44365747910400 : Int) atom0684Coded) (CoefficientMerge.scale (41113185478400 : Int) atom0685Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39603701894400 : Int) atom0686Coded) (CoefficientMerge.scale (38971630252800 : Int) atom0687Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47136694348800 : Int) atom0688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37088825104800 : Int) atom0689Coded) (CoefficientMerge.scale (49022833305600 : Int) atom0690Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42821685900000 : Int) atom0691Coded) (CoefficientMerge.scale (46253783368800 : Int) atom0692Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54355865810400 : Int) atom0693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26866266336000 : Int) atom0694Coded) (CoefficientMerge.scale (50413919673600 : Int) atom0695Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45984196294400 : Int) atom0696Coded) (CoefficientMerge.scale (43724731680000 : Int) atom0697Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42342679008000 : Int) atom0698Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49927860864000 : Int) atom0699Coded) (CoefficientMerge.scale (39228832188000 : Int) atom0700Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52822994918400 : Int) atom0701Coded) (CoefficientMerge.scale (43999571700000 : Int) atom0702Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47040248656800 : Int) atom0703Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54750910586400 : Int) atom0704Coded) (CoefficientMerge.scale (28841978188800 : Int) atom0705Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50886380518400 : Int) atom0706Coded) (CoefficientMerge.scale (47708769024000 : Int) atom0707Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45408569472000 : Int) atom0708Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52095180211200 : Int) atom0709Coded) (CoefficientMerge.scale (40662744998400 : Int) atom0710Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55999309363200 : Int) atom0711Coded) (CoefficientMerge.scale (44005822963200 : Int) atom0712Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46400774515200 : Int) atom0713Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53465711040000 : Int) atom0714Coded) (CoefficientMerge.scale (27765907097600 : Int) atom0715Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50840710054400 : Int) atom0716Coded) (CoefficientMerge.scale (47454197772800 : Int) atom0717Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50163393280000 : Int) atom0718Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40943623616000 : Int) atom0719Coded) (CoefficientMerge.scale (55076517529600 : Int) atom0720Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43587528678400 : Int) atom0721Coded) (CoefficientMerge.scale (44782300864000 : Int) atom0722Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51304759027200 : Int) atom0723Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28504801843200 : Int) atom0724Coded) (CoefficientMerge.scale (51198079104000 : Int) atom0725Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52516793448000 : Int) atom0726Coded) (CoefficientMerge.scale (41770540036800 : Int) atom0727Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57639883392000 : Int) atom0728Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46655392089600 : Int) atom0729Coded) (CoefficientMerge.scale (40485755707200 : Int) atom0730Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52168139251200 : Int) atom0731Coded) (CoefficientMerge.scale (30391628198400 : Int) atom0732Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55197057484800 : Int) atom0733Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42478307020800 : Int) atom0734Coded) (CoefficientMerge.scale (61958073139200 : Int) atom0735Coded))))))))) := by
  rw [block010_data_flat159_step, block010_data_flat158_original]
theorem block010_data : block010 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37423734021504 : Int) atom0656Coded) (CoefficientMerge.scale (34748060719104 : Int) atom0657Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34509342530304 : Int) atom0658Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34217714824704 : Int) atom0659Coded) (CoefficientMerge.scale (31960616904704 : Int) atom0660Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (31446597832704 : Int) atom0661Coded) (CoefficientMerge.scale (31809990703104 : Int) atom0662Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41404370635008 : Int) atom0663Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31000486141440 : Int) atom0664Coded) (CoefficientMerge.scale (41272519396608 : Int) atom0665Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36889019085312 : Int) atom0666Coded) (CoefficientMerge.scale (40093076482560 : Int) atom0667Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47967118852608 : Int) atom0668Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22303076342400 : Int) atom0669Coded) (CoefficientMerge.scale (41607678268800 : Int) atom0670Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40696296681600 : Int) atom0671Coded) (CoefficientMerge.scale (39732005577600 : Int) atom0672Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36634078409600 : Int) atom0673Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35706410006400 : Int) atom0674Coded) (CoefficientMerge.scale (35656153545600 : Int) atom0675Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44345527833600 : Int) atom0676Coded) (CoefficientMerge.scale (34468180210800 : Int) atom0677Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45222671692800 : Int) atom0678Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40427074270800 : Int) atom0679Coded) (CoefficientMerge.scale (43815922189200 : Int) atom0680Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (51874755080400 : Int) atom0681Coded) (CoefficientMerge.scale (24598926777600 : Int) atom0682Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46170868262400 : Int) atom0683Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44365747910400 : Int) atom0684Coded) (CoefficientMerge.scale (41113185478400 : Int) atom0685Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39603701894400 : Int) atom0686Coded) (CoefficientMerge.scale (38971630252800 : Int) atom0687Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47136694348800 : Int) atom0688Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37088825104800 : Int) atom0689Coded) (CoefficientMerge.scale (49022833305600 : Int) atom0690Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (42821685900000 : Int) atom0691Coded) (CoefficientMerge.scale (46253783368800 : Int) atom0692Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54355865810400 : Int) atom0693Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26866266336000 : Int) atom0694Coded) (CoefficientMerge.scale (50413919673600 : Int) atom0695Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (45984196294400 : Int) atom0696Coded) (CoefficientMerge.scale (43724731680000 : Int) atom0697Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42342679008000 : Int) atom0698Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (49927860864000 : Int) atom0699Coded) (CoefficientMerge.scale (39228832188000 : Int) atom0700Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52822994918400 : Int) atom0701Coded) (CoefficientMerge.scale (43999571700000 : Int) atom0702Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47040248656800 : Int) atom0703Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (54750910586400 : Int) atom0704Coded) (CoefficientMerge.scale (28841978188800 : Int) atom0705Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50886380518400 : Int) atom0706Coded) (CoefficientMerge.scale (47708769024000 : Int) atom0707Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45408569472000 : Int) atom0708Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52095180211200 : Int) atom0709Coded) (CoefficientMerge.scale (40662744998400 : Int) atom0710Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55999309363200 : Int) atom0711Coded) (CoefficientMerge.scale (44005822963200 : Int) atom0712Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46400774515200 : Int) atom0713Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53465711040000 : Int) atom0714Coded) (CoefficientMerge.scale (27765907097600 : Int) atom0715Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (50840710054400 : Int) atom0716Coded) (CoefficientMerge.scale (47454197772800 : Int) atom0717Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50163393280000 : Int) atom0718Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40943623616000 : Int) atom0719Coded) (CoefficientMerge.scale (55076517529600 : Int) atom0720Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (43587528678400 : Int) atom0721Coded) (CoefficientMerge.scale (44782300864000 : Int) atom0722Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (51304759027200 : Int) atom0723Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28504801843200 : Int) atom0724Coded) (CoefficientMerge.scale (51198079104000 : Int) atom0725Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52516793448000 : Int) atom0726Coded) (CoefficientMerge.scale (41770540036800 : Int) atom0727Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57639883392000 : Int) atom0728Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46655392089600 : Int) atom0729Coded) (CoefficientMerge.scale (40485755707200 : Int) atom0730Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52168139251200 : Int) atom0731Coded) (CoefficientMerge.scale (30391628198400 : Int) atom0732Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (55197057484800 : Int) atom0733Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42478307020800 : Int) atom0734Coded) (CoefficientMerge.scale (61958073139200 : Int) atom0735Coded)))))))) := by
  have h : block010 = block010_data_flat159 := by decide +kernel
  exact h.trans block010_data_flat159_original
theorem block010_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block010 := by
  rw [block010_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0656Coded_nonneg g hg hA hB) (atom0657Coded_nonneg g hg hA hB)) (add_nonneg (atom0658Coded_nonneg g hg hA hB) (add_nonneg (atom0659Coded_nonneg g hg hA hB) (atom0660Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0661Coded_nonneg g hg hA hB) (atom0662Coded_nonneg g hg hA hB)) (add_nonneg (atom0663Coded_nonneg g hg hA hB) (add_nonneg (atom0664Coded_nonneg g hg hA hB) (atom0665Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0666Coded_nonneg g hg hA hB) (atom0667Coded_nonneg g hg hA hB)) (add_nonneg (atom0668Coded_nonneg g hg hA hB) (add_nonneg (atom0669Coded_nonneg g hg hA hB) (atom0670Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0671Coded_nonneg g hg hA hB) (atom0672Coded_nonneg g hg hA hB)) (add_nonneg (atom0673Coded_nonneg g hg hA hB) (add_nonneg (atom0674Coded_nonneg g hg hA hB) (atom0675Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0676Coded_nonneg g hg hA hB) (atom0677Coded_nonneg g hg hA hB)) (add_nonneg (atom0678Coded_nonneg g hg hA hB) (add_nonneg (atom0679Coded_nonneg g hg hA hB) (atom0680Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0681Coded_nonneg g hg hA hB) (atom0682Coded_nonneg g hg hA hB)) (add_nonneg (atom0683Coded_nonneg g hg hA hB) (add_nonneg (atom0684Coded_nonneg g hg hA hB) (atom0685Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0686Coded_nonneg g hg hA hB) (atom0687Coded_nonneg g hg hA hB)) (add_nonneg (atom0688Coded_nonneg g hg hA hB) (add_nonneg (atom0689Coded_nonneg g hg hA hB) (atom0690Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0691Coded_nonneg g hg hA hB) (atom0692Coded_nonneg g hg hA hB)) (add_nonneg (atom0693Coded_nonneg g hg hA hB) (add_nonneg (atom0694Coded_nonneg g hg hA hB) (atom0695Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0696Coded_nonneg g hg hA hB) (atom0697Coded_nonneg g hg hA hB)) (add_nonneg (atom0698Coded_nonneg g hg hA hB) (add_nonneg (atom0699Coded_nonneg g hg hA hB) (atom0700Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0701Coded_nonneg g hg hA hB) (atom0702Coded_nonneg g hg hA hB)) (add_nonneg (atom0703Coded_nonneg g hg hA hB) (add_nonneg (atom0704Coded_nonneg g hg hA hB) (atom0705Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0706Coded_nonneg g hg hA hB) (atom0707Coded_nonneg g hg hA hB)) (add_nonneg (atom0708Coded_nonneg g hg hA hB) (add_nonneg (atom0709Coded_nonneg g hg hA hB) (atom0710Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0711Coded_nonneg g hg hA hB) (atom0712Coded_nonneg g hg hA hB)) (add_nonneg (atom0713Coded_nonneg g hg hA hB) (add_nonneg (atom0714Coded_nonneg g hg hA hB) (atom0715Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0716Coded_nonneg g hg hA hB) (atom0717Coded_nonneg g hg hA hB)) (add_nonneg (atom0718Coded_nonneg g hg hA hB) (add_nonneg (atom0719Coded_nonneg g hg hA hB) (atom0720Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0721Coded_nonneg g hg hA hB) (atom0722Coded_nonneg g hg hA hB)) (add_nonneg (atom0723Coded_nonneg g hg hA hB) (add_nonneg (atom0724Coded_nonneg g hg hA hB) (atom0725Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0726Coded_nonneg g hg hA hB) (atom0727Coded_nonneg g hg hA hB)) (add_nonneg (atom0728Coded_nonneg g hg hA hB) (add_nonneg (atom0729Coded_nonneg g hg hA hB) (atom0730Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0731Coded_nonneg g hg hA hB) (atom0732Coded_nonneg g hg hA hB)) (add_nonneg (atom0733Coded_nonneg g hg hA hB) (add_nonneg (atom0734Coded_nonneg g hg hA hB) (atom0735Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
