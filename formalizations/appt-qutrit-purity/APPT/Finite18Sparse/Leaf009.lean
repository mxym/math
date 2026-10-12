-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0655 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0655 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0655 = ((g 3) * (g 14) * (g 14)) := by
  norm_num [atom0655, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0655_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8141283000 : Int) atom0655) := by
  rw [SparsePolynomial.eval_scale, eval_atom0655]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0655Coded : CoefficientMerge.Poly := [(nat_lit 1238, Int.ofNat (nat_lit 1))]
theorem atom0655Coded_decode : atom0655 = SparsePolynomial.decodeCubic 18 atom0655Coded := by decide +kernel
theorem atom0655Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8141283000 : Int) atom0655Coded) := by
  have h := atom0655_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0655Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0656 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0656 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0656 = ((g 3) * (g 14) * (g 15)) := by
  norm_num [atom0656, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0656_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12793243320 : Int) atom0656) := by
  rw [SparsePolynomial.eval_scale, eval_atom0656]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0656Coded : CoefficientMerge.Poly := [(nat_lit 1239, Int.ofNat (nat_lit 1))]
theorem atom0656Coded_decode : atom0656 = SparsePolynomial.decodeCubic 18 atom0656Coded := by decide +kernel
theorem atom0656Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12793243320 : Int) atom0656Coded) := by
  have h := atom0656_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0656Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0657 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0657 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0657 = ((g 3) * (g 14) * (g 16)) := by
  norm_num [atom0657, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0657_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8558934480 : Int) atom0657) := by
  rw [SparsePolynomial.eval_scale, eval_atom0657]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0657Coded : CoefficientMerge.Poly := [(nat_lit 1240, Int.ofNat (nat_lit 1))]
theorem atom0657Coded_decode : atom0657 = SparsePolynomial.decodeCubic 18 atom0657Coded := by decide +kernel
theorem atom0657Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8558934480 : Int) atom0657Coded) := by
  have h := atom0657_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0657Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0658 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0658 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0658 = ((g 3) * (g 14) * (g 17)) := by
  norm_num [atom0658, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0658_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11377463760 : Int) atom0658) := by
  rw [SparsePolynomial.eval_scale, eval_atom0658]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0658Coded : CoefficientMerge.Poly := [(nat_lit 1241, Int.ofNat (nat_lit 1))]
theorem atom0658Coded_decode : atom0658 = SparsePolynomial.decodeCubic 18 atom0658Coded := by decide +kernel
theorem atom0658Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11377463760 : Int) atom0658Coded) := by
  have h := atom0658_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0658Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0659 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0659 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0659 = ((g 3) * (g 15) * (g 15)) := by
  norm_num [atom0659, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0659_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4082641920 : Int) atom0659) := by
  rw [SparsePolynomial.eval_scale, eval_atom0659]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0659Coded : CoefficientMerge.Poly := [(nat_lit 1257, Int.ofNat (nat_lit 1))]
theorem atom0659Coded_decode : atom0659 = SparsePolynomial.decodeCubic 18 atom0659Coded := by decide +kernel
theorem atom0659Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4082641920 : Int) atom0659Coded) := by
  have h := atom0659_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0659Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0660 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0660 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0660 = ((g 3) * (g 15) * (g 16)) := by
  norm_num [atom0660, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0660_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5228697600 : Int) atom0660) := by
  rw [SparsePolynomial.eval_scale, eval_atom0660]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0660Coded : CoefficientMerge.Poly := [(nat_lit 1258, Int.ofNat (nat_lit 1))]
theorem atom0660Coded_decode : atom0660 = SparsePolynomial.decodeCubic 18 atom0660Coded := by decide +kernel
theorem atom0660Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5228697600 : Int) atom0660Coded) := by
  have h := atom0660_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0660Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0661 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0661 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0661 = ((g 3) * (g 15) * (g 17)) := by
  norm_num [atom0661, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0661_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8587353600 : Int) atom0661) := by
  rw [SparsePolynomial.eval_scale, eval_atom0661]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0661Coded : CoefficientMerge.Poly := [(nat_lit 1259, Int.ofNat (nat_lit 1))]
theorem atom0661Coded_decode : atom0661 = SparsePolynomial.decodeCubic 18 atom0661Coded := by decide +kernel
theorem atom0661Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8587353600 : Int) atom0661Coded) := by
  have h := atom0661_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0661Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0662 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0662 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0662 = ((g 3) * (g 16) * (g 16)) := by
  norm_num [atom0662, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0662_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (258048000 : Int) atom0662) := by
  rw [SparsePolynomial.eval_scale, eval_atom0662]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0662Coded : CoefficientMerge.Poly := [(nat_lit 1276, Int.ofNat (nat_lit 1))]
theorem atom0662Coded_decode : atom0662 = SparsePolynomial.decodeCubic 18 atom0662Coded := by decide +kernel
theorem atom0662Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (258048000 : Int) atom0662Coded) := by
  have h := atom0662_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0662Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0663 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0663 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0663 = ((g 3) * (g 16) * (g 17)) := by
  norm_num [atom0663, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0663_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4255534080 : Int) atom0663) := by
  rw [SparsePolynomial.eval_scale, eval_atom0663]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0663Coded : CoefficientMerge.Poly := [(nat_lit 1277, Int.ofNat (nat_lit 1))]
theorem atom0663Coded_decode : atom0663 = SparsePolynomial.decodeCubic 18 atom0663Coded := by decide +kernel
theorem atom0663Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4255534080 : Int) atom0663Coded) := by
  have h := atom0663_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0663Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0664 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0664 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0664 = ((g 3) * (g 17) * (g 17)) := by
  norm_num [atom0664, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0664_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3789918720 : Int) atom0664) := by
  rw [SparsePolynomial.eval_scale, eval_atom0664]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0664Coded : CoefficientMerge.Poly := [(nat_lit 1295, Int.ofNat (nat_lit 1))]
theorem atom0664Coded_decode : atom0664 = SparsePolynomial.decodeCubic 18 atom0664Coded := by decide +kernel
theorem atom0664Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3789918720 : Int) atom0664Coded) := by
  have h := atom0664_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0664Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0665 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0665 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0665 = ((g 4) * (g 4) * (g 4)) := by
  norm_num [atom0665, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0665_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (839677440 : Int) atom0665) := by
  rw [SparsePolynomial.eval_scale, eval_atom0665]
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 4) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0665Coded : CoefficientMerge.Poly := [(nat_lit 1372, Int.ofNat (nat_lit 1))]
theorem atom0665Coded_decode : atom0665 = SparsePolynomial.decodeCubic 18 atom0665Coded := by decide +kernel
theorem atom0665Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (839677440 : Int) atom0665Coded) := by
  have h := atom0665_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0665Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0666 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0666 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0666 = ((g 4) * (g 4) * (g 5)) := by
  norm_num [atom0666, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0666_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1603536000 : Int) atom0666) := by
  rw [SparsePolynomial.eval_scale, eval_atom0666]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0666Coded : CoefficientMerge.Poly := [(nat_lit 1373, Int.ofNat (nat_lit 1))]
theorem atom0666Coded_decode : atom0666 = SparsePolynomial.decodeCubic 18 atom0666Coded := by decide +kernel
theorem atom0666Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1603536000 : Int) atom0666Coded) := by
  have h := atom0666_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0666Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0667 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0667 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0667 = ((g 4) * (g 4) * (g 6)) := by
  norm_num [atom0667, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0667_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (615212160 : Int) atom0667) := by
  rw [SparsePolynomial.eval_scale, eval_atom0667]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0667Coded : CoefficientMerge.Poly := [(nat_lit 1374, Int.ofNat (nat_lit 1))]
theorem atom0667Coded_decode : atom0667 = SparsePolynomial.decodeCubic 18 atom0667Coded := by decide +kernel
theorem atom0667Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (615212160 : Int) atom0667Coded) := by
  have h := atom0667_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0667Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0668 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0668 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0668 = ((g 4) * (g 4) * (g 7)) := by
  norm_num [atom0668, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0668_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103864320 : Int) atom0668) := by
  rw [SparsePolynomial.eval_scale, eval_atom0668]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0668Coded : CoefficientMerge.Poly := [(nat_lit 1375, Int.ofNat (nat_lit 1))]
theorem atom0668Coded_decode : atom0668 = SparsePolynomial.decodeCubic 18 atom0668Coded := by decide +kernel
theorem atom0668Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (103864320 : Int) atom0668Coded) := by
  have h := atom0668_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0668Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0669 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0669 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0669 = ((g 4) * (g 4) * (g 8)) := by
  norm_num [atom0669, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0669_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25159680 : Int) atom0669) := by
  rw [SparsePolynomial.eval_scale, eval_atom0669]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0669Coded : CoefficientMerge.Poly := [(nat_lit 1376, Int.ofNat (nat_lit 1))]
theorem atom0669Coded_decode : atom0669 = SparsePolynomial.decodeCubic 18 atom0669Coded := by decide +kernel
theorem atom0669Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (25159680 : Int) atom0669Coded) := by
  have h := atom0669_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0669Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0670 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0670 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0670 = ((g 4) * (g 4) * (g 12)) := by
  norm_num [atom0670, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0670_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1531037760 : Int) atom0670) := by
  rw [SparsePolynomial.eval_scale, eval_atom0670]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0670Coded : CoefficientMerge.Poly := [(nat_lit 1380, Int.ofNat (nat_lit 1))]
theorem atom0670Coded_decode : atom0670 = SparsePolynomial.decodeCubic 18 atom0670Coded := by decide +kernel
theorem atom0670Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1531037760 : Int) atom0670Coded) := by
  have h := atom0670_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0670Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0671 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 4, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0671 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0671 = ((g 4) * (g 4) * (g 14)) := by
  norm_num [atom0671, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0671_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (460951440 : Int) atom0671) := by
  rw [SparsePolynomial.eval_scale, eval_atom0671]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0671Coded : CoefficientMerge.Poly := [(nat_lit 1382, Int.ofNat (nat_lit 1))]
theorem atom0671Coded_decode : atom0671 = SparsePolynomial.decodeCubic 18 atom0671Coded := by decide +kernel
theorem atom0671Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (460951440 : Int) atom0671Coded) := by
  have h := atom0671_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0671Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0672 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0672 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0672 = ((g 4) * (g 5) * (g 5)) := by
  norm_num [atom0672, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0672_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1465409280 : Int) atom0672) := by
  rw [SparsePolynomial.eval_scale, eval_atom0672]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0672Coded : CoefficientMerge.Poly := [(nat_lit 1391, Int.ofNat (nat_lit 1))]
theorem atom0672Coded_decode : atom0672 = SparsePolynomial.decodeCubic 18 atom0672Coded := by decide +kernel
theorem atom0672Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1465409280 : Int) atom0672Coded) := by
  have h := atom0672_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0672Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0673 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0673 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0673 = ((g 4) * (g 5) * (g 6)) := by
  norm_num [atom0673, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0673_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1111580160 : Int) atom0673) := by
  rw [SparsePolynomial.eval_scale, eval_atom0673]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0673Coded : CoefficientMerge.Poly := [(nat_lit 1392, Int.ofNat (nat_lit 1))]
theorem atom0673Coded_decode : atom0673 = SparsePolynomial.decodeCubic 18 atom0673Coded := by decide +kernel
theorem atom0673Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1111580160 : Int) atom0673Coded) := by
  have h := atom0673_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0673Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0674 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0674 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0674 = ((g 4) * (g 5) * (g 10)) := by
  norm_num [atom0674, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0674_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103864320 : Int) atom0674) := by
  rw [SparsePolynomial.eval_scale, eval_atom0674]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0674Coded : CoefficientMerge.Poly := [(nat_lit 1396, Int.ofNat (nat_lit 1))]
theorem atom0674Coded_decode : atom0674 = SparsePolynomial.decodeCubic 18 atom0674Coded := by decide +kernel
theorem atom0674Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (103864320 : Int) atom0674Coded) := by
  have h := atom0674_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0674Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0675 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0675 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0675 = ((g 4) * (g 5) * (g 11)) := by
  norm_num [atom0675, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0675_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207728640 : Int) atom0675) := by
  rw [SparsePolynomial.eval_scale, eval_atom0675]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0675Coded : CoefficientMerge.Poly := [(nat_lit 1397, Int.ofNat (nat_lit 1))]
theorem atom0675Coded_decode : atom0675 = SparsePolynomial.decodeCubic 18 atom0675Coded := by decide +kernel
theorem atom0675Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (207728640 : Int) atom0675Coded) := by
  have h := atom0675_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0675Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0676 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0676 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0676 = ((g 4) * (g 5) * (g 12)) := by
  norm_num [atom0676, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0676_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2424376752 : Int) atom0676) := by
  rw [SparsePolynomial.eval_scale, eval_atom0676]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0676Coded : CoefficientMerge.Poly := [(nat_lit 1398, Int.ofNat (nat_lit 1))]
theorem atom0676Coded_decode : atom0676 = SparsePolynomial.decodeCubic 18 atom0676Coded := by decide +kernel
theorem atom0676Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2424376752 : Int) atom0676Coded) := by
  have h := atom0676_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0676Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0677 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0677 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0677 = ((g 4) * (g 5) * (g 14)) := by
  norm_num [atom0677, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0677_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1101237360 : Int) atom0677) := by
  rw [SparsePolynomial.eval_scale, eval_atom0677]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0677Coded : CoefficientMerge.Poly := [(nat_lit 1400, Int.ofNat (nat_lit 1))]
theorem atom0677Coded_decode : atom0677 = SparsePolynomial.decodeCubic 18 atom0677Coded := by decide +kernel
theorem atom0677Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1101237360 : Int) atom0677Coded) := by
  have h := atom0677_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0677Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0678 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0678 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0678 = ((g 4) * (g 5) * (g 15)) := by
  norm_num [atom0678, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0678_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1180247040 : Int) atom0678) := by
  rw [SparsePolynomial.eval_scale, eval_atom0678]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0678Coded : CoefficientMerge.Poly := [(nat_lit 1401, Int.ofNat (nat_lit 1))]
theorem atom0678Coded_decode : atom0678 = SparsePolynomial.decodeCubic 18 atom0678Coded := by decide +kernel
theorem atom0678Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1180247040 : Int) atom0678Coded) := by
  have h := atom0678_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0678Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0679 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0679 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0679 = ((g 4) * (g 5) * (g 16)) := by
  norm_num [atom0679, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0679_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2293143552 : Int) atom0679) := by
  rw [SparsePolynomial.eval_scale, eval_atom0679]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0679Coded : CoefficientMerge.Poly := [(nat_lit 1402, Int.ofNat (nat_lit 1))]
theorem atom0679Coded_decode : atom0679 = SparsePolynomial.decodeCubic 18 atom0679Coded := by decide +kernel
theorem atom0679Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2293143552 : Int) atom0679Coded) := by
  have h := atom0679_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0679Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0680 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 5, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0680 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0680 = ((g 4) * (g 5) * (g 17)) := by
  norm_num [atom0680, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0680_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3586383360 : Int) atom0680) := by
  rw [SparsePolynomial.eval_scale, eval_atom0680]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0680Coded : CoefficientMerge.Poly := [(nat_lit 1403, Int.ofNat (nat_lit 1))]
theorem atom0680Coded_decode : atom0680 = SparsePolynomial.decodeCubic 18 atom0680Coded := by decide +kernel
theorem atom0680Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3586383360 : Int) atom0680Coded) := by
  have h := atom0680_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0680Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0681 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0681 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0681 = ((g 4) * (g 6) * (g 6)) := by
  norm_num [atom0681, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0681_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (423540480 : Int) atom0681) := by
  rw [SparsePolynomial.eval_scale, eval_atom0681]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0681Coded : CoefficientMerge.Poly := [(nat_lit 1410, Int.ofNat (nat_lit 1))]
theorem atom0681Coded_decode : atom0681 = SparsePolynomial.decodeCubic 18 atom0681Coded := by decide +kernel
theorem atom0681Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (423540480 : Int) atom0681Coded) := by
  have h := atom0681_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0681Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0682 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0682 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0682 = ((g 4) * (g 6) * (g 9)) := by
  norm_num [atom0682, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0682_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (107089920 : Int) atom0682) := by
  rw [SparsePolynomial.eval_scale, eval_atom0682]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0682Coded : CoefficientMerge.Poly := [(nat_lit 1413, Int.ofNat (nat_lit 1))]
theorem atom0682Coded_decode : atom0682 = SparsePolynomial.decodeCubic 18 atom0682Coded := by decide +kernel
theorem atom0682Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (107089920 : Int) atom0682Coded) := by
  have h := atom0682_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0682Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0683 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0683 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0683 = ((g 4) * (g 6) * (g 10)) := by
  norm_num [atom0683, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0683_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (264499200 : Int) atom0683) := by
  rw [SparsePolynomial.eval_scale, eval_atom0683]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0683Coded : CoefficientMerge.Poly := [(nat_lit 1414, Int.ofNat (nat_lit 1))]
theorem atom0683Coded_decode : atom0683 = SparsePolynomial.decodeCubic 18 atom0683Coded := by decide +kernel
theorem atom0683Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (264499200 : Int) atom0683Coded) := by
  have h := atom0683_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0683Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0684 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0684 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0684 = ((g 4) * (g 6) * (g 11)) := by
  norm_num [atom0684, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0684_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (421908480 : Int) atom0684) := by
  rw [SparsePolynomial.eval_scale, eval_atom0684]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0684Coded : CoefficientMerge.Poly := [(nat_lit 1415, Int.ofNat (nat_lit 1))]
theorem atom0684Coded_decode : atom0684 = SparsePolynomial.decodeCubic 18 atom0684Coded := by decide +kernel
theorem atom0684Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (421908480 : Int) atom0684Coded) := by
  have h := atom0684_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0684Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0685 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0685 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0685 = ((g 4) * (g 6) * (g 12)) := by
  norm_num [atom0685, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0685_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2576627520 : Int) atom0685) := by
  rw [SparsePolynomial.eval_scale, eval_atom0685]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0685Coded : CoefficientMerge.Poly := [(nat_lit 1416, Int.ofNat (nat_lit 1))]
theorem atom0685Coded_decode : atom0685 = SparsePolynomial.decodeCubic 18 atom0685Coded := by decide +kernel
theorem atom0685Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2576627520 : Int) atom0685Coded) := by
  have h := atom0685_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0685Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0686 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0686 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0686 = ((g 4) * (g 6) * (g 13)) := by
  norm_num [atom0686, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0686_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1293281520 : Int) atom0686) := by
  rw [SparsePolynomial.eval_scale, eval_atom0686]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0686Coded : CoefficientMerge.Poly := [(nat_lit 1417, Int.ofNat (nat_lit 1))]
theorem atom0686Coded_decode : atom0686 = SparsePolynomial.decodeCubic 18 atom0686Coded := by decide +kernel
theorem atom0686Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1293281520 : Int) atom0686Coded) := by
  have h := atom0686_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0686Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0687 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0687 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0687 = ((g 4) * (g 6) * (g 14)) := by
  norm_num [atom0687, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0687_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2694257760 : Int) atom0687) := by
  rw [SparsePolynomial.eval_scale, eval_atom0687]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0687Coded : CoefficientMerge.Poly := [(nat_lit 1418, Int.ofNat (nat_lit 1))]
theorem atom0687Coded_decode : atom0687 = SparsePolynomial.decodeCubic 18 atom0687Coded := by decide +kernel
theorem atom0687Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2694257760 : Int) atom0687Coded) := by
  have h := atom0687_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0687Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0688 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0688 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0688 = ((g 4) * (g 6) * (g 15)) := by
  norm_num [atom0688, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0688_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3482496240 : Int) atom0688) := by
  rw [SparsePolynomial.eval_scale, eval_atom0688]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0688Coded : CoefficientMerge.Poly := [(nat_lit 1419, Int.ofNat (nat_lit 1))]
theorem atom0688Coded_decode : atom0688 = SparsePolynomial.decodeCubic 18 atom0688Coded := by decide +kernel
theorem atom0688Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3482496240 : Int) atom0688Coded) := by
  have h := atom0688_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0688Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0689 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0689 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0689 = ((g 4) * (g 6) * (g 16)) := by
  norm_num [atom0689, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0689_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5041760400 : Int) atom0689) := by
  rw [SparsePolynomial.eval_scale, eval_atom0689]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0689Coded : CoefficientMerge.Poly := [(nat_lit 1420, Int.ofNat (nat_lit 1))]
theorem atom0689Coded_decode : atom0689 = SparsePolynomial.decodeCubic 18 atom0689Coded := by decide +kernel
theorem atom0689Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5041760400 : Int) atom0689Coded) := by
  have h := atom0689_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0689Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0690 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 6, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0690 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0690 = ((g 4) * (g 6) * (g 17)) := by
  norm_num [atom0690, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0690_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6677153280 : Int) atom0690) := by
  rw [SparsePolynomial.eval_scale, eval_atom0690]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0690Coded : CoefficientMerge.Poly := [(nat_lit 1421, Int.ofNat (nat_lit 1))]
theorem atom0690Coded_decode : atom0690 = SparsePolynomial.decodeCubic 18 atom0690Coded := by decide +kernel
theorem atom0690Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6677153280 : Int) atom0690Coded) := by
  have h := atom0690_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0690Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0691 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0691 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0691 = ((g 4) * (g 7) * (g 7)) := by
  norm_num [atom0691, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0691_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (353829120 : Int) atom0691) := by
  rw [SparsePolynomial.eval_scale, eval_atom0691]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0691Coded : CoefficientMerge.Poly := [(nat_lit 1429, Int.ofNat (nat_lit 1))]
theorem atom0691Coded_decode : atom0691 = SparsePolynomial.decodeCubic 18 atom0691Coded := by decide +kernel
theorem atom0691Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (353829120 : Int) atom0691Coded) := by
  have h := atom0691_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0691Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0692 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0692 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0692 = ((g 4) * (g 7) * (g 8)) := by
  norm_num [atom0692, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0692_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (403703040 : Int) atom0692) := by
  rw [SparsePolynomial.eval_scale, eval_atom0692]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0692Coded : CoefficientMerge.Poly := [(nat_lit 1430, Int.ofNat (nat_lit 1))]
theorem atom0692Coded_decode : atom0692 = SparsePolynomial.decodeCubic 18 atom0692Coded := by decide +kernel
theorem atom0692Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (403703040 : Int) atom0692Coded) := by
  have h := atom0692_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0692Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0693 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0693 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0693 = ((g 4) * (g 7) * (g 9)) := by
  norm_num [atom0693, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0693_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (460473600 : Int) atom0693) := by
  rw [SparsePolynomial.eval_scale, eval_atom0693]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0693Coded : CoefficientMerge.Poly := [(nat_lit 1431, Int.ofNat (nat_lit 1))]
theorem atom0693Coded_decode : atom0693 = SparsePolynomial.decodeCubic 18 atom0693Coded := by decide +kernel
theorem atom0693Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (460473600 : Int) atom0693Coded) := by
  have h := atom0693_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0693Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0694 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0694 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0694 = ((g 4) * (g 7) * (g 10)) := by
  norm_num [atom0694, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0694_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (621108480 : Int) atom0694) := by
  rw [SparsePolynomial.eval_scale, eval_atom0694]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0694Coded : CoefficientMerge.Poly := [(nat_lit 1432, Int.ofNat (nat_lit 1))]
theorem atom0694Coded_decode : atom0694 = SparsePolynomial.decodeCubic 18 atom0694Coded := by decide +kernel
theorem atom0694Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (621108480 : Int) atom0694Coded) := by
  have h := atom0694_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0694Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0695 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0695 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0695 = ((g 4) * (g 7) * (g 11)) := by
  norm_num [atom0695, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0695_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (781743360 : Int) atom0695) := by
  rw [SparsePolynomial.eval_scale, eval_atom0695]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0695Coded : CoefficientMerge.Poly := [(nat_lit 1433, Int.ofNat (nat_lit 1))]
theorem atom0695Coded_decode : atom0695 = SparsePolynomial.decodeCubic 18 atom0695Coded := by decide +kernel
theorem atom0695Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (781743360 : Int) atom0695Coded) := by
  have h := atom0695_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0695Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0696 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0696 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0696 = ((g 4) * (g 7) * (g 12)) := by
  norm_num [atom0696, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0696_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3019296000 : Int) atom0696) := by
  rw [SparsePolynomial.eval_scale, eval_atom0696]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0696Coded : CoefficientMerge.Poly := [(nat_lit 1434, Int.ofNat (nat_lit 1))]
theorem atom0696Coded_decode : atom0696 = SparsePolynomial.decodeCubic 18 atom0696Coded := by decide +kernel
theorem atom0696Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3019296000 : Int) atom0696Coded) := by
  have h := atom0696_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0696Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0697 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0697 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0697 = ((g 4) * (g 7) * (g 13)) := by
  norm_num [atom0697, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0697_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2332497120 : Int) atom0697) := by
  rw [SparsePolynomial.eval_scale, eval_atom0697]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0697Coded : CoefficientMerge.Poly := [(nat_lit 1435, Int.ofNat (nat_lit 1))]
theorem atom0697Coded_decode : atom0697 = SparsePolynomial.decodeCubic 18 atom0697Coded := by decide +kernel
theorem atom0697Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2332497120 : Int) atom0697Coded) := by
  have h := atom0697_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0697Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0698 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0698 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0698 = ((g 4) * (g 7) * (g 14)) := by
  norm_num [atom0698, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0698_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4135339680 : Int) atom0698) := by
  rw [SparsePolynomial.eval_scale, eval_atom0698]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0698Coded : CoefficientMerge.Poly := [(nat_lit 1436, Int.ofNat (nat_lit 1))]
theorem atom0698Coded_decode : atom0698 = SparsePolynomial.decodeCubic 18 atom0698Coded := by decide +kernel
theorem atom0698Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4135339680 : Int) atom0698Coded) := by
  have h := atom0698_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0698Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0699 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0699 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0699 = ((g 4) * (g 7) * (g 15)) := by
  norm_num [atom0699, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0699_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5254997280 : Int) atom0699) := by
  rw [SparsePolynomial.eval_scale, eval_atom0699]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0699Coded : CoefficientMerge.Poly := [(nat_lit 1437, Int.ofNat (nat_lit 1))]
theorem atom0699Coded_decode : atom0699 = SparsePolynomial.decodeCubic 18 atom0699Coded := by decide +kernel
theorem atom0699Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5254997280 : Int) atom0699Coded) := by
  have h := atom0699_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0699Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0700 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0700 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0700 = ((g 4) * (g 7) * (g 16)) := by
  norm_num [atom0700, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0700_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7178238240 : Int) atom0700) := by
  rw [SparsePolynomial.eval_scale, eval_atom0700]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0700Coded : CoefficientMerge.Poly := [(nat_lit 1438, Int.ofNat (nat_lit 1))]
theorem atom0700Coded_decode : atom0700 = SparsePolynomial.decodeCubic 18 atom0700Coded := by decide +kernel
theorem atom0700Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7178238240 : Int) atom0700Coded) := by
  have h := atom0700_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0700Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0701 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 7, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0701 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0701 = ((g 4) * (g 7) * (g 17)) := by
  norm_num [atom0701, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0701_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9115705440 : Int) atom0701) := by
  rw [SparsePolynomial.eval_scale, eval_atom0701]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0701Coded : CoefficientMerge.Poly := [(nat_lit 1439, Int.ofNat (nat_lit 1))]
theorem atom0701Coded_decode : atom0701 = SparsePolynomial.decodeCubic 18 atom0701Coded := by decide +kernel
theorem atom0701Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9115705440 : Int) atom0701Coded) := by
  have h := atom0701_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0701Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0702 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0702 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0702 = ((g 4) * (g 8) * (g 8)) := by
  norm_num [atom0702, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0702_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (827243520 : Int) atom0702) := by
  rw [SparsePolynomial.eval_scale, eval_atom0702]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0702Coded : CoefficientMerge.Poly := [(nat_lit 1448, Int.ofNat (nat_lit 1))]
theorem atom0702Coded_decode : atom0702 = SparsePolynomial.decodeCubic 18 atom0702Coded := by decide +kernel
theorem atom0702Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (827243520 : Int) atom0702Coded) := by
  have h := atom0702_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0702Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0703 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0703 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0703 = ((g 4) * (g 8) * (g 9)) := by
  norm_num [atom0703, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0703_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1400517120 : Int) atom0703) := by
  rw [SparsePolynomial.eval_scale, eval_atom0703]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0703Coded : CoefficientMerge.Poly := [(nat_lit 1449, Int.ofNat (nat_lit 1))]
theorem atom0703Coded_decode : atom0703 = SparsePolynomial.decodeCubic 18 atom0703Coded := by decide +kernel
theorem atom0703Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1400517120 : Int) atom0703Coded) := by
  have h := atom0703_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0703Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0704 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0704 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0704 = ((g 4) * (g 8) * (g 10)) := by
  norm_num [atom0704, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0704_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1514058240 : Int) atom0704) := by
  rw [SparsePolynomial.eval_scale, eval_atom0704]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0704Coded : CoefficientMerge.Poly := [(nat_lit 1450, Int.ofNat (nat_lit 1))]
theorem atom0704Coded_decode : atom0704 = SparsePolynomial.decodeCubic 18 atom0704Coded := by decide +kernel
theorem atom0704Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1514058240 : Int) atom0704Coded) := by
  have h := atom0704_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0704Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0705 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0705 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0705 = ((g 4) * (g 8) * (g 11)) := by
  norm_num [atom0705, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0705_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1627599360 : Int) atom0705) := by
  rw [SparsePolynomial.eval_scale, eval_atom0705]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0705Coded : CoefficientMerge.Poly := [(nat_lit 1451, Int.ofNat (nat_lit 1))]
theorem atom0705Coded_decode : atom0705 = SparsePolynomial.decodeCubic 18 atom0705Coded := by decide +kernel
theorem atom0705Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1627599360 : Int) atom0705Coded) := by
  have h := atom0705_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0705Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0706 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0706 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0706 = ((g 4) * (g 8) * (g 12)) := by
  norm_num [atom0706, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0706_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3755136000 : Int) atom0706) := by
  rw [SparsePolynomial.eval_scale, eval_atom0706]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0706Coded : CoefficientMerge.Poly := [(nat_lit 1452, Int.ofNat (nat_lit 1))]
theorem atom0706Coded_decode : atom0706 = SparsePolynomial.decodeCubic 18 atom0706Coded := by decide +kernel
theorem atom0706Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3755136000 : Int) atom0706Coded) := by
  have h := atom0706_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0706Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0707 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0707 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0707 = ((g 4) * (g 8) * (g 13)) := by
  norm_num [atom0707, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0707_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3303554880 : Int) atom0707) := by
  rw [SparsePolynomial.eval_scale, eval_atom0707]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0707Coded : CoefficientMerge.Poly := [(nat_lit 1453, Int.ofNat (nat_lit 1))]
theorem atom0707Coded_decode : atom0707 = SparsePolynomial.decodeCubic 18 atom0707Coded := by decide +kernel
theorem atom0707Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3303554880 : Int) atom0707Coded) := by
  have h := atom0707_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0707Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0708 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0708 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0708 = ((g 4) * (g 8) * (g 14)) := by
  norm_num [atom0708, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0708_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5488183200 : Int) atom0708) := by
  rw [SparsePolynomial.eval_scale, eval_atom0708]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0708Coded : CoefficientMerge.Poly := [(nat_lit 1454, Int.ofNat (nat_lit 1))]
theorem atom0708Coded_decode : atom0708 = SparsePolynomial.decodeCubic 18 atom0708Coded := by decide +kernel
theorem atom0708Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5488183200 : Int) atom0708Coded) := by
  have h := atom0708_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0708Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0709 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0709 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0709 = ((g 4) * (g 8) * (g 15)) := by
  norm_num [atom0709, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0709_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6428383680 : Int) atom0709) := by
  rw [SparsePolynomial.eval_scale, eval_atom0709]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0709Coded : CoefficientMerge.Poly := [(nat_lit 1455, Int.ofNat (nat_lit 1))]
theorem atom0709Coded_decode : atom0709 = SparsePolynomial.decodeCubic 18 atom0709Coded := by decide +kernel
theorem atom0709Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6428383680 : Int) atom0709Coded) := by
  have h := atom0709_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0709Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0710 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0710 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0710 = ((g 4) * (g 8) * (g 16)) := by
  norm_num [atom0710, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0710_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8473755840 : Int) atom0710) := by
  rw [SparsePolynomial.eval_scale, eval_atom0710]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0710Coded : CoefficientMerge.Poly := [(nat_lit 1456, Int.ofNat (nat_lit 1))]
theorem atom0710Coded_decode : atom0710 = SparsePolynomial.decodeCubic 18 atom0710Coded := by decide +kernel
theorem atom0710Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8473755840 : Int) atom0710Coded) := by
  have h := atom0710_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0710Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0711 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0711 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0711 = ((g 4) * (g 8) * (g 17)) := by
  norm_num [atom0711, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0711_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10519128000 : Int) atom0711) := by
  rw [SparsePolynomial.eval_scale, eval_atom0711]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0711Coded : CoefficientMerge.Poly := [(nat_lit 1457, Int.ofNat (nat_lit 1))]
theorem atom0711Coded_decode : atom0711 = SparsePolynomial.decodeCubic 18 atom0711Coded := by decide +kernel
theorem atom0711Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10519128000 : Int) atom0711Coded) := by
  have h := atom0711_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0711Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0712 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0712 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0712 = ((g 4) * (g 9) * (g 9)) := by
  norm_num [atom0712, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0712_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1454507520 : Int) atom0712) := by
  rw [SparsePolynomial.eval_scale, eval_atom0712]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0712Coded : CoefficientMerge.Poly := [(nat_lit 1467, Int.ofNat (nat_lit 1))]
theorem atom0712Coded_decode : atom0712 = SparsePolynomial.decodeCubic 18 atom0712Coded := by decide +kernel
theorem atom0712Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1454507520 : Int) atom0712Coded) := by
  have h := atom0712_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0712Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0713 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0713 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0713 = ((g 4) * (g 9) * (g 10)) := by
  norm_num [atom0713, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0713_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2574428160 : Int) atom0713) := by
  rw [SparsePolynomial.eval_scale, eval_atom0713]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0713Coded : CoefficientMerge.Poly := [(nat_lit 1468, Int.ofNat (nat_lit 1))]
theorem atom0713Coded_decode : atom0713 = SparsePolynomial.decodeCubic 18 atom0713Coded := by decide +kernel
theorem atom0713Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2574428160 : Int) atom0713Coded) := by
  have h := atom0713_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0713Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0714 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0714 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0714 = ((g 4) * (g 9) * (g 11)) := by
  norm_num [atom0714, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0714_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2590556160 : Int) atom0714) := by
  rw [SparsePolynomial.eval_scale, eval_atom0714]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0714Coded : CoefficientMerge.Poly := [(nat_lit 1469, Int.ofNat (nat_lit 1))]
theorem atom0714Coded_decode : atom0714 = SparsePolynomial.decodeCubic 18 atom0714Coded := by decide +kernel
theorem atom0714Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2590556160 : Int) atom0714Coded) := by
  have h := atom0714_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0714Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0715 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0715 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0715 = ((g 4) * (g 9) * (g 12)) := by
  norm_num [atom0715, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0715_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4644494400 : Int) atom0715) := by
  rw [SparsePolynomial.eval_scale, eval_atom0715]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0715Coded : CoefficientMerge.Poly := [(nat_lit 1470, Int.ofNat (nat_lit 1))]
theorem atom0715Coded_decode : atom0715 = SparsePolynomial.decodeCubic 18 atom0715Coded := by decide +kernel
theorem atom0715Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4644494400 : Int) atom0715Coded) := by
  have h := atom0715_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0715Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0716 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0716 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0716 = ((g 4) * (g 9) * (g 13)) := by
  norm_num [atom0716, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0716_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4143129600 : Int) atom0716) := by
  rw [SparsePolynomial.eval_scale, eval_atom0716]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0716Coded : CoefficientMerge.Poly := [(nat_lit 1471, Int.ofNat (nat_lit 1))]
theorem atom0716Coded_decode : atom0716 = SparsePolynomial.decodeCubic 18 atom0716Coded := by decide +kernel
theorem atom0716Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4143129600 : Int) atom0716Coded) := by
  have h := atom0716_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0716Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0717 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0717 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0717 = ((g 4) * (g 9) * (g 14)) := by
  norm_num [atom0717, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0717_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6663591840 : Int) atom0717) := by
  rw [SparsePolynomial.eval_scale, eval_atom0717]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0717Coded : CoefficientMerge.Poly := [(nat_lit 1472, Int.ofNat (nat_lit 1))]
theorem atom0717Coded_decode : atom0717 = SparsePolynomial.decodeCubic 18 atom0717Coded := by decide +kernel
theorem atom0717Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6663591840 : Int) atom0717Coded) := by
  have h := atom0717_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0717Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0718 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0718 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0718 = ((g 4) * (g 9) * (g 15)) := by
  norm_num [atom0718, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0718_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7216020480 : Int) atom0718) := by
  rw [SparsePolynomial.eval_scale, eval_atom0718]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0718Coded : CoefficientMerge.Poly := [(nat_lit 1473, Int.ofNat (nat_lit 1))]
theorem atom0718Coded_decode : atom0718 = SparsePolynomial.decodeCubic 18 atom0718Coded := by decide +kernel
theorem atom0718Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7216020480 : Int) atom0718Coded) := by
  have h := atom0718_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0718Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0719 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0719 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0719 = ((g 4) * (g 9) * (g 16)) := by
  norm_num [atom0719, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0719_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9259238400 : Int) atom0719) := by
  rw [SparsePolynomial.eval_scale, eval_atom0719]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0719Coded : CoefficientMerge.Poly := [(nat_lit 1474, Int.ofNat (nat_lit 1))]
theorem atom0719Coded_decode : atom0719 = SparsePolynomial.decodeCubic 18 atom0719Coded := by decide +kernel
theorem atom0719Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9259238400 : Int) atom0719Coded) := by
  have h := atom0719_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0719Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0720 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0720 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0720 = ((g 4) * (g 9) * (g 17)) := by
  norm_num [atom0720, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0720_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11302456320 : Int) atom0720) := by
  rw [SparsePolynomial.eval_scale, eval_atom0720]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0720Coded : CoefficientMerge.Poly := [(nat_lit 1475, Int.ofNat (nat_lit 1))]
theorem atom0720Coded_decode : atom0720 = SparsePolynomial.decodeCubic 18 atom0720Coded := by decide +kernel
theorem atom0720Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11302456320 : Int) atom0720Coded) := by
  have h := atom0720_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0720Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0721 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0721 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0721 = ((g 4) * (g 10) * (g 10)) := by
  norm_num [atom0721, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0721_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2105018880 : Int) atom0721) := by
  rw [SparsePolynomial.eval_scale, eval_atom0721]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0721Coded : CoefficientMerge.Poly := [(nat_lit 1486, Int.ofNat (nat_lit 1))]
theorem atom0721Coded_decode : atom0721 = SparsePolynomial.decodeCubic 18 atom0721Coded := by decide +kernel
theorem atom0721Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2105018880 : Int) atom0721Coded) := by
  have h := atom0721_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0721Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0722 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0722 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0722 = ((g 4) * (g 10) * (g 11)) := by
  norm_num [atom0722, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0722_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3744445440 : Int) atom0722) := by
  rw [SparsePolynomial.eval_scale, eval_atom0722]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0722Coded : CoefficientMerge.Poly := [(nat_lit 1487, Int.ofNat (nat_lit 1))]
theorem atom0722Coded_decode : atom0722 = SparsePolynomial.decodeCubic 18 atom0722Coded := by decide +kernel
theorem atom0722Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3744445440 : Int) atom0722Coded) := by
  have h := atom0722_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0722Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0723 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0723 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0723 = ((g 4) * (g 10) * (g 12)) := by
  norm_num [atom0723, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0723_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5639632320 : Int) atom0723) := by
  rw [SparsePolynomial.eval_scale, eval_atom0723]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0723Coded : CoefficientMerge.Poly := [(nat_lit 1488, Int.ofNat (nat_lit 1))]
theorem atom0723Coded_decode : atom0723 = SparsePolynomial.decodeCubic 18 atom0723Coded := by decide +kernel
theorem atom0723Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5639632320 : Int) atom0723Coded) := by
  have h := atom0723_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0723Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0724 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0724 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0724 = ((g 4) * (g 10) * (g 13)) := by
  norm_num [atom0724, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0724_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4968497280 : Int) atom0724) := by
  rw [SparsePolynomial.eval_scale, eval_atom0724]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0724Coded : CoefficientMerge.Poly := [(nat_lit 1489, Int.ofNat (nat_lit 1))]
theorem atom0724Coded_decode : atom0724 = SparsePolynomial.decodeCubic 18 atom0724Coded := by decide +kernel
theorem atom0724Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4968497280 : Int) atom0724Coded) := by
  have h := atom0724_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0724Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0725 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0725 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0725 = ((g 4) * (g 10) * (g 14)) := by
  norm_num [atom0725, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0725_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7889319840 : Int) atom0725) := by
  rw [SparsePolynomial.eval_scale, eval_atom0725]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0725Coded : CoefficientMerge.Poly := [(nat_lit 1490, Int.ofNat (nat_lit 1))]
theorem atom0725Coded_decode : atom0725 = SparsePolynomial.decodeCubic 18 atom0725Coded := by decide +kernel
theorem atom0725Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7889319840 : Int) atom0725Coded) := by
  have h := atom0725_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0725Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0726 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0726 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0726 = ((g 4) * (g 10) * (g 15)) := by
  norm_num [atom0726, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0726_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7679809920 : Int) atom0726) := by
  rw [SparsePolynomial.eval_scale, eval_atom0726]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0726Coded : CoefficientMerge.Poly := [(nat_lit 1491, Int.ofNat (nat_lit 1))]
theorem atom0726Coded_decode : atom0726 = SparsePolynomial.decodeCubic 18 atom0726Coded := by decide +kernel
theorem atom0726Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7679809920 : Int) atom0726Coded) := by
  have h := atom0726_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0726Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0727 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0727 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0727 = ((g 4) * (g 10) * (g 16)) := by
  norm_num [atom0727, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0727_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9531219840 : Int) atom0727) := by
  rw [SparsePolynomial.eval_scale, eval_atom0727]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0727Coded : CoefficientMerge.Poly := [(nat_lit 1492, Int.ofNat (nat_lit 1))]
theorem atom0727Coded_decode : atom0727 = SparsePolynomial.decodeCubic 18 atom0727Coded := by decide +kernel
theorem atom0727Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9531219840 : Int) atom0727Coded) := by
  have h := atom0727_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0727Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0728 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0728 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0728 = ((g 4) * (g 10) * (g 17)) := by
  norm_num [atom0728, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0728_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11673385920 : Int) atom0728) := by
  rw [SparsePolynomial.eval_scale, eval_atom0728]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0728Coded : CoefficientMerge.Poly := [(nat_lit 1493, Int.ofNat (nat_lit 1))]
theorem atom0728Coded_decode : atom0728 = SparsePolynomial.decodeCubic 18 atom0728Coded := by decide +kernel
theorem atom0728Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11673385920 : Int) atom0728Coded) := by
  have h := atom0728_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0728Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0729 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0729 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0729 = ((g 4) * (g 11) * (g 11)) := by
  norm_num [atom0729, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0729_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2958144000 : Int) atom0729) := by
  rw [SparsePolynomial.eval_scale, eval_atom0729]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0729Coded : CoefficientMerge.Poly := [(nat_lit 1505, Int.ofNat (nat_lit 1))]
theorem atom0729Coded_decode : atom0729 = SparsePolynomial.decodeCubic 18 atom0729Coded := by decide +kernel
theorem atom0729Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2958144000 : Int) atom0729Coded) := by
  have h := atom0729_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0729Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0730 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0730 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0730 = ((g 4) * (g 11) * (g 12)) := by
  norm_num [atom0730, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0730_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6511653120 : Int) atom0730) := by
  rw [SparsePolynomial.eval_scale, eval_atom0730]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0730Coded : CoefficientMerge.Poly := [(nat_lit 1506, Int.ofNat (nat_lit 1))]
theorem atom0730Coded_decode : atom0730 = SparsePolynomial.decodeCubic 18 atom0730Coded := by decide +kernel
theorem atom0730Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6511653120 : Int) atom0730Coded) := by
  have h := atom0730_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0730Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0731 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0731 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0731 = ((g 4) * (g 11) * (g 13)) := by
  norm_num [atom0731, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0731_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5589568320 : Int) atom0731) := by
  rw [SparsePolynomial.eval_scale, eval_atom0731]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0731Coded : CoefficientMerge.Poly := [(nat_lit 1507, Int.ofNat (nat_lit 1))]
theorem atom0731Coded_decode : atom0731 = SparsePolynomial.decodeCubic 18 atom0731Coded := by decide +kernel
theorem atom0731Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5589568320 : Int) atom0731Coded) := by
  have h := atom0731_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0731Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0732 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0732 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0732 = ((g 4) * (g 11) * (g 14)) := by
  norm_num [atom0732, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0732_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8928903840 : Int) atom0732) := by
  rw [SparsePolynomial.eval_scale, eval_atom0732]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0732Coded : CoefficientMerge.Poly := [(nat_lit 1508, Int.ofNat (nat_lit 1))]
theorem atom0732Coded_decode : atom0732 = SparsePolynomial.decodeCubic 18 atom0732Coded := by decide +kernel
theorem atom0732Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8928903840 : Int) atom0732Coded) := by
  have h := atom0732_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0732Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0733 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0733 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0733 = ((g 4) * (g 11) * (g 15)) := by
  norm_num [atom0733, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0733_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8835408960 : Int) atom0733) := by
  rw [SparsePolynomial.eval_scale, eval_atom0733]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0733Coded : CoefficientMerge.Poly := [(nat_lit 1509, Int.ofNat (nat_lit 1))]
theorem atom0733Coded_decode : atom0733 = SparsePolynomial.decodeCubic 18 atom0733Coded := by decide +kernel
theorem atom0733Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8835408960 : Int) atom0733Coded) := by
  have h := atom0733_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0733Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0734 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0734 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0734 = ((g 4) * (g 11) * (g 16)) := by
  norm_num [atom0734, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0734_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9405332160 : Int) atom0734) := by
  rw [SparsePolynomial.eval_scale, eval_atom0734]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0734Coded : CoefficientMerge.Poly := [(nat_lit 1510, Int.ofNat (nat_lit 1))]
theorem atom0734Coded_decode : atom0734 = SparsePolynomial.decodeCubic 18 atom0734Coded := by decide +kernel
theorem atom0734Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9405332160 : Int) atom0734Coded) := by
  have h := atom0734_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0734Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block009 : CoefficientMerge.Poly := [(nat_lit 1238, Int.ofNat (nat_lit 8141283000)), (nat_lit 1239, Int.ofNat (nat_lit 12793243320)), (nat_lit 1240, Int.ofNat (nat_lit 8558934480)), (nat_lit 1241, Int.ofNat (nat_lit 11377463760)), (nat_lit 1257, Int.ofNat (nat_lit 4082641920)), (nat_lit 1258, Int.ofNat (nat_lit 5228697600)), (nat_lit 1259, Int.ofNat (nat_lit 8587353600)), (nat_lit 1276, Int.ofNat (nat_lit 258048000)), (nat_lit 1277, Int.ofNat (nat_lit 4255534080)), (nat_lit 1295, Int.ofNat (nat_lit 3789918720)), (nat_lit 1372, Int.ofNat (nat_lit 839677440)), (nat_lit 1373, Int.ofNat (nat_lit 1603536000)), (nat_lit 1374, Int.ofNat (nat_lit 615212160)), (nat_lit 1375, Int.ofNat (nat_lit 103864320)), (nat_lit 1376, Int.ofNat (nat_lit 25159680)), (nat_lit 1380, Int.ofNat (nat_lit 1531037760)), (nat_lit 1382, Int.ofNat (nat_lit 460951440)), (nat_lit 1391, Int.ofNat (nat_lit 1465409280)), (nat_lit 1392, Int.ofNat (nat_lit 1111580160)), (nat_lit 1396, Int.ofNat (nat_lit 103864320)), (nat_lit 1397, Int.ofNat (nat_lit 207728640)), (nat_lit 1398, Int.ofNat (nat_lit 2424376752)), (nat_lit 1400, Int.ofNat (nat_lit 1101237360)), (nat_lit 1401, Int.ofNat (nat_lit 1180247040)), (nat_lit 1402, Int.ofNat (nat_lit 2293143552)), (nat_lit 1403, Int.ofNat (nat_lit 3586383360)), (nat_lit 1410, Int.ofNat (nat_lit 423540480)), (nat_lit 1413, Int.ofNat (nat_lit 107089920)), (nat_lit 1414, Int.ofNat (nat_lit 264499200)), (nat_lit 1415, Int.ofNat (nat_lit 421908480)), (nat_lit 1416, Int.ofNat (nat_lit 2576627520)), (nat_lit 1417, Int.ofNat (nat_lit 1293281520)), (nat_lit 1418, Int.ofNat (nat_lit 2694257760)), (nat_lit 1419, Int.ofNat (nat_lit 3482496240)), (nat_lit 1420, Int.ofNat (nat_lit 5041760400)), (nat_lit 1421, Int.ofNat (nat_lit 6677153280)), (nat_lit 1429, Int.ofNat (nat_lit 353829120)), (nat_lit 1430, Int.ofNat (nat_lit 403703040)), (nat_lit 1431, Int.ofNat (nat_lit 460473600)), (nat_lit 1432, Int.ofNat (nat_lit 621108480)), (nat_lit 1433, Int.ofNat (nat_lit 781743360)), (nat_lit 1434, Int.ofNat (nat_lit 3019296000)), (nat_lit 1435, Int.ofNat (nat_lit 2332497120)), (nat_lit 1436, Int.ofNat (nat_lit 4135339680)), (nat_lit 1437, Int.ofNat (nat_lit 5254997280)), (nat_lit 1438, Int.ofNat (nat_lit 7178238240)), (nat_lit 1439, Int.ofNat (nat_lit 9115705440)), (nat_lit 1448, Int.ofNat (nat_lit 827243520)), (nat_lit 1449, Int.ofNat (nat_lit 1400517120)), (nat_lit 1450, Int.ofNat (nat_lit 1514058240)), (nat_lit 1451, Int.ofNat (nat_lit 1627599360)), (nat_lit 1452, Int.ofNat (nat_lit 3755136000)), (nat_lit 1453, Int.ofNat (nat_lit 3303554880)), (nat_lit 1454, Int.ofNat (nat_lit 5488183200)), (nat_lit 1455, Int.ofNat (nat_lit 6428383680)), (nat_lit 1456, Int.ofNat (nat_lit 8473755840)), (nat_lit 1457, Int.ofNat (nat_lit 10519128000)), (nat_lit 1467, Int.ofNat (nat_lit 1454507520)), (nat_lit 1468, Int.ofNat (nat_lit 2574428160)), (nat_lit 1469, Int.ofNat (nat_lit 2590556160)), (nat_lit 1470, Int.ofNat (nat_lit 4644494400)), (nat_lit 1471, Int.ofNat (nat_lit 4143129600)), (nat_lit 1472, Int.ofNat (nat_lit 6663591840)), (nat_lit 1473, Int.ofNat (nat_lit 7216020480)), (nat_lit 1474, Int.ofNat (nat_lit 9259238400)), (nat_lit 1475, Int.ofNat (nat_lit 11302456320)), (nat_lit 1486, Int.ofNat (nat_lit 2105018880)), (nat_lit 1487, Int.ofNat (nat_lit 3744445440)), (nat_lit 1488, Int.ofNat (nat_lit 5639632320)), (nat_lit 1489, Int.ofNat (nat_lit 4968497280)), (nat_lit 1490, Int.ofNat (nat_lit 7889319840)), (nat_lit 1491, Int.ofNat (nat_lit 7679809920)), (nat_lit 1492, Int.ofNat (nat_lit 9531219840)), (nat_lit 1493, Int.ofNat (nat_lit 11673385920)), (nat_lit 1505, Int.ofNat (nat_lit 2958144000)), (nat_lit 1506, Int.ofNat (nat_lit 6511653120)), (nat_lit 1507, Int.ofNat (nat_lit 5589568320)), (nat_lit 1508, Int.ofNat (nat_lit 8928903840)), (nat_lit 1509, Int.ofNat (nat_lit 8835408960)), (nat_lit 1510, Int.ofNat (nat_lit 9405332160))]
def block009_data_flat000 : CoefficientMerge.Poly := [(nat_lit 1238, Int.ofNat (nat_lit 8141283000))]
theorem block009_data_flat000_step : block009_data_flat000 = (CoefficientMerge.scale (8141283000 : Int) atom0655Coded) := by decide +kernel
theorem block009_data_flat000_original : block009_data_flat000 = (CoefficientMerge.scale (8141283000 : Int) atom0655Coded) := by
  rw [block009_data_flat000_step]
def block009_data_flat001 : CoefficientMerge.Poly := [(nat_lit 1239, Int.ofNat (nat_lit 12793243320))]
theorem block009_data_flat001_step : block009_data_flat001 = (CoefficientMerge.scale (12793243320 : Int) atom0656Coded) := by decide +kernel
theorem block009_data_flat001_original : block009_data_flat001 = (CoefficientMerge.scale (12793243320 : Int) atom0656Coded) := by
  rw [block009_data_flat001_step]
def block009_data_flat002 : CoefficientMerge.Poly := [(nat_lit 1238, Int.ofNat (nat_lit 8141283000)), (nat_lit 1239, Int.ofNat (nat_lit 12793243320))]
theorem block009_data_flat002_step : block009_data_flat002 = (CoefficientMerge.fastMerge block009_data_flat000 block009_data_flat001) := by decide +kernel
theorem block009_data_flat002_original : block009_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8141283000 : Int) atom0655Coded) (CoefficientMerge.scale (12793243320 : Int) atom0656Coded)) := by
  rw [block009_data_flat002_step, block009_data_flat000_original, block009_data_flat001_original]
def block009_data_flat003 : CoefficientMerge.Poly := [(nat_lit 1240, Int.ofNat (nat_lit 8558934480))]
theorem block009_data_flat003_step : block009_data_flat003 = (CoefficientMerge.scale (8558934480 : Int) atom0657Coded) := by decide +kernel
theorem block009_data_flat003_original : block009_data_flat003 = (CoefficientMerge.scale (8558934480 : Int) atom0657Coded) := by
  rw [block009_data_flat003_step]
def block009_data_flat004 : CoefficientMerge.Poly := [(nat_lit 1241, Int.ofNat (nat_lit 11377463760))]
theorem block009_data_flat004_step : block009_data_flat004 = (CoefficientMerge.scale (11377463760 : Int) atom0658Coded) := by decide +kernel
theorem block009_data_flat004_original : block009_data_flat004 = (CoefficientMerge.scale (11377463760 : Int) atom0658Coded) := by
  rw [block009_data_flat004_step]
def block009_data_flat005 : CoefficientMerge.Poly := [(nat_lit 1257, Int.ofNat (nat_lit 4082641920))]
theorem block009_data_flat005_step : block009_data_flat005 = (CoefficientMerge.scale (4082641920 : Int) atom0659Coded) := by decide +kernel
theorem block009_data_flat005_original : block009_data_flat005 = (CoefficientMerge.scale (4082641920 : Int) atom0659Coded) := by
  rw [block009_data_flat005_step]
def block009_data_flat006 : CoefficientMerge.Poly := [(nat_lit 1241, Int.ofNat (nat_lit 11377463760)), (nat_lit 1257, Int.ofNat (nat_lit 4082641920))]
theorem block009_data_flat006_step : block009_data_flat006 = (CoefficientMerge.fastMerge block009_data_flat004 block009_data_flat005) := by decide +kernel
theorem block009_data_flat006_original : block009_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11377463760 : Int) atom0658Coded) (CoefficientMerge.scale (4082641920 : Int) atom0659Coded)) := by
  rw [block009_data_flat006_step, block009_data_flat004_original, block009_data_flat005_original]
def block009_data_flat007 : CoefficientMerge.Poly := [(nat_lit 1240, Int.ofNat (nat_lit 8558934480)), (nat_lit 1241, Int.ofNat (nat_lit 11377463760)), (nat_lit 1257, Int.ofNat (nat_lit 4082641920))]
theorem block009_data_flat007_step : block009_data_flat007 = (CoefficientMerge.fastMerge block009_data_flat003 block009_data_flat006) := by decide +kernel
theorem block009_data_flat007_original : block009_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8558934480 : Int) atom0657Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11377463760 : Int) atom0658Coded) (CoefficientMerge.scale (4082641920 : Int) atom0659Coded))) := by
  rw [block009_data_flat007_step, block009_data_flat003_original, block009_data_flat006_original]
def block009_data_flat008 : CoefficientMerge.Poly := [(nat_lit 1238, Int.ofNat (nat_lit 8141283000)), (nat_lit 1239, Int.ofNat (nat_lit 12793243320)), (nat_lit 1240, Int.ofNat (nat_lit 8558934480)), (nat_lit 1241, Int.ofNat (nat_lit 11377463760)), (nat_lit 1257, Int.ofNat (nat_lit 4082641920))]
theorem block009_data_flat008_step : block009_data_flat008 = (CoefficientMerge.fastMerge block009_data_flat002 block009_data_flat007) := by decide +kernel
theorem block009_data_flat008_original : block009_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8141283000 : Int) atom0655Coded) (CoefficientMerge.scale (12793243320 : Int) atom0656Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8558934480 : Int) atom0657Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11377463760 : Int) atom0658Coded) (CoefficientMerge.scale (4082641920 : Int) atom0659Coded)))) := by
  rw [block009_data_flat008_step, block009_data_flat002_original, block009_data_flat007_original]
def block009_data_flat009 : CoefficientMerge.Poly := [(nat_lit 1258, Int.ofNat (nat_lit 5228697600))]
theorem block009_data_flat009_step : block009_data_flat009 = (CoefficientMerge.scale (5228697600 : Int) atom0660Coded) := by decide +kernel
theorem block009_data_flat009_original : block009_data_flat009 = (CoefficientMerge.scale (5228697600 : Int) atom0660Coded) := by
  rw [block009_data_flat009_step]
def block009_data_flat010 : CoefficientMerge.Poly := [(nat_lit 1259, Int.ofNat (nat_lit 8587353600))]
theorem block009_data_flat010_step : block009_data_flat010 = (CoefficientMerge.scale (8587353600 : Int) atom0661Coded) := by decide +kernel
theorem block009_data_flat010_original : block009_data_flat010 = (CoefficientMerge.scale (8587353600 : Int) atom0661Coded) := by
  rw [block009_data_flat010_step]
def block009_data_flat011 : CoefficientMerge.Poly := [(nat_lit 1258, Int.ofNat (nat_lit 5228697600)), (nat_lit 1259, Int.ofNat (nat_lit 8587353600))]
theorem block009_data_flat011_step : block009_data_flat011 = (CoefficientMerge.fastMerge block009_data_flat009 block009_data_flat010) := by decide +kernel
theorem block009_data_flat011_original : block009_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5228697600 : Int) atom0660Coded) (CoefficientMerge.scale (8587353600 : Int) atom0661Coded)) := by
  rw [block009_data_flat011_step, block009_data_flat009_original, block009_data_flat010_original]
def block009_data_flat012 : CoefficientMerge.Poly := [(nat_lit 1276, Int.ofNat (nat_lit 258048000))]
theorem block009_data_flat012_step : block009_data_flat012 = (CoefficientMerge.scale (258048000 : Int) atom0662Coded) := by decide +kernel
theorem block009_data_flat012_original : block009_data_flat012 = (CoefficientMerge.scale (258048000 : Int) atom0662Coded) := by
  rw [block009_data_flat012_step]
def block009_data_flat013 : CoefficientMerge.Poly := [(nat_lit 1277, Int.ofNat (nat_lit 4255534080))]
theorem block009_data_flat013_step : block009_data_flat013 = (CoefficientMerge.scale (4255534080 : Int) atom0663Coded) := by decide +kernel
theorem block009_data_flat013_original : block009_data_flat013 = (CoefficientMerge.scale (4255534080 : Int) atom0663Coded) := by
  rw [block009_data_flat013_step]
def block009_data_flat014 : CoefficientMerge.Poly := [(nat_lit 1295, Int.ofNat (nat_lit 3789918720))]
theorem block009_data_flat014_step : block009_data_flat014 = (CoefficientMerge.scale (3789918720 : Int) atom0664Coded) := by decide +kernel
theorem block009_data_flat014_original : block009_data_flat014 = (CoefficientMerge.scale (3789918720 : Int) atom0664Coded) := by
  rw [block009_data_flat014_step]
def block009_data_flat015 : CoefficientMerge.Poly := [(nat_lit 1277, Int.ofNat (nat_lit 4255534080)), (nat_lit 1295, Int.ofNat (nat_lit 3789918720))]
theorem block009_data_flat015_step : block009_data_flat015 = (CoefficientMerge.fastMerge block009_data_flat013 block009_data_flat014) := by decide +kernel
theorem block009_data_flat015_original : block009_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4255534080 : Int) atom0663Coded) (CoefficientMerge.scale (3789918720 : Int) atom0664Coded)) := by
  rw [block009_data_flat015_step, block009_data_flat013_original, block009_data_flat014_original]
def block009_data_flat016 : CoefficientMerge.Poly := [(nat_lit 1276, Int.ofNat (nat_lit 258048000)), (nat_lit 1277, Int.ofNat (nat_lit 4255534080)), (nat_lit 1295, Int.ofNat (nat_lit 3789918720))]
theorem block009_data_flat016_step : block009_data_flat016 = (CoefficientMerge.fastMerge block009_data_flat012 block009_data_flat015) := by decide +kernel
theorem block009_data_flat016_original : block009_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (258048000 : Int) atom0662Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4255534080 : Int) atom0663Coded) (CoefficientMerge.scale (3789918720 : Int) atom0664Coded))) := by
  rw [block009_data_flat016_step, block009_data_flat012_original, block009_data_flat015_original]
def block009_data_flat017 : CoefficientMerge.Poly := [(nat_lit 1258, Int.ofNat (nat_lit 5228697600)), (nat_lit 1259, Int.ofNat (nat_lit 8587353600)), (nat_lit 1276, Int.ofNat (nat_lit 258048000)), (nat_lit 1277, Int.ofNat (nat_lit 4255534080)), (nat_lit 1295, Int.ofNat (nat_lit 3789918720))]
theorem block009_data_flat017_step : block009_data_flat017 = (CoefficientMerge.fastMerge block009_data_flat011 block009_data_flat016) := by decide +kernel
theorem block009_data_flat017_original : block009_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5228697600 : Int) atom0660Coded) (CoefficientMerge.scale (8587353600 : Int) atom0661Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (258048000 : Int) atom0662Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4255534080 : Int) atom0663Coded) (CoefficientMerge.scale (3789918720 : Int) atom0664Coded)))) := by
  rw [block009_data_flat017_step, block009_data_flat011_original, block009_data_flat016_original]
def block009_data_flat018 : CoefficientMerge.Poly := [(nat_lit 1238, Int.ofNat (nat_lit 8141283000)), (nat_lit 1239, Int.ofNat (nat_lit 12793243320)), (nat_lit 1240, Int.ofNat (nat_lit 8558934480)), (nat_lit 1241, Int.ofNat (nat_lit 11377463760)), (nat_lit 1257, Int.ofNat (nat_lit 4082641920)), (nat_lit 1258, Int.ofNat (nat_lit 5228697600)), (nat_lit 1259, Int.ofNat (nat_lit 8587353600)), (nat_lit 1276, Int.ofNat (nat_lit 258048000)), (nat_lit 1277, Int.ofNat (nat_lit 4255534080)), (nat_lit 1295, Int.ofNat (nat_lit 3789918720))]
theorem block009_data_flat018_step : block009_data_flat018 = (CoefficientMerge.fastMerge block009_data_flat008 block009_data_flat017) := by decide +kernel
theorem block009_data_flat018_original : block009_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8141283000 : Int) atom0655Coded) (CoefficientMerge.scale (12793243320 : Int) atom0656Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8558934480 : Int) atom0657Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11377463760 : Int) atom0658Coded) (CoefficientMerge.scale (4082641920 : Int) atom0659Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5228697600 : Int) atom0660Coded) (CoefficientMerge.scale (8587353600 : Int) atom0661Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (258048000 : Int) atom0662Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4255534080 : Int) atom0663Coded) (CoefficientMerge.scale (3789918720 : Int) atom0664Coded))))) := by
  rw [block009_data_flat018_step, block009_data_flat008_original, block009_data_flat017_original]
def block009_data_flat019 : CoefficientMerge.Poly := [(nat_lit 1372, Int.ofNat (nat_lit 839677440))]
theorem block009_data_flat019_step : block009_data_flat019 = (CoefficientMerge.scale (839677440 : Int) atom0665Coded) := by decide +kernel
theorem block009_data_flat019_original : block009_data_flat019 = (CoefficientMerge.scale (839677440 : Int) atom0665Coded) := by
  rw [block009_data_flat019_step]
def block009_data_flat020 : CoefficientMerge.Poly := [(nat_lit 1373, Int.ofNat (nat_lit 1603536000))]
theorem block009_data_flat020_step : block009_data_flat020 = (CoefficientMerge.scale (1603536000 : Int) atom0666Coded) := by decide +kernel
theorem block009_data_flat020_original : block009_data_flat020 = (CoefficientMerge.scale (1603536000 : Int) atom0666Coded) := by
  rw [block009_data_flat020_step]
def block009_data_flat021 : CoefficientMerge.Poly := [(nat_lit 1372, Int.ofNat (nat_lit 839677440)), (nat_lit 1373, Int.ofNat (nat_lit 1603536000))]
theorem block009_data_flat021_step : block009_data_flat021 = (CoefficientMerge.fastMerge block009_data_flat019 block009_data_flat020) := by decide +kernel
theorem block009_data_flat021_original : block009_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (839677440 : Int) atom0665Coded) (CoefficientMerge.scale (1603536000 : Int) atom0666Coded)) := by
  rw [block009_data_flat021_step, block009_data_flat019_original, block009_data_flat020_original]
def block009_data_flat022 : CoefficientMerge.Poly := [(nat_lit 1374, Int.ofNat (nat_lit 615212160))]
theorem block009_data_flat022_step : block009_data_flat022 = (CoefficientMerge.scale (615212160 : Int) atom0667Coded) := by decide +kernel
theorem block009_data_flat022_original : block009_data_flat022 = (CoefficientMerge.scale (615212160 : Int) atom0667Coded) := by
  rw [block009_data_flat022_step]
def block009_data_flat023 : CoefficientMerge.Poly := [(nat_lit 1375, Int.ofNat (nat_lit 103864320))]
theorem block009_data_flat023_step : block009_data_flat023 = (CoefficientMerge.scale (103864320 : Int) atom0668Coded) := by decide +kernel
theorem block009_data_flat023_original : block009_data_flat023 = (CoefficientMerge.scale (103864320 : Int) atom0668Coded) := by
  rw [block009_data_flat023_step]
def block009_data_flat024 : CoefficientMerge.Poly := [(nat_lit 1376, Int.ofNat (nat_lit 25159680))]
theorem block009_data_flat024_step : block009_data_flat024 = (CoefficientMerge.scale (25159680 : Int) atom0669Coded) := by decide +kernel
theorem block009_data_flat024_original : block009_data_flat024 = (CoefficientMerge.scale (25159680 : Int) atom0669Coded) := by
  rw [block009_data_flat024_step]
def block009_data_flat025 : CoefficientMerge.Poly := [(nat_lit 1375, Int.ofNat (nat_lit 103864320)), (nat_lit 1376, Int.ofNat (nat_lit 25159680))]
theorem block009_data_flat025_step : block009_data_flat025 = (CoefficientMerge.fastMerge block009_data_flat023 block009_data_flat024) := by decide +kernel
theorem block009_data_flat025_original : block009_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0668Coded) (CoefficientMerge.scale (25159680 : Int) atom0669Coded)) := by
  rw [block009_data_flat025_step, block009_data_flat023_original, block009_data_flat024_original]
def block009_data_flat026 : CoefficientMerge.Poly := [(nat_lit 1374, Int.ofNat (nat_lit 615212160)), (nat_lit 1375, Int.ofNat (nat_lit 103864320)), (nat_lit 1376, Int.ofNat (nat_lit 25159680))]
theorem block009_data_flat026_step : block009_data_flat026 = (CoefficientMerge.fastMerge block009_data_flat022 block009_data_flat025) := by decide +kernel
theorem block009_data_flat026_original : block009_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (615212160 : Int) atom0667Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0668Coded) (CoefficientMerge.scale (25159680 : Int) atom0669Coded))) := by
  rw [block009_data_flat026_step, block009_data_flat022_original, block009_data_flat025_original]
def block009_data_flat027 : CoefficientMerge.Poly := [(nat_lit 1372, Int.ofNat (nat_lit 839677440)), (nat_lit 1373, Int.ofNat (nat_lit 1603536000)), (nat_lit 1374, Int.ofNat (nat_lit 615212160)), (nat_lit 1375, Int.ofNat (nat_lit 103864320)), (nat_lit 1376, Int.ofNat (nat_lit 25159680))]
theorem block009_data_flat027_step : block009_data_flat027 = (CoefficientMerge.fastMerge block009_data_flat021 block009_data_flat026) := by decide +kernel
theorem block009_data_flat027_original : block009_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (839677440 : Int) atom0665Coded) (CoefficientMerge.scale (1603536000 : Int) atom0666Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (615212160 : Int) atom0667Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0668Coded) (CoefficientMerge.scale (25159680 : Int) atom0669Coded)))) := by
  rw [block009_data_flat027_step, block009_data_flat021_original, block009_data_flat026_original]
def block009_data_flat028 : CoefficientMerge.Poly := [(nat_lit 1380, Int.ofNat (nat_lit 1531037760))]
theorem block009_data_flat028_step : block009_data_flat028 = (CoefficientMerge.scale (1531037760 : Int) atom0670Coded) := by decide +kernel
theorem block009_data_flat028_original : block009_data_flat028 = (CoefficientMerge.scale (1531037760 : Int) atom0670Coded) := by
  rw [block009_data_flat028_step]
def block009_data_flat029 : CoefficientMerge.Poly := [(nat_lit 1382, Int.ofNat (nat_lit 460951440))]
theorem block009_data_flat029_step : block009_data_flat029 = (CoefficientMerge.scale (460951440 : Int) atom0671Coded) := by decide +kernel
theorem block009_data_flat029_original : block009_data_flat029 = (CoefficientMerge.scale (460951440 : Int) atom0671Coded) := by
  rw [block009_data_flat029_step]
def block009_data_flat030 : CoefficientMerge.Poly := [(nat_lit 1380, Int.ofNat (nat_lit 1531037760)), (nat_lit 1382, Int.ofNat (nat_lit 460951440))]
theorem block009_data_flat030_step : block009_data_flat030 = (CoefficientMerge.fastMerge block009_data_flat028 block009_data_flat029) := by decide +kernel
theorem block009_data_flat030_original : block009_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1531037760 : Int) atom0670Coded) (CoefficientMerge.scale (460951440 : Int) atom0671Coded)) := by
  rw [block009_data_flat030_step, block009_data_flat028_original, block009_data_flat029_original]
def block009_data_flat031 : CoefficientMerge.Poly := [(nat_lit 1391, Int.ofNat (nat_lit 1465409280))]
theorem block009_data_flat031_step : block009_data_flat031 = (CoefficientMerge.scale (1465409280 : Int) atom0672Coded) := by decide +kernel
theorem block009_data_flat031_original : block009_data_flat031 = (CoefficientMerge.scale (1465409280 : Int) atom0672Coded) := by
  rw [block009_data_flat031_step]
def block009_data_flat032 : CoefficientMerge.Poly := [(nat_lit 1392, Int.ofNat (nat_lit 1111580160))]
theorem block009_data_flat032_step : block009_data_flat032 = (CoefficientMerge.scale (1111580160 : Int) atom0673Coded) := by decide +kernel
theorem block009_data_flat032_original : block009_data_flat032 = (CoefficientMerge.scale (1111580160 : Int) atom0673Coded) := by
  rw [block009_data_flat032_step]
def block009_data_flat033 : CoefficientMerge.Poly := [(nat_lit 1396, Int.ofNat (nat_lit 103864320))]
theorem block009_data_flat033_step : block009_data_flat033 = (CoefficientMerge.scale (103864320 : Int) atom0674Coded) := by decide +kernel
theorem block009_data_flat033_original : block009_data_flat033 = (CoefficientMerge.scale (103864320 : Int) atom0674Coded) := by
  rw [block009_data_flat033_step]
def block009_data_flat034 : CoefficientMerge.Poly := [(nat_lit 1392, Int.ofNat (nat_lit 1111580160)), (nat_lit 1396, Int.ofNat (nat_lit 103864320))]
theorem block009_data_flat034_step : block009_data_flat034 = (CoefficientMerge.fastMerge block009_data_flat032 block009_data_flat033) := by decide +kernel
theorem block009_data_flat034_original : block009_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1111580160 : Int) atom0673Coded) (CoefficientMerge.scale (103864320 : Int) atom0674Coded)) := by
  rw [block009_data_flat034_step, block009_data_flat032_original, block009_data_flat033_original]
def block009_data_flat035 : CoefficientMerge.Poly := [(nat_lit 1391, Int.ofNat (nat_lit 1465409280)), (nat_lit 1392, Int.ofNat (nat_lit 1111580160)), (nat_lit 1396, Int.ofNat (nat_lit 103864320))]
theorem block009_data_flat035_step : block009_data_flat035 = (CoefficientMerge.fastMerge block009_data_flat031 block009_data_flat034) := by decide +kernel
theorem block009_data_flat035_original : block009_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1465409280 : Int) atom0672Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1111580160 : Int) atom0673Coded) (CoefficientMerge.scale (103864320 : Int) atom0674Coded))) := by
  rw [block009_data_flat035_step, block009_data_flat031_original, block009_data_flat034_original]
def block009_data_flat036 : CoefficientMerge.Poly := [(nat_lit 1380, Int.ofNat (nat_lit 1531037760)), (nat_lit 1382, Int.ofNat (nat_lit 460951440)), (nat_lit 1391, Int.ofNat (nat_lit 1465409280)), (nat_lit 1392, Int.ofNat (nat_lit 1111580160)), (nat_lit 1396, Int.ofNat (nat_lit 103864320))]
theorem block009_data_flat036_step : block009_data_flat036 = (CoefficientMerge.fastMerge block009_data_flat030 block009_data_flat035) := by decide +kernel
theorem block009_data_flat036_original : block009_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1531037760 : Int) atom0670Coded) (CoefficientMerge.scale (460951440 : Int) atom0671Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1465409280 : Int) atom0672Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1111580160 : Int) atom0673Coded) (CoefficientMerge.scale (103864320 : Int) atom0674Coded)))) := by
  rw [block009_data_flat036_step, block009_data_flat030_original, block009_data_flat035_original]
def block009_data_flat037 : CoefficientMerge.Poly := [(nat_lit 1372, Int.ofNat (nat_lit 839677440)), (nat_lit 1373, Int.ofNat (nat_lit 1603536000)), (nat_lit 1374, Int.ofNat (nat_lit 615212160)), (nat_lit 1375, Int.ofNat (nat_lit 103864320)), (nat_lit 1376, Int.ofNat (nat_lit 25159680)), (nat_lit 1380, Int.ofNat (nat_lit 1531037760)), (nat_lit 1382, Int.ofNat (nat_lit 460951440)), (nat_lit 1391, Int.ofNat (nat_lit 1465409280)), (nat_lit 1392, Int.ofNat (nat_lit 1111580160)), (nat_lit 1396, Int.ofNat (nat_lit 103864320))]
theorem block009_data_flat037_step : block009_data_flat037 = (CoefficientMerge.fastMerge block009_data_flat027 block009_data_flat036) := by decide +kernel
theorem block009_data_flat037_original : block009_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (839677440 : Int) atom0665Coded) (CoefficientMerge.scale (1603536000 : Int) atom0666Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (615212160 : Int) atom0667Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0668Coded) (CoefficientMerge.scale (25159680 : Int) atom0669Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1531037760 : Int) atom0670Coded) (CoefficientMerge.scale (460951440 : Int) atom0671Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1465409280 : Int) atom0672Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1111580160 : Int) atom0673Coded) (CoefficientMerge.scale (103864320 : Int) atom0674Coded))))) := by
  rw [block009_data_flat037_step, block009_data_flat027_original, block009_data_flat036_original]
def block009_data_flat038 : CoefficientMerge.Poly := [(nat_lit 1238, Int.ofNat (nat_lit 8141283000)), (nat_lit 1239, Int.ofNat (nat_lit 12793243320)), (nat_lit 1240, Int.ofNat (nat_lit 8558934480)), (nat_lit 1241, Int.ofNat (nat_lit 11377463760)), (nat_lit 1257, Int.ofNat (nat_lit 4082641920)), (nat_lit 1258, Int.ofNat (nat_lit 5228697600)), (nat_lit 1259, Int.ofNat (nat_lit 8587353600)), (nat_lit 1276, Int.ofNat (nat_lit 258048000)), (nat_lit 1277, Int.ofNat (nat_lit 4255534080)), (nat_lit 1295, Int.ofNat (nat_lit 3789918720)), (nat_lit 1372, Int.ofNat (nat_lit 839677440)), (nat_lit 1373, Int.ofNat (nat_lit 1603536000)), (nat_lit 1374, Int.ofNat (nat_lit 615212160)), (nat_lit 1375, Int.ofNat (nat_lit 103864320)), (nat_lit 1376, Int.ofNat (nat_lit 25159680)), (nat_lit 1380, Int.ofNat (nat_lit 1531037760)), (nat_lit 1382, Int.ofNat (nat_lit 460951440)), (nat_lit 1391, Int.ofNat (nat_lit 1465409280)), (nat_lit 1392, Int.ofNat (nat_lit 1111580160)), (nat_lit 1396, Int.ofNat (nat_lit 103864320))]
theorem block009_data_flat038_step : block009_data_flat038 = (CoefficientMerge.fastMerge block009_data_flat018 block009_data_flat037) := by decide +kernel
theorem block009_data_flat038_original : block009_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8141283000 : Int) atom0655Coded) (CoefficientMerge.scale (12793243320 : Int) atom0656Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8558934480 : Int) atom0657Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11377463760 : Int) atom0658Coded) (CoefficientMerge.scale (4082641920 : Int) atom0659Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5228697600 : Int) atom0660Coded) (CoefficientMerge.scale (8587353600 : Int) atom0661Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (258048000 : Int) atom0662Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4255534080 : Int) atom0663Coded) (CoefficientMerge.scale (3789918720 : Int) atom0664Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (839677440 : Int) atom0665Coded) (CoefficientMerge.scale (1603536000 : Int) atom0666Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (615212160 : Int) atom0667Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0668Coded) (CoefficientMerge.scale (25159680 : Int) atom0669Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1531037760 : Int) atom0670Coded) (CoefficientMerge.scale (460951440 : Int) atom0671Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1465409280 : Int) atom0672Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1111580160 : Int) atom0673Coded) (CoefficientMerge.scale (103864320 : Int) atom0674Coded)))))) := by
  rw [block009_data_flat038_step, block009_data_flat018_original, block009_data_flat037_original]
def block009_data_flat039 : CoefficientMerge.Poly := [(nat_lit 1397, Int.ofNat (nat_lit 207728640))]
theorem block009_data_flat039_step : block009_data_flat039 = (CoefficientMerge.scale (207728640 : Int) atom0675Coded) := by decide +kernel
theorem block009_data_flat039_original : block009_data_flat039 = (CoefficientMerge.scale (207728640 : Int) atom0675Coded) := by
  rw [block009_data_flat039_step]
def block009_data_flat040 : CoefficientMerge.Poly := [(nat_lit 1398, Int.ofNat (nat_lit 2424376752))]
theorem block009_data_flat040_step : block009_data_flat040 = (CoefficientMerge.scale (2424376752 : Int) atom0676Coded) := by decide +kernel
theorem block009_data_flat040_original : block009_data_flat040 = (CoefficientMerge.scale (2424376752 : Int) atom0676Coded) := by
  rw [block009_data_flat040_step]
def block009_data_flat041 : CoefficientMerge.Poly := [(nat_lit 1397, Int.ofNat (nat_lit 207728640)), (nat_lit 1398, Int.ofNat (nat_lit 2424376752))]
theorem block009_data_flat041_step : block009_data_flat041 = (CoefficientMerge.fastMerge block009_data_flat039 block009_data_flat040) := by decide +kernel
theorem block009_data_flat041_original : block009_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0675Coded) (CoefficientMerge.scale (2424376752 : Int) atom0676Coded)) := by
  rw [block009_data_flat041_step, block009_data_flat039_original, block009_data_flat040_original]
def block009_data_flat042 : CoefficientMerge.Poly := [(nat_lit 1400, Int.ofNat (nat_lit 1101237360))]
theorem block009_data_flat042_step : block009_data_flat042 = (CoefficientMerge.scale (1101237360 : Int) atom0677Coded) := by decide +kernel
theorem block009_data_flat042_original : block009_data_flat042 = (CoefficientMerge.scale (1101237360 : Int) atom0677Coded) := by
  rw [block009_data_flat042_step]
def block009_data_flat043 : CoefficientMerge.Poly := [(nat_lit 1401, Int.ofNat (nat_lit 1180247040))]
theorem block009_data_flat043_step : block009_data_flat043 = (CoefficientMerge.scale (1180247040 : Int) atom0678Coded) := by decide +kernel
theorem block009_data_flat043_original : block009_data_flat043 = (CoefficientMerge.scale (1180247040 : Int) atom0678Coded) := by
  rw [block009_data_flat043_step]
def block009_data_flat044 : CoefficientMerge.Poly := [(nat_lit 1402, Int.ofNat (nat_lit 2293143552))]
theorem block009_data_flat044_step : block009_data_flat044 = (CoefficientMerge.scale (2293143552 : Int) atom0679Coded) := by decide +kernel
theorem block009_data_flat044_original : block009_data_flat044 = (CoefficientMerge.scale (2293143552 : Int) atom0679Coded) := by
  rw [block009_data_flat044_step]
def block009_data_flat045 : CoefficientMerge.Poly := [(nat_lit 1401, Int.ofNat (nat_lit 1180247040)), (nat_lit 1402, Int.ofNat (nat_lit 2293143552))]
theorem block009_data_flat045_step : block009_data_flat045 = (CoefficientMerge.fastMerge block009_data_flat043 block009_data_flat044) := by decide +kernel
theorem block009_data_flat045_original : block009_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0678Coded) (CoefficientMerge.scale (2293143552 : Int) atom0679Coded)) := by
  rw [block009_data_flat045_step, block009_data_flat043_original, block009_data_flat044_original]
def block009_data_flat046 : CoefficientMerge.Poly := [(nat_lit 1400, Int.ofNat (nat_lit 1101237360)), (nat_lit 1401, Int.ofNat (nat_lit 1180247040)), (nat_lit 1402, Int.ofNat (nat_lit 2293143552))]
theorem block009_data_flat046_step : block009_data_flat046 = (CoefficientMerge.fastMerge block009_data_flat042 block009_data_flat045) := by decide +kernel
theorem block009_data_flat046_original : block009_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1101237360 : Int) atom0677Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0678Coded) (CoefficientMerge.scale (2293143552 : Int) atom0679Coded))) := by
  rw [block009_data_flat046_step, block009_data_flat042_original, block009_data_flat045_original]
def block009_data_flat047 : CoefficientMerge.Poly := [(nat_lit 1397, Int.ofNat (nat_lit 207728640)), (nat_lit 1398, Int.ofNat (nat_lit 2424376752)), (nat_lit 1400, Int.ofNat (nat_lit 1101237360)), (nat_lit 1401, Int.ofNat (nat_lit 1180247040)), (nat_lit 1402, Int.ofNat (nat_lit 2293143552))]
theorem block009_data_flat047_step : block009_data_flat047 = (CoefficientMerge.fastMerge block009_data_flat041 block009_data_flat046) := by decide +kernel
theorem block009_data_flat047_original : block009_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0675Coded) (CoefficientMerge.scale (2424376752 : Int) atom0676Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1101237360 : Int) atom0677Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0678Coded) (CoefficientMerge.scale (2293143552 : Int) atom0679Coded)))) := by
  rw [block009_data_flat047_step, block009_data_flat041_original, block009_data_flat046_original]
def block009_data_flat048 : CoefficientMerge.Poly := [(nat_lit 1403, Int.ofNat (nat_lit 3586383360))]
theorem block009_data_flat048_step : block009_data_flat048 = (CoefficientMerge.scale (3586383360 : Int) atom0680Coded) := by decide +kernel
theorem block009_data_flat048_original : block009_data_flat048 = (CoefficientMerge.scale (3586383360 : Int) atom0680Coded) := by
  rw [block009_data_flat048_step]
def block009_data_flat049 : CoefficientMerge.Poly := [(nat_lit 1410, Int.ofNat (nat_lit 423540480))]
theorem block009_data_flat049_step : block009_data_flat049 = (CoefficientMerge.scale (423540480 : Int) atom0681Coded) := by decide +kernel
theorem block009_data_flat049_original : block009_data_flat049 = (CoefficientMerge.scale (423540480 : Int) atom0681Coded) := by
  rw [block009_data_flat049_step]
def block009_data_flat050 : CoefficientMerge.Poly := [(nat_lit 1403, Int.ofNat (nat_lit 3586383360)), (nat_lit 1410, Int.ofNat (nat_lit 423540480))]
theorem block009_data_flat050_step : block009_data_flat050 = (CoefficientMerge.fastMerge block009_data_flat048 block009_data_flat049) := by decide +kernel
theorem block009_data_flat050_original : block009_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0680Coded) (CoefficientMerge.scale (423540480 : Int) atom0681Coded)) := by
  rw [block009_data_flat050_step, block009_data_flat048_original, block009_data_flat049_original]
def block009_data_flat051 : CoefficientMerge.Poly := [(nat_lit 1413, Int.ofNat (nat_lit 107089920))]
theorem block009_data_flat051_step : block009_data_flat051 = (CoefficientMerge.scale (107089920 : Int) atom0682Coded) := by decide +kernel
theorem block009_data_flat051_original : block009_data_flat051 = (CoefficientMerge.scale (107089920 : Int) atom0682Coded) := by
  rw [block009_data_flat051_step]
def block009_data_flat052 : CoefficientMerge.Poly := [(nat_lit 1414, Int.ofNat (nat_lit 264499200))]
theorem block009_data_flat052_step : block009_data_flat052 = (CoefficientMerge.scale (264499200 : Int) atom0683Coded) := by decide +kernel
theorem block009_data_flat052_original : block009_data_flat052 = (CoefficientMerge.scale (264499200 : Int) atom0683Coded) := by
  rw [block009_data_flat052_step]
def block009_data_flat053 : CoefficientMerge.Poly := [(nat_lit 1415, Int.ofNat (nat_lit 421908480))]
theorem block009_data_flat053_step : block009_data_flat053 = (CoefficientMerge.scale (421908480 : Int) atom0684Coded) := by decide +kernel
theorem block009_data_flat053_original : block009_data_flat053 = (CoefficientMerge.scale (421908480 : Int) atom0684Coded) := by
  rw [block009_data_flat053_step]
def block009_data_flat054 : CoefficientMerge.Poly := [(nat_lit 1414, Int.ofNat (nat_lit 264499200)), (nat_lit 1415, Int.ofNat (nat_lit 421908480))]
theorem block009_data_flat054_step : block009_data_flat054 = (CoefficientMerge.fastMerge block009_data_flat052 block009_data_flat053) := by decide +kernel
theorem block009_data_flat054_original : block009_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (264499200 : Int) atom0683Coded) (CoefficientMerge.scale (421908480 : Int) atom0684Coded)) := by
  rw [block009_data_flat054_step, block009_data_flat052_original, block009_data_flat053_original]
def block009_data_flat055 : CoefficientMerge.Poly := [(nat_lit 1413, Int.ofNat (nat_lit 107089920)), (nat_lit 1414, Int.ofNat (nat_lit 264499200)), (nat_lit 1415, Int.ofNat (nat_lit 421908480))]
theorem block009_data_flat055_step : block009_data_flat055 = (CoefficientMerge.fastMerge block009_data_flat051 block009_data_flat054) := by decide +kernel
theorem block009_data_flat055_original : block009_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (107089920 : Int) atom0682Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264499200 : Int) atom0683Coded) (CoefficientMerge.scale (421908480 : Int) atom0684Coded))) := by
  rw [block009_data_flat055_step, block009_data_flat051_original, block009_data_flat054_original]
def block009_data_flat056 : CoefficientMerge.Poly := [(nat_lit 1403, Int.ofNat (nat_lit 3586383360)), (nat_lit 1410, Int.ofNat (nat_lit 423540480)), (nat_lit 1413, Int.ofNat (nat_lit 107089920)), (nat_lit 1414, Int.ofNat (nat_lit 264499200)), (nat_lit 1415, Int.ofNat (nat_lit 421908480))]
theorem block009_data_flat056_step : block009_data_flat056 = (CoefficientMerge.fastMerge block009_data_flat050 block009_data_flat055) := by decide +kernel
theorem block009_data_flat056_original : block009_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0680Coded) (CoefficientMerge.scale (423540480 : Int) atom0681Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107089920 : Int) atom0682Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264499200 : Int) atom0683Coded) (CoefficientMerge.scale (421908480 : Int) atom0684Coded)))) := by
  rw [block009_data_flat056_step, block009_data_flat050_original, block009_data_flat055_original]
def block009_data_flat057 : CoefficientMerge.Poly := [(nat_lit 1397, Int.ofNat (nat_lit 207728640)), (nat_lit 1398, Int.ofNat (nat_lit 2424376752)), (nat_lit 1400, Int.ofNat (nat_lit 1101237360)), (nat_lit 1401, Int.ofNat (nat_lit 1180247040)), (nat_lit 1402, Int.ofNat (nat_lit 2293143552)), (nat_lit 1403, Int.ofNat (nat_lit 3586383360)), (nat_lit 1410, Int.ofNat (nat_lit 423540480)), (nat_lit 1413, Int.ofNat (nat_lit 107089920)), (nat_lit 1414, Int.ofNat (nat_lit 264499200)), (nat_lit 1415, Int.ofNat (nat_lit 421908480))]
theorem block009_data_flat057_step : block009_data_flat057 = (CoefficientMerge.fastMerge block009_data_flat047 block009_data_flat056) := by decide +kernel
theorem block009_data_flat057_original : block009_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0675Coded) (CoefficientMerge.scale (2424376752 : Int) atom0676Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1101237360 : Int) atom0677Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0678Coded) (CoefficientMerge.scale (2293143552 : Int) atom0679Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0680Coded) (CoefficientMerge.scale (423540480 : Int) atom0681Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107089920 : Int) atom0682Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264499200 : Int) atom0683Coded) (CoefficientMerge.scale (421908480 : Int) atom0684Coded))))) := by
  rw [block009_data_flat057_step, block009_data_flat047_original, block009_data_flat056_original]
def block009_data_flat058 : CoefficientMerge.Poly := [(nat_lit 1416, Int.ofNat (nat_lit 2576627520))]
theorem block009_data_flat058_step : block009_data_flat058 = (CoefficientMerge.scale (2576627520 : Int) atom0685Coded) := by decide +kernel
theorem block009_data_flat058_original : block009_data_flat058 = (CoefficientMerge.scale (2576627520 : Int) atom0685Coded) := by
  rw [block009_data_flat058_step]
def block009_data_flat059 : CoefficientMerge.Poly := [(nat_lit 1417, Int.ofNat (nat_lit 1293281520))]
theorem block009_data_flat059_step : block009_data_flat059 = (CoefficientMerge.scale (1293281520 : Int) atom0686Coded) := by decide +kernel
theorem block009_data_flat059_original : block009_data_flat059 = (CoefficientMerge.scale (1293281520 : Int) atom0686Coded) := by
  rw [block009_data_flat059_step]
def block009_data_flat060 : CoefficientMerge.Poly := [(nat_lit 1416, Int.ofNat (nat_lit 2576627520)), (nat_lit 1417, Int.ofNat (nat_lit 1293281520))]
theorem block009_data_flat060_step : block009_data_flat060 = (CoefficientMerge.fastMerge block009_data_flat058 block009_data_flat059) := by decide +kernel
theorem block009_data_flat060_original : block009_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2576627520 : Int) atom0685Coded) (CoefficientMerge.scale (1293281520 : Int) atom0686Coded)) := by
  rw [block009_data_flat060_step, block009_data_flat058_original, block009_data_flat059_original]
def block009_data_flat061 : CoefficientMerge.Poly := [(nat_lit 1418, Int.ofNat (nat_lit 2694257760))]
theorem block009_data_flat061_step : block009_data_flat061 = (CoefficientMerge.scale (2694257760 : Int) atom0687Coded) := by decide +kernel
theorem block009_data_flat061_original : block009_data_flat061 = (CoefficientMerge.scale (2694257760 : Int) atom0687Coded) := by
  rw [block009_data_flat061_step]
def block009_data_flat062 : CoefficientMerge.Poly := [(nat_lit 1419, Int.ofNat (nat_lit 3482496240))]
theorem block009_data_flat062_step : block009_data_flat062 = (CoefficientMerge.scale (3482496240 : Int) atom0688Coded) := by decide +kernel
theorem block009_data_flat062_original : block009_data_flat062 = (CoefficientMerge.scale (3482496240 : Int) atom0688Coded) := by
  rw [block009_data_flat062_step]
def block009_data_flat063 : CoefficientMerge.Poly := [(nat_lit 1420, Int.ofNat (nat_lit 5041760400))]
theorem block009_data_flat063_step : block009_data_flat063 = (CoefficientMerge.scale (5041760400 : Int) atom0689Coded) := by decide +kernel
theorem block009_data_flat063_original : block009_data_flat063 = (CoefficientMerge.scale (5041760400 : Int) atom0689Coded) := by
  rw [block009_data_flat063_step]
def block009_data_flat064 : CoefficientMerge.Poly := [(nat_lit 1419, Int.ofNat (nat_lit 3482496240)), (nat_lit 1420, Int.ofNat (nat_lit 5041760400))]
theorem block009_data_flat064_step : block009_data_flat064 = (CoefficientMerge.fastMerge block009_data_flat062 block009_data_flat063) := by decide +kernel
theorem block009_data_flat064_original : block009_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3482496240 : Int) atom0688Coded) (CoefficientMerge.scale (5041760400 : Int) atom0689Coded)) := by
  rw [block009_data_flat064_step, block009_data_flat062_original, block009_data_flat063_original]
def block009_data_flat065 : CoefficientMerge.Poly := [(nat_lit 1418, Int.ofNat (nat_lit 2694257760)), (nat_lit 1419, Int.ofNat (nat_lit 3482496240)), (nat_lit 1420, Int.ofNat (nat_lit 5041760400))]
theorem block009_data_flat065_step : block009_data_flat065 = (CoefficientMerge.fastMerge block009_data_flat061 block009_data_flat064) := by decide +kernel
theorem block009_data_flat065_original : block009_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2694257760 : Int) atom0687Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3482496240 : Int) atom0688Coded) (CoefficientMerge.scale (5041760400 : Int) atom0689Coded))) := by
  rw [block009_data_flat065_step, block009_data_flat061_original, block009_data_flat064_original]
def block009_data_flat066 : CoefficientMerge.Poly := [(nat_lit 1416, Int.ofNat (nat_lit 2576627520)), (nat_lit 1417, Int.ofNat (nat_lit 1293281520)), (nat_lit 1418, Int.ofNat (nat_lit 2694257760)), (nat_lit 1419, Int.ofNat (nat_lit 3482496240)), (nat_lit 1420, Int.ofNat (nat_lit 5041760400))]
theorem block009_data_flat066_step : block009_data_flat066 = (CoefficientMerge.fastMerge block009_data_flat060 block009_data_flat065) := by decide +kernel
theorem block009_data_flat066_original : block009_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2576627520 : Int) atom0685Coded) (CoefficientMerge.scale (1293281520 : Int) atom0686Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2694257760 : Int) atom0687Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3482496240 : Int) atom0688Coded) (CoefficientMerge.scale (5041760400 : Int) atom0689Coded)))) := by
  rw [block009_data_flat066_step, block009_data_flat060_original, block009_data_flat065_original]
def block009_data_flat067 : CoefficientMerge.Poly := [(nat_lit 1421, Int.ofNat (nat_lit 6677153280))]
theorem block009_data_flat067_step : block009_data_flat067 = (CoefficientMerge.scale (6677153280 : Int) atom0690Coded) := by decide +kernel
theorem block009_data_flat067_original : block009_data_flat067 = (CoefficientMerge.scale (6677153280 : Int) atom0690Coded) := by
  rw [block009_data_flat067_step]
def block009_data_flat068 : CoefficientMerge.Poly := [(nat_lit 1429, Int.ofNat (nat_lit 353829120))]
theorem block009_data_flat068_step : block009_data_flat068 = (CoefficientMerge.scale (353829120 : Int) atom0691Coded) := by decide +kernel
theorem block009_data_flat068_original : block009_data_flat068 = (CoefficientMerge.scale (353829120 : Int) atom0691Coded) := by
  rw [block009_data_flat068_step]
def block009_data_flat069 : CoefficientMerge.Poly := [(nat_lit 1421, Int.ofNat (nat_lit 6677153280)), (nat_lit 1429, Int.ofNat (nat_lit 353829120))]
theorem block009_data_flat069_step : block009_data_flat069 = (CoefficientMerge.fastMerge block009_data_flat067 block009_data_flat068) := by decide +kernel
theorem block009_data_flat069_original : block009_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6677153280 : Int) atom0690Coded) (CoefficientMerge.scale (353829120 : Int) atom0691Coded)) := by
  rw [block009_data_flat069_step, block009_data_flat067_original, block009_data_flat068_original]
def block009_data_flat070 : CoefficientMerge.Poly := [(nat_lit 1430, Int.ofNat (nat_lit 403703040))]
theorem block009_data_flat070_step : block009_data_flat070 = (CoefficientMerge.scale (403703040 : Int) atom0692Coded) := by decide +kernel
theorem block009_data_flat070_original : block009_data_flat070 = (CoefficientMerge.scale (403703040 : Int) atom0692Coded) := by
  rw [block009_data_flat070_step]
def block009_data_flat071 : CoefficientMerge.Poly := [(nat_lit 1431, Int.ofNat (nat_lit 460473600))]
theorem block009_data_flat071_step : block009_data_flat071 = (CoefficientMerge.scale (460473600 : Int) atom0693Coded) := by decide +kernel
theorem block009_data_flat071_original : block009_data_flat071 = (CoefficientMerge.scale (460473600 : Int) atom0693Coded) := by
  rw [block009_data_flat071_step]
def block009_data_flat072 : CoefficientMerge.Poly := [(nat_lit 1432, Int.ofNat (nat_lit 621108480))]
theorem block009_data_flat072_step : block009_data_flat072 = (CoefficientMerge.scale (621108480 : Int) atom0694Coded) := by decide +kernel
theorem block009_data_flat072_original : block009_data_flat072 = (CoefficientMerge.scale (621108480 : Int) atom0694Coded) := by
  rw [block009_data_flat072_step]
def block009_data_flat073 : CoefficientMerge.Poly := [(nat_lit 1431, Int.ofNat (nat_lit 460473600)), (nat_lit 1432, Int.ofNat (nat_lit 621108480))]
theorem block009_data_flat073_step : block009_data_flat073 = (CoefficientMerge.fastMerge block009_data_flat071 block009_data_flat072) := by decide +kernel
theorem block009_data_flat073_original : block009_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (460473600 : Int) atom0693Coded) (CoefficientMerge.scale (621108480 : Int) atom0694Coded)) := by
  rw [block009_data_flat073_step, block009_data_flat071_original, block009_data_flat072_original]
def block009_data_flat074 : CoefficientMerge.Poly := [(nat_lit 1430, Int.ofNat (nat_lit 403703040)), (nat_lit 1431, Int.ofNat (nat_lit 460473600)), (nat_lit 1432, Int.ofNat (nat_lit 621108480))]
theorem block009_data_flat074_step : block009_data_flat074 = (CoefficientMerge.fastMerge block009_data_flat070 block009_data_flat073) := by decide +kernel
theorem block009_data_flat074_original : block009_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (403703040 : Int) atom0692Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (460473600 : Int) atom0693Coded) (CoefficientMerge.scale (621108480 : Int) atom0694Coded))) := by
  rw [block009_data_flat074_step, block009_data_flat070_original, block009_data_flat073_original]
def block009_data_flat075 : CoefficientMerge.Poly := [(nat_lit 1421, Int.ofNat (nat_lit 6677153280)), (nat_lit 1429, Int.ofNat (nat_lit 353829120)), (nat_lit 1430, Int.ofNat (nat_lit 403703040)), (nat_lit 1431, Int.ofNat (nat_lit 460473600)), (nat_lit 1432, Int.ofNat (nat_lit 621108480))]
theorem block009_data_flat075_step : block009_data_flat075 = (CoefficientMerge.fastMerge block009_data_flat069 block009_data_flat074) := by decide +kernel
theorem block009_data_flat075_original : block009_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6677153280 : Int) atom0690Coded) (CoefficientMerge.scale (353829120 : Int) atom0691Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (403703040 : Int) atom0692Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (460473600 : Int) atom0693Coded) (CoefficientMerge.scale (621108480 : Int) atom0694Coded)))) := by
  rw [block009_data_flat075_step, block009_data_flat069_original, block009_data_flat074_original]
def block009_data_flat076 : CoefficientMerge.Poly := [(nat_lit 1416, Int.ofNat (nat_lit 2576627520)), (nat_lit 1417, Int.ofNat (nat_lit 1293281520)), (nat_lit 1418, Int.ofNat (nat_lit 2694257760)), (nat_lit 1419, Int.ofNat (nat_lit 3482496240)), (nat_lit 1420, Int.ofNat (nat_lit 5041760400)), (nat_lit 1421, Int.ofNat (nat_lit 6677153280)), (nat_lit 1429, Int.ofNat (nat_lit 353829120)), (nat_lit 1430, Int.ofNat (nat_lit 403703040)), (nat_lit 1431, Int.ofNat (nat_lit 460473600)), (nat_lit 1432, Int.ofNat (nat_lit 621108480))]
theorem block009_data_flat076_step : block009_data_flat076 = (CoefficientMerge.fastMerge block009_data_flat066 block009_data_flat075) := by decide +kernel
theorem block009_data_flat076_original : block009_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2576627520 : Int) atom0685Coded) (CoefficientMerge.scale (1293281520 : Int) atom0686Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2694257760 : Int) atom0687Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3482496240 : Int) atom0688Coded) (CoefficientMerge.scale (5041760400 : Int) atom0689Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6677153280 : Int) atom0690Coded) (CoefficientMerge.scale (353829120 : Int) atom0691Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (403703040 : Int) atom0692Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (460473600 : Int) atom0693Coded) (CoefficientMerge.scale (621108480 : Int) atom0694Coded))))) := by
  rw [block009_data_flat076_step, block009_data_flat066_original, block009_data_flat075_original]
def block009_data_flat077 : CoefficientMerge.Poly := [(nat_lit 1397, Int.ofNat (nat_lit 207728640)), (nat_lit 1398, Int.ofNat (nat_lit 2424376752)), (nat_lit 1400, Int.ofNat (nat_lit 1101237360)), (nat_lit 1401, Int.ofNat (nat_lit 1180247040)), (nat_lit 1402, Int.ofNat (nat_lit 2293143552)), (nat_lit 1403, Int.ofNat (nat_lit 3586383360)), (nat_lit 1410, Int.ofNat (nat_lit 423540480)), (nat_lit 1413, Int.ofNat (nat_lit 107089920)), (nat_lit 1414, Int.ofNat (nat_lit 264499200)), (nat_lit 1415, Int.ofNat (nat_lit 421908480)), (nat_lit 1416, Int.ofNat (nat_lit 2576627520)), (nat_lit 1417, Int.ofNat (nat_lit 1293281520)), (nat_lit 1418, Int.ofNat (nat_lit 2694257760)), (nat_lit 1419, Int.ofNat (nat_lit 3482496240)), (nat_lit 1420, Int.ofNat (nat_lit 5041760400)), (nat_lit 1421, Int.ofNat (nat_lit 6677153280)), (nat_lit 1429, Int.ofNat (nat_lit 353829120)), (nat_lit 1430, Int.ofNat (nat_lit 403703040)), (nat_lit 1431, Int.ofNat (nat_lit 460473600)), (nat_lit 1432, Int.ofNat (nat_lit 621108480))]
theorem block009_data_flat077_step : block009_data_flat077 = (CoefficientMerge.fastMerge block009_data_flat057 block009_data_flat076) := by decide +kernel
theorem block009_data_flat077_original : block009_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0675Coded) (CoefficientMerge.scale (2424376752 : Int) atom0676Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1101237360 : Int) atom0677Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0678Coded) (CoefficientMerge.scale (2293143552 : Int) atom0679Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0680Coded) (CoefficientMerge.scale (423540480 : Int) atom0681Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107089920 : Int) atom0682Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264499200 : Int) atom0683Coded) (CoefficientMerge.scale (421908480 : Int) atom0684Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2576627520 : Int) atom0685Coded) (CoefficientMerge.scale (1293281520 : Int) atom0686Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2694257760 : Int) atom0687Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3482496240 : Int) atom0688Coded) (CoefficientMerge.scale (5041760400 : Int) atom0689Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6677153280 : Int) atom0690Coded) (CoefficientMerge.scale (353829120 : Int) atom0691Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (403703040 : Int) atom0692Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (460473600 : Int) atom0693Coded) (CoefficientMerge.scale (621108480 : Int) atom0694Coded)))))) := by
  rw [block009_data_flat077_step, block009_data_flat057_original, block009_data_flat076_original]
def block009_data_flat078 : CoefficientMerge.Poly := [(nat_lit 1238, Int.ofNat (nat_lit 8141283000)), (nat_lit 1239, Int.ofNat (nat_lit 12793243320)), (nat_lit 1240, Int.ofNat (nat_lit 8558934480)), (nat_lit 1241, Int.ofNat (nat_lit 11377463760)), (nat_lit 1257, Int.ofNat (nat_lit 4082641920)), (nat_lit 1258, Int.ofNat (nat_lit 5228697600)), (nat_lit 1259, Int.ofNat (nat_lit 8587353600)), (nat_lit 1276, Int.ofNat (nat_lit 258048000)), (nat_lit 1277, Int.ofNat (nat_lit 4255534080)), (nat_lit 1295, Int.ofNat (nat_lit 3789918720)), (nat_lit 1372, Int.ofNat (nat_lit 839677440)), (nat_lit 1373, Int.ofNat (nat_lit 1603536000)), (nat_lit 1374, Int.ofNat (nat_lit 615212160)), (nat_lit 1375, Int.ofNat (nat_lit 103864320)), (nat_lit 1376, Int.ofNat (nat_lit 25159680)), (nat_lit 1380, Int.ofNat (nat_lit 1531037760)), (nat_lit 1382, Int.ofNat (nat_lit 460951440)), (nat_lit 1391, Int.ofNat (nat_lit 1465409280)), (nat_lit 1392, Int.ofNat (nat_lit 1111580160)), (nat_lit 1396, Int.ofNat (nat_lit 103864320)), (nat_lit 1397, Int.ofNat (nat_lit 207728640)), (nat_lit 1398, Int.ofNat (nat_lit 2424376752)), (nat_lit 1400, Int.ofNat (nat_lit 1101237360)), (nat_lit 1401, Int.ofNat (nat_lit 1180247040)), (nat_lit 1402, Int.ofNat (nat_lit 2293143552)), (nat_lit 1403, Int.ofNat (nat_lit 3586383360)), (nat_lit 1410, Int.ofNat (nat_lit 423540480)), (nat_lit 1413, Int.ofNat (nat_lit 107089920)), (nat_lit 1414, Int.ofNat (nat_lit 264499200)), (nat_lit 1415, Int.ofNat (nat_lit 421908480)), (nat_lit 1416, Int.ofNat (nat_lit 2576627520)), (nat_lit 1417, Int.ofNat (nat_lit 1293281520)), (nat_lit 1418, Int.ofNat (nat_lit 2694257760)), (nat_lit 1419, Int.ofNat (nat_lit 3482496240)), (nat_lit 1420, Int.ofNat (nat_lit 5041760400)), (nat_lit 1421, Int.ofNat (nat_lit 6677153280)), (nat_lit 1429, Int.ofNat (nat_lit 353829120)), (nat_lit 1430, Int.ofNat (nat_lit 403703040)), (nat_lit 1431, Int.ofNat (nat_lit 460473600)), (nat_lit 1432, Int.ofNat (nat_lit 621108480))]
theorem block009_data_flat078_step : block009_data_flat078 = (CoefficientMerge.fastMerge block009_data_flat038 block009_data_flat077) := by decide +kernel
theorem block009_data_flat078_original : block009_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8141283000 : Int) atom0655Coded) (CoefficientMerge.scale (12793243320 : Int) atom0656Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8558934480 : Int) atom0657Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11377463760 : Int) atom0658Coded) (CoefficientMerge.scale (4082641920 : Int) atom0659Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5228697600 : Int) atom0660Coded) (CoefficientMerge.scale (8587353600 : Int) atom0661Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (258048000 : Int) atom0662Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4255534080 : Int) atom0663Coded) (CoefficientMerge.scale (3789918720 : Int) atom0664Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (839677440 : Int) atom0665Coded) (CoefficientMerge.scale (1603536000 : Int) atom0666Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (615212160 : Int) atom0667Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0668Coded) (CoefficientMerge.scale (25159680 : Int) atom0669Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1531037760 : Int) atom0670Coded) (CoefficientMerge.scale (460951440 : Int) atom0671Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1465409280 : Int) atom0672Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1111580160 : Int) atom0673Coded) (CoefficientMerge.scale (103864320 : Int) atom0674Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0675Coded) (CoefficientMerge.scale (2424376752 : Int) atom0676Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1101237360 : Int) atom0677Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0678Coded) (CoefficientMerge.scale (2293143552 : Int) atom0679Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0680Coded) (CoefficientMerge.scale (423540480 : Int) atom0681Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107089920 : Int) atom0682Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264499200 : Int) atom0683Coded) (CoefficientMerge.scale (421908480 : Int) atom0684Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2576627520 : Int) atom0685Coded) (CoefficientMerge.scale (1293281520 : Int) atom0686Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2694257760 : Int) atom0687Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3482496240 : Int) atom0688Coded) (CoefficientMerge.scale (5041760400 : Int) atom0689Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6677153280 : Int) atom0690Coded) (CoefficientMerge.scale (353829120 : Int) atom0691Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (403703040 : Int) atom0692Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (460473600 : Int) atom0693Coded) (CoefficientMerge.scale (621108480 : Int) atom0694Coded))))))) := by
  rw [block009_data_flat078_step, block009_data_flat038_original, block009_data_flat077_original]
def block009_data_flat079 : CoefficientMerge.Poly := [(nat_lit 1433, Int.ofNat (nat_lit 781743360))]
theorem block009_data_flat079_step : block009_data_flat079 = (CoefficientMerge.scale (781743360 : Int) atom0695Coded) := by decide +kernel
theorem block009_data_flat079_original : block009_data_flat079 = (CoefficientMerge.scale (781743360 : Int) atom0695Coded) := by
  rw [block009_data_flat079_step]
def block009_data_flat080 : CoefficientMerge.Poly := [(nat_lit 1434, Int.ofNat (nat_lit 3019296000))]
theorem block009_data_flat080_step : block009_data_flat080 = (CoefficientMerge.scale (3019296000 : Int) atom0696Coded) := by decide +kernel
theorem block009_data_flat080_original : block009_data_flat080 = (CoefficientMerge.scale (3019296000 : Int) atom0696Coded) := by
  rw [block009_data_flat080_step]
def block009_data_flat081 : CoefficientMerge.Poly := [(nat_lit 1433, Int.ofNat (nat_lit 781743360)), (nat_lit 1434, Int.ofNat (nat_lit 3019296000))]
theorem block009_data_flat081_step : block009_data_flat081 = (CoefficientMerge.fastMerge block009_data_flat079 block009_data_flat080) := by decide +kernel
theorem block009_data_flat081_original : block009_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (781743360 : Int) atom0695Coded) (CoefficientMerge.scale (3019296000 : Int) atom0696Coded)) := by
  rw [block009_data_flat081_step, block009_data_flat079_original, block009_data_flat080_original]
def block009_data_flat082 : CoefficientMerge.Poly := [(nat_lit 1435, Int.ofNat (nat_lit 2332497120))]
theorem block009_data_flat082_step : block009_data_flat082 = (CoefficientMerge.scale (2332497120 : Int) atom0697Coded) := by decide +kernel
theorem block009_data_flat082_original : block009_data_flat082 = (CoefficientMerge.scale (2332497120 : Int) atom0697Coded) := by
  rw [block009_data_flat082_step]
def block009_data_flat083 : CoefficientMerge.Poly := [(nat_lit 1436, Int.ofNat (nat_lit 4135339680))]
theorem block009_data_flat083_step : block009_data_flat083 = (CoefficientMerge.scale (4135339680 : Int) atom0698Coded) := by decide +kernel
theorem block009_data_flat083_original : block009_data_flat083 = (CoefficientMerge.scale (4135339680 : Int) atom0698Coded) := by
  rw [block009_data_flat083_step]
def block009_data_flat084 : CoefficientMerge.Poly := [(nat_lit 1437, Int.ofNat (nat_lit 5254997280))]
theorem block009_data_flat084_step : block009_data_flat084 = (CoefficientMerge.scale (5254997280 : Int) atom0699Coded) := by decide +kernel
theorem block009_data_flat084_original : block009_data_flat084 = (CoefficientMerge.scale (5254997280 : Int) atom0699Coded) := by
  rw [block009_data_flat084_step]
def block009_data_flat085 : CoefficientMerge.Poly := [(nat_lit 1436, Int.ofNat (nat_lit 4135339680)), (nat_lit 1437, Int.ofNat (nat_lit 5254997280))]
theorem block009_data_flat085_step : block009_data_flat085 = (CoefficientMerge.fastMerge block009_data_flat083 block009_data_flat084) := by decide +kernel
theorem block009_data_flat085_original : block009_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4135339680 : Int) atom0698Coded) (CoefficientMerge.scale (5254997280 : Int) atom0699Coded)) := by
  rw [block009_data_flat085_step, block009_data_flat083_original, block009_data_flat084_original]
def block009_data_flat086 : CoefficientMerge.Poly := [(nat_lit 1435, Int.ofNat (nat_lit 2332497120)), (nat_lit 1436, Int.ofNat (nat_lit 4135339680)), (nat_lit 1437, Int.ofNat (nat_lit 5254997280))]
theorem block009_data_flat086_step : block009_data_flat086 = (CoefficientMerge.fastMerge block009_data_flat082 block009_data_flat085) := by decide +kernel
theorem block009_data_flat086_original : block009_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2332497120 : Int) atom0697Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4135339680 : Int) atom0698Coded) (CoefficientMerge.scale (5254997280 : Int) atom0699Coded))) := by
  rw [block009_data_flat086_step, block009_data_flat082_original, block009_data_flat085_original]
def block009_data_flat087 : CoefficientMerge.Poly := [(nat_lit 1433, Int.ofNat (nat_lit 781743360)), (nat_lit 1434, Int.ofNat (nat_lit 3019296000)), (nat_lit 1435, Int.ofNat (nat_lit 2332497120)), (nat_lit 1436, Int.ofNat (nat_lit 4135339680)), (nat_lit 1437, Int.ofNat (nat_lit 5254997280))]
theorem block009_data_flat087_step : block009_data_flat087 = (CoefficientMerge.fastMerge block009_data_flat081 block009_data_flat086) := by decide +kernel
theorem block009_data_flat087_original : block009_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (781743360 : Int) atom0695Coded) (CoefficientMerge.scale (3019296000 : Int) atom0696Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2332497120 : Int) atom0697Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4135339680 : Int) atom0698Coded) (CoefficientMerge.scale (5254997280 : Int) atom0699Coded)))) := by
  rw [block009_data_flat087_step, block009_data_flat081_original, block009_data_flat086_original]
def block009_data_flat088 : CoefficientMerge.Poly := [(nat_lit 1438, Int.ofNat (nat_lit 7178238240))]
theorem block009_data_flat088_step : block009_data_flat088 = (CoefficientMerge.scale (7178238240 : Int) atom0700Coded) := by decide +kernel
theorem block009_data_flat088_original : block009_data_flat088 = (CoefficientMerge.scale (7178238240 : Int) atom0700Coded) := by
  rw [block009_data_flat088_step]
def block009_data_flat089 : CoefficientMerge.Poly := [(nat_lit 1439, Int.ofNat (nat_lit 9115705440))]
theorem block009_data_flat089_step : block009_data_flat089 = (CoefficientMerge.scale (9115705440 : Int) atom0701Coded) := by decide +kernel
theorem block009_data_flat089_original : block009_data_flat089 = (CoefficientMerge.scale (9115705440 : Int) atom0701Coded) := by
  rw [block009_data_flat089_step]
def block009_data_flat090 : CoefficientMerge.Poly := [(nat_lit 1438, Int.ofNat (nat_lit 7178238240)), (nat_lit 1439, Int.ofNat (nat_lit 9115705440))]
theorem block009_data_flat090_step : block009_data_flat090 = (CoefficientMerge.fastMerge block009_data_flat088 block009_data_flat089) := by decide +kernel
theorem block009_data_flat090_original : block009_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7178238240 : Int) atom0700Coded) (CoefficientMerge.scale (9115705440 : Int) atom0701Coded)) := by
  rw [block009_data_flat090_step, block009_data_flat088_original, block009_data_flat089_original]
def block009_data_flat091 : CoefficientMerge.Poly := [(nat_lit 1448, Int.ofNat (nat_lit 827243520))]
theorem block009_data_flat091_step : block009_data_flat091 = (CoefficientMerge.scale (827243520 : Int) atom0702Coded) := by decide +kernel
theorem block009_data_flat091_original : block009_data_flat091 = (CoefficientMerge.scale (827243520 : Int) atom0702Coded) := by
  rw [block009_data_flat091_step]
def block009_data_flat092 : CoefficientMerge.Poly := [(nat_lit 1449, Int.ofNat (nat_lit 1400517120))]
theorem block009_data_flat092_step : block009_data_flat092 = (CoefficientMerge.scale (1400517120 : Int) atom0703Coded) := by decide +kernel
theorem block009_data_flat092_original : block009_data_flat092 = (CoefficientMerge.scale (1400517120 : Int) atom0703Coded) := by
  rw [block009_data_flat092_step]
def block009_data_flat093 : CoefficientMerge.Poly := [(nat_lit 1450, Int.ofNat (nat_lit 1514058240))]
theorem block009_data_flat093_step : block009_data_flat093 = (CoefficientMerge.scale (1514058240 : Int) atom0704Coded) := by decide +kernel
theorem block009_data_flat093_original : block009_data_flat093 = (CoefficientMerge.scale (1514058240 : Int) atom0704Coded) := by
  rw [block009_data_flat093_step]
def block009_data_flat094 : CoefficientMerge.Poly := [(nat_lit 1449, Int.ofNat (nat_lit 1400517120)), (nat_lit 1450, Int.ofNat (nat_lit 1514058240))]
theorem block009_data_flat094_step : block009_data_flat094 = (CoefficientMerge.fastMerge block009_data_flat092 block009_data_flat093) := by decide +kernel
theorem block009_data_flat094_original : block009_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1400517120 : Int) atom0703Coded) (CoefficientMerge.scale (1514058240 : Int) atom0704Coded)) := by
  rw [block009_data_flat094_step, block009_data_flat092_original, block009_data_flat093_original]
def block009_data_flat095 : CoefficientMerge.Poly := [(nat_lit 1448, Int.ofNat (nat_lit 827243520)), (nat_lit 1449, Int.ofNat (nat_lit 1400517120)), (nat_lit 1450, Int.ofNat (nat_lit 1514058240))]
theorem block009_data_flat095_step : block009_data_flat095 = (CoefficientMerge.fastMerge block009_data_flat091 block009_data_flat094) := by decide +kernel
theorem block009_data_flat095_original : block009_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (827243520 : Int) atom0702Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1400517120 : Int) atom0703Coded) (CoefficientMerge.scale (1514058240 : Int) atom0704Coded))) := by
  rw [block009_data_flat095_step, block009_data_flat091_original, block009_data_flat094_original]
def block009_data_flat096 : CoefficientMerge.Poly := [(nat_lit 1438, Int.ofNat (nat_lit 7178238240)), (nat_lit 1439, Int.ofNat (nat_lit 9115705440)), (nat_lit 1448, Int.ofNat (nat_lit 827243520)), (nat_lit 1449, Int.ofNat (nat_lit 1400517120)), (nat_lit 1450, Int.ofNat (nat_lit 1514058240))]
theorem block009_data_flat096_step : block009_data_flat096 = (CoefficientMerge.fastMerge block009_data_flat090 block009_data_flat095) := by decide +kernel
theorem block009_data_flat096_original : block009_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7178238240 : Int) atom0700Coded) (CoefficientMerge.scale (9115705440 : Int) atom0701Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (827243520 : Int) atom0702Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1400517120 : Int) atom0703Coded) (CoefficientMerge.scale (1514058240 : Int) atom0704Coded)))) := by
  rw [block009_data_flat096_step, block009_data_flat090_original, block009_data_flat095_original]
def block009_data_flat097 : CoefficientMerge.Poly := [(nat_lit 1433, Int.ofNat (nat_lit 781743360)), (nat_lit 1434, Int.ofNat (nat_lit 3019296000)), (nat_lit 1435, Int.ofNat (nat_lit 2332497120)), (nat_lit 1436, Int.ofNat (nat_lit 4135339680)), (nat_lit 1437, Int.ofNat (nat_lit 5254997280)), (nat_lit 1438, Int.ofNat (nat_lit 7178238240)), (nat_lit 1439, Int.ofNat (nat_lit 9115705440)), (nat_lit 1448, Int.ofNat (nat_lit 827243520)), (nat_lit 1449, Int.ofNat (nat_lit 1400517120)), (nat_lit 1450, Int.ofNat (nat_lit 1514058240))]
theorem block009_data_flat097_step : block009_data_flat097 = (CoefficientMerge.fastMerge block009_data_flat087 block009_data_flat096) := by decide +kernel
theorem block009_data_flat097_original : block009_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (781743360 : Int) atom0695Coded) (CoefficientMerge.scale (3019296000 : Int) atom0696Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2332497120 : Int) atom0697Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4135339680 : Int) atom0698Coded) (CoefficientMerge.scale (5254997280 : Int) atom0699Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7178238240 : Int) atom0700Coded) (CoefficientMerge.scale (9115705440 : Int) atom0701Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (827243520 : Int) atom0702Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1400517120 : Int) atom0703Coded) (CoefficientMerge.scale (1514058240 : Int) atom0704Coded))))) := by
  rw [block009_data_flat097_step, block009_data_flat087_original, block009_data_flat096_original]
def block009_data_flat098 : CoefficientMerge.Poly := [(nat_lit 1451, Int.ofNat (nat_lit 1627599360))]
theorem block009_data_flat098_step : block009_data_flat098 = (CoefficientMerge.scale (1627599360 : Int) atom0705Coded) := by decide +kernel
theorem block009_data_flat098_original : block009_data_flat098 = (CoefficientMerge.scale (1627599360 : Int) atom0705Coded) := by
  rw [block009_data_flat098_step]
def block009_data_flat099 : CoefficientMerge.Poly := [(nat_lit 1452, Int.ofNat (nat_lit 3755136000))]
theorem block009_data_flat099_step : block009_data_flat099 = (CoefficientMerge.scale (3755136000 : Int) atom0706Coded) := by decide +kernel
theorem block009_data_flat099_original : block009_data_flat099 = (CoefficientMerge.scale (3755136000 : Int) atom0706Coded) := by
  rw [block009_data_flat099_step]
def block009_data_flat100 : CoefficientMerge.Poly := [(nat_lit 1451, Int.ofNat (nat_lit 1627599360)), (nat_lit 1452, Int.ofNat (nat_lit 3755136000))]
theorem block009_data_flat100_step : block009_data_flat100 = (CoefficientMerge.fastMerge block009_data_flat098 block009_data_flat099) := by decide +kernel
theorem block009_data_flat100_original : block009_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1627599360 : Int) atom0705Coded) (CoefficientMerge.scale (3755136000 : Int) atom0706Coded)) := by
  rw [block009_data_flat100_step, block009_data_flat098_original, block009_data_flat099_original]
def block009_data_flat101 : CoefficientMerge.Poly := [(nat_lit 1453, Int.ofNat (nat_lit 3303554880))]
theorem block009_data_flat101_step : block009_data_flat101 = (CoefficientMerge.scale (3303554880 : Int) atom0707Coded) := by decide +kernel
theorem block009_data_flat101_original : block009_data_flat101 = (CoefficientMerge.scale (3303554880 : Int) atom0707Coded) := by
  rw [block009_data_flat101_step]
def block009_data_flat102 : CoefficientMerge.Poly := [(nat_lit 1454, Int.ofNat (nat_lit 5488183200))]
theorem block009_data_flat102_step : block009_data_flat102 = (CoefficientMerge.scale (5488183200 : Int) atom0708Coded) := by decide +kernel
theorem block009_data_flat102_original : block009_data_flat102 = (CoefficientMerge.scale (5488183200 : Int) atom0708Coded) := by
  rw [block009_data_flat102_step]
def block009_data_flat103 : CoefficientMerge.Poly := [(nat_lit 1455, Int.ofNat (nat_lit 6428383680))]
theorem block009_data_flat103_step : block009_data_flat103 = (CoefficientMerge.scale (6428383680 : Int) atom0709Coded) := by decide +kernel
theorem block009_data_flat103_original : block009_data_flat103 = (CoefficientMerge.scale (6428383680 : Int) atom0709Coded) := by
  rw [block009_data_flat103_step]
def block009_data_flat104 : CoefficientMerge.Poly := [(nat_lit 1454, Int.ofNat (nat_lit 5488183200)), (nat_lit 1455, Int.ofNat (nat_lit 6428383680))]
theorem block009_data_flat104_step : block009_data_flat104 = (CoefficientMerge.fastMerge block009_data_flat102 block009_data_flat103) := by decide +kernel
theorem block009_data_flat104_original : block009_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5488183200 : Int) atom0708Coded) (CoefficientMerge.scale (6428383680 : Int) atom0709Coded)) := by
  rw [block009_data_flat104_step, block009_data_flat102_original, block009_data_flat103_original]
def block009_data_flat105 : CoefficientMerge.Poly := [(nat_lit 1453, Int.ofNat (nat_lit 3303554880)), (nat_lit 1454, Int.ofNat (nat_lit 5488183200)), (nat_lit 1455, Int.ofNat (nat_lit 6428383680))]
theorem block009_data_flat105_step : block009_data_flat105 = (CoefficientMerge.fastMerge block009_data_flat101 block009_data_flat104) := by decide +kernel
theorem block009_data_flat105_original : block009_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3303554880 : Int) atom0707Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5488183200 : Int) atom0708Coded) (CoefficientMerge.scale (6428383680 : Int) atom0709Coded))) := by
  rw [block009_data_flat105_step, block009_data_flat101_original, block009_data_flat104_original]
def block009_data_flat106 : CoefficientMerge.Poly := [(nat_lit 1451, Int.ofNat (nat_lit 1627599360)), (nat_lit 1452, Int.ofNat (nat_lit 3755136000)), (nat_lit 1453, Int.ofNat (nat_lit 3303554880)), (nat_lit 1454, Int.ofNat (nat_lit 5488183200)), (nat_lit 1455, Int.ofNat (nat_lit 6428383680))]
theorem block009_data_flat106_step : block009_data_flat106 = (CoefficientMerge.fastMerge block009_data_flat100 block009_data_flat105) := by decide +kernel
theorem block009_data_flat106_original : block009_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1627599360 : Int) atom0705Coded) (CoefficientMerge.scale (3755136000 : Int) atom0706Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3303554880 : Int) atom0707Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5488183200 : Int) atom0708Coded) (CoefficientMerge.scale (6428383680 : Int) atom0709Coded)))) := by
  rw [block009_data_flat106_step, block009_data_flat100_original, block009_data_flat105_original]
def block009_data_flat107 : CoefficientMerge.Poly := [(nat_lit 1456, Int.ofNat (nat_lit 8473755840))]
theorem block009_data_flat107_step : block009_data_flat107 = (CoefficientMerge.scale (8473755840 : Int) atom0710Coded) := by decide +kernel
theorem block009_data_flat107_original : block009_data_flat107 = (CoefficientMerge.scale (8473755840 : Int) atom0710Coded) := by
  rw [block009_data_flat107_step]
def block009_data_flat108 : CoefficientMerge.Poly := [(nat_lit 1457, Int.ofNat (nat_lit 10519128000))]
theorem block009_data_flat108_step : block009_data_flat108 = (CoefficientMerge.scale (10519128000 : Int) atom0711Coded) := by decide +kernel
theorem block009_data_flat108_original : block009_data_flat108 = (CoefficientMerge.scale (10519128000 : Int) atom0711Coded) := by
  rw [block009_data_flat108_step]
def block009_data_flat109 : CoefficientMerge.Poly := [(nat_lit 1456, Int.ofNat (nat_lit 8473755840)), (nat_lit 1457, Int.ofNat (nat_lit 10519128000))]
theorem block009_data_flat109_step : block009_data_flat109 = (CoefficientMerge.fastMerge block009_data_flat107 block009_data_flat108) := by decide +kernel
theorem block009_data_flat109_original : block009_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8473755840 : Int) atom0710Coded) (CoefficientMerge.scale (10519128000 : Int) atom0711Coded)) := by
  rw [block009_data_flat109_step, block009_data_flat107_original, block009_data_flat108_original]
def block009_data_flat110 : CoefficientMerge.Poly := [(nat_lit 1467, Int.ofNat (nat_lit 1454507520))]
theorem block009_data_flat110_step : block009_data_flat110 = (CoefficientMerge.scale (1454507520 : Int) atom0712Coded) := by decide +kernel
theorem block009_data_flat110_original : block009_data_flat110 = (CoefficientMerge.scale (1454507520 : Int) atom0712Coded) := by
  rw [block009_data_flat110_step]
def block009_data_flat111 : CoefficientMerge.Poly := [(nat_lit 1468, Int.ofNat (nat_lit 2574428160))]
theorem block009_data_flat111_step : block009_data_flat111 = (CoefficientMerge.scale (2574428160 : Int) atom0713Coded) := by decide +kernel
theorem block009_data_flat111_original : block009_data_flat111 = (CoefficientMerge.scale (2574428160 : Int) atom0713Coded) := by
  rw [block009_data_flat111_step]
def block009_data_flat112 : CoefficientMerge.Poly := [(nat_lit 1469, Int.ofNat (nat_lit 2590556160))]
theorem block009_data_flat112_step : block009_data_flat112 = (CoefficientMerge.scale (2590556160 : Int) atom0714Coded) := by decide +kernel
theorem block009_data_flat112_original : block009_data_flat112 = (CoefficientMerge.scale (2590556160 : Int) atom0714Coded) := by
  rw [block009_data_flat112_step]
def block009_data_flat113 : CoefficientMerge.Poly := [(nat_lit 1468, Int.ofNat (nat_lit 2574428160)), (nat_lit 1469, Int.ofNat (nat_lit 2590556160))]
theorem block009_data_flat113_step : block009_data_flat113 = (CoefficientMerge.fastMerge block009_data_flat111 block009_data_flat112) := by decide +kernel
theorem block009_data_flat113_original : block009_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2574428160 : Int) atom0713Coded) (CoefficientMerge.scale (2590556160 : Int) atom0714Coded)) := by
  rw [block009_data_flat113_step, block009_data_flat111_original, block009_data_flat112_original]
def block009_data_flat114 : CoefficientMerge.Poly := [(nat_lit 1467, Int.ofNat (nat_lit 1454507520)), (nat_lit 1468, Int.ofNat (nat_lit 2574428160)), (nat_lit 1469, Int.ofNat (nat_lit 2590556160))]
theorem block009_data_flat114_step : block009_data_flat114 = (CoefficientMerge.fastMerge block009_data_flat110 block009_data_flat113) := by decide +kernel
theorem block009_data_flat114_original : block009_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1454507520 : Int) atom0712Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2574428160 : Int) atom0713Coded) (CoefficientMerge.scale (2590556160 : Int) atom0714Coded))) := by
  rw [block009_data_flat114_step, block009_data_flat110_original, block009_data_flat113_original]
def block009_data_flat115 : CoefficientMerge.Poly := [(nat_lit 1456, Int.ofNat (nat_lit 8473755840)), (nat_lit 1457, Int.ofNat (nat_lit 10519128000)), (nat_lit 1467, Int.ofNat (nat_lit 1454507520)), (nat_lit 1468, Int.ofNat (nat_lit 2574428160)), (nat_lit 1469, Int.ofNat (nat_lit 2590556160))]
theorem block009_data_flat115_step : block009_data_flat115 = (CoefficientMerge.fastMerge block009_data_flat109 block009_data_flat114) := by decide +kernel
theorem block009_data_flat115_original : block009_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8473755840 : Int) atom0710Coded) (CoefficientMerge.scale (10519128000 : Int) atom0711Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1454507520 : Int) atom0712Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2574428160 : Int) atom0713Coded) (CoefficientMerge.scale (2590556160 : Int) atom0714Coded)))) := by
  rw [block009_data_flat115_step, block009_data_flat109_original, block009_data_flat114_original]
def block009_data_flat116 : CoefficientMerge.Poly := [(nat_lit 1451, Int.ofNat (nat_lit 1627599360)), (nat_lit 1452, Int.ofNat (nat_lit 3755136000)), (nat_lit 1453, Int.ofNat (nat_lit 3303554880)), (nat_lit 1454, Int.ofNat (nat_lit 5488183200)), (nat_lit 1455, Int.ofNat (nat_lit 6428383680)), (nat_lit 1456, Int.ofNat (nat_lit 8473755840)), (nat_lit 1457, Int.ofNat (nat_lit 10519128000)), (nat_lit 1467, Int.ofNat (nat_lit 1454507520)), (nat_lit 1468, Int.ofNat (nat_lit 2574428160)), (nat_lit 1469, Int.ofNat (nat_lit 2590556160))]
theorem block009_data_flat116_step : block009_data_flat116 = (CoefficientMerge.fastMerge block009_data_flat106 block009_data_flat115) := by decide +kernel
theorem block009_data_flat116_original : block009_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1627599360 : Int) atom0705Coded) (CoefficientMerge.scale (3755136000 : Int) atom0706Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3303554880 : Int) atom0707Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5488183200 : Int) atom0708Coded) (CoefficientMerge.scale (6428383680 : Int) atom0709Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8473755840 : Int) atom0710Coded) (CoefficientMerge.scale (10519128000 : Int) atom0711Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1454507520 : Int) atom0712Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2574428160 : Int) atom0713Coded) (CoefficientMerge.scale (2590556160 : Int) atom0714Coded))))) := by
  rw [block009_data_flat116_step, block009_data_flat106_original, block009_data_flat115_original]
def block009_data_flat117 : CoefficientMerge.Poly := [(nat_lit 1433, Int.ofNat (nat_lit 781743360)), (nat_lit 1434, Int.ofNat (nat_lit 3019296000)), (nat_lit 1435, Int.ofNat (nat_lit 2332497120)), (nat_lit 1436, Int.ofNat (nat_lit 4135339680)), (nat_lit 1437, Int.ofNat (nat_lit 5254997280)), (nat_lit 1438, Int.ofNat (nat_lit 7178238240)), (nat_lit 1439, Int.ofNat (nat_lit 9115705440)), (nat_lit 1448, Int.ofNat (nat_lit 827243520)), (nat_lit 1449, Int.ofNat (nat_lit 1400517120)), (nat_lit 1450, Int.ofNat (nat_lit 1514058240)), (nat_lit 1451, Int.ofNat (nat_lit 1627599360)), (nat_lit 1452, Int.ofNat (nat_lit 3755136000)), (nat_lit 1453, Int.ofNat (nat_lit 3303554880)), (nat_lit 1454, Int.ofNat (nat_lit 5488183200)), (nat_lit 1455, Int.ofNat (nat_lit 6428383680)), (nat_lit 1456, Int.ofNat (nat_lit 8473755840)), (nat_lit 1457, Int.ofNat (nat_lit 10519128000)), (nat_lit 1467, Int.ofNat (nat_lit 1454507520)), (nat_lit 1468, Int.ofNat (nat_lit 2574428160)), (nat_lit 1469, Int.ofNat (nat_lit 2590556160))]
theorem block009_data_flat117_step : block009_data_flat117 = (CoefficientMerge.fastMerge block009_data_flat097 block009_data_flat116) := by decide +kernel
theorem block009_data_flat117_original : block009_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (781743360 : Int) atom0695Coded) (CoefficientMerge.scale (3019296000 : Int) atom0696Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2332497120 : Int) atom0697Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4135339680 : Int) atom0698Coded) (CoefficientMerge.scale (5254997280 : Int) atom0699Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7178238240 : Int) atom0700Coded) (CoefficientMerge.scale (9115705440 : Int) atom0701Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (827243520 : Int) atom0702Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1400517120 : Int) atom0703Coded) (CoefficientMerge.scale (1514058240 : Int) atom0704Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1627599360 : Int) atom0705Coded) (CoefficientMerge.scale (3755136000 : Int) atom0706Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3303554880 : Int) atom0707Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5488183200 : Int) atom0708Coded) (CoefficientMerge.scale (6428383680 : Int) atom0709Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8473755840 : Int) atom0710Coded) (CoefficientMerge.scale (10519128000 : Int) atom0711Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1454507520 : Int) atom0712Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2574428160 : Int) atom0713Coded) (CoefficientMerge.scale (2590556160 : Int) atom0714Coded)))))) := by
  rw [block009_data_flat117_step, block009_data_flat097_original, block009_data_flat116_original]
def block009_data_flat118 : CoefficientMerge.Poly := [(nat_lit 1470, Int.ofNat (nat_lit 4644494400))]
theorem block009_data_flat118_step : block009_data_flat118 = (CoefficientMerge.scale (4644494400 : Int) atom0715Coded) := by decide +kernel
theorem block009_data_flat118_original : block009_data_flat118 = (CoefficientMerge.scale (4644494400 : Int) atom0715Coded) := by
  rw [block009_data_flat118_step]
def block009_data_flat119 : CoefficientMerge.Poly := [(nat_lit 1471, Int.ofNat (nat_lit 4143129600))]
theorem block009_data_flat119_step : block009_data_flat119 = (CoefficientMerge.scale (4143129600 : Int) atom0716Coded) := by decide +kernel
theorem block009_data_flat119_original : block009_data_flat119 = (CoefficientMerge.scale (4143129600 : Int) atom0716Coded) := by
  rw [block009_data_flat119_step]
def block009_data_flat120 : CoefficientMerge.Poly := [(nat_lit 1470, Int.ofNat (nat_lit 4644494400)), (nat_lit 1471, Int.ofNat (nat_lit 4143129600))]
theorem block009_data_flat120_step : block009_data_flat120 = (CoefficientMerge.fastMerge block009_data_flat118 block009_data_flat119) := by decide +kernel
theorem block009_data_flat120_original : block009_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4644494400 : Int) atom0715Coded) (CoefficientMerge.scale (4143129600 : Int) atom0716Coded)) := by
  rw [block009_data_flat120_step, block009_data_flat118_original, block009_data_flat119_original]
def block009_data_flat121 : CoefficientMerge.Poly := [(nat_lit 1472, Int.ofNat (nat_lit 6663591840))]
theorem block009_data_flat121_step : block009_data_flat121 = (CoefficientMerge.scale (6663591840 : Int) atom0717Coded) := by decide +kernel
theorem block009_data_flat121_original : block009_data_flat121 = (CoefficientMerge.scale (6663591840 : Int) atom0717Coded) := by
  rw [block009_data_flat121_step]
def block009_data_flat122 : CoefficientMerge.Poly := [(nat_lit 1473, Int.ofNat (nat_lit 7216020480))]
theorem block009_data_flat122_step : block009_data_flat122 = (CoefficientMerge.scale (7216020480 : Int) atom0718Coded) := by decide +kernel
theorem block009_data_flat122_original : block009_data_flat122 = (CoefficientMerge.scale (7216020480 : Int) atom0718Coded) := by
  rw [block009_data_flat122_step]
def block009_data_flat123 : CoefficientMerge.Poly := [(nat_lit 1474, Int.ofNat (nat_lit 9259238400))]
theorem block009_data_flat123_step : block009_data_flat123 = (CoefficientMerge.scale (9259238400 : Int) atom0719Coded) := by decide +kernel
theorem block009_data_flat123_original : block009_data_flat123 = (CoefficientMerge.scale (9259238400 : Int) atom0719Coded) := by
  rw [block009_data_flat123_step]
def block009_data_flat124 : CoefficientMerge.Poly := [(nat_lit 1473, Int.ofNat (nat_lit 7216020480)), (nat_lit 1474, Int.ofNat (nat_lit 9259238400))]
theorem block009_data_flat124_step : block009_data_flat124 = (CoefficientMerge.fastMerge block009_data_flat122 block009_data_flat123) := by decide +kernel
theorem block009_data_flat124_original : block009_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7216020480 : Int) atom0718Coded) (CoefficientMerge.scale (9259238400 : Int) atom0719Coded)) := by
  rw [block009_data_flat124_step, block009_data_flat122_original, block009_data_flat123_original]
def block009_data_flat125 : CoefficientMerge.Poly := [(nat_lit 1472, Int.ofNat (nat_lit 6663591840)), (nat_lit 1473, Int.ofNat (nat_lit 7216020480)), (nat_lit 1474, Int.ofNat (nat_lit 9259238400))]
theorem block009_data_flat125_step : block009_data_flat125 = (CoefficientMerge.fastMerge block009_data_flat121 block009_data_flat124) := by decide +kernel
theorem block009_data_flat125_original : block009_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6663591840 : Int) atom0717Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7216020480 : Int) atom0718Coded) (CoefficientMerge.scale (9259238400 : Int) atom0719Coded))) := by
  rw [block009_data_flat125_step, block009_data_flat121_original, block009_data_flat124_original]
def block009_data_flat126 : CoefficientMerge.Poly := [(nat_lit 1470, Int.ofNat (nat_lit 4644494400)), (nat_lit 1471, Int.ofNat (nat_lit 4143129600)), (nat_lit 1472, Int.ofNat (nat_lit 6663591840)), (nat_lit 1473, Int.ofNat (nat_lit 7216020480)), (nat_lit 1474, Int.ofNat (nat_lit 9259238400))]
theorem block009_data_flat126_step : block009_data_flat126 = (CoefficientMerge.fastMerge block009_data_flat120 block009_data_flat125) := by decide +kernel
theorem block009_data_flat126_original : block009_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4644494400 : Int) atom0715Coded) (CoefficientMerge.scale (4143129600 : Int) atom0716Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6663591840 : Int) atom0717Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7216020480 : Int) atom0718Coded) (CoefficientMerge.scale (9259238400 : Int) atom0719Coded)))) := by
  rw [block009_data_flat126_step, block009_data_flat120_original, block009_data_flat125_original]
def block009_data_flat127 : CoefficientMerge.Poly := [(nat_lit 1475, Int.ofNat (nat_lit 11302456320))]
theorem block009_data_flat127_step : block009_data_flat127 = (CoefficientMerge.scale (11302456320 : Int) atom0720Coded) := by decide +kernel
theorem block009_data_flat127_original : block009_data_flat127 = (CoefficientMerge.scale (11302456320 : Int) atom0720Coded) := by
  rw [block009_data_flat127_step]
def block009_data_flat128 : CoefficientMerge.Poly := [(nat_lit 1486, Int.ofNat (nat_lit 2105018880))]
theorem block009_data_flat128_step : block009_data_flat128 = (CoefficientMerge.scale (2105018880 : Int) atom0721Coded) := by decide +kernel
theorem block009_data_flat128_original : block009_data_flat128 = (CoefficientMerge.scale (2105018880 : Int) atom0721Coded) := by
  rw [block009_data_flat128_step]
def block009_data_flat129 : CoefficientMerge.Poly := [(nat_lit 1475, Int.ofNat (nat_lit 11302456320)), (nat_lit 1486, Int.ofNat (nat_lit 2105018880))]
theorem block009_data_flat129_step : block009_data_flat129 = (CoefficientMerge.fastMerge block009_data_flat127 block009_data_flat128) := by decide +kernel
theorem block009_data_flat129_original : block009_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11302456320 : Int) atom0720Coded) (CoefficientMerge.scale (2105018880 : Int) atom0721Coded)) := by
  rw [block009_data_flat129_step, block009_data_flat127_original, block009_data_flat128_original]
def block009_data_flat130 : CoefficientMerge.Poly := [(nat_lit 1487, Int.ofNat (nat_lit 3744445440))]
theorem block009_data_flat130_step : block009_data_flat130 = (CoefficientMerge.scale (3744445440 : Int) atom0722Coded) := by decide +kernel
theorem block009_data_flat130_original : block009_data_flat130 = (CoefficientMerge.scale (3744445440 : Int) atom0722Coded) := by
  rw [block009_data_flat130_step]
def block009_data_flat131 : CoefficientMerge.Poly := [(nat_lit 1488, Int.ofNat (nat_lit 5639632320))]
theorem block009_data_flat131_step : block009_data_flat131 = (CoefficientMerge.scale (5639632320 : Int) atom0723Coded) := by decide +kernel
theorem block009_data_flat131_original : block009_data_flat131 = (CoefficientMerge.scale (5639632320 : Int) atom0723Coded) := by
  rw [block009_data_flat131_step]
def block009_data_flat132 : CoefficientMerge.Poly := [(nat_lit 1489, Int.ofNat (nat_lit 4968497280))]
theorem block009_data_flat132_step : block009_data_flat132 = (CoefficientMerge.scale (4968497280 : Int) atom0724Coded) := by decide +kernel
theorem block009_data_flat132_original : block009_data_flat132 = (CoefficientMerge.scale (4968497280 : Int) atom0724Coded) := by
  rw [block009_data_flat132_step]
def block009_data_flat133 : CoefficientMerge.Poly := [(nat_lit 1488, Int.ofNat (nat_lit 5639632320)), (nat_lit 1489, Int.ofNat (nat_lit 4968497280))]
theorem block009_data_flat133_step : block009_data_flat133 = (CoefficientMerge.fastMerge block009_data_flat131 block009_data_flat132) := by decide +kernel
theorem block009_data_flat133_original : block009_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5639632320 : Int) atom0723Coded) (CoefficientMerge.scale (4968497280 : Int) atom0724Coded)) := by
  rw [block009_data_flat133_step, block009_data_flat131_original, block009_data_flat132_original]
def block009_data_flat134 : CoefficientMerge.Poly := [(nat_lit 1487, Int.ofNat (nat_lit 3744445440)), (nat_lit 1488, Int.ofNat (nat_lit 5639632320)), (nat_lit 1489, Int.ofNat (nat_lit 4968497280))]
theorem block009_data_flat134_step : block009_data_flat134 = (CoefficientMerge.fastMerge block009_data_flat130 block009_data_flat133) := by decide +kernel
theorem block009_data_flat134_original : block009_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3744445440 : Int) atom0722Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5639632320 : Int) atom0723Coded) (CoefficientMerge.scale (4968497280 : Int) atom0724Coded))) := by
  rw [block009_data_flat134_step, block009_data_flat130_original, block009_data_flat133_original]
def block009_data_flat135 : CoefficientMerge.Poly := [(nat_lit 1475, Int.ofNat (nat_lit 11302456320)), (nat_lit 1486, Int.ofNat (nat_lit 2105018880)), (nat_lit 1487, Int.ofNat (nat_lit 3744445440)), (nat_lit 1488, Int.ofNat (nat_lit 5639632320)), (nat_lit 1489, Int.ofNat (nat_lit 4968497280))]
theorem block009_data_flat135_step : block009_data_flat135 = (CoefficientMerge.fastMerge block009_data_flat129 block009_data_flat134) := by decide +kernel
theorem block009_data_flat135_original : block009_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11302456320 : Int) atom0720Coded) (CoefficientMerge.scale (2105018880 : Int) atom0721Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3744445440 : Int) atom0722Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5639632320 : Int) atom0723Coded) (CoefficientMerge.scale (4968497280 : Int) atom0724Coded)))) := by
  rw [block009_data_flat135_step, block009_data_flat129_original, block009_data_flat134_original]
def block009_data_flat136 : CoefficientMerge.Poly := [(nat_lit 1470, Int.ofNat (nat_lit 4644494400)), (nat_lit 1471, Int.ofNat (nat_lit 4143129600)), (nat_lit 1472, Int.ofNat (nat_lit 6663591840)), (nat_lit 1473, Int.ofNat (nat_lit 7216020480)), (nat_lit 1474, Int.ofNat (nat_lit 9259238400)), (nat_lit 1475, Int.ofNat (nat_lit 11302456320)), (nat_lit 1486, Int.ofNat (nat_lit 2105018880)), (nat_lit 1487, Int.ofNat (nat_lit 3744445440)), (nat_lit 1488, Int.ofNat (nat_lit 5639632320)), (nat_lit 1489, Int.ofNat (nat_lit 4968497280))]
theorem block009_data_flat136_step : block009_data_flat136 = (CoefficientMerge.fastMerge block009_data_flat126 block009_data_flat135) := by decide +kernel
theorem block009_data_flat136_original : block009_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4644494400 : Int) atom0715Coded) (CoefficientMerge.scale (4143129600 : Int) atom0716Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6663591840 : Int) atom0717Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7216020480 : Int) atom0718Coded) (CoefficientMerge.scale (9259238400 : Int) atom0719Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11302456320 : Int) atom0720Coded) (CoefficientMerge.scale (2105018880 : Int) atom0721Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3744445440 : Int) atom0722Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5639632320 : Int) atom0723Coded) (CoefficientMerge.scale (4968497280 : Int) atom0724Coded))))) := by
  rw [block009_data_flat136_step, block009_data_flat126_original, block009_data_flat135_original]
def block009_data_flat137 : CoefficientMerge.Poly := [(nat_lit 1490, Int.ofNat (nat_lit 7889319840))]
theorem block009_data_flat137_step : block009_data_flat137 = (CoefficientMerge.scale (7889319840 : Int) atom0725Coded) := by decide +kernel
theorem block009_data_flat137_original : block009_data_flat137 = (CoefficientMerge.scale (7889319840 : Int) atom0725Coded) := by
  rw [block009_data_flat137_step]
def block009_data_flat138 : CoefficientMerge.Poly := [(nat_lit 1491, Int.ofNat (nat_lit 7679809920))]
theorem block009_data_flat138_step : block009_data_flat138 = (CoefficientMerge.scale (7679809920 : Int) atom0726Coded) := by decide +kernel
theorem block009_data_flat138_original : block009_data_flat138 = (CoefficientMerge.scale (7679809920 : Int) atom0726Coded) := by
  rw [block009_data_flat138_step]
def block009_data_flat139 : CoefficientMerge.Poly := [(nat_lit 1490, Int.ofNat (nat_lit 7889319840)), (nat_lit 1491, Int.ofNat (nat_lit 7679809920))]
theorem block009_data_flat139_step : block009_data_flat139 = (CoefficientMerge.fastMerge block009_data_flat137 block009_data_flat138) := by decide +kernel
theorem block009_data_flat139_original : block009_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7889319840 : Int) atom0725Coded) (CoefficientMerge.scale (7679809920 : Int) atom0726Coded)) := by
  rw [block009_data_flat139_step, block009_data_flat137_original, block009_data_flat138_original]
def block009_data_flat140 : CoefficientMerge.Poly := [(nat_lit 1492, Int.ofNat (nat_lit 9531219840))]
theorem block009_data_flat140_step : block009_data_flat140 = (CoefficientMerge.scale (9531219840 : Int) atom0727Coded) := by decide +kernel
theorem block009_data_flat140_original : block009_data_flat140 = (CoefficientMerge.scale (9531219840 : Int) atom0727Coded) := by
  rw [block009_data_flat140_step]
def block009_data_flat141 : CoefficientMerge.Poly := [(nat_lit 1493, Int.ofNat (nat_lit 11673385920))]
theorem block009_data_flat141_step : block009_data_flat141 = (CoefficientMerge.scale (11673385920 : Int) atom0728Coded) := by decide +kernel
theorem block009_data_flat141_original : block009_data_flat141 = (CoefficientMerge.scale (11673385920 : Int) atom0728Coded) := by
  rw [block009_data_flat141_step]
def block009_data_flat142 : CoefficientMerge.Poly := [(nat_lit 1505, Int.ofNat (nat_lit 2958144000))]
theorem block009_data_flat142_step : block009_data_flat142 = (CoefficientMerge.scale (2958144000 : Int) atom0729Coded) := by decide +kernel
theorem block009_data_flat142_original : block009_data_flat142 = (CoefficientMerge.scale (2958144000 : Int) atom0729Coded) := by
  rw [block009_data_flat142_step]
def block009_data_flat143 : CoefficientMerge.Poly := [(nat_lit 1493, Int.ofNat (nat_lit 11673385920)), (nat_lit 1505, Int.ofNat (nat_lit 2958144000))]
theorem block009_data_flat143_step : block009_data_flat143 = (CoefficientMerge.fastMerge block009_data_flat141 block009_data_flat142) := by decide +kernel
theorem block009_data_flat143_original : block009_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11673385920 : Int) atom0728Coded) (CoefficientMerge.scale (2958144000 : Int) atom0729Coded)) := by
  rw [block009_data_flat143_step, block009_data_flat141_original, block009_data_flat142_original]
def block009_data_flat144 : CoefficientMerge.Poly := [(nat_lit 1492, Int.ofNat (nat_lit 9531219840)), (nat_lit 1493, Int.ofNat (nat_lit 11673385920)), (nat_lit 1505, Int.ofNat (nat_lit 2958144000))]
theorem block009_data_flat144_step : block009_data_flat144 = (CoefficientMerge.fastMerge block009_data_flat140 block009_data_flat143) := by decide +kernel
theorem block009_data_flat144_original : block009_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9531219840 : Int) atom0727Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11673385920 : Int) atom0728Coded) (CoefficientMerge.scale (2958144000 : Int) atom0729Coded))) := by
  rw [block009_data_flat144_step, block009_data_flat140_original, block009_data_flat143_original]
def block009_data_flat145 : CoefficientMerge.Poly := [(nat_lit 1490, Int.ofNat (nat_lit 7889319840)), (nat_lit 1491, Int.ofNat (nat_lit 7679809920)), (nat_lit 1492, Int.ofNat (nat_lit 9531219840)), (nat_lit 1493, Int.ofNat (nat_lit 11673385920)), (nat_lit 1505, Int.ofNat (nat_lit 2958144000))]
theorem block009_data_flat145_step : block009_data_flat145 = (CoefficientMerge.fastMerge block009_data_flat139 block009_data_flat144) := by decide +kernel
theorem block009_data_flat145_original : block009_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7889319840 : Int) atom0725Coded) (CoefficientMerge.scale (7679809920 : Int) atom0726Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9531219840 : Int) atom0727Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11673385920 : Int) atom0728Coded) (CoefficientMerge.scale (2958144000 : Int) atom0729Coded)))) := by
  rw [block009_data_flat145_step, block009_data_flat139_original, block009_data_flat144_original]
def block009_data_flat146 : CoefficientMerge.Poly := [(nat_lit 1506, Int.ofNat (nat_lit 6511653120))]
theorem block009_data_flat146_step : block009_data_flat146 = (CoefficientMerge.scale (6511653120 : Int) atom0730Coded) := by decide +kernel
theorem block009_data_flat146_original : block009_data_flat146 = (CoefficientMerge.scale (6511653120 : Int) atom0730Coded) := by
  rw [block009_data_flat146_step]
def block009_data_flat147 : CoefficientMerge.Poly := [(nat_lit 1507, Int.ofNat (nat_lit 5589568320))]
theorem block009_data_flat147_step : block009_data_flat147 = (CoefficientMerge.scale (5589568320 : Int) atom0731Coded) := by decide +kernel
theorem block009_data_flat147_original : block009_data_flat147 = (CoefficientMerge.scale (5589568320 : Int) atom0731Coded) := by
  rw [block009_data_flat147_step]
def block009_data_flat148 : CoefficientMerge.Poly := [(nat_lit 1506, Int.ofNat (nat_lit 6511653120)), (nat_lit 1507, Int.ofNat (nat_lit 5589568320))]
theorem block009_data_flat148_step : block009_data_flat148 = (CoefficientMerge.fastMerge block009_data_flat146 block009_data_flat147) := by decide +kernel
theorem block009_data_flat148_original : block009_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6511653120 : Int) atom0730Coded) (CoefficientMerge.scale (5589568320 : Int) atom0731Coded)) := by
  rw [block009_data_flat148_step, block009_data_flat146_original, block009_data_flat147_original]
def block009_data_flat149 : CoefficientMerge.Poly := [(nat_lit 1508, Int.ofNat (nat_lit 8928903840))]
theorem block009_data_flat149_step : block009_data_flat149 = (CoefficientMerge.scale (8928903840 : Int) atom0732Coded) := by decide +kernel
theorem block009_data_flat149_original : block009_data_flat149 = (CoefficientMerge.scale (8928903840 : Int) atom0732Coded) := by
  rw [block009_data_flat149_step]
def block009_data_flat150 : CoefficientMerge.Poly := [(nat_lit 1509, Int.ofNat (nat_lit 8835408960))]
theorem block009_data_flat150_step : block009_data_flat150 = (CoefficientMerge.scale (8835408960 : Int) atom0733Coded) := by decide +kernel
theorem block009_data_flat150_original : block009_data_flat150 = (CoefficientMerge.scale (8835408960 : Int) atom0733Coded) := by
  rw [block009_data_flat150_step]
def block009_data_flat151 : CoefficientMerge.Poly := [(nat_lit 1510, Int.ofNat (nat_lit 9405332160))]
theorem block009_data_flat151_step : block009_data_flat151 = (CoefficientMerge.scale (9405332160 : Int) atom0734Coded) := by decide +kernel
theorem block009_data_flat151_original : block009_data_flat151 = (CoefficientMerge.scale (9405332160 : Int) atom0734Coded) := by
  rw [block009_data_flat151_step]
def block009_data_flat152 : CoefficientMerge.Poly := [(nat_lit 1509, Int.ofNat (nat_lit 8835408960)), (nat_lit 1510, Int.ofNat (nat_lit 9405332160))]
theorem block009_data_flat152_step : block009_data_flat152 = (CoefficientMerge.fastMerge block009_data_flat150 block009_data_flat151) := by decide +kernel
theorem block009_data_flat152_original : block009_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8835408960 : Int) atom0733Coded) (CoefficientMerge.scale (9405332160 : Int) atom0734Coded)) := by
  rw [block009_data_flat152_step, block009_data_flat150_original, block009_data_flat151_original]
def block009_data_flat153 : CoefficientMerge.Poly := [(nat_lit 1508, Int.ofNat (nat_lit 8928903840)), (nat_lit 1509, Int.ofNat (nat_lit 8835408960)), (nat_lit 1510, Int.ofNat (nat_lit 9405332160))]
theorem block009_data_flat153_step : block009_data_flat153 = (CoefficientMerge.fastMerge block009_data_flat149 block009_data_flat152) := by decide +kernel
theorem block009_data_flat153_original : block009_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8928903840 : Int) atom0732Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8835408960 : Int) atom0733Coded) (CoefficientMerge.scale (9405332160 : Int) atom0734Coded))) := by
  rw [block009_data_flat153_step, block009_data_flat149_original, block009_data_flat152_original]
def block009_data_flat154 : CoefficientMerge.Poly := [(nat_lit 1506, Int.ofNat (nat_lit 6511653120)), (nat_lit 1507, Int.ofNat (nat_lit 5589568320)), (nat_lit 1508, Int.ofNat (nat_lit 8928903840)), (nat_lit 1509, Int.ofNat (nat_lit 8835408960)), (nat_lit 1510, Int.ofNat (nat_lit 9405332160))]
theorem block009_data_flat154_step : block009_data_flat154 = (CoefficientMerge.fastMerge block009_data_flat148 block009_data_flat153) := by decide +kernel
theorem block009_data_flat154_original : block009_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6511653120 : Int) atom0730Coded) (CoefficientMerge.scale (5589568320 : Int) atom0731Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8928903840 : Int) atom0732Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8835408960 : Int) atom0733Coded) (CoefficientMerge.scale (9405332160 : Int) atom0734Coded)))) := by
  rw [block009_data_flat154_step, block009_data_flat148_original, block009_data_flat153_original]
def block009_data_flat155 : CoefficientMerge.Poly := [(nat_lit 1490, Int.ofNat (nat_lit 7889319840)), (nat_lit 1491, Int.ofNat (nat_lit 7679809920)), (nat_lit 1492, Int.ofNat (nat_lit 9531219840)), (nat_lit 1493, Int.ofNat (nat_lit 11673385920)), (nat_lit 1505, Int.ofNat (nat_lit 2958144000)), (nat_lit 1506, Int.ofNat (nat_lit 6511653120)), (nat_lit 1507, Int.ofNat (nat_lit 5589568320)), (nat_lit 1508, Int.ofNat (nat_lit 8928903840)), (nat_lit 1509, Int.ofNat (nat_lit 8835408960)), (nat_lit 1510, Int.ofNat (nat_lit 9405332160))]
theorem block009_data_flat155_step : block009_data_flat155 = (CoefficientMerge.fastMerge block009_data_flat145 block009_data_flat154) := by decide +kernel
theorem block009_data_flat155_original : block009_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7889319840 : Int) atom0725Coded) (CoefficientMerge.scale (7679809920 : Int) atom0726Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9531219840 : Int) atom0727Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11673385920 : Int) atom0728Coded) (CoefficientMerge.scale (2958144000 : Int) atom0729Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6511653120 : Int) atom0730Coded) (CoefficientMerge.scale (5589568320 : Int) atom0731Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8928903840 : Int) atom0732Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8835408960 : Int) atom0733Coded) (CoefficientMerge.scale (9405332160 : Int) atom0734Coded))))) := by
  rw [block009_data_flat155_step, block009_data_flat145_original, block009_data_flat154_original]
def block009_data_flat156 : CoefficientMerge.Poly := [(nat_lit 1470, Int.ofNat (nat_lit 4644494400)), (nat_lit 1471, Int.ofNat (nat_lit 4143129600)), (nat_lit 1472, Int.ofNat (nat_lit 6663591840)), (nat_lit 1473, Int.ofNat (nat_lit 7216020480)), (nat_lit 1474, Int.ofNat (nat_lit 9259238400)), (nat_lit 1475, Int.ofNat (nat_lit 11302456320)), (nat_lit 1486, Int.ofNat (nat_lit 2105018880)), (nat_lit 1487, Int.ofNat (nat_lit 3744445440)), (nat_lit 1488, Int.ofNat (nat_lit 5639632320)), (nat_lit 1489, Int.ofNat (nat_lit 4968497280)), (nat_lit 1490, Int.ofNat (nat_lit 7889319840)), (nat_lit 1491, Int.ofNat (nat_lit 7679809920)), (nat_lit 1492, Int.ofNat (nat_lit 9531219840)), (nat_lit 1493, Int.ofNat (nat_lit 11673385920)), (nat_lit 1505, Int.ofNat (nat_lit 2958144000)), (nat_lit 1506, Int.ofNat (nat_lit 6511653120)), (nat_lit 1507, Int.ofNat (nat_lit 5589568320)), (nat_lit 1508, Int.ofNat (nat_lit 8928903840)), (nat_lit 1509, Int.ofNat (nat_lit 8835408960)), (nat_lit 1510, Int.ofNat (nat_lit 9405332160))]
theorem block009_data_flat156_step : block009_data_flat156 = (CoefficientMerge.fastMerge block009_data_flat136 block009_data_flat155) := by decide +kernel
theorem block009_data_flat156_original : block009_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4644494400 : Int) atom0715Coded) (CoefficientMerge.scale (4143129600 : Int) atom0716Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6663591840 : Int) atom0717Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7216020480 : Int) atom0718Coded) (CoefficientMerge.scale (9259238400 : Int) atom0719Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11302456320 : Int) atom0720Coded) (CoefficientMerge.scale (2105018880 : Int) atom0721Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3744445440 : Int) atom0722Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5639632320 : Int) atom0723Coded) (CoefficientMerge.scale (4968497280 : Int) atom0724Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7889319840 : Int) atom0725Coded) (CoefficientMerge.scale (7679809920 : Int) atom0726Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9531219840 : Int) atom0727Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11673385920 : Int) atom0728Coded) (CoefficientMerge.scale (2958144000 : Int) atom0729Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6511653120 : Int) atom0730Coded) (CoefficientMerge.scale (5589568320 : Int) atom0731Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8928903840 : Int) atom0732Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8835408960 : Int) atom0733Coded) (CoefficientMerge.scale (9405332160 : Int) atom0734Coded)))))) := by
  rw [block009_data_flat156_step, block009_data_flat136_original, block009_data_flat155_original]
def block009_data_flat157 : CoefficientMerge.Poly := [(nat_lit 1433, Int.ofNat (nat_lit 781743360)), (nat_lit 1434, Int.ofNat (nat_lit 3019296000)), (nat_lit 1435, Int.ofNat (nat_lit 2332497120)), (nat_lit 1436, Int.ofNat (nat_lit 4135339680)), (nat_lit 1437, Int.ofNat (nat_lit 5254997280)), (nat_lit 1438, Int.ofNat (nat_lit 7178238240)), (nat_lit 1439, Int.ofNat (nat_lit 9115705440)), (nat_lit 1448, Int.ofNat (nat_lit 827243520)), (nat_lit 1449, Int.ofNat (nat_lit 1400517120)), (nat_lit 1450, Int.ofNat (nat_lit 1514058240)), (nat_lit 1451, Int.ofNat (nat_lit 1627599360)), (nat_lit 1452, Int.ofNat (nat_lit 3755136000)), (nat_lit 1453, Int.ofNat (nat_lit 3303554880)), (nat_lit 1454, Int.ofNat (nat_lit 5488183200)), (nat_lit 1455, Int.ofNat (nat_lit 6428383680)), (nat_lit 1456, Int.ofNat (nat_lit 8473755840)), (nat_lit 1457, Int.ofNat (nat_lit 10519128000)), (nat_lit 1467, Int.ofNat (nat_lit 1454507520)), (nat_lit 1468, Int.ofNat (nat_lit 2574428160)), (nat_lit 1469, Int.ofNat (nat_lit 2590556160)), (nat_lit 1470, Int.ofNat (nat_lit 4644494400)), (nat_lit 1471, Int.ofNat (nat_lit 4143129600)), (nat_lit 1472, Int.ofNat (nat_lit 6663591840)), (nat_lit 1473, Int.ofNat (nat_lit 7216020480)), (nat_lit 1474, Int.ofNat (nat_lit 9259238400)), (nat_lit 1475, Int.ofNat (nat_lit 11302456320)), (nat_lit 1486, Int.ofNat (nat_lit 2105018880)), (nat_lit 1487, Int.ofNat (nat_lit 3744445440)), (nat_lit 1488, Int.ofNat (nat_lit 5639632320)), (nat_lit 1489, Int.ofNat (nat_lit 4968497280)), (nat_lit 1490, Int.ofNat (nat_lit 7889319840)), (nat_lit 1491, Int.ofNat (nat_lit 7679809920)), (nat_lit 1492, Int.ofNat (nat_lit 9531219840)), (nat_lit 1493, Int.ofNat (nat_lit 11673385920)), (nat_lit 1505, Int.ofNat (nat_lit 2958144000)), (nat_lit 1506, Int.ofNat (nat_lit 6511653120)), (nat_lit 1507, Int.ofNat (nat_lit 5589568320)), (nat_lit 1508, Int.ofNat (nat_lit 8928903840)), (nat_lit 1509, Int.ofNat (nat_lit 8835408960)), (nat_lit 1510, Int.ofNat (nat_lit 9405332160))]
theorem block009_data_flat157_step : block009_data_flat157 = (CoefficientMerge.fastMerge block009_data_flat117 block009_data_flat156) := by decide +kernel
theorem block009_data_flat157_original : block009_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (781743360 : Int) atom0695Coded) (CoefficientMerge.scale (3019296000 : Int) atom0696Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2332497120 : Int) atom0697Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4135339680 : Int) atom0698Coded) (CoefficientMerge.scale (5254997280 : Int) atom0699Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7178238240 : Int) atom0700Coded) (CoefficientMerge.scale (9115705440 : Int) atom0701Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (827243520 : Int) atom0702Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1400517120 : Int) atom0703Coded) (CoefficientMerge.scale (1514058240 : Int) atom0704Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1627599360 : Int) atom0705Coded) (CoefficientMerge.scale (3755136000 : Int) atom0706Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3303554880 : Int) atom0707Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5488183200 : Int) atom0708Coded) (CoefficientMerge.scale (6428383680 : Int) atom0709Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8473755840 : Int) atom0710Coded) (CoefficientMerge.scale (10519128000 : Int) atom0711Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1454507520 : Int) atom0712Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2574428160 : Int) atom0713Coded) (CoefficientMerge.scale (2590556160 : Int) atom0714Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4644494400 : Int) atom0715Coded) (CoefficientMerge.scale (4143129600 : Int) atom0716Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6663591840 : Int) atom0717Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7216020480 : Int) atom0718Coded) (CoefficientMerge.scale (9259238400 : Int) atom0719Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11302456320 : Int) atom0720Coded) (CoefficientMerge.scale (2105018880 : Int) atom0721Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3744445440 : Int) atom0722Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5639632320 : Int) atom0723Coded) (CoefficientMerge.scale (4968497280 : Int) atom0724Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7889319840 : Int) atom0725Coded) (CoefficientMerge.scale (7679809920 : Int) atom0726Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9531219840 : Int) atom0727Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11673385920 : Int) atom0728Coded) (CoefficientMerge.scale (2958144000 : Int) atom0729Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6511653120 : Int) atom0730Coded) (CoefficientMerge.scale (5589568320 : Int) atom0731Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8928903840 : Int) atom0732Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8835408960 : Int) atom0733Coded) (CoefficientMerge.scale (9405332160 : Int) atom0734Coded))))))) := by
  rw [block009_data_flat157_step, block009_data_flat117_original, block009_data_flat156_original]
def block009_data_flat158 : CoefficientMerge.Poly := [(nat_lit 1238, Int.ofNat (nat_lit 8141283000)), (nat_lit 1239, Int.ofNat (nat_lit 12793243320)), (nat_lit 1240, Int.ofNat (nat_lit 8558934480)), (nat_lit 1241, Int.ofNat (nat_lit 11377463760)), (nat_lit 1257, Int.ofNat (nat_lit 4082641920)), (nat_lit 1258, Int.ofNat (nat_lit 5228697600)), (nat_lit 1259, Int.ofNat (nat_lit 8587353600)), (nat_lit 1276, Int.ofNat (nat_lit 258048000)), (nat_lit 1277, Int.ofNat (nat_lit 4255534080)), (nat_lit 1295, Int.ofNat (nat_lit 3789918720)), (nat_lit 1372, Int.ofNat (nat_lit 839677440)), (nat_lit 1373, Int.ofNat (nat_lit 1603536000)), (nat_lit 1374, Int.ofNat (nat_lit 615212160)), (nat_lit 1375, Int.ofNat (nat_lit 103864320)), (nat_lit 1376, Int.ofNat (nat_lit 25159680)), (nat_lit 1380, Int.ofNat (nat_lit 1531037760)), (nat_lit 1382, Int.ofNat (nat_lit 460951440)), (nat_lit 1391, Int.ofNat (nat_lit 1465409280)), (nat_lit 1392, Int.ofNat (nat_lit 1111580160)), (nat_lit 1396, Int.ofNat (nat_lit 103864320)), (nat_lit 1397, Int.ofNat (nat_lit 207728640)), (nat_lit 1398, Int.ofNat (nat_lit 2424376752)), (nat_lit 1400, Int.ofNat (nat_lit 1101237360)), (nat_lit 1401, Int.ofNat (nat_lit 1180247040)), (nat_lit 1402, Int.ofNat (nat_lit 2293143552)), (nat_lit 1403, Int.ofNat (nat_lit 3586383360)), (nat_lit 1410, Int.ofNat (nat_lit 423540480)), (nat_lit 1413, Int.ofNat (nat_lit 107089920)), (nat_lit 1414, Int.ofNat (nat_lit 264499200)), (nat_lit 1415, Int.ofNat (nat_lit 421908480)), (nat_lit 1416, Int.ofNat (nat_lit 2576627520)), (nat_lit 1417, Int.ofNat (nat_lit 1293281520)), (nat_lit 1418, Int.ofNat (nat_lit 2694257760)), (nat_lit 1419, Int.ofNat (nat_lit 3482496240)), (nat_lit 1420, Int.ofNat (nat_lit 5041760400)), (nat_lit 1421, Int.ofNat (nat_lit 6677153280)), (nat_lit 1429, Int.ofNat (nat_lit 353829120)), (nat_lit 1430, Int.ofNat (nat_lit 403703040)), (nat_lit 1431, Int.ofNat (nat_lit 460473600)), (nat_lit 1432, Int.ofNat (nat_lit 621108480)), (nat_lit 1433, Int.ofNat (nat_lit 781743360)), (nat_lit 1434, Int.ofNat (nat_lit 3019296000)), (nat_lit 1435, Int.ofNat (nat_lit 2332497120)), (nat_lit 1436, Int.ofNat (nat_lit 4135339680)), (nat_lit 1437, Int.ofNat (nat_lit 5254997280)), (nat_lit 1438, Int.ofNat (nat_lit 7178238240)), (nat_lit 1439, Int.ofNat (nat_lit 9115705440)), (nat_lit 1448, Int.ofNat (nat_lit 827243520)), (nat_lit 1449, Int.ofNat (nat_lit 1400517120)), (nat_lit 1450, Int.ofNat (nat_lit 1514058240)), (nat_lit 1451, Int.ofNat (nat_lit 1627599360)), (nat_lit 1452, Int.ofNat (nat_lit 3755136000)), (nat_lit 1453, Int.ofNat (nat_lit 3303554880)), (nat_lit 1454, Int.ofNat (nat_lit 5488183200)), (nat_lit 1455, Int.ofNat (nat_lit 6428383680)), (nat_lit 1456, Int.ofNat (nat_lit 8473755840)), (nat_lit 1457, Int.ofNat (nat_lit 10519128000)), (nat_lit 1467, Int.ofNat (nat_lit 1454507520)), (nat_lit 1468, Int.ofNat (nat_lit 2574428160)), (nat_lit 1469, Int.ofNat (nat_lit 2590556160)), (nat_lit 1470, Int.ofNat (nat_lit 4644494400)), (nat_lit 1471, Int.ofNat (nat_lit 4143129600)), (nat_lit 1472, Int.ofNat (nat_lit 6663591840)), (nat_lit 1473, Int.ofNat (nat_lit 7216020480)), (nat_lit 1474, Int.ofNat (nat_lit 9259238400)), (nat_lit 1475, Int.ofNat (nat_lit 11302456320)), (nat_lit 1486, Int.ofNat (nat_lit 2105018880)), (nat_lit 1487, Int.ofNat (nat_lit 3744445440)), (nat_lit 1488, Int.ofNat (nat_lit 5639632320)), (nat_lit 1489, Int.ofNat (nat_lit 4968497280)), (nat_lit 1490, Int.ofNat (nat_lit 7889319840)), (nat_lit 1491, Int.ofNat (nat_lit 7679809920)), (nat_lit 1492, Int.ofNat (nat_lit 9531219840)), (nat_lit 1493, Int.ofNat (nat_lit 11673385920)), (nat_lit 1505, Int.ofNat (nat_lit 2958144000)), (nat_lit 1506, Int.ofNat (nat_lit 6511653120)), (nat_lit 1507, Int.ofNat (nat_lit 5589568320)), (nat_lit 1508, Int.ofNat (nat_lit 8928903840)), (nat_lit 1509, Int.ofNat (nat_lit 8835408960)), (nat_lit 1510, Int.ofNat (nat_lit 9405332160))]
theorem block009_data_flat158_step : block009_data_flat158 = (CoefficientMerge.fastMerge block009_data_flat078 block009_data_flat157) := by decide +kernel
theorem block009_data_flat158_original : block009_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8141283000 : Int) atom0655Coded) (CoefficientMerge.scale (12793243320 : Int) atom0656Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8558934480 : Int) atom0657Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11377463760 : Int) atom0658Coded) (CoefficientMerge.scale (4082641920 : Int) atom0659Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5228697600 : Int) atom0660Coded) (CoefficientMerge.scale (8587353600 : Int) atom0661Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (258048000 : Int) atom0662Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4255534080 : Int) atom0663Coded) (CoefficientMerge.scale (3789918720 : Int) atom0664Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (839677440 : Int) atom0665Coded) (CoefficientMerge.scale (1603536000 : Int) atom0666Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (615212160 : Int) atom0667Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0668Coded) (CoefficientMerge.scale (25159680 : Int) atom0669Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1531037760 : Int) atom0670Coded) (CoefficientMerge.scale (460951440 : Int) atom0671Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1465409280 : Int) atom0672Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1111580160 : Int) atom0673Coded) (CoefficientMerge.scale (103864320 : Int) atom0674Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0675Coded) (CoefficientMerge.scale (2424376752 : Int) atom0676Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1101237360 : Int) atom0677Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0678Coded) (CoefficientMerge.scale (2293143552 : Int) atom0679Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0680Coded) (CoefficientMerge.scale (423540480 : Int) atom0681Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107089920 : Int) atom0682Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264499200 : Int) atom0683Coded) (CoefficientMerge.scale (421908480 : Int) atom0684Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2576627520 : Int) atom0685Coded) (CoefficientMerge.scale (1293281520 : Int) atom0686Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2694257760 : Int) atom0687Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3482496240 : Int) atom0688Coded) (CoefficientMerge.scale (5041760400 : Int) atom0689Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6677153280 : Int) atom0690Coded) (CoefficientMerge.scale (353829120 : Int) atom0691Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (403703040 : Int) atom0692Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (460473600 : Int) atom0693Coded) (CoefficientMerge.scale (621108480 : Int) atom0694Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (781743360 : Int) atom0695Coded) (CoefficientMerge.scale (3019296000 : Int) atom0696Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2332497120 : Int) atom0697Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4135339680 : Int) atom0698Coded) (CoefficientMerge.scale (5254997280 : Int) atom0699Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7178238240 : Int) atom0700Coded) (CoefficientMerge.scale (9115705440 : Int) atom0701Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (827243520 : Int) atom0702Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1400517120 : Int) atom0703Coded) (CoefficientMerge.scale (1514058240 : Int) atom0704Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1627599360 : Int) atom0705Coded) (CoefficientMerge.scale (3755136000 : Int) atom0706Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3303554880 : Int) atom0707Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5488183200 : Int) atom0708Coded) (CoefficientMerge.scale (6428383680 : Int) atom0709Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8473755840 : Int) atom0710Coded) (CoefficientMerge.scale (10519128000 : Int) atom0711Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1454507520 : Int) atom0712Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2574428160 : Int) atom0713Coded) (CoefficientMerge.scale (2590556160 : Int) atom0714Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4644494400 : Int) atom0715Coded) (CoefficientMerge.scale (4143129600 : Int) atom0716Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6663591840 : Int) atom0717Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7216020480 : Int) atom0718Coded) (CoefficientMerge.scale (9259238400 : Int) atom0719Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11302456320 : Int) atom0720Coded) (CoefficientMerge.scale (2105018880 : Int) atom0721Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3744445440 : Int) atom0722Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5639632320 : Int) atom0723Coded) (CoefficientMerge.scale (4968497280 : Int) atom0724Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7889319840 : Int) atom0725Coded) (CoefficientMerge.scale (7679809920 : Int) atom0726Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9531219840 : Int) atom0727Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11673385920 : Int) atom0728Coded) (CoefficientMerge.scale (2958144000 : Int) atom0729Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6511653120 : Int) atom0730Coded) (CoefficientMerge.scale (5589568320 : Int) atom0731Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8928903840 : Int) atom0732Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8835408960 : Int) atom0733Coded) (CoefficientMerge.scale (9405332160 : Int) atom0734Coded)))))))) := by
  rw [block009_data_flat158_step, block009_data_flat078_original, block009_data_flat157_original]
def block009_data_flat159 : CoefficientMerge.Poly := [(nat_lit 1238, Int.ofNat (nat_lit 8141283000)), (nat_lit 1239, Int.ofNat (nat_lit 12793243320)), (nat_lit 1240, Int.ofNat (nat_lit 8558934480)), (nat_lit 1241, Int.ofNat (nat_lit 11377463760)), (nat_lit 1257, Int.ofNat (nat_lit 4082641920)), (nat_lit 1258, Int.ofNat (nat_lit 5228697600)), (nat_lit 1259, Int.ofNat (nat_lit 8587353600)), (nat_lit 1276, Int.ofNat (nat_lit 258048000)), (nat_lit 1277, Int.ofNat (nat_lit 4255534080)), (nat_lit 1295, Int.ofNat (nat_lit 3789918720)), (nat_lit 1372, Int.ofNat (nat_lit 839677440)), (nat_lit 1373, Int.ofNat (nat_lit 1603536000)), (nat_lit 1374, Int.ofNat (nat_lit 615212160)), (nat_lit 1375, Int.ofNat (nat_lit 103864320)), (nat_lit 1376, Int.ofNat (nat_lit 25159680)), (nat_lit 1380, Int.ofNat (nat_lit 1531037760)), (nat_lit 1382, Int.ofNat (nat_lit 460951440)), (nat_lit 1391, Int.ofNat (nat_lit 1465409280)), (nat_lit 1392, Int.ofNat (nat_lit 1111580160)), (nat_lit 1396, Int.ofNat (nat_lit 103864320)), (nat_lit 1397, Int.ofNat (nat_lit 207728640)), (nat_lit 1398, Int.ofNat (nat_lit 2424376752)), (nat_lit 1400, Int.ofNat (nat_lit 1101237360)), (nat_lit 1401, Int.ofNat (nat_lit 1180247040)), (nat_lit 1402, Int.ofNat (nat_lit 2293143552)), (nat_lit 1403, Int.ofNat (nat_lit 3586383360)), (nat_lit 1410, Int.ofNat (nat_lit 423540480)), (nat_lit 1413, Int.ofNat (nat_lit 107089920)), (nat_lit 1414, Int.ofNat (nat_lit 264499200)), (nat_lit 1415, Int.ofNat (nat_lit 421908480)), (nat_lit 1416, Int.ofNat (nat_lit 2576627520)), (nat_lit 1417, Int.ofNat (nat_lit 1293281520)), (nat_lit 1418, Int.ofNat (nat_lit 2694257760)), (nat_lit 1419, Int.ofNat (nat_lit 3482496240)), (nat_lit 1420, Int.ofNat (nat_lit 5041760400)), (nat_lit 1421, Int.ofNat (nat_lit 6677153280)), (nat_lit 1429, Int.ofNat (nat_lit 353829120)), (nat_lit 1430, Int.ofNat (nat_lit 403703040)), (nat_lit 1431, Int.ofNat (nat_lit 460473600)), (nat_lit 1432, Int.ofNat (nat_lit 621108480)), (nat_lit 1433, Int.ofNat (nat_lit 781743360)), (nat_lit 1434, Int.ofNat (nat_lit 3019296000)), (nat_lit 1435, Int.ofNat (nat_lit 2332497120)), (nat_lit 1436, Int.ofNat (nat_lit 4135339680)), (nat_lit 1437, Int.ofNat (nat_lit 5254997280)), (nat_lit 1438, Int.ofNat (nat_lit 7178238240)), (nat_lit 1439, Int.ofNat (nat_lit 9115705440)), (nat_lit 1448, Int.ofNat (nat_lit 827243520)), (nat_lit 1449, Int.ofNat (nat_lit 1400517120)), (nat_lit 1450, Int.ofNat (nat_lit 1514058240)), (nat_lit 1451, Int.ofNat (nat_lit 1627599360)), (nat_lit 1452, Int.ofNat (nat_lit 3755136000)), (nat_lit 1453, Int.ofNat (nat_lit 3303554880)), (nat_lit 1454, Int.ofNat (nat_lit 5488183200)), (nat_lit 1455, Int.ofNat (nat_lit 6428383680)), (nat_lit 1456, Int.ofNat (nat_lit 8473755840)), (nat_lit 1457, Int.ofNat (nat_lit 10519128000)), (nat_lit 1467, Int.ofNat (nat_lit 1454507520)), (nat_lit 1468, Int.ofNat (nat_lit 2574428160)), (nat_lit 1469, Int.ofNat (nat_lit 2590556160)), (nat_lit 1470, Int.ofNat (nat_lit 4644494400)), (nat_lit 1471, Int.ofNat (nat_lit 4143129600)), (nat_lit 1472, Int.ofNat (nat_lit 6663591840)), (nat_lit 1473, Int.ofNat (nat_lit 7216020480)), (nat_lit 1474, Int.ofNat (nat_lit 9259238400)), (nat_lit 1475, Int.ofNat (nat_lit 11302456320)), (nat_lit 1486, Int.ofNat (nat_lit 2105018880)), (nat_lit 1487, Int.ofNat (nat_lit 3744445440)), (nat_lit 1488, Int.ofNat (nat_lit 5639632320)), (nat_lit 1489, Int.ofNat (nat_lit 4968497280)), (nat_lit 1490, Int.ofNat (nat_lit 7889319840)), (nat_lit 1491, Int.ofNat (nat_lit 7679809920)), (nat_lit 1492, Int.ofNat (nat_lit 9531219840)), (nat_lit 1493, Int.ofNat (nat_lit 11673385920)), (nat_lit 1505, Int.ofNat (nat_lit 2958144000)), (nat_lit 1506, Int.ofNat (nat_lit 6511653120)), (nat_lit 1507, Int.ofNat (nat_lit 5589568320)), (nat_lit 1508, Int.ofNat (nat_lit 8928903840)), (nat_lit 1509, Int.ofNat (nat_lit 8835408960)), (nat_lit 1510, Int.ofNat (nat_lit 9405332160))]
theorem block009_data_flat159_step : block009_data_flat159 = (CoefficientMerge.trim block009_data_flat158) := by decide +kernel
theorem block009_data_flat159_original : block009_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8141283000 : Int) atom0655Coded) (CoefficientMerge.scale (12793243320 : Int) atom0656Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8558934480 : Int) atom0657Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11377463760 : Int) atom0658Coded) (CoefficientMerge.scale (4082641920 : Int) atom0659Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5228697600 : Int) atom0660Coded) (CoefficientMerge.scale (8587353600 : Int) atom0661Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (258048000 : Int) atom0662Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4255534080 : Int) atom0663Coded) (CoefficientMerge.scale (3789918720 : Int) atom0664Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (839677440 : Int) atom0665Coded) (CoefficientMerge.scale (1603536000 : Int) atom0666Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (615212160 : Int) atom0667Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0668Coded) (CoefficientMerge.scale (25159680 : Int) atom0669Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1531037760 : Int) atom0670Coded) (CoefficientMerge.scale (460951440 : Int) atom0671Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1465409280 : Int) atom0672Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1111580160 : Int) atom0673Coded) (CoefficientMerge.scale (103864320 : Int) atom0674Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0675Coded) (CoefficientMerge.scale (2424376752 : Int) atom0676Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1101237360 : Int) atom0677Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0678Coded) (CoefficientMerge.scale (2293143552 : Int) atom0679Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0680Coded) (CoefficientMerge.scale (423540480 : Int) atom0681Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107089920 : Int) atom0682Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264499200 : Int) atom0683Coded) (CoefficientMerge.scale (421908480 : Int) atom0684Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2576627520 : Int) atom0685Coded) (CoefficientMerge.scale (1293281520 : Int) atom0686Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2694257760 : Int) atom0687Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3482496240 : Int) atom0688Coded) (CoefficientMerge.scale (5041760400 : Int) atom0689Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6677153280 : Int) atom0690Coded) (CoefficientMerge.scale (353829120 : Int) atom0691Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (403703040 : Int) atom0692Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (460473600 : Int) atom0693Coded) (CoefficientMerge.scale (621108480 : Int) atom0694Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (781743360 : Int) atom0695Coded) (CoefficientMerge.scale (3019296000 : Int) atom0696Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2332497120 : Int) atom0697Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4135339680 : Int) atom0698Coded) (CoefficientMerge.scale (5254997280 : Int) atom0699Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7178238240 : Int) atom0700Coded) (CoefficientMerge.scale (9115705440 : Int) atom0701Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (827243520 : Int) atom0702Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1400517120 : Int) atom0703Coded) (CoefficientMerge.scale (1514058240 : Int) atom0704Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1627599360 : Int) atom0705Coded) (CoefficientMerge.scale (3755136000 : Int) atom0706Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3303554880 : Int) atom0707Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5488183200 : Int) atom0708Coded) (CoefficientMerge.scale (6428383680 : Int) atom0709Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8473755840 : Int) atom0710Coded) (CoefficientMerge.scale (10519128000 : Int) atom0711Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1454507520 : Int) atom0712Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2574428160 : Int) atom0713Coded) (CoefficientMerge.scale (2590556160 : Int) atom0714Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4644494400 : Int) atom0715Coded) (CoefficientMerge.scale (4143129600 : Int) atom0716Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6663591840 : Int) atom0717Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7216020480 : Int) atom0718Coded) (CoefficientMerge.scale (9259238400 : Int) atom0719Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11302456320 : Int) atom0720Coded) (CoefficientMerge.scale (2105018880 : Int) atom0721Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3744445440 : Int) atom0722Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5639632320 : Int) atom0723Coded) (CoefficientMerge.scale (4968497280 : Int) atom0724Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7889319840 : Int) atom0725Coded) (CoefficientMerge.scale (7679809920 : Int) atom0726Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9531219840 : Int) atom0727Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11673385920 : Int) atom0728Coded) (CoefficientMerge.scale (2958144000 : Int) atom0729Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6511653120 : Int) atom0730Coded) (CoefficientMerge.scale (5589568320 : Int) atom0731Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8928903840 : Int) atom0732Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8835408960 : Int) atom0733Coded) (CoefficientMerge.scale (9405332160 : Int) atom0734Coded))))))))) := by
  rw [block009_data_flat159_step, block009_data_flat158_original]
theorem block009_data : block009 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8141283000 : Int) atom0655Coded) (CoefficientMerge.scale (12793243320 : Int) atom0656Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8558934480 : Int) atom0657Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11377463760 : Int) atom0658Coded) (CoefficientMerge.scale (4082641920 : Int) atom0659Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5228697600 : Int) atom0660Coded) (CoefficientMerge.scale (8587353600 : Int) atom0661Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (258048000 : Int) atom0662Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4255534080 : Int) atom0663Coded) (CoefficientMerge.scale (3789918720 : Int) atom0664Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (839677440 : Int) atom0665Coded) (CoefficientMerge.scale (1603536000 : Int) atom0666Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (615212160 : Int) atom0667Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0668Coded) (CoefficientMerge.scale (25159680 : Int) atom0669Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1531037760 : Int) atom0670Coded) (CoefficientMerge.scale (460951440 : Int) atom0671Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1465409280 : Int) atom0672Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1111580160 : Int) atom0673Coded) (CoefficientMerge.scale (103864320 : Int) atom0674Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0675Coded) (CoefficientMerge.scale (2424376752 : Int) atom0676Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1101237360 : Int) atom0677Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0678Coded) (CoefficientMerge.scale (2293143552 : Int) atom0679Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0680Coded) (CoefficientMerge.scale (423540480 : Int) atom0681Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (107089920 : Int) atom0682Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264499200 : Int) atom0683Coded) (CoefficientMerge.scale (421908480 : Int) atom0684Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2576627520 : Int) atom0685Coded) (CoefficientMerge.scale (1293281520 : Int) atom0686Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2694257760 : Int) atom0687Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3482496240 : Int) atom0688Coded) (CoefficientMerge.scale (5041760400 : Int) atom0689Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6677153280 : Int) atom0690Coded) (CoefficientMerge.scale (353829120 : Int) atom0691Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (403703040 : Int) atom0692Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (460473600 : Int) atom0693Coded) (CoefficientMerge.scale (621108480 : Int) atom0694Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (781743360 : Int) atom0695Coded) (CoefficientMerge.scale (3019296000 : Int) atom0696Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2332497120 : Int) atom0697Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4135339680 : Int) atom0698Coded) (CoefficientMerge.scale (5254997280 : Int) atom0699Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7178238240 : Int) atom0700Coded) (CoefficientMerge.scale (9115705440 : Int) atom0701Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (827243520 : Int) atom0702Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1400517120 : Int) atom0703Coded) (CoefficientMerge.scale (1514058240 : Int) atom0704Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1627599360 : Int) atom0705Coded) (CoefficientMerge.scale (3755136000 : Int) atom0706Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3303554880 : Int) atom0707Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5488183200 : Int) atom0708Coded) (CoefficientMerge.scale (6428383680 : Int) atom0709Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8473755840 : Int) atom0710Coded) (CoefficientMerge.scale (10519128000 : Int) atom0711Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1454507520 : Int) atom0712Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2574428160 : Int) atom0713Coded) (CoefficientMerge.scale (2590556160 : Int) atom0714Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4644494400 : Int) atom0715Coded) (CoefficientMerge.scale (4143129600 : Int) atom0716Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6663591840 : Int) atom0717Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7216020480 : Int) atom0718Coded) (CoefficientMerge.scale (9259238400 : Int) atom0719Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11302456320 : Int) atom0720Coded) (CoefficientMerge.scale (2105018880 : Int) atom0721Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3744445440 : Int) atom0722Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5639632320 : Int) atom0723Coded) (CoefficientMerge.scale (4968497280 : Int) atom0724Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7889319840 : Int) atom0725Coded) (CoefficientMerge.scale (7679809920 : Int) atom0726Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9531219840 : Int) atom0727Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11673385920 : Int) atom0728Coded) (CoefficientMerge.scale (2958144000 : Int) atom0729Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6511653120 : Int) atom0730Coded) (CoefficientMerge.scale (5589568320 : Int) atom0731Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8928903840 : Int) atom0732Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8835408960 : Int) atom0733Coded) (CoefficientMerge.scale (9405332160 : Int) atom0734Coded)))))))) := by
  have h : block009 = block009_data_flat159 := by decide +kernel
  exact h.trans block009_data_flat159_original
theorem block009_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) block009 := by
  rw [block009_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0655Coded_nonneg g hg hA hB) (atom0656Coded_nonneg g hg hA hB)) (add_nonneg (atom0657Coded_nonneg g hg hA hB) (add_nonneg (atom0658Coded_nonneg g hg hA hB) (atom0659Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0660Coded_nonneg g hg hA hB) (atom0661Coded_nonneg g hg hA hB)) (add_nonneg (atom0662Coded_nonneg g hg hA hB) (add_nonneg (atom0663Coded_nonneg g hg hA hB) (atom0664Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0665Coded_nonneg g hg hA hB) (atom0666Coded_nonneg g hg hA hB)) (add_nonneg (atom0667Coded_nonneg g hg hA hB) (add_nonneg (atom0668Coded_nonneg g hg hA hB) (atom0669Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0670Coded_nonneg g hg hA hB) (atom0671Coded_nonneg g hg hA hB)) (add_nonneg (atom0672Coded_nonneg g hg hA hB) (add_nonneg (atom0673Coded_nonneg g hg hA hB) (atom0674Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0675Coded_nonneg g hg hA hB) (atom0676Coded_nonneg g hg hA hB)) (add_nonneg (atom0677Coded_nonneg g hg hA hB) (add_nonneg (atom0678Coded_nonneg g hg hA hB) (atom0679Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0680Coded_nonneg g hg hA hB) (atom0681Coded_nonneg g hg hA hB)) (add_nonneg (atom0682Coded_nonneg g hg hA hB) (add_nonneg (atom0683Coded_nonneg g hg hA hB) (atom0684Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0685Coded_nonneg g hg hA hB) (atom0686Coded_nonneg g hg hA hB)) (add_nonneg (atom0687Coded_nonneg g hg hA hB) (add_nonneg (atom0688Coded_nonneg g hg hA hB) (atom0689Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0690Coded_nonneg g hg hA hB) (atom0691Coded_nonneg g hg hA hB)) (add_nonneg (atom0692Coded_nonneg g hg hA hB) (add_nonneg (atom0693Coded_nonneg g hg hA hB) (atom0694Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0695Coded_nonneg g hg hA hB) (atom0696Coded_nonneg g hg hA hB)) (add_nonneg (atom0697Coded_nonneg g hg hA hB) (add_nonneg (atom0698Coded_nonneg g hg hA hB) (atom0699Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0700Coded_nonneg g hg hA hB) (atom0701Coded_nonneg g hg hA hB)) (add_nonneg (atom0702Coded_nonneg g hg hA hB) (add_nonneg (atom0703Coded_nonneg g hg hA hB) (atom0704Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0705Coded_nonneg g hg hA hB) (atom0706Coded_nonneg g hg hA hB)) (add_nonneg (atom0707Coded_nonneg g hg hA hB) (add_nonneg (atom0708Coded_nonneg g hg hA hB) (atom0709Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0710Coded_nonneg g hg hA hB) (atom0711Coded_nonneg g hg hA hB)) (add_nonneg (atom0712Coded_nonneg g hg hA hB) (add_nonneg (atom0713Coded_nonneg g hg hA hB) (atom0714Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0715Coded_nonneg g hg hA hB) (atom0716Coded_nonneg g hg hA hB)) (add_nonneg (atom0717Coded_nonneg g hg hA hB) (add_nonneg (atom0718Coded_nonneg g hg hA hB) (atom0719Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0720Coded_nonneg g hg hA hB) (atom0721Coded_nonneg g hg hA hB)) (add_nonneg (atom0722Coded_nonneg g hg hA hB) (add_nonneg (atom0723Coded_nonneg g hg hA hB) (atom0724Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0725Coded_nonneg g hg hA hB) (atom0726Coded_nonneg g hg hA hB)) (add_nonneg (atom0727Coded_nonneg g hg hA hB) (add_nonneg (atom0728Coded_nonneg g hg hA hB) (atom0729Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0730Coded_nonneg g hg hA hB) (atom0731Coded_nonneg g hg hA hB)) (add_nonneg (atom0732Coded_nonneg g hg hA hB) (add_nonneg (atom0733Coded_nonneg g hg hA hB) (atom0734Coded_nonneg g hg hA hB))))))))

end APPT.Finite18
