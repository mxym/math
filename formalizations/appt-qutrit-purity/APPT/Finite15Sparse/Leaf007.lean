-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def atom0553 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0553 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0553 = ((g 6) * (g 9) * (g 10)) := by
  norm_num [atom0553, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0553_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60699240 : Int) atom0553) := by
  rw [SparsePolynomial.eval_scale, eval_atom0553]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0553Coded : CoefficientMerge.Poly := [(nat_lit 1495, Int.ofNat (nat_lit 1))]
theorem atom0553Coded_decode : atom0553 = SparsePolynomial.decodeCubic 15 atom0553Coded := by decide +kernel
theorem atom0553Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (60699240 : Int) atom0553Coded) := by
  have h := atom0553_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0553Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0554 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0554 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0554 = ((g 6) * (g 9) * (g 11)) := by
  norm_num [atom0554, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0554_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126096480 : Int) atom0554) := by
  rw [SparsePolynomial.eval_scale, eval_atom0554]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0554Coded : CoefficientMerge.Poly := [(nat_lit 1496, Int.ofNat (nat_lit 1))]
theorem atom0554Coded_decode : atom0554 = SparsePolynomial.decodeCubic 15 atom0554Coded := by decide +kernel
theorem atom0554Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (126096480 : Int) atom0554Coded) := by
  have h := atom0554_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0554Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0555 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0555 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0555 = ((g 6) * (g 9) * (g 12)) := by
  norm_num [atom0555, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0555_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (156091320 : Int) atom0555) := by
  rw [SparsePolynomial.eval_scale, eval_atom0555]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0555Coded : CoefficientMerge.Poly := [(nat_lit 1497, Int.ofNat (nat_lit 1))]
theorem atom0555Coded_decode : atom0555 = SparsePolynomial.decodeCubic 15 atom0555Coded := by decide +kernel
theorem atom0555Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (156091320 : Int) atom0555Coded) := by
  have h := atom0555_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0555Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0556 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0556 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0556 = ((g 6) * (g 9) * (g 13)) := by
  norm_num [atom0556, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0556_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (110217240 : Int) atom0556) := by
  rw [SparsePolynomial.eval_scale, eval_atom0556]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0556Coded : CoefficientMerge.Poly := [(nat_lit 1498, Int.ofNat (nat_lit 1))]
theorem atom0556Coded_decode : atom0556 = SparsePolynomial.decodeCubic 15 atom0556Coded := by decide +kernel
theorem atom0556Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (110217240 : Int) atom0556Coded) := by
  have h := atom0556_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0556Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0557 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0557 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0557 = ((g 6) * (g 9) * (g 14)) := by
  norm_num [atom0557, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0557_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (200423160 : Int) atom0557) := by
  rw [SparsePolynomial.eval_scale, eval_atom0557]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0557Coded : CoefficientMerge.Poly := [(nat_lit 1499, Int.ofNat (nat_lit 1))]
theorem atom0557Coded_decode : atom0557 = SparsePolynomial.decodeCubic 15 atom0557Coded := by decide +kernel
theorem atom0557Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (200423160 : Int) atom0557Coded) := by
  have h := atom0557_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0557Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0558 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0558 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0558 = ((g 6) * (g 10) * (g 10)) := by
  norm_num [atom0558, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0558_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26469504 : Int) atom0558) := by
  rw [SparsePolynomial.eval_scale, eval_atom0558]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0558Coded : CoefficientMerge.Poly := [(nat_lit 1510, Int.ofNat (nat_lit 1))]
theorem atom0558Coded_decode : atom0558 = SparsePolynomial.decodeCubic 15 atom0558Coded := by decide +kernel
theorem atom0558Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (26469504 : Int) atom0558Coded) := by
  have h := atom0558_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0558Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0559 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0559 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0559 = ((g 6) * (g 10) * (g 11)) := by
  norm_num [atom0559, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0559_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (100582560 : Int) atom0559) := by
  rw [SparsePolynomial.eval_scale, eval_atom0559]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0559Coded : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 1))]
theorem atom0559Coded_decode : atom0559 = SparsePolynomial.decodeCubic 15 atom0559Coded := by decide +kernel
theorem atom0559Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (100582560 : Int) atom0559Coded) := by
  have h := atom0559_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0559Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0560 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0560 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0560 = ((g 6) * (g 10) * (g 12)) := by
  norm_num [atom0560, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0560_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (147665700 : Int) atom0560) := by
  rw [SparsePolynomial.eval_scale, eval_atom0560]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0560Coded : CoefficientMerge.Poly := [(nat_lit 1512, Int.ofNat (nat_lit 1))]
theorem atom0560Coded_decode : atom0560 = SparsePolynomial.decodeCubic 15 atom0560Coded := by decide +kernel
theorem atom0560Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (147665700 : Int) atom0560Coded) := by
  have h := atom0560_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0560Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0561 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0561 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0561 = ((g 6) * (g 10) * (g 13)) := by
  norm_num [atom0561, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0561_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (118586160 : Int) atom0561) := by
  rw [SparsePolynomial.eval_scale, eval_atom0561]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0561Coded : CoefficientMerge.Poly := [(nat_lit 1513, Int.ofNat (nat_lit 1))]
theorem atom0561Coded_decode : atom0561 = SparsePolynomial.decodeCubic 15 atom0561Coded := by decide +kernel
theorem atom0561Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (118586160 : Int) atom0561Coded) := by
  have h := atom0561_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0561Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0562 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0562 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0562 = ((g 6) * (g 10) * (g 14)) := by
  norm_num [atom0562, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0562_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (173295990 : Int) atom0562) := by
  rw [SparsePolynomial.eval_scale, eval_atom0562]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0562Coded : CoefficientMerge.Poly := [(nat_lit 1514, Int.ofNat (nat_lit 1))]
theorem atom0562Coded_decode : atom0562 = SparsePolynomial.decodeCubic 15 atom0562Coded := by decide +kernel
theorem atom0562Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (173295990 : Int) atom0562Coded) := by
  have h := atom0562_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0562Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0563 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0563 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0563 = ((g 6) * (g 11) * (g 11)) := by
  norm_num [atom0563, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0563_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (86044680 : Int) atom0563) := by
  rw [SparsePolynomial.eval_scale, eval_atom0563]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0563Coded : CoefficientMerge.Poly := [(nat_lit 1526, Int.ofNat (nat_lit 1))]
theorem atom0563Coded_decode : atom0563 = SparsePolynomial.decodeCubic 15 atom0563Coded := by decide +kernel
theorem atom0563Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (86044680 : Int) atom0563Coded) := by
  have h := atom0563_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0563Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0564 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0564 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0564 = ((g 6) * (g 11) * (g 12)) := by
  norm_num [atom0564, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0564_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (170421840 : Int) atom0564) := by
  rw [SparsePolynomial.eval_scale, eval_atom0564]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0564Coded : CoefficientMerge.Poly := [(nat_lit 1527, Int.ofNat (nat_lit 1))]
theorem atom0564Coded_decode : atom0564 = SparsePolynomial.decodeCubic 15 atom0564Coded := by decide +kernel
theorem atom0564Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (170421840 : Int) atom0564Coded) := by
  have h := atom0564_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0564Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0565 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0565 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0565 = ((g 6) * (g 11) * (g 13)) := by
  norm_num [atom0565, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0565_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (146729880 : Int) atom0565) := by
  rw [SparsePolynomial.eval_scale, eval_atom0565]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0565Coded : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 1))]
theorem atom0565Coded_decode : atom0565 = SparsePolynomial.decodeCubic 15 atom0565Coded := by decide +kernel
theorem atom0565Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (146729880 : Int) atom0565Coded) := by
  have h := atom0565_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0565Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0566 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0566 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0566 = ((g 6) * (g 11) * (g 14)) := by
  norm_num [atom0566, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0566_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (224658360 : Int) atom0566) := by
  rw [SparsePolynomial.eval_scale, eval_atom0566]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0566Coded : CoefficientMerge.Poly := [(nat_lit 1529, Int.ofNat (nat_lit 1))]
theorem atom0566Coded_decode : atom0566 = SparsePolynomial.decodeCubic 15 atom0566Coded := by decide +kernel
theorem atom0566Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (224658360 : Int) atom0566Coded) := by
  have h := atom0566_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0566Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0567 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0567 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0567 = ((g 6) * (g 12) * (g 12)) := by
  norm_num [atom0567, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0567_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (67597740 : Int) atom0567) := by
  rw [SparsePolynomial.eval_scale, eval_atom0567]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0567Coded : CoefficientMerge.Poly := [(nat_lit 1542, Int.ofNat (nat_lit 1))]
theorem atom0567Coded_decode : atom0567 = SparsePolynomial.decodeCubic 15 atom0567Coded := by decide +kernel
theorem atom0567Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (67597740 : Int) atom0567Coded) := by
  have h := atom0567_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0567Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0568 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0568 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0568 = ((g 6) * (g 12) * (g 13)) := by
  norm_num [atom0568, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0568_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (129105900 : Int) atom0568) := by
  rw [SparsePolynomial.eval_scale, eval_atom0568]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0568Coded : CoefficientMerge.Poly := [(nat_lit 1543, Int.ofNat (nat_lit 1))]
theorem atom0568Coded_decode : atom0568 = SparsePolynomial.decodeCubic 15 atom0568Coded := by decide +kernel
theorem atom0568Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (129105900 : Int) atom0568Coded) := by
  have h := atom0568_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0568Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0569 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0569 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0569 = ((g 6) * (g 12) * (g 14)) := by
  norm_num [atom0569, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0569_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (220009230 : Int) atom0569) := by
  rw [SparsePolynomial.eval_scale, eval_atom0569]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0569Coded : CoefficientMerge.Poly := [(nat_lit 1544, Int.ofNat (nat_lit 1))]
theorem atom0569Coded_decode : atom0569 = SparsePolynomial.decodeCubic 15 atom0569Coded := by decide +kernel
theorem atom0569Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (220009230 : Int) atom0569Coded) := by
  have h := atom0569_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0569Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0570 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0570 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0570 = ((g 6) * (g 13) * (g 13)) := by
  norm_num [atom0570, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0570_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40960080 : Int) atom0570) := by
  rw [SparsePolynomial.eval_scale, eval_atom0570]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0570Coded : CoefficientMerge.Poly := [(nat_lit 1558, Int.ofNat (nat_lit 1))]
theorem atom0570Coded_decode : atom0570 = SparsePolynomial.decodeCubic 15 atom0570Coded := by decide +kernel
theorem atom0570Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (40960080 : Int) atom0570Coded) := by
  have h := atom0570_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0570Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0571 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0571 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0571 = ((g 6) * (g 13) * (g 14)) := by
  norm_num [atom0571, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0571_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (183914010 : Int) atom0571) := by
  rw [SparsePolynomial.eval_scale, eval_atom0571]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0571Coded : CoefficientMerge.Poly := [(nat_lit 1559, Int.ofNat (nat_lit 1))]
theorem atom0571Coded_decode : atom0571 = SparsePolynomial.decodeCubic 15 atom0571Coded := by decide +kernel
theorem atom0571Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (183914010 : Int) atom0571Coded) := by
  have h := atom0571_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0571Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0572 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0572 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0572 = ((g 6) * (g 14) * (g 14)) := by
  norm_num [atom0572, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0572_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (132831090 : Int) atom0572) := by
  rw [SparsePolynomial.eval_scale, eval_atom0572]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0572Coded : CoefficientMerge.Poly := [(nat_lit 1574, Int.ofNat (nat_lit 1))]
theorem atom0572Coded_decode : atom0572 = SparsePolynomial.decodeCubic 15 atom0572Coded := by decide +kernel
theorem atom0572Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (132831090 : Int) atom0572Coded) := by
  have h := atom0572_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0572Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0573 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0573 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0573 = ((g 7) * (g 7) * (g 7)) := by
  norm_num [atom0573, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0573_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13440 : Int) atom0573) := by
  rw [SparsePolynomial.eval_scale, eval_atom0573]
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 7) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0573Coded : CoefficientMerge.Poly := [(nat_lit 1687, Int.ofNat (nat_lit 1))]
theorem atom0573Coded_decode : atom0573 = SparsePolynomial.decodeCubic 15 atom0573Coded := by decide +kernel
theorem atom0573Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (13440 : Int) atom0573Coded) := by
  have h := atom0573_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0573Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0574 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0574 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0574 = ((g 7) * (g 8) * (g 8)) := by
  norm_num [atom0574, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0574_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2284800 : Int) atom0574) := by
  rw [SparsePolynomial.eval_scale, eval_atom0574]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0574Coded : CoefficientMerge.Poly := [(nat_lit 1703, Int.ofNat (nat_lit 1))]
theorem atom0574Coded_decode : atom0574 = SparsePolynomial.decodeCubic 15 atom0574Coded := by decide +kernel
theorem atom0574Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (2284800 : Int) atom0574Coded) := by
  have h := atom0574_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0574Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0575 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0575 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0575 = ((g 7) * (g 8) * (g 10)) := by
  norm_num [atom0575, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0575_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (509120 : Int) atom0575) := by
  rw [SparsePolynomial.eval_scale, eval_atom0575]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0575Coded : CoefficientMerge.Poly := [(nat_lit 1705, Int.ofNat (nat_lit 1))]
theorem atom0575Coded_decode : atom0575 = SparsePolynomial.decodeCubic 15 atom0575Coded := by decide +kernel
theorem atom0575Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (509120 : Int) atom0575Coded) := by
  have h := atom0575_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0575Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0576 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0576 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0576 = ((g 7) * (g 8) * (g 11)) := by
  norm_num [atom0576, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0576_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11378240 : Int) atom0576) := by
  rw [SparsePolynomial.eval_scale, eval_atom0576]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0576Coded : CoefficientMerge.Poly := [(nat_lit 1706, Int.ofNat (nat_lit 1))]
theorem atom0576Coded_decode : atom0576 = SparsePolynomial.decodeCubic 15 atom0576Coded := by decide +kernel
theorem atom0576Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (11378240 : Int) atom0576Coded) := by
  have h := atom0576_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0576Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0577 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0577 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0577 = ((g 7) * (g 8) * (g 12)) := by
  norm_num [atom0577, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0577_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26440640 : Int) atom0577) := by
  rw [SparsePolynomial.eval_scale, eval_atom0577]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0577Coded : CoefficientMerge.Poly := [(nat_lit 1707, Int.ofNat (nat_lit 1))]
theorem atom0577Coded_decode : atom0577 = SparsePolynomial.decodeCubic 15 atom0577Coded := by decide +kernel
theorem atom0577Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (26440640 : Int) atom0577Coded) := by
  have h := atom0577_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0577Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0578 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0578 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0578 = ((g 7) * (g 8) * (g 13)) := by
  norm_num [atom0578, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0578_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33900480 : Int) atom0578) := by
  rw [SparsePolynomial.eval_scale, eval_atom0578]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0578Coded : CoefficientMerge.Poly := [(nat_lit 1708, Int.ofNat (nat_lit 1))]
theorem atom0578Coded_decode : atom0578 = SparsePolynomial.decodeCubic 15 atom0578Coded := by decide +kernel
theorem atom0578Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (33900480 : Int) atom0578Coded) := by
  have h := atom0578_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0578Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0579 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0579 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0579 = ((g 7) * (g 8) * (g 14)) := by
  norm_num [atom0579, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0579_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83671920 : Int) atom0579) := by
  rw [SparsePolynomial.eval_scale, eval_atom0579]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0579Coded : CoefficientMerge.Poly := [(nat_lit 1709, Int.ofNat (nat_lit 1))]
theorem atom0579Coded_decode : atom0579 = SparsePolynomial.decodeCubic 15 atom0579Coded := by decide +kernel
theorem atom0579Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (83671920 : Int) atom0579Coded) := by
  have h := atom0579_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0579Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0580 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0580 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0580 = ((g 7) * (g 9) * (g 9)) := by
  norm_num [atom0580, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0580_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14717760 : Int) atom0580) := by
  rw [SparsePolynomial.eval_scale, eval_atom0580]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0580Coded : CoefficientMerge.Poly := [(nat_lit 1719, Int.ofNat (nat_lit 1))]
theorem atom0580Coded_decode : atom0580 = SparsePolynomial.decodeCubic 15 atom0580Coded := by decide +kernel
theorem atom0580Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (14717760 : Int) atom0580Coded) := by
  have h := atom0580_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0580Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0581 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0581 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0581 = ((g 7) * (g 9) * (g 10)) := by
  norm_num [atom0581, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0581_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37833600 : Int) atom0581) := by
  rw [SparsePolynomial.eval_scale, eval_atom0581]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0581Coded : CoefficientMerge.Poly := [(nat_lit 1720, Int.ofNat (nat_lit 1))]
theorem atom0581Coded_decode : atom0581 = SparsePolynomial.decodeCubic 15 atom0581Coded := by decide +kernel
theorem atom0581Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (37833600 : Int) atom0581Coded) := by
  have h := atom0581_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0581Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0582 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0582 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0582 = ((g 7) * (g 9) * (g 11)) := by
  norm_num [atom0582, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0582_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108389280 : Int) atom0582) := by
  rw [SparsePolynomial.eval_scale, eval_atom0582]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0582Coded : CoefficientMerge.Poly := [(nat_lit 1721, Int.ofNat (nat_lit 1))]
theorem atom0582Coded_decode : atom0582 = SparsePolynomial.decodeCubic 15 atom0582Coded := by decide +kernel
theorem atom0582Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (108389280 : Int) atom0582Coded) := by
  have h := atom0582_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0582Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0583 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0583 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0583 = ((g 7) * (g 9) * (g 12)) := by
  norm_num [atom0583, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0583_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140625120 : Int) atom0583) := by
  rw [SparsePolynomial.eval_scale, eval_atom0583]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0583Coded : CoefficientMerge.Poly := [(nat_lit 1722, Int.ofNat (nat_lit 1))]
theorem atom0583Coded_decode : atom0583 = SparsePolynomial.decodeCubic 15 atom0583Coded := by decide +kernel
theorem atom0583Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (140625120 : Int) atom0583Coded) := by
  have h := atom0583_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0583Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0584 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0584 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0584 = ((g 7) * (g 9) * (g 13)) := by
  norm_num [atom0584, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0584_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (98938560 : Int) atom0584) := by
  rw [SparsePolynomial.eval_scale, eval_atom0584]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0584Coded : CoefficientMerge.Poly := [(nat_lit 1723, Int.ofNat (nat_lit 1))]
theorem atom0584Coded_decode : atom0584 = SparsePolynomial.decodeCubic 15 atom0584Coded := by decide +kernel
theorem atom0584Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (98938560 : Int) atom0584Coded) := by
  have h := atom0584_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0584Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0585 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0585 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0585 = ((g 7) * (g 9) * (g 14)) := by
  norm_num [atom0585, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0585_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193577040 : Int) atom0585) := by
  rw [SparsePolynomial.eval_scale, eval_atom0585]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0585Coded : CoefficientMerge.Poly := [(nat_lit 1724, Int.ofNat (nat_lit 1))]
theorem atom0585Coded_decode : atom0585 = SparsePolynomial.decodeCubic 15 atom0585Coded := by decide +kernel
theorem atom0585Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (193577040 : Int) atom0585Coded) := by
  have h := atom0585_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0585Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0586 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0586 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0586 = ((g 7) * (g 10) * (g 10)) := by
  norm_num [atom0586, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0586_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16205184 : Int) atom0586) := by
  rw [SparsePolynomial.eval_scale, eval_atom0586]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0586Coded : CoefficientMerge.Poly := [(nat_lit 1735, Int.ofNat (nat_lit 1))]
theorem atom0586Coded_decode : atom0586 = SparsePolynomial.decodeCubic 15 atom0586Coded := by decide +kernel
theorem atom0586Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (16205184 : Int) atom0586Coded) := by
  have h := atom0586_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0586Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0587 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0587 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0587 = ((g 7) * (g 10) * (g 11)) := by
  norm_num [atom0587, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0587_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87384840 : Int) atom0587) := by
  rw [SparsePolynomial.eval_scale, eval_atom0587]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0587Coded : CoefficientMerge.Poly := [(nat_lit 1736, Int.ofNat (nat_lit 1))]
theorem atom0587Coded_decode : atom0587 = SparsePolynomial.decodeCubic 15 atom0587Coded := by decide +kernel
theorem atom0587Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (87384840 : Int) atom0587Coded) := by
  have h := atom0587_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0587Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0588 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0588 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0588 = ((g 7) * (g 10) * (g 12)) := by
  norm_num [atom0588, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0588_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142194240 : Int) atom0588) := by
  rw [SparsePolynomial.eval_scale, eval_atom0588]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0588Coded : CoefficientMerge.Poly := [(nat_lit 1737, Int.ofNat (nat_lit 1))]
theorem atom0588Coded_decode : atom0588 = SparsePolynomial.decodeCubic 15 atom0588Coded := by decide +kernel
theorem atom0588Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (142194240 : Int) atom0588Coded) := by
  have h := atom0588_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0588Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0589 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0589 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0589 = ((g 7) * (g 10) * (g 13)) := by
  norm_num [atom0589, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0589_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (120840960 : Int) atom0589) := by
  rw [SparsePolynomial.eval_scale, eval_atom0589]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0589Coded : CoefficientMerge.Poly := [(nat_lit 1738, Int.ofNat (nat_lit 1))]
theorem atom0589Coded_decode : atom0589 = SparsePolynomial.decodeCubic 15 atom0589Coded := by decide +kernel
theorem atom0589Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (120840960 : Int) atom0589Coded) := by
  have h := atom0589_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0589Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0590 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0590 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0590 = ((g 7) * (g 10) * (g 14)) := by
  norm_num [atom0590, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0590_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (183474720 : Int) atom0590) := by
  rw [SparsePolynomial.eval_scale, eval_atom0590]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0590Coded : CoefficientMerge.Poly := [(nat_lit 1739, Int.ofNat (nat_lit 1))]
theorem atom0590Coded_decode : atom0590 = SparsePolynomial.decodeCubic 15 atom0590Coded := by decide +kernel
theorem atom0590Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (183474720 : Int) atom0590Coded) := by
  have h := atom0590_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0590Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0591 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0591 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0591 = ((g 7) * (g 11) * (g 11)) := by
  norm_num [atom0591, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0591_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82001160 : Int) atom0591) := by
  rw [SparsePolynomial.eval_scale, eval_atom0591]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0591Coded : CoefficientMerge.Poly := [(nat_lit 1751, Int.ofNat (nat_lit 1))]
theorem atom0591Coded_decode : atom0591 = SparsePolynomial.decodeCubic 15 atom0591Coded := by decide +kernel
theorem atom0591Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (82001160 : Int) atom0591Coded) := by
  have h := atom0591_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0591Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0592 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0592 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0592 = ((g 7) * (g 11) * (g 12)) := by
  norm_num [atom0592, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0592_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175846920 : Int) atom0592) := by
  rw [SparsePolynomial.eval_scale, eval_atom0592]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0592Coded : CoefficientMerge.Poly := [(nat_lit 1752, Int.ofNat (nat_lit 1))]
theorem atom0592Coded_decode : atom0592 = SparsePolynomial.decodeCubic 15 atom0592Coded := by decide +kernel
theorem atom0592Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (175846920 : Int) atom0592Coded) := by
  have h := atom0592_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0592Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0593 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0593 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0593 = ((g 7) * (g 11) * (g 13)) := by
  norm_num [atom0593, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0593_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (163720560 : Int) atom0593) := by
  rw [SparsePolynomial.eval_scale, eval_atom0593]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0593Coded : CoefficientMerge.Poly := [(nat_lit 1753, Int.ofNat (nat_lit 1))]
theorem atom0593Coded_decode : atom0593 = SparsePolynomial.decodeCubic 15 atom0593Coded := by decide +kernel
theorem atom0593Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (163720560 : Int) atom0593Coded) := by
  have h := atom0593_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0593Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0594 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0594 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0594 = ((g 7) * (g 11) * (g 14)) := by
  norm_num [atom0594, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0594_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (253214640 : Int) atom0594) := by
  rw [SparsePolynomial.eval_scale, eval_atom0594]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0594Coded : CoefficientMerge.Poly := [(nat_lit 1754, Int.ofNat (nat_lit 1))]
theorem atom0594Coded_decode : atom0594 = SparsePolynomial.decodeCubic 15 atom0594Coded := by decide +kernel
theorem atom0594Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (253214640 : Int) atom0594Coded) := by
  have h := atom0594_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0594Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0595 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0595 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0595 = ((g 7) * (g 12) * (g 12)) := by
  norm_num [atom0595, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0595_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77264640 : Int) atom0595) := by
  rw [SparsePolynomial.eval_scale, eval_atom0595]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0595Coded : CoefficientMerge.Poly := [(nat_lit 1767, Int.ofNat (nat_lit 1))]
theorem atom0595Coded_decode : atom0595 = SparsePolynomial.decodeCubic 15 atom0595Coded := by decide +kernel
theorem atom0595Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (77264640 : Int) atom0595Coded) := by
  have h := atom0595_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0595Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0596 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0596 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0596 = ((g 7) * (g 12) * (g 13)) := by
  norm_num [atom0596, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0596_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (164422560 : Int) atom0596) := by
  rw [SparsePolynomial.eval_scale, eval_atom0596]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0596Coded : CoefficientMerge.Poly := [(nat_lit 1768, Int.ofNat (nat_lit 1))]
theorem atom0596Coded_decode : atom0596 = SparsePolynomial.decodeCubic 15 atom0596Coded := by decide +kernel
theorem atom0596Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (164422560 : Int) atom0596Coded) := by
  have h := atom0596_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0596Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0597 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0597 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0597 = ((g 7) * (g 12) * (g 14)) := by
  norm_num [atom0597, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0597_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (270259200 : Int) atom0597) := by
  rw [SparsePolynomial.eval_scale, eval_atom0597]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0597Coded : CoefficientMerge.Poly := [(nat_lit 1769, Int.ofNat (nat_lit 1))]
theorem atom0597Coded_decode : atom0597 = SparsePolynomial.decodeCubic 15 atom0597Coded := by decide +kernel
theorem atom0597Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (270259200 : Int) atom0597Coded) := by
  have h := atom0597_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0597Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0598 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0598 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0598 = ((g 7) * (g 13) * (g 13)) := by
  norm_num [atom0598, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0598_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65834880 : Int) atom0598) := by
  rw [SparsePolynomial.eval_scale, eval_atom0598]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0598Coded : CoefficientMerge.Poly := [(nat_lit 1783, Int.ofNat (nat_lit 1))]
theorem atom0598Coded_decode : atom0598 = SparsePolynomial.decodeCubic 15 atom0598Coded := by decide +kernel
theorem atom0598Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (65834880 : Int) atom0598Coded) := by
  have h := atom0598_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0598Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0599 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0599 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0599 = ((g 7) * (g 13) * (g 14)) := by
  norm_num [atom0599, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0599_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (251478000 : Int) atom0599) := by
  rw [SparsePolynomial.eval_scale, eval_atom0599]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0599Coded : CoefficientMerge.Poly := [(nat_lit 1784, Int.ofNat (nat_lit 1))]
theorem atom0599Coded_decode : atom0599 = SparsePolynomial.decodeCubic 15 atom0599Coded := by decide +kernel
theorem atom0599Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (251478000 : Int) atom0599Coded) := by
  have h := atom0599_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0599Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0600 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0600 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0600 = ((g 7) * (g 14) * (g 14)) := by
  norm_num [atom0600, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0600_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (174182400 : Int) atom0600) := by
  rw [SparsePolynomial.eval_scale, eval_atom0600]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0600Coded : CoefficientMerge.Poly := [(nat_lit 1799, Int.ofNat (nat_lit 1))]
theorem atom0600Coded_decode : atom0600 = SparsePolynomial.decodeCubic 15 atom0600Coded := by decide +kernel
theorem atom0600Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (174182400 : Int) atom0600Coded) := by
  have h := atom0600_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0600Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0601 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0601 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0601 = ((g 8) * (g 8) * (g 11)) := by
  norm_num [atom0601, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0601_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3436560 : Int) atom0601) := by
  rw [SparsePolynomial.eval_scale, eval_atom0601]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0601Coded : CoefficientMerge.Poly := [(nat_lit 1931, Int.ofNat (nat_lit 1))]
theorem atom0601Coded_decode : atom0601 = SparsePolynomial.decodeCubic 15 atom0601Coded := by decide +kernel
theorem atom0601Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (3436560 : Int) atom0601Coded) := by
  have h := atom0601_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0601Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0602 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0602 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0602 = ((g 8) * (g 8) * (g 12)) := by
  norm_num [atom0602, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0602_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8981280 : Int) atom0602) := by
  rw [SparsePolynomial.eval_scale, eval_atom0602]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0602Coded : CoefficientMerge.Poly := [(nat_lit 1932, Int.ofNat (nat_lit 1))]
theorem atom0602Coded_decode : atom0602 = SparsePolynomial.decodeCubic 15 atom0602Coded := by decide +kernel
theorem atom0602Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (8981280 : Int) atom0602Coded) := by
  have h := atom0602_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0602Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0603 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0603 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0603 = ((g 8) * (g 8) * (g 14)) := by
  norm_num [atom0603, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0603_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30443040 : Int) atom0603) := by
  rw [SparsePolynomial.eval_scale, eval_atom0603]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0603Coded : CoefficientMerge.Poly := [(nat_lit 1934, Int.ofNat (nat_lit 1))]
theorem atom0603Coded_decode : atom0603 = SparsePolynomial.decodeCubic 15 atom0603Coded := by decide +kernel
theorem atom0603Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (30443040 : Int) atom0603Coded) := by
  have h := atom0603_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0603Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0604 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0604 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0604 = ((g 8) * (g 9) * (g 9)) := by
  norm_num [atom0604, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0604_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3985200 : Int) atom0604) := by
  rw [SparsePolynomial.eval_scale, eval_atom0604]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0604Coded : CoefficientMerge.Poly := [(nat_lit 1944, Int.ofNat (nat_lit 1))]
theorem atom0604Coded_decode : atom0604 = SparsePolynomial.decodeCubic 15 atom0604Coded := by decide +kernel
theorem atom0604Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (3985200 : Int) atom0604Coded) := by
  have h := atom0604_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0604Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0605 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0605 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0605 = ((g 8) * (g 9) * (g 10)) := by
  norm_num [atom0605, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0605_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14832720 : Int) atom0605) := by
  rw [SparsePolynomial.eval_scale, eval_atom0605]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0605Coded : CoefficientMerge.Poly := [(nat_lit 1945, Int.ofNat (nat_lit 1))]
theorem atom0605Coded_decode : atom0605 = SparsePolynomial.decodeCubic 15 atom0605Coded := by decide +kernel
theorem atom0605Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (14832720 : Int) atom0605Coded) := by
  have h := atom0605_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0605Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0606 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0606 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0606 = ((g 8) * (g 9) * (g 11)) := by
  norm_num [atom0606, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0606_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87102000 : Int) atom0606) := by
  rw [SparsePolynomial.eval_scale, eval_atom0606]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0606Coded : CoefficientMerge.Poly := [(nat_lit 1946, Int.ofNat (nat_lit 1))]
theorem atom0606Coded_decode : atom0606 = SparsePolynomial.decodeCubic 15 atom0606Coded := by decide +kernel
theorem atom0606Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (87102000 : Int) atom0606Coded) := by
  have h := atom0606_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0606Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0607 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0607 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0607 = ((g 8) * (g 9) * (g 12)) := by
  norm_num [atom0607, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0607_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121237560 : Int) atom0607) := by
  rw [SparsePolynomial.eval_scale, eval_atom0607]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0607Coded : CoefficientMerge.Poly := [(nat_lit 1947, Int.ofNat (nat_lit 1))]
theorem atom0607Coded_decode : atom0607 = SparsePolynomial.decodeCubic 15 atom0607Coded := by decide +kernel
theorem atom0607Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (121237560 : Int) atom0607Coded) := by
  have h := atom0607_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0607Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0608 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0608 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0608 = ((g 8) * (g 9) * (g 13)) := by
  norm_num [atom0608, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0608_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (75718800 : Int) atom0608) := by
  rw [SparsePolynomial.eval_scale, eval_atom0608]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0608Coded : CoefficientMerge.Poly := [(nat_lit 1948, Int.ofNat (nat_lit 1))]
theorem atom0608Coded_decode : atom0608 = SparsePolynomial.decodeCubic 15 atom0608Coded := by decide +kernel
theorem atom0608Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (75718800 : Int) atom0608Coded) := by
  have h := atom0608_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0608Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0609 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0609 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0609 = ((g 8) * (g 9) * (g 14)) := by
  norm_num [atom0609, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0609_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (187377300 : Int) atom0609) := by
  rw [SparsePolynomial.eval_scale, eval_atom0609]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0609Coded : CoefficientMerge.Poly := [(nat_lit 1949, Int.ofNat (nat_lit 1))]
theorem atom0609Coded_decode : atom0609 = SparsePolynomial.decodeCubic 15 atom0609Coded := by decide +kernel
theorem atom0609Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (187377300 : Int) atom0609Coded) := by
  have h := atom0609_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0609Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0610 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0610 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0610 = ((g 8) * (g 10) * (g 10)) := by
  norm_num [atom0610, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0610_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5940864 : Int) atom0610) := by
  rw [SparsePolynomial.eval_scale, eval_atom0610]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0610Coded : CoefficientMerge.Poly := [(nat_lit 1960, Int.ofNat (nat_lit 1))]
theorem atom0610Coded_decode : atom0610 = SparsePolynomial.decodeCubic 15 atom0610Coded := by decide +kernel
theorem atom0610Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (5940864 : Int) atom0610Coded) := by
  have h := atom0610_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0610Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0611 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0611 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0611 = ((g 8) * (g 10) * (g 11)) := by
  norm_num [atom0611, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0611_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74322360 : Int) atom0611) := by
  rw [SparsePolynomial.eval_scale, eval_atom0611]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0611Coded : CoefficientMerge.Poly := [(nat_lit 1961, Int.ofNat (nat_lit 1))]
theorem atom0611Coded_decode : atom0611 = SparsePolynomial.decodeCubic 15 atom0611Coded := by decide +kernel
theorem atom0611Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (74322360 : Int) atom0611Coded) := by
  have h := atom0611_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0611Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0612 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0612 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0612 = ((g 8) * (g 10) * (g 12)) := by
  norm_num [atom0612, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0612_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (136925640 : Int) atom0612) := by
  rw [SparsePolynomial.eval_scale, eval_atom0612]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0612Coded : CoefficientMerge.Poly := [(nat_lit 1962, Int.ofNat (nat_lit 1))]
theorem atom0612Coded_decode : atom0612 = SparsePolynomial.decodeCubic 15 atom0612Coded := by decide +kernel
theorem atom0612Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (136925640 : Int) atom0612Coded) := by
  have h := atom0612_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0612Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0613 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0613 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0613 = ((g 8) * (g 10) * (g 13)) := by
  norm_num [atom0613, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0613_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (123366240 : Int) atom0613) := by
  rw [SparsePolynomial.eval_scale, eval_atom0613]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0613Coded : CoefficientMerge.Poly := [(nat_lit 1963, Int.ofNat (nat_lit 1))]
theorem atom0613Coded_decode : atom0613 = SparsePolynomial.decodeCubic 15 atom0613Coded := by decide +kernel
theorem atom0613Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (123366240 : Int) atom0613Coded) := by
  have h := atom0613_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0613Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0614 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0614 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0614 = ((g 8) * (g 10) * (g 14)) := by
  norm_num [atom0614, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0614_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193957740 : Int) atom0614) := by
  rw [SparsePolynomial.eval_scale, eval_atom0614]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0614Coded : CoefficientMerge.Poly := [(nat_lit 1964, Int.ofNat (nat_lit 1))]
theorem atom0614Coded_decode : atom0614 = SparsePolynomial.decodeCubic 15 atom0614Coded := by decide +kernel
theorem atom0614Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (193957740 : Int) atom0614Coded) := by
  have h := atom0614_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0614Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0615 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0615 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0615 = ((g 8) * (g 11) * (g 11)) := by
  norm_num [atom0615, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0615_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77957640 : Int) atom0615) := by
  rw [SparsePolynomial.eval_scale, eval_atom0615]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0615Coded : CoefficientMerge.Poly := [(nat_lit 1976, Int.ofNat (nat_lit 1))]
theorem atom0615Coded_decode : atom0615 = SparsePolynomial.decodeCubic 15 atom0615Coded := by decide +kernel
theorem atom0615Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (77957640 : Int) atom0615Coded) := by
  have h := atom0615_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0615Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0616 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0616 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0616 = ((g 8) * (g 11) * (g 12)) := by
  norm_num [atom0616, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0616_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (179823240 : Int) atom0616) := by
  rw [SparsePolynomial.eval_scale, eval_atom0616]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0616Coded : CoefficientMerge.Poly := [(nat_lit 1977, Int.ofNat (nat_lit 1))]
theorem atom0616Coded_decode : atom0616 = SparsePolynomial.decodeCubic 15 atom0616Coded := by decide +kernel
theorem atom0616Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (179823240 : Int) atom0616Coded) := by
  have h := atom0616_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0616Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0617 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0617 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0617 = ((g 8) * (g 11) * (g 13)) := by
  norm_num [atom0617, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0617_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (185492160 : Int) atom0617) := by
  rw [SparsePolynomial.eval_scale, eval_atom0617]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0617Coded : CoefficientMerge.Poly := [(nat_lit 1978, Int.ofNat (nat_lit 1))]
theorem atom0617Coded_decode : atom0617 = SparsePolynomial.decodeCubic 15 atom0617Coded := by decide +kernel
theorem atom0617Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (185492160 : Int) atom0617Coded) := by
  have h := atom0617_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0617Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0618 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0618 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0618 = ((g 8) * (g 11) * (g 14)) := by
  norm_num [atom0618, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0618_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (273069360 : Int) atom0618) := by
  rw [SparsePolynomial.eval_scale, eval_atom0618]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0618Coded : CoefficientMerge.Poly := [(nat_lit 1979, Int.ofNat (nat_lit 1))]
theorem atom0618Coded_decode : atom0618 = SparsePolynomial.decodeCubic 15 atom0618Coded := by decide +kernel
theorem atom0618Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (273069360 : Int) atom0618Coded) := by
  have h := atom0618_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0618Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0619 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0619 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0619 = ((g 8) * (g 12) * (g 12)) := by
  norm_num [atom0619, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0619_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84758400 : Int) atom0619) := by
  rw [SparsePolynomial.eval_scale, eval_atom0619]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0619Coded : CoefficientMerge.Poly := [(nat_lit 1992, Int.ofNat (nat_lit 1))]
theorem atom0619Coded_decode : atom0619 = SparsePolynomial.decodeCubic 15 atom0619Coded := by decide +kernel
theorem atom0619Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (84758400 : Int) atom0619Coded) := by
  have h := atom0619_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0619Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0620 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0620 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0620 = ((g 8) * (g 12) * (g 13)) := by
  norm_num [atom0620, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0620_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (204013080 : Int) atom0620) := by
  rw [SparsePolynomial.eval_scale, eval_atom0620]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0620Coded : CoefficientMerge.Poly := [(nat_lit 1993, Int.ofNat (nat_lit 1))]
theorem atom0620Coded_decode : atom0620 = SparsePolynomial.decodeCubic 15 atom0620Coded := by decide +kernel
theorem atom0620Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (204013080 : Int) atom0620Coded) := by
  have h := atom0620_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0620Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0621 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0621 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0621 = ((g 8) * (g 12) * (g 14)) := by
  norm_num [atom0621, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0621_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (304197120 : Int) atom0621) := by
  rw [SparsePolynomial.eval_scale, eval_atom0621]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0621Coded : CoefficientMerge.Poly := [(nat_lit 1994, Int.ofNat (nat_lit 1))]
theorem atom0621Coded_decode : atom0621 = SparsePolynomial.decodeCubic 15 atom0621Coded := by decide +kernel
theorem atom0621Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (304197120 : Int) atom0621Coded) := by
  have h := atom0621_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0621Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0622 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0622 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0622 = ((g 8) * (g 13) * (g 13)) := by
  norm_num [atom0622, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0622_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (100271520 : Int) atom0622) := by
  rw [SparsePolynomial.eval_scale, eval_atom0622]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0622Coded : CoefficientMerge.Poly := [(nat_lit 2008, Int.ofNat (nat_lit 1))]
theorem atom0622Coded_decode : atom0622 = SparsePolynomial.decodeCubic 15 atom0622Coded := by decide +kernel
theorem atom0622Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (100271520 : Int) atom0622Coded) := by
  have h := atom0622_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0622Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0623 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0623 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0623 = ((g 8) * (g 13) * (g 14)) := by
  norm_num [atom0623, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0623_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (312395940 : Int) atom0623) := by
  rw [SparsePolynomial.eval_scale, eval_atom0623]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0623Coded : CoefficientMerge.Poly := [(nat_lit 2009, Int.ofNat (nat_lit 1))]
theorem atom0623Coded_decode : atom0623 = SparsePolynomial.decodeCubic 15 atom0623Coded := by decide +kernel
theorem atom0623Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (312395940 : Int) atom0623Coded) := by
  have h := atom0623_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0623Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0624 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0624 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0624 = ((g 8) * (g 14) * (g 14)) := by
  norm_num [atom0624, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0624_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (195955200 : Int) atom0624) := by
  rw [SparsePolynomial.eval_scale, eval_atom0624]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0624Coded : CoefficientMerge.Poly := [(nat_lit 2024, Int.ofNat (nat_lit 1))]
theorem atom0624Coded_decode : atom0624 = SparsePolynomial.decodeCubic 15 atom0624Coded := by decide +kernel
theorem atom0624Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (195955200 : Int) atom0624Coded) := by
  have h := atom0624_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0624Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0625 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0625 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0625 = ((g 9) * (g 9) * (g 9)) := by
  norm_num [atom0625, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0625_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3456000 : Int) atom0625) := by
  rw [SparsePolynomial.eval_scale, eval_atom0625]
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 9) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0625Coded : CoefficientMerge.Poly := [(nat_lit 2169, Int.ofNat (nat_lit 1))]
theorem atom0625Coded_decode : atom0625 = SparsePolynomial.decodeCubic 15 atom0625Coded := by decide +kernel
theorem atom0625Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (3456000 : Int) atom0625Coded) := by
  have h := atom0625_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0625Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0626 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0626 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0626 = ((g 9) * (g 9) * (g 10)) := by
  norm_num [atom0626, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0626_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17798400 : Int) atom0626) := by
  rw [SparsePolynomial.eval_scale, eval_atom0626]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0626Coded : CoefficientMerge.Poly := [(nat_lit 2170, Int.ofNat (nat_lit 1))]
theorem atom0626Coded_decode : atom0626 = SparsePolynomial.decodeCubic 15 atom0626Coded := by decide +kernel
theorem atom0626Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (17798400 : Int) atom0626Coded) := by
  have h := atom0626_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0626Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0627 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0627 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0627 = ((g 9) * (g 9) * (g 11)) := by
  norm_num [atom0627, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0627_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65173680 : Int) atom0627) := by
  rw [SparsePolynomial.eval_scale, eval_atom0627]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0627Coded : CoefficientMerge.Poly := [(nat_lit 2171, Int.ofNat (nat_lit 1))]
theorem atom0627Coded_decode : atom0627 = SparsePolynomial.decodeCubic 15 atom0627Coded := by decide +kernel
theorem atom0627Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (65173680 : Int) atom0627Coded) := by
  have h := atom0627_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0627Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0628 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0628 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0628 = ((g 9) * (g 9) * (g 12)) := by
  norm_num [atom0628, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0628_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87091200 : Int) atom0628) := by
  rw [SparsePolynomial.eval_scale, eval_atom0628]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 9) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0628Coded : CoefficientMerge.Poly := [(nat_lit 2172, Int.ofNat (nat_lit 1))]
theorem atom0628Coded_decode : atom0628 = SparsePolynomial.decodeCubic 15 atom0628Coded := by decide +kernel
theorem atom0628Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (87091200 : Int) atom0628Coded) := by
  have h := atom0628_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0628Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0629 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0629 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0629 = ((g 9) * (g 9) * (g 13)) := by
  norm_num [atom0629, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0629_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40089600 : Int) atom0629) := by
  rw [SparsePolynomial.eval_scale, eval_atom0629]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 9) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0629Coded : CoefficientMerge.Poly := [(nat_lit 2173, Int.ofNat (nat_lit 1))]
theorem atom0629Coded_decode : atom0629 = SparsePolynomial.decodeCubic 15 atom0629Coded := by decide +kernel
theorem atom0629Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (40089600 : Int) atom0629Coded) := by
  have h := atom0629_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0629Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0630 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0630 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0630 = ((g 9) * (g 9) * (g 14)) := by
  norm_num [atom0630, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0630_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101952000 : Int) atom0630) := by
  rw [SparsePolynomial.eval_scale, eval_atom0630]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 9) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0630Coded : CoefficientMerge.Poly := [(nat_lit 2174, Int.ofNat (nat_lit 1))]
theorem atom0630Coded_decode : atom0630 = SparsePolynomial.decodeCubic 15 atom0630Coded := by decide +kernel
theorem atom0630Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (101952000 : Int) atom0630Coded) := by
  have h := atom0630_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0630Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0631 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0631 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0631 = ((g 9) * (g 10) * (g 10)) := by
  norm_num [atom0631, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0631_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20808576 : Int) atom0631) := by
  rw [SparsePolynomial.eval_scale, eval_atom0631]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 9) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0631Coded : CoefficientMerge.Poly := [(nat_lit 2185, Int.ofNat (nat_lit 1))]
theorem atom0631Coded_decode : atom0631 = SparsePolynomial.decodeCubic 15 atom0631Coded := by decide +kernel
theorem atom0631Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (20808576 : Int) atom0631Coded) := by
  have h := atom0631_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0631Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0632 : SparsePolynomial.Poly := [([nat_lit 9, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0632 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0632 = ((g 9) * (g 10) * (g 11)) := by
  norm_num [atom0632, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0632_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126358920 : Int) atom0632) := by
  rw [SparsePolynomial.eval_scale, eval_atom0632]
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 9) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0632Coded : CoefficientMerge.Poly := [(nat_lit 2186, Int.ofNat (nat_lit 1))]
theorem atom0632Coded_decode : atom0632 = SparsePolynomial.decodeCubic 15 atom0632Coded := by decide +kernel
theorem atom0632Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (126358920 : Int) atom0632Coded) := by
  have h := atom0632_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0632Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block007 : CoefficientMerge.Poly := [(nat_lit 1495, Int.ofNat (nat_lit 60699240)), (nat_lit 1496, Int.ofNat (nat_lit 126096480)), (nat_lit 1497, Int.ofNat (nat_lit 156091320)), (nat_lit 1498, Int.ofNat (nat_lit 110217240)), (nat_lit 1499, Int.ofNat (nat_lit 200423160)), (nat_lit 1510, Int.ofNat (nat_lit 26469504)), (nat_lit 1511, Int.ofNat (nat_lit 100582560)), (nat_lit 1512, Int.ofNat (nat_lit 147665700)), (nat_lit 1513, Int.ofNat (nat_lit 118586160)), (nat_lit 1514, Int.ofNat (nat_lit 173295990)), (nat_lit 1526, Int.ofNat (nat_lit 86044680)), (nat_lit 1527, Int.ofNat (nat_lit 170421840)), (nat_lit 1528, Int.ofNat (nat_lit 146729880)), (nat_lit 1529, Int.ofNat (nat_lit 224658360)), (nat_lit 1542, Int.ofNat (nat_lit 67597740)), (nat_lit 1543, Int.ofNat (nat_lit 129105900)), (nat_lit 1544, Int.ofNat (nat_lit 220009230)), (nat_lit 1558, Int.ofNat (nat_lit 40960080)), (nat_lit 1559, Int.ofNat (nat_lit 183914010)), (nat_lit 1574, Int.ofNat (nat_lit 132831090)), (nat_lit 1687, Int.ofNat (nat_lit 13440)), (nat_lit 1703, Int.ofNat (nat_lit 2284800)), (nat_lit 1705, Int.ofNat (nat_lit 509120)), (nat_lit 1706, Int.ofNat (nat_lit 11378240)), (nat_lit 1707, Int.ofNat (nat_lit 26440640)), (nat_lit 1708, Int.ofNat (nat_lit 33900480)), (nat_lit 1709, Int.ofNat (nat_lit 83671920)), (nat_lit 1719, Int.ofNat (nat_lit 14717760)), (nat_lit 1720, Int.ofNat (nat_lit 37833600)), (nat_lit 1721, Int.ofNat (nat_lit 108389280)), (nat_lit 1722, Int.ofNat (nat_lit 140625120)), (nat_lit 1723, Int.ofNat (nat_lit 98938560)), (nat_lit 1724, Int.ofNat (nat_lit 193577040)), (nat_lit 1735, Int.ofNat (nat_lit 16205184)), (nat_lit 1736, Int.ofNat (nat_lit 87384840)), (nat_lit 1737, Int.ofNat (nat_lit 142194240)), (nat_lit 1738, Int.ofNat (nat_lit 120840960)), (nat_lit 1739, Int.ofNat (nat_lit 183474720)), (nat_lit 1751, Int.ofNat (nat_lit 82001160)), (nat_lit 1752, Int.ofNat (nat_lit 175846920)), (nat_lit 1753, Int.ofNat (nat_lit 163720560)), (nat_lit 1754, Int.ofNat (nat_lit 253214640)), (nat_lit 1767, Int.ofNat (nat_lit 77264640)), (nat_lit 1768, Int.ofNat (nat_lit 164422560)), (nat_lit 1769, Int.ofNat (nat_lit 270259200)), (nat_lit 1783, Int.ofNat (nat_lit 65834880)), (nat_lit 1784, Int.ofNat (nat_lit 251478000)), (nat_lit 1799, Int.ofNat (nat_lit 174182400)), (nat_lit 1931, Int.ofNat (nat_lit 3436560)), (nat_lit 1932, Int.ofNat (nat_lit 8981280)), (nat_lit 1934, Int.ofNat (nat_lit 30443040)), (nat_lit 1944, Int.ofNat (nat_lit 3985200)), (nat_lit 1945, Int.ofNat (nat_lit 14832720)), (nat_lit 1946, Int.ofNat (nat_lit 87102000)), (nat_lit 1947, Int.ofNat (nat_lit 121237560)), (nat_lit 1948, Int.ofNat (nat_lit 75718800)), (nat_lit 1949, Int.ofNat (nat_lit 187377300)), (nat_lit 1960, Int.ofNat (nat_lit 5940864)), (nat_lit 1961, Int.ofNat (nat_lit 74322360)), (nat_lit 1962, Int.ofNat (nat_lit 136925640)), (nat_lit 1963, Int.ofNat (nat_lit 123366240)), (nat_lit 1964, Int.ofNat (nat_lit 193957740)), (nat_lit 1976, Int.ofNat (nat_lit 77957640)), (nat_lit 1977, Int.ofNat (nat_lit 179823240)), (nat_lit 1978, Int.ofNat (nat_lit 185492160)), (nat_lit 1979, Int.ofNat (nat_lit 273069360)), (nat_lit 1992, Int.ofNat (nat_lit 84758400)), (nat_lit 1993, Int.ofNat (nat_lit 204013080)), (nat_lit 1994, Int.ofNat (nat_lit 304197120)), (nat_lit 2008, Int.ofNat (nat_lit 100271520)), (nat_lit 2009, Int.ofNat (nat_lit 312395940)), (nat_lit 2024, Int.ofNat (nat_lit 195955200)), (nat_lit 2169, Int.ofNat (nat_lit 3456000)), (nat_lit 2170, Int.ofNat (nat_lit 17798400)), (nat_lit 2171, Int.ofNat (nat_lit 65173680)), (nat_lit 2172, Int.ofNat (nat_lit 87091200)), (nat_lit 2173, Int.ofNat (nat_lit 40089600)), (nat_lit 2174, Int.ofNat (nat_lit 101952000)), (nat_lit 2185, Int.ofNat (nat_lit 20808576)), (nat_lit 2186, Int.ofNat (nat_lit 126358920))]
def block007_data_flat000 : CoefficientMerge.Poly := [(nat_lit 1495, Int.ofNat (nat_lit 60699240))]
theorem block007_data_flat000_step : block007_data_flat000 = (CoefficientMerge.scale (60699240 : Int) atom0553Coded) := by decide +kernel
theorem block007_data_flat000_original : block007_data_flat000 = (CoefficientMerge.scale (60699240 : Int) atom0553Coded) := by
  rw [block007_data_flat000_step]
def block007_data_flat001 : CoefficientMerge.Poly := [(nat_lit 1496, Int.ofNat (nat_lit 126096480))]
theorem block007_data_flat001_step : block007_data_flat001 = (CoefficientMerge.scale (126096480 : Int) atom0554Coded) := by decide +kernel
theorem block007_data_flat001_original : block007_data_flat001 = (CoefficientMerge.scale (126096480 : Int) atom0554Coded) := by
  rw [block007_data_flat001_step]
def block007_data_flat002 : CoefficientMerge.Poly := [(nat_lit 1495, Int.ofNat (nat_lit 60699240)), (nat_lit 1496, Int.ofNat (nat_lit 126096480))]
theorem block007_data_flat002_step : block007_data_flat002 = (CoefficientMerge.fastMerge block007_data_flat000 block007_data_flat001) := by decide +kernel
theorem block007_data_flat002_original : block007_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (60699240 : Int) atom0553Coded) (CoefficientMerge.scale (126096480 : Int) atom0554Coded)) := by
  rw [block007_data_flat002_step, block007_data_flat000_original, block007_data_flat001_original]
def block007_data_flat003 : CoefficientMerge.Poly := [(nat_lit 1497, Int.ofNat (nat_lit 156091320))]
theorem block007_data_flat003_step : block007_data_flat003 = (CoefficientMerge.scale (156091320 : Int) atom0555Coded) := by decide +kernel
theorem block007_data_flat003_original : block007_data_flat003 = (CoefficientMerge.scale (156091320 : Int) atom0555Coded) := by
  rw [block007_data_flat003_step]
def block007_data_flat004 : CoefficientMerge.Poly := [(nat_lit 1498, Int.ofNat (nat_lit 110217240))]
theorem block007_data_flat004_step : block007_data_flat004 = (CoefficientMerge.scale (110217240 : Int) atom0556Coded) := by decide +kernel
theorem block007_data_flat004_original : block007_data_flat004 = (CoefficientMerge.scale (110217240 : Int) atom0556Coded) := by
  rw [block007_data_flat004_step]
def block007_data_flat005 : CoefficientMerge.Poly := [(nat_lit 1499, Int.ofNat (nat_lit 200423160))]
theorem block007_data_flat005_step : block007_data_flat005 = (CoefficientMerge.scale (200423160 : Int) atom0557Coded) := by decide +kernel
theorem block007_data_flat005_original : block007_data_flat005 = (CoefficientMerge.scale (200423160 : Int) atom0557Coded) := by
  rw [block007_data_flat005_step]
def block007_data_flat006 : CoefficientMerge.Poly := [(nat_lit 1498, Int.ofNat (nat_lit 110217240)), (nat_lit 1499, Int.ofNat (nat_lit 200423160))]
theorem block007_data_flat006_step : block007_data_flat006 = (CoefficientMerge.fastMerge block007_data_flat004 block007_data_flat005) := by decide +kernel
theorem block007_data_flat006_original : block007_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (110217240 : Int) atom0556Coded) (CoefficientMerge.scale (200423160 : Int) atom0557Coded)) := by
  rw [block007_data_flat006_step, block007_data_flat004_original, block007_data_flat005_original]
def block007_data_flat007 : CoefficientMerge.Poly := [(nat_lit 1497, Int.ofNat (nat_lit 156091320)), (nat_lit 1498, Int.ofNat (nat_lit 110217240)), (nat_lit 1499, Int.ofNat (nat_lit 200423160))]
theorem block007_data_flat007_step : block007_data_flat007 = (CoefficientMerge.fastMerge block007_data_flat003 block007_data_flat006) := by decide +kernel
theorem block007_data_flat007_original : block007_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (156091320 : Int) atom0555Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110217240 : Int) atom0556Coded) (CoefficientMerge.scale (200423160 : Int) atom0557Coded))) := by
  rw [block007_data_flat007_step, block007_data_flat003_original, block007_data_flat006_original]
def block007_data_flat008 : CoefficientMerge.Poly := [(nat_lit 1495, Int.ofNat (nat_lit 60699240)), (nat_lit 1496, Int.ofNat (nat_lit 126096480)), (nat_lit 1497, Int.ofNat (nat_lit 156091320)), (nat_lit 1498, Int.ofNat (nat_lit 110217240)), (nat_lit 1499, Int.ofNat (nat_lit 200423160))]
theorem block007_data_flat008_step : block007_data_flat008 = (CoefficientMerge.fastMerge block007_data_flat002 block007_data_flat007) := by decide +kernel
theorem block007_data_flat008_original : block007_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60699240 : Int) atom0553Coded) (CoefficientMerge.scale (126096480 : Int) atom0554Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156091320 : Int) atom0555Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110217240 : Int) atom0556Coded) (CoefficientMerge.scale (200423160 : Int) atom0557Coded)))) := by
  rw [block007_data_flat008_step, block007_data_flat002_original, block007_data_flat007_original]
def block007_data_flat009 : CoefficientMerge.Poly := [(nat_lit 1510, Int.ofNat (nat_lit 26469504))]
theorem block007_data_flat009_step : block007_data_flat009 = (CoefficientMerge.scale (26469504 : Int) atom0558Coded) := by decide +kernel
theorem block007_data_flat009_original : block007_data_flat009 = (CoefficientMerge.scale (26469504 : Int) atom0558Coded) := by
  rw [block007_data_flat009_step]
def block007_data_flat010 : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 100582560))]
theorem block007_data_flat010_step : block007_data_flat010 = (CoefficientMerge.scale (100582560 : Int) atom0559Coded) := by decide +kernel
theorem block007_data_flat010_original : block007_data_flat010 = (CoefficientMerge.scale (100582560 : Int) atom0559Coded) := by
  rw [block007_data_flat010_step]
def block007_data_flat011 : CoefficientMerge.Poly := [(nat_lit 1510, Int.ofNat (nat_lit 26469504)), (nat_lit 1511, Int.ofNat (nat_lit 100582560))]
theorem block007_data_flat011_step : block007_data_flat011 = (CoefficientMerge.fastMerge block007_data_flat009 block007_data_flat010) := by decide +kernel
theorem block007_data_flat011_original : block007_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26469504 : Int) atom0558Coded) (CoefficientMerge.scale (100582560 : Int) atom0559Coded)) := by
  rw [block007_data_flat011_step, block007_data_flat009_original, block007_data_flat010_original]
def block007_data_flat012 : CoefficientMerge.Poly := [(nat_lit 1512, Int.ofNat (nat_lit 147665700))]
theorem block007_data_flat012_step : block007_data_flat012 = (CoefficientMerge.scale (147665700 : Int) atom0560Coded) := by decide +kernel
theorem block007_data_flat012_original : block007_data_flat012 = (CoefficientMerge.scale (147665700 : Int) atom0560Coded) := by
  rw [block007_data_flat012_step]
def block007_data_flat013 : CoefficientMerge.Poly := [(nat_lit 1513, Int.ofNat (nat_lit 118586160))]
theorem block007_data_flat013_step : block007_data_flat013 = (CoefficientMerge.scale (118586160 : Int) atom0561Coded) := by decide +kernel
theorem block007_data_flat013_original : block007_data_flat013 = (CoefficientMerge.scale (118586160 : Int) atom0561Coded) := by
  rw [block007_data_flat013_step]
def block007_data_flat014 : CoefficientMerge.Poly := [(nat_lit 1514, Int.ofNat (nat_lit 173295990))]
theorem block007_data_flat014_step : block007_data_flat014 = (CoefficientMerge.scale (173295990 : Int) atom0562Coded) := by decide +kernel
theorem block007_data_flat014_original : block007_data_flat014 = (CoefficientMerge.scale (173295990 : Int) atom0562Coded) := by
  rw [block007_data_flat014_step]
def block007_data_flat015 : CoefficientMerge.Poly := [(nat_lit 1513, Int.ofNat (nat_lit 118586160)), (nat_lit 1514, Int.ofNat (nat_lit 173295990))]
theorem block007_data_flat015_step : block007_data_flat015 = (CoefficientMerge.fastMerge block007_data_flat013 block007_data_flat014) := by decide +kernel
theorem block007_data_flat015_original : block007_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (118586160 : Int) atom0561Coded) (CoefficientMerge.scale (173295990 : Int) atom0562Coded)) := by
  rw [block007_data_flat015_step, block007_data_flat013_original, block007_data_flat014_original]
def block007_data_flat016 : CoefficientMerge.Poly := [(nat_lit 1512, Int.ofNat (nat_lit 147665700)), (nat_lit 1513, Int.ofNat (nat_lit 118586160)), (nat_lit 1514, Int.ofNat (nat_lit 173295990))]
theorem block007_data_flat016_step : block007_data_flat016 = (CoefficientMerge.fastMerge block007_data_flat012 block007_data_flat015) := by decide +kernel
theorem block007_data_flat016_original : block007_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (147665700 : Int) atom0560Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118586160 : Int) atom0561Coded) (CoefficientMerge.scale (173295990 : Int) atom0562Coded))) := by
  rw [block007_data_flat016_step, block007_data_flat012_original, block007_data_flat015_original]
def block007_data_flat017 : CoefficientMerge.Poly := [(nat_lit 1510, Int.ofNat (nat_lit 26469504)), (nat_lit 1511, Int.ofNat (nat_lit 100582560)), (nat_lit 1512, Int.ofNat (nat_lit 147665700)), (nat_lit 1513, Int.ofNat (nat_lit 118586160)), (nat_lit 1514, Int.ofNat (nat_lit 173295990))]
theorem block007_data_flat017_step : block007_data_flat017 = (CoefficientMerge.fastMerge block007_data_flat011 block007_data_flat016) := by decide +kernel
theorem block007_data_flat017_original : block007_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26469504 : Int) atom0558Coded) (CoefficientMerge.scale (100582560 : Int) atom0559Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (147665700 : Int) atom0560Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118586160 : Int) atom0561Coded) (CoefficientMerge.scale (173295990 : Int) atom0562Coded)))) := by
  rw [block007_data_flat017_step, block007_data_flat011_original, block007_data_flat016_original]
def block007_data_flat018 : CoefficientMerge.Poly := [(nat_lit 1495, Int.ofNat (nat_lit 60699240)), (nat_lit 1496, Int.ofNat (nat_lit 126096480)), (nat_lit 1497, Int.ofNat (nat_lit 156091320)), (nat_lit 1498, Int.ofNat (nat_lit 110217240)), (nat_lit 1499, Int.ofNat (nat_lit 200423160)), (nat_lit 1510, Int.ofNat (nat_lit 26469504)), (nat_lit 1511, Int.ofNat (nat_lit 100582560)), (nat_lit 1512, Int.ofNat (nat_lit 147665700)), (nat_lit 1513, Int.ofNat (nat_lit 118586160)), (nat_lit 1514, Int.ofNat (nat_lit 173295990))]
theorem block007_data_flat018_step : block007_data_flat018 = (CoefficientMerge.fastMerge block007_data_flat008 block007_data_flat017) := by decide +kernel
theorem block007_data_flat018_original : block007_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60699240 : Int) atom0553Coded) (CoefficientMerge.scale (126096480 : Int) atom0554Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156091320 : Int) atom0555Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110217240 : Int) atom0556Coded) (CoefficientMerge.scale (200423160 : Int) atom0557Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26469504 : Int) atom0558Coded) (CoefficientMerge.scale (100582560 : Int) atom0559Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (147665700 : Int) atom0560Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118586160 : Int) atom0561Coded) (CoefficientMerge.scale (173295990 : Int) atom0562Coded))))) := by
  rw [block007_data_flat018_step, block007_data_flat008_original, block007_data_flat017_original]
def block007_data_flat019 : CoefficientMerge.Poly := [(nat_lit 1526, Int.ofNat (nat_lit 86044680))]
theorem block007_data_flat019_step : block007_data_flat019 = (CoefficientMerge.scale (86044680 : Int) atom0563Coded) := by decide +kernel
theorem block007_data_flat019_original : block007_data_flat019 = (CoefficientMerge.scale (86044680 : Int) atom0563Coded) := by
  rw [block007_data_flat019_step]
def block007_data_flat020 : CoefficientMerge.Poly := [(nat_lit 1527, Int.ofNat (nat_lit 170421840))]
theorem block007_data_flat020_step : block007_data_flat020 = (CoefficientMerge.scale (170421840 : Int) atom0564Coded) := by decide +kernel
theorem block007_data_flat020_original : block007_data_flat020 = (CoefficientMerge.scale (170421840 : Int) atom0564Coded) := by
  rw [block007_data_flat020_step]
def block007_data_flat021 : CoefficientMerge.Poly := [(nat_lit 1526, Int.ofNat (nat_lit 86044680)), (nat_lit 1527, Int.ofNat (nat_lit 170421840))]
theorem block007_data_flat021_step : block007_data_flat021 = (CoefficientMerge.fastMerge block007_data_flat019 block007_data_flat020) := by decide +kernel
theorem block007_data_flat021_original : block007_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (86044680 : Int) atom0563Coded) (CoefficientMerge.scale (170421840 : Int) atom0564Coded)) := by
  rw [block007_data_flat021_step, block007_data_flat019_original, block007_data_flat020_original]
def block007_data_flat022 : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 146729880))]
theorem block007_data_flat022_step : block007_data_flat022 = (CoefficientMerge.scale (146729880 : Int) atom0565Coded) := by decide +kernel
theorem block007_data_flat022_original : block007_data_flat022 = (CoefficientMerge.scale (146729880 : Int) atom0565Coded) := by
  rw [block007_data_flat022_step]
def block007_data_flat023 : CoefficientMerge.Poly := [(nat_lit 1529, Int.ofNat (nat_lit 224658360))]
theorem block007_data_flat023_step : block007_data_flat023 = (CoefficientMerge.scale (224658360 : Int) atom0566Coded) := by decide +kernel
theorem block007_data_flat023_original : block007_data_flat023 = (CoefficientMerge.scale (224658360 : Int) atom0566Coded) := by
  rw [block007_data_flat023_step]
def block007_data_flat024 : CoefficientMerge.Poly := [(nat_lit 1542, Int.ofNat (nat_lit 67597740))]
theorem block007_data_flat024_step : block007_data_flat024 = (CoefficientMerge.scale (67597740 : Int) atom0567Coded) := by decide +kernel
theorem block007_data_flat024_original : block007_data_flat024 = (CoefficientMerge.scale (67597740 : Int) atom0567Coded) := by
  rw [block007_data_flat024_step]
def block007_data_flat025 : CoefficientMerge.Poly := [(nat_lit 1529, Int.ofNat (nat_lit 224658360)), (nat_lit 1542, Int.ofNat (nat_lit 67597740))]
theorem block007_data_flat025_step : block007_data_flat025 = (CoefficientMerge.fastMerge block007_data_flat023 block007_data_flat024) := by decide +kernel
theorem block007_data_flat025_original : block007_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (224658360 : Int) atom0566Coded) (CoefficientMerge.scale (67597740 : Int) atom0567Coded)) := by
  rw [block007_data_flat025_step, block007_data_flat023_original, block007_data_flat024_original]
def block007_data_flat026 : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 146729880)), (nat_lit 1529, Int.ofNat (nat_lit 224658360)), (nat_lit 1542, Int.ofNat (nat_lit 67597740))]
theorem block007_data_flat026_step : block007_data_flat026 = (CoefficientMerge.fastMerge block007_data_flat022 block007_data_flat025) := by decide +kernel
theorem block007_data_flat026_original : block007_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (146729880 : Int) atom0565Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (224658360 : Int) atom0566Coded) (CoefficientMerge.scale (67597740 : Int) atom0567Coded))) := by
  rw [block007_data_flat026_step, block007_data_flat022_original, block007_data_flat025_original]
def block007_data_flat027 : CoefficientMerge.Poly := [(nat_lit 1526, Int.ofNat (nat_lit 86044680)), (nat_lit 1527, Int.ofNat (nat_lit 170421840)), (nat_lit 1528, Int.ofNat (nat_lit 146729880)), (nat_lit 1529, Int.ofNat (nat_lit 224658360)), (nat_lit 1542, Int.ofNat (nat_lit 67597740))]
theorem block007_data_flat027_step : block007_data_flat027 = (CoefficientMerge.fastMerge block007_data_flat021 block007_data_flat026) := by decide +kernel
theorem block007_data_flat027_original : block007_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (86044680 : Int) atom0563Coded) (CoefficientMerge.scale (170421840 : Int) atom0564Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (146729880 : Int) atom0565Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (224658360 : Int) atom0566Coded) (CoefficientMerge.scale (67597740 : Int) atom0567Coded)))) := by
  rw [block007_data_flat027_step, block007_data_flat021_original, block007_data_flat026_original]
def block007_data_flat028 : CoefficientMerge.Poly := [(nat_lit 1543, Int.ofNat (nat_lit 129105900))]
theorem block007_data_flat028_step : block007_data_flat028 = (CoefficientMerge.scale (129105900 : Int) atom0568Coded) := by decide +kernel
theorem block007_data_flat028_original : block007_data_flat028 = (CoefficientMerge.scale (129105900 : Int) atom0568Coded) := by
  rw [block007_data_flat028_step]
def block007_data_flat029 : CoefficientMerge.Poly := [(nat_lit 1544, Int.ofNat (nat_lit 220009230))]
theorem block007_data_flat029_step : block007_data_flat029 = (CoefficientMerge.scale (220009230 : Int) atom0569Coded) := by decide +kernel
theorem block007_data_flat029_original : block007_data_flat029 = (CoefficientMerge.scale (220009230 : Int) atom0569Coded) := by
  rw [block007_data_flat029_step]
def block007_data_flat030 : CoefficientMerge.Poly := [(nat_lit 1543, Int.ofNat (nat_lit 129105900)), (nat_lit 1544, Int.ofNat (nat_lit 220009230))]
theorem block007_data_flat030_step : block007_data_flat030 = (CoefficientMerge.fastMerge block007_data_flat028 block007_data_flat029) := by decide +kernel
theorem block007_data_flat030_original : block007_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (129105900 : Int) atom0568Coded) (CoefficientMerge.scale (220009230 : Int) atom0569Coded)) := by
  rw [block007_data_flat030_step, block007_data_flat028_original, block007_data_flat029_original]
def block007_data_flat031 : CoefficientMerge.Poly := [(nat_lit 1558, Int.ofNat (nat_lit 40960080))]
theorem block007_data_flat031_step : block007_data_flat031 = (CoefficientMerge.scale (40960080 : Int) atom0570Coded) := by decide +kernel
theorem block007_data_flat031_original : block007_data_flat031 = (CoefficientMerge.scale (40960080 : Int) atom0570Coded) := by
  rw [block007_data_flat031_step]
def block007_data_flat032 : CoefficientMerge.Poly := [(nat_lit 1559, Int.ofNat (nat_lit 183914010))]
theorem block007_data_flat032_step : block007_data_flat032 = (CoefficientMerge.scale (183914010 : Int) atom0571Coded) := by decide +kernel
theorem block007_data_flat032_original : block007_data_flat032 = (CoefficientMerge.scale (183914010 : Int) atom0571Coded) := by
  rw [block007_data_flat032_step]
def block007_data_flat033 : CoefficientMerge.Poly := [(nat_lit 1574, Int.ofNat (nat_lit 132831090))]
theorem block007_data_flat033_step : block007_data_flat033 = (CoefficientMerge.scale (132831090 : Int) atom0572Coded) := by decide +kernel
theorem block007_data_flat033_original : block007_data_flat033 = (CoefficientMerge.scale (132831090 : Int) atom0572Coded) := by
  rw [block007_data_flat033_step]
def block007_data_flat034 : CoefficientMerge.Poly := [(nat_lit 1559, Int.ofNat (nat_lit 183914010)), (nat_lit 1574, Int.ofNat (nat_lit 132831090))]
theorem block007_data_flat034_step : block007_data_flat034 = (CoefficientMerge.fastMerge block007_data_flat032 block007_data_flat033) := by decide +kernel
theorem block007_data_flat034_original : block007_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (183914010 : Int) atom0571Coded) (CoefficientMerge.scale (132831090 : Int) atom0572Coded)) := by
  rw [block007_data_flat034_step, block007_data_flat032_original, block007_data_flat033_original]
def block007_data_flat035 : CoefficientMerge.Poly := [(nat_lit 1558, Int.ofNat (nat_lit 40960080)), (nat_lit 1559, Int.ofNat (nat_lit 183914010)), (nat_lit 1574, Int.ofNat (nat_lit 132831090))]
theorem block007_data_flat035_step : block007_data_flat035 = (CoefficientMerge.fastMerge block007_data_flat031 block007_data_flat034) := by decide +kernel
theorem block007_data_flat035_original : block007_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40960080 : Int) atom0570Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183914010 : Int) atom0571Coded) (CoefficientMerge.scale (132831090 : Int) atom0572Coded))) := by
  rw [block007_data_flat035_step, block007_data_flat031_original, block007_data_flat034_original]
def block007_data_flat036 : CoefficientMerge.Poly := [(nat_lit 1543, Int.ofNat (nat_lit 129105900)), (nat_lit 1544, Int.ofNat (nat_lit 220009230)), (nat_lit 1558, Int.ofNat (nat_lit 40960080)), (nat_lit 1559, Int.ofNat (nat_lit 183914010)), (nat_lit 1574, Int.ofNat (nat_lit 132831090))]
theorem block007_data_flat036_step : block007_data_flat036 = (CoefficientMerge.fastMerge block007_data_flat030 block007_data_flat035) := by decide +kernel
theorem block007_data_flat036_original : block007_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129105900 : Int) atom0568Coded) (CoefficientMerge.scale (220009230 : Int) atom0569Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40960080 : Int) atom0570Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183914010 : Int) atom0571Coded) (CoefficientMerge.scale (132831090 : Int) atom0572Coded)))) := by
  rw [block007_data_flat036_step, block007_data_flat030_original, block007_data_flat035_original]
def block007_data_flat037 : CoefficientMerge.Poly := [(nat_lit 1526, Int.ofNat (nat_lit 86044680)), (nat_lit 1527, Int.ofNat (nat_lit 170421840)), (nat_lit 1528, Int.ofNat (nat_lit 146729880)), (nat_lit 1529, Int.ofNat (nat_lit 224658360)), (nat_lit 1542, Int.ofNat (nat_lit 67597740)), (nat_lit 1543, Int.ofNat (nat_lit 129105900)), (nat_lit 1544, Int.ofNat (nat_lit 220009230)), (nat_lit 1558, Int.ofNat (nat_lit 40960080)), (nat_lit 1559, Int.ofNat (nat_lit 183914010)), (nat_lit 1574, Int.ofNat (nat_lit 132831090))]
theorem block007_data_flat037_step : block007_data_flat037 = (CoefficientMerge.fastMerge block007_data_flat027 block007_data_flat036) := by decide +kernel
theorem block007_data_flat037_original : block007_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (86044680 : Int) atom0563Coded) (CoefficientMerge.scale (170421840 : Int) atom0564Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (146729880 : Int) atom0565Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (224658360 : Int) atom0566Coded) (CoefficientMerge.scale (67597740 : Int) atom0567Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129105900 : Int) atom0568Coded) (CoefficientMerge.scale (220009230 : Int) atom0569Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40960080 : Int) atom0570Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183914010 : Int) atom0571Coded) (CoefficientMerge.scale (132831090 : Int) atom0572Coded))))) := by
  rw [block007_data_flat037_step, block007_data_flat027_original, block007_data_flat036_original]
def block007_data_flat038 : CoefficientMerge.Poly := [(nat_lit 1495, Int.ofNat (nat_lit 60699240)), (nat_lit 1496, Int.ofNat (nat_lit 126096480)), (nat_lit 1497, Int.ofNat (nat_lit 156091320)), (nat_lit 1498, Int.ofNat (nat_lit 110217240)), (nat_lit 1499, Int.ofNat (nat_lit 200423160)), (nat_lit 1510, Int.ofNat (nat_lit 26469504)), (nat_lit 1511, Int.ofNat (nat_lit 100582560)), (nat_lit 1512, Int.ofNat (nat_lit 147665700)), (nat_lit 1513, Int.ofNat (nat_lit 118586160)), (nat_lit 1514, Int.ofNat (nat_lit 173295990)), (nat_lit 1526, Int.ofNat (nat_lit 86044680)), (nat_lit 1527, Int.ofNat (nat_lit 170421840)), (nat_lit 1528, Int.ofNat (nat_lit 146729880)), (nat_lit 1529, Int.ofNat (nat_lit 224658360)), (nat_lit 1542, Int.ofNat (nat_lit 67597740)), (nat_lit 1543, Int.ofNat (nat_lit 129105900)), (nat_lit 1544, Int.ofNat (nat_lit 220009230)), (nat_lit 1558, Int.ofNat (nat_lit 40960080)), (nat_lit 1559, Int.ofNat (nat_lit 183914010)), (nat_lit 1574, Int.ofNat (nat_lit 132831090))]
theorem block007_data_flat038_step : block007_data_flat038 = (CoefficientMerge.fastMerge block007_data_flat018 block007_data_flat037) := by decide +kernel
theorem block007_data_flat038_original : block007_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60699240 : Int) atom0553Coded) (CoefficientMerge.scale (126096480 : Int) atom0554Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156091320 : Int) atom0555Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110217240 : Int) atom0556Coded) (CoefficientMerge.scale (200423160 : Int) atom0557Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26469504 : Int) atom0558Coded) (CoefficientMerge.scale (100582560 : Int) atom0559Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (147665700 : Int) atom0560Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118586160 : Int) atom0561Coded) (CoefficientMerge.scale (173295990 : Int) atom0562Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (86044680 : Int) atom0563Coded) (CoefficientMerge.scale (170421840 : Int) atom0564Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (146729880 : Int) atom0565Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (224658360 : Int) atom0566Coded) (CoefficientMerge.scale (67597740 : Int) atom0567Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129105900 : Int) atom0568Coded) (CoefficientMerge.scale (220009230 : Int) atom0569Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40960080 : Int) atom0570Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183914010 : Int) atom0571Coded) (CoefficientMerge.scale (132831090 : Int) atom0572Coded)))))) := by
  rw [block007_data_flat038_step, block007_data_flat018_original, block007_data_flat037_original]
def block007_data_flat039 : CoefficientMerge.Poly := [(nat_lit 1687, Int.ofNat (nat_lit 13440))]
theorem block007_data_flat039_step : block007_data_flat039 = (CoefficientMerge.scale (13440 : Int) atom0573Coded) := by decide +kernel
theorem block007_data_flat039_original : block007_data_flat039 = (CoefficientMerge.scale (13440 : Int) atom0573Coded) := by
  rw [block007_data_flat039_step]
def block007_data_flat040 : CoefficientMerge.Poly := [(nat_lit 1703, Int.ofNat (nat_lit 2284800))]
theorem block007_data_flat040_step : block007_data_flat040 = (CoefficientMerge.scale (2284800 : Int) atom0574Coded) := by decide +kernel
theorem block007_data_flat040_original : block007_data_flat040 = (CoefficientMerge.scale (2284800 : Int) atom0574Coded) := by
  rw [block007_data_flat040_step]
def block007_data_flat041 : CoefficientMerge.Poly := [(nat_lit 1687, Int.ofNat (nat_lit 13440)), (nat_lit 1703, Int.ofNat (nat_lit 2284800))]
theorem block007_data_flat041_step : block007_data_flat041 = (CoefficientMerge.fastMerge block007_data_flat039 block007_data_flat040) := by decide +kernel
theorem block007_data_flat041_original : block007_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13440 : Int) atom0573Coded) (CoefficientMerge.scale (2284800 : Int) atom0574Coded)) := by
  rw [block007_data_flat041_step, block007_data_flat039_original, block007_data_flat040_original]
def block007_data_flat042 : CoefficientMerge.Poly := [(nat_lit 1705, Int.ofNat (nat_lit 509120))]
theorem block007_data_flat042_step : block007_data_flat042 = (CoefficientMerge.scale (509120 : Int) atom0575Coded) := by decide +kernel
theorem block007_data_flat042_original : block007_data_flat042 = (CoefficientMerge.scale (509120 : Int) atom0575Coded) := by
  rw [block007_data_flat042_step]
def block007_data_flat043 : CoefficientMerge.Poly := [(nat_lit 1706, Int.ofNat (nat_lit 11378240))]
theorem block007_data_flat043_step : block007_data_flat043 = (CoefficientMerge.scale (11378240 : Int) atom0576Coded) := by decide +kernel
theorem block007_data_flat043_original : block007_data_flat043 = (CoefficientMerge.scale (11378240 : Int) atom0576Coded) := by
  rw [block007_data_flat043_step]
def block007_data_flat044 : CoefficientMerge.Poly := [(nat_lit 1707, Int.ofNat (nat_lit 26440640))]
theorem block007_data_flat044_step : block007_data_flat044 = (CoefficientMerge.scale (26440640 : Int) atom0577Coded) := by decide +kernel
theorem block007_data_flat044_original : block007_data_flat044 = (CoefficientMerge.scale (26440640 : Int) atom0577Coded) := by
  rw [block007_data_flat044_step]
def block007_data_flat045 : CoefficientMerge.Poly := [(nat_lit 1706, Int.ofNat (nat_lit 11378240)), (nat_lit 1707, Int.ofNat (nat_lit 26440640))]
theorem block007_data_flat045_step : block007_data_flat045 = (CoefficientMerge.fastMerge block007_data_flat043 block007_data_flat044) := by decide +kernel
theorem block007_data_flat045_original : block007_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11378240 : Int) atom0576Coded) (CoefficientMerge.scale (26440640 : Int) atom0577Coded)) := by
  rw [block007_data_flat045_step, block007_data_flat043_original, block007_data_flat044_original]
def block007_data_flat046 : CoefficientMerge.Poly := [(nat_lit 1705, Int.ofNat (nat_lit 509120)), (nat_lit 1706, Int.ofNat (nat_lit 11378240)), (nat_lit 1707, Int.ofNat (nat_lit 26440640))]
theorem block007_data_flat046_step : block007_data_flat046 = (CoefficientMerge.fastMerge block007_data_flat042 block007_data_flat045) := by decide +kernel
theorem block007_data_flat046_original : block007_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (509120 : Int) atom0575Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11378240 : Int) atom0576Coded) (CoefficientMerge.scale (26440640 : Int) atom0577Coded))) := by
  rw [block007_data_flat046_step, block007_data_flat042_original, block007_data_flat045_original]
def block007_data_flat047 : CoefficientMerge.Poly := [(nat_lit 1687, Int.ofNat (nat_lit 13440)), (nat_lit 1703, Int.ofNat (nat_lit 2284800)), (nat_lit 1705, Int.ofNat (nat_lit 509120)), (nat_lit 1706, Int.ofNat (nat_lit 11378240)), (nat_lit 1707, Int.ofNat (nat_lit 26440640))]
theorem block007_data_flat047_step : block007_data_flat047 = (CoefficientMerge.fastMerge block007_data_flat041 block007_data_flat046) := by decide +kernel
theorem block007_data_flat047_original : block007_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13440 : Int) atom0573Coded) (CoefficientMerge.scale (2284800 : Int) atom0574Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (509120 : Int) atom0575Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11378240 : Int) atom0576Coded) (CoefficientMerge.scale (26440640 : Int) atom0577Coded)))) := by
  rw [block007_data_flat047_step, block007_data_flat041_original, block007_data_flat046_original]
def block007_data_flat048 : CoefficientMerge.Poly := [(nat_lit 1708, Int.ofNat (nat_lit 33900480))]
theorem block007_data_flat048_step : block007_data_flat048 = (CoefficientMerge.scale (33900480 : Int) atom0578Coded) := by decide +kernel
theorem block007_data_flat048_original : block007_data_flat048 = (CoefficientMerge.scale (33900480 : Int) atom0578Coded) := by
  rw [block007_data_flat048_step]
def block007_data_flat049 : CoefficientMerge.Poly := [(nat_lit 1709, Int.ofNat (nat_lit 83671920))]
theorem block007_data_flat049_step : block007_data_flat049 = (CoefficientMerge.scale (83671920 : Int) atom0579Coded) := by decide +kernel
theorem block007_data_flat049_original : block007_data_flat049 = (CoefficientMerge.scale (83671920 : Int) atom0579Coded) := by
  rw [block007_data_flat049_step]
def block007_data_flat050 : CoefficientMerge.Poly := [(nat_lit 1708, Int.ofNat (nat_lit 33900480)), (nat_lit 1709, Int.ofNat (nat_lit 83671920))]
theorem block007_data_flat050_step : block007_data_flat050 = (CoefficientMerge.fastMerge block007_data_flat048 block007_data_flat049) := by decide +kernel
theorem block007_data_flat050_original : block007_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (33900480 : Int) atom0578Coded) (CoefficientMerge.scale (83671920 : Int) atom0579Coded)) := by
  rw [block007_data_flat050_step, block007_data_flat048_original, block007_data_flat049_original]
def block007_data_flat051 : CoefficientMerge.Poly := [(nat_lit 1719, Int.ofNat (nat_lit 14717760))]
theorem block007_data_flat051_step : block007_data_flat051 = (CoefficientMerge.scale (14717760 : Int) atom0580Coded) := by decide +kernel
theorem block007_data_flat051_original : block007_data_flat051 = (CoefficientMerge.scale (14717760 : Int) atom0580Coded) := by
  rw [block007_data_flat051_step]
def block007_data_flat052 : CoefficientMerge.Poly := [(nat_lit 1720, Int.ofNat (nat_lit 37833600))]
theorem block007_data_flat052_step : block007_data_flat052 = (CoefficientMerge.scale (37833600 : Int) atom0581Coded) := by decide +kernel
theorem block007_data_flat052_original : block007_data_flat052 = (CoefficientMerge.scale (37833600 : Int) atom0581Coded) := by
  rw [block007_data_flat052_step]
def block007_data_flat053 : CoefficientMerge.Poly := [(nat_lit 1721, Int.ofNat (nat_lit 108389280))]
theorem block007_data_flat053_step : block007_data_flat053 = (CoefficientMerge.scale (108389280 : Int) atom0582Coded) := by decide +kernel
theorem block007_data_flat053_original : block007_data_flat053 = (CoefficientMerge.scale (108389280 : Int) atom0582Coded) := by
  rw [block007_data_flat053_step]
def block007_data_flat054 : CoefficientMerge.Poly := [(nat_lit 1720, Int.ofNat (nat_lit 37833600)), (nat_lit 1721, Int.ofNat (nat_lit 108389280))]
theorem block007_data_flat054_step : block007_data_flat054 = (CoefficientMerge.fastMerge block007_data_flat052 block007_data_flat053) := by decide +kernel
theorem block007_data_flat054_original : block007_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (37833600 : Int) atom0581Coded) (CoefficientMerge.scale (108389280 : Int) atom0582Coded)) := by
  rw [block007_data_flat054_step, block007_data_flat052_original, block007_data_flat053_original]
def block007_data_flat055 : CoefficientMerge.Poly := [(nat_lit 1719, Int.ofNat (nat_lit 14717760)), (nat_lit 1720, Int.ofNat (nat_lit 37833600)), (nat_lit 1721, Int.ofNat (nat_lit 108389280))]
theorem block007_data_flat055_step : block007_data_flat055 = (CoefficientMerge.fastMerge block007_data_flat051 block007_data_flat054) := by decide +kernel
theorem block007_data_flat055_original : block007_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14717760 : Int) atom0580Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37833600 : Int) atom0581Coded) (CoefficientMerge.scale (108389280 : Int) atom0582Coded))) := by
  rw [block007_data_flat055_step, block007_data_flat051_original, block007_data_flat054_original]
def block007_data_flat056 : CoefficientMerge.Poly := [(nat_lit 1708, Int.ofNat (nat_lit 33900480)), (nat_lit 1709, Int.ofNat (nat_lit 83671920)), (nat_lit 1719, Int.ofNat (nat_lit 14717760)), (nat_lit 1720, Int.ofNat (nat_lit 37833600)), (nat_lit 1721, Int.ofNat (nat_lit 108389280))]
theorem block007_data_flat056_step : block007_data_flat056 = (CoefficientMerge.fastMerge block007_data_flat050 block007_data_flat055) := by decide +kernel
theorem block007_data_flat056_original : block007_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33900480 : Int) atom0578Coded) (CoefficientMerge.scale (83671920 : Int) atom0579Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14717760 : Int) atom0580Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37833600 : Int) atom0581Coded) (CoefficientMerge.scale (108389280 : Int) atom0582Coded)))) := by
  rw [block007_data_flat056_step, block007_data_flat050_original, block007_data_flat055_original]
def block007_data_flat057 : CoefficientMerge.Poly := [(nat_lit 1687, Int.ofNat (nat_lit 13440)), (nat_lit 1703, Int.ofNat (nat_lit 2284800)), (nat_lit 1705, Int.ofNat (nat_lit 509120)), (nat_lit 1706, Int.ofNat (nat_lit 11378240)), (nat_lit 1707, Int.ofNat (nat_lit 26440640)), (nat_lit 1708, Int.ofNat (nat_lit 33900480)), (nat_lit 1709, Int.ofNat (nat_lit 83671920)), (nat_lit 1719, Int.ofNat (nat_lit 14717760)), (nat_lit 1720, Int.ofNat (nat_lit 37833600)), (nat_lit 1721, Int.ofNat (nat_lit 108389280))]
theorem block007_data_flat057_step : block007_data_flat057 = (CoefficientMerge.fastMerge block007_data_flat047 block007_data_flat056) := by decide +kernel
theorem block007_data_flat057_original : block007_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13440 : Int) atom0573Coded) (CoefficientMerge.scale (2284800 : Int) atom0574Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (509120 : Int) atom0575Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11378240 : Int) atom0576Coded) (CoefficientMerge.scale (26440640 : Int) atom0577Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33900480 : Int) atom0578Coded) (CoefficientMerge.scale (83671920 : Int) atom0579Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14717760 : Int) atom0580Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37833600 : Int) atom0581Coded) (CoefficientMerge.scale (108389280 : Int) atom0582Coded))))) := by
  rw [block007_data_flat057_step, block007_data_flat047_original, block007_data_flat056_original]
def block007_data_flat058 : CoefficientMerge.Poly := [(nat_lit 1722, Int.ofNat (nat_lit 140625120))]
theorem block007_data_flat058_step : block007_data_flat058 = (CoefficientMerge.scale (140625120 : Int) atom0583Coded) := by decide +kernel
theorem block007_data_flat058_original : block007_data_flat058 = (CoefficientMerge.scale (140625120 : Int) atom0583Coded) := by
  rw [block007_data_flat058_step]
def block007_data_flat059 : CoefficientMerge.Poly := [(nat_lit 1723, Int.ofNat (nat_lit 98938560))]
theorem block007_data_flat059_step : block007_data_flat059 = (CoefficientMerge.scale (98938560 : Int) atom0584Coded) := by decide +kernel
theorem block007_data_flat059_original : block007_data_flat059 = (CoefficientMerge.scale (98938560 : Int) atom0584Coded) := by
  rw [block007_data_flat059_step]
def block007_data_flat060 : CoefficientMerge.Poly := [(nat_lit 1722, Int.ofNat (nat_lit 140625120)), (nat_lit 1723, Int.ofNat (nat_lit 98938560))]
theorem block007_data_flat060_step : block007_data_flat060 = (CoefficientMerge.fastMerge block007_data_flat058 block007_data_flat059) := by decide +kernel
theorem block007_data_flat060_original : block007_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (140625120 : Int) atom0583Coded) (CoefficientMerge.scale (98938560 : Int) atom0584Coded)) := by
  rw [block007_data_flat060_step, block007_data_flat058_original, block007_data_flat059_original]
def block007_data_flat061 : CoefficientMerge.Poly := [(nat_lit 1724, Int.ofNat (nat_lit 193577040))]
theorem block007_data_flat061_step : block007_data_flat061 = (CoefficientMerge.scale (193577040 : Int) atom0585Coded) := by decide +kernel
theorem block007_data_flat061_original : block007_data_flat061 = (CoefficientMerge.scale (193577040 : Int) atom0585Coded) := by
  rw [block007_data_flat061_step]
def block007_data_flat062 : CoefficientMerge.Poly := [(nat_lit 1735, Int.ofNat (nat_lit 16205184))]
theorem block007_data_flat062_step : block007_data_flat062 = (CoefficientMerge.scale (16205184 : Int) atom0586Coded) := by decide +kernel
theorem block007_data_flat062_original : block007_data_flat062 = (CoefficientMerge.scale (16205184 : Int) atom0586Coded) := by
  rw [block007_data_flat062_step]
def block007_data_flat063 : CoefficientMerge.Poly := [(nat_lit 1736, Int.ofNat (nat_lit 87384840))]
theorem block007_data_flat063_step : block007_data_flat063 = (CoefficientMerge.scale (87384840 : Int) atom0587Coded) := by decide +kernel
theorem block007_data_flat063_original : block007_data_flat063 = (CoefficientMerge.scale (87384840 : Int) atom0587Coded) := by
  rw [block007_data_flat063_step]
def block007_data_flat064 : CoefficientMerge.Poly := [(nat_lit 1735, Int.ofNat (nat_lit 16205184)), (nat_lit 1736, Int.ofNat (nat_lit 87384840))]
theorem block007_data_flat064_step : block007_data_flat064 = (CoefficientMerge.fastMerge block007_data_flat062 block007_data_flat063) := by decide +kernel
theorem block007_data_flat064_original : block007_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16205184 : Int) atom0586Coded) (CoefficientMerge.scale (87384840 : Int) atom0587Coded)) := by
  rw [block007_data_flat064_step, block007_data_flat062_original, block007_data_flat063_original]
def block007_data_flat065 : CoefficientMerge.Poly := [(nat_lit 1724, Int.ofNat (nat_lit 193577040)), (nat_lit 1735, Int.ofNat (nat_lit 16205184)), (nat_lit 1736, Int.ofNat (nat_lit 87384840))]
theorem block007_data_flat065_step : block007_data_flat065 = (CoefficientMerge.fastMerge block007_data_flat061 block007_data_flat064) := by decide +kernel
theorem block007_data_flat065_original : block007_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (193577040 : Int) atom0585Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16205184 : Int) atom0586Coded) (CoefficientMerge.scale (87384840 : Int) atom0587Coded))) := by
  rw [block007_data_flat065_step, block007_data_flat061_original, block007_data_flat064_original]
def block007_data_flat066 : CoefficientMerge.Poly := [(nat_lit 1722, Int.ofNat (nat_lit 140625120)), (nat_lit 1723, Int.ofNat (nat_lit 98938560)), (nat_lit 1724, Int.ofNat (nat_lit 193577040)), (nat_lit 1735, Int.ofNat (nat_lit 16205184)), (nat_lit 1736, Int.ofNat (nat_lit 87384840))]
theorem block007_data_flat066_step : block007_data_flat066 = (CoefficientMerge.fastMerge block007_data_flat060 block007_data_flat065) := by decide +kernel
theorem block007_data_flat066_original : block007_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (140625120 : Int) atom0583Coded) (CoefficientMerge.scale (98938560 : Int) atom0584Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193577040 : Int) atom0585Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16205184 : Int) atom0586Coded) (CoefficientMerge.scale (87384840 : Int) atom0587Coded)))) := by
  rw [block007_data_flat066_step, block007_data_flat060_original, block007_data_flat065_original]
def block007_data_flat067 : CoefficientMerge.Poly := [(nat_lit 1737, Int.ofNat (nat_lit 142194240))]
theorem block007_data_flat067_step : block007_data_flat067 = (CoefficientMerge.scale (142194240 : Int) atom0588Coded) := by decide +kernel
theorem block007_data_flat067_original : block007_data_flat067 = (CoefficientMerge.scale (142194240 : Int) atom0588Coded) := by
  rw [block007_data_flat067_step]
def block007_data_flat068 : CoefficientMerge.Poly := [(nat_lit 1738, Int.ofNat (nat_lit 120840960))]
theorem block007_data_flat068_step : block007_data_flat068 = (CoefficientMerge.scale (120840960 : Int) atom0589Coded) := by decide +kernel
theorem block007_data_flat068_original : block007_data_flat068 = (CoefficientMerge.scale (120840960 : Int) atom0589Coded) := by
  rw [block007_data_flat068_step]
def block007_data_flat069 : CoefficientMerge.Poly := [(nat_lit 1737, Int.ofNat (nat_lit 142194240)), (nat_lit 1738, Int.ofNat (nat_lit 120840960))]
theorem block007_data_flat069_step : block007_data_flat069 = (CoefficientMerge.fastMerge block007_data_flat067 block007_data_flat068) := by decide +kernel
theorem block007_data_flat069_original : block007_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (142194240 : Int) atom0588Coded) (CoefficientMerge.scale (120840960 : Int) atom0589Coded)) := by
  rw [block007_data_flat069_step, block007_data_flat067_original, block007_data_flat068_original]
def block007_data_flat070 : CoefficientMerge.Poly := [(nat_lit 1739, Int.ofNat (nat_lit 183474720))]
theorem block007_data_flat070_step : block007_data_flat070 = (CoefficientMerge.scale (183474720 : Int) atom0590Coded) := by decide +kernel
theorem block007_data_flat070_original : block007_data_flat070 = (CoefficientMerge.scale (183474720 : Int) atom0590Coded) := by
  rw [block007_data_flat070_step]
def block007_data_flat071 : CoefficientMerge.Poly := [(nat_lit 1751, Int.ofNat (nat_lit 82001160))]
theorem block007_data_flat071_step : block007_data_flat071 = (CoefficientMerge.scale (82001160 : Int) atom0591Coded) := by decide +kernel
theorem block007_data_flat071_original : block007_data_flat071 = (CoefficientMerge.scale (82001160 : Int) atom0591Coded) := by
  rw [block007_data_flat071_step]
def block007_data_flat072 : CoefficientMerge.Poly := [(nat_lit 1752, Int.ofNat (nat_lit 175846920))]
theorem block007_data_flat072_step : block007_data_flat072 = (CoefficientMerge.scale (175846920 : Int) atom0592Coded) := by decide +kernel
theorem block007_data_flat072_original : block007_data_flat072 = (CoefficientMerge.scale (175846920 : Int) atom0592Coded) := by
  rw [block007_data_flat072_step]
def block007_data_flat073 : CoefficientMerge.Poly := [(nat_lit 1751, Int.ofNat (nat_lit 82001160)), (nat_lit 1752, Int.ofNat (nat_lit 175846920))]
theorem block007_data_flat073_step : block007_data_flat073 = (CoefficientMerge.fastMerge block007_data_flat071 block007_data_flat072) := by decide +kernel
theorem block007_data_flat073_original : block007_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (82001160 : Int) atom0591Coded) (CoefficientMerge.scale (175846920 : Int) atom0592Coded)) := by
  rw [block007_data_flat073_step, block007_data_flat071_original, block007_data_flat072_original]
def block007_data_flat074 : CoefficientMerge.Poly := [(nat_lit 1739, Int.ofNat (nat_lit 183474720)), (nat_lit 1751, Int.ofNat (nat_lit 82001160)), (nat_lit 1752, Int.ofNat (nat_lit 175846920))]
theorem block007_data_flat074_step : block007_data_flat074 = (CoefficientMerge.fastMerge block007_data_flat070 block007_data_flat073) := by decide +kernel
theorem block007_data_flat074_original : block007_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (183474720 : Int) atom0590Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82001160 : Int) atom0591Coded) (CoefficientMerge.scale (175846920 : Int) atom0592Coded))) := by
  rw [block007_data_flat074_step, block007_data_flat070_original, block007_data_flat073_original]
def block007_data_flat075 : CoefficientMerge.Poly := [(nat_lit 1737, Int.ofNat (nat_lit 142194240)), (nat_lit 1738, Int.ofNat (nat_lit 120840960)), (nat_lit 1739, Int.ofNat (nat_lit 183474720)), (nat_lit 1751, Int.ofNat (nat_lit 82001160)), (nat_lit 1752, Int.ofNat (nat_lit 175846920))]
theorem block007_data_flat075_step : block007_data_flat075 = (CoefficientMerge.fastMerge block007_data_flat069 block007_data_flat074) := by decide +kernel
theorem block007_data_flat075_original : block007_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142194240 : Int) atom0588Coded) (CoefficientMerge.scale (120840960 : Int) atom0589Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183474720 : Int) atom0590Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82001160 : Int) atom0591Coded) (CoefficientMerge.scale (175846920 : Int) atom0592Coded)))) := by
  rw [block007_data_flat075_step, block007_data_flat069_original, block007_data_flat074_original]
def block007_data_flat076 : CoefficientMerge.Poly := [(nat_lit 1722, Int.ofNat (nat_lit 140625120)), (nat_lit 1723, Int.ofNat (nat_lit 98938560)), (nat_lit 1724, Int.ofNat (nat_lit 193577040)), (nat_lit 1735, Int.ofNat (nat_lit 16205184)), (nat_lit 1736, Int.ofNat (nat_lit 87384840)), (nat_lit 1737, Int.ofNat (nat_lit 142194240)), (nat_lit 1738, Int.ofNat (nat_lit 120840960)), (nat_lit 1739, Int.ofNat (nat_lit 183474720)), (nat_lit 1751, Int.ofNat (nat_lit 82001160)), (nat_lit 1752, Int.ofNat (nat_lit 175846920))]
theorem block007_data_flat076_step : block007_data_flat076 = (CoefficientMerge.fastMerge block007_data_flat066 block007_data_flat075) := by decide +kernel
theorem block007_data_flat076_original : block007_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (140625120 : Int) atom0583Coded) (CoefficientMerge.scale (98938560 : Int) atom0584Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193577040 : Int) atom0585Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16205184 : Int) atom0586Coded) (CoefficientMerge.scale (87384840 : Int) atom0587Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142194240 : Int) atom0588Coded) (CoefficientMerge.scale (120840960 : Int) atom0589Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183474720 : Int) atom0590Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82001160 : Int) atom0591Coded) (CoefficientMerge.scale (175846920 : Int) atom0592Coded))))) := by
  rw [block007_data_flat076_step, block007_data_flat066_original, block007_data_flat075_original]
def block007_data_flat077 : CoefficientMerge.Poly := [(nat_lit 1687, Int.ofNat (nat_lit 13440)), (nat_lit 1703, Int.ofNat (nat_lit 2284800)), (nat_lit 1705, Int.ofNat (nat_lit 509120)), (nat_lit 1706, Int.ofNat (nat_lit 11378240)), (nat_lit 1707, Int.ofNat (nat_lit 26440640)), (nat_lit 1708, Int.ofNat (nat_lit 33900480)), (nat_lit 1709, Int.ofNat (nat_lit 83671920)), (nat_lit 1719, Int.ofNat (nat_lit 14717760)), (nat_lit 1720, Int.ofNat (nat_lit 37833600)), (nat_lit 1721, Int.ofNat (nat_lit 108389280)), (nat_lit 1722, Int.ofNat (nat_lit 140625120)), (nat_lit 1723, Int.ofNat (nat_lit 98938560)), (nat_lit 1724, Int.ofNat (nat_lit 193577040)), (nat_lit 1735, Int.ofNat (nat_lit 16205184)), (nat_lit 1736, Int.ofNat (nat_lit 87384840)), (nat_lit 1737, Int.ofNat (nat_lit 142194240)), (nat_lit 1738, Int.ofNat (nat_lit 120840960)), (nat_lit 1739, Int.ofNat (nat_lit 183474720)), (nat_lit 1751, Int.ofNat (nat_lit 82001160)), (nat_lit 1752, Int.ofNat (nat_lit 175846920))]
theorem block007_data_flat077_step : block007_data_flat077 = (CoefficientMerge.fastMerge block007_data_flat057 block007_data_flat076) := by decide +kernel
theorem block007_data_flat077_original : block007_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13440 : Int) atom0573Coded) (CoefficientMerge.scale (2284800 : Int) atom0574Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (509120 : Int) atom0575Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11378240 : Int) atom0576Coded) (CoefficientMerge.scale (26440640 : Int) atom0577Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33900480 : Int) atom0578Coded) (CoefficientMerge.scale (83671920 : Int) atom0579Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14717760 : Int) atom0580Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37833600 : Int) atom0581Coded) (CoefficientMerge.scale (108389280 : Int) atom0582Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (140625120 : Int) atom0583Coded) (CoefficientMerge.scale (98938560 : Int) atom0584Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193577040 : Int) atom0585Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16205184 : Int) atom0586Coded) (CoefficientMerge.scale (87384840 : Int) atom0587Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142194240 : Int) atom0588Coded) (CoefficientMerge.scale (120840960 : Int) atom0589Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183474720 : Int) atom0590Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82001160 : Int) atom0591Coded) (CoefficientMerge.scale (175846920 : Int) atom0592Coded)))))) := by
  rw [block007_data_flat077_step, block007_data_flat057_original, block007_data_flat076_original]
def block007_data_flat078 : CoefficientMerge.Poly := [(nat_lit 1495, Int.ofNat (nat_lit 60699240)), (nat_lit 1496, Int.ofNat (nat_lit 126096480)), (nat_lit 1497, Int.ofNat (nat_lit 156091320)), (nat_lit 1498, Int.ofNat (nat_lit 110217240)), (nat_lit 1499, Int.ofNat (nat_lit 200423160)), (nat_lit 1510, Int.ofNat (nat_lit 26469504)), (nat_lit 1511, Int.ofNat (nat_lit 100582560)), (nat_lit 1512, Int.ofNat (nat_lit 147665700)), (nat_lit 1513, Int.ofNat (nat_lit 118586160)), (nat_lit 1514, Int.ofNat (nat_lit 173295990)), (nat_lit 1526, Int.ofNat (nat_lit 86044680)), (nat_lit 1527, Int.ofNat (nat_lit 170421840)), (nat_lit 1528, Int.ofNat (nat_lit 146729880)), (nat_lit 1529, Int.ofNat (nat_lit 224658360)), (nat_lit 1542, Int.ofNat (nat_lit 67597740)), (nat_lit 1543, Int.ofNat (nat_lit 129105900)), (nat_lit 1544, Int.ofNat (nat_lit 220009230)), (nat_lit 1558, Int.ofNat (nat_lit 40960080)), (nat_lit 1559, Int.ofNat (nat_lit 183914010)), (nat_lit 1574, Int.ofNat (nat_lit 132831090)), (nat_lit 1687, Int.ofNat (nat_lit 13440)), (nat_lit 1703, Int.ofNat (nat_lit 2284800)), (nat_lit 1705, Int.ofNat (nat_lit 509120)), (nat_lit 1706, Int.ofNat (nat_lit 11378240)), (nat_lit 1707, Int.ofNat (nat_lit 26440640)), (nat_lit 1708, Int.ofNat (nat_lit 33900480)), (nat_lit 1709, Int.ofNat (nat_lit 83671920)), (nat_lit 1719, Int.ofNat (nat_lit 14717760)), (nat_lit 1720, Int.ofNat (nat_lit 37833600)), (nat_lit 1721, Int.ofNat (nat_lit 108389280)), (nat_lit 1722, Int.ofNat (nat_lit 140625120)), (nat_lit 1723, Int.ofNat (nat_lit 98938560)), (nat_lit 1724, Int.ofNat (nat_lit 193577040)), (nat_lit 1735, Int.ofNat (nat_lit 16205184)), (nat_lit 1736, Int.ofNat (nat_lit 87384840)), (nat_lit 1737, Int.ofNat (nat_lit 142194240)), (nat_lit 1738, Int.ofNat (nat_lit 120840960)), (nat_lit 1739, Int.ofNat (nat_lit 183474720)), (nat_lit 1751, Int.ofNat (nat_lit 82001160)), (nat_lit 1752, Int.ofNat (nat_lit 175846920))]
theorem block007_data_flat078_step : block007_data_flat078 = (CoefficientMerge.fastMerge block007_data_flat038 block007_data_flat077) := by decide +kernel
theorem block007_data_flat078_original : block007_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60699240 : Int) atom0553Coded) (CoefficientMerge.scale (126096480 : Int) atom0554Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156091320 : Int) atom0555Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110217240 : Int) atom0556Coded) (CoefficientMerge.scale (200423160 : Int) atom0557Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26469504 : Int) atom0558Coded) (CoefficientMerge.scale (100582560 : Int) atom0559Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (147665700 : Int) atom0560Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118586160 : Int) atom0561Coded) (CoefficientMerge.scale (173295990 : Int) atom0562Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (86044680 : Int) atom0563Coded) (CoefficientMerge.scale (170421840 : Int) atom0564Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (146729880 : Int) atom0565Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (224658360 : Int) atom0566Coded) (CoefficientMerge.scale (67597740 : Int) atom0567Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129105900 : Int) atom0568Coded) (CoefficientMerge.scale (220009230 : Int) atom0569Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40960080 : Int) atom0570Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183914010 : Int) atom0571Coded) (CoefficientMerge.scale (132831090 : Int) atom0572Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13440 : Int) atom0573Coded) (CoefficientMerge.scale (2284800 : Int) atom0574Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (509120 : Int) atom0575Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11378240 : Int) atom0576Coded) (CoefficientMerge.scale (26440640 : Int) atom0577Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33900480 : Int) atom0578Coded) (CoefficientMerge.scale (83671920 : Int) atom0579Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14717760 : Int) atom0580Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37833600 : Int) atom0581Coded) (CoefficientMerge.scale (108389280 : Int) atom0582Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (140625120 : Int) atom0583Coded) (CoefficientMerge.scale (98938560 : Int) atom0584Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193577040 : Int) atom0585Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16205184 : Int) atom0586Coded) (CoefficientMerge.scale (87384840 : Int) atom0587Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142194240 : Int) atom0588Coded) (CoefficientMerge.scale (120840960 : Int) atom0589Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183474720 : Int) atom0590Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82001160 : Int) atom0591Coded) (CoefficientMerge.scale (175846920 : Int) atom0592Coded))))))) := by
  rw [block007_data_flat078_step, block007_data_flat038_original, block007_data_flat077_original]
def block007_data_flat079 : CoefficientMerge.Poly := [(nat_lit 1753, Int.ofNat (nat_lit 163720560))]
theorem block007_data_flat079_step : block007_data_flat079 = (CoefficientMerge.scale (163720560 : Int) atom0593Coded) := by decide +kernel
theorem block007_data_flat079_original : block007_data_flat079 = (CoefficientMerge.scale (163720560 : Int) atom0593Coded) := by
  rw [block007_data_flat079_step]
def block007_data_flat080 : CoefficientMerge.Poly := [(nat_lit 1754, Int.ofNat (nat_lit 253214640))]
theorem block007_data_flat080_step : block007_data_flat080 = (CoefficientMerge.scale (253214640 : Int) atom0594Coded) := by decide +kernel
theorem block007_data_flat080_original : block007_data_flat080 = (CoefficientMerge.scale (253214640 : Int) atom0594Coded) := by
  rw [block007_data_flat080_step]
def block007_data_flat081 : CoefficientMerge.Poly := [(nat_lit 1753, Int.ofNat (nat_lit 163720560)), (nat_lit 1754, Int.ofNat (nat_lit 253214640))]
theorem block007_data_flat081_step : block007_data_flat081 = (CoefficientMerge.fastMerge block007_data_flat079 block007_data_flat080) := by decide +kernel
theorem block007_data_flat081_original : block007_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (163720560 : Int) atom0593Coded) (CoefficientMerge.scale (253214640 : Int) atom0594Coded)) := by
  rw [block007_data_flat081_step, block007_data_flat079_original, block007_data_flat080_original]
def block007_data_flat082 : CoefficientMerge.Poly := [(nat_lit 1767, Int.ofNat (nat_lit 77264640))]
theorem block007_data_flat082_step : block007_data_flat082 = (CoefficientMerge.scale (77264640 : Int) atom0595Coded) := by decide +kernel
theorem block007_data_flat082_original : block007_data_flat082 = (CoefficientMerge.scale (77264640 : Int) atom0595Coded) := by
  rw [block007_data_flat082_step]
def block007_data_flat083 : CoefficientMerge.Poly := [(nat_lit 1768, Int.ofNat (nat_lit 164422560))]
theorem block007_data_flat083_step : block007_data_flat083 = (CoefficientMerge.scale (164422560 : Int) atom0596Coded) := by decide +kernel
theorem block007_data_flat083_original : block007_data_flat083 = (CoefficientMerge.scale (164422560 : Int) atom0596Coded) := by
  rw [block007_data_flat083_step]
def block007_data_flat084 : CoefficientMerge.Poly := [(nat_lit 1769, Int.ofNat (nat_lit 270259200))]
theorem block007_data_flat084_step : block007_data_flat084 = (CoefficientMerge.scale (270259200 : Int) atom0597Coded) := by decide +kernel
theorem block007_data_flat084_original : block007_data_flat084 = (CoefficientMerge.scale (270259200 : Int) atom0597Coded) := by
  rw [block007_data_flat084_step]
def block007_data_flat085 : CoefficientMerge.Poly := [(nat_lit 1768, Int.ofNat (nat_lit 164422560)), (nat_lit 1769, Int.ofNat (nat_lit 270259200))]
theorem block007_data_flat085_step : block007_data_flat085 = (CoefficientMerge.fastMerge block007_data_flat083 block007_data_flat084) := by decide +kernel
theorem block007_data_flat085_original : block007_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (164422560 : Int) atom0596Coded) (CoefficientMerge.scale (270259200 : Int) atom0597Coded)) := by
  rw [block007_data_flat085_step, block007_data_flat083_original, block007_data_flat084_original]
def block007_data_flat086 : CoefficientMerge.Poly := [(nat_lit 1767, Int.ofNat (nat_lit 77264640)), (nat_lit 1768, Int.ofNat (nat_lit 164422560)), (nat_lit 1769, Int.ofNat (nat_lit 270259200))]
theorem block007_data_flat086_step : block007_data_flat086 = (CoefficientMerge.fastMerge block007_data_flat082 block007_data_flat085) := by decide +kernel
theorem block007_data_flat086_original : block007_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (77264640 : Int) atom0595Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164422560 : Int) atom0596Coded) (CoefficientMerge.scale (270259200 : Int) atom0597Coded))) := by
  rw [block007_data_flat086_step, block007_data_flat082_original, block007_data_flat085_original]
def block007_data_flat087 : CoefficientMerge.Poly := [(nat_lit 1753, Int.ofNat (nat_lit 163720560)), (nat_lit 1754, Int.ofNat (nat_lit 253214640)), (nat_lit 1767, Int.ofNat (nat_lit 77264640)), (nat_lit 1768, Int.ofNat (nat_lit 164422560)), (nat_lit 1769, Int.ofNat (nat_lit 270259200))]
theorem block007_data_flat087_step : block007_data_flat087 = (CoefficientMerge.fastMerge block007_data_flat081 block007_data_flat086) := by decide +kernel
theorem block007_data_flat087_original : block007_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (163720560 : Int) atom0593Coded) (CoefficientMerge.scale (253214640 : Int) atom0594Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77264640 : Int) atom0595Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164422560 : Int) atom0596Coded) (CoefficientMerge.scale (270259200 : Int) atom0597Coded)))) := by
  rw [block007_data_flat087_step, block007_data_flat081_original, block007_data_flat086_original]
def block007_data_flat088 : CoefficientMerge.Poly := [(nat_lit 1783, Int.ofNat (nat_lit 65834880))]
theorem block007_data_flat088_step : block007_data_flat088 = (CoefficientMerge.scale (65834880 : Int) atom0598Coded) := by decide +kernel
theorem block007_data_flat088_original : block007_data_flat088 = (CoefficientMerge.scale (65834880 : Int) atom0598Coded) := by
  rw [block007_data_flat088_step]
def block007_data_flat089 : CoefficientMerge.Poly := [(nat_lit 1784, Int.ofNat (nat_lit 251478000))]
theorem block007_data_flat089_step : block007_data_flat089 = (CoefficientMerge.scale (251478000 : Int) atom0599Coded) := by decide +kernel
theorem block007_data_flat089_original : block007_data_flat089 = (CoefficientMerge.scale (251478000 : Int) atom0599Coded) := by
  rw [block007_data_flat089_step]
def block007_data_flat090 : CoefficientMerge.Poly := [(nat_lit 1783, Int.ofNat (nat_lit 65834880)), (nat_lit 1784, Int.ofNat (nat_lit 251478000))]
theorem block007_data_flat090_step : block007_data_flat090 = (CoefficientMerge.fastMerge block007_data_flat088 block007_data_flat089) := by decide +kernel
theorem block007_data_flat090_original : block007_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (65834880 : Int) atom0598Coded) (CoefficientMerge.scale (251478000 : Int) atom0599Coded)) := by
  rw [block007_data_flat090_step, block007_data_flat088_original, block007_data_flat089_original]
def block007_data_flat091 : CoefficientMerge.Poly := [(nat_lit 1799, Int.ofNat (nat_lit 174182400))]
theorem block007_data_flat091_step : block007_data_flat091 = (CoefficientMerge.scale (174182400 : Int) atom0600Coded) := by decide +kernel
theorem block007_data_flat091_original : block007_data_flat091 = (CoefficientMerge.scale (174182400 : Int) atom0600Coded) := by
  rw [block007_data_flat091_step]
def block007_data_flat092 : CoefficientMerge.Poly := [(nat_lit 1931, Int.ofNat (nat_lit 3436560))]
theorem block007_data_flat092_step : block007_data_flat092 = (CoefficientMerge.scale (3436560 : Int) atom0601Coded) := by decide +kernel
theorem block007_data_flat092_original : block007_data_flat092 = (CoefficientMerge.scale (3436560 : Int) atom0601Coded) := by
  rw [block007_data_flat092_step]
def block007_data_flat093 : CoefficientMerge.Poly := [(nat_lit 1932, Int.ofNat (nat_lit 8981280))]
theorem block007_data_flat093_step : block007_data_flat093 = (CoefficientMerge.scale (8981280 : Int) atom0602Coded) := by decide +kernel
theorem block007_data_flat093_original : block007_data_flat093 = (CoefficientMerge.scale (8981280 : Int) atom0602Coded) := by
  rw [block007_data_flat093_step]
def block007_data_flat094 : CoefficientMerge.Poly := [(nat_lit 1931, Int.ofNat (nat_lit 3436560)), (nat_lit 1932, Int.ofNat (nat_lit 8981280))]
theorem block007_data_flat094_step : block007_data_flat094 = (CoefficientMerge.fastMerge block007_data_flat092 block007_data_flat093) := by decide +kernel
theorem block007_data_flat094_original : block007_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3436560 : Int) atom0601Coded) (CoefficientMerge.scale (8981280 : Int) atom0602Coded)) := by
  rw [block007_data_flat094_step, block007_data_flat092_original, block007_data_flat093_original]
def block007_data_flat095 : CoefficientMerge.Poly := [(nat_lit 1799, Int.ofNat (nat_lit 174182400)), (nat_lit 1931, Int.ofNat (nat_lit 3436560)), (nat_lit 1932, Int.ofNat (nat_lit 8981280))]
theorem block007_data_flat095_step : block007_data_flat095 = (CoefficientMerge.fastMerge block007_data_flat091 block007_data_flat094) := by decide +kernel
theorem block007_data_flat095_original : block007_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (174182400 : Int) atom0600Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3436560 : Int) atom0601Coded) (CoefficientMerge.scale (8981280 : Int) atom0602Coded))) := by
  rw [block007_data_flat095_step, block007_data_flat091_original, block007_data_flat094_original]
def block007_data_flat096 : CoefficientMerge.Poly := [(nat_lit 1783, Int.ofNat (nat_lit 65834880)), (nat_lit 1784, Int.ofNat (nat_lit 251478000)), (nat_lit 1799, Int.ofNat (nat_lit 174182400)), (nat_lit 1931, Int.ofNat (nat_lit 3436560)), (nat_lit 1932, Int.ofNat (nat_lit 8981280))]
theorem block007_data_flat096_step : block007_data_flat096 = (CoefficientMerge.fastMerge block007_data_flat090 block007_data_flat095) := by decide +kernel
theorem block007_data_flat096_original : block007_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65834880 : Int) atom0598Coded) (CoefficientMerge.scale (251478000 : Int) atom0599Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174182400 : Int) atom0600Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3436560 : Int) atom0601Coded) (CoefficientMerge.scale (8981280 : Int) atom0602Coded)))) := by
  rw [block007_data_flat096_step, block007_data_flat090_original, block007_data_flat095_original]
def block007_data_flat097 : CoefficientMerge.Poly := [(nat_lit 1753, Int.ofNat (nat_lit 163720560)), (nat_lit 1754, Int.ofNat (nat_lit 253214640)), (nat_lit 1767, Int.ofNat (nat_lit 77264640)), (nat_lit 1768, Int.ofNat (nat_lit 164422560)), (nat_lit 1769, Int.ofNat (nat_lit 270259200)), (nat_lit 1783, Int.ofNat (nat_lit 65834880)), (nat_lit 1784, Int.ofNat (nat_lit 251478000)), (nat_lit 1799, Int.ofNat (nat_lit 174182400)), (nat_lit 1931, Int.ofNat (nat_lit 3436560)), (nat_lit 1932, Int.ofNat (nat_lit 8981280))]
theorem block007_data_flat097_step : block007_data_flat097 = (CoefficientMerge.fastMerge block007_data_flat087 block007_data_flat096) := by decide +kernel
theorem block007_data_flat097_original : block007_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (163720560 : Int) atom0593Coded) (CoefficientMerge.scale (253214640 : Int) atom0594Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77264640 : Int) atom0595Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164422560 : Int) atom0596Coded) (CoefficientMerge.scale (270259200 : Int) atom0597Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65834880 : Int) atom0598Coded) (CoefficientMerge.scale (251478000 : Int) atom0599Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174182400 : Int) atom0600Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3436560 : Int) atom0601Coded) (CoefficientMerge.scale (8981280 : Int) atom0602Coded))))) := by
  rw [block007_data_flat097_step, block007_data_flat087_original, block007_data_flat096_original]
def block007_data_flat098 : CoefficientMerge.Poly := [(nat_lit 1934, Int.ofNat (nat_lit 30443040))]
theorem block007_data_flat098_step : block007_data_flat098 = (CoefficientMerge.scale (30443040 : Int) atom0603Coded) := by decide +kernel
theorem block007_data_flat098_original : block007_data_flat098 = (CoefficientMerge.scale (30443040 : Int) atom0603Coded) := by
  rw [block007_data_flat098_step]
def block007_data_flat099 : CoefficientMerge.Poly := [(nat_lit 1944, Int.ofNat (nat_lit 3985200))]
theorem block007_data_flat099_step : block007_data_flat099 = (CoefficientMerge.scale (3985200 : Int) atom0604Coded) := by decide +kernel
theorem block007_data_flat099_original : block007_data_flat099 = (CoefficientMerge.scale (3985200 : Int) atom0604Coded) := by
  rw [block007_data_flat099_step]
def block007_data_flat100 : CoefficientMerge.Poly := [(nat_lit 1934, Int.ofNat (nat_lit 30443040)), (nat_lit 1944, Int.ofNat (nat_lit 3985200))]
theorem block007_data_flat100_step : block007_data_flat100 = (CoefficientMerge.fastMerge block007_data_flat098 block007_data_flat099) := by decide +kernel
theorem block007_data_flat100_original : block007_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30443040 : Int) atom0603Coded) (CoefficientMerge.scale (3985200 : Int) atom0604Coded)) := by
  rw [block007_data_flat100_step, block007_data_flat098_original, block007_data_flat099_original]
def block007_data_flat101 : CoefficientMerge.Poly := [(nat_lit 1945, Int.ofNat (nat_lit 14832720))]
theorem block007_data_flat101_step : block007_data_flat101 = (CoefficientMerge.scale (14832720 : Int) atom0605Coded) := by decide +kernel
theorem block007_data_flat101_original : block007_data_flat101 = (CoefficientMerge.scale (14832720 : Int) atom0605Coded) := by
  rw [block007_data_flat101_step]
def block007_data_flat102 : CoefficientMerge.Poly := [(nat_lit 1946, Int.ofNat (nat_lit 87102000))]
theorem block007_data_flat102_step : block007_data_flat102 = (CoefficientMerge.scale (87102000 : Int) atom0606Coded) := by decide +kernel
theorem block007_data_flat102_original : block007_data_flat102 = (CoefficientMerge.scale (87102000 : Int) atom0606Coded) := by
  rw [block007_data_flat102_step]
def block007_data_flat103 : CoefficientMerge.Poly := [(nat_lit 1947, Int.ofNat (nat_lit 121237560))]
theorem block007_data_flat103_step : block007_data_flat103 = (CoefficientMerge.scale (121237560 : Int) atom0607Coded) := by decide +kernel
theorem block007_data_flat103_original : block007_data_flat103 = (CoefficientMerge.scale (121237560 : Int) atom0607Coded) := by
  rw [block007_data_flat103_step]
def block007_data_flat104 : CoefficientMerge.Poly := [(nat_lit 1946, Int.ofNat (nat_lit 87102000)), (nat_lit 1947, Int.ofNat (nat_lit 121237560))]
theorem block007_data_flat104_step : block007_data_flat104 = (CoefficientMerge.fastMerge block007_data_flat102 block007_data_flat103) := by decide +kernel
theorem block007_data_flat104_original : block007_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (87102000 : Int) atom0606Coded) (CoefficientMerge.scale (121237560 : Int) atom0607Coded)) := by
  rw [block007_data_flat104_step, block007_data_flat102_original, block007_data_flat103_original]
def block007_data_flat105 : CoefficientMerge.Poly := [(nat_lit 1945, Int.ofNat (nat_lit 14832720)), (nat_lit 1946, Int.ofNat (nat_lit 87102000)), (nat_lit 1947, Int.ofNat (nat_lit 121237560))]
theorem block007_data_flat105_step : block007_data_flat105 = (CoefficientMerge.fastMerge block007_data_flat101 block007_data_flat104) := by decide +kernel
theorem block007_data_flat105_original : block007_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14832720 : Int) atom0605Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87102000 : Int) atom0606Coded) (CoefficientMerge.scale (121237560 : Int) atom0607Coded))) := by
  rw [block007_data_flat105_step, block007_data_flat101_original, block007_data_flat104_original]
def block007_data_flat106 : CoefficientMerge.Poly := [(nat_lit 1934, Int.ofNat (nat_lit 30443040)), (nat_lit 1944, Int.ofNat (nat_lit 3985200)), (nat_lit 1945, Int.ofNat (nat_lit 14832720)), (nat_lit 1946, Int.ofNat (nat_lit 87102000)), (nat_lit 1947, Int.ofNat (nat_lit 121237560))]
theorem block007_data_flat106_step : block007_data_flat106 = (CoefficientMerge.fastMerge block007_data_flat100 block007_data_flat105) := by decide +kernel
theorem block007_data_flat106_original : block007_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30443040 : Int) atom0603Coded) (CoefficientMerge.scale (3985200 : Int) atom0604Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14832720 : Int) atom0605Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87102000 : Int) atom0606Coded) (CoefficientMerge.scale (121237560 : Int) atom0607Coded)))) := by
  rw [block007_data_flat106_step, block007_data_flat100_original, block007_data_flat105_original]
def block007_data_flat107 : CoefficientMerge.Poly := [(nat_lit 1948, Int.ofNat (nat_lit 75718800))]
theorem block007_data_flat107_step : block007_data_flat107 = (CoefficientMerge.scale (75718800 : Int) atom0608Coded) := by decide +kernel
theorem block007_data_flat107_original : block007_data_flat107 = (CoefficientMerge.scale (75718800 : Int) atom0608Coded) := by
  rw [block007_data_flat107_step]
def block007_data_flat108 : CoefficientMerge.Poly := [(nat_lit 1949, Int.ofNat (nat_lit 187377300))]
theorem block007_data_flat108_step : block007_data_flat108 = (CoefficientMerge.scale (187377300 : Int) atom0609Coded) := by decide +kernel
theorem block007_data_flat108_original : block007_data_flat108 = (CoefficientMerge.scale (187377300 : Int) atom0609Coded) := by
  rw [block007_data_flat108_step]
def block007_data_flat109 : CoefficientMerge.Poly := [(nat_lit 1948, Int.ofNat (nat_lit 75718800)), (nat_lit 1949, Int.ofNat (nat_lit 187377300))]
theorem block007_data_flat109_step : block007_data_flat109 = (CoefficientMerge.fastMerge block007_data_flat107 block007_data_flat108) := by decide +kernel
theorem block007_data_flat109_original : block007_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (75718800 : Int) atom0608Coded) (CoefficientMerge.scale (187377300 : Int) atom0609Coded)) := by
  rw [block007_data_flat109_step, block007_data_flat107_original, block007_data_flat108_original]
def block007_data_flat110 : CoefficientMerge.Poly := [(nat_lit 1960, Int.ofNat (nat_lit 5940864))]
theorem block007_data_flat110_step : block007_data_flat110 = (CoefficientMerge.scale (5940864 : Int) atom0610Coded) := by decide +kernel
theorem block007_data_flat110_original : block007_data_flat110 = (CoefficientMerge.scale (5940864 : Int) atom0610Coded) := by
  rw [block007_data_flat110_step]
def block007_data_flat111 : CoefficientMerge.Poly := [(nat_lit 1961, Int.ofNat (nat_lit 74322360))]
theorem block007_data_flat111_step : block007_data_flat111 = (CoefficientMerge.scale (74322360 : Int) atom0611Coded) := by decide +kernel
theorem block007_data_flat111_original : block007_data_flat111 = (CoefficientMerge.scale (74322360 : Int) atom0611Coded) := by
  rw [block007_data_flat111_step]
def block007_data_flat112 : CoefficientMerge.Poly := [(nat_lit 1962, Int.ofNat (nat_lit 136925640))]
theorem block007_data_flat112_step : block007_data_flat112 = (CoefficientMerge.scale (136925640 : Int) atom0612Coded) := by decide +kernel
theorem block007_data_flat112_original : block007_data_flat112 = (CoefficientMerge.scale (136925640 : Int) atom0612Coded) := by
  rw [block007_data_flat112_step]
def block007_data_flat113 : CoefficientMerge.Poly := [(nat_lit 1961, Int.ofNat (nat_lit 74322360)), (nat_lit 1962, Int.ofNat (nat_lit 136925640))]
theorem block007_data_flat113_step : block007_data_flat113 = (CoefficientMerge.fastMerge block007_data_flat111 block007_data_flat112) := by decide +kernel
theorem block007_data_flat113_original : block007_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (74322360 : Int) atom0611Coded) (CoefficientMerge.scale (136925640 : Int) atom0612Coded)) := by
  rw [block007_data_flat113_step, block007_data_flat111_original, block007_data_flat112_original]
def block007_data_flat114 : CoefficientMerge.Poly := [(nat_lit 1960, Int.ofNat (nat_lit 5940864)), (nat_lit 1961, Int.ofNat (nat_lit 74322360)), (nat_lit 1962, Int.ofNat (nat_lit 136925640))]
theorem block007_data_flat114_step : block007_data_flat114 = (CoefficientMerge.fastMerge block007_data_flat110 block007_data_flat113) := by decide +kernel
theorem block007_data_flat114_original : block007_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5940864 : Int) atom0610Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74322360 : Int) atom0611Coded) (CoefficientMerge.scale (136925640 : Int) atom0612Coded))) := by
  rw [block007_data_flat114_step, block007_data_flat110_original, block007_data_flat113_original]
def block007_data_flat115 : CoefficientMerge.Poly := [(nat_lit 1948, Int.ofNat (nat_lit 75718800)), (nat_lit 1949, Int.ofNat (nat_lit 187377300)), (nat_lit 1960, Int.ofNat (nat_lit 5940864)), (nat_lit 1961, Int.ofNat (nat_lit 74322360)), (nat_lit 1962, Int.ofNat (nat_lit 136925640))]
theorem block007_data_flat115_step : block007_data_flat115 = (CoefficientMerge.fastMerge block007_data_flat109 block007_data_flat114) := by decide +kernel
theorem block007_data_flat115_original : block007_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75718800 : Int) atom0608Coded) (CoefficientMerge.scale (187377300 : Int) atom0609Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5940864 : Int) atom0610Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74322360 : Int) atom0611Coded) (CoefficientMerge.scale (136925640 : Int) atom0612Coded)))) := by
  rw [block007_data_flat115_step, block007_data_flat109_original, block007_data_flat114_original]
def block007_data_flat116 : CoefficientMerge.Poly := [(nat_lit 1934, Int.ofNat (nat_lit 30443040)), (nat_lit 1944, Int.ofNat (nat_lit 3985200)), (nat_lit 1945, Int.ofNat (nat_lit 14832720)), (nat_lit 1946, Int.ofNat (nat_lit 87102000)), (nat_lit 1947, Int.ofNat (nat_lit 121237560)), (nat_lit 1948, Int.ofNat (nat_lit 75718800)), (nat_lit 1949, Int.ofNat (nat_lit 187377300)), (nat_lit 1960, Int.ofNat (nat_lit 5940864)), (nat_lit 1961, Int.ofNat (nat_lit 74322360)), (nat_lit 1962, Int.ofNat (nat_lit 136925640))]
theorem block007_data_flat116_step : block007_data_flat116 = (CoefficientMerge.fastMerge block007_data_flat106 block007_data_flat115) := by decide +kernel
theorem block007_data_flat116_original : block007_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30443040 : Int) atom0603Coded) (CoefficientMerge.scale (3985200 : Int) atom0604Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14832720 : Int) atom0605Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87102000 : Int) atom0606Coded) (CoefficientMerge.scale (121237560 : Int) atom0607Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75718800 : Int) atom0608Coded) (CoefficientMerge.scale (187377300 : Int) atom0609Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5940864 : Int) atom0610Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74322360 : Int) atom0611Coded) (CoefficientMerge.scale (136925640 : Int) atom0612Coded))))) := by
  rw [block007_data_flat116_step, block007_data_flat106_original, block007_data_flat115_original]
def block007_data_flat117 : CoefficientMerge.Poly := [(nat_lit 1753, Int.ofNat (nat_lit 163720560)), (nat_lit 1754, Int.ofNat (nat_lit 253214640)), (nat_lit 1767, Int.ofNat (nat_lit 77264640)), (nat_lit 1768, Int.ofNat (nat_lit 164422560)), (nat_lit 1769, Int.ofNat (nat_lit 270259200)), (nat_lit 1783, Int.ofNat (nat_lit 65834880)), (nat_lit 1784, Int.ofNat (nat_lit 251478000)), (nat_lit 1799, Int.ofNat (nat_lit 174182400)), (nat_lit 1931, Int.ofNat (nat_lit 3436560)), (nat_lit 1932, Int.ofNat (nat_lit 8981280)), (nat_lit 1934, Int.ofNat (nat_lit 30443040)), (nat_lit 1944, Int.ofNat (nat_lit 3985200)), (nat_lit 1945, Int.ofNat (nat_lit 14832720)), (nat_lit 1946, Int.ofNat (nat_lit 87102000)), (nat_lit 1947, Int.ofNat (nat_lit 121237560)), (nat_lit 1948, Int.ofNat (nat_lit 75718800)), (nat_lit 1949, Int.ofNat (nat_lit 187377300)), (nat_lit 1960, Int.ofNat (nat_lit 5940864)), (nat_lit 1961, Int.ofNat (nat_lit 74322360)), (nat_lit 1962, Int.ofNat (nat_lit 136925640))]
theorem block007_data_flat117_step : block007_data_flat117 = (CoefficientMerge.fastMerge block007_data_flat097 block007_data_flat116) := by decide +kernel
theorem block007_data_flat117_original : block007_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (163720560 : Int) atom0593Coded) (CoefficientMerge.scale (253214640 : Int) atom0594Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77264640 : Int) atom0595Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164422560 : Int) atom0596Coded) (CoefficientMerge.scale (270259200 : Int) atom0597Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65834880 : Int) atom0598Coded) (CoefficientMerge.scale (251478000 : Int) atom0599Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174182400 : Int) atom0600Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3436560 : Int) atom0601Coded) (CoefficientMerge.scale (8981280 : Int) atom0602Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30443040 : Int) atom0603Coded) (CoefficientMerge.scale (3985200 : Int) atom0604Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14832720 : Int) atom0605Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87102000 : Int) atom0606Coded) (CoefficientMerge.scale (121237560 : Int) atom0607Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75718800 : Int) atom0608Coded) (CoefficientMerge.scale (187377300 : Int) atom0609Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5940864 : Int) atom0610Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74322360 : Int) atom0611Coded) (CoefficientMerge.scale (136925640 : Int) atom0612Coded)))))) := by
  rw [block007_data_flat117_step, block007_data_flat097_original, block007_data_flat116_original]
def block007_data_flat118 : CoefficientMerge.Poly := [(nat_lit 1963, Int.ofNat (nat_lit 123366240))]
theorem block007_data_flat118_step : block007_data_flat118 = (CoefficientMerge.scale (123366240 : Int) atom0613Coded) := by decide +kernel
theorem block007_data_flat118_original : block007_data_flat118 = (CoefficientMerge.scale (123366240 : Int) atom0613Coded) := by
  rw [block007_data_flat118_step]
def block007_data_flat119 : CoefficientMerge.Poly := [(nat_lit 1964, Int.ofNat (nat_lit 193957740))]
theorem block007_data_flat119_step : block007_data_flat119 = (CoefficientMerge.scale (193957740 : Int) atom0614Coded) := by decide +kernel
theorem block007_data_flat119_original : block007_data_flat119 = (CoefficientMerge.scale (193957740 : Int) atom0614Coded) := by
  rw [block007_data_flat119_step]
def block007_data_flat120 : CoefficientMerge.Poly := [(nat_lit 1963, Int.ofNat (nat_lit 123366240)), (nat_lit 1964, Int.ofNat (nat_lit 193957740))]
theorem block007_data_flat120_step : block007_data_flat120 = (CoefficientMerge.fastMerge block007_data_flat118 block007_data_flat119) := by decide +kernel
theorem block007_data_flat120_original : block007_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (123366240 : Int) atom0613Coded) (CoefficientMerge.scale (193957740 : Int) atom0614Coded)) := by
  rw [block007_data_flat120_step, block007_data_flat118_original, block007_data_flat119_original]
def block007_data_flat121 : CoefficientMerge.Poly := [(nat_lit 1976, Int.ofNat (nat_lit 77957640))]
theorem block007_data_flat121_step : block007_data_flat121 = (CoefficientMerge.scale (77957640 : Int) atom0615Coded) := by decide +kernel
theorem block007_data_flat121_original : block007_data_flat121 = (CoefficientMerge.scale (77957640 : Int) atom0615Coded) := by
  rw [block007_data_flat121_step]
def block007_data_flat122 : CoefficientMerge.Poly := [(nat_lit 1977, Int.ofNat (nat_lit 179823240))]
theorem block007_data_flat122_step : block007_data_flat122 = (CoefficientMerge.scale (179823240 : Int) atom0616Coded) := by decide +kernel
theorem block007_data_flat122_original : block007_data_flat122 = (CoefficientMerge.scale (179823240 : Int) atom0616Coded) := by
  rw [block007_data_flat122_step]
def block007_data_flat123 : CoefficientMerge.Poly := [(nat_lit 1978, Int.ofNat (nat_lit 185492160))]
theorem block007_data_flat123_step : block007_data_flat123 = (CoefficientMerge.scale (185492160 : Int) atom0617Coded) := by decide +kernel
theorem block007_data_flat123_original : block007_data_flat123 = (CoefficientMerge.scale (185492160 : Int) atom0617Coded) := by
  rw [block007_data_flat123_step]
def block007_data_flat124 : CoefficientMerge.Poly := [(nat_lit 1977, Int.ofNat (nat_lit 179823240)), (nat_lit 1978, Int.ofNat (nat_lit 185492160))]
theorem block007_data_flat124_step : block007_data_flat124 = (CoefficientMerge.fastMerge block007_data_flat122 block007_data_flat123) := by decide +kernel
theorem block007_data_flat124_original : block007_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (179823240 : Int) atom0616Coded) (CoefficientMerge.scale (185492160 : Int) atom0617Coded)) := by
  rw [block007_data_flat124_step, block007_data_flat122_original, block007_data_flat123_original]
def block007_data_flat125 : CoefficientMerge.Poly := [(nat_lit 1976, Int.ofNat (nat_lit 77957640)), (nat_lit 1977, Int.ofNat (nat_lit 179823240)), (nat_lit 1978, Int.ofNat (nat_lit 185492160))]
theorem block007_data_flat125_step : block007_data_flat125 = (CoefficientMerge.fastMerge block007_data_flat121 block007_data_flat124) := by decide +kernel
theorem block007_data_flat125_original : block007_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (77957640 : Int) atom0615Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179823240 : Int) atom0616Coded) (CoefficientMerge.scale (185492160 : Int) atom0617Coded))) := by
  rw [block007_data_flat125_step, block007_data_flat121_original, block007_data_flat124_original]
def block007_data_flat126 : CoefficientMerge.Poly := [(nat_lit 1963, Int.ofNat (nat_lit 123366240)), (nat_lit 1964, Int.ofNat (nat_lit 193957740)), (nat_lit 1976, Int.ofNat (nat_lit 77957640)), (nat_lit 1977, Int.ofNat (nat_lit 179823240)), (nat_lit 1978, Int.ofNat (nat_lit 185492160))]
theorem block007_data_flat126_step : block007_data_flat126 = (CoefficientMerge.fastMerge block007_data_flat120 block007_data_flat125) := by decide +kernel
theorem block007_data_flat126_original : block007_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (123366240 : Int) atom0613Coded) (CoefficientMerge.scale (193957740 : Int) atom0614Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77957640 : Int) atom0615Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179823240 : Int) atom0616Coded) (CoefficientMerge.scale (185492160 : Int) atom0617Coded)))) := by
  rw [block007_data_flat126_step, block007_data_flat120_original, block007_data_flat125_original]
def block007_data_flat127 : CoefficientMerge.Poly := [(nat_lit 1979, Int.ofNat (nat_lit 273069360))]
theorem block007_data_flat127_step : block007_data_flat127 = (CoefficientMerge.scale (273069360 : Int) atom0618Coded) := by decide +kernel
theorem block007_data_flat127_original : block007_data_flat127 = (CoefficientMerge.scale (273069360 : Int) atom0618Coded) := by
  rw [block007_data_flat127_step]
def block007_data_flat128 : CoefficientMerge.Poly := [(nat_lit 1992, Int.ofNat (nat_lit 84758400))]
theorem block007_data_flat128_step : block007_data_flat128 = (CoefficientMerge.scale (84758400 : Int) atom0619Coded) := by decide +kernel
theorem block007_data_flat128_original : block007_data_flat128 = (CoefficientMerge.scale (84758400 : Int) atom0619Coded) := by
  rw [block007_data_flat128_step]
def block007_data_flat129 : CoefficientMerge.Poly := [(nat_lit 1979, Int.ofNat (nat_lit 273069360)), (nat_lit 1992, Int.ofNat (nat_lit 84758400))]
theorem block007_data_flat129_step : block007_data_flat129 = (CoefficientMerge.fastMerge block007_data_flat127 block007_data_flat128) := by decide +kernel
theorem block007_data_flat129_original : block007_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (273069360 : Int) atom0618Coded) (CoefficientMerge.scale (84758400 : Int) atom0619Coded)) := by
  rw [block007_data_flat129_step, block007_data_flat127_original, block007_data_flat128_original]
def block007_data_flat130 : CoefficientMerge.Poly := [(nat_lit 1993, Int.ofNat (nat_lit 204013080))]
theorem block007_data_flat130_step : block007_data_flat130 = (CoefficientMerge.scale (204013080 : Int) atom0620Coded) := by decide +kernel
theorem block007_data_flat130_original : block007_data_flat130 = (CoefficientMerge.scale (204013080 : Int) atom0620Coded) := by
  rw [block007_data_flat130_step]
def block007_data_flat131 : CoefficientMerge.Poly := [(nat_lit 1994, Int.ofNat (nat_lit 304197120))]
theorem block007_data_flat131_step : block007_data_flat131 = (CoefficientMerge.scale (304197120 : Int) atom0621Coded) := by decide +kernel
theorem block007_data_flat131_original : block007_data_flat131 = (CoefficientMerge.scale (304197120 : Int) atom0621Coded) := by
  rw [block007_data_flat131_step]
def block007_data_flat132 : CoefficientMerge.Poly := [(nat_lit 2008, Int.ofNat (nat_lit 100271520))]
theorem block007_data_flat132_step : block007_data_flat132 = (CoefficientMerge.scale (100271520 : Int) atom0622Coded) := by decide +kernel
theorem block007_data_flat132_original : block007_data_flat132 = (CoefficientMerge.scale (100271520 : Int) atom0622Coded) := by
  rw [block007_data_flat132_step]
def block007_data_flat133 : CoefficientMerge.Poly := [(nat_lit 1994, Int.ofNat (nat_lit 304197120)), (nat_lit 2008, Int.ofNat (nat_lit 100271520))]
theorem block007_data_flat133_step : block007_data_flat133 = (CoefficientMerge.fastMerge block007_data_flat131 block007_data_flat132) := by decide +kernel
theorem block007_data_flat133_original : block007_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (304197120 : Int) atom0621Coded) (CoefficientMerge.scale (100271520 : Int) atom0622Coded)) := by
  rw [block007_data_flat133_step, block007_data_flat131_original, block007_data_flat132_original]
def block007_data_flat134 : CoefficientMerge.Poly := [(nat_lit 1993, Int.ofNat (nat_lit 204013080)), (nat_lit 1994, Int.ofNat (nat_lit 304197120)), (nat_lit 2008, Int.ofNat (nat_lit 100271520))]
theorem block007_data_flat134_step : block007_data_flat134 = (CoefficientMerge.fastMerge block007_data_flat130 block007_data_flat133) := by decide +kernel
theorem block007_data_flat134_original : block007_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (204013080 : Int) atom0620Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (304197120 : Int) atom0621Coded) (CoefficientMerge.scale (100271520 : Int) atom0622Coded))) := by
  rw [block007_data_flat134_step, block007_data_flat130_original, block007_data_flat133_original]
def block007_data_flat135 : CoefficientMerge.Poly := [(nat_lit 1979, Int.ofNat (nat_lit 273069360)), (nat_lit 1992, Int.ofNat (nat_lit 84758400)), (nat_lit 1993, Int.ofNat (nat_lit 204013080)), (nat_lit 1994, Int.ofNat (nat_lit 304197120)), (nat_lit 2008, Int.ofNat (nat_lit 100271520))]
theorem block007_data_flat135_step : block007_data_flat135 = (CoefficientMerge.fastMerge block007_data_flat129 block007_data_flat134) := by decide +kernel
theorem block007_data_flat135_original : block007_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (273069360 : Int) atom0618Coded) (CoefficientMerge.scale (84758400 : Int) atom0619Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (204013080 : Int) atom0620Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (304197120 : Int) atom0621Coded) (CoefficientMerge.scale (100271520 : Int) atom0622Coded)))) := by
  rw [block007_data_flat135_step, block007_data_flat129_original, block007_data_flat134_original]
def block007_data_flat136 : CoefficientMerge.Poly := [(nat_lit 1963, Int.ofNat (nat_lit 123366240)), (nat_lit 1964, Int.ofNat (nat_lit 193957740)), (nat_lit 1976, Int.ofNat (nat_lit 77957640)), (nat_lit 1977, Int.ofNat (nat_lit 179823240)), (nat_lit 1978, Int.ofNat (nat_lit 185492160)), (nat_lit 1979, Int.ofNat (nat_lit 273069360)), (nat_lit 1992, Int.ofNat (nat_lit 84758400)), (nat_lit 1993, Int.ofNat (nat_lit 204013080)), (nat_lit 1994, Int.ofNat (nat_lit 304197120)), (nat_lit 2008, Int.ofNat (nat_lit 100271520))]
theorem block007_data_flat136_step : block007_data_flat136 = (CoefficientMerge.fastMerge block007_data_flat126 block007_data_flat135) := by decide +kernel
theorem block007_data_flat136_original : block007_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (123366240 : Int) atom0613Coded) (CoefficientMerge.scale (193957740 : Int) atom0614Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77957640 : Int) atom0615Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179823240 : Int) atom0616Coded) (CoefficientMerge.scale (185492160 : Int) atom0617Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (273069360 : Int) atom0618Coded) (CoefficientMerge.scale (84758400 : Int) atom0619Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (204013080 : Int) atom0620Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (304197120 : Int) atom0621Coded) (CoefficientMerge.scale (100271520 : Int) atom0622Coded))))) := by
  rw [block007_data_flat136_step, block007_data_flat126_original, block007_data_flat135_original]
def block007_data_flat137 : CoefficientMerge.Poly := [(nat_lit 2009, Int.ofNat (nat_lit 312395940))]
theorem block007_data_flat137_step : block007_data_flat137 = (CoefficientMerge.scale (312395940 : Int) atom0623Coded) := by decide +kernel
theorem block007_data_flat137_original : block007_data_flat137 = (CoefficientMerge.scale (312395940 : Int) atom0623Coded) := by
  rw [block007_data_flat137_step]
def block007_data_flat138 : CoefficientMerge.Poly := [(nat_lit 2024, Int.ofNat (nat_lit 195955200))]
theorem block007_data_flat138_step : block007_data_flat138 = (CoefficientMerge.scale (195955200 : Int) atom0624Coded) := by decide +kernel
theorem block007_data_flat138_original : block007_data_flat138 = (CoefficientMerge.scale (195955200 : Int) atom0624Coded) := by
  rw [block007_data_flat138_step]
def block007_data_flat139 : CoefficientMerge.Poly := [(nat_lit 2009, Int.ofNat (nat_lit 312395940)), (nat_lit 2024, Int.ofNat (nat_lit 195955200))]
theorem block007_data_flat139_step : block007_data_flat139 = (CoefficientMerge.fastMerge block007_data_flat137 block007_data_flat138) := by decide +kernel
theorem block007_data_flat139_original : block007_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (312395940 : Int) atom0623Coded) (CoefficientMerge.scale (195955200 : Int) atom0624Coded)) := by
  rw [block007_data_flat139_step, block007_data_flat137_original, block007_data_flat138_original]
def block007_data_flat140 : CoefficientMerge.Poly := [(nat_lit 2169, Int.ofNat (nat_lit 3456000))]
theorem block007_data_flat140_step : block007_data_flat140 = (CoefficientMerge.scale (3456000 : Int) atom0625Coded) := by decide +kernel
theorem block007_data_flat140_original : block007_data_flat140 = (CoefficientMerge.scale (3456000 : Int) atom0625Coded) := by
  rw [block007_data_flat140_step]
def block007_data_flat141 : CoefficientMerge.Poly := [(nat_lit 2170, Int.ofNat (nat_lit 17798400))]
theorem block007_data_flat141_step : block007_data_flat141 = (CoefficientMerge.scale (17798400 : Int) atom0626Coded) := by decide +kernel
theorem block007_data_flat141_original : block007_data_flat141 = (CoefficientMerge.scale (17798400 : Int) atom0626Coded) := by
  rw [block007_data_flat141_step]
def block007_data_flat142 : CoefficientMerge.Poly := [(nat_lit 2171, Int.ofNat (nat_lit 65173680))]
theorem block007_data_flat142_step : block007_data_flat142 = (CoefficientMerge.scale (65173680 : Int) atom0627Coded) := by decide +kernel
theorem block007_data_flat142_original : block007_data_flat142 = (CoefficientMerge.scale (65173680 : Int) atom0627Coded) := by
  rw [block007_data_flat142_step]
def block007_data_flat143 : CoefficientMerge.Poly := [(nat_lit 2170, Int.ofNat (nat_lit 17798400)), (nat_lit 2171, Int.ofNat (nat_lit 65173680))]
theorem block007_data_flat143_step : block007_data_flat143 = (CoefficientMerge.fastMerge block007_data_flat141 block007_data_flat142) := by decide +kernel
theorem block007_data_flat143_original : block007_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17798400 : Int) atom0626Coded) (CoefficientMerge.scale (65173680 : Int) atom0627Coded)) := by
  rw [block007_data_flat143_step, block007_data_flat141_original, block007_data_flat142_original]
def block007_data_flat144 : CoefficientMerge.Poly := [(nat_lit 2169, Int.ofNat (nat_lit 3456000)), (nat_lit 2170, Int.ofNat (nat_lit 17798400)), (nat_lit 2171, Int.ofNat (nat_lit 65173680))]
theorem block007_data_flat144_step : block007_data_flat144 = (CoefficientMerge.fastMerge block007_data_flat140 block007_data_flat143) := by decide +kernel
theorem block007_data_flat144_original : block007_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3456000 : Int) atom0625Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17798400 : Int) atom0626Coded) (CoefficientMerge.scale (65173680 : Int) atom0627Coded))) := by
  rw [block007_data_flat144_step, block007_data_flat140_original, block007_data_flat143_original]
def block007_data_flat145 : CoefficientMerge.Poly := [(nat_lit 2009, Int.ofNat (nat_lit 312395940)), (nat_lit 2024, Int.ofNat (nat_lit 195955200)), (nat_lit 2169, Int.ofNat (nat_lit 3456000)), (nat_lit 2170, Int.ofNat (nat_lit 17798400)), (nat_lit 2171, Int.ofNat (nat_lit 65173680))]
theorem block007_data_flat145_step : block007_data_flat145 = (CoefficientMerge.fastMerge block007_data_flat139 block007_data_flat144) := by decide +kernel
theorem block007_data_flat145_original : block007_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (312395940 : Int) atom0623Coded) (CoefficientMerge.scale (195955200 : Int) atom0624Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3456000 : Int) atom0625Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17798400 : Int) atom0626Coded) (CoefficientMerge.scale (65173680 : Int) atom0627Coded)))) := by
  rw [block007_data_flat145_step, block007_data_flat139_original, block007_data_flat144_original]
def block007_data_flat146 : CoefficientMerge.Poly := [(nat_lit 2172, Int.ofNat (nat_lit 87091200))]
theorem block007_data_flat146_step : block007_data_flat146 = (CoefficientMerge.scale (87091200 : Int) atom0628Coded) := by decide +kernel
theorem block007_data_flat146_original : block007_data_flat146 = (CoefficientMerge.scale (87091200 : Int) atom0628Coded) := by
  rw [block007_data_flat146_step]
def block007_data_flat147 : CoefficientMerge.Poly := [(nat_lit 2173, Int.ofNat (nat_lit 40089600))]
theorem block007_data_flat147_step : block007_data_flat147 = (CoefficientMerge.scale (40089600 : Int) atom0629Coded) := by decide +kernel
theorem block007_data_flat147_original : block007_data_flat147 = (CoefficientMerge.scale (40089600 : Int) atom0629Coded) := by
  rw [block007_data_flat147_step]
def block007_data_flat148 : CoefficientMerge.Poly := [(nat_lit 2172, Int.ofNat (nat_lit 87091200)), (nat_lit 2173, Int.ofNat (nat_lit 40089600))]
theorem block007_data_flat148_step : block007_data_flat148 = (CoefficientMerge.fastMerge block007_data_flat146 block007_data_flat147) := by decide +kernel
theorem block007_data_flat148_original : block007_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (87091200 : Int) atom0628Coded) (CoefficientMerge.scale (40089600 : Int) atom0629Coded)) := by
  rw [block007_data_flat148_step, block007_data_flat146_original, block007_data_flat147_original]
def block007_data_flat149 : CoefficientMerge.Poly := [(nat_lit 2174, Int.ofNat (nat_lit 101952000))]
theorem block007_data_flat149_step : block007_data_flat149 = (CoefficientMerge.scale (101952000 : Int) atom0630Coded) := by decide +kernel
theorem block007_data_flat149_original : block007_data_flat149 = (CoefficientMerge.scale (101952000 : Int) atom0630Coded) := by
  rw [block007_data_flat149_step]
def block007_data_flat150 : CoefficientMerge.Poly := [(nat_lit 2185, Int.ofNat (nat_lit 20808576))]
theorem block007_data_flat150_step : block007_data_flat150 = (CoefficientMerge.scale (20808576 : Int) atom0631Coded) := by decide +kernel
theorem block007_data_flat150_original : block007_data_flat150 = (CoefficientMerge.scale (20808576 : Int) atom0631Coded) := by
  rw [block007_data_flat150_step]
def block007_data_flat151 : CoefficientMerge.Poly := [(nat_lit 2186, Int.ofNat (nat_lit 126358920))]
theorem block007_data_flat151_step : block007_data_flat151 = (CoefficientMerge.scale (126358920 : Int) atom0632Coded) := by decide +kernel
theorem block007_data_flat151_original : block007_data_flat151 = (CoefficientMerge.scale (126358920 : Int) atom0632Coded) := by
  rw [block007_data_flat151_step]
def block007_data_flat152 : CoefficientMerge.Poly := [(nat_lit 2185, Int.ofNat (nat_lit 20808576)), (nat_lit 2186, Int.ofNat (nat_lit 126358920))]
theorem block007_data_flat152_step : block007_data_flat152 = (CoefficientMerge.fastMerge block007_data_flat150 block007_data_flat151) := by decide +kernel
theorem block007_data_flat152_original : block007_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20808576 : Int) atom0631Coded) (CoefficientMerge.scale (126358920 : Int) atom0632Coded)) := by
  rw [block007_data_flat152_step, block007_data_flat150_original, block007_data_flat151_original]
def block007_data_flat153 : CoefficientMerge.Poly := [(nat_lit 2174, Int.ofNat (nat_lit 101952000)), (nat_lit 2185, Int.ofNat (nat_lit 20808576)), (nat_lit 2186, Int.ofNat (nat_lit 126358920))]
theorem block007_data_flat153_step : block007_data_flat153 = (CoefficientMerge.fastMerge block007_data_flat149 block007_data_flat152) := by decide +kernel
theorem block007_data_flat153_original : block007_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (101952000 : Int) atom0630Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20808576 : Int) atom0631Coded) (CoefficientMerge.scale (126358920 : Int) atom0632Coded))) := by
  rw [block007_data_flat153_step, block007_data_flat149_original, block007_data_flat152_original]
def block007_data_flat154 : CoefficientMerge.Poly := [(nat_lit 2172, Int.ofNat (nat_lit 87091200)), (nat_lit 2173, Int.ofNat (nat_lit 40089600)), (nat_lit 2174, Int.ofNat (nat_lit 101952000)), (nat_lit 2185, Int.ofNat (nat_lit 20808576)), (nat_lit 2186, Int.ofNat (nat_lit 126358920))]
theorem block007_data_flat154_step : block007_data_flat154 = (CoefficientMerge.fastMerge block007_data_flat148 block007_data_flat153) := by decide +kernel
theorem block007_data_flat154_original : block007_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87091200 : Int) atom0628Coded) (CoefficientMerge.scale (40089600 : Int) atom0629Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101952000 : Int) atom0630Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20808576 : Int) atom0631Coded) (CoefficientMerge.scale (126358920 : Int) atom0632Coded)))) := by
  rw [block007_data_flat154_step, block007_data_flat148_original, block007_data_flat153_original]
def block007_data_flat155 : CoefficientMerge.Poly := [(nat_lit 2009, Int.ofNat (nat_lit 312395940)), (nat_lit 2024, Int.ofNat (nat_lit 195955200)), (nat_lit 2169, Int.ofNat (nat_lit 3456000)), (nat_lit 2170, Int.ofNat (nat_lit 17798400)), (nat_lit 2171, Int.ofNat (nat_lit 65173680)), (nat_lit 2172, Int.ofNat (nat_lit 87091200)), (nat_lit 2173, Int.ofNat (nat_lit 40089600)), (nat_lit 2174, Int.ofNat (nat_lit 101952000)), (nat_lit 2185, Int.ofNat (nat_lit 20808576)), (nat_lit 2186, Int.ofNat (nat_lit 126358920))]
theorem block007_data_flat155_step : block007_data_flat155 = (CoefficientMerge.fastMerge block007_data_flat145 block007_data_flat154) := by decide +kernel
theorem block007_data_flat155_original : block007_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (312395940 : Int) atom0623Coded) (CoefficientMerge.scale (195955200 : Int) atom0624Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3456000 : Int) atom0625Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17798400 : Int) atom0626Coded) (CoefficientMerge.scale (65173680 : Int) atom0627Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87091200 : Int) atom0628Coded) (CoefficientMerge.scale (40089600 : Int) atom0629Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101952000 : Int) atom0630Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20808576 : Int) atom0631Coded) (CoefficientMerge.scale (126358920 : Int) atom0632Coded))))) := by
  rw [block007_data_flat155_step, block007_data_flat145_original, block007_data_flat154_original]
def block007_data_flat156 : CoefficientMerge.Poly := [(nat_lit 1963, Int.ofNat (nat_lit 123366240)), (nat_lit 1964, Int.ofNat (nat_lit 193957740)), (nat_lit 1976, Int.ofNat (nat_lit 77957640)), (nat_lit 1977, Int.ofNat (nat_lit 179823240)), (nat_lit 1978, Int.ofNat (nat_lit 185492160)), (nat_lit 1979, Int.ofNat (nat_lit 273069360)), (nat_lit 1992, Int.ofNat (nat_lit 84758400)), (nat_lit 1993, Int.ofNat (nat_lit 204013080)), (nat_lit 1994, Int.ofNat (nat_lit 304197120)), (nat_lit 2008, Int.ofNat (nat_lit 100271520)), (nat_lit 2009, Int.ofNat (nat_lit 312395940)), (nat_lit 2024, Int.ofNat (nat_lit 195955200)), (nat_lit 2169, Int.ofNat (nat_lit 3456000)), (nat_lit 2170, Int.ofNat (nat_lit 17798400)), (nat_lit 2171, Int.ofNat (nat_lit 65173680)), (nat_lit 2172, Int.ofNat (nat_lit 87091200)), (nat_lit 2173, Int.ofNat (nat_lit 40089600)), (nat_lit 2174, Int.ofNat (nat_lit 101952000)), (nat_lit 2185, Int.ofNat (nat_lit 20808576)), (nat_lit 2186, Int.ofNat (nat_lit 126358920))]
theorem block007_data_flat156_step : block007_data_flat156 = (CoefficientMerge.fastMerge block007_data_flat136 block007_data_flat155) := by decide +kernel
theorem block007_data_flat156_original : block007_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (123366240 : Int) atom0613Coded) (CoefficientMerge.scale (193957740 : Int) atom0614Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77957640 : Int) atom0615Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179823240 : Int) atom0616Coded) (CoefficientMerge.scale (185492160 : Int) atom0617Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (273069360 : Int) atom0618Coded) (CoefficientMerge.scale (84758400 : Int) atom0619Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (204013080 : Int) atom0620Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (304197120 : Int) atom0621Coded) (CoefficientMerge.scale (100271520 : Int) atom0622Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (312395940 : Int) atom0623Coded) (CoefficientMerge.scale (195955200 : Int) atom0624Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3456000 : Int) atom0625Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17798400 : Int) atom0626Coded) (CoefficientMerge.scale (65173680 : Int) atom0627Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87091200 : Int) atom0628Coded) (CoefficientMerge.scale (40089600 : Int) atom0629Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101952000 : Int) atom0630Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20808576 : Int) atom0631Coded) (CoefficientMerge.scale (126358920 : Int) atom0632Coded)))))) := by
  rw [block007_data_flat156_step, block007_data_flat136_original, block007_data_flat155_original]
def block007_data_flat157 : CoefficientMerge.Poly := [(nat_lit 1753, Int.ofNat (nat_lit 163720560)), (nat_lit 1754, Int.ofNat (nat_lit 253214640)), (nat_lit 1767, Int.ofNat (nat_lit 77264640)), (nat_lit 1768, Int.ofNat (nat_lit 164422560)), (nat_lit 1769, Int.ofNat (nat_lit 270259200)), (nat_lit 1783, Int.ofNat (nat_lit 65834880)), (nat_lit 1784, Int.ofNat (nat_lit 251478000)), (nat_lit 1799, Int.ofNat (nat_lit 174182400)), (nat_lit 1931, Int.ofNat (nat_lit 3436560)), (nat_lit 1932, Int.ofNat (nat_lit 8981280)), (nat_lit 1934, Int.ofNat (nat_lit 30443040)), (nat_lit 1944, Int.ofNat (nat_lit 3985200)), (nat_lit 1945, Int.ofNat (nat_lit 14832720)), (nat_lit 1946, Int.ofNat (nat_lit 87102000)), (nat_lit 1947, Int.ofNat (nat_lit 121237560)), (nat_lit 1948, Int.ofNat (nat_lit 75718800)), (nat_lit 1949, Int.ofNat (nat_lit 187377300)), (nat_lit 1960, Int.ofNat (nat_lit 5940864)), (nat_lit 1961, Int.ofNat (nat_lit 74322360)), (nat_lit 1962, Int.ofNat (nat_lit 136925640)), (nat_lit 1963, Int.ofNat (nat_lit 123366240)), (nat_lit 1964, Int.ofNat (nat_lit 193957740)), (nat_lit 1976, Int.ofNat (nat_lit 77957640)), (nat_lit 1977, Int.ofNat (nat_lit 179823240)), (nat_lit 1978, Int.ofNat (nat_lit 185492160)), (nat_lit 1979, Int.ofNat (nat_lit 273069360)), (nat_lit 1992, Int.ofNat (nat_lit 84758400)), (nat_lit 1993, Int.ofNat (nat_lit 204013080)), (nat_lit 1994, Int.ofNat (nat_lit 304197120)), (nat_lit 2008, Int.ofNat (nat_lit 100271520)), (nat_lit 2009, Int.ofNat (nat_lit 312395940)), (nat_lit 2024, Int.ofNat (nat_lit 195955200)), (nat_lit 2169, Int.ofNat (nat_lit 3456000)), (nat_lit 2170, Int.ofNat (nat_lit 17798400)), (nat_lit 2171, Int.ofNat (nat_lit 65173680)), (nat_lit 2172, Int.ofNat (nat_lit 87091200)), (nat_lit 2173, Int.ofNat (nat_lit 40089600)), (nat_lit 2174, Int.ofNat (nat_lit 101952000)), (nat_lit 2185, Int.ofNat (nat_lit 20808576)), (nat_lit 2186, Int.ofNat (nat_lit 126358920))]
theorem block007_data_flat157_step : block007_data_flat157 = (CoefficientMerge.fastMerge block007_data_flat117 block007_data_flat156) := by decide +kernel
theorem block007_data_flat157_original : block007_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (163720560 : Int) atom0593Coded) (CoefficientMerge.scale (253214640 : Int) atom0594Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77264640 : Int) atom0595Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164422560 : Int) atom0596Coded) (CoefficientMerge.scale (270259200 : Int) atom0597Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65834880 : Int) atom0598Coded) (CoefficientMerge.scale (251478000 : Int) atom0599Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174182400 : Int) atom0600Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3436560 : Int) atom0601Coded) (CoefficientMerge.scale (8981280 : Int) atom0602Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30443040 : Int) atom0603Coded) (CoefficientMerge.scale (3985200 : Int) atom0604Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14832720 : Int) atom0605Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87102000 : Int) atom0606Coded) (CoefficientMerge.scale (121237560 : Int) atom0607Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75718800 : Int) atom0608Coded) (CoefficientMerge.scale (187377300 : Int) atom0609Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5940864 : Int) atom0610Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74322360 : Int) atom0611Coded) (CoefficientMerge.scale (136925640 : Int) atom0612Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (123366240 : Int) atom0613Coded) (CoefficientMerge.scale (193957740 : Int) atom0614Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77957640 : Int) atom0615Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179823240 : Int) atom0616Coded) (CoefficientMerge.scale (185492160 : Int) atom0617Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (273069360 : Int) atom0618Coded) (CoefficientMerge.scale (84758400 : Int) atom0619Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (204013080 : Int) atom0620Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (304197120 : Int) atom0621Coded) (CoefficientMerge.scale (100271520 : Int) atom0622Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (312395940 : Int) atom0623Coded) (CoefficientMerge.scale (195955200 : Int) atom0624Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3456000 : Int) atom0625Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17798400 : Int) atom0626Coded) (CoefficientMerge.scale (65173680 : Int) atom0627Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87091200 : Int) atom0628Coded) (CoefficientMerge.scale (40089600 : Int) atom0629Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101952000 : Int) atom0630Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20808576 : Int) atom0631Coded) (CoefficientMerge.scale (126358920 : Int) atom0632Coded))))))) := by
  rw [block007_data_flat157_step, block007_data_flat117_original, block007_data_flat156_original]
def block007_data_flat158 : CoefficientMerge.Poly := [(nat_lit 1495, Int.ofNat (nat_lit 60699240)), (nat_lit 1496, Int.ofNat (nat_lit 126096480)), (nat_lit 1497, Int.ofNat (nat_lit 156091320)), (nat_lit 1498, Int.ofNat (nat_lit 110217240)), (nat_lit 1499, Int.ofNat (nat_lit 200423160)), (nat_lit 1510, Int.ofNat (nat_lit 26469504)), (nat_lit 1511, Int.ofNat (nat_lit 100582560)), (nat_lit 1512, Int.ofNat (nat_lit 147665700)), (nat_lit 1513, Int.ofNat (nat_lit 118586160)), (nat_lit 1514, Int.ofNat (nat_lit 173295990)), (nat_lit 1526, Int.ofNat (nat_lit 86044680)), (nat_lit 1527, Int.ofNat (nat_lit 170421840)), (nat_lit 1528, Int.ofNat (nat_lit 146729880)), (nat_lit 1529, Int.ofNat (nat_lit 224658360)), (nat_lit 1542, Int.ofNat (nat_lit 67597740)), (nat_lit 1543, Int.ofNat (nat_lit 129105900)), (nat_lit 1544, Int.ofNat (nat_lit 220009230)), (nat_lit 1558, Int.ofNat (nat_lit 40960080)), (nat_lit 1559, Int.ofNat (nat_lit 183914010)), (nat_lit 1574, Int.ofNat (nat_lit 132831090)), (nat_lit 1687, Int.ofNat (nat_lit 13440)), (nat_lit 1703, Int.ofNat (nat_lit 2284800)), (nat_lit 1705, Int.ofNat (nat_lit 509120)), (nat_lit 1706, Int.ofNat (nat_lit 11378240)), (nat_lit 1707, Int.ofNat (nat_lit 26440640)), (nat_lit 1708, Int.ofNat (nat_lit 33900480)), (nat_lit 1709, Int.ofNat (nat_lit 83671920)), (nat_lit 1719, Int.ofNat (nat_lit 14717760)), (nat_lit 1720, Int.ofNat (nat_lit 37833600)), (nat_lit 1721, Int.ofNat (nat_lit 108389280)), (nat_lit 1722, Int.ofNat (nat_lit 140625120)), (nat_lit 1723, Int.ofNat (nat_lit 98938560)), (nat_lit 1724, Int.ofNat (nat_lit 193577040)), (nat_lit 1735, Int.ofNat (nat_lit 16205184)), (nat_lit 1736, Int.ofNat (nat_lit 87384840)), (nat_lit 1737, Int.ofNat (nat_lit 142194240)), (nat_lit 1738, Int.ofNat (nat_lit 120840960)), (nat_lit 1739, Int.ofNat (nat_lit 183474720)), (nat_lit 1751, Int.ofNat (nat_lit 82001160)), (nat_lit 1752, Int.ofNat (nat_lit 175846920)), (nat_lit 1753, Int.ofNat (nat_lit 163720560)), (nat_lit 1754, Int.ofNat (nat_lit 253214640)), (nat_lit 1767, Int.ofNat (nat_lit 77264640)), (nat_lit 1768, Int.ofNat (nat_lit 164422560)), (nat_lit 1769, Int.ofNat (nat_lit 270259200)), (nat_lit 1783, Int.ofNat (nat_lit 65834880)), (nat_lit 1784, Int.ofNat (nat_lit 251478000)), (nat_lit 1799, Int.ofNat (nat_lit 174182400)), (nat_lit 1931, Int.ofNat (nat_lit 3436560)), (nat_lit 1932, Int.ofNat (nat_lit 8981280)), (nat_lit 1934, Int.ofNat (nat_lit 30443040)), (nat_lit 1944, Int.ofNat (nat_lit 3985200)), (nat_lit 1945, Int.ofNat (nat_lit 14832720)), (nat_lit 1946, Int.ofNat (nat_lit 87102000)), (nat_lit 1947, Int.ofNat (nat_lit 121237560)), (nat_lit 1948, Int.ofNat (nat_lit 75718800)), (nat_lit 1949, Int.ofNat (nat_lit 187377300)), (nat_lit 1960, Int.ofNat (nat_lit 5940864)), (nat_lit 1961, Int.ofNat (nat_lit 74322360)), (nat_lit 1962, Int.ofNat (nat_lit 136925640)), (nat_lit 1963, Int.ofNat (nat_lit 123366240)), (nat_lit 1964, Int.ofNat (nat_lit 193957740)), (nat_lit 1976, Int.ofNat (nat_lit 77957640)), (nat_lit 1977, Int.ofNat (nat_lit 179823240)), (nat_lit 1978, Int.ofNat (nat_lit 185492160)), (nat_lit 1979, Int.ofNat (nat_lit 273069360)), (nat_lit 1992, Int.ofNat (nat_lit 84758400)), (nat_lit 1993, Int.ofNat (nat_lit 204013080)), (nat_lit 1994, Int.ofNat (nat_lit 304197120)), (nat_lit 2008, Int.ofNat (nat_lit 100271520)), (nat_lit 2009, Int.ofNat (nat_lit 312395940)), (nat_lit 2024, Int.ofNat (nat_lit 195955200)), (nat_lit 2169, Int.ofNat (nat_lit 3456000)), (nat_lit 2170, Int.ofNat (nat_lit 17798400)), (nat_lit 2171, Int.ofNat (nat_lit 65173680)), (nat_lit 2172, Int.ofNat (nat_lit 87091200)), (nat_lit 2173, Int.ofNat (nat_lit 40089600)), (nat_lit 2174, Int.ofNat (nat_lit 101952000)), (nat_lit 2185, Int.ofNat (nat_lit 20808576)), (nat_lit 2186, Int.ofNat (nat_lit 126358920))]
theorem block007_data_flat158_step : block007_data_flat158 = (CoefficientMerge.fastMerge block007_data_flat078 block007_data_flat157) := by decide +kernel
theorem block007_data_flat158_original : block007_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60699240 : Int) atom0553Coded) (CoefficientMerge.scale (126096480 : Int) atom0554Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156091320 : Int) atom0555Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110217240 : Int) atom0556Coded) (CoefficientMerge.scale (200423160 : Int) atom0557Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26469504 : Int) atom0558Coded) (CoefficientMerge.scale (100582560 : Int) atom0559Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (147665700 : Int) atom0560Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118586160 : Int) atom0561Coded) (CoefficientMerge.scale (173295990 : Int) atom0562Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (86044680 : Int) atom0563Coded) (CoefficientMerge.scale (170421840 : Int) atom0564Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (146729880 : Int) atom0565Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (224658360 : Int) atom0566Coded) (CoefficientMerge.scale (67597740 : Int) atom0567Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129105900 : Int) atom0568Coded) (CoefficientMerge.scale (220009230 : Int) atom0569Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40960080 : Int) atom0570Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183914010 : Int) atom0571Coded) (CoefficientMerge.scale (132831090 : Int) atom0572Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13440 : Int) atom0573Coded) (CoefficientMerge.scale (2284800 : Int) atom0574Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (509120 : Int) atom0575Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11378240 : Int) atom0576Coded) (CoefficientMerge.scale (26440640 : Int) atom0577Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33900480 : Int) atom0578Coded) (CoefficientMerge.scale (83671920 : Int) atom0579Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14717760 : Int) atom0580Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37833600 : Int) atom0581Coded) (CoefficientMerge.scale (108389280 : Int) atom0582Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (140625120 : Int) atom0583Coded) (CoefficientMerge.scale (98938560 : Int) atom0584Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193577040 : Int) atom0585Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16205184 : Int) atom0586Coded) (CoefficientMerge.scale (87384840 : Int) atom0587Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142194240 : Int) atom0588Coded) (CoefficientMerge.scale (120840960 : Int) atom0589Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183474720 : Int) atom0590Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82001160 : Int) atom0591Coded) (CoefficientMerge.scale (175846920 : Int) atom0592Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (163720560 : Int) atom0593Coded) (CoefficientMerge.scale (253214640 : Int) atom0594Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77264640 : Int) atom0595Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164422560 : Int) atom0596Coded) (CoefficientMerge.scale (270259200 : Int) atom0597Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65834880 : Int) atom0598Coded) (CoefficientMerge.scale (251478000 : Int) atom0599Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174182400 : Int) atom0600Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3436560 : Int) atom0601Coded) (CoefficientMerge.scale (8981280 : Int) atom0602Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30443040 : Int) atom0603Coded) (CoefficientMerge.scale (3985200 : Int) atom0604Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14832720 : Int) atom0605Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87102000 : Int) atom0606Coded) (CoefficientMerge.scale (121237560 : Int) atom0607Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75718800 : Int) atom0608Coded) (CoefficientMerge.scale (187377300 : Int) atom0609Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5940864 : Int) atom0610Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74322360 : Int) atom0611Coded) (CoefficientMerge.scale (136925640 : Int) atom0612Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (123366240 : Int) atom0613Coded) (CoefficientMerge.scale (193957740 : Int) atom0614Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77957640 : Int) atom0615Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179823240 : Int) atom0616Coded) (CoefficientMerge.scale (185492160 : Int) atom0617Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (273069360 : Int) atom0618Coded) (CoefficientMerge.scale (84758400 : Int) atom0619Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (204013080 : Int) atom0620Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (304197120 : Int) atom0621Coded) (CoefficientMerge.scale (100271520 : Int) atom0622Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (312395940 : Int) atom0623Coded) (CoefficientMerge.scale (195955200 : Int) atom0624Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3456000 : Int) atom0625Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17798400 : Int) atom0626Coded) (CoefficientMerge.scale (65173680 : Int) atom0627Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87091200 : Int) atom0628Coded) (CoefficientMerge.scale (40089600 : Int) atom0629Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101952000 : Int) atom0630Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20808576 : Int) atom0631Coded) (CoefficientMerge.scale (126358920 : Int) atom0632Coded)))))))) := by
  rw [block007_data_flat158_step, block007_data_flat078_original, block007_data_flat157_original]
def block007_data_flat159 : CoefficientMerge.Poly := [(nat_lit 1495, Int.ofNat (nat_lit 60699240)), (nat_lit 1496, Int.ofNat (nat_lit 126096480)), (nat_lit 1497, Int.ofNat (nat_lit 156091320)), (nat_lit 1498, Int.ofNat (nat_lit 110217240)), (nat_lit 1499, Int.ofNat (nat_lit 200423160)), (nat_lit 1510, Int.ofNat (nat_lit 26469504)), (nat_lit 1511, Int.ofNat (nat_lit 100582560)), (nat_lit 1512, Int.ofNat (nat_lit 147665700)), (nat_lit 1513, Int.ofNat (nat_lit 118586160)), (nat_lit 1514, Int.ofNat (nat_lit 173295990)), (nat_lit 1526, Int.ofNat (nat_lit 86044680)), (nat_lit 1527, Int.ofNat (nat_lit 170421840)), (nat_lit 1528, Int.ofNat (nat_lit 146729880)), (nat_lit 1529, Int.ofNat (nat_lit 224658360)), (nat_lit 1542, Int.ofNat (nat_lit 67597740)), (nat_lit 1543, Int.ofNat (nat_lit 129105900)), (nat_lit 1544, Int.ofNat (nat_lit 220009230)), (nat_lit 1558, Int.ofNat (nat_lit 40960080)), (nat_lit 1559, Int.ofNat (nat_lit 183914010)), (nat_lit 1574, Int.ofNat (nat_lit 132831090)), (nat_lit 1687, Int.ofNat (nat_lit 13440)), (nat_lit 1703, Int.ofNat (nat_lit 2284800)), (nat_lit 1705, Int.ofNat (nat_lit 509120)), (nat_lit 1706, Int.ofNat (nat_lit 11378240)), (nat_lit 1707, Int.ofNat (nat_lit 26440640)), (nat_lit 1708, Int.ofNat (nat_lit 33900480)), (nat_lit 1709, Int.ofNat (nat_lit 83671920)), (nat_lit 1719, Int.ofNat (nat_lit 14717760)), (nat_lit 1720, Int.ofNat (nat_lit 37833600)), (nat_lit 1721, Int.ofNat (nat_lit 108389280)), (nat_lit 1722, Int.ofNat (nat_lit 140625120)), (nat_lit 1723, Int.ofNat (nat_lit 98938560)), (nat_lit 1724, Int.ofNat (nat_lit 193577040)), (nat_lit 1735, Int.ofNat (nat_lit 16205184)), (nat_lit 1736, Int.ofNat (nat_lit 87384840)), (nat_lit 1737, Int.ofNat (nat_lit 142194240)), (nat_lit 1738, Int.ofNat (nat_lit 120840960)), (nat_lit 1739, Int.ofNat (nat_lit 183474720)), (nat_lit 1751, Int.ofNat (nat_lit 82001160)), (nat_lit 1752, Int.ofNat (nat_lit 175846920)), (nat_lit 1753, Int.ofNat (nat_lit 163720560)), (nat_lit 1754, Int.ofNat (nat_lit 253214640)), (nat_lit 1767, Int.ofNat (nat_lit 77264640)), (nat_lit 1768, Int.ofNat (nat_lit 164422560)), (nat_lit 1769, Int.ofNat (nat_lit 270259200)), (nat_lit 1783, Int.ofNat (nat_lit 65834880)), (nat_lit 1784, Int.ofNat (nat_lit 251478000)), (nat_lit 1799, Int.ofNat (nat_lit 174182400)), (nat_lit 1931, Int.ofNat (nat_lit 3436560)), (nat_lit 1932, Int.ofNat (nat_lit 8981280)), (nat_lit 1934, Int.ofNat (nat_lit 30443040)), (nat_lit 1944, Int.ofNat (nat_lit 3985200)), (nat_lit 1945, Int.ofNat (nat_lit 14832720)), (nat_lit 1946, Int.ofNat (nat_lit 87102000)), (nat_lit 1947, Int.ofNat (nat_lit 121237560)), (nat_lit 1948, Int.ofNat (nat_lit 75718800)), (nat_lit 1949, Int.ofNat (nat_lit 187377300)), (nat_lit 1960, Int.ofNat (nat_lit 5940864)), (nat_lit 1961, Int.ofNat (nat_lit 74322360)), (nat_lit 1962, Int.ofNat (nat_lit 136925640)), (nat_lit 1963, Int.ofNat (nat_lit 123366240)), (nat_lit 1964, Int.ofNat (nat_lit 193957740)), (nat_lit 1976, Int.ofNat (nat_lit 77957640)), (nat_lit 1977, Int.ofNat (nat_lit 179823240)), (nat_lit 1978, Int.ofNat (nat_lit 185492160)), (nat_lit 1979, Int.ofNat (nat_lit 273069360)), (nat_lit 1992, Int.ofNat (nat_lit 84758400)), (nat_lit 1993, Int.ofNat (nat_lit 204013080)), (nat_lit 1994, Int.ofNat (nat_lit 304197120)), (nat_lit 2008, Int.ofNat (nat_lit 100271520)), (nat_lit 2009, Int.ofNat (nat_lit 312395940)), (nat_lit 2024, Int.ofNat (nat_lit 195955200)), (nat_lit 2169, Int.ofNat (nat_lit 3456000)), (nat_lit 2170, Int.ofNat (nat_lit 17798400)), (nat_lit 2171, Int.ofNat (nat_lit 65173680)), (nat_lit 2172, Int.ofNat (nat_lit 87091200)), (nat_lit 2173, Int.ofNat (nat_lit 40089600)), (nat_lit 2174, Int.ofNat (nat_lit 101952000)), (nat_lit 2185, Int.ofNat (nat_lit 20808576)), (nat_lit 2186, Int.ofNat (nat_lit 126358920))]
theorem block007_data_flat159_step : block007_data_flat159 = (CoefficientMerge.trim block007_data_flat158) := by decide +kernel
theorem block007_data_flat159_original : block007_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60699240 : Int) atom0553Coded) (CoefficientMerge.scale (126096480 : Int) atom0554Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156091320 : Int) atom0555Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110217240 : Int) atom0556Coded) (CoefficientMerge.scale (200423160 : Int) atom0557Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26469504 : Int) atom0558Coded) (CoefficientMerge.scale (100582560 : Int) atom0559Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (147665700 : Int) atom0560Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118586160 : Int) atom0561Coded) (CoefficientMerge.scale (173295990 : Int) atom0562Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (86044680 : Int) atom0563Coded) (CoefficientMerge.scale (170421840 : Int) atom0564Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (146729880 : Int) atom0565Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (224658360 : Int) atom0566Coded) (CoefficientMerge.scale (67597740 : Int) atom0567Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129105900 : Int) atom0568Coded) (CoefficientMerge.scale (220009230 : Int) atom0569Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40960080 : Int) atom0570Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183914010 : Int) atom0571Coded) (CoefficientMerge.scale (132831090 : Int) atom0572Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13440 : Int) atom0573Coded) (CoefficientMerge.scale (2284800 : Int) atom0574Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (509120 : Int) atom0575Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11378240 : Int) atom0576Coded) (CoefficientMerge.scale (26440640 : Int) atom0577Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33900480 : Int) atom0578Coded) (CoefficientMerge.scale (83671920 : Int) atom0579Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14717760 : Int) atom0580Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37833600 : Int) atom0581Coded) (CoefficientMerge.scale (108389280 : Int) atom0582Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (140625120 : Int) atom0583Coded) (CoefficientMerge.scale (98938560 : Int) atom0584Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193577040 : Int) atom0585Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16205184 : Int) atom0586Coded) (CoefficientMerge.scale (87384840 : Int) atom0587Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142194240 : Int) atom0588Coded) (CoefficientMerge.scale (120840960 : Int) atom0589Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183474720 : Int) atom0590Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82001160 : Int) atom0591Coded) (CoefficientMerge.scale (175846920 : Int) atom0592Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (163720560 : Int) atom0593Coded) (CoefficientMerge.scale (253214640 : Int) atom0594Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77264640 : Int) atom0595Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164422560 : Int) atom0596Coded) (CoefficientMerge.scale (270259200 : Int) atom0597Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65834880 : Int) atom0598Coded) (CoefficientMerge.scale (251478000 : Int) atom0599Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174182400 : Int) atom0600Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3436560 : Int) atom0601Coded) (CoefficientMerge.scale (8981280 : Int) atom0602Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30443040 : Int) atom0603Coded) (CoefficientMerge.scale (3985200 : Int) atom0604Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14832720 : Int) atom0605Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87102000 : Int) atom0606Coded) (CoefficientMerge.scale (121237560 : Int) atom0607Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75718800 : Int) atom0608Coded) (CoefficientMerge.scale (187377300 : Int) atom0609Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5940864 : Int) atom0610Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74322360 : Int) atom0611Coded) (CoefficientMerge.scale (136925640 : Int) atom0612Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (123366240 : Int) atom0613Coded) (CoefficientMerge.scale (193957740 : Int) atom0614Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77957640 : Int) atom0615Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179823240 : Int) atom0616Coded) (CoefficientMerge.scale (185492160 : Int) atom0617Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (273069360 : Int) atom0618Coded) (CoefficientMerge.scale (84758400 : Int) atom0619Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (204013080 : Int) atom0620Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (304197120 : Int) atom0621Coded) (CoefficientMerge.scale (100271520 : Int) atom0622Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (312395940 : Int) atom0623Coded) (CoefficientMerge.scale (195955200 : Int) atom0624Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3456000 : Int) atom0625Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17798400 : Int) atom0626Coded) (CoefficientMerge.scale (65173680 : Int) atom0627Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87091200 : Int) atom0628Coded) (CoefficientMerge.scale (40089600 : Int) atom0629Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101952000 : Int) atom0630Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20808576 : Int) atom0631Coded) (CoefficientMerge.scale (126358920 : Int) atom0632Coded))))))))) := by
  rw [block007_data_flat159_step, block007_data_flat158_original]
theorem block007_data : block007 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60699240 : Int) atom0553Coded) (CoefficientMerge.scale (126096480 : Int) atom0554Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (156091320 : Int) atom0555Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (110217240 : Int) atom0556Coded) (CoefficientMerge.scale (200423160 : Int) atom0557Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (26469504 : Int) atom0558Coded) (CoefficientMerge.scale (100582560 : Int) atom0559Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (147665700 : Int) atom0560Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (118586160 : Int) atom0561Coded) (CoefficientMerge.scale (173295990 : Int) atom0562Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (86044680 : Int) atom0563Coded) (CoefficientMerge.scale (170421840 : Int) atom0564Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (146729880 : Int) atom0565Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (224658360 : Int) atom0566Coded) (CoefficientMerge.scale (67597740 : Int) atom0567Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (129105900 : Int) atom0568Coded) (CoefficientMerge.scale (220009230 : Int) atom0569Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40960080 : Int) atom0570Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183914010 : Int) atom0571Coded) (CoefficientMerge.scale (132831090 : Int) atom0572Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13440 : Int) atom0573Coded) (CoefficientMerge.scale (2284800 : Int) atom0574Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (509120 : Int) atom0575Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11378240 : Int) atom0576Coded) (CoefficientMerge.scale (26440640 : Int) atom0577Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33900480 : Int) atom0578Coded) (CoefficientMerge.scale (83671920 : Int) atom0579Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14717760 : Int) atom0580Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37833600 : Int) atom0581Coded) (CoefficientMerge.scale (108389280 : Int) atom0582Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (140625120 : Int) atom0583Coded) (CoefficientMerge.scale (98938560 : Int) atom0584Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193577040 : Int) atom0585Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16205184 : Int) atom0586Coded) (CoefficientMerge.scale (87384840 : Int) atom0587Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (142194240 : Int) atom0588Coded) (CoefficientMerge.scale (120840960 : Int) atom0589Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (183474720 : Int) atom0590Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82001160 : Int) atom0591Coded) (CoefficientMerge.scale (175846920 : Int) atom0592Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (163720560 : Int) atom0593Coded) (CoefficientMerge.scale (253214640 : Int) atom0594Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77264640 : Int) atom0595Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (164422560 : Int) atom0596Coded) (CoefficientMerge.scale (270259200 : Int) atom0597Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65834880 : Int) atom0598Coded) (CoefficientMerge.scale (251478000 : Int) atom0599Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (174182400 : Int) atom0600Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3436560 : Int) atom0601Coded) (CoefficientMerge.scale (8981280 : Int) atom0602Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30443040 : Int) atom0603Coded) (CoefficientMerge.scale (3985200 : Int) atom0604Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14832720 : Int) atom0605Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (87102000 : Int) atom0606Coded) (CoefficientMerge.scale (121237560 : Int) atom0607Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (75718800 : Int) atom0608Coded) (CoefficientMerge.scale (187377300 : Int) atom0609Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5940864 : Int) atom0610Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74322360 : Int) atom0611Coded) (CoefficientMerge.scale (136925640 : Int) atom0612Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (123366240 : Int) atom0613Coded) (CoefficientMerge.scale (193957740 : Int) atom0614Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77957640 : Int) atom0615Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179823240 : Int) atom0616Coded) (CoefficientMerge.scale (185492160 : Int) atom0617Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (273069360 : Int) atom0618Coded) (CoefficientMerge.scale (84758400 : Int) atom0619Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (204013080 : Int) atom0620Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (304197120 : Int) atom0621Coded) (CoefficientMerge.scale (100271520 : Int) atom0622Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (312395940 : Int) atom0623Coded) (CoefficientMerge.scale (195955200 : Int) atom0624Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3456000 : Int) atom0625Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17798400 : Int) atom0626Coded) (CoefficientMerge.scale (65173680 : Int) atom0627Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (87091200 : Int) atom0628Coded) (CoefficientMerge.scale (40089600 : Int) atom0629Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101952000 : Int) atom0630Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20808576 : Int) atom0631Coded) (CoefficientMerge.scale (126358920 : Int) atom0632Coded)))))))) := by
  have h : block007 = block007_data_flat159 := by decide +kernel
  exact h.trans block007_data_flat159_original
theorem block007_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) block007 := by
  rw [block007_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0553Coded_nonneg g hg hA hB) (atom0554Coded_nonneg g hg hA hB)) (add_nonneg (atom0555Coded_nonneg g hg hA hB) (add_nonneg (atom0556Coded_nonneg g hg hA hB) (atom0557Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0558Coded_nonneg g hg hA hB) (atom0559Coded_nonneg g hg hA hB)) (add_nonneg (atom0560Coded_nonneg g hg hA hB) (add_nonneg (atom0561Coded_nonneg g hg hA hB) (atom0562Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0563Coded_nonneg g hg hA hB) (atom0564Coded_nonneg g hg hA hB)) (add_nonneg (atom0565Coded_nonneg g hg hA hB) (add_nonneg (atom0566Coded_nonneg g hg hA hB) (atom0567Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0568Coded_nonneg g hg hA hB) (atom0569Coded_nonneg g hg hA hB)) (add_nonneg (atom0570Coded_nonneg g hg hA hB) (add_nonneg (atom0571Coded_nonneg g hg hA hB) (atom0572Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0573Coded_nonneg g hg hA hB) (atom0574Coded_nonneg g hg hA hB)) (add_nonneg (atom0575Coded_nonneg g hg hA hB) (add_nonneg (atom0576Coded_nonneg g hg hA hB) (atom0577Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0578Coded_nonneg g hg hA hB) (atom0579Coded_nonneg g hg hA hB)) (add_nonneg (atom0580Coded_nonneg g hg hA hB) (add_nonneg (atom0581Coded_nonneg g hg hA hB) (atom0582Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0583Coded_nonneg g hg hA hB) (atom0584Coded_nonneg g hg hA hB)) (add_nonneg (atom0585Coded_nonneg g hg hA hB) (add_nonneg (atom0586Coded_nonneg g hg hA hB) (atom0587Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0588Coded_nonneg g hg hA hB) (atom0589Coded_nonneg g hg hA hB)) (add_nonneg (atom0590Coded_nonneg g hg hA hB) (add_nonneg (atom0591Coded_nonneg g hg hA hB) (atom0592Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0593Coded_nonneg g hg hA hB) (atom0594Coded_nonneg g hg hA hB)) (add_nonneg (atom0595Coded_nonneg g hg hA hB) (add_nonneg (atom0596Coded_nonneg g hg hA hB) (atom0597Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0598Coded_nonneg g hg hA hB) (atom0599Coded_nonneg g hg hA hB)) (add_nonneg (atom0600Coded_nonneg g hg hA hB) (add_nonneg (atom0601Coded_nonneg g hg hA hB) (atom0602Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0603Coded_nonneg g hg hA hB) (atom0604Coded_nonneg g hg hA hB)) (add_nonneg (atom0605Coded_nonneg g hg hA hB) (add_nonneg (atom0606Coded_nonneg g hg hA hB) (atom0607Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0608Coded_nonneg g hg hA hB) (atom0609Coded_nonneg g hg hA hB)) (add_nonneg (atom0610Coded_nonneg g hg hA hB) (add_nonneg (atom0611Coded_nonneg g hg hA hB) (atom0612Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0613Coded_nonneg g hg hA hB) (atom0614Coded_nonneg g hg hA hB)) (add_nonneg (atom0615Coded_nonneg g hg hA hB) (add_nonneg (atom0616Coded_nonneg g hg hA hB) (atom0617Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0618Coded_nonneg g hg hA hB) (atom0619Coded_nonneg g hg hA hB)) (add_nonneg (atom0620Coded_nonneg g hg hA hB) (add_nonneg (atom0621Coded_nonneg g hg hA hB) (atom0622Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0623Coded_nonneg g hg hA hB) (atom0624Coded_nonneg g hg hA hB)) (add_nonneg (atom0625Coded_nonneg g hg hA hB) (add_nonneg (atom0626Coded_nonneg g hg hA hB) (atom0627Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0628Coded_nonneg g hg hA hB) (atom0629Coded_nonneg g hg hA hB)) (add_nonneg (atom0630Coded_nonneg g hg hA hB) (add_nonneg (atom0631Coded_nonneg g hg hA hB) (atom0632Coded_nonneg g hg hA hB))))))))

end APPT.Finite15
