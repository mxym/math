-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0495 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0495 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0495 = ((g 2) * (g 8) * (g 8)) := by
  norm_num [atom0495, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0495_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3718671360 : Int) atom0495) := by
  rw [SparsePolynomial.eval_scale, eval_atom0495]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0495Coded : CoefficientMerge.Poly := [(nat_lit 800, Int.ofNat (nat_lit 1))]
theorem atom0495Coded_decode : atom0495 = SparsePolynomial.decodeCubic 18 atom0495Coded := by decide +kernel
theorem atom0495Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3718671360 : Int) atom0495Coded) := by
  have h := atom0495_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0495Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0496 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0496 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0496 = ((g 2) * (g 8) * (g 9)) := by
  norm_num [atom0496, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0496_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6793720320 : Int) atom0496) := by
  rw [SparsePolynomial.eval_scale, eval_atom0496]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0496Coded : CoefficientMerge.Poly := [(nat_lit 801, Int.ofNat (nat_lit 1))]
theorem atom0496Coded_decode : atom0496 = SparsePolynomial.decodeCubic 18 atom0496Coded := by decide +kernel
theorem atom0496Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6793720320 : Int) atom0496Coded) := by
  have h := atom0496_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0496Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0497 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0497 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0497 = ((g 2) * (g 8) * (g 10)) := by
  norm_num [atom0497, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0497_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6517608960 : Int) atom0497) := by
  rw [SparsePolynomial.eval_scale, eval_atom0497]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0497Coded : CoefficientMerge.Poly := [(nat_lit 802, Int.ofNat (nat_lit 1))]
theorem atom0497Coded_decode : atom0497 = SparsePolynomial.decodeCubic 18 atom0497Coded := by decide +kernel
theorem atom0497Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6517608960 : Int) atom0497Coded) := by
  have h := atom0497_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0497Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0498 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0498 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0498 = ((g 2) * (g 8) * (g 11)) := by
  norm_num [atom0498, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0498_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6167040000 : Int) atom0498) := by
  rw [SparsePolynomial.eval_scale, eval_atom0498]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0498Coded : CoefficientMerge.Poly := [(nat_lit 803, Int.ofNat (nat_lit 1))]
theorem atom0498Coded_decode : atom0498 = SparsePolynomial.decodeCubic 18 atom0498Coded := by decide +kernel
theorem atom0498Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6167040000 : Int) atom0498Coded) := by
  have h := atom0498_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0498Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0499 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0499 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0499 = ((g 2) * (g 8) * (g 12)) := by
  norm_num [atom0499, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0499_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7979381760 : Int) atom0499) := by
  rw [SparsePolynomial.eval_scale, eval_atom0499]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0499Coded : CoefficientMerge.Poly := [(nat_lit 804, Int.ofNat (nat_lit 1))]
theorem atom0499Coded_decode : atom0499 = SparsePolynomial.decodeCubic 18 atom0499Coded := by decide +kernel
theorem atom0499Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7979381760 : Int) atom0499Coded) := by
  have h := atom0499_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0499Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0500 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0500 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0500 = ((g 2) * (g 8) * (g 13)) := by
  norm_num [atom0500, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0500_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6566323200 : Int) atom0500) := by
  rw [SparsePolynomial.eval_scale, eval_atom0500]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0500Coded : CoefficientMerge.Poly := [(nat_lit 805, Int.ofNat (nat_lit 1))]
theorem atom0500Coded_decode : atom0500 = SparsePolynomial.decodeCubic 18 atom0500Coded := by decide +kernel
theorem atom0500Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6566323200 : Int) atom0500Coded) := by
  have h := atom0500_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0500Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0501 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0501 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0501 = ((g 2) * (g 8) * (g 14)) := by
  norm_num [atom0501, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0501_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8933124000 : Int) atom0501) := by
  rw [SparsePolynomial.eval_scale, eval_atom0501]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0501Coded : CoefficientMerge.Poly := [(nat_lit 806, Int.ofNat (nat_lit 1))]
theorem atom0501Coded_decode : atom0501 = SparsePolynomial.decodeCubic 18 atom0501Coded := by decide +kernel
theorem atom0501Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8933124000 : Int) atom0501Coded) := by
  have h := atom0501_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0501Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0502 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0502 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0502 = ((g 2) * (g 8) * (g 15)) := by
  norm_num [atom0502, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0502_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7949368320 : Int) atom0502) := by
  rw [SparsePolynomial.eval_scale, eval_atom0502]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0502Coded : CoefficientMerge.Poly := [(nat_lit 807, Int.ofNat (nat_lit 1))]
theorem atom0502Coded_decode : atom0502 = SparsePolynomial.decodeCubic 18 atom0502Coded := by decide +kernel
theorem atom0502Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7949368320 : Int) atom0502Coded) := by
  have h := atom0502_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0502Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0503 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0503 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0503 = ((g 2) * (g 8) * (g 16)) := by
  norm_num [atom0503, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0503_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8692055040 : Int) atom0503) := by
  rw [SparsePolynomial.eval_scale, eval_atom0503]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0503Coded : CoefficientMerge.Poly := [(nat_lit 808, Int.ofNat (nat_lit 1))]
theorem atom0503Coded_decode : atom0503 = SparsePolynomial.decodeCubic 18 atom0503Coded := by decide +kernel
theorem atom0503Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8692055040 : Int) atom0503Coded) := by
  have h := atom0503_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0503Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0504 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0504 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0504 = ((g 2) * (g 8) * (g 17)) := by
  norm_num [atom0504, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0504_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10609182720 : Int) atom0504) := by
  rw [SparsePolynomial.eval_scale, eval_atom0504]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0504Coded : CoefficientMerge.Poly := [(nat_lit 809, Int.ofNat (nat_lit 1))]
theorem atom0504Coded_decode : atom0504 = SparsePolynomial.decodeCubic 18 atom0504Coded := by decide +kernel
theorem atom0504Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10609182720 : Int) atom0504Coded) := by
  have h := atom0504_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0504Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0505 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0505 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0505 = ((g 2) * (g 9) * (g 9)) := by
  norm_num [atom0505, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0505_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4164011520 : Int) atom0505) := by
  rw [SparsePolynomial.eval_scale, eval_atom0505]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0505Coded : CoefficientMerge.Poly := [(nat_lit 819, Int.ofNat (nat_lit 1))]
theorem atom0505Coded_decode : atom0505 = SparsePolynomial.decodeCubic 18 atom0505Coded := by decide +kernel
theorem atom0505Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4164011520 : Int) atom0505Coded) := by
  have h := atom0505_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0505Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0506 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0506 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0506 = ((g 2) * (g 9) * (g 10)) := by
  norm_num [atom0506, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0506_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7503144960 : Int) atom0506) := by
  rw [SparsePolynomial.eval_scale, eval_atom0506]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0506Coded : CoefficientMerge.Poly := [(nat_lit 820, Int.ofNat (nat_lit 1))]
theorem atom0506Coded_decode : atom0506 = SparsePolynomial.decodeCubic 18 atom0506Coded := by decide +kernel
theorem atom0506Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7503144960 : Int) atom0506Coded) := by
  have h := atom0506_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0506Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0507 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0507 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0507 = ((g 2) * (g 9) * (g 11)) := by
  norm_num [atom0507, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0507_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6954524160 : Int) atom0507) := by
  rw [SparsePolynomial.eval_scale, eval_atom0507]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0507Coded : CoefficientMerge.Poly := [(nat_lit 821, Int.ofNat (nat_lit 1))]
theorem atom0507Coded_decode : atom0507 = SparsePolynomial.decodeCubic 18 atom0507Coded := by decide +kernel
theorem atom0507Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6954524160 : Int) atom0507Coded) := by
  have h := atom0507_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0507Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0508 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0508 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0508 = ((g 2) * (g 9) * (g 12)) := by
  norm_num [atom0508, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0508_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8592628800 : Int) atom0508) := by
  rw [SparsePolynomial.eval_scale, eval_atom0508]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0508Coded : CoefficientMerge.Poly := [(nat_lit 822, Int.ofNat (nat_lit 1))]
theorem atom0508Coded_decode : atom0508 = SparsePolynomial.decodeCubic 18 atom0508Coded := by decide +kernel
theorem atom0508Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8592628800 : Int) atom0508Coded) := by
  have h := atom0508_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0508Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0509 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0509 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0509 = ((g 2) * (g 9) * (g 13)) := by
  norm_num [atom0509, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0509_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7029147840 : Int) atom0509) := by
  rw [SparsePolynomial.eval_scale, eval_atom0509]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0509Coded : CoefficientMerge.Poly := [(nat_lit 823, Int.ofNat (nat_lit 1))]
theorem atom0509Coded_decode : atom0509 = SparsePolynomial.decodeCubic 18 atom0509Coded := by decide +kernel
theorem atom0509Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7029147840 : Int) atom0509Coded) := by
  have h := atom0509_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0509Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0510 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0510 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0510 = ((g 2) * (g 9) * (g 14)) := by
  norm_num [atom0510, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0510_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9631143840 : Int) atom0510) := by
  rw [SparsePolynomial.eval_scale, eval_atom0510]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0510Coded : CoefficientMerge.Poly := [(nat_lit 824, Int.ofNat (nat_lit 1))]
theorem atom0510Coded_decode : atom0510 = SparsePolynomial.decodeCubic 18 atom0510Coded := by decide +kernel
theorem atom0510Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9631143840 : Int) atom0510Coded) := by
  have h := atom0510_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0510Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0511 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0511 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0511 = ((g 2) * (g 9) * (g 15)) := by
  norm_num [atom0511, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0511_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8158977600 : Int) atom0511) := by
  rw [SparsePolynomial.eval_scale, eval_atom0511]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0511Coded : CoefficientMerge.Poly := [(nat_lit 825, Int.ofNat (nat_lit 1))]
theorem atom0511Coded_decode : atom0511 = SparsePolynomial.decodeCubic 18 atom0511Coded := by decide +kernel
theorem atom0511Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8158977600 : Int) atom0511Coded) := by
  have h := atom0511_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0511Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0512 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0512 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0512 = ((g 2) * (g 9) * (g 16)) := by
  norm_num [atom0512, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0512_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8798871360 : Int) atom0512) := by
  rw [SparsePolynomial.eval_scale, eval_atom0512]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0512Coded : CoefficientMerge.Poly := [(nat_lit 826, Int.ofNat (nat_lit 1))]
theorem atom0512Coded_decode : atom0512 = SparsePolynomial.decodeCubic 18 atom0512Coded := by decide +kernel
theorem atom0512Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8798871360 : Int) atom0512Coded) := by
  have h := atom0512_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0512Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0513 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0513 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0513 = ((g 2) * (g 9) * (g 17)) := by
  norm_num [atom0513, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0513_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10613206080 : Int) atom0513) := by
  rw [SparsePolynomial.eval_scale, eval_atom0513]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0513Coded : CoefficientMerge.Poly := [(nat_lit 827, Int.ofNat (nat_lit 1))]
theorem atom0513Coded_decode : atom0513 = SparsePolynomial.decodeCubic 18 atom0513Coded := by decide +kernel
theorem atom0513Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10613206080 : Int) atom0513Coded) := by
  have h := atom0513_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0513Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0514 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0514 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0514 = ((g 2) * (g 10) * (g 10)) := by
  norm_num [atom0514, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0514_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4531960320 : Int) atom0514) := by
  rw [SparsePolynomial.eval_scale, eval_atom0514]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0514Coded : CoefficientMerge.Poly := [(nat_lit 838, Int.ofNat (nat_lit 1))]
theorem atom0514Coded_decode : atom0514 = SparsePolynomial.decodeCubic 18 atom0514Coded := by decide +kernel
theorem atom0514Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4531960320 : Int) atom0514Coded) := by
  have h := atom0514_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0514Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0515 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0515 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0515 = ((g 2) * (g 10) * (g 11)) := by
  norm_num [atom0515, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0515_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7932940800 : Int) atom0515) := by
  rw [SparsePolynomial.eval_scale, eval_atom0515]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0515Coded : CoefficientMerge.Poly := [(nat_lit 839, Int.ofNat (nat_lit 1))]
theorem atom0515Coded_decode : atom0515 = SparsePolynomial.decodeCubic 18 atom0515Coded := by decide +kernel
theorem atom0515Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7932940800 : Int) atom0515Coded) := by
  have h := atom0515_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0515Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0516 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0516 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0516 = ((g 2) * (g 10) * (g 12)) := by
  norm_num [atom0516, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0516_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9311655360 : Int) atom0516) := by
  rw [SparsePolynomial.eval_scale, eval_atom0516]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0516Coded : CoefficientMerge.Poly := [(nat_lit 840, Int.ofNat (nat_lit 1))]
theorem atom0516Coded_decode : atom0516 = SparsePolynomial.decodeCubic 18 atom0516Coded := by decide +kernel
theorem atom0516Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9311655360 : Int) atom0516Coded) := by
  have h := atom0516_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0516Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0517 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0517 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0517 = ((g 2) * (g 10) * (g 13)) := by
  norm_num [atom0517, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0517_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7477765440 : Int) atom0517) := by
  rw [SparsePolynomial.eval_scale, eval_atom0517]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0517Coded : CoefficientMerge.Poly := [(nat_lit 841, Int.ofNat (nat_lit 1))]
theorem atom0517Coded_decode : atom0517 = SparsePolynomial.decodeCubic 18 atom0517Coded := by decide +kernel
theorem atom0517Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7477765440 : Int) atom0517Coded) := by
  have h := atom0517_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0517Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0518 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0518 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0518 = ((g 2) * (g 10) * (g 14)) := by
  norm_num [atom0518, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0518_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10379483040 : Int) atom0518) := by
  rw [SparsePolynomial.eval_scale, eval_atom0518]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0518Coded : CoefficientMerge.Poly := [(nat_lit 842, Int.ofNat (nat_lit 1))]
theorem atom0518Coded_decode : atom0518 = SparsePolynomial.decodeCubic 18 atom0518Coded := by decide +kernel
theorem atom0518Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10379483040 : Int) atom0518Coded) := by
  have h := atom0518_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0518Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0519 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0519 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0519 = ((g 2) * (g 10) * (g 15)) := by
  norm_num [atom0519, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0519_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8044739520 : Int) atom0519) := by
  rw [SparsePolynomial.eval_scale, eval_atom0519]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0519Coded : CoefficientMerge.Poly := [(nat_lit 843, Int.ofNat (nat_lit 1))]
theorem atom0519Coded_decode : atom0519 = SparsePolynomial.decodeCubic 18 atom0519Coded := by decide +kernel
theorem atom0519Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8044739520 : Int) atom0519Coded) := by
  have h := atom0519_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0519Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0520 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0520 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0520 = ((g 2) * (g 10) * (g 16)) := by
  norm_num [atom0520, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0520_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8392186560 : Int) atom0520) := by
  rw [SparsePolynomial.eval_scale, eval_atom0520]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0520Coded : CoefficientMerge.Poly := [(nat_lit 844, Int.ofNat (nat_lit 1))]
theorem atom0520Coded_decode : atom0520 = SparsePolynomial.decodeCubic 18 atom0520Coded := by decide +kernel
theorem atom0520Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8392186560 : Int) atom0520Coded) := by
  have h := atom0520_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0520Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0521 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0521 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0521 = ((g 2) * (g 10) * (g 17)) := by
  norm_num [atom0521, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0521_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10204830720 : Int) atom0521) := by
  rw [SparsePolynomial.eval_scale, eval_atom0521]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0521Coded : CoefficientMerge.Poly := [(nat_lit 845, Int.ofNat (nat_lit 1))]
theorem atom0521Coded_decode : atom0521 = SparsePolynomial.decodeCubic 18 atom0521Coded := by decide +kernel
theorem atom0521Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10204830720 : Int) atom0521Coded) := by
  have h := atom0521_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0521Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0522 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0522 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0522 = ((g 2) * (g 11) * (g 11)) := by
  norm_num [atom0522, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0522_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4927426560 : Int) atom0522) := by
  rw [SparsePolynomial.eval_scale, eval_atom0522]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0522Coded : CoefficientMerge.Poly := [(nat_lit 857, Int.ofNat (nat_lit 1))]
theorem atom0522Coded_decode : atom0522 = SparsePolynomial.decodeCubic 18 atom0522Coded := by decide +kernel
theorem atom0522Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4927426560 : Int) atom0522Coded) := by
  have h := atom0522_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0522Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0523 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0523 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0523 = ((g 2) * (g 11) * (g 12)) := by
  norm_num [atom0523, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0523_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9870336000 : Int) atom0523) := by
  rw [SparsePolynomial.eval_scale, eval_atom0523]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0523Coded : CoefficientMerge.Poly := [(nat_lit 858, Int.ofNat (nat_lit 1))]
theorem atom0523Coded_decode : atom0523 = SparsePolynomial.decodeCubic 18 atom0523Coded := by decide +kernel
theorem atom0523Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9870336000 : Int) atom0523Coded) := by
  have h := atom0523_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0523Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0524 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0524 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0524 = ((g 2) * (g 11) * (g 13)) := by
  norm_num [atom0524, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0524_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7722086400 : Int) atom0524) := by
  rw [SparsePolynomial.eval_scale, eval_atom0524]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0524Coded : CoefficientMerge.Poly := [(nat_lit 859, Int.ofNat (nat_lit 1))]
theorem atom0524Coded_decode : atom0524 = SparsePolynomial.decodeCubic 18 atom0524Coded := by decide +kernel
theorem atom0524Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7722086400 : Int) atom0524Coded) := by
  have h := atom0524_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0524Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0525 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0525 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0525 = ((g 2) * (g 11) * (g 14)) := by
  norm_num [atom0525, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0525_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10978907040 : Int) atom0525) := by
  rw [SparsePolynomial.eval_scale, eval_atom0525]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0525Coded : CoefficientMerge.Poly := [(nat_lit 860, Int.ofNat (nat_lit 1))]
theorem atom0525Coded_decode : atom0525 = SparsePolynomial.decodeCubic 18 atom0525Coded := by decide +kernel
theorem atom0525Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10978907040 : Int) atom0525Coded) := by
  have h := atom0525_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0525Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0526 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0526 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0526 = ((g 2) * (g 11) * (g 15)) := by
  norm_num [atom0526, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0526_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8678154240 : Int) atom0526) := by
  rw [SparsePolynomial.eval_scale, eval_atom0526]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0526Coded : CoefficientMerge.Poly := [(nat_lit 861, Int.ofNat (nat_lit 1))]
theorem atom0526Coded_decode : atom0526 = SparsePolynomial.decodeCubic 18 atom0526Coded := by decide +kernel
theorem atom0526Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8678154240 : Int) atom0526Coded) := by
  have h := atom0526_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0526Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0527 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0527 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0527 = ((g 2) * (g 11) * (g 16)) := by
  norm_num [atom0527, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0527_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7662090240 : Int) atom0527) := by
  rw [SparsePolynomial.eval_scale, eval_atom0527]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0527Coded : CoefficientMerge.Poly := [(nat_lit 862, Int.ofNat (nat_lit 1))]
theorem atom0527Coded_decode : atom0527 = SparsePolynomial.decodeCubic 18 atom0527Coded := by decide +kernel
theorem atom0527Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7662090240 : Int) atom0527Coded) := by
  have h := atom0527_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0527Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0528 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0528 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0528 = ((g 2) * (g 11) * (g 17)) := by
  norm_num [atom0528, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0528_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11373788160 : Int) atom0528) := by
  rw [SparsePolynomial.eval_scale, eval_atom0528]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0528Coded : CoefficientMerge.Poly := [(nat_lit 863, Int.ofNat (nat_lit 1))]
theorem atom0528Coded_decode : atom0528 = SparsePolynomial.decodeCubic 18 atom0528Coded := by decide +kernel
theorem atom0528Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11373788160 : Int) atom0528Coded) := by
  have h := atom0528_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0528Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0529 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0529 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0529 = ((g 2) * (g 12) * (g 12)) := by
  norm_num [atom0529, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0529_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6543452160 : Int) atom0529) := by
  rw [SparsePolynomial.eval_scale, eval_atom0529]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0529Coded : CoefficientMerge.Poly := [(nat_lit 876, Int.ofNat (nat_lit 1))]
theorem atom0529Coded_decode : atom0529 = SparsePolynomial.decodeCubic 18 atom0529Coded := by decide +kernel
theorem atom0529Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6543452160 : Int) atom0529Coded) := by
  have h := atom0529_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0529Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0530 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0530 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0530 = ((g 2) * (g 12) * (g 13)) := by
  norm_num [atom0530, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0530_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10721894400 : Int) atom0530) := by
  rw [SparsePolynomial.eval_scale, eval_atom0530]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0530Coded : CoefficientMerge.Poly := [(nat_lit 877, Int.ofNat (nat_lit 1))]
theorem atom0530Coded_decode : atom0530 = SparsePolynomial.decodeCubic 18 atom0530Coded := by decide +kernel
theorem atom0530Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10721894400 : Int) atom0530Coded) := by
  have h := atom0530_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0530Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0531 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0531 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0531 = ((g 2) * (g 12) * (g 14)) := by
  norm_num [atom0531, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0531_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15248311200 : Int) atom0531) := by
  rw [SparsePolynomial.eval_scale, eval_atom0531]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0531Coded : CoefficientMerge.Poly := [(nat_lit 878, Int.ofNat (nat_lit 1))]
theorem atom0531Coded_decode : atom0531 = SparsePolynomial.decodeCubic 18 atom0531Coded := by decide +kernel
theorem atom0531Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (15248311200 : Int) atom0531Coded) := by
  have h := atom0531_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0531Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0532 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0532 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0532 = ((g 2) * (g 12) * (g 15)) := by
  norm_num [atom0532, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0532_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13098516480 : Int) atom0532) := by
  rw [SparsePolynomial.eval_scale, eval_atom0532]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0532Coded : CoefficientMerge.Poly := [(nat_lit 879, Int.ofNat (nat_lit 1))]
theorem atom0532Coded_decode : atom0532 = SparsePolynomial.decodeCubic 18 atom0532Coded := by decide +kernel
theorem atom0532Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13098516480 : Int) atom0532Coded) := by
  have h := atom0532_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0532Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0533 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0533 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0533 = ((g 2) * (g 12) * (g 16)) := by
  norm_num [atom0533, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0533_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7930137600 : Int) atom0533) := by
  rw [SparsePolynomial.eval_scale, eval_atom0533]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0533Coded : CoefficientMerge.Poly := [(nat_lit 880, Int.ofNat (nat_lit 1))]
theorem atom0533Coded_decode : atom0533 = SparsePolynomial.decodeCubic 18 atom0533Coded := by decide +kernel
theorem atom0533Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7930137600 : Int) atom0533Coded) := by
  have h := atom0533_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0533Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0534 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0534 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0534 = ((g 2) * (g 12) * (g 17)) := by
  norm_num [atom0534, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0534_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12465129600 : Int) atom0534) := by
  rw [SparsePolynomial.eval_scale, eval_atom0534]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0534Coded : CoefficientMerge.Poly := [(nat_lit 881, Int.ofNat (nat_lit 1))]
theorem atom0534Coded_decode : atom0534 = SparsePolynomial.decodeCubic 18 atom0534Coded := by decide +kernel
theorem atom0534Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12465129600 : Int) atom0534Coded) := by
  have h := atom0534_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0534Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0535 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0535 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0535 = ((g 2) * (g 13) * (g 13)) := by
  norm_num [atom0535, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0535_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4665765888 : Int) atom0535) := by
  rw [SparsePolynomial.eval_scale, eval_atom0535]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0535Coded : CoefficientMerge.Poly := [(nat_lit 895, Int.ofNat (nat_lit 1))]
theorem atom0535Coded_decode : atom0535 = SparsePolynomial.decodeCubic 18 atom0535Coded := by decide +kernel
theorem atom0535Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4665765888 : Int) atom0535Coded) := by
  have h := atom0535_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0535Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0536 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0536 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0536 = ((g 2) * (g 13) * (g 14)) := by
  norm_num [atom0536, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0536_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12464877240 : Int) atom0536) := by
  rw [SparsePolynomial.eval_scale, eval_atom0536]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0536Coded : CoefficientMerge.Poly := [(nat_lit 896, Int.ofNat (nat_lit 1))]
theorem atom0536Coded_decode : atom0536 = SparsePolynomial.decodeCubic 18 atom0536Coded := by decide +kernel
theorem atom0536Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12464877240 : Int) atom0536Coded) := by
  have h := atom0536_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0536Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0537 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0537 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0537 = ((g 2) * (g 13) * (g 15)) := by
  norm_num [atom0537, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0537_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12188897280 : Int) atom0537) := by
  rw [SparsePolynomial.eval_scale, eval_atom0537]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0537Coded : CoefficientMerge.Poly := [(nat_lit 897, Int.ofNat (nat_lit 1))]
theorem atom0537Coded_decode : atom0537 = SparsePolynomial.decodeCubic 18 atom0537Coded := by decide +kernel
theorem atom0537Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12188897280 : Int) atom0537Coded) := by
  have h := atom0537_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0537Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0538 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0538 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0538 = ((g 2) * (g 13) * (g 16)) := by
  norm_num [atom0538, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0538_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8198184960 : Int) atom0538) := by
  rw [SparsePolynomial.eval_scale, eval_atom0538]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0538Coded : CoefficientMerge.Poly := [(nat_lit 898, Int.ofNat (nat_lit 1))]
theorem atom0538Coded_decode : atom0538 = SparsePolynomial.decodeCubic 18 atom0538Coded := by decide +kernel
theorem atom0538Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8198184960 : Int) atom0538Coded) := by
  have h := atom0538_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0538Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0539 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0539 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0539 = ((g 2) * (g 13) * (g 17)) := by
  norm_num [atom0539, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0539_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9925534080 : Int) atom0539) := by
  rw [SparsePolynomial.eval_scale, eval_atom0539]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0539Coded : CoefficientMerge.Poly := [(nat_lit 899, Int.ofNat (nat_lit 1))]
theorem atom0539Coded_decode : atom0539 = SparsePolynomial.decodeCubic 18 atom0539Coded := by decide +kernel
theorem atom0539Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9925534080 : Int) atom0539Coded) := by
  have h := atom0539_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0539Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0540 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0540 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0540 = ((g 2) * (g 14) * (g 14)) := by
  norm_num [atom0540, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0540_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8286435000 : Int) atom0540) := by
  rw [SparsePolynomial.eval_scale, eval_atom0540]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0540Coded : CoefficientMerge.Poly := [(nat_lit 914, Int.ofNat (nat_lit 1))]
theorem atom0540Coded_decode : atom0540 = SparsePolynomial.decodeCubic 18 atom0540Coded := by decide +kernel
theorem atom0540Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8286435000 : Int) atom0540Coded) := by
  have h := atom0540_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0540Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0541 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0541 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0541 = ((g 2) * (g 14) * (g 15)) := by
  norm_num [atom0541, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0541_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12894527160 : Int) atom0541) := by
  rw [SparsePolynomial.eval_scale, eval_atom0541]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0541Coded : CoefficientMerge.Poly := [(nat_lit 915, Int.ofNat (nat_lit 1))]
theorem atom0541Coded_decode : atom0541 = SparsePolynomial.decodeCubic 18 atom0541Coded := by decide +kernel
theorem atom0541Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12894527160 : Int) atom0541Coded) := by
  have h := atom0541_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0541Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0542 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0542 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0542 = ((g 2) * (g 14) * (g 16)) := by
  norm_num [atom0542, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0542_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8358624720 : Int) atom0542) := by
  rw [SparsePolynomial.eval_scale, eval_atom0542]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0542Coded : CoefficientMerge.Poly := [(nat_lit 916, Int.ofNat (nat_lit 1))]
theorem atom0542Coded_decode : atom0542 = SparsePolynomial.decodeCubic 18 atom0542Coded := by decide +kernel
theorem atom0542Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8358624720 : Int) atom0542Coded) := by
  have h := atom0542_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0542Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0543 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0543 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0543 = ((g 2) * (g 14) * (g 17)) := by
  norm_num [atom0543, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0543_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10676419920 : Int) atom0543) := by
  rw [SparsePolynomial.eval_scale, eval_atom0543]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0543Coded : CoefficientMerge.Poly := [(nat_lit 917, Int.ofNat (nat_lit 1))]
theorem atom0543Coded_decode : atom0543 = SparsePolynomial.decodeCubic 18 atom0543Coded := by decide +kernel
theorem atom0543Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10676419920 : Int) atom0543Coded) := by
  have h := atom0543_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0543Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0544 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0544 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0544 = ((g 2) * (g 15) * (g 15)) := by
  norm_num [atom0544, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0544_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4296499200 : Int) atom0544) := by
  rw [SparsePolynomial.eval_scale, eval_atom0544]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0544Coded : CoefficientMerge.Poly := [(nat_lit 933, Int.ofNat (nat_lit 1))]
theorem atom0544Coded_decode : atom0544 = SparsePolynomial.decodeCubic 18 atom0544Coded := by decide +kernel
theorem atom0544Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4296499200 : Int) atom0544Coded) := by
  have h := atom0544_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0544Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0545 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0545 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0545 = ((g 2) * (g 15) * (g 16)) := by
  norm_num [atom0545, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0545_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5555934720 : Int) atom0545) := by
  rw [SparsePolynomial.eval_scale, eval_atom0545]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0545Coded : CoefficientMerge.Poly := [(nat_lit 934, Int.ofNat (nat_lit 1))]
theorem atom0545Coded_decode : atom0545 = SparsePolynomial.decodeCubic 18 atom0545Coded := by decide +kernel
theorem atom0545Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5555934720 : Int) atom0545Coded) := by
  have h := atom0545_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0545Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0546 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0546 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0546 = ((g 2) * (g 15) * (g 17)) := by
  norm_num [atom0546, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0546_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8244432000 : Int) atom0546) := by
  rw [SparsePolynomial.eval_scale, eval_atom0546]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0546Coded : CoefficientMerge.Poly := [(nat_lit 935, Int.ofNat (nat_lit 1))]
theorem atom0546Coded_decode : atom0546 = SparsePolynomial.decodeCubic 18 atom0546Coded := by decide +kernel
theorem atom0546Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8244432000 : Int) atom0546Coded) := by
  have h := atom0546_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0546Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0547 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0547 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0547 = ((g 2) * (g 16) * (g 16)) := by
  norm_num [atom0547, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0547_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (572866560 : Int) atom0547) := by
  rw [SparsePolynomial.eval_scale, eval_atom0547]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0547Coded : CoefficientMerge.Poly := [(nat_lit 952, Int.ofNat (nat_lit 1))]
theorem atom0547Coded_decode : atom0547 = SparsePolynomial.decodeCubic 18 atom0547Coded := by decide +kernel
theorem atom0547Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (572866560 : Int) atom0547Coded) := by
  have h := atom0547_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0547Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0548 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0548 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0548 = ((g 2) * (g 16) * (g 17)) := by
  norm_num [atom0548, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0548_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3862212480 : Int) atom0548) := by
  rw [SparsePolynomial.eval_scale, eval_atom0548]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0548Coded : CoefficientMerge.Poly := [(nat_lit 953, Int.ofNat (nat_lit 1))]
theorem atom0548Coded_decode : atom0548 = SparsePolynomial.decodeCubic 18 atom0548Coded := by decide +kernel
theorem atom0548Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3862212480 : Int) atom0548Coded) := by
  have h := atom0548_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0548Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0549 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0549 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0549 = ((g 2) * (g 17) * (g 17)) := by
  norm_num [atom0549, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0549_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2854776960 : Int) atom0549) := by
  rw [SparsePolynomial.eval_scale, eval_atom0549]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0549Coded : CoefficientMerge.Poly := [(nat_lit 971, Int.ofNat (nat_lit 1))]
theorem atom0549Coded_decode : atom0549 = SparsePolynomial.decodeCubic 18 atom0549Coded := by decide +kernel
theorem atom0549Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2854776960 : Int) atom0549Coded) := by
  have h := atom0549_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0549Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0550 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0550 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0550 = ((g 3) * (g 3) * (g 3)) := by
  norm_num [atom0550, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0550_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (249016320 : Int) atom0550) := by
  rw [SparsePolynomial.eval_scale, eval_atom0550]
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 3) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0550Coded : CoefficientMerge.Poly := [(nat_lit 1029, Int.ofNat (nat_lit 1))]
theorem atom0550Coded_decode : atom0550 = SparsePolynomial.decodeCubic 18 atom0550Coded := by decide +kernel
theorem atom0550Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (249016320 : Int) atom0550Coded) := by
  have h := atom0550_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0550Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0551 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0551 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0551 = ((g 3) * (g 3) * (g 4)) := by
  norm_num [atom0551, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0551_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (633507840 : Int) atom0551) := by
  rw [SparsePolynomial.eval_scale, eval_atom0551]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0551Coded : CoefficientMerge.Poly := [(nat_lit 1030, Int.ofNat (nat_lit 1))]
theorem atom0551Coded_decode : atom0551 = SparsePolynomial.decodeCubic 18 atom0551Coded := by decide +kernel
theorem atom0551Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (633507840 : Int) atom0551Coded) := by
  have h := atom0551_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0551Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0552 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0552 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0552 = ((g 3) * (g 3) * (g 5)) := by
  norm_num [atom0552, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0552_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (519966720 : Int) atom0552) := by
  rw [SparsePolynomial.eval_scale, eval_atom0552]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0552Coded : CoefficientMerge.Poly := [(nat_lit 1031, Int.ofNat (nat_lit 1))]
theorem atom0552Coded_decode : atom0552 = SparsePolynomial.decodeCubic 18 atom0552Coded := by decide +kernel
theorem atom0552Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (519966720 : Int) atom0552Coded) := by
  have h := atom0552_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0552Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0553 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0553 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0553 = ((g 3) * (g 3) * (g 6)) := by
  norm_num [atom0553, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0553_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (406425600 : Int) atom0553) := by
  rw [SparsePolynomial.eval_scale, eval_atom0553]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0553Coded : CoefficientMerge.Poly := [(nat_lit 1032, Int.ofNat (nat_lit 1))]
theorem atom0553Coded_decode : atom0553 = SparsePolynomial.decodeCubic 18 atom0553Coded := by decide +kernel
theorem atom0553Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (406425600 : Int) atom0553Coded) := by
  have h := atom0553_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0553Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0554 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0554 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0554 = ((g 3) * (g 3) * (g 7)) := by
  norm_num [atom0554, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0554_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (292884480 : Int) atom0554) := by
  rw [SparsePolynomial.eval_scale, eval_atom0554]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0554Coded : CoefficientMerge.Poly := [(nat_lit 1033, Int.ofNat (nat_lit 1))]
theorem atom0554Coded_decode : atom0554 = SparsePolynomial.decodeCubic 18 atom0554Coded := by decide +kernel
theorem atom0554Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (292884480 : Int) atom0554Coded) := by
  have h := atom0554_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0554Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0555 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0555 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0555 = ((g 3) * (g 3) * (g 8)) := by
  norm_num [atom0555, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0555_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (230576640 : Int) atom0555) := by
  rw [SparsePolynomial.eval_scale, eval_atom0555]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0555Coded : CoefficientMerge.Poly := [(nat_lit 1034, Int.ofNat (nat_lit 1))]
theorem atom0555Coded_decode : atom0555 = SparsePolynomial.decodeCubic 18 atom0555Coded := by decide +kernel
theorem atom0555Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (230576640 : Int) atom0555Coded) := by
  have h := atom0555_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0555Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0556 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0556 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0556 = ((g 3) * (g 3) * (g 9)) := by
  norm_num [atom0556, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0556_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (108003840 : Int) atom0556) := by
  rw [SparsePolynomial.eval_scale, eval_atom0556]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0556Coded : CoefficientMerge.Poly := [(nat_lit 1035, Int.ofNat (nat_lit 1))]
theorem atom0556Coded_decode : atom0556 = SparsePolynomial.decodeCubic 18 atom0556Coded := by decide +kernel
theorem atom0556Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (108003840 : Int) atom0556Coded) := by
  have h := atom0556_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0556Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0557 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0557 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0557 = ((g 3) * (g 3) * (g 10)) := by
  norm_num [atom0557, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0557_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10590720 : Int) atom0557) := by
  rw [SparsePolynomial.eval_scale, eval_atom0557]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0557Coded : CoefficientMerge.Poly := [(nat_lit 1036, Int.ofNat (nat_lit 1))]
theorem atom0557Coded_decode : atom0557 = SparsePolynomial.decodeCubic 18 atom0557Coded := by decide +kernel
theorem atom0557Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10590720 : Int) atom0557Coded) := by
  have h := atom0557_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0557Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0558 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0558 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0558 = ((g 3) * (g 3) * (g 12)) := by
  norm_num [atom0558, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0558_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1501839360 : Int) atom0558) := by
  rw [SparsePolynomial.eval_scale, eval_atom0558]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0558Coded : CoefficientMerge.Poly := [(nat_lit 1038, Int.ofNat (nat_lit 1))]
theorem atom0558Coded_decode : atom0558 = SparsePolynomial.decodeCubic 18 atom0558Coded := by decide +kernel
theorem atom0558Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1501839360 : Int) atom0558Coded) := by
  have h := atom0558_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0558Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0559 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 3, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0559 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0559 = ((g 3) * (g 3) * (g 14)) := by
  norm_num [atom0559, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0559_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1167149520 : Int) atom0559) := by
  rw [SparsePolynomial.eval_scale, eval_atom0559]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0559Coded : CoefficientMerge.Poly := [(nat_lit 1040, Int.ofNat (nat_lit 1))]
theorem atom0559Coded_decode : atom0559 = SparsePolynomial.decodeCubic 18 atom0559Coded := by decide +kernel
theorem atom0559Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1167149520 : Int) atom0559Coded) := by
  have h := atom0559_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0559Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0560 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0560 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0560 = ((g 3) * (g 4) * (g 4)) := by
  norm_num [atom0560, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0560_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1344806400 : Int) atom0560) := by
  rw [SparsePolynomial.eval_scale, eval_atom0560]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 3) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0560Coded : CoefficientMerge.Poly := [(nat_lit 1048, Int.ofNat (nat_lit 1))]
theorem atom0560Coded_decode : atom0560 = SparsePolynomial.decodeCubic 18 atom0560Coded := by decide +kernel
theorem atom0560Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1344806400 : Int) atom0560Coded) := by
  have h := atom0560_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0560Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0561 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0561 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0561 = ((g 3) * (g 4) * (g 5)) := by
  norm_num [atom0561, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0561_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1764439680 : Int) atom0561) := by
  rw [SparsePolynomial.eval_scale, eval_atom0561]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0561Coded : CoefficientMerge.Poly := [(nat_lit 1049, Int.ofNat (nat_lit 1))]
theorem atom0561Coded_decode : atom0561 = SparsePolynomial.decodeCubic 18 atom0561Coded := by decide +kernel
theorem atom0561Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1764439680 : Int) atom0561Coded) := by
  have h := atom0561_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0561Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0562 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0562 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0562 = ((g 3) * (g 4) * (g 6)) := by
  norm_num [atom0562, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0562_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (766439040 : Int) atom0562) := by
  rw [SparsePolynomial.eval_scale, eval_atom0562]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 3) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0562Coded : CoefficientMerge.Poly := [(nat_lit 1050, Int.ofNat (nat_lit 1))]
theorem atom0562Coded_decode : atom0562 = SparsePolynomial.decodeCubic 18 atom0562Coded := by decide +kernel
theorem atom0562Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (766439040 : Int) atom0562Coded) := by
  have h := atom0562_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0562Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0563 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0563 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0563 = ((g 3) * (g 4) * (g 7)) := by
  norm_num [atom0563, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0563_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (245414400 : Int) atom0563) := by
  rw [SparsePolynomial.eval_scale, eval_atom0563]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0563Coded : CoefficientMerge.Poly := [(nat_lit 1051, Int.ofNat (nat_lit 1))]
theorem atom0563Coded_decode : atom0563 = SparsePolynomial.decodeCubic 18 atom0563Coded := by decide +kernel
theorem atom0563Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (245414400 : Int) atom0563Coded) := by
  have h := atom0563_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0563Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0564 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0564 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0564 = ((g 3) * (g 4) * (g 8)) := by
  norm_num [atom0564, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0564_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (208266240 : Int) atom0564) := by
  rw [SparsePolynomial.eval_scale, eval_atom0564]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0564Coded : CoefficientMerge.Poly := [(nat_lit 1052, Int.ofNat (nat_lit 1))]
theorem atom0564Coded_decode : atom0564 = SparsePolynomial.decodeCubic 18 atom0564Coded := by decide +kernel
theorem atom0564Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (208266240 : Int) atom0564Coded) := by
  have h := atom0564_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0564Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0565 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0565 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0565 = ((g 3) * (g 4) * (g 9)) := by
  norm_num [atom0565, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0565_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (164398080 : Int) atom0565) := by
  rw [SparsePolynomial.eval_scale, eval_atom0565]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0565Coded : CoefficientMerge.Poly := [(nat_lit 1053, Int.ofNat (nat_lit 1))]
theorem atom0565Coded_decode : atom0565 = SparsePolynomial.decodeCubic 18 atom0565Coded := by decide +kernel
theorem atom0565Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (164398080 : Int) atom0565Coded) := by
  have h := atom0565_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0565Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0566 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0566 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0566 = ((g 3) * (g 4) * (g 10)) := by
  norm_num [atom0566, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0566_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (170849280 : Int) atom0566) := by
  rw [SparsePolynomial.eval_scale, eval_atom0566]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0566Coded : CoefficientMerge.Poly := [(nat_lit 1054, Int.ofNat (nat_lit 1))]
theorem atom0566Coded_decode : atom0566 = SparsePolynomial.decodeCubic 18 atom0566Coded := by decide +kernel
theorem atom0566Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (170849280 : Int) atom0566Coded) := by
  have h := atom0566_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0566Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0567 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0567 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0567 = ((g 3) * (g 4) * (g 11)) := by
  norm_num [atom0567, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0567_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (264122880 : Int) atom0567) := by
  rw [SparsePolynomial.eval_scale, eval_atom0567]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0567Coded : CoefficientMerge.Poly := [(nat_lit 1055, Int.ofNat (nat_lit 1))]
theorem atom0567Coded_decode : atom0567 = SparsePolynomial.decodeCubic 18 atom0567Coded := by decide +kernel
theorem atom0567Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (264122880 : Int) atom0567Coded) := by
  have h := atom0567_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0567Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0568 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0568 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0568 = ((g 3) * (g 4) * (g 12)) := by
  norm_num [atom0568, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0568_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3555901440 : Int) atom0568) := by
  rw [SparsePolynomial.eval_scale, eval_atom0568]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0568Coded : CoefficientMerge.Poly := [(nat_lit 1056, Int.ofNat (nat_lit 1))]
theorem atom0568Coded_decode : atom0568 = SparsePolynomial.decodeCubic 18 atom0568Coded := by decide +kernel
theorem atom0568Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3555901440 : Int) atom0568Coded) := by
  have h := atom0568_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0568Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0569 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0569 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0569 = ((g 3) * (g 4) * (g 13)) := by
  norm_num [atom0569, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0569_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (936962880 : Int) atom0569) := by
  rw [SparsePolynomial.eval_scale, eval_atom0569]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0569Coded : CoefficientMerge.Poly := [(nat_lit 1057, Int.ofNat (nat_lit 1))]
theorem atom0569Coded_decode : atom0569 = SparsePolynomial.decodeCubic 18 atom0569Coded := by decide +kernel
theorem atom0569Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (936962880 : Int) atom0569Coded) := by
  have h := atom0569_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0569Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0570 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0570 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0570 = ((g 3) * (g 4) * (g 14)) := by
  norm_num [atom0570, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0570_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3289076640 : Int) atom0570) := by
  rw [SparsePolynomial.eval_scale, eval_atom0570]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0570Coded : CoefficientMerge.Poly := [(nat_lit 1058, Int.ofNat (nat_lit 1))]
theorem atom0570Coded_decode : atom0570 = SparsePolynomial.decodeCubic 18 atom0570Coded := by decide +kernel
theorem atom0570Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3289076640 : Int) atom0570Coded) := by
  have h := atom0570_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0570Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0571 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0571 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0571 = ((g 3) * (g 4) * (g 15)) := by
  norm_num [atom0571, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0571_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2074914240 : Int) atom0571) := by
  rw [SparsePolynomial.eval_scale, eval_atom0571]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0571Coded : CoefficientMerge.Poly := [(nat_lit 1059, Int.ofNat (nat_lit 1))]
theorem atom0571Coded_decode : atom0571 = SparsePolynomial.decodeCubic 18 atom0571Coded := by decide +kernel
theorem atom0571Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2074914240 : Int) atom0571Coded) := by
  have h := atom0571_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0571Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0572 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0572 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0572 = ((g 3) * (g 4) * (g 16)) := by
  norm_num [atom0572, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0572_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2798927040 : Int) atom0572) := by
  rw [SparsePolynomial.eval_scale, eval_atom0572]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0572Coded : CoefficientMerge.Poly := [(nat_lit 1060, Int.ofNat (nat_lit 1))]
theorem atom0572Coded_decode : atom0572 = SparsePolynomial.decodeCubic 18 atom0572Coded := by decide +kernel
theorem atom0572Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2798927040 : Int) atom0572Coded) := by
  have h := atom0572_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0572Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0573 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 4, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0573 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0573 = ((g 3) * (g 4) * (g 17)) := by
  norm_num [atom0573, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0573_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3522939840 : Int) atom0573) := by
  rw [SparsePolynomial.eval_scale, eval_atom0573]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0573Coded : CoefficientMerge.Poly := [(nat_lit 1061, Int.ofNat (nat_lit 1))]
theorem atom0573Coded_decode : atom0573 = SparsePolynomial.decodeCubic 18 atom0573Coded := by decide +kernel
theorem atom0573Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3522939840 : Int) atom0573Coded) := by
  have h := atom0573_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0573Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0574 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0574 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0574 = ((g 3) * (g 5) * (g 5)) := by
  norm_num [atom0574, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0574_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1300867200 : Int) atom0574) := by
  rw [SparsePolynomial.eval_scale, eval_atom0574]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 3) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0574Coded : CoefficientMerge.Poly := [(nat_lit 1067, Int.ofNat (nat_lit 1))]
theorem atom0574Coded_decode : atom0574 = SparsePolynomial.decodeCubic 18 atom0574Coded := by decide +kernel
theorem atom0574Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1300867200 : Int) atom0574Coded) := by
  have h := atom0574_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0574Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block007 : CoefficientMerge.Poly := [(nat_lit 800, Int.ofNat (nat_lit 3718671360)), (nat_lit 801, Int.ofNat (nat_lit 6793720320)), (nat_lit 802, Int.ofNat (nat_lit 6517608960)), (nat_lit 803, Int.ofNat (nat_lit 6167040000)), (nat_lit 804, Int.ofNat (nat_lit 7979381760)), (nat_lit 805, Int.ofNat (nat_lit 6566323200)), (nat_lit 806, Int.ofNat (nat_lit 8933124000)), (nat_lit 807, Int.ofNat (nat_lit 7949368320)), (nat_lit 808, Int.ofNat (nat_lit 8692055040)), (nat_lit 809, Int.ofNat (nat_lit 10609182720)), (nat_lit 819, Int.ofNat (nat_lit 4164011520)), (nat_lit 820, Int.ofNat (nat_lit 7503144960)), (nat_lit 821, Int.ofNat (nat_lit 6954524160)), (nat_lit 822, Int.ofNat (nat_lit 8592628800)), (nat_lit 823, Int.ofNat (nat_lit 7029147840)), (nat_lit 824, Int.ofNat (nat_lit 9631143840)), (nat_lit 825, Int.ofNat (nat_lit 8158977600)), (nat_lit 826, Int.ofNat (nat_lit 8798871360)), (nat_lit 827, Int.ofNat (nat_lit 10613206080)), (nat_lit 838, Int.ofNat (nat_lit 4531960320)), (nat_lit 839, Int.ofNat (nat_lit 7932940800)), (nat_lit 840, Int.ofNat (nat_lit 9311655360)), (nat_lit 841, Int.ofNat (nat_lit 7477765440)), (nat_lit 842, Int.ofNat (nat_lit 10379483040)), (nat_lit 843, Int.ofNat (nat_lit 8044739520)), (nat_lit 844, Int.ofNat (nat_lit 8392186560)), (nat_lit 845, Int.ofNat (nat_lit 10204830720)), (nat_lit 857, Int.ofNat (nat_lit 4927426560)), (nat_lit 858, Int.ofNat (nat_lit 9870336000)), (nat_lit 859, Int.ofNat (nat_lit 7722086400)), (nat_lit 860, Int.ofNat (nat_lit 10978907040)), (nat_lit 861, Int.ofNat (nat_lit 8678154240)), (nat_lit 862, Int.ofNat (nat_lit 7662090240)), (nat_lit 863, Int.ofNat (nat_lit 11373788160)), (nat_lit 876, Int.ofNat (nat_lit 6543452160)), (nat_lit 877, Int.ofNat (nat_lit 10721894400)), (nat_lit 878, Int.ofNat (nat_lit 15248311200)), (nat_lit 879, Int.ofNat (nat_lit 13098516480)), (nat_lit 880, Int.ofNat (nat_lit 7930137600)), (nat_lit 881, Int.ofNat (nat_lit 12465129600)), (nat_lit 895, Int.ofNat (nat_lit 4665765888)), (nat_lit 896, Int.ofNat (nat_lit 12464877240)), (nat_lit 897, Int.ofNat (nat_lit 12188897280)), (nat_lit 898, Int.ofNat (nat_lit 8198184960)), (nat_lit 899, Int.ofNat (nat_lit 9925534080)), (nat_lit 914, Int.ofNat (nat_lit 8286435000)), (nat_lit 915, Int.ofNat (nat_lit 12894527160)), (nat_lit 916, Int.ofNat (nat_lit 8358624720)), (nat_lit 917, Int.ofNat (nat_lit 10676419920)), (nat_lit 933, Int.ofNat (nat_lit 4296499200)), (nat_lit 934, Int.ofNat (nat_lit 5555934720)), (nat_lit 935, Int.ofNat (nat_lit 8244432000)), (nat_lit 952, Int.ofNat (nat_lit 572866560)), (nat_lit 953, Int.ofNat (nat_lit 3862212480)), (nat_lit 971, Int.ofNat (nat_lit 2854776960)), (nat_lit 1029, Int.ofNat (nat_lit 249016320)), (nat_lit 1030, Int.ofNat (nat_lit 633507840)), (nat_lit 1031, Int.ofNat (nat_lit 519966720)), (nat_lit 1032, Int.ofNat (nat_lit 406425600)), (nat_lit 1033, Int.ofNat (nat_lit 292884480)), (nat_lit 1034, Int.ofNat (nat_lit 230576640)), (nat_lit 1035, Int.ofNat (nat_lit 108003840)), (nat_lit 1036, Int.ofNat (nat_lit 10590720)), (nat_lit 1038, Int.ofNat (nat_lit 1501839360)), (nat_lit 1040, Int.ofNat (nat_lit 1167149520)), (nat_lit 1048, Int.ofNat (nat_lit 1344806400)), (nat_lit 1049, Int.ofNat (nat_lit 1764439680)), (nat_lit 1050, Int.ofNat (nat_lit 766439040)), (nat_lit 1051, Int.ofNat (nat_lit 245414400)), (nat_lit 1052, Int.ofNat (nat_lit 208266240)), (nat_lit 1053, Int.ofNat (nat_lit 164398080)), (nat_lit 1054, Int.ofNat (nat_lit 170849280)), (nat_lit 1055, Int.ofNat (nat_lit 264122880)), (nat_lit 1056, Int.ofNat (nat_lit 3555901440)), (nat_lit 1057, Int.ofNat (nat_lit 936962880)), (nat_lit 1058, Int.ofNat (nat_lit 3289076640)), (nat_lit 1059, Int.ofNat (nat_lit 2074914240)), (nat_lit 1060, Int.ofNat (nat_lit 2798927040)), (nat_lit 1061, Int.ofNat (nat_lit 3522939840)), (nat_lit 1067, Int.ofNat (nat_lit 1300867200))]
def block007_data_flat000 : CoefficientMerge.Poly := [(nat_lit 800, Int.ofNat (nat_lit 3718671360))]
theorem block007_data_flat000_step : block007_data_flat000 = (CoefficientMerge.scale (3718671360 : Int) atom0495Coded) := by decide +kernel
theorem block007_data_flat000_original : block007_data_flat000 = (CoefficientMerge.scale (3718671360 : Int) atom0495Coded) := by
  rw [block007_data_flat000_step]
def block007_data_flat001 : CoefficientMerge.Poly := [(nat_lit 801, Int.ofNat (nat_lit 6793720320))]
theorem block007_data_flat001_step : block007_data_flat001 = (CoefficientMerge.scale (6793720320 : Int) atom0496Coded) := by decide +kernel
theorem block007_data_flat001_original : block007_data_flat001 = (CoefficientMerge.scale (6793720320 : Int) atom0496Coded) := by
  rw [block007_data_flat001_step]
def block007_data_flat002 : CoefficientMerge.Poly := [(nat_lit 800, Int.ofNat (nat_lit 3718671360)), (nat_lit 801, Int.ofNat (nat_lit 6793720320))]
theorem block007_data_flat002_step : block007_data_flat002 = (CoefficientMerge.fastMerge block007_data_flat000 block007_data_flat001) := by decide +kernel
theorem block007_data_flat002_original : block007_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3718671360 : Int) atom0495Coded) (CoefficientMerge.scale (6793720320 : Int) atom0496Coded)) := by
  rw [block007_data_flat002_step, block007_data_flat000_original, block007_data_flat001_original]
def block007_data_flat003 : CoefficientMerge.Poly := [(nat_lit 802, Int.ofNat (nat_lit 6517608960))]
theorem block007_data_flat003_step : block007_data_flat003 = (CoefficientMerge.scale (6517608960 : Int) atom0497Coded) := by decide +kernel
theorem block007_data_flat003_original : block007_data_flat003 = (CoefficientMerge.scale (6517608960 : Int) atom0497Coded) := by
  rw [block007_data_flat003_step]
def block007_data_flat004 : CoefficientMerge.Poly := [(nat_lit 803, Int.ofNat (nat_lit 6167040000))]
theorem block007_data_flat004_step : block007_data_flat004 = (CoefficientMerge.scale (6167040000 : Int) atom0498Coded) := by decide +kernel
theorem block007_data_flat004_original : block007_data_flat004 = (CoefficientMerge.scale (6167040000 : Int) atom0498Coded) := by
  rw [block007_data_flat004_step]
def block007_data_flat005 : CoefficientMerge.Poly := [(nat_lit 804, Int.ofNat (nat_lit 7979381760))]
theorem block007_data_flat005_step : block007_data_flat005 = (CoefficientMerge.scale (7979381760 : Int) atom0499Coded) := by decide +kernel
theorem block007_data_flat005_original : block007_data_flat005 = (CoefficientMerge.scale (7979381760 : Int) atom0499Coded) := by
  rw [block007_data_flat005_step]
def block007_data_flat006 : CoefficientMerge.Poly := [(nat_lit 803, Int.ofNat (nat_lit 6167040000)), (nat_lit 804, Int.ofNat (nat_lit 7979381760))]
theorem block007_data_flat006_step : block007_data_flat006 = (CoefficientMerge.fastMerge block007_data_flat004 block007_data_flat005) := by decide +kernel
theorem block007_data_flat006_original : block007_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6167040000 : Int) atom0498Coded) (CoefficientMerge.scale (7979381760 : Int) atom0499Coded)) := by
  rw [block007_data_flat006_step, block007_data_flat004_original, block007_data_flat005_original]
def block007_data_flat007 : CoefficientMerge.Poly := [(nat_lit 802, Int.ofNat (nat_lit 6517608960)), (nat_lit 803, Int.ofNat (nat_lit 6167040000)), (nat_lit 804, Int.ofNat (nat_lit 7979381760))]
theorem block007_data_flat007_step : block007_data_flat007 = (CoefficientMerge.fastMerge block007_data_flat003 block007_data_flat006) := by decide +kernel
theorem block007_data_flat007_original : block007_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6517608960 : Int) atom0497Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6167040000 : Int) atom0498Coded) (CoefficientMerge.scale (7979381760 : Int) atom0499Coded))) := by
  rw [block007_data_flat007_step, block007_data_flat003_original, block007_data_flat006_original]
def block007_data_flat008 : CoefficientMerge.Poly := [(nat_lit 800, Int.ofNat (nat_lit 3718671360)), (nat_lit 801, Int.ofNat (nat_lit 6793720320)), (nat_lit 802, Int.ofNat (nat_lit 6517608960)), (nat_lit 803, Int.ofNat (nat_lit 6167040000)), (nat_lit 804, Int.ofNat (nat_lit 7979381760))]
theorem block007_data_flat008_step : block007_data_flat008 = (CoefficientMerge.fastMerge block007_data_flat002 block007_data_flat007) := by decide +kernel
theorem block007_data_flat008_original : block007_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3718671360 : Int) atom0495Coded) (CoefficientMerge.scale (6793720320 : Int) atom0496Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6517608960 : Int) atom0497Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6167040000 : Int) atom0498Coded) (CoefficientMerge.scale (7979381760 : Int) atom0499Coded)))) := by
  rw [block007_data_flat008_step, block007_data_flat002_original, block007_data_flat007_original]
def block007_data_flat009 : CoefficientMerge.Poly := [(nat_lit 805, Int.ofNat (nat_lit 6566323200))]
theorem block007_data_flat009_step : block007_data_flat009 = (CoefficientMerge.scale (6566323200 : Int) atom0500Coded) := by decide +kernel
theorem block007_data_flat009_original : block007_data_flat009 = (CoefficientMerge.scale (6566323200 : Int) atom0500Coded) := by
  rw [block007_data_flat009_step]
def block007_data_flat010 : CoefficientMerge.Poly := [(nat_lit 806, Int.ofNat (nat_lit 8933124000))]
theorem block007_data_flat010_step : block007_data_flat010 = (CoefficientMerge.scale (8933124000 : Int) atom0501Coded) := by decide +kernel
theorem block007_data_flat010_original : block007_data_flat010 = (CoefficientMerge.scale (8933124000 : Int) atom0501Coded) := by
  rw [block007_data_flat010_step]
def block007_data_flat011 : CoefficientMerge.Poly := [(nat_lit 805, Int.ofNat (nat_lit 6566323200)), (nat_lit 806, Int.ofNat (nat_lit 8933124000))]
theorem block007_data_flat011_step : block007_data_flat011 = (CoefficientMerge.fastMerge block007_data_flat009 block007_data_flat010) := by decide +kernel
theorem block007_data_flat011_original : block007_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6566323200 : Int) atom0500Coded) (CoefficientMerge.scale (8933124000 : Int) atom0501Coded)) := by
  rw [block007_data_flat011_step, block007_data_flat009_original, block007_data_flat010_original]
def block007_data_flat012 : CoefficientMerge.Poly := [(nat_lit 807, Int.ofNat (nat_lit 7949368320))]
theorem block007_data_flat012_step : block007_data_flat012 = (CoefficientMerge.scale (7949368320 : Int) atom0502Coded) := by decide +kernel
theorem block007_data_flat012_original : block007_data_flat012 = (CoefficientMerge.scale (7949368320 : Int) atom0502Coded) := by
  rw [block007_data_flat012_step]
def block007_data_flat013 : CoefficientMerge.Poly := [(nat_lit 808, Int.ofNat (nat_lit 8692055040))]
theorem block007_data_flat013_step : block007_data_flat013 = (CoefficientMerge.scale (8692055040 : Int) atom0503Coded) := by decide +kernel
theorem block007_data_flat013_original : block007_data_flat013 = (CoefficientMerge.scale (8692055040 : Int) atom0503Coded) := by
  rw [block007_data_flat013_step]
def block007_data_flat014 : CoefficientMerge.Poly := [(nat_lit 809, Int.ofNat (nat_lit 10609182720))]
theorem block007_data_flat014_step : block007_data_flat014 = (CoefficientMerge.scale (10609182720 : Int) atom0504Coded) := by decide +kernel
theorem block007_data_flat014_original : block007_data_flat014 = (CoefficientMerge.scale (10609182720 : Int) atom0504Coded) := by
  rw [block007_data_flat014_step]
def block007_data_flat015 : CoefficientMerge.Poly := [(nat_lit 808, Int.ofNat (nat_lit 8692055040)), (nat_lit 809, Int.ofNat (nat_lit 10609182720))]
theorem block007_data_flat015_step : block007_data_flat015 = (CoefficientMerge.fastMerge block007_data_flat013 block007_data_flat014) := by decide +kernel
theorem block007_data_flat015_original : block007_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8692055040 : Int) atom0503Coded) (CoefficientMerge.scale (10609182720 : Int) atom0504Coded)) := by
  rw [block007_data_flat015_step, block007_data_flat013_original, block007_data_flat014_original]
def block007_data_flat016 : CoefficientMerge.Poly := [(nat_lit 807, Int.ofNat (nat_lit 7949368320)), (nat_lit 808, Int.ofNat (nat_lit 8692055040)), (nat_lit 809, Int.ofNat (nat_lit 10609182720))]
theorem block007_data_flat016_step : block007_data_flat016 = (CoefficientMerge.fastMerge block007_data_flat012 block007_data_flat015) := by decide +kernel
theorem block007_data_flat016_original : block007_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7949368320 : Int) atom0502Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8692055040 : Int) atom0503Coded) (CoefficientMerge.scale (10609182720 : Int) atom0504Coded))) := by
  rw [block007_data_flat016_step, block007_data_flat012_original, block007_data_flat015_original]
def block007_data_flat017 : CoefficientMerge.Poly := [(nat_lit 805, Int.ofNat (nat_lit 6566323200)), (nat_lit 806, Int.ofNat (nat_lit 8933124000)), (nat_lit 807, Int.ofNat (nat_lit 7949368320)), (nat_lit 808, Int.ofNat (nat_lit 8692055040)), (nat_lit 809, Int.ofNat (nat_lit 10609182720))]
theorem block007_data_flat017_step : block007_data_flat017 = (CoefficientMerge.fastMerge block007_data_flat011 block007_data_flat016) := by decide +kernel
theorem block007_data_flat017_original : block007_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6566323200 : Int) atom0500Coded) (CoefficientMerge.scale (8933124000 : Int) atom0501Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7949368320 : Int) atom0502Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8692055040 : Int) atom0503Coded) (CoefficientMerge.scale (10609182720 : Int) atom0504Coded)))) := by
  rw [block007_data_flat017_step, block007_data_flat011_original, block007_data_flat016_original]
def block007_data_flat018 : CoefficientMerge.Poly := [(nat_lit 800, Int.ofNat (nat_lit 3718671360)), (nat_lit 801, Int.ofNat (nat_lit 6793720320)), (nat_lit 802, Int.ofNat (nat_lit 6517608960)), (nat_lit 803, Int.ofNat (nat_lit 6167040000)), (nat_lit 804, Int.ofNat (nat_lit 7979381760)), (nat_lit 805, Int.ofNat (nat_lit 6566323200)), (nat_lit 806, Int.ofNat (nat_lit 8933124000)), (nat_lit 807, Int.ofNat (nat_lit 7949368320)), (nat_lit 808, Int.ofNat (nat_lit 8692055040)), (nat_lit 809, Int.ofNat (nat_lit 10609182720))]
theorem block007_data_flat018_step : block007_data_flat018 = (CoefficientMerge.fastMerge block007_data_flat008 block007_data_flat017) := by decide +kernel
theorem block007_data_flat018_original : block007_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3718671360 : Int) atom0495Coded) (CoefficientMerge.scale (6793720320 : Int) atom0496Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6517608960 : Int) atom0497Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6167040000 : Int) atom0498Coded) (CoefficientMerge.scale (7979381760 : Int) atom0499Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6566323200 : Int) atom0500Coded) (CoefficientMerge.scale (8933124000 : Int) atom0501Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7949368320 : Int) atom0502Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8692055040 : Int) atom0503Coded) (CoefficientMerge.scale (10609182720 : Int) atom0504Coded))))) := by
  rw [block007_data_flat018_step, block007_data_flat008_original, block007_data_flat017_original]
def block007_data_flat019 : CoefficientMerge.Poly := [(nat_lit 819, Int.ofNat (nat_lit 4164011520))]
theorem block007_data_flat019_step : block007_data_flat019 = (CoefficientMerge.scale (4164011520 : Int) atom0505Coded) := by decide +kernel
theorem block007_data_flat019_original : block007_data_flat019 = (CoefficientMerge.scale (4164011520 : Int) atom0505Coded) := by
  rw [block007_data_flat019_step]
def block007_data_flat020 : CoefficientMerge.Poly := [(nat_lit 820, Int.ofNat (nat_lit 7503144960))]
theorem block007_data_flat020_step : block007_data_flat020 = (CoefficientMerge.scale (7503144960 : Int) atom0506Coded) := by decide +kernel
theorem block007_data_flat020_original : block007_data_flat020 = (CoefficientMerge.scale (7503144960 : Int) atom0506Coded) := by
  rw [block007_data_flat020_step]
def block007_data_flat021 : CoefficientMerge.Poly := [(nat_lit 819, Int.ofNat (nat_lit 4164011520)), (nat_lit 820, Int.ofNat (nat_lit 7503144960))]
theorem block007_data_flat021_step : block007_data_flat021 = (CoefficientMerge.fastMerge block007_data_flat019 block007_data_flat020) := by decide +kernel
theorem block007_data_flat021_original : block007_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4164011520 : Int) atom0505Coded) (CoefficientMerge.scale (7503144960 : Int) atom0506Coded)) := by
  rw [block007_data_flat021_step, block007_data_flat019_original, block007_data_flat020_original]
def block007_data_flat022 : CoefficientMerge.Poly := [(nat_lit 821, Int.ofNat (nat_lit 6954524160))]
theorem block007_data_flat022_step : block007_data_flat022 = (CoefficientMerge.scale (6954524160 : Int) atom0507Coded) := by decide +kernel
theorem block007_data_flat022_original : block007_data_flat022 = (CoefficientMerge.scale (6954524160 : Int) atom0507Coded) := by
  rw [block007_data_flat022_step]
def block007_data_flat023 : CoefficientMerge.Poly := [(nat_lit 822, Int.ofNat (nat_lit 8592628800))]
theorem block007_data_flat023_step : block007_data_flat023 = (CoefficientMerge.scale (8592628800 : Int) atom0508Coded) := by decide +kernel
theorem block007_data_flat023_original : block007_data_flat023 = (CoefficientMerge.scale (8592628800 : Int) atom0508Coded) := by
  rw [block007_data_flat023_step]
def block007_data_flat024 : CoefficientMerge.Poly := [(nat_lit 823, Int.ofNat (nat_lit 7029147840))]
theorem block007_data_flat024_step : block007_data_flat024 = (CoefficientMerge.scale (7029147840 : Int) atom0509Coded) := by decide +kernel
theorem block007_data_flat024_original : block007_data_flat024 = (CoefficientMerge.scale (7029147840 : Int) atom0509Coded) := by
  rw [block007_data_flat024_step]
def block007_data_flat025 : CoefficientMerge.Poly := [(nat_lit 822, Int.ofNat (nat_lit 8592628800)), (nat_lit 823, Int.ofNat (nat_lit 7029147840))]
theorem block007_data_flat025_step : block007_data_flat025 = (CoefficientMerge.fastMerge block007_data_flat023 block007_data_flat024) := by decide +kernel
theorem block007_data_flat025_original : block007_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8592628800 : Int) atom0508Coded) (CoefficientMerge.scale (7029147840 : Int) atom0509Coded)) := by
  rw [block007_data_flat025_step, block007_data_flat023_original, block007_data_flat024_original]
def block007_data_flat026 : CoefficientMerge.Poly := [(nat_lit 821, Int.ofNat (nat_lit 6954524160)), (nat_lit 822, Int.ofNat (nat_lit 8592628800)), (nat_lit 823, Int.ofNat (nat_lit 7029147840))]
theorem block007_data_flat026_step : block007_data_flat026 = (CoefficientMerge.fastMerge block007_data_flat022 block007_data_flat025) := by decide +kernel
theorem block007_data_flat026_original : block007_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6954524160 : Int) atom0507Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8592628800 : Int) atom0508Coded) (CoefficientMerge.scale (7029147840 : Int) atom0509Coded))) := by
  rw [block007_data_flat026_step, block007_data_flat022_original, block007_data_flat025_original]
def block007_data_flat027 : CoefficientMerge.Poly := [(nat_lit 819, Int.ofNat (nat_lit 4164011520)), (nat_lit 820, Int.ofNat (nat_lit 7503144960)), (nat_lit 821, Int.ofNat (nat_lit 6954524160)), (nat_lit 822, Int.ofNat (nat_lit 8592628800)), (nat_lit 823, Int.ofNat (nat_lit 7029147840))]
theorem block007_data_flat027_step : block007_data_flat027 = (CoefficientMerge.fastMerge block007_data_flat021 block007_data_flat026) := by decide +kernel
theorem block007_data_flat027_original : block007_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4164011520 : Int) atom0505Coded) (CoefficientMerge.scale (7503144960 : Int) atom0506Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6954524160 : Int) atom0507Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8592628800 : Int) atom0508Coded) (CoefficientMerge.scale (7029147840 : Int) atom0509Coded)))) := by
  rw [block007_data_flat027_step, block007_data_flat021_original, block007_data_flat026_original]
def block007_data_flat028 : CoefficientMerge.Poly := [(nat_lit 824, Int.ofNat (nat_lit 9631143840))]
theorem block007_data_flat028_step : block007_data_flat028 = (CoefficientMerge.scale (9631143840 : Int) atom0510Coded) := by decide +kernel
theorem block007_data_flat028_original : block007_data_flat028 = (CoefficientMerge.scale (9631143840 : Int) atom0510Coded) := by
  rw [block007_data_flat028_step]
def block007_data_flat029 : CoefficientMerge.Poly := [(nat_lit 825, Int.ofNat (nat_lit 8158977600))]
theorem block007_data_flat029_step : block007_data_flat029 = (CoefficientMerge.scale (8158977600 : Int) atom0511Coded) := by decide +kernel
theorem block007_data_flat029_original : block007_data_flat029 = (CoefficientMerge.scale (8158977600 : Int) atom0511Coded) := by
  rw [block007_data_flat029_step]
def block007_data_flat030 : CoefficientMerge.Poly := [(nat_lit 824, Int.ofNat (nat_lit 9631143840)), (nat_lit 825, Int.ofNat (nat_lit 8158977600))]
theorem block007_data_flat030_step : block007_data_flat030 = (CoefficientMerge.fastMerge block007_data_flat028 block007_data_flat029) := by decide +kernel
theorem block007_data_flat030_original : block007_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9631143840 : Int) atom0510Coded) (CoefficientMerge.scale (8158977600 : Int) atom0511Coded)) := by
  rw [block007_data_flat030_step, block007_data_flat028_original, block007_data_flat029_original]
def block007_data_flat031 : CoefficientMerge.Poly := [(nat_lit 826, Int.ofNat (nat_lit 8798871360))]
theorem block007_data_flat031_step : block007_data_flat031 = (CoefficientMerge.scale (8798871360 : Int) atom0512Coded) := by decide +kernel
theorem block007_data_flat031_original : block007_data_flat031 = (CoefficientMerge.scale (8798871360 : Int) atom0512Coded) := by
  rw [block007_data_flat031_step]
def block007_data_flat032 : CoefficientMerge.Poly := [(nat_lit 827, Int.ofNat (nat_lit 10613206080))]
theorem block007_data_flat032_step : block007_data_flat032 = (CoefficientMerge.scale (10613206080 : Int) atom0513Coded) := by decide +kernel
theorem block007_data_flat032_original : block007_data_flat032 = (CoefficientMerge.scale (10613206080 : Int) atom0513Coded) := by
  rw [block007_data_flat032_step]
def block007_data_flat033 : CoefficientMerge.Poly := [(nat_lit 838, Int.ofNat (nat_lit 4531960320))]
theorem block007_data_flat033_step : block007_data_flat033 = (CoefficientMerge.scale (4531960320 : Int) atom0514Coded) := by decide +kernel
theorem block007_data_flat033_original : block007_data_flat033 = (CoefficientMerge.scale (4531960320 : Int) atom0514Coded) := by
  rw [block007_data_flat033_step]
def block007_data_flat034 : CoefficientMerge.Poly := [(nat_lit 827, Int.ofNat (nat_lit 10613206080)), (nat_lit 838, Int.ofNat (nat_lit 4531960320))]
theorem block007_data_flat034_step : block007_data_flat034 = (CoefficientMerge.fastMerge block007_data_flat032 block007_data_flat033) := by decide +kernel
theorem block007_data_flat034_original : block007_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10613206080 : Int) atom0513Coded) (CoefficientMerge.scale (4531960320 : Int) atom0514Coded)) := by
  rw [block007_data_flat034_step, block007_data_flat032_original, block007_data_flat033_original]
def block007_data_flat035 : CoefficientMerge.Poly := [(nat_lit 826, Int.ofNat (nat_lit 8798871360)), (nat_lit 827, Int.ofNat (nat_lit 10613206080)), (nat_lit 838, Int.ofNat (nat_lit 4531960320))]
theorem block007_data_flat035_step : block007_data_flat035 = (CoefficientMerge.fastMerge block007_data_flat031 block007_data_flat034) := by decide +kernel
theorem block007_data_flat035_original : block007_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8798871360 : Int) atom0512Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10613206080 : Int) atom0513Coded) (CoefficientMerge.scale (4531960320 : Int) atom0514Coded))) := by
  rw [block007_data_flat035_step, block007_data_flat031_original, block007_data_flat034_original]
def block007_data_flat036 : CoefficientMerge.Poly := [(nat_lit 824, Int.ofNat (nat_lit 9631143840)), (nat_lit 825, Int.ofNat (nat_lit 8158977600)), (nat_lit 826, Int.ofNat (nat_lit 8798871360)), (nat_lit 827, Int.ofNat (nat_lit 10613206080)), (nat_lit 838, Int.ofNat (nat_lit 4531960320))]
theorem block007_data_flat036_step : block007_data_flat036 = (CoefficientMerge.fastMerge block007_data_flat030 block007_data_flat035) := by decide +kernel
theorem block007_data_flat036_original : block007_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9631143840 : Int) atom0510Coded) (CoefficientMerge.scale (8158977600 : Int) atom0511Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8798871360 : Int) atom0512Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10613206080 : Int) atom0513Coded) (CoefficientMerge.scale (4531960320 : Int) atom0514Coded)))) := by
  rw [block007_data_flat036_step, block007_data_flat030_original, block007_data_flat035_original]
def block007_data_flat037 : CoefficientMerge.Poly := [(nat_lit 819, Int.ofNat (nat_lit 4164011520)), (nat_lit 820, Int.ofNat (nat_lit 7503144960)), (nat_lit 821, Int.ofNat (nat_lit 6954524160)), (nat_lit 822, Int.ofNat (nat_lit 8592628800)), (nat_lit 823, Int.ofNat (nat_lit 7029147840)), (nat_lit 824, Int.ofNat (nat_lit 9631143840)), (nat_lit 825, Int.ofNat (nat_lit 8158977600)), (nat_lit 826, Int.ofNat (nat_lit 8798871360)), (nat_lit 827, Int.ofNat (nat_lit 10613206080)), (nat_lit 838, Int.ofNat (nat_lit 4531960320))]
theorem block007_data_flat037_step : block007_data_flat037 = (CoefficientMerge.fastMerge block007_data_flat027 block007_data_flat036) := by decide +kernel
theorem block007_data_flat037_original : block007_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4164011520 : Int) atom0505Coded) (CoefficientMerge.scale (7503144960 : Int) atom0506Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6954524160 : Int) atom0507Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8592628800 : Int) atom0508Coded) (CoefficientMerge.scale (7029147840 : Int) atom0509Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9631143840 : Int) atom0510Coded) (CoefficientMerge.scale (8158977600 : Int) atom0511Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8798871360 : Int) atom0512Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10613206080 : Int) atom0513Coded) (CoefficientMerge.scale (4531960320 : Int) atom0514Coded))))) := by
  rw [block007_data_flat037_step, block007_data_flat027_original, block007_data_flat036_original]
def block007_data_flat038 : CoefficientMerge.Poly := [(nat_lit 800, Int.ofNat (nat_lit 3718671360)), (nat_lit 801, Int.ofNat (nat_lit 6793720320)), (nat_lit 802, Int.ofNat (nat_lit 6517608960)), (nat_lit 803, Int.ofNat (nat_lit 6167040000)), (nat_lit 804, Int.ofNat (nat_lit 7979381760)), (nat_lit 805, Int.ofNat (nat_lit 6566323200)), (nat_lit 806, Int.ofNat (nat_lit 8933124000)), (nat_lit 807, Int.ofNat (nat_lit 7949368320)), (nat_lit 808, Int.ofNat (nat_lit 8692055040)), (nat_lit 809, Int.ofNat (nat_lit 10609182720)), (nat_lit 819, Int.ofNat (nat_lit 4164011520)), (nat_lit 820, Int.ofNat (nat_lit 7503144960)), (nat_lit 821, Int.ofNat (nat_lit 6954524160)), (nat_lit 822, Int.ofNat (nat_lit 8592628800)), (nat_lit 823, Int.ofNat (nat_lit 7029147840)), (nat_lit 824, Int.ofNat (nat_lit 9631143840)), (nat_lit 825, Int.ofNat (nat_lit 8158977600)), (nat_lit 826, Int.ofNat (nat_lit 8798871360)), (nat_lit 827, Int.ofNat (nat_lit 10613206080)), (nat_lit 838, Int.ofNat (nat_lit 4531960320))]
theorem block007_data_flat038_step : block007_data_flat038 = (CoefficientMerge.fastMerge block007_data_flat018 block007_data_flat037) := by decide +kernel
theorem block007_data_flat038_original : block007_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3718671360 : Int) atom0495Coded) (CoefficientMerge.scale (6793720320 : Int) atom0496Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6517608960 : Int) atom0497Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6167040000 : Int) atom0498Coded) (CoefficientMerge.scale (7979381760 : Int) atom0499Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6566323200 : Int) atom0500Coded) (CoefficientMerge.scale (8933124000 : Int) atom0501Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7949368320 : Int) atom0502Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8692055040 : Int) atom0503Coded) (CoefficientMerge.scale (10609182720 : Int) atom0504Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4164011520 : Int) atom0505Coded) (CoefficientMerge.scale (7503144960 : Int) atom0506Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6954524160 : Int) atom0507Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8592628800 : Int) atom0508Coded) (CoefficientMerge.scale (7029147840 : Int) atom0509Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9631143840 : Int) atom0510Coded) (CoefficientMerge.scale (8158977600 : Int) atom0511Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8798871360 : Int) atom0512Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10613206080 : Int) atom0513Coded) (CoefficientMerge.scale (4531960320 : Int) atom0514Coded)))))) := by
  rw [block007_data_flat038_step, block007_data_flat018_original, block007_data_flat037_original]
def block007_data_flat039 : CoefficientMerge.Poly := [(nat_lit 839, Int.ofNat (nat_lit 7932940800))]
theorem block007_data_flat039_step : block007_data_flat039 = (CoefficientMerge.scale (7932940800 : Int) atom0515Coded) := by decide +kernel
theorem block007_data_flat039_original : block007_data_flat039 = (CoefficientMerge.scale (7932940800 : Int) atom0515Coded) := by
  rw [block007_data_flat039_step]
def block007_data_flat040 : CoefficientMerge.Poly := [(nat_lit 840, Int.ofNat (nat_lit 9311655360))]
theorem block007_data_flat040_step : block007_data_flat040 = (CoefficientMerge.scale (9311655360 : Int) atom0516Coded) := by decide +kernel
theorem block007_data_flat040_original : block007_data_flat040 = (CoefficientMerge.scale (9311655360 : Int) atom0516Coded) := by
  rw [block007_data_flat040_step]
def block007_data_flat041 : CoefficientMerge.Poly := [(nat_lit 839, Int.ofNat (nat_lit 7932940800)), (nat_lit 840, Int.ofNat (nat_lit 9311655360))]
theorem block007_data_flat041_step : block007_data_flat041 = (CoefficientMerge.fastMerge block007_data_flat039 block007_data_flat040) := by decide +kernel
theorem block007_data_flat041_original : block007_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7932940800 : Int) atom0515Coded) (CoefficientMerge.scale (9311655360 : Int) atom0516Coded)) := by
  rw [block007_data_flat041_step, block007_data_flat039_original, block007_data_flat040_original]
def block007_data_flat042 : CoefficientMerge.Poly := [(nat_lit 841, Int.ofNat (nat_lit 7477765440))]
theorem block007_data_flat042_step : block007_data_flat042 = (CoefficientMerge.scale (7477765440 : Int) atom0517Coded) := by decide +kernel
theorem block007_data_flat042_original : block007_data_flat042 = (CoefficientMerge.scale (7477765440 : Int) atom0517Coded) := by
  rw [block007_data_flat042_step]
def block007_data_flat043 : CoefficientMerge.Poly := [(nat_lit 842, Int.ofNat (nat_lit 10379483040))]
theorem block007_data_flat043_step : block007_data_flat043 = (CoefficientMerge.scale (10379483040 : Int) atom0518Coded) := by decide +kernel
theorem block007_data_flat043_original : block007_data_flat043 = (CoefficientMerge.scale (10379483040 : Int) atom0518Coded) := by
  rw [block007_data_flat043_step]
def block007_data_flat044 : CoefficientMerge.Poly := [(nat_lit 843, Int.ofNat (nat_lit 8044739520))]
theorem block007_data_flat044_step : block007_data_flat044 = (CoefficientMerge.scale (8044739520 : Int) atom0519Coded) := by decide +kernel
theorem block007_data_flat044_original : block007_data_flat044 = (CoefficientMerge.scale (8044739520 : Int) atom0519Coded) := by
  rw [block007_data_flat044_step]
def block007_data_flat045 : CoefficientMerge.Poly := [(nat_lit 842, Int.ofNat (nat_lit 10379483040)), (nat_lit 843, Int.ofNat (nat_lit 8044739520))]
theorem block007_data_flat045_step : block007_data_flat045 = (CoefficientMerge.fastMerge block007_data_flat043 block007_data_flat044) := by decide +kernel
theorem block007_data_flat045_original : block007_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10379483040 : Int) atom0518Coded) (CoefficientMerge.scale (8044739520 : Int) atom0519Coded)) := by
  rw [block007_data_flat045_step, block007_data_flat043_original, block007_data_flat044_original]
def block007_data_flat046 : CoefficientMerge.Poly := [(nat_lit 841, Int.ofNat (nat_lit 7477765440)), (nat_lit 842, Int.ofNat (nat_lit 10379483040)), (nat_lit 843, Int.ofNat (nat_lit 8044739520))]
theorem block007_data_flat046_step : block007_data_flat046 = (CoefficientMerge.fastMerge block007_data_flat042 block007_data_flat045) := by decide +kernel
theorem block007_data_flat046_original : block007_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7477765440 : Int) atom0517Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10379483040 : Int) atom0518Coded) (CoefficientMerge.scale (8044739520 : Int) atom0519Coded))) := by
  rw [block007_data_flat046_step, block007_data_flat042_original, block007_data_flat045_original]
def block007_data_flat047 : CoefficientMerge.Poly := [(nat_lit 839, Int.ofNat (nat_lit 7932940800)), (nat_lit 840, Int.ofNat (nat_lit 9311655360)), (nat_lit 841, Int.ofNat (nat_lit 7477765440)), (nat_lit 842, Int.ofNat (nat_lit 10379483040)), (nat_lit 843, Int.ofNat (nat_lit 8044739520))]
theorem block007_data_flat047_step : block007_data_flat047 = (CoefficientMerge.fastMerge block007_data_flat041 block007_data_flat046) := by decide +kernel
theorem block007_data_flat047_original : block007_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7932940800 : Int) atom0515Coded) (CoefficientMerge.scale (9311655360 : Int) atom0516Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7477765440 : Int) atom0517Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10379483040 : Int) atom0518Coded) (CoefficientMerge.scale (8044739520 : Int) atom0519Coded)))) := by
  rw [block007_data_flat047_step, block007_data_flat041_original, block007_data_flat046_original]
def block007_data_flat048 : CoefficientMerge.Poly := [(nat_lit 844, Int.ofNat (nat_lit 8392186560))]
theorem block007_data_flat048_step : block007_data_flat048 = (CoefficientMerge.scale (8392186560 : Int) atom0520Coded) := by decide +kernel
theorem block007_data_flat048_original : block007_data_flat048 = (CoefficientMerge.scale (8392186560 : Int) atom0520Coded) := by
  rw [block007_data_flat048_step]
def block007_data_flat049 : CoefficientMerge.Poly := [(nat_lit 845, Int.ofNat (nat_lit 10204830720))]
theorem block007_data_flat049_step : block007_data_flat049 = (CoefficientMerge.scale (10204830720 : Int) atom0521Coded) := by decide +kernel
theorem block007_data_flat049_original : block007_data_flat049 = (CoefficientMerge.scale (10204830720 : Int) atom0521Coded) := by
  rw [block007_data_flat049_step]
def block007_data_flat050 : CoefficientMerge.Poly := [(nat_lit 844, Int.ofNat (nat_lit 8392186560)), (nat_lit 845, Int.ofNat (nat_lit 10204830720))]
theorem block007_data_flat050_step : block007_data_flat050 = (CoefficientMerge.fastMerge block007_data_flat048 block007_data_flat049) := by decide +kernel
theorem block007_data_flat050_original : block007_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8392186560 : Int) atom0520Coded) (CoefficientMerge.scale (10204830720 : Int) atom0521Coded)) := by
  rw [block007_data_flat050_step, block007_data_flat048_original, block007_data_flat049_original]
def block007_data_flat051 : CoefficientMerge.Poly := [(nat_lit 857, Int.ofNat (nat_lit 4927426560))]
theorem block007_data_flat051_step : block007_data_flat051 = (CoefficientMerge.scale (4927426560 : Int) atom0522Coded) := by decide +kernel
theorem block007_data_flat051_original : block007_data_flat051 = (CoefficientMerge.scale (4927426560 : Int) atom0522Coded) := by
  rw [block007_data_flat051_step]
def block007_data_flat052 : CoefficientMerge.Poly := [(nat_lit 858, Int.ofNat (nat_lit 9870336000))]
theorem block007_data_flat052_step : block007_data_flat052 = (CoefficientMerge.scale (9870336000 : Int) atom0523Coded) := by decide +kernel
theorem block007_data_flat052_original : block007_data_flat052 = (CoefficientMerge.scale (9870336000 : Int) atom0523Coded) := by
  rw [block007_data_flat052_step]
def block007_data_flat053 : CoefficientMerge.Poly := [(nat_lit 859, Int.ofNat (nat_lit 7722086400))]
theorem block007_data_flat053_step : block007_data_flat053 = (CoefficientMerge.scale (7722086400 : Int) atom0524Coded) := by decide +kernel
theorem block007_data_flat053_original : block007_data_flat053 = (CoefficientMerge.scale (7722086400 : Int) atom0524Coded) := by
  rw [block007_data_flat053_step]
def block007_data_flat054 : CoefficientMerge.Poly := [(nat_lit 858, Int.ofNat (nat_lit 9870336000)), (nat_lit 859, Int.ofNat (nat_lit 7722086400))]
theorem block007_data_flat054_step : block007_data_flat054 = (CoefficientMerge.fastMerge block007_data_flat052 block007_data_flat053) := by decide +kernel
theorem block007_data_flat054_original : block007_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9870336000 : Int) atom0523Coded) (CoefficientMerge.scale (7722086400 : Int) atom0524Coded)) := by
  rw [block007_data_flat054_step, block007_data_flat052_original, block007_data_flat053_original]
def block007_data_flat055 : CoefficientMerge.Poly := [(nat_lit 857, Int.ofNat (nat_lit 4927426560)), (nat_lit 858, Int.ofNat (nat_lit 9870336000)), (nat_lit 859, Int.ofNat (nat_lit 7722086400))]
theorem block007_data_flat055_step : block007_data_flat055 = (CoefficientMerge.fastMerge block007_data_flat051 block007_data_flat054) := by decide +kernel
theorem block007_data_flat055_original : block007_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4927426560 : Int) atom0522Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9870336000 : Int) atom0523Coded) (CoefficientMerge.scale (7722086400 : Int) atom0524Coded))) := by
  rw [block007_data_flat055_step, block007_data_flat051_original, block007_data_flat054_original]
def block007_data_flat056 : CoefficientMerge.Poly := [(nat_lit 844, Int.ofNat (nat_lit 8392186560)), (nat_lit 845, Int.ofNat (nat_lit 10204830720)), (nat_lit 857, Int.ofNat (nat_lit 4927426560)), (nat_lit 858, Int.ofNat (nat_lit 9870336000)), (nat_lit 859, Int.ofNat (nat_lit 7722086400))]
theorem block007_data_flat056_step : block007_data_flat056 = (CoefficientMerge.fastMerge block007_data_flat050 block007_data_flat055) := by decide +kernel
theorem block007_data_flat056_original : block007_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8392186560 : Int) atom0520Coded) (CoefficientMerge.scale (10204830720 : Int) atom0521Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4927426560 : Int) atom0522Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9870336000 : Int) atom0523Coded) (CoefficientMerge.scale (7722086400 : Int) atom0524Coded)))) := by
  rw [block007_data_flat056_step, block007_data_flat050_original, block007_data_flat055_original]
def block007_data_flat057 : CoefficientMerge.Poly := [(nat_lit 839, Int.ofNat (nat_lit 7932940800)), (nat_lit 840, Int.ofNat (nat_lit 9311655360)), (nat_lit 841, Int.ofNat (nat_lit 7477765440)), (nat_lit 842, Int.ofNat (nat_lit 10379483040)), (nat_lit 843, Int.ofNat (nat_lit 8044739520)), (nat_lit 844, Int.ofNat (nat_lit 8392186560)), (nat_lit 845, Int.ofNat (nat_lit 10204830720)), (nat_lit 857, Int.ofNat (nat_lit 4927426560)), (nat_lit 858, Int.ofNat (nat_lit 9870336000)), (nat_lit 859, Int.ofNat (nat_lit 7722086400))]
theorem block007_data_flat057_step : block007_data_flat057 = (CoefficientMerge.fastMerge block007_data_flat047 block007_data_flat056) := by decide +kernel
theorem block007_data_flat057_original : block007_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7932940800 : Int) atom0515Coded) (CoefficientMerge.scale (9311655360 : Int) atom0516Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7477765440 : Int) atom0517Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10379483040 : Int) atom0518Coded) (CoefficientMerge.scale (8044739520 : Int) atom0519Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8392186560 : Int) atom0520Coded) (CoefficientMerge.scale (10204830720 : Int) atom0521Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4927426560 : Int) atom0522Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9870336000 : Int) atom0523Coded) (CoefficientMerge.scale (7722086400 : Int) atom0524Coded))))) := by
  rw [block007_data_flat057_step, block007_data_flat047_original, block007_data_flat056_original]
def block007_data_flat058 : CoefficientMerge.Poly := [(nat_lit 860, Int.ofNat (nat_lit 10978907040))]
theorem block007_data_flat058_step : block007_data_flat058 = (CoefficientMerge.scale (10978907040 : Int) atom0525Coded) := by decide +kernel
theorem block007_data_flat058_original : block007_data_flat058 = (CoefficientMerge.scale (10978907040 : Int) atom0525Coded) := by
  rw [block007_data_flat058_step]
def block007_data_flat059 : CoefficientMerge.Poly := [(nat_lit 861, Int.ofNat (nat_lit 8678154240))]
theorem block007_data_flat059_step : block007_data_flat059 = (CoefficientMerge.scale (8678154240 : Int) atom0526Coded) := by decide +kernel
theorem block007_data_flat059_original : block007_data_flat059 = (CoefficientMerge.scale (8678154240 : Int) atom0526Coded) := by
  rw [block007_data_flat059_step]
def block007_data_flat060 : CoefficientMerge.Poly := [(nat_lit 860, Int.ofNat (nat_lit 10978907040)), (nat_lit 861, Int.ofNat (nat_lit 8678154240))]
theorem block007_data_flat060_step : block007_data_flat060 = (CoefficientMerge.fastMerge block007_data_flat058 block007_data_flat059) := by decide +kernel
theorem block007_data_flat060_original : block007_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10978907040 : Int) atom0525Coded) (CoefficientMerge.scale (8678154240 : Int) atom0526Coded)) := by
  rw [block007_data_flat060_step, block007_data_flat058_original, block007_data_flat059_original]
def block007_data_flat061 : CoefficientMerge.Poly := [(nat_lit 862, Int.ofNat (nat_lit 7662090240))]
theorem block007_data_flat061_step : block007_data_flat061 = (CoefficientMerge.scale (7662090240 : Int) atom0527Coded) := by decide +kernel
theorem block007_data_flat061_original : block007_data_flat061 = (CoefficientMerge.scale (7662090240 : Int) atom0527Coded) := by
  rw [block007_data_flat061_step]
def block007_data_flat062 : CoefficientMerge.Poly := [(nat_lit 863, Int.ofNat (nat_lit 11373788160))]
theorem block007_data_flat062_step : block007_data_flat062 = (CoefficientMerge.scale (11373788160 : Int) atom0528Coded) := by decide +kernel
theorem block007_data_flat062_original : block007_data_flat062 = (CoefficientMerge.scale (11373788160 : Int) atom0528Coded) := by
  rw [block007_data_flat062_step]
def block007_data_flat063 : CoefficientMerge.Poly := [(nat_lit 876, Int.ofNat (nat_lit 6543452160))]
theorem block007_data_flat063_step : block007_data_flat063 = (CoefficientMerge.scale (6543452160 : Int) atom0529Coded) := by decide +kernel
theorem block007_data_flat063_original : block007_data_flat063 = (CoefficientMerge.scale (6543452160 : Int) atom0529Coded) := by
  rw [block007_data_flat063_step]
def block007_data_flat064 : CoefficientMerge.Poly := [(nat_lit 863, Int.ofNat (nat_lit 11373788160)), (nat_lit 876, Int.ofNat (nat_lit 6543452160))]
theorem block007_data_flat064_step : block007_data_flat064 = (CoefficientMerge.fastMerge block007_data_flat062 block007_data_flat063) := by decide +kernel
theorem block007_data_flat064_original : block007_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11373788160 : Int) atom0528Coded) (CoefficientMerge.scale (6543452160 : Int) atom0529Coded)) := by
  rw [block007_data_flat064_step, block007_data_flat062_original, block007_data_flat063_original]
def block007_data_flat065 : CoefficientMerge.Poly := [(nat_lit 862, Int.ofNat (nat_lit 7662090240)), (nat_lit 863, Int.ofNat (nat_lit 11373788160)), (nat_lit 876, Int.ofNat (nat_lit 6543452160))]
theorem block007_data_flat065_step : block007_data_flat065 = (CoefficientMerge.fastMerge block007_data_flat061 block007_data_flat064) := by decide +kernel
theorem block007_data_flat065_original : block007_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7662090240 : Int) atom0527Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11373788160 : Int) atom0528Coded) (CoefficientMerge.scale (6543452160 : Int) atom0529Coded))) := by
  rw [block007_data_flat065_step, block007_data_flat061_original, block007_data_flat064_original]
def block007_data_flat066 : CoefficientMerge.Poly := [(nat_lit 860, Int.ofNat (nat_lit 10978907040)), (nat_lit 861, Int.ofNat (nat_lit 8678154240)), (nat_lit 862, Int.ofNat (nat_lit 7662090240)), (nat_lit 863, Int.ofNat (nat_lit 11373788160)), (nat_lit 876, Int.ofNat (nat_lit 6543452160))]
theorem block007_data_flat066_step : block007_data_flat066 = (CoefficientMerge.fastMerge block007_data_flat060 block007_data_flat065) := by decide +kernel
theorem block007_data_flat066_original : block007_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10978907040 : Int) atom0525Coded) (CoefficientMerge.scale (8678154240 : Int) atom0526Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7662090240 : Int) atom0527Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11373788160 : Int) atom0528Coded) (CoefficientMerge.scale (6543452160 : Int) atom0529Coded)))) := by
  rw [block007_data_flat066_step, block007_data_flat060_original, block007_data_flat065_original]
def block007_data_flat067 : CoefficientMerge.Poly := [(nat_lit 877, Int.ofNat (nat_lit 10721894400))]
theorem block007_data_flat067_step : block007_data_flat067 = (CoefficientMerge.scale (10721894400 : Int) atom0530Coded) := by decide +kernel
theorem block007_data_flat067_original : block007_data_flat067 = (CoefficientMerge.scale (10721894400 : Int) atom0530Coded) := by
  rw [block007_data_flat067_step]
def block007_data_flat068 : CoefficientMerge.Poly := [(nat_lit 878, Int.ofNat (nat_lit 15248311200))]
theorem block007_data_flat068_step : block007_data_flat068 = (CoefficientMerge.scale (15248311200 : Int) atom0531Coded) := by decide +kernel
theorem block007_data_flat068_original : block007_data_flat068 = (CoefficientMerge.scale (15248311200 : Int) atom0531Coded) := by
  rw [block007_data_flat068_step]
def block007_data_flat069 : CoefficientMerge.Poly := [(nat_lit 877, Int.ofNat (nat_lit 10721894400)), (nat_lit 878, Int.ofNat (nat_lit 15248311200))]
theorem block007_data_flat069_step : block007_data_flat069 = (CoefficientMerge.fastMerge block007_data_flat067 block007_data_flat068) := by decide +kernel
theorem block007_data_flat069_original : block007_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10721894400 : Int) atom0530Coded) (CoefficientMerge.scale (15248311200 : Int) atom0531Coded)) := by
  rw [block007_data_flat069_step, block007_data_flat067_original, block007_data_flat068_original]
def block007_data_flat070 : CoefficientMerge.Poly := [(nat_lit 879, Int.ofNat (nat_lit 13098516480))]
theorem block007_data_flat070_step : block007_data_flat070 = (CoefficientMerge.scale (13098516480 : Int) atom0532Coded) := by decide +kernel
theorem block007_data_flat070_original : block007_data_flat070 = (CoefficientMerge.scale (13098516480 : Int) atom0532Coded) := by
  rw [block007_data_flat070_step]
def block007_data_flat071 : CoefficientMerge.Poly := [(nat_lit 880, Int.ofNat (nat_lit 7930137600))]
theorem block007_data_flat071_step : block007_data_flat071 = (CoefficientMerge.scale (7930137600 : Int) atom0533Coded) := by decide +kernel
theorem block007_data_flat071_original : block007_data_flat071 = (CoefficientMerge.scale (7930137600 : Int) atom0533Coded) := by
  rw [block007_data_flat071_step]
def block007_data_flat072 : CoefficientMerge.Poly := [(nat_lit 881, Int.ofNat (nat_lit 12465129600))]
theorem block007_data_flat072_step : block007_data_flat072 = (CoefficientMerge.scale (12465129600 : Int) atom0534Coded) := by decide +kernel
theorem block007_data_flat072_original : block007_data_flat072 = (CoefficientMerge.scale (12465129600 : Int) atom0534Coded) := by
  rw [block007_data_flat072_step]
def block007_data_flat073 : CoefficientMerge.Poly := [(nat_lit 880, Int.ofNat (nat_lit 7930137600)), (nat_lit 881, Int.ofNat (nat_lit 12465129600))]
theorem block007_data_flat073_step : block007_data_flat073 = (CoefficientMerge.fastMerge block007_data_flat071 block007_data_flat072) := by decide +kernel
theorem block007_data_flat073_original : block007_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7930137600 : Int) atom0533Coded) (CoefficientMerge.scale (12465129600 : Int) atom0534Coded)) := by
  rw [block007_data_flat073_step, block007_data_flat071_original, block007_data_flat072_original]
def block007_data_flat074 : CoefficientMerge.Poly := [(nat_lit 879, Int.ofNat (nat_lit 13098516480)), (nat_lit 880, Int.ofNat (nat_lit 7930137600)), (nat_lit 881, Int.ofNat (nat_lit 12465129600))]
theorem block007_data_flat074_step : block007_data_flat074 = (CoefficientMerge.fastMerge block007_data_flat070 block007_data_flat073) := by decide +kernel
theorem block007_data_flat074_original : block007_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13098516480 : Int) atom0532Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7930137600 : Int) atom0533Coded) (CoefficientMerge.scale (12465129600 : Int) atom0534Coded))) := by
  rw [block007_data_flat074_step, block007_data_flat070_original, block007_data_flat073_original]
def block007_data_flat075 : CoefficientMerge.Poly := [(nat_lit 877, Int.ofNat (nat_lit 10721894400)), (nat_lit 878, Int.ofNat (nat_lit 15248311200)), (nat_lit 879, Int.ofNat (nat_lit 13098516480)), (nat_lit 880, Int.ofNat (nat_lit 7930137600)), (nat_lit 881, Int.ofNat (nat_lit 12465129600))]
theorem block007_data_flat075_step : block007_data_flat075 = (CoefficientMerge.fastMerge block007_data_flat069 block007_data_flat074) := by decide +kernel
theorem block007_data_flat075_original : block007_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10721894400 : Int) atom0530Coded) (CoefficientMerge.scale (15248311200 : Int) atom0531Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13098516480 : Int) atom0532Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7930137600 : Int) atom0533Coded) (CoefficientMerge.scale (12465129600 : Int) atom0534Coded)))) := by
  rw [block007_data_flat075_step, block007_data_flat069_original, block007_data_flat074_original]
def block007_data_flat076 : CoefficientMerge.Poly := [(nat_lit 860, Int.ofNat (nat_lit 10978907040)), (nat_lit 861, Int.ofNat (nat_lit 8678154240)), (nat_lit 862, Int.ofNat (nat_lit 7662090240)), (nat_lit 863, Int.ofNat (nat_lit 11373788160)), (nat_lit 876, Int.ofNat (nat_lit 6543452160)), (nat_lit 877, Int.ofNat (nat_lit 10721894400)), (nat_lit 878, Int.ofNat (nat_lit 15248311200)), (nat_lit 879, Int.ofNat (nat_lit 13098516480)), (nat_lit 880, Int.ofNat (nat_lit 7930137600)), (nat_lit 881, Int.ofNat (nat_lit 12465129600))]
theorem block007_data_flat076_step : block007_data_flat076 = (CoefficientMerge.fastMerge block007_data_flat066 block007_data_flat075) := by decide +kernel
theorem block007_data_flat076_original : block007_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10978907040 : Int) atom0525Coded) (CoefficientMerge.scale (8678154240 : Int) atom0526Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7662090240 : Int) atom0527Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11373788160 : Int) atom0528Coded) (CoefficientMerge.scale (6543452160 : Int) atom0529Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10721894400 : Int) atom0530Coded) (CoefficientMerge.scale (15248311200 : Int) atom0531Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13098516480 : Int) atom0532Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7930137600 : Int) atom0533Coded) (CoefficientMerge.scale (12465129600 : Int) atom0534Coded))))) := by
  rw [block007_data_flat076_step, block007_data_flat066_original, block007_data_flat075_original]
def block007_data_flat077 : CoefficientMerge.Poly := [(nat_lit 839, Int.ofNat (nat_lit 7932940800)), (nat_lit 840, Int.ofNat (nat_lit 9311655360)), (nat_lit 841, Int.ofNat (nat_lit 7477765440)), (nat_lit 842, Int.ofNat (nat_lit 10379483040)), (nat_lit 843, Int.ofNat (nat_lit 8044739520)), (nat_lit 844, Int.ofNat (nat_lit 8392186560)), (nat_lit 845, Int.ofNat (nat_lit 10204830720)), (nat_lit 857, Int.ofNat (nat_lit 4927426560)), (nat_lit 858, Int.ofNat (nat_lit 9870336000)), (nat_lit 859, Int.ofNat (nat_lit 7722086400)), (nat_lit 860, Int.ofNat (nat_lit 10978907040)), (nat_lit 861, Int.ofNat (nat_lit 8678154240)), (nat_lit 862, Int.ofNat (nat_lit 7662090240)), (nat_lit 863, Int.ofNat (nat_lit 11373788160)), (nat_lit 876, Int.ofNat (nat_lit 6543452160)), (nat_lit 877, Int.ofNat (nat_lit 10721894400)), (nat_lit 878, Int.ofNat (nat_lit 15248311200)), (nat_lit 879, Int.ofNat (nat_lit 13098516480)), (nat_lit 880, Int.ofNat (nat_lit 7930137600)), (nat_lit 881, Int.ofNat (nat_lit 12465129600))]
theorem block007_data_flat077_step : block007_data_flat077 = (CoefficientMerge.fastMerge block007_data_flat057 block007_data_flat076) := by decide +kernel
theorem block007_data_flat077_original : block007_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7932940800 : Int) atom0515Coded) (CoefficientMerge.scale (9311655360 : Int) atom0516Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7477765440 : Int) atom0517Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10379483040 : Int) atom0518Coded) (CoefficientMerge.scale (8044739520 : Int) atom0519Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8392186560 : Int) atom0520Coded) (CoefficientMerge.scale (10204830720 : Int) atom0521Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4927426560 : Int) atom0522Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9870336000 : Int) atom0523Coded) (CoefficientMerge.scale (7722086400 : Int) atom0524Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10978907040 : Int) atom0525Coded) (CoefficientMerge.scale (8678154240 : Int) atom0526Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7662090240 : Int) atom0527Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11373788160 : Int) atom0528Coded) (CoefficientMerge.scale (6543452160 : Int) atom0529Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10721894400 : Int) atom0530Coded) (CoefficientMerge.scale (15248311200 : Int) atom0531Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13098516480 : Int) atom0532Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7930137600 : Int) atom0533Coded) (CoefficientMerge.scale (12465129600 : Int) atom0534Coded)))))) := by
  rw [block007_data_flat077_step, block007_data_flat057_original, block007_data_flat076_original]
def block007_data_flat078 : CoefficientMerge.Poly := [(nat_lit 800, Int.ofNat (nat_lit 3718671360)), (nat_lit 801, Int.ofNat (nat_lit 6793720320)), (nat_lit 802, Int.ofNat (nat_lit 6517608960)), (nat_lit 803, Int.ofNat (nat_lit 6167040000)), (nat_lit 804, Int.ofNat (nat_lit 7979381760)), (nat_lit 805, Int.ofNat (nat_lit 6566323200)), (nat_lit 806, Int.ofNat (nat_lit 8933124000)), (nat_lit 807, Int.ofNat (nat_lit 7949368320)), (nat_lit 808, Int.ofNat (nat_lit 8692055040)), (nat_lit 809, Int.ofNat (nat_lit 10609182720)), (nat_lit 819, Int.ofNat (nat_lit 4164011520)), (nat_lit 820, Int.ofNat (nat_lit 7503144960)), (nat_lit 821, Int.ofNat (nat_lit 6954524160)), (nat_lit 822, Int.ofNat (nat_lit 8592628800)), (nat_lit 823, Int.ofNat (nat_lit 7029147840)), (nat_lit 824, Int.ofNat (nat_lit 9631143840)), (nat_lit 825, Int.ofNat (nat_lit 8158977600)), (nat_lit 826, Int.ofNat (nat_lit 8798871360)), (nat_lit 827, Int.ofNat (nat_lit 10613206080)), (nat_lit 838, Int.ofNat (nat_lit 4531960320)), (nat_lit 839, Int.ofNat (nat_lit 7932940800)), (nat_lit 840, Int.ofNat (nat_lit 9311655360)), (nat_lit 841, Int.ofNat (nat_lit 7477765440)), (nat_lit 842, Int.ofNat (nat_lit 10379483040)), (nat_lit 843, Int.ofNat (nat_lit 8044739520)), (nat_lit 844, Int.ofNat (nat_lit 8392186560)), (nat_lit 845, Int.ofNat (nat_lit 10204830720)), (nat_lit 857, Int.ofNat (nat_lit 4927426560)), (nat_lit 858, Int.ofNat (nat_lit 9870336000)), (nat_lit 859, Int.ofNat (nat_lit 7722086400)), (nat_lit 860, Int.ofNat (nat_lit 10978907040)), (nat_lit 861, Int.ofNat (nat_lit 8678154240)), (nat_lit 862, Int.ofNat (nat_lit 7662090240)), (nat_lit 863, Int.ofNat (nat_lit 11373788160)), (nat_lit 876, Int.ofNat (nat_lit 6543452160)), (nat_lit 877, Int.ofNat (nat_lit 10721894400)), (nat_lit 878, Int.ofNat (nat_lit 15248311200)), (nat_lit 879, Int.ofNat (nat_lit 13098516480)), (nat_lit 880, Int.ofNat (nat_lit 7930137600)), (nat_lit 881, Int.ofNat (nat_lit 12465129600))]
theorem block007_data_flat078_step : block007_data_flat078 = (CoefficientMerge.fastMerge block007_data_flat038 block007_data_flat077) := by decide +kernel
theorem block007_data_flat078_original : block007_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3718671360 : Int) atom0495Coded) (CoefficientMerge.scale (6793720320 : Int) atom0496Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6517608960 : Int) atom0497Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6167040000 : Int) atom0498Coded) (CoefficientMerge.scale (7979381760 : Int) atom0499Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6566323200 : Int) atom0500Coded) (CoefficientMerge.scale (8933124000 : Int) atom0501Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7949368320 : Int) atom0502Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8692055040 : Int) atom0503Coded) (CoefficientMerge.scale (10609182720 : Int) atom0504Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4164011520 : Int) atom0505Coded) (CoefficientMerge.scale (7503144960 : Int) atom0506Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6954524160 : Int) atom0507Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8592628800 : Int) atom0508Coded) (CoefficientMerge.scale (7029147840 : Int) atom0509Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9631143840 : Int) atom0510Coded) (CoefficientMerge.scale (8158977600 : Int) atom0511Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8798871360 : Int) atom0512Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10613206080 : Int) atom0513Coded) (CoefficientMerge.scale (4531960320 : Int) atom0514Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7932940800 : Int) atom0515Coded) (CoefficientMerge.scale (9311655360 : Int) atom0516Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7477765440 : Int) atom0517Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10379483040 : Int) atom0518Coded) (CoefficientMerge.scale (8044739520 : Int) atom0519Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8392186560 : Int) atom0520Coded) (CoefficientMerge.scale (10204830720 : Int) atom0521Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4927426560 : Int) atom0522Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9870336000 : Int) atom0523Coded) (CoefficientMerge.scale (7722086400 : Int) atom0524Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10978907040 : Int) atom0525Coded) (CoefficientMerge.scale (8678154240 : Int) atom0526Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7662090240 : Int) atom0527Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11373788160 : Int) atom0528Coded) (CoefficientMerge.scale (6543452160 : Int) atom0529Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10721894400 : Int) atom0530Coded) (CoefficientMerge.scale (15248311200 : Int) atom0531Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13098516480 : Int) atom0532Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7930137600 : Int) atom0533Coded) (CoefficientMerge.scale (12465129600 : Int) atom0534Coded))))))) := by
  rw [block007_data_flat078_step, block007_data_flat038_original, block007_data_flat077_original]
def block007_data_flat079 : CoefficientMerge.Poly := [(nat_lit 895, Int.ofNat (nat_lit 4665765888))]
theorem block007_data_flat079_step : block007_data_flat079 = (CoefficientMerge.scale (4665765888 : Int) atom0535Coded) := by decide +kernel
theorem block007_data_flat079_original : block007_data_flat079 = (CoefficientMerge.scale (4665765888 : Int) atom0535Coded) := by
  rw [block007_data_flat079_step]
def block007_data_flat080 : CoefficientMerge.Poly := [(nat_lit 896, Int.ofNat (nat_lit 12464877240))]
theorem block007_data_flat080_step : block007_data_flat080 = (CoefficientMerge.scale (12464877240 : Int) atom0536Coded) := by decide +kernel
theorem block007_data_flat080_original : block007_data_flat080 = (CoefficientMerge.scale (12464877240 : Int) atom0536Coded) := by
  rw [block007_data_flat080_step]
def block007_data_flat081 : CoefficientMerge.Poly := [(nat_lit 895, Int.ofNat (nat_lit 4665765888)), (nat_lit 896, Int.ofNat (nat_lit 12464877240))]
theorem block007_data_flat081_step : block007_data_flat081 = (CoefficientMerge.fastMerge block007_data_flat079 block007_data_flat080) := by decide +kernel
theorem block007_data_flat081_original : block007_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4665765888 : Int) atom0535Coded) (CoefficientMerge.scale (12464877240 : Int) atom0536Coded)) := by
  rw [block007_data_flat081_step, block007_data_flat079_original, block007_data_flat080_original]
def block007_data_flat082 : CoefficientMerge.Poly := [(nat_lit 897, Int.ofNat (nat_lit 12188897280))]
theorem block007_data_flat082_step : block007_data_flat082 = (CoefficientMerge.scale (12188897280 : Int) atom0537Coded) := by decide +kernel
theorem block007_data_flat082_original : block007_data_flat082 = (CoefficientMerge.scale (12188897280 : Int) atom0537Coded) := by
  rw [block007_data_flat082_step]
def block007_data_flat083 : CoefficientMerge.Poly := [(nat_lit 898, Int.ofNat (nat_lit 8198184960))]
theorem block007_data_flat083_step : block007_data_flat083 = (CoefficientMerge.scale (8198184960 : Int) atom0538Coded) := by decide +kernel
theorem block007_data_flat083_original : block007_data_flat083 = (CoefficientMerge.scale (8198184960 : Int) atom0538Coded) := by
  rw [block007_data_flat083_step]
def block007_data_flat084 : CoefficientMerge.Poly := [(nat_lit 899, Int.ofNat (nat_lit 9925534080))]
theorem block007_data_flat084_step : block007_data_flat084 = (CoefficientMerge.scale (9925534080 : Int) atom0539Coded) := by decide +kernel
theorem block007_data_flat084_original : block007_data_flat084 = (CoefficientMerge.scale (9925534080 : Int) atom0539Coded) := by
  rw [block007_data_flat084_step]
def block007_data_flat085 : CoefficientMerge.Poly := [(nat_lit 898, Int.ofNat (nat_lit 8198184960)), (nat_lit 899, Int.ofNat (nat_lit 9925534080))]
theorem block007_data_flat085_step : block007_data_flat085 = (CoefficientMerge.fastMerge block007_data_flat083 block007_data_flat084) := by decide +kernel
theorem block007_data_flat085_original : block007_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8198184960 : Int) atom0538Coded) (CoefficientMerge.scale (9925534080 : Int) atom0539Coded)) := by
  rw [block007_data_flat085_step, block007_data_flat083_original, block007_data_flat084_original]
def block007_data_flat086 : CoefficientMerge.Poly := [(nat_lit 897, Int.ofNat (nat_lit 12188897280)), (nat_lit 898, Int.ofNat (nat_lit 8198184960)), (nat_lit 899, Int.ofNat (nat_lit 9925534080))]
theorem block007_data_flat086_step : block007_data_flat086 = (CoefficientMerge.fastMerge block007_data_flat082 block007_data_flat085) := by decide +kernel
theorem block007_data_flat086_original : block007_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12188897280 : Int) atom0537Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8198184960 : Int) atom0538Coded) (CoefficientMerge.scale (9925534080 : Int) atom0539Coded))) := by
  rw [block007_data_flat086_step, block007_data_flat082_original, block007_data_flat085_original]
def block007_data_flat087 : CoefficientMerge.Poly := [(nat_lit 895, Int.ofNat (nat_lit 4665765888)), (nat_lit 896, Int.ofNat (nat_lit 12464877240)), (nat_lit 897, Int.ofNat (nat_lit 12188897280)), (nat_lit 898, Int.ofNat (nat_lit 8198184960)), (nat_lit 899, Int.ofNat (nat_lit 9925534080))]
theorem block007_data_flat087_step : block007_data_flat087 = (CoefficientMerge.fastMerge block007_data_flat081 block007_data_flat086) := by decide +kernel
theorem block007_data_flat087_original : block007_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4665765888 : Int) atom0535Coded) (CoefficientMerge.scale (12464877240 : Int) atom0536Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12188897280 : Int) atom0537Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8198184960 : Int) atom0538Coded) (CoefficientMerge.scale (9925534080 : Int) atom0539Coded)))) := by
  rw [block007_data_flat087_step, block007_data_flat081_original, block007_data_flat086_original]
def block007_data_flat088 : CoefficientMerge.Poly := [(nat_lit 914, Int.ofNat (nat_lit 8286435000))]
theorem block007_data_flat088_step : block007_data_flat088 = (CoefficientMerge.scale (8286435000 : Int) atom0540Coded) := by decide +kernel
theorem block007_data_flat088_original : block007_data_flat088 = (CoefficientMerge.scale (8286435000 : Int) atom0540Coded) := by
  rw [block007_data_flat088_step]
def block007_data_flat089 : CoefficientMerge.Poly := [(nat_lit 915, Int.ofNat (nat_lit 12894527160))]
theorem block007_data_flat089_step : block007_data_flat089 = (CoefficientMerge.scale (12894527160 : Int) atom0541Coded) := by decide +kernel
theorem block007_data_flat089_original : block007_data_flat089 = (CoefficientMerge.scale (12894527160 : Int) atom0541Coded) := by
  rw [block007_data_flat089_step]
def block007_data_flat090 : CoefficientMerge.Poly := [(nat_lit 914, Int.ofNat (nat_lit 8286435000)), (nat_lit 915, Int.ofNat (nat_lit 12894527160))]
theorem block007_data_flat090_step : block007_data_flat090 = (CoefficientMerge.fastMerge block007_data_flat088 block007_data_flat089) := by decide +kernel
theorem block007_data_flat090_original : block007_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8286435000 : Int) atom0540Coded) (CoefficientMerge.scale (12894527160 : Int) atom0541Coded)) := by
  rw [block007_data_flat090_step, block007_data_flat088_original, block007_data_flat089_original]
def block007_data_flat091 : CoefficientMerge.Poly := [(nat_lit 916, Int.ofNat (nat_lit 8358624720))]
theorem block007_data_flat091_step : block007_data_flat091 = (CoefficientMerge.scale (8358624720 : Int) atom0542Coded) := by decide +kernel
theorem block007_data_flat091_original : block007_data_flat091 = (CoefficientMerge.scale (8358624720 : Int) atom0542Coded) := by
  rw [block007_data_flat091_step]
def block007_data_flat092 : CoefficientMerge.Poly := [(nat_lit 917, Int.ofNat (nat_lit 10676419920))]
theorem block007_data_flat092_step : block007_data_flat092 = (CoefficientMerge.scale (10676419920 : Int) atom0543Coded) := by decide +kernel
theorem block007_data_flat092_original : block007_data_flat092 = (CoefficientMerge.scale (10676419920 : Int) atom0543Coded) := by
  rw [block007_data_flat092_step]
def block007_data_flat093 : CoefficientMerge.Poly := [(nat_lit 933, Int.ofNat (nat_lit 4296499200))]
theorem block007_data_flat093_step : block007_data_flat093 = (CoefficientMerge.scale (4296499200 : Int) atom0544Coded) := by decide +kernel
theorem block007_data_flat093_original : block007_data_flat093 = (CoefficientMerge.scale (4296499200 : Int) atom0544Coded) := by
  rw [block007_data_flat093_step]
def block007_data_flat094 : CoefficientMerge.Poly := [(nat_lit 917, Int.ofNat (nat_lit 10676419920)), (nat_lit 933, Int.ofNat (nat_lit 4296499200))]
theorem block007_data_flat094_step : block007_data_flat094 = (CoefficientMerge.fastMerge block007_data_flat092 block007_data_flat093) := by decide +kernel
theorem block007_data_flat094_original : block007_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10676419920 : Int) atom0543Coded) (CoefficientMerge.scale (4296499200 : Int) atom0544Coded)) := by
  rw [block007_data_flat094_step, block007_data_flat092_original, block007_data_flat093_original]
def block007_data_flat095 : CoefficientMerge.Poly := [(nat_lit 916, Int.ofNat (nat_lit 8358624720)), (nat_lit 917, Int.ofNat (nat_lit 10676419920)), (nat_lit 933, Int.ofNat (nat_lit 4296499200))]
theorem block007_data_flat095_step : block007_data_flat095 = (CoefficientMerge.fastMerge block007_data_flat091 block007_data_flat094) := by decide +kernel
theorem block007_data_flat095_original : block007_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8358624720 : Int) atom0542Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10676419920 : Int) atom0543Coded) (CoefficientMerge.scale (4296499200 : Int) atom0544Coded))) := by
  rw [block007_data_flat095_step, block007_data_flat091_original, block007_data_flat094_original]
def block007_data_flat096 : CoefficientMerge.Poly := [(nat_lit 914, Int.ofNat (nat_lit 8286435000)), (nat_lit 915, Int.ofNat (nat_lit 12894527160)), (nat_lit 916, Int.ofNat (nat_lit 8358624720)), (nat_lit 917, Int.ofNat (nat_lit 10676419920)), (nat_lit 933, Int.ofNat (nat_lit 4296499200))]
theorem block007_data_flat096_step : block007_data_flat096 = (CoefficientMerge.fastMerge block007_data_flat090 block007_data_flat095) := by decide +kernel
theorem block007_data_flat096_original : block007_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8286435000 : Int) atom0540Coded) (CoefficientMerge.scale (12894527160 : Int) atom0541Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8358624720 : Int) atom0542Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10676419920 : Int) atom0543Coded) (CoefficientMerge.scale (4296499200 : Int) atom0544Coded)))) := by
  rw [block007_data_flat096_step, block007_data_flat090_original, block007_data_flat095_original]
def block007_data_flat097 : CoefficientMerge.Poly := [(nat_lit 895, Int.ofNat (nat_lit 4665765888)), (nat_lit 896, Int.ofNat (nat_lit 12464877240)), (nat_lit 897, Int.ofNat (nat_lit 12188897280)), (nat_lit 898, Int.ofNat (nat_lit 8198184960)), (nat_lit 899, Int.ofNat (nat_lit 9925534080)), (nat_lit 914, Int.ofNat (nat_lit 8286435000)), (nat_lit 915, Int.ofNat (nat_lit 12894527160)), (nat_lit 916, Int.ofNat (nat_lit 8358624720)), (nat_lit 917, Int.ofNat (nat_lit 10676419920)), (nat_lit 933, Int.ofNat (nat_lit 4296499200))]
theorem block007_data_flat097_step : block007_data_flat097 = (CoefficientMerge.fastMerge block007_data_flat087 block007_data_flat096) := by decide +kernel
theorem block007_data_flat097_original : block007_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4665765888 : Int) atom0535Coded) (CoefficientMerge.scale (12464877240 : Int) atom0536Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12188897280 : Int) atom0537Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8198184960 : Int) atom0538Coded) (CoefficientMerge.scale (9925534080 : Int) atom0539Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8286435000 : Int) atom0540Coded) (CoefficientMerge.scale (12894527160 : Int) atom0541Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8358624720 : Int) atom0542Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10676419920 : Int) atom0543Coded) (CoefficientMerge.scale (4296499200 : Int) atom0544Coded))))) := by
  rw [block007_data_flat097_step, block007_data_flat087_original, block007_data_flat096_original]
def block007_data_flat098 : CoefficientMerge.Poly := [(nat_lit 934, Int.ofNat (nat_lit 5555934720))]
theorem block007_data_flat098_step : block007_data_flat098 = (CoefficientMerge.scale (5555934720 : Int) atom0545Coded) := by decide +kernel
theorem block007_data_flat098_original : block007_data_flat098 = (CoefficientMerge.scale (5555934720 : Int) atom0545Coded) := by
  rw [block007_data_flat098_step]
def block007_data_flat099 : CoefficientMerge.Poly := [(nat_lit 935, Int.ofNat (nat_lit 8244432000))]
theorem block007_data_flat099_step : block007_data_flat099 = (CoefficientMerge.scale (8244432000 : Int) atom0546Coded) := by decide +kernel
theorem block007_data_flat099_original : block007_data_flat099 = (CoefficientMerge.scale (8244432000 : Int) atom0546Coded) := by
  rw [block007_data_flat099_step]
def block007_data_flat100 : CoefficientMerge.Poly := [(nat_lit 934, Int.ofNat (nat_lit 5555934720)), (nat_lit 935, Int.ofNat (nat_lit 8244432000))]
theorem block007_data_flat100_step : block007_data_flat100 = (CoefficientMerge.fastMerge block007_data_flat098 block007_data_flat099) := by decide +kernel
theorem block007_data_flat100_original : block007_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5555934720 : Int) atom0545Coded) (CoefficientMerge.scale (8244432000 : Int) atom0546Coded)) := by
  rw [block007_data_flat100_step, block007_data_flat098_original, block007_data_flat099_original]
def block007_data_flat101 : CoefficientMerge.Poly := [(nat_lit 952, Int.ofNat (nat_lit 572866560))]
theorem block007_data_flat101_step : block007_data_flat101 = (CoefficientMerge.scale (572866560 : Int) atom0547Coded) := by decide +kernel
theorem block007_data_flat101_original : block007_data_flat101 = (CoefficientMerge.scale (572866560 : Int) atom0547Coded) := by
  rw [block007_data_flat101_step]
def block007_data_flat102 : CoefficientMerge.Poly := [(nat_lit 953, Int.ofNat (nat_lit 3862212480))]
theorem block007_data_flat102_step : block007_data_flat102 = (CoefficientMerge.scale (3862212480 : Int) atom0548Coded) := by decide +kernel
theorem block007_data_flat102_original : block007_data_flat102 = (CoefficientMerge.scale (3862212480 : Int) atom0548Coded) := by
  rw [block007_data_flat102_step]
def block007_data_flat103 : CoefficientMerge.Poly := [(nat_lit 971, Int.ofNat (nat_lit 2854776960))]
theorem block007_data_flat103_step : block007_data_flat103 = (CoefficientMerge.scale (2854776960 : Int) atom0549Coded) := by decide +kernel
theorem block007_data_flat103_original : block007_data_flat103 = (CoefficientMerge.scale (2854776960 : Int) atom0549Coded) := by
  rw [block007_data_flat103_step]
def block007_data_flat104 : CoefficientMerge.Poly := [(nat_lit 953, Int.ofNat (nat_lit 3862212480)), (nat_lit 971, Int.ofNat (nat_lit 2854776960))]
theorem block007_data_flat104_step : block007_data_flat104 = (CoefficientMerge.fastMerge block007_data_flat102 block007_data_flat103) := by decide +kernel
theorem block007_data_flat104_original : block007_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3862212480 : Int) atom0548Coded) (CoefficientMerge.scale (2854776960 : Int) atom0549Coded)) := by
  rw [block007_data_flat104_step, block007_data_flat102_original, block007_data_flat103_original]
def block007_data_flat105 : CoefficientMerge.Poly := [(nat_lit 952, Int.ofNat (nat_lit 572866560)), (nat_lit 953, Int.ofNat (nat_lit 3862212480)), (nat_lit 971, Int.ofNat (nat_lit 2854776960))]
theorem block007_data_flat105_step : block007_data_flat105 = (CoefficientMerge.fastMerge block007_data_flat101 block007_data_flat104) := by decide +kernel
theorem block007_data_flat105_original : block007_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (572866560 : Int) atom0547Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3862212480 : Int) atom0548Coded) (CoefficientMerge.scale (2854776960 : Int) atom0549Coded))) := by
  rw [block007_data_flat105_step, block007_data_flat101_original, block007_data_flat104_original]
def block007_data_flat106 : CoefficientMerge.Poly := [(nat_lit 934, Int.ofNat (nat_lit 5555934720)), (nat_lit 935, Int.ofNat (nat_lit 8244432000)), (nat_lit 952, Int.ofNat (nat_lit 572866560)), (nat_lit 953, Int.ofNat (nat_lit 3862212480)), (nat_lit 971, Int.ofNat (nat_lit 2854776960))]
theorem block007_data_flat106_step : block007_data_flat106 = (CoefficientMerge.fastMerge block007_data_flat100 block007_data_flat105) := by decide +kernel
theorem block007_data_flat106_original : block007_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5555934720 : Int) atom0545Coded) (CoefficientMerge.scale (8244432000 : Int) atom0546Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (572866560 : Int) atom0547Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3862212480 : Int) atom0548Coded) (CoefficientMerge.scale (2854776960 : Int) atom0549Coded)))) := by
  rw [block007_data_flat106_step, block007_data_flat100_original, block007_data_flat105_original]
def block007_data_flat107 : CoefficientMerge.Poly := [(nat_lit 1029, Int.ofNat (nat_lit 249016320))]
theorem block007_data_flat107_step : block007_data_flat107 = (CoefficientMerge.scale (249016320 : Int) atom0550Coded) := by decide +kernel
theorem block007_data_flat107_original : block007_data_flat107 = (CoefficientMerge.scale (249016320 : Int) atom0550Coded) := by
  rw [block007_data_flat107_step]
def block007_data_flat108 : CoefficientMerge.Poly := [(nat_lit 1030, Int.ofNat (nat_lit 633507840))]
theorem block007_data_flat108_step : block007_data_flat108 = (CoefficientMerge.scale (633507840 : Int) atom0551Coded) := by decide +kernel
theorem block007_data_flat108_original : block007_data_flat108 = (CoefficientMerge.scale (633507840 : Int) atom0551Coded) := by
  rw [block007_data_flat108_step]
def block007_data_flat109 : CoefficientMerge.Poly := [(nat_lit 1029, Int.ofNat (nat_lit 249016320)), (nat_lit 1030, Int.ofNat (nat_lit 633507840))]
theorem block007_data_flat109_step : block007_data_flat109 = (CoefficientMerge.fastMerge block007_data_flat107 block007_data_flat108) := by decide +kernel
theorem block007_data_flat109_original : block007_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (249016320 : Int) atom0550Coded) (CoefficientMerge.scale (633507840 : Int) atom0551Coded)) := by
  rw [block007_data_flat109_step, block007_data_flat107_original, block007_data_flat108_original]
def block007_data_flat110 : CoefficientMerge.Poly := [(nat_lit 1031, Int.ofNat (nat_lit 519966720))]
theorem block007_data_flat110_step : block007_data_flat110 = (CoefficientMerge.scale (519966720 : Int) atom0552Coded) := by decide +kernel
theorem block007_data_flat110_original : block007_data_flat110 = (CoefficientMerge.scale (519966720 : Int) atom0552Coded) := by
  rw [block007_data_flat110_step]
def block007_data_flat111 : CoefficientMerge.Poly := [(nat_lit 1032, Int.ofNat (nat_lit 406425600))]
theorem block007_data_flat111_step : block007_data_flat111 = (CoefficientMerge.scale (406425600 : Int) atom0553Coded) := by decide +kernel
theorem block007_data_flat111_original : block007_data_flat111 = (CoefficientMerge.scale (406425600 : Int) atom0553Coded) := by
  rw [block007_data_flat111_step]
def block007_data_flat112 : CoefficientMerge.Poly := [(nat_lit 1033, Int.ofNat (nat_lit 292884480))]
theorem block007_data_flat112_step : block007_data_flat112 = (CoefficientMerge.scale (292884480 : Int) atom0554Coded) := by decide +kernel
theorem block007_data_flat112_original : block007_data_flat112 = (CoefficientMerge.scale (292884480 : Int) atom0554Coded) := by
  rw [block007_data_flat112_step]
def block007_data_flat113 : CoefficientMerge.Poly := [(nat_lit 1032, Int.ofNat (nat_lit 406425600)), (nat_lit 1033, Int.ofNat (nat_lit 292884480))]
theorem block007_data_flat113_step : block007_data_flat113 = (CoefficientMerge.fastMerge block007_data_flat111 block007_data_flat112) := by decide +kernel
theorem block007_data_flat113_original : block007_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (406425600 : Int) atom0553Coded) (CoefficientMerge.scale (292884480 : Int) atom0554Coded)) := by
  rw [block007_data_flat113_step, block007_data_flat111_original, block007_data_flat112_original]
def block007_data_flat114 : CoefficientMerge.Poly := [(nat_lit 1031, Int.ofNat (nat_lit 519966720)), (nat_lit 1032, Int.ofNat (nat_lit 406425600)), (nat_lit 1033, Int.ofNat (nat_lit 292884480))]
theorem block007_data_flat114_step : block007_data_flat114 = (CoefficientMerge.fastMerge block007_data_flat110 block007_data_flat113) := by decide +kernel
theorem block007_data_flat114_original : block007_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (519966720 : Int) atom0552Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (406425600 : Int) atom0553Coded) (CoefficientMerge.scale (292884480 : Int) atom0554Coded))) := by
  rw [block007_data_flat114_step, block007_data_flat110_original, block007_data_flat113_original]
def block007_data_flat115 : CoefficientMerge.Poly := [(nat_lit 1029, Int.ofNat (nat_lit 249016320)), (nat_lit 1030, Int.ofNat (nat_lit 633507840)), (nat_lit 1031, Int.ofNat (nat_lit 519966720)), (nat_lit 1032, Int.ofNat (nat_lit 406425600)), (nat_lit 1033, Int.ofNat (nat_lit 292884480))]
theorem block007_data_flat115_step : block007_data_flat115 = (CoefficientMerge.fastMerge block007_data_flat109 block007_data_flat114) := by decide +kernel
theorem block007_data_flat115_original : block007_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (249016320 : Int) atom0550Coded) (CoefficientMerge.scale (633507840 : Int) atom0551Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519966720 : Int) atom0552Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (406425600 : Int) atom0553Coded) (CoefficientMerge.scale (292884480 : Int) atom0554Coded)))) := by
  rw [block007_data_flat115_step, block007_data_flat109_original, block007_data_flat114_original]
def block007_data_flat116 : CoefficientMerge.Poly := [(nat_lit 934, Int.ofNat (nat_lit 5555934720)), (nat_lit 935, Int.ofNat (nat_lit 8244432000)), (nat_lit 952, Int.ofNat (nat_lit 572866560)), (nat_lit 953, Int.ofNat (nat_lit 3862212480)), (nat_lit 971, Int.ofNat (nat_lit 2854776960)), (nat_lit 1029, Int.ofNat (nat_lit 249016320)), (nat_lit 1030, Int.ofNat (nat_lit 633507840)), (nat_lit 1031, Int.ofNat (nat_lit 519966720)), (nat_lit 1032, Int.ofNat (nat_lit 406425600)), (nat_lit 1033, Int.ofNat (nat_lit 292884480))]
theorem block007_data_flat116_step : block007_data_flat116 = (CoefficientMerge.fastMerge block007_data_flat106 block007_data_flat115) := by decide +kernel
theorem block007_data_flat116_original : block007_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5555934720 : Int) atom0545Coded) (CoefficientMerge.scale (8244432000 : Int) atom0546Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (572866560 : Int) atom0547Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3862212480 : Int) atom0548Coded) (CoefficientMerge.scale (2854776960 : Int) atom0549Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (249016320 : Int) atom0550Coded) (CoefficientMerge.scale (633507840 : Int) atom0551Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519966720 : Int) atom0552Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (406425600 : Int) atom0553Coded) (CoefficientMerge.scale (292884480 : Int) atom0554Coded))))) := by
  rw [block007_data_flat116_step, block007_data_flat106_original, block007_data_flat115_original]
def block007_data_flat117 : CoefficientMerge.Poly := [(nat_lit 895, Int.ofNat (nat_lit 4665765888)), (nat_lit 896, Int.ofNat (nat_lit 12464877240)), (nat_lit 897, Int.ofNat (nat_lit 12188897280)), (nat_lit 898, Int.ofNat (nat_lit 8198184960)), (nat_lit 899, Int.ofNat (nat_lit 9925534080)), (nat_lit 914, Int.ofNat (nat_lit 8286435000)), (nat_lit 915, Int.ofNat (nat_lit 12894527160)), (nat_lit 916, Int.ofNat (nat_lit 8358624720)), (nat_lit 917, Int.ofNat (nat_lit 10676419920)), (nat_lit 933, Int.ofNat (nat_lit 4296499200)), (nat_lit 934, Int.ofNat (nat_lit 5555934720)), (nat_lit 935, Int.ofNat (nat_lit 8244432000)), (nat_lit 952, Int.ofNat (nat_lit 572866560)), (nat_lit 953, Int.ofNat (nat_lit 3862212480)), (nat_lit 971, Int.ofNat (nat_lit 2854776960)), (nat_lit 1029, Int.ofNat (nat_lit 249016320)), (nat_lit 1030, Int.ofNat (nat_lit 633507840)), (nat_lit 1031, Int.ofNat (nat_lit 519966720)), (nat_lit 1032, Int.ofNat (nat_lit 406425600)), (nat_lit 1033, Int.ofNat (nat_lit 292884480))]
theorem block007_data_flat117_step : block007_data_flat117 = (CoefficientMerge.fastMerge block007_data_flat097 block007_data_flat116) := by decide +kernel
theorem block007_data_flat117_original : block007_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4665765888 : Int) atom0535Coded) (CoefficientMerge.scale (12464877240 : Int) atom0536Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12188897280 : Int) atom0537Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8198184960 : Int) atom0538Coded) (CoefficientMerge.scale (9925534080 : Int) atom0539Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8286435000 : Int) atom0540Coded) (CoefficientMerge.scale (12894527160 : Int) atom0541Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8358624720 : Int) atom0542Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10676419920 : Int) atom0543Coded) (CoefficientMerge.scale (4296499200 : Int) atom0544Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5555934720 : Int) atom0545Coded) (CoefficientMerge.scale (8244432000 : Int) atom0546Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (572866560 : Int) atom0547Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3862212480 : Int) atom0548Coded) (CoefficientMerge.scale (2854776960 : Int) atom0549Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (249016320 : Int) atom0550Coded) (CoefficientMerge.scale (633507840 : Int) atom0551Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519966720 : Int) atom0552Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (406425600 : Int) atom0553Coded) (CoefficientMerge.scale (292884480 : Int) atom0554Coded)))))) := by
  rw [block007_data_flat117_step, block007_data_flat097_original, block007_data_flat116_original]
def block007_data_flat118 : CoefficientMerge.Poly := [(nat_lit 1034, Int.ofNat (nat_lit 230576640))]
theorem block007_data_flat118_step : block007_data_flat118 = (CoefficientMerge.scale (230576640 : Int) atom0555Coded) := by decide +kernel
theorem block007_data_flat118_original : block007_data_flat118 = (CoefficientMerge.scale (230576640 : Int) atom0555Coded) := by
  rw [block007_data_flat118_step]
def block007_data_flat119 : CoefficientMerge.Poly := [(nat_lit 1035, Int.ofNat (nat_lit 108003840))]
theorem block007_data_flat119_step : block007_data_flat119 = (CoefficientMerge.scale (108003840 : Int) atom0556Coded) := by decide +kernel
theorem block007_data_flat119_original : block007_data_flat119 = (CoefficientMerge.scale (108003840 : Int) atom0556Coded) := by
  rw [block007_data_flat119_step]
def block007_data_flat120 : CoefficientMerge.Poly := [(nat_lit 1034, Int.ofNat (nat_lit 230576640)), (nat_lit 1035, Int.ofNat (nat_lit 108003840))]
theorem block007_data_flat120_step : block007_data_flat120 = (CoefficientMerge.fastMerge block007_data_flat118 block007_data_flat119) := by decide +kernel
theorem block007_data_flat120_original : block007_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (230576640 : Int) atom0555Coded) (CoefficientMerge.scale (108003840 : Int) atom0556Coded)) := by
  rw [block007_data_flat120_step, block007_data_flat118_original, block007_data_flat119_original]
def block007_data_flat121 : CoefficientMerge.Poly := [(nat_lit 1036, Int.ofNat (nat_lit 10590720))]
theorem block007_data_flat121_step : block007_data_flat121 = (CoefficientMerge.scale (10590720 : Int) atom0557Coded) := by decide +kernel
theorem block007_data_flat121_original : block007_data_flat121 = (CoefficientMerge.scale (10590720 : Int) atom0557Coded) := by
  rw [block007_data_flat121_step]
def block007_data_flat122 : CoefficientMerge.Poly := [(nat_lit 1038, Int.ofNat (nat_lit 1501839360))]
theorem block007_data_flat122_step : block007_data_flat122 = (CoefficientMerge.scale (1501839360 : Int) atom0558Coded) := by decide +kernel
theorem block007_data_flat122_original : block007_data_flat122 = (CoefficientMerge.scale (1501839360 : Int) atom0558Coded) := by
  rw [block007_data_flat122_step]
def block007_data_flat123 : CoefficientMerge.Poly := [(nat_lit 1040, Int.ofNat (nat_lit 1167149520))]
theorem block007_data_flat123_step : block007_data_flat123 = (CoefficientMerge.scale (1167149520 : Int) atom0559Coded) := by decide +kernel
theorem block007_data_flat123_original : block007_data_flat123 = (CoefficientMerge.scale (1167149520 : Int) atom0559Coded) := by
  rw [block007_data_flat123_step]
def block007_data_flat124 : CoefficientMerge.Poly := [(nat_lit 1038, Int.ofNat (nat_lit 1501839360)), (nat_lit 1040, Int.ofNat (nat_lit 1167149520))]
theorem block007_data_flat124_step : block007_data_flat124 = (CoefficientMerge.fastMerge block007_data_flat122 block007_data_flat123) := by decide +kernel
theorem block007_data_flat124_original : block007_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1501839360 : Int) atom0558Coded) (CoefficientMerge.scale (1167149520 : Int) atom0559Coded)) := by
  rw [block007_data_flat124_step, block007_data_flat122_original, block007_data_flat123_original]
def block007_data_flat125 : CoefficientMerge.Poly := [(nat_lit 1036, Int.ofNat (nat_lit 10590720)), (nat_lit 1038, Int.ofNat (nat_lit 1501839360)), (nat_lit 1040, Int.ofNat (nat_lit 1167149520))]
theorem block007_data_flat125_step : block007_data_flat125 = (CoefficientMerge.fastMerge block007_data_flat121 block007_data_flat124) := by decide +kernel
theorem block007_data_flat125_original : block007_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10590720 : Int) atom0557Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1501839360 : Int) atom0558Coded) (CoefficientMerge.scale (1167149520 : Int) atom0559Coded))) := by
  rw [block007_data_flat125_step, block007_data_flat121_original, block007_data_flat124_original]
def block007_data_flat126 : CoefficientMerge.Poly := [(nat_lit 1034, Int.ofNat (nat_lit 230576640)), (nat_lit 1035, Int.ofNat (nat_lit 108003840)), (nat_lit 1036, Int.ofNat (nat_lit 10590720)), (nat_lit 1038, Int.ofNat (nat_lit 1501839360)), (nat_lit 1040, Int.ofNat (nat_lit 1167149520))]
theorem block007_data_flat126_step : block007_data_flat126 = (CoefficientMerge.fastMerge block007_data_flat120 block007_data_flat125) := by decide +kernel
theorem block007_data_flat126_original : block007_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (230576640 : Int) atom0555Coded) (CoefficientMerge.scale (108003840 : Int) atom0556Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10590720 : Int) atom0557Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1501839360 : Int) atom0558Coded) (CoefficientMerge.scale (1167149520 : Int) atom0559Coded)))) := by
  rw [block007_data_flat126_step, block007_data_flat120_original, block007_data_flat125_original]
def block007_data_flat127 : CoefficientMerge.Poly := [(nat_lit 1048, Int.ofNat (nat_lit 1344806400))]
theorem block007_data_flat127_step : block007_data_flat127 = (CoefficientMerge.scale (1344806400 : Int) atom0560Coded) := by decide +kernel
theorem block007_data_flat127_original : block007_data_flat127 = (CoefficientMerge.scale (1344806400 : Int) atom0560Coded) := by
  rw [block007_data_flat127_step]
def block007_data_flat128 : CoefficientMerge.Poly := [(nat_lit 1049, Int.ofNat (nat_lit 1764439680))]
theorem block007_data_flat128_step : block007_data_flat128 = (CoefficientMerge.scale (1764439680 : Int) atom0561Coded) := by decide +kernel
theorem block007_data_flat128_original : block007_data_flat128 = (CoefficientMerge.scale (1764439680 : Int) atom0561Coded) := by
  rw [block007_data_flat128_step]
def block007_data_flat129 : CoefficientMerge.Poly := [(nat_lit 1048, Int.ofNat (nat_lit 1344806400)), (nat_lit 1049, Int.ofNat (nat_lit 1764439680))]
theorem block007_data_flat129_step : block007_data_flat129 = (CoefficientMerge.fastMerge block007_data_flat127 block007_data_flat128) := by decide +kernel
theorem block007_data_flat129_original : block007_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1344806400 : Int) atom0560Coded) (CoefficientMerge.scale (1764439680 : Int) atom0561Coded)) := by
  rw [block007_data_flat129_step, block007_data_flat127_original, block007_data_flat128_original]
def block007_data_flat130 : CoefficientMerge.Poly := [(nat_lit 1050, Int.ofNat (nat_lit 766439040))]
theorem block007_data_flat130_step : block007_data_flat130 = (CoefficientMerge.scale (766439040 : Int) atom0562Coded) := by decide +kernel
theorem block007_data_flat130_original : block007_data_flat130 = (CoefficientMerge.scale (766439040 : Int) atom0562Coded) := by
  rw [block007_data_flat130_step]
def block007_data_flat131 : CoefficientMerge.Poly := [(nat_lit 1051, Int.ofNat (nat_lit 245414400))]
theorem block007_data_flat131_step : block007_data_flat131 = (CoefficientMerge.scale (245414400 : Int) atom0563Coded) := by decide +kernel
theorem block007_data_flat131_original : block007_data_flat131 = (CoefficientMerge.scale (245414400 : Int) atom0563Coded) := by
  rw [block007_data_flat131_step]
def block007_data_flat132 : CoefficientMerge.Poly := [(nat_lit 1052, Int.ofNat (nat_lit 208266240))]
theorem block007_data_flat132_step : block007_data_flat132 = (CoefficientMerge.scale (208266240 : Int) atom0564Coded) := by decide +kernel
theorem block007_data_flat132_original : block007_data_flat132 = (CoefficientMerge.scale (208266240 : Int) atom0564Coded) := by
  rw [block007_data_flat132_step]
def block007_data_flat133 : CoefficientMerge.Poly := [(nat_lit 1051, Int.ofNat (nat_lit 245414400)), (nat_lit 1052, Int.ofNat (nat_lit 208266240))]
theorem block007_data_flat133_step : block007_data_flat133 = (CoefficientMerge.fastMerge block007_data_flat131 block007_data_flat132) := by decide +kernel
theorem block007_data_flat133_original : block007_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (245414400 : Int) atom0563Coded) (CoefficientMerge.scale (208266240 : Int) atom0564Coded)) := by
  rw [block007_data_flat133_step, block007_data_flat131_original, block007_data_flat132_original]
def block007_data_flat134 : CoefficientMerge.Poly := [(nat_lit 1050, Int.ofNat (nat_lit 766439040)), (nat_lit 1051, Int.ofNat (nat_lit 245414400)), (nat_lit 1052, Int.ofNat (nat_lit 208266240))]
theorem block007_data_flat134_step : block007_data_flat134 = (CoefficientMerge.fastMerge block007_data_flat130 block007_data_flat133) := by decide +kernel
theorem block007_data_flat134_original : block007_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (766439040 : Int) atom0562Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245414400 : Int) atom0563Coded) (CoefficientMerge.scale (208266240 : Int) atom0564Coded))) := by
  rw [block007_data_flat134_step, block007_data_flat130_original, block007_data_flat133_original]
def block007_data_flat135 : CoefficientMerge.Poly := [(nat_lit 1048, Int.ofNat (nat_lit 1344806400)), (nat_lit 1049, Int.ofNat (nat_lit 1764439680)), (nat_lit 1050, Int.ofNat (nat_lit 766439040)), (nat_lit 1051, Int.ofNat (nat_lit 245414400)), (nat_lit 1052, Int.ofNat (nat_lit 208266240))]
theorem block007_data_flat135_step : block007_data_flat135 = (CoefficientMerge.fastMerge block007_data_flat129 block007_data_flat134) := by decide +kernel
theorem block007_data_flat135_original : block007_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1344806400 : Int) atom0560Coded) (CoefficientMerge.scale (1764439680 : Int) atom0561Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (766439040 : Int) atom0562Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245414400 : Int) atom0563Coded) (CoefficientMerge.scale (208266240 : Int) atom0564Coded)))) := by
  rw [block007_data_flat135_step, block007_data_flat129_original, block007_data_flat134_original]
def block007_data_flat136 : CoefficientMerge.Poly := [(nat_lit 1034, Int.ofNat (nat_lit 230576640)), (nat_lit 1035, Int.ofNat (nat_lit 108003840)), (nat_lit 1036, Int.ofNat (nat_lit 10590720)), (nat_lit 1038, Int.ofNat (nat_lit 1501839360)), (nat_lit 1040, Int.ofNat (nat_lit 1167149520)), (nat_lit 1048, Int.ofNat (nat_lit 1344806400)), (nat_lit 1049, Int.ofNat (nat_lit 1764439680)), (nat_lit 1050, Int.ofNat (nat_lit 766439040)), (nat_lit 1051, Int.ofNat (nat_lit 245414400)), (nat_lit 1052, Int.ofNat (nat_lit 208266240))]
theorem block007_data_flat136_step : block007_data_flat136 = (CoefficientMerge.fastMerge block007_data_flat126 block007_data_flat135) := by decide +kernel
theorem block007_data_flat136_original : block007_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (230576640 : Int) atom0555Coded) (CoefficientMerge.scale (108003840 : Int) atom0556Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10590720 : Int) atom0557Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1501839360 : Int) atom0558Coded) (CoefficientMerge.scale (1167149520 : Int) atom0559Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1344806400 : Int) atom0560Coded) (CoefficientMerge.scale (1764439680 : Int) atom0561Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (766439040 : Int) atom0562Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245414400 : Int) atom0563Coded) (CoefficientMerge.scale (208266240 : Int) atom0564Coded))))) := by
  rw [block007_data_flat136_step, block007_data_flat126_original, block007_data_flat135_original]
def block007_data_flat137 : CoefficientMerge.Poly := [(nat_lit 1053, Int.ofNat (nat_lit 164398080))]
theorem block007_data_flat137_step : block007_data_flat137 = (CoefficientMerge.scale (164398080 : Int) atom0565Coded) := by decide +kernel
theorem block007_data_flat137_original : block007_data_flat137 = (CoefficientMerge.scale (164398080 : Int) atom0565Coded) := by
  rw [block007_data_flat137_step]
def block007_data_flat138 : CoefficientMerge.Poly := [(nat_lit 1054, Int.ofNat (nat_lit 170849280))]
theorem block007_data_flat138_step : block007_data_flat138 = (CoefficientMerge.scale (170849280 : Int) atom0566Coded) := by decide +kernel
theorem block007_data_flat138_original : block007_data_flat138 = (CoefficientMerge.scale (170849280 : Int) atom0566Coded) := by
  rw [block007_data_flat138_step]
def block007_data_flat139 : CoefficientMerge.Poly := [(nat_lit 1053, Int.ofNat (nat_lit 164398080)), (nat_lit 1054, Int.ofNat (nat_lit 170849280))]
theorem block007_data_flat139_step : block007_data_flat139 = (CoefficientMerge.fastMerge block007_data_flat137 block007_data_flat138) := by decide +kernel
theorem block007_data_flat139_original : block007_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (164398080 : Int) atom0565Coded) (CoefficientMerge.scale (170849280 : Int) atom0566Coded)) := by
  rw [block007_data_flat139_step, block007_data_flat137_original, block007_data_flat138_original]
def block007_data_flat140 : CoefficientMerge.Poly := [(nat_lit 1055, Int.ofNat (nat_lit 264122880))]
theorem block007_data_flat140_step : block007_data_flat140 = (CoefficientMerge.scale (264122880 : Int) atom0567Coded) := by decide +kernel
theorem block007_data_flat140_original : block007_data_flat140 = (CoefficientMerge.scale (264122880 : Int) atom0567Coded) := by
  rw [block007_data_flat140_step]
def block007_data_flat141 : CoefficientMerge.Poly := [(nat_lit 1056, Int.ofNat (nat_lit 3555901440))]
theorem block007_data_flat141_step : block007_data_flat141 = (CoefficientMerge.scale (3555901440 : Int) atom0568Coded) := by decide +kernel
theorem block007_data_flat141_original : block007_data_flat141 = (CoefficientMerge.scale (3555901440 : Int) atom0568Coded) := by
  rw [block007_data_flat141_step]
def block007_data_flat142 : CoefficientMerge.Poly := [(nat_lit 1057, Int.ofNat (nat_lit 936962880))]
theorem block007_data_flat142_step : block007_data_flat142 = (CoefficientMerge.scale (936962880 : Int) atom0569Coded) := by decide +kernel
theorem block007_data_flat142_original : block007_data_flat142 = (CoefficientMerge.scale (936962880 : Int) atom0569Coded) := by
  rw [block007_data_flat142_step]
def block007_data_flat143 : CoefficientMerge.Poly := [(nat_lit 1056, Int.ofNat (nat_lit 3555901440)), (nat_lit 1057, Int.ofNat (nat_lit 936962880))]
theorem block007_data_flat143_step : block007_data_flat143 = (CoefficientMerge.fastMerge block007_data_flat141 block007_data_flat142) := by decide +kernel
theorem block007_data_flat143_original : block007_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3555901440 : Int) atom0568Coded) (CoefficientMerge.scale (936962880 : Int) atom0569Coded)) := by
  rw [block007_data_flat143_step, block007_data_flat141_original, block007_data_flat142_original]
def block007_data_flat144 : CoefficientMerge.Poly := [(nat_lit 1055, Int.ofNat (nat_lit 264122880)), (nat_lit 1056, Int.ofNat (nat_lit 3555901440)), (nat_lit 1057, Int.ofNat (nat_lit 936962880))]
theorem block007_data_flat144_step : block007_data_flat144 = (CoefficientMerge.fastMerge block007_data_flat140 block007_data_flat143) := by decide +kernel
theorem block007_data_flat144_original : block007_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (264122880 : Int) atom0567Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3555901440 : Int) atom0568Coded) (CoefficientMerge.scale (936962880 : Int) atom0569Coded))) := by
  rw [block007_data_flat144_step, block007_data_flat140_original, block007_data_flat143_original]
def block007_data_flat145 : CoefficientMerge.Poly := [(nat_lit 1053, Int.ofNat (nat_lit 164398080)), (nat_lit 1054, Int.ofNat (nat_lit 170849280)), (nat_lit 1055, Int.ofNat (nat_lit 264122880)), (nat_lit 1056, Int.ofNat (nat_lit 3555901440)), (nat_lit 1057, Int.ofNat (nat_lit 936962880))]
theorem block007_data_flat145_step : block007_data_flat145 = (CoefficientMerge.fastMerge block007_data_flat139 block007_data_flat144) := by decide +kernel
theorem block007_data_flat145_original : block007_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (164398080 : Int) atom0565Coded) (CoefficientMerge.scale (170849280 : Int) atom0566Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264122880 : Int) atom0567Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3555901440 : Int) atom0568Coded) (CoefficientMerge.scale (936962880 : Int) atom0569Coded)))) := by
  rw [block007_data_flat145_step, block007_data_flat139_original, block007_data_flat144_original]
def block007_data_flat146 : CoefficientMerge.Poly := [(nat_lit 1058, Int.ofNat (nat_lit 3289076640))]
theorem block007_data_flat146_step : block007_data_flat146 = (CoefficientMerge.scale (3289076640 : Int) atom0570Coded) := by decide +kernel
theorem block007_data_flat146_original : block007_data_flat146 = (CoefficientMerge.scale (3289076640 : Int) atom0570Coded) := by
  rw [block007_data_flat146_step]
def block007_data_flat147 : CoefficientMerge.Poly := [(nat_lit 1059, Int.ofNat (nat_lit 2074914240))]
theorem block007_data_flat147_step : block007_data_flat147 = (CoefficientMerge.scale (2074914240 : Int) atom0571Coded) := by decide +kernel
theorem block007_data_flat147_original : block007_data_flat147 = (CoefficientMerge.scale (2074914240 : Int) atom0571Coded) := by
  rw [block007_data_flat147_step]
def block007_data_flat148 : CoefficientMerge.Poly := [(nat_lit 1058, Int.ofNat (nat_lit 3289076640)), (nat_lit 1059, Int.ofNat (nat_lit 2074914240))]
theorem block007_data_flat148_step : block007_data_flat148 = (CoefficientMerge.fastMerge block007_data_flat146 block007_data_flat147) := by decide +kernel
theorem block007_data_flat148_original : block007_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3289076640 : Int) atom0570Coded) (CoefficientMerge.scale (2074914240 : Int) atom0571Coded)) := by
  rw [block007_data_flat148_step, block007_data_flat146_original, block007_data_flat147_original]
def block007_data_flat149 : CoefficientMerge.Poly := [(nat_lit 1060, Int.ofNat (nat_lit 2798927040))]
theorem block007_data_flat149_step : block007_data_flat149 = (CoefficientMerge.scale (2798927040 : Int) atom0572Coded) := by decide +kernel
theorem block007_data_flat149_original : block007_data_flat149 = (CoefficientMerge.scale (2798927040 : Int) atom0572Coded) := by
  rw [block007_data_flat149_step]
def block007_data_flat150 : CoefficientMerge.Poly := [(nat_lit 1061, Int.ofNat (nat_lit 3522939840))]
theorem block007_data_flat150_step : block007_data_flat150 = (CoefficientMerge.scale (3522939840 : Int) atom0573Coded) := by decide +kernel
theorem block007_data_flat150_original : block007_data_flat150 = (CoefficientMerge.scale (3522939840 : Int) atom0573Coded) := by
  rw [block007_data_flat150_step]
def block007_data_flat151 : CoefficientMerge.Poly := [(nat_lit 1067, Int.ofNat (nat_lit 1300867200))]
theorem block007_data_flat151_step : block007_data_flat151 = (CoefficientMerge.scale (1300867200 : Int) atom0574Coded) := by decide +kernel
theorem block007_data_flat151_original : block007_data_flat151 = (CoefficientMerge.scale (1300867200 : Int) atom0574Coded) := by
  rw [block007_data_flat151_step]
def block007_data_flat152 : CoefficientMerge.Poly := [(nat_lit 1061, Int.ofNat (nat_lit 3522939840)), (nat_lit 1067, Int.ofNat (nat_lit 1300867200))]
theorem block007_data_flat152_step : block007_data_flat152 = (CoefficientMerge.fastMerge block007_data_flat150 block007_data_flat151) := by decide +kernel
theorem block007_data_flat152_original : block007_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3522939840 : Int) atom0573Coded) (CoefficientMerge.scale (1300867200 : Int) atom0574Coded)) := by
  rw [block007_data_flat152_step, block007_data_flat150_original, block007_data_flat151_original]
def block007_data_flat153 : CoefficientMerge.Poly := [(nat_lit 1060, Int.ofNat (nat_lit 2798927040)), (nat_lit 1061, Int.ofNat (nat_lit 3522939840)), (nat_lit 1067, Int.ofNat (nat_lit 1300867200))]
theorem block007_data_flat153_step : block007_data_flat153 = (CoefficientMerge.fastMerge block007_data_flat149 block007_data_flat152) := by decide +kernel
theorem block007_data_flat153_original : block007_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2798927040 : Int) atom0572Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3522939840 : Int) atom0573Coded) (CoefficientMerge.scale (1300867200 : Int) atom0574Coded))) := by
  rw [block007_data_flat153_step, block007_data_flat149_original, block007_data_flat152_original]
def block007_data_flat154 : CoefficientMerge.Poly := [(nat_lit 1058, Int.ofNat (nat_lit 3289076640)), (nat_lit 1059, Int.ofNat (nat_lit 2074914240)), (nat_lit 1060, Int.ofNat (nat_lit 2798927040)), (nat_lit 1061, Int.ofNat (nat_lit 3522939840)), (nat_lit 1067, Int.ofNat (nat_lit 1300867200))]
theorem block007_data_flat154_step : block007_data_flat154 = (CoefficientMerge.fastMerge block007_data_flat148 block007_data_flat153) := by decide +kernel
theorem block007_data_flat154_original : block007_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3289076640 : Int) atom0570Coded) (CoefficientMerge.scale (2074914240 : Int) atom0571Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2798927040 : Int) atom0572Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3522939840 : Int) atom0573Coded) (CoefficientMerge.scale (1300867200 : Int) atom0574Coded)))) := by
  rw [block007_data_flat154_step, block007_data_flat148_original, block007_data_flat153_original]
def block007_data_flat155 : CoefficientMerge.Poly := [(nat_lit 1053, Int.ofNat (nat_lit 164398080)), (nat_lit 1054, Int.ofNat (nat_lit 170849280)), (nat_lit 1055, Int.ofNat (nat_lit 264122880)), (nat_lit 1056, Int.ofNat (nat_lit 3555901440)), (nat_lit 1057, Int.ofNat (nat_lit 936962880)), (nat_lit 1058, Int.ofNat (nat_lit 3289076640)), (nat_lit 1059, Int.ofNat (nat_lit 2074914240)), (nat_lit 1060, Int.ofNat (nat_lit 2798927040)), (nat_lit 1061, Int.ofNat (nat_lit 3522939840)), (nat_lit 1067, Int.ofNat (nat_lit 1300867200))]
theorem block007_data_flat155_step : block007_data_flat155 = (CoefficientMerge.fastMerge block007_data_flat145 block007_data_flat154) := by decide +kernel
theorem block007_data_flat155_original : block007_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (164398080 : Int) atom0565Coded) (CoefficientMerge.scale (170849280 : Int) atom0566Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264122880 : Int) atom0567Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3555901440 : Int) atom0568Coded) (CoefficientMerge.scale (936962880 : Int) atom0569Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3289076640 : Int) atom0570Coded) (CoefficientMerge.scale (2074914240 : Int) atom0571Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2798927040 : Int) atom0572Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3522939840 : Int) atom0573Coded) (CoefficientMerge.scale (1300867200 : Int) atom0574Coded))))) := by
  rw [block007_data_flat155_step, block007_data_flat145_original, block007_data_flat154_original]
def block007_data_flat156 : CoefficientMerge.Poly := [(nat_lit 1034, Int.ofNat (nat_lit 230576640)), (nat_lit 1035, Int.ofNat (nat_lit 108003840)), (nat_lit 1036, Int.ofNat (nat_lit 10590720)), (nat_lit 1038, Int.ofNat (nat_lit 1501839360)), (nat_lit 1040, Int.ofNat (nat_lit 1167149520)), (nat_lit 1048, Int.ofNat (nat_lit 1344806400)), (nat_lit 1049, Int.ofNat (nat_lit 1764439680)), (nat_lit 1050, Int.ofNat (nat_lit 766439040)), (nat_lit 1051, Int.ofNat (nat_lit 245414400)), (nat_lit 1052, Int.ofNat (nat_lit 208266240)), (nat_lit 1053, Int.ofNat (nat_lit 164398080)), (nat_lit 1054, Int.ofNat (nat_lit 170849280)), (nat_lit 1055, Int.ofNat (nat_lit 264122880)), (nat_lit 1056, Int.ofNat (nat_lit 3555901440)), (nat_lit 1057, Int.ofNat (nat_lit 936962880)), (nat_lit 1058, Int.ofNat (nat_lit 3289076640)), (nat_lit 1059, Int.ofNat (nat_lit 2074914240)), (nat_lit 1060, Int.ofNat (nat_lit 2798927040)), (nat_lit 1061, Int.ofNat (nat_lit 3522939840)), (nat_lit 1067, Int.ofNat (nat_lit 1300867200))]
theorem block007_data_flat156_step : block007_data_flat156 = (CoefficientMerge.fastMerge block007_data_flat136 block007_data_flat155) := by decide +kernel
theorem block007_data_flat156_original : block007_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (230576640 : Int) atom0555Coded) (CoefficientMerge.scale (108003840 : Int) atom0556Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10590720 : Int) atom0557Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1501839360 : Int) atom0558Coded) (CoefficientMerge.scale (1167149520 : Int) atom0559Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1344806400 : Int) atom0560Coded) (CoefficientMerge.scale (1764439680 : Int) atom0561Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (766439040 : Int) atom0562Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245414400 : Int) atom0563Coded) (CoefficientMerge.scale (208266240 : Int) atom0564Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (164398080 : Int) atom0565Coded) (CoefficientMerge.scale (170849280 : Int) atom0566Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264122880 : Int) atom0567Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3555901440 : Int) atom0568Coded) (CoefficientMerge.scale (936962880 : Int) atom0569Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3289076640 : Int) atom0570Coded) (CoefficientMerge.scale (2074914240 : Int) atom0571Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2798927040 : Int) atom0572Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3522939840 : Int) atom0573Coded) (CoefficientMerge.scale (1300867200 : Int) atom0574Coded)))))) := by
  rw [block007_data_flat156_step, block007_data_flat136_original, block007_data_flat155_original]
def block007_data_flat157 : CoefficientMerge.Poly := [(nat_lit 895, Int.ofNat (nat_lit 4665765888)), (nat_lit 896, Int.ofNat (nat_lit 12464877240)), (nat_lit 897, Int.ofNat (nat_lit 12188897280)), (nat_lit 898, Int.ofNat (nat_lit 8198184960)), (nat_lit 899, Int.ofNat (nat_lit 9925534080)), (nat_lit 914, Int.ofNat (nat_lit 8286435000)), (nat_lit 915, Int.ofNat (nat_lit 12894527160)), (nat_lit 916, Int.ofNat (nat_lit 8358624720)), (nat_lit 917, Int.ofNat (nat_lit 10676419920)), (nat_lit 933, Int.ofNat (nat_lit 4296499200)), (nat_lit 934, Int.ofNat (nat_lit 5555934720)), (nat_lit 935, Int.ofNat (nat_lit 8244432000)), (nat_lit 952, Int.ofNat (nat_lit 572866560)), (nat_lit 953, Int.ofNat (nat_lit 3862212480)), (nat_lit 971, Int.ofNat (nat_lit 2854776960)), (nat_lit 1029, Int.ofNat (nat_lit 249016320)), (nat_lit 1030, Int.ofNat (nat_lit 633507840)), (nat_lit 1031, Int.ofNat (nat_lit 519966720)), (nat_lit 1032, Int.ofNat (nat_lit 406425600)), (nat_lit 1033, Int.ofNat (nat_lit 292884480)), (nat_lit 1034, Int.ofNat (nat_lit 230576640)), (nat_lit 1035, Int.ofNat (nat_lit 108003840)), (nat_lit 1036, Int.ofNat (nat_lit 10590720)), (nat_lit 1038, Int.ofNat (nat_lit 1501839360)), (nat_lit 1040, Int.ofNat (nat_lit 1167149520)), (nat_lit 1048, Int.ofNat (nat_lit 1344806400)), (nat_lit 1049, Int.ofNat (nat_lit 1764439680)), (nat_lit 1050, Int.ofNat (nat_lit 766439040)), (nat_lit 1051, Int.ofNat (nat_lit 245414400)), (nat_lit 1052, Int.ofNat (nat_lit 208266240)), (nat_lit 1053, Int.ofNat (nat_lit 164398080)), (nat_lit 1054, Int.ofNat (nat_lit 170849280)), (nat_lit 1055, Int.ofNat (nat_lit 264122880)), (nat_lit 1056, Int.ofNat (nat_lit 3555901440)), (nat_lit 1057, Int.ofNat (nat_lit 936962880)), (nat_lit 1058, Int.ofNat (nat_lit 3289076640)), (nat_lit 1059, Int.ofNat (nat_lit 2074914240)), (nat_lit 1060, Int.ofNat (nat_lit 2798927040)), (nat_lit 1061, Int.ofNat (nat_lit 3522939840)), (nat_lit 1067, Int.ofNat (nat_lit 1300867200))]
theorem block007_data_flat157_step : block007_data_flat157 = (CoefficientMerge.fastMerge block007_data_flat117 block007_data_flat156) := by decide +kernel
theorem block007_data_flat157_original : block007_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4665765888 : Int) atom0535Coded) (CoefficientMerge.scale (12464877240 : Int) atom0536Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12188897280 : Int) atom0537Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8198184960 : Int) atom0538Coded) (CoefficientMerge.scale (9925534080 : Int) atom0539Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8286435000 : Int) atom0540Coded) (CoefficientMerge.scale (12894527160 : Int) atom0541Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8358624720 : Int) atom0542Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10676419920 : Int) atom0543Coded) (CoefficientMerge.scale (4296499200 : Int) atom0544Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5555934720 : Int) atom0545Coded) (CoefficientMerge.scale (8244432000 : Int) atom0546Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (572866560 : Int) atom0547Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3862212480 : Int) atom0548Coded) (CoefficientMerge.scale (2854776960 : Int) atom0549Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (249016320 : Int) atom0550Coded) (CoefficientMerge.scale (633507840 : Int) atom0551Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519966720 : Int) atom0552Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (406425600 : Int) atom0553Coded) (CoefficientMerge.scale (292884480 : Int) atom0554Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (230576640 : Int) atom0555Coded) (CoefficientMerge.scale (108003840 : Int) atom0556Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10590720 : Int) atom0557Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1501839360 : Int) atom0558Coded) (CoefficientMerge.scale (1167149520 : Int) atom0559Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1344806400 : Int) atom0560Coded) (CoefficientMerge.scale (1764439680 : Int) atom0561Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (766439040 : Int) atom0562Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245414400 : Int) atom0563Coded) (CoefficientMerge.scale (208266240 : Int) atom0564Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (164398080 : Int) atom0565Coded) (CoefficientMerge.scale (170849280 : Int) atom0566Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264122880 : Int) atom0567Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3555901440 : Int) atom0568Coded) (CoefficientMerge.scale (936962880 : Int) atom0569Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3289076640 : Int) atom0570Coded) (CoefficientMerge.scale (2074914240 : Int) atom0571Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2798927040 : Int) atom0572Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3522939840 : Int) atom0573Coded) (CoefficientMerge.scale (1300867200 : Int) atom0574Coded))))))) := by
  rw [block007_data_flat157_step, block007_data_flat117_original, block007_data_flat156_original]
def block007_data_flat158 : CoefficientMerge.Poly := [(nat_lit 800, Int.ofNat (nat_lit 3718671360)), (nat_lit 801, Int.ofNat (nat_lit 6793720320)), (nat_lit 802, Int.ofNat (nat_lit 6517608960)), (nat_lit 803, Int.ofNat (nat_lit 6167040000)), (nat_lit 804, Int.ofNat (nat_lit 7979381760)), (nat_lit 805, Int.ofNat (nat_lit 6566323200)), (nat_lit 806, Int.ofNat (nat_lit 8933124000)), (nat_lit 807, Int.ofNat (nat_lit 7949368320)), (nat_lit 808, Int.ofNat (nat_lit 8692055040)), (nat_lit 809, Int.ofNat (nat_lit 10609182720)), (nat_lit 819, Int.ofNat (nat_lit 4164011520)), (nat_lit 820, Int.ofNat (nat_lit 7503144960)), (nat_lit 821, Int.ofNat (nat_lit 6954524160)), (nat_lit 822, Int.ofNat (nat_lit 8592628800)), (nat_lit 823, Int.ofNat (nat_lit 7029147840)), (nat_lit 824, Int.ofNat (nat_lit 9631143840)), (nat_lit 825, Int.ofNat (nat_lit 8158977600)), (nat_lit 826, Int.ofNat (nat_lit 8798871360)), (nat_lit 827, Int.ofNat (nat_lit 10613206080)), (nat_lit 838, Int.ofNat (nat_lit 4531960320)), (nat_lit 839, Int.ofNat (nat_lit 7932940800)), (nat_lit 840, Int.ofNat (nat_lit 9311655360)), (nat_lit 841, Int.ofNat (nat_lit 7477765440)), (nat_lit 842, Int.ofNat (nat_lit 10379483040)), (nat_lit 843, Int.ofNat (nat_lit 8044739520)), (nat_lit 844, Int.ofNat (nat_lit 8392186560)), (nat_lit 845, Int.ofNat (nat_lit 10204830720)), (nat_lit 857, Int.ofNat (nat_lit 4927426560)), (nat_lit 858, Int.ofNat (nat_lit 9870336000)), (nat_lit 859, Int.ofNat (nat_lit 7722086400)), (nat_lit 860, Int.ofNat (nat_lit 10978907040)), (nat_lit 861, Int.ofNat (nat_lit 8678154240)), (nat_lit 862, Int.ofNat (nat_lit 7662090240)), (nat_lit 863, Int.ofNat (nat_lit 11373788160)), (nat_lit 876, Int.ofNat (nat_lit 6543452160)), (nat_lit 877, Int.ofNat (nat_lit 10721894400)), (nat_lit 878, Int.ofNat (nat_lit 15248311200)), (nat_lit 879, Int.ofNat (nat_lit 13098516480)), (nat_lit 880, Int.ofNat (nat_lit 7930137600)), (nat_lit 881, Int.ofNat (nat_lit 12465129600)), (nat_lit 895, Int.ofNat (nat_lit 4665765888)), (nat_lit 896, Int.ofNat (nat_lit 12464877240)), (nat_lit 897, Int.ofNat (nat_lit 12188897280)), (nat_lit 898, Int.ofNat (nat_lit 8198184960)), (nat_lit 899, Int.ofNat (nat_lit 9925534080)), (nat_lit 914, Int.ofNat (nat_lit 8286435000)), (nat_lit 915, Int.ofNat (nat_lit 12894527160)), (nat_lit 916, Int.ofNat (nat_lit 8358624720)), (nat_lit 917, Int.ofNat (nat_lit 10676419920)), (nat_lit 933, Int.ofNat (nat_lit 4296499200)), (nat_lit 934, Int.ofNat (nat_lit 5555934720)), (nat_lit 935, Int.ofNat (nat_lit 8244432000)), (nat_lit 952, Int.ofNat (nat_lit 572866560)), (nat_lit 953, Int.ofNat (nat_lit 3862212480)), (nat_lit 971, Int.ofNat (nat_lit 2854776960)), (nat_lit 1029, Int.ofNat (nat_lit 249016320)), (nat_lit 1030, Int.ofNat (nat_lit 633507840)), (nat_lit 1031, Int.ofNat (nat_lit 519966720)), (nat_lit 1032, Int.ofNat (nat_lit 406425600)), (nat_lit 1033, Int.ofNat (nat_lit 292884480)), (nat_lit 1034, Int.ofNat (nat_lit 230576640)), (nat_lit 1035, Int.ofNat (nat_lit 108003840)), (nat_lit 1036, Int.ofNat (nat_lit 10590720)), (nat_lit 1038, Int.ofNat (nat_lit 1501839360)), (nat_lit 1040, Int.ofNat (nat_lit 1167149520)), (nat_lit 1048, Int.ofNat (nat_lit 1344806400)), (nat_lit 1049, Int.ofNat (nat_lit 1764439680)), (nat_lit 1050, Int.ofNat (nat_lit 766439040)), (nat_lit 1051, Int.ofNat (nat_lit 245414400)), (nat_lit 1052, Int.ofNat (nat_lit 208266240)), (nat_lit 1053, Int.ofNat (nat_lit 164398080)), (nat_lit 1054, Int.ofNat (nat_lit 170849280)), (nat_lit 1055, Int.ofNat (nat_lit 264122880)), (nat_lit 1056, Int.ofNat (nat_lit 3555901440)), (nat_lit 1057, Int.ofNat (nat_lit 936962880)), (nat_lit 1058, Int.ofNat (nat_lit 3289076640)), (nat_lit 1059, Int.ofNat (nat_lit 2074914240)), (nat_lit 1060, Int.ofNat (nat_lit 2798927040)), (nat_lit 1061, Int.ofNat (nat_lit 3522939840)), (nat_lit 1067, Int.ofNat (nat_lit 1300867200))]
theorem block007_data_flat158_step : block007_data_flat158 = (CoefficientMerge.fastMerge block007_data_flat078 block007_data_flat157) := by decide +kernel
theorem block007_data_flat158_original : block007_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3718671360 : Int) atom0495Coded) (CoefficientMerge.scale (6793720320 : Int) atom0496Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6517608960 : Int) atom0497Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6167040000 : Int) atom0498Coded) (CoefficientMerge.scale (7979381760 : Int) atom0499Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6566323200 : Int) atom0500Coded) (CoefficientMerge.scale (8933124000 : Int) atom0501Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7949368320 : Int) atom0502Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8692055040 : Int) atom0503Coded) (CoefficientMerge.scale (10609182720 : Int) atom0504Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4164011520 : Int) atom0505Coded) (CoefficientMerge.scale (7503144960 : Int) atom0506Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6954524160 : Int) atom0507Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8592628800 : Int) atom0508Coded) (CoefficientMerge.scale (7029147840 : Int) atom0509Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9631143840 : Int) atom0510Coded) (CoefficientMerge.scale (8158977600 : Int) atom0511Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8798871360 : Int) atom0512Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10613206080 : Int) atom0513Coded) (CoefficientMerge.scale (4531960320 : Int) atom0514Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7932940800 : Int) atom0515Coded) (CoefficientMerge.scale (9311655360 : Int) atom0516Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7477765440 : Int) atom0517Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10379483040 : Int) atom0518Coded) (CoefficientMerge.scale (8044739520 : Int) atom0519Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8392186560 : Int) atom0520Coded) (CoefficientMerge.scale (10204830720 : Int) atom0521Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4927426560 : Int) atom0522Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9870336000 : Int) atom0523Coded) (CoefficientMerge.scale (7722086400 : Int) atom0524Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10978907040 : Int) atom0525Coded) (CoefficientMerge.scale (8678154240 : Int) atom0526Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7662090240 : Int) atom0527Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11373788160 : Int) atom0528Coded) (CoefficientMerge.scale (6543452160 : Int) atom0529Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10721894400 : Int) atom0530Coded) (CoefficientMerge.scale (15248311200 : Int) atom0531Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13098516480 : Int) atom0532Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7930137600 : Int) atom0533Coded) (CoefficientMerge.scale (12465129600 : Int) atom0534Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4665765888 : Int) atom0535Coded) (CoefficientMerge.scale (12464877240 : Int) atom0536Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12188897280 : Int) atom0537Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8198184960 : Int) atom0538Coded) (CoefficientMerge.scale (9925534080 : Int) atom0539Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8286435000 : Int) atom0540Coded) (CoefficientMerge.scale (12894527160 : Int) atom0541Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8358624720 : Int) atom0542Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10676419920 : Int) atom0543Coded) (CoefficientMerge.scale (4296499200 : Int) atom0544Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5555934720 : Int) atom0545Coded) (CoefficientMerge.scale (8244432000 : Int) atom0546Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (572866560 : Int) atom0547Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3862212480 : Int) atom0548Coded) (CoefficientMerge.scale (2854776960 : Int) atom0549Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (249016320 : Int) atom0550Coded) (CoefficientMerge.scale (633507840 : Int) atom0551Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519966720 : Int) atom0552Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (406425600 : Int) atom0553Coded) (CoefficientMerge.scale (292884480 : Int) atom0554Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (230576640 : Int) atom0555Coded) (CoefficientMerge.scale (108003840 : Int) atom0556Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10590720 : Int) atom0557Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1501839360 : Int) atom0558Coded) (CoefficientMerge.scale (1167149520 : Int) atom0559Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1344806400 : Int) atom0560Coded) (CoefficientMerge.scale (1764439680 : Int) atom0561Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (766439040 : Int) atom0562Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245414400 : Int) atom0563Coded) (CoefficientMerge.scale (208266240 : Int) atom0564Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (164398080 : Int) atom0565Coded) (CoefficientMerge.scale (170849280 : Int) atom0566Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264122880 : Int) atom0567Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3555901440 : Int) atom0568Coded) (CoefficientMerge.scale (936962880 : Int) atom0569Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3289076640 : Int) atom0570Coded) (CoefficientMerge.scale (2074914240 : Int) atom0571Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2798927040 : Int) atom0572Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3522939840 : Int) atom0573Coded) (CoefficientMerge.scale (1300867200 : Int) atom0574Coded)))))))) := by
  rw [block007_data_flat158_step, block007_data_flat078_original, block007_data_flat157_original]
def block007_data_flat159 : CoefficientMerge.Poly := [(nat_lit 800, Int.ofNat (nat_lit 3718671360)), (nat_lit 801, Int.ofNat (nat_lit 6793720320)), (nat_lit 802, Int.ofNat (nat_lit 6517608960)), (nat_lit 803, Int.ofNat (nat_lit 6167040000)), (nat_lit 804, Int.ofNat (nat_lit 7979381760)), (nat_lit 805, Int.ofNat (nat_lit 6566323200)), (nat_lit 806, Int.ofNat (nat_lit 8933124000)), (nat_lit 807, Int.ofNat (nat_lit 7949368320)), (nat_lit 808, Int.ofNat (nat_lit 8692055040)), (nat_lit 809, Int.ofNat (nat_lit 10609182720)), (nat_lit 819, Int.ofNat (nat_lit 4164011520)), (nat_lit 820, Int.ofNat (nat_lit 7503144960)), (nat_lit 821, Int.ofNat (nat_lit 6954524160)), (nat_lit 822, Int.ofNat (nat_lit 8592628800)), (nat_lit 823, Int.ofNat (nat_lit 7029147840)), (nat_lit 824, Int.ofNat (nat_lit 9631143840)), (nat_lit 825, Int.ofNat (nat_lit 8158977600)), (nat_lit 826, Int.ofNat (nat_lit 8798871360)), (nat_lit 827, Int.ofNat (nat_lit 10613206080)), (nat_lit 838, Int.ofNat (nat_lit 4531960320)), (nat_lit 839, Int.ofNat (nat_lit 7932940800)), (nat_lit 840, Int.ofNat (nat_lit 9311655360)), (nat_lit 841, Int.ofNat (nat_lit 7477765440)), (nat_lit 842, Int.ofNat (nat_lit 10379483040)), (nat_lit 843, Int.ofNat (nat_lit 8044739520)), (nat_lit 844, Int.ofNat (nat_lit 8392186560)), (nat_lit 845, Int.ofNat (nat_lit 10204830720)), (nat_lit 857, Int.ofNat (nat_lit 4927426560)), (nat_lit 858, Int.ofNat (nat_lit 9870336000)), (nat_lit 859, Int.ofNat (nat_lit 7722086400)), (nat_lit 860, Int.ofNat (nat_lit 10978907040)), (nat_lit 861, Int.ofNat (nat_lit 8678154240)), (nat_lit 862, Int.ofNat (nat_lit 7662090240)), (nat_lit 863, Int.ofNat (nat_lit 11373788160)), (nat_lit 876, Int.ofNat (nat_lit 6543452160)), (nat_lit 877, Int.ofNat (nat_lit 10721894400)), (nat_lit 878, Int.ofNat (nat_lit 15248311200)), (nat_lit 879, Int.ofNat (nat_lit 13098516480)), (nat_lit 880, Int.ofNat (nat_lit 7930137600)), (nat_lit 881, Int.ofNat (nat_lit 12465129600)), (nat_lit 895, Int.ofNat (nat_lit 4665765888)), (nat_lit 896, Int.ofNat (nat_lit 12464877240)), (nat_lit 897, Int.ofNat (nat_lit 12188897280)), (nat_lit 898, Int.ofNat (nat_lit 8198184960)), (nat_lit 899, Int.ofNat (nat_lit 9925534080)), (nat_lit 914, Int.ofNat (nat_lit 8286435000)), (nat_lit 915, Int.ofNat (nat_lit 12894527160)), (nat_lit 916, Int.ofNat (nat_lit 8358624720)), (nat_lit 917, Int.ofNat (nat_lit 10676419920)), (nat_lit 933, Int.ofNat (nat_lit 4296499200)), (nat_lit 934, Int.ofNat (nat_lit 5555934720)), (nat_lit 935, Int.ofNat (nat_lit 8244432000)), (nat_lit 952, Int.ofNat (nat_lit 572866560)), (nat_lit 953, Int.ofNat (nat_lit 3862212480)), (nat_lit 971, Int.ofNat (nat_lit 2854776960)), (nat_lit 1029, Int.ofNat (nat_lit 249016320)), (nat_lit 1030, Int.ofNat (nat_lit 633507840)), (nat_lit 1031, Int.ofNat (nat_lit 519966720)), (nat_lit 1032, Int.ofNat (nat_lit 406425600)), (nat_lit 1033, Int.ofNat (nat_lit 292884480)), (nat_lit 1034, Int.ofNat (nat_lit 230576640)), (nat_lit 1035, Int.ofNat (nat_lit 108003840)), (nat_lit 1036, Int.ofNat (nat_lit 10590720)), (nat_lit 1038, Int.ofNat (nat_lit 1501839360)), (nat_lit 1040, Int.ofNat (nat_lit 1167149520)), (nat_lit 1048, Int.ofNat (nat_lit 1344806400)), (nat_lit 1049, Int.ofNat (nat_lit 1764439680)), (nat_lit 1050, Int.ofNat (nat_lit 766439040)), (nat_lit 1051, Int.ofNat (nat_lit 245414400)), (nat_lit 1052, Int.ofNat (nat_lit 208266240)), (nat_lit 1053, Int.ofNat (nat_lit 164398080)), (nat_lit 1054, Int.ofNat (nat_lit 170849280)), (nat_lit 1055, Int.ofNat (nat_lit 264122880)), (nat_lit 1056, Int.ofNat (nat_lit 3555901440)), (nat_lit 1057, Int.ofNat (nat_lit 936962880)), (nat_lit 1058, Int.ofNat (nat_lit 3289076640)), (nat_lit 1059, Int.ofNat (nat_lit 2074914240)), (nat_lit 1060, Int.ofNat (nat_lit 2798927040)), (nat_lit 1061, Int.ofNat (nat_lit 3522939840)), (nat_lit 1067, Int.ofNat (nat_lit 1300867200))]
theorem block007_data_flat159_step : block007_data_flat159 = (CoefficientMerge.trim block007_data_flat158) := by decide +kernel
theorem block007_data_flat159_original : block007_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3718671360 : Int) atom0495Coded) (CoefficientMerge.scale (6793720320 : Int) atom0496Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6517608960 : Int) atom0497Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6167040000 : Int) atom0498Coded) (CoefficientMerge.scale (7979381760 : Int) atom0499Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6566323200 : Int) atom0500Coded) (CoefficientMerge.scale (8933124000 : Int) atom0501Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7949368320 : Int) atom0502Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8692055040 : Int) atom0503Coded) (CoefficientMerge.scale (10609182720 : Int) atom0504Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4164011520 : Int) atom0505Coded) (CoefficientMerge.scale (7503144960 : Int) atom0506Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6954524160 : Int) atom0507Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8592628800 : Int) atom0508Coded) (CoefficientMerge.scale (7029147840 : Int) atom0509Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9631143840 : Int) atom0510Coded) (CoefficientMerge.scale (8158977600 : Int) atom0511Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8798871360 : Int) atom0512Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10613206080 : Int) atom0513Coded) (CoefficientMerge.scale (4531960320 : Int) atom0514Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7932940800 : Int) atom0515Coded) (CoefficientMerge.scale (9311655360 : Int) atom0516Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7477765440 : Int) atom0517Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10379483040 : Int) atom0518Coded) (CoefficientMerge.scale (8044739520 : Int) atom0519Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8392186560 : Int) atom0520Coded) (CoefficientMerge.scale (10204830720 : Int) atom0521Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4927426560 : Int) atom0522Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9870336000 : Int) atom0523Coded) (CoefficientMerge.scale (7722086400 : Int) atom0524Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10978907040 : Int) atom0525Coded) (CoefficientMerge.scale (8678154240 : Int) atom0526Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7662090240 : Int) atom0527Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11373788160 : Int) atom0528Coded) (CoefficientMerge.scale (6543452160 : Int) atom0529Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10721894400 : Int) atom0530Coded) (CoefficientMerge.scale (15248311200 : Int) atom0531Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13098516480 : Int) atom0532Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7930137600 : Int) atom0533Coded) (CoefficientMerge.scale (12465129600 : Int) atom0534Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4665765888 : Int) atom0535Coded) (CoefficientMerge.scale (12464877240 : Int) atom0536Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12188897280 : Int) atom0537Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8198184960 : Int) atom0538Coded) (CoefficientMerge.scale (9925534080 : Int) atom0539Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8286435000 : Int) atom0540Coded) (CoefficientMerge.scale (12894527160 : Int) atom0541Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8358624720 : Int) atom0542Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10676419920 : Int) atom0543Coded) (CoefficientMerge.scale (4296499200 : Int) atom0544Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5555934720 : Int) atom0545Coded) (CoefficientMerge.scale (8244432000 : Int) atom0546Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (572866560 : Int) atom0547Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3862212480 : Int) atom0548Coded) (CoefficientMerge.scale (2854776960 : Int) atom0549Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (249016320 : Int) atom0550Coded) (CoefficientMerge.scale (633507840 : Int) atom0551Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519966720 : Int) atom0552Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (406425600 : Int) atom0553Coded) (CoefficientMerge.scale (292884480 : Int) atom0554Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (230576640 : Int) atom0555Coded) (CoefficientMerge.scale (108003840 : Int) atom0556Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10590720 : Int) atom0557Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1501839360 : Int) atom0558Coded) (CoefficientMerge.scale (1167149520 : Int) atom0559Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1344806400 : Int) atom0560Coded) (CoefficientMerge.scale (1764439680 : Int) atom0561Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (766439040 : Int) atom0562Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245414400 : Int) atom0563Coded) (CoefficientMerge.scale (208266240 : Int) atom0564Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (164398080 : Int) atom0565Coded) (CoefficientMerge.scale (170849280 : Int) atom0566Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264122880 : Int) atom0567Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3555901440 : Int) atom0568Coded) (CoefficientMerge.scale (936962880 : Int) atom0569Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3289076640 : Int) atom0570Coded) (CoefficientMerge.scale (2074914240 : Int) atom0571Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2798927040 : Int) atom0572Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3522939840 : Int) atom0573Coded) (CoefficientMerge.scale (1300867200 : Int) atom0574Coded))))))))) := by
  rw [block007_data_flat159_step, block007_data_flat158_original]
theorem block007_data : block007 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3718671360 : Int) atom0495Coded) (CoefficientMerge.scale (6793720320 : Int) atom0496Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6517608960 : Int) atom0497Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6167040000 : Int) atom0498Coded) (CoefficientMerge.scale (7979381760 : Int) atom0499Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6566323200 : Int) atom0500Coded) (CoefficientMerge.scale (8933124000 : Int) atom0501Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7949368320 : Int) atom0502Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8692055040 : Int) atom0503Coded) (CoefficientMerge.scale (10609182720 : Int) atom0504Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4164011520 : Int) atom0505Coded) (CoefficientMerge.scale (7503144960 : Int) atom0506Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6954524160 : Int) atom0507Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8592628800 : Int) atom0508Coded) (CoefficientMerge.scale (7029147840 : Int) atom0509Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9631143840 : Int) atom0510Coded) (CoefficientMerge.scale (8158977600 : Int) atom0511Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8798871360 : Int) atom0512Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10613206080 : Int) atom0513Coded) (CoefficientMerge.scale (4531960320 : Int) atom0514Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7932940800 : Int) atom0515Coded) (CoefficientMerge.scale (9311655360 : Int) atom0516Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7477765440 : Int) atom0517Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10379483040 : Int) atom0518Coded) (CoefficientMerge.scale (8044739520 : Int) atom0519Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8392186560 : Int) atom0520Coded) (CoefficientMerge.scale (10204830720 : Int) atom0521Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4927426560 : Int) atom0522Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9870336000 : Int) atom0523Coded) (CoefficientMerge.scale (7722086400 : Int) atom0524Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10978907040 : Int) atom0525Coded) (CoefficientMerge.scale (8678154240 : Int) atom0526Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7662090240 : Int) atom0527Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11373788160 : Int) atom0528Coded) (CoefficientMerge.scale (6543452160 : Int) atom0529Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10721894400 : Int) atom0530Coded) (CoefficientMerge.scale (15248311200 : Int) atom0531Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13098516480 : Int) atom0532Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7930137600 : Int) atom0533Coded) (CoefficientMerge.scale (12465129600 : Int) atom0534Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4665765888 : Int) atom0535Coded) (CoefficientMerge.scale (12464877240 : Int) atom0536Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12188897280 : Int) atom0537Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8198184960 : Int) atom0538Coded) (CoefficientMerge.scale (9925534080 : Int) atom0539Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (8286435000 : Int) atom0540Coded) (CoefficientMerge.scale (12894527160 : Int) atom0541Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8358624720 : Int) atom0542Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10676419920 : Int) atom0543Coded) (CoefficientMerge.scale (4296499200 : Int) atom0544Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5555934720 : Int) atom0545Coded) (CoefficientMerge.scale (8244432000 : Int) atom0546Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (572866560 : Int) atom0547Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3862212480 : Int) atom0548Coded) (CoefficientMerge.scale (2854776960 : Int) atom0549Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (249016320 : Int) atom0550Coded) (CoefficientMerge.scale (633507840 : Int) atom0551Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519966720 : Int) atom0552Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (406425600 : Int) atom0553Coded) (CoefficientMerge.scale (292884480 : Int) atom0554Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (230576640 : Int) atom0555Coded) (CoefficientMerge.scale (108003840 : Int) atom0556Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10590720 : Int) atom0557Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1501839360 : Int) atom0558Coded) (CoefficientMerge.scale (1167149520 : Int) atom0559Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1344806400 : Int) atom0560Coded) (CoefficientMerge.scale (1764439680 : Int) atom0561Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (766439040 : Int) atom0562Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (245414400 : Int) atom0563Coded) (CoefficientMerge.scale (208266240 : Int) atom0564Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (164398080 : Int) atom0565Coded) (CoefficientMerge.scale (170849280 : Int) atom0566Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (264122880 : Int) atom0567Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3555901440 : Int) atom0568Coded) (CoefficientMerge.scale (936962880 : Int) atom0569Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3289076640 : Int) atom0570Coded) (CoefficientMerge.scale (2074914240 : Int) atom0571Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2798927040 : Int) atom0572Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3522939840 : Int) atom0573Coded) (CoefficientMerge.scale (1300867200 : Int) atom0574Coded)))))))) := by
  have h : block007 = block007_data_flat159 := by decide +kernel
  exact h.trans block007_data_flat159_original
theorem block007_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) block007 := by
  rw [block007_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0495Coded_nonneg g hg hA hB) (atom0496Coded_nonneg g hg hA hB)) (add_nonneg (atom0497Coded_nonneg g hg hA hB) (add_nonneg (atom0498Coded_nonneg g hg hA hB) (atom0499Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0500Coded_nonneg g hg hA hB) (atom0501Coded_nonneg g hg hA hB)) (add_nonneg (atom0502Coded_nonneg g hg hA hB) (add_nonneg (atom0503Coded_nonneg g hg hA hB) (atom0504Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0505Coded_nonneg g hg hA hB) (atom0506Coded_nonneg g hg hA hB)) (add_nonneg (atom0507Coded_nonneg g hg hA hB) (add_nonneg (atom0508Coded_nonneg g hg hA hB) (atom0509Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0510Coded_nonneg g hg hA hB) (atom0511Coded_nonneg g hg hA hB)) (add_nonneg (atom0512Coded_nonneg g hg hA hB) (add_nonneg (atom0513Coded_nonneg g hg hA hB) (atom0514Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0515Coded_nonneg g hg hA hB) (atom0516Coded_nonneg g hg hA hB)) (add_nonneg (atom0517Coded_nonneg g hg hA hB) (add_nonneg (atom0518Coded_nonneg g hg hA hB) (atom0519Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0520Coded_nonneg g hg hA hB) (atom0521Coded_nonneg g hg hA hB)) (add_nonneg (atom0522Coded_nonneg g hg hA hB) (add_nonneg (atom0523Coded_nonneg g hg hA hB) (atom0524Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0525Coded_nonneg g hg hA hB) (atom0526Coded_nonneg g hg hA hB)) (add_nonneg (atom0527Coded_nonneg g hg hA hB) (add_nonneg (atom0528Coded_nonneg g hg hA hB) (atom0529Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0530Coded_nonneg g hg hA hB) (atom0531Coded_nonneg g hg hA hB)) (add_nonneg (atom0532Coded_nonneg g hg hA hB) (add_nonneg (atom0533Coded_nonneg g hg hA hB) (atom0534Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0535Coded_nonneg g hg hA hB) (atom0536Coded_nonneg g hg hA hB)) (add_nonneg (atom0537Coded_nonneg g hg hA hB) (add_nonneg (atom0538Coded_nonneg g hg hA hB) (atom0539Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0540Coded_nonneg g hg hA hB) (atom0541Coded_nonneg g hg hA hB)) (add_nonneg (atom0542Coded_nonneg g hg hA hB) (add_nonneg (atom0543Coded_nonneg g hg hA hB) (atom0544Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0545Coded_nonneg g hg hA hB) (atom0546Coded_nonneg g hg hA hB)) (add_nonneg (atom0547Coded_nonneg g hg hA hB) (add_nonneg (atom0548Coded_nonneg g hg hA hB) (atom0549Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0550Coded_nonneg g hg hA hB) (atom0551Coded_nonneg g hg hA hB)) (add_nonneg (atom0552Coded_nonneg g hg hA hB) (add_nonneg (atom0553Coded_nonneg g hg hA hB) (atom0554Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0555Coded_nonneg g hg hA hB) (atom0556Coded_nonneg g hg hA hB)) (add_nonneg (atom0557Coded_nonneg g hg hA hB) (add_nonneg (atom0558Coded_nonneg g hg hA hB) (atom0559Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0560Coded_nonneg g hg hA hB) (atom0561Coded_nonneg g hg hA hB)) (add_nonneg (atom0562Coded_nonneg g hg hA hB) (add_nonneg (atom0563Coded_nonneg g hg hA hB) (atom0564Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0565Coded_nonneg g hg hA hB) (atom0566Coded_nonneg g hg hA hB)) (add_nonneg (atom0567Coded_nonneg g hg hA hB) (add_nonneg (atom0568Coded_nonneg g hg hA hB) (atom0569Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0570Coded_nonneg g hg hA hB) (atom0571Coded_nonneg g hg hA hB)) (add_nonneg (atom0572Coded_nonneg g hg hA hB) (add_nonneg (atom0573Coded_nonneg g hg hA hB) (atom0574Coded_nonneg g hg hA hB))))))))

end APPT.Finite18
