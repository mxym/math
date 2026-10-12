-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0496 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0496 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0496 = ((g 1) * (g 9) * (g 12)) := by
  norm_num [atom0496, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0496_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30403816464000 : Int) atom0496) := by
  rw [SparsePolynomial.eval_scale, eval_atom0496]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0496Coded : CoefficientMerge.Poly := [(nat_lit 642, Int.ofNat (nat_lit 1))]
theorem atom0496Coded_decode : atom0496 = SparsePolynomial.decodeCubic 21 atom0496Coded := by decide +kernel
theorem atom0496Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30403816464000 : Int) atom0496Coded) := by
  have h := atom0496_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0496Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0497 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0497 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0497 = ((g 1) * (g 9) * (g 13)) := by
  norm_num [atom0497, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0497_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29787423120000 : Int) atom0497) := by
  rw [SparsePolynomial.eval_scale, eval_atom0497]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0497Coded : CoefficientMerge.Poly := [(nat_lit 643, Int.ofNat (nat_lit 1))]
theorem atom0497Coded_decode : atom0497 = SparsePolynomial.decodeCubic 21 atom0497Coded := by decide +kernel
theorem atom0497Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29787423120000 : Int) atom0497Coded) := by
  have h := atom0497_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0497Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0498 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0498 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0498 = ((g 1) * (g 9) * (g 14)) := by
  norm_num [atom0498, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0498_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30487147689600 : Int) atom0498) := by
  rw [SparsePolynomial.eval_scale, eval_atom0498]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0498Coded : CoefficientMerge.Poly := [(nat_lit 644, Int.ofNat (nat_lit 1))]
theorem atom0498Coded_decode : atom0498 = SparsePolynomial.decodeCubic 21 atom0498Coded := by decide +kernel
theorem atom0498Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30487147689600 : Int) atom0498Coded) := by
  have h := atom0498_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0498Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0499 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0499 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0499 = ((g 1) * (g 9) * (g 15)) := by
  norm_num [atom0499, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0499_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39992545152000 : Int) atom0499) := by
  rw [SparsePolynomial.eval_scale, eval_atom0499]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0499Coded : CoefficientMerge.Poly := [(nat_lit 645, Int.ofNat (nat_lit 1))]
theorem atom0499Coded_decode : atom0499 = SparsePolynomial.decodeCubic 21 atom0499Coded := by decide +kernel
theorem atom0499Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39992545152000 : Int) atom0499Coded) := by
  have h := atom0499_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0499Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0500 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0500 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0500 = ((g 1) * (g 9) * (g 16)) := by
  norm_num [atom0500, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0500_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34392272014800 : Int) atom0500) := by
  rw [SparsePolynomial.eval_scale, eval_atom0500]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0500Coded : CoefficientMerge.Poly := [(nat_lit 646, Int.ofNat (nat_lit 1))]
theorem atom0500Coded_decode : atom0500 = SparsePolynomial.decodeCubic 21 atom0500Coded := by decide +kernel
theorem atom0500Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34392272014800 : Int) atom0500Coded) := by
  have h := atom0500_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0500Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0501 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0501 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0501 = ((g 1) * (g 9) * (g 17)) := by
  norm_num [atom0501, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0501_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41077582963200 : Int) atom0501) := by
  rw [SparsePolynomial.eval_scale, eval_atom0501]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0501Coded : CoefficientMerge.Poly := [(nat_lit 647, Int.ofNat (nat_lit 1))]
theorem atom0501Coded_decode : atom0501 = SparsePolynomial.decodeCubic 21 atom0501Coded := by decide +kernel
theorem atom0501Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41077582963200 : Int) atom0501Coded) := by
  have h := atom0501_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0501Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0502 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0502 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0502 = ((g 1) * (g 9) * (g 18)) := by
  norm_num [atom0502, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0502_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39334036518000 : Int) atom0502) := by
  rw [SparsePolynomial.eval_scale, eval_atom0502]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0502Coded : CoefficientMerge.Poly := [(nat_lit 648, Int.ofNat (nat_lit 1))]
theorem atom0502Coded_decode : atom0502 = SparsePolynomial.decodeCubic 21 atom0502Coded := by decide +kernel
theorem atom0502Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39334036518000 : Int) atom0502Coded) := by
  have h := atom0502_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0502Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0503 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0503 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0503 = ((g 1) * (g 9) * (g 19)) := by
  norm_num [atom0503, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0503_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35737719620400 : Int) atom0503) := by
  rw [SparsePolynomial.eval_scale, eval_atom0503]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0503Coded : CoefficientMerge.Poly := [(nat_lit 649, Int.ofNat (nat_lit 1))]
theorem atom0503Coded_decode : atom0503 = SparsePolynomial.decodeCubic 21 atom0503Coded := by decide +kernel
theorem atom0503Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35737719620400 : Int) atom0503Coded) := by
  have h := atom0503_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0503Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0504 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0504 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0504 = ((g 1) * (g 9) * (g 20)) := by
  norm_num [atom0504, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0504_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36469257174000 : Int) atom0504) := by
  rw [SparsePolynomial.eval_scale, eval_atom0504]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0504Coded : CoefficientMerge.Poly := [(nat_lit 650, Int.ofNat (nat_lit 1))]
theorem atom0504Coded_decode : atom0504 = SparsePolynomial.decodeCubic 21 atom0504Coded := by decide +kernel
theorem atom0504Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36469257174000 : Int) atom0504Coded) := by
  have h := atom0504_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0504Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0505 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0505 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0505 = ((g 1) * (g 10) * (g 10)) := by
  norm_num [atom0505, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0505_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22070559672000 : Int) atom0505) := by
  rw [SparsePolynomial.eval_scale, eval_atom0505]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0505Coded : CoefficientMerge.Poly := [(nat_lit 661, Int.ofNat (nat_lit 1))]
theorem atom0505Coded_decode : atom0505 = SparsePolynomial.decodeCubic 21 atom0505Coded := by decide +kernel
theorem atom0505Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22070559672000 : Int) atom0505Coded) := by
  have h := atom0505_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0505Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0506 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0506 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0506 = ((g 1) * (g 10) * (g 11)) := by
  norm_num [atom0506, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0506_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39833095538880 : Int) atom0506) := by
  rw [SparsePolynomial.eval_scale, eval_atom0506]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0506Coded : CoefficientMerge.Poly := [(nat_lit 662, Int.ofNat (nat_lit 1))]
theorem atom0506Coded_decode : atom0506 = SparsePolynomial.decodeCubic 21 atom0506Coded := by decide +kernel
theorem atom0506Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39833095538880 : Int) atom0506Coded) := by
  have h := atom0506_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0506Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0507 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0507 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0507 = ((g 1) * (g 10) * (g 12)) := by
  norm_num [atom0507, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0507_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33381177081280 : Int) atom0507) := by
  rw [SparsePolynomial.eval_scale, eval_atom0507]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0507Coded : CoefficientMerge.Poly := [(nat_lit 663, Int.ofNat (nat_lit 1))]
theorem atom0507Coded_decode : atom0507 = SparsePolynomial.decodeCubic 21 atom0507Coded := by decide +kernel
theorem atom0507Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33381177081280 : Int) atom0507Coded) := by
  have h := atom0507_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0507Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0508 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0508 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0508 = ((g 1) * (g 10) * (g 13)) := by
  norm_num [atom0508, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0508_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32429753193600 : Int) atom0508) := by
  rw [SparsePolynomial.eval_scale, eval_atom0508]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0508Coded : CoefficientMerge.Poly := [(nat_lit 664, Int.ofNat (nat_lit 1))]
theorem atom0508Coded_decode : atom0508 = SparsePolynomial.decodeCubic 21 atom0508Coded := by decide +kernel
theorem atom0508Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32429753193600 : Int) atom0508Coded) := by
  have h := atom0508_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0508Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0509 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0509 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0509 = ((g 1) * (g 10) * (g 14)) := by
  norm_num [atom0509, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0509_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32838570172800 : Int) atom0509) := by
  rw [SparsePolynomial.eval_scale, eval_atom0509]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0509Coded : CoefficientMerge.Poly := [(nat_lit 665, Int.ofNat (nat_lit 1))]
theorem atom0509Coded_decode : atom0509 = SparsePolynomial.decodeCubic 21 atom0509Coded := by decide +kernel
theorem atom0509Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32838570172800 : Int) atom0509Coded) := by
  have h := atom0509_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0509Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0510 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0510 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0510 = ((g 1) * (g 10) * (g 15)) := by
  norm_num [atom0510, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0510_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42138109440000 : Int) atom0510) := by
  rw [SparsePolynomial.eval_scale, eval_atom0510]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0510Coded : CoefficientMerge.Poly := [(nat_lit 666, Int.ofNat (nat_lit 1))]
theorem atom0510Coded_decode : atom0510 = SparsePolynomial.decodeCubic 21 atom0510Coded := by decide +kernel
theorem atom0510Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42138109440000 : Int) atom0510Coded) := by
  have h := atom0510_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0510Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0511 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0511 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0511 = ((g 1) * (g 10) * (g 16)) := by
  norm_num [atom0511, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0511_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36296339511600 : Int) atom0511) := by
  rw [SparsePolynomial.eval_scale, eval_atom0511]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0511Coded : CoefficientMerge.Poly := [(nat_lit 667, Int.ofNat (nat_lit 1))]
theorem atom0511Coded_decode : atom0511 = SparsePolynomial.decodeCubic 21 atom0511Coded := by decide +kernel
theorem atom0511Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36296339511600 : Int) atom0511Coded) := by
  have h := atom0511_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0511Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0512 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0512 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0512 = ((g 1) * (g 10) * (g 17)) := by
  norm_num [atom0512, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0512_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43895810649600 : Int) atom0512) := by
  rw [SparsePolynomial.eval_scale, eval_atom0512]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0512Coded : CoefficientMerge.Poly := [(nat_lit 668, Int.ofNat (nat_lit 1))]
theorem atom0512Coded_decode : atom0512 = SparsePolynomial.decodeCubic 21 atom0512Coded := by decide +kernel
theorem atom0512Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43895810649600 : Int) atom0512Coded) := by
  have h := atom0512_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0512Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0513 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0513 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0513 = ((g 1) * (g 10) * (g 18)) := by
  norm_num [atom0513, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0513_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40925209222800 : Int) atom0513) := by
  rw [SparsePolynomial.eval_scale, eval_atom0513]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0513Coded : CoefficientMerge.Poly := [(nat_lit 669, Int.ofNat (nat_lit 1))]
theorem atom0513Coded_decode : atom0513 = SparsePolynomial.decodeCubic 21 atom0513Coded := by decide +kernel
theorem atom0513Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40925209222800 : Int) atom0513Coded) := by
  have h := atom0513_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0513Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0514 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0514 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0514 = ((g 1) * (g 10) * (g 19)) := by
  norm_num [atom0514, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0514_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36790085077200 : Int) atom0514) := by
  rw [SparsePolynomial.eval_scale, eval_atom0514]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0514Coded : CoefficientMerge.Poly := [(nat_lit 670, Int.ofNat (nat_lit 1))]
theorem atom0514Coded_decode : atom0514 = SparsePolynomial.decodeCubic 21 atom0514Coded := by decide +kernel
theorem atom0514Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36790085077200 : Int) atom0514Coded) := by
  have h := atom0514_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0514Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0515 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0515 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0515 = ((g 1) * (g 10) * (g 20)) := by
  norm_num [atom0515, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0515_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37409995299600 : Int) atom0515) := by
  rw [SparsePolynomial.eval_scale, eval_atom0515]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0515Coded : CoefficientMerge.Poly := [(nat_lit 671, Int.ofNat (nat_lit 1))]
theorem atom0515Coded_decode : atom0515 = SparsePolynomial.decodeCubic 21 atom0515Coded := by decide +kernel
theorem atom0515Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37409995299600 : Int) atom0515Coded) := by
  have h := atom0515_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0515Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0516 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0516 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0516 = ((g 1) * (g 11) * (g 11)) := by
  norm_num [atom0516, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0516_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23509942041600 : Int) atom0516) := by
  rw [SparsePolynomial.eval_scale, eval_atom0516]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0516Coded : CoefficientMerge.Poly := [(nat_lit 683, Int.ofNat (nat_lit 1))]
theorem atom0516Coded_decode : atom0516 = SparsePolynomial.decodeCubic 21 atom0516Coded := by decide +kernel
theorem atom0516Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23509942041600 : Int) atom0516Coded) := by
  have h := atom0516_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0516Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0517 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0517 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0517 = ((g 1) * (g 11) * (g 12)) := by
  norm_num [atom0517, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0517_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39142615079680 : Int) atom0517) := by
  rw [SparsePolynomial.eval_scale, eval_atom0517]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0517Coded : CoefficientMerge.Poly := [(nat_lit 684, Int.ofNat (nat_lit 1))]
theorem atom0517Coded_decode : atom0517 = SparsePolynomial.decodeCubic 21 atom0517Coded := by decide +kernel
theorem atom0517Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39142615079680 : Int) atom0517Coded) := by
  have h := atom0517_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0517Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0518 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0518 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0518 = ((g 1) * (g 11) * (g 13)) := by
  norm_num [atom0518, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0518_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34691663462400 : Int) atom0518) := by
  rw [SparsePolynomial.eval_scale, eval_atom0518]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0518Coded : CoefficientMerge.Poly := [(nat_lit 685, Int.ofNat (nat_lit 1))]
theorem atom0518Coded_decode : atom0518 = SparsePolynomial.decodeCubic 21 atom0518Coded := by decide +kernel
theorem atom0518Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34691663462400 : Int) atom0518Coded) := by
  have h := atom0518_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0518Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0519 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0519 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0519 = ((g 1) * (g 11) * (g 14)) := by
  norm_num [atom0519, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0519_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34725489926400 : Int) atom0519) := by
  rw [SparsePolynomial.eval_scale, eval_atom0519]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0519Coded : CoefficientMerge.Poly := [(nat_lit 686, Int.ofNat (nat_lit 1))]
theorem atom0519Coded_decode : atom0519 = SparsePolynomial.decodeCubic 21 atom0519Coded := by decide +kernel
theorem atom0519Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34725489926400 : Int) atom0519Coded) := by
  have h := atom0519_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0519Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0520 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0520 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0520 = ((g 1) * (g 11) * (g 15)) := by
  norm_num [atom0520, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0520_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43659826560000 : Int) atom0520) := by
  rw [SparsePolynomial.eval_scale, eval_atom0520]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0520Coded : CoefficientMerge.Poly := [(nat_lit 687, Int.ofNat (nat_lit 1))]
theorem atom0520Coded_decode : atom0520 = SparsePolynomial.decodeCubic 21 atom0520Coded := by decide +kernel
theorem atom0520Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43659826560000 : Int) atom0520Coded) := by
  have h := atom0520_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0520Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0521 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0521 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0521 = ((g 1) * (g 11) * (g 16)) := by
  norm_num [atom0521, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0521_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37535436288000 : Int) atom0521) := by
  rw [SparsePolynomial.eval_scale, eval_atom0521]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0521Coded : CoefficientMerge.Poly := [(nat_lit 688, Int.ofNat (nat_lit 1))]
theorem atom0521Coded_decode : atom0521 = SparsePolynomial.decodeCubic 21 atom0521Coded := by decide +kernel
theorem atom0521Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37535436288000 : Int) atom0521Coded) := by
  have h := atom0521_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0521Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0522 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0522 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0522 = ((g 1) * (g 11) * (g 17)) := by
  norm_num [atom0522, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0522_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46090191168000 : Int) atom0522) := by
  rw [SparsePolynomial.eval_scale, eval_atom0522]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0522Coded : CoefficientMerge.Poly := [(nat_lit 689, Int.ofNat (nat_lit 1))]
theorem atom0522Coded_decode : atom0522 = SparsePolynomial.decodeCubic 21 atom0522Coded := by decide +kernel
theorem atom0522Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46090191168000 : Int) atom0522Coded) := by
  have h := atom0522_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0522Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0523 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0523 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0523 = ((g 1) * (g 11) * (g 18)) := by
  norm_num [atom0523, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0523_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41618641075200 : Int) atom0523) := by
  rw [SparsePolynomial.eval_scale, eval_atom0523]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0523Coded : CoefficientMerge.Poly := [(nat_lit 690, Int.ofNat (nat_lit 1))]
theorem atom0523Coded_decode : atom0523 = SparsePolynomial.decodeCubic 21 atom0523Coded := by decide +kernel
theorem atom0523Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41618641075200 : Int) atom0523Coded) := by
  have h := atom0523_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0523Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0524 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0524 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0524 = ((g 1) * (g 11) * (g 19)) := by
  norm_num [atom0524, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0524_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37129480819200 : Int) atom0524) := by
  rw [SparsePolynomial.eval_scale, eval_atom0524]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0524Coded : CoefficientMerge.Poly := [(nat_lit 691, Int.ofNat (nat_lit 1))]
theorem atom0524Coded_decode : atom0524 = SparsePolynomial.decodeCubic 21 atom0524Coded := by decide +kernel
theorem atom0524Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37129480819200 : Int) atom0524Coded) := by
  have h := atom0524_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0524Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0525 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0525 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0525 = ((g 1) * (g 11) * (g 20)) := by
  norm_num [atom0525, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0525_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37510611264000 : Int) atom0525) := by
  rw [SparsePolynomial.eval_scale, eval_atom0525]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0525Coded : CoefficientMerge.Poly := [(nat_lit 692, Int.ofNat (nat_lit 1))]
theorem atom0525Coded_decode : atom0525 = SparsePolynomial.decodeCubic 21 atom0525Coded := by decide +kernel
theorem atom0525Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37510611264000 : Int) atom0525Coded) := by
  have h := atom0525_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0525Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0526 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0526 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0526 = ((g 1) * (g 12) * (g 12)) := by
  norm_num [atom0526, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0526_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21593669171200 : Int) atom0526) := by
  rw [SparsePolynomial.eval_scale, eval_atom0526]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0526Coded : CoefficientMerge.Poly := [(nat_lit 705, Int.ofNat (nat_lit 1))]
theorem atom0526Coded_decode : atom0526 = SparsePolynomial.decodeCubic 21 atom0526Coded := by decide +kernel
theorem atom0526Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21593669171200 : Int) atom0526Coded) := by
  have h := atom0526_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0526Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0527 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0527 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0527 = ((g 1) * (g 12) * (g 13)) := by
  norm_num [atom0527, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0527_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37959288304000 : Int) atom0527) := by
  rw [SparsePolynomial.eval_scale, eval_atom0527]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0527Coded : CoefficientMerge.Poly := [(nat_lit 706, Int.ofNat (nat_lit 1))]
theorem atom0527Coded_decode : atom0527 = SparsePolynomial.decodeCubic 21 atom0527Coded := by decide +kernel
theorem atom0527Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37959288304000 : Int) atom0527Coded) := by
  have h := atom0527_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0527Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0528 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0528 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0528 = ((g 1) * (g 12) * (g 14)) := by
  norm_num [atom0528, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0528_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34193114233600 : Int) atom0528) := by
  rw [SparsePolynomial.eval_scale, eval_atom0528]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0528Coded : CoefficientMerge.Poly := [(nat_lit 707, Int.ofNat (nat_lit 1))]
theorem atom0528Coded_decode : atom0528 = SparsePolynomial.decodeCubic 21 atom0528Coded := by decide +kernel
theorem atom0528Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34193114233600 : Int) atom0528Coded) := by
  have h := atom0528_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0528Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0529 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0529 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0529 = ((g 1) * (g 12) * (g 15)) := by
  norm_num [atom0529, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0529_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41082437401600 : Int) atom0529) := by
  rw [SparsePolynomial.eval_scale, eval_atom0529]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0529Coded : CoefficientMerge.Poly := [(nat_lit 708, Int.ofNat (nat_lit 1))]
theorem atom0529Coded_decode : atom0529 = SparsePolynomial.decodeCubic 21 atom0529Coded := by decide +kernel
theorem atom0529Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41082437401600 : Int) atom0529Coded) := by
  have h := atom0529_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0529Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0530 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0530 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0530 = ((g 1) * (g 12) * (g 16)) := by
  norm_num [atom0530, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0530_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36148462828800 : Int) atom0530) := by
  rw [SparsePolynomial.eval_scale, eval_atom0530]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0530Coded : CoefficientMerge.Poly := [(nat_lit 709, Int.ofNat (nat_lit 1))]
theorem atom0530Coded_decode : atom0530 = SparsePolynomial.decodeCubic 21 atom0530Coded := by decide +kernel
theorem atom0530Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36148462828800 : Int) atom0530Coded) := by
  have h := atom0530_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0530Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0531 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0531 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0531 = ((g 1) * (g 12) * (g 17)) := by
  norm_num [atom0531, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0531_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44185465408000 : Int) atom0531) := by
  rw [SparsePolynomial.eval_scale, eval_atom0531]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0531Coded : CoefficientMerge.Poly := [(nat_lit 710, Int.ofNat (nat_lit 1))]
theorem atom0531Coded_decode : atom0531 = SparsePolynomial.decodeCubic 21 atom0531Coded := by decide +kernel
theorem atom0531Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44185465408000 : Int) atom0531Coded) := by
  have h := atom0531_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0531Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0532 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0532 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0532 = ((g 1) * (g 12) * (g 18)) := by
  norm_num [atom0532, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0532_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40050247014400 : Int) atom0532) := by
  rw [SparsePolynomial.eval_scale, eval_atom0532]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0532Coded : CoefficientMerge.Poly := [(nat_lit 711, Int.ofNat (nat_lit 1))]
theorem atom0532Coded_decode : atom0532 = SparsePolynomial.decodeCubic 21 atom0532Coded := by decide +kernel
theorem atom0532Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40050247014400 : Int) atom0532Coded) := by
  have h := atom0532_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0532Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0533 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0533 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0533 = ((g 1) * (g 12) * (g 19)) := by
  norm_num [atom0533, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0533_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36979376806400 : Int) atom0533) := by
  rw [SparsePolynomial.eval_scale, eval_atom0533]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0533Coded : CoefficientMerge.Poly := [(nat_lit 712, Int.ofNat (nat_lit 1))]
theorem atom0533Coded_decode : atom0533 = SparsePolynomial.decodeCubic 21 atom0533Coded := by decide +kernel
theorem atom0533Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36979376806400 : Int) atom0533Coded) := by
  have h := atom0533_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0533Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0534 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0534 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0534 = ((g 1) * (g 12) * (g 20)) := by
  norm_num [atom0534, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0534_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37173350995200 : Int) atom0534) := by
  rw [SparsePolynomial.eval_scale, eval_atom0534]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0534Coded : CoefficientMerge.Poly := [(nat_lit 713, Int.ofNat (nat_lit 1))]
theorem atom0534Coded_decode : atom0534 = SparsePolynomial.decodeCubic 21 atom0534Coded := by decide +kernel
theorem atom0534Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37173350995200 : Int) atom0534Coded) := by
  have h := atom0534_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0534Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0535 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0535 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0535 = ((g 1) * (g 13) * (g 13)) := by
  norm_num [atom0535, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0535_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21868118640000 : Int) atom0535) := by
  rw [SparsePolynomial.eval_scale, eval_atom0535]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0535Coded : CoefficientMerge.Poly := [(nat_lit 727, Int.ofNat (nat_lit 1))]
theorem atom0535Coded_decode : atom0535 = SparsePolynomial.decodeCubic 21 atom0535Coded := by decide +kernel
theorem atom0535Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21868118640000 : Int) atom0535Coded) := by
  have h := atom0535_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0535Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0536 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0536 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0536 = ((g 1) * (g 13) * (g 14)) := by
  norm_num [atom0536, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0536_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39387741782400 : Int) atom0536) := by
  rw [SparsePolynomial.eval_scale, eval_atom0536]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0536Coded : CoefficientMerge.Poly := [(nat_lit 728, Int.ofNat (nat_lit 1))]
theorem atom0536Coded_decode : atom0536 = SparsePolynomial.decodeCubic 21 atom0536Coded := by decide +kernel
theorem atom0536Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39387741782400 : Int) atom0536Coded) := by
  have h := atom0536_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0536Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0537 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0537 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0537 = ((g 1) * (g 13) * (g 15)) := by
  norm_num [atom0537, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0537_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42390720640800 : Int) atom0537) := by
  rw [SparsePolynomial.eval_scale, eval_atom0537]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0537Coded : CoefficientMerge.Poly := [(nat_lit 729, Int.ofNat (nat_lit 1))]
theorem atom0537Coded_decode : atom0537 = SparsePolynomial.decodeCubic 21 atom0537Coded := by decide +kernel
theorem atom0537Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42390720640800 : Int) atom0537Coded) := by
  have h := atom0537_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0537Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0538 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0538 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0538 = ((g 1) * (g 13) * (g 16)) := by
  norm_num [atom0538, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0538_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36777587119200 : Int) atom0538) := by
  rw [SparsePolynomial.eval_scale, eval_atom0538]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0538Coded : CoefficientMerge.Poly := [(nat_lit 730, Int.ofNat (nat_lit 1))]
theorem atom0538Coded_decode : atom0538 = SparsePolynomial.decodeCubic 21 atom0538Coded := by decide +kernel
theorem atom0538Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36777587119200 : Int) atom0538Coded) := by
  have h := atom0538_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0538Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0539 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0539 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0539 = ((g 1) * (g 13) * (g 17)) := by
  norm_num [atom0539, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0539_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45766897344000 : Int) atom0539) := by
  rw [SparsePolynomial.eval_scale, eval_atom0539]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0539Coded : CoefficientMerge.Poly := [(nat_lit 731, Int.ofNat (nat_lit 1))]
theorem atom0539Coded_decode : atom0539 = SparsePolynomial.decodeCubic 21 atom0539Coded := by decide +kernel
theorem atom0539Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (45766897344000 : Int) atom0539Coded) := by
  have h := atom0539_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0539Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0540 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0540 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0540 = ((g 1) * (g 13) * (g 18)) := by
  norm_num [atom0540, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0540_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41968010649600 : Int) atom0540) := by
  rw [SparsePolynomial.eval_scale, eval_atom0540]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0540Coded : CoefficientMerge.Poly := [(nat_lit 732, Int.ofNat (nat_lit 1))]
theorem atom0540Coded_decode : atom0540 = SparsePolynomial.decodeCubic 21 atom0540Coded := by decide +kernel
theorem atom0540Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41968010649600 : Int) atom0540Coded) := by
  have h := atom0540_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0540Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0541 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0541 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0541 = ((g 1) * (g 13) * (g 19)) := by
  norm_num [atom0541, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0541_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35490237040800 : Int) atom0541) := by
  rw [SparsePolynomial.eval_scale, eval_atom0541]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0541Coded : CoefficientMerge.Poly := [(nat_lit 733, Int.ofNat (nat_lit 1))]
theorem atom0541Coded_decode : atom0541 = SparsePolynomial.decodeCubic 21 atom0541Coded := by decide +kernel
theorem atom0541Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35490237040800 : Int) atom0541Coded) := by
  have h := atom0541_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0541Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0542 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0542 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0542 = ((g 1) * (g 13) * (g 20)) := by
  norm_num [atom0542, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0542_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38348256844800 : Int) atom0542) := by
  rw [SparsePolynomial.eval_scale, eval_atom0542]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0542Coded : CoefficientMerge.Poly := [(nat_lit 734, Int.ofNat (nat_lit 1))]
theorem atom0542Coded_decode : atom0542 = SparsePolynomial.decodeCubic 21 atom0542Coded := by decide +kernel
theorem atom0542Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38348256844800 : Int) atom0542Coded) := by
  have h := atom0542_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0542Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0543 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0543 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0543 = ((g 1) * (g 14) * (g 14)) := by
  norm_num [atom0543, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0543_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23400181324800 : Int) atom0543) := by
  rw [SparsePolynomial.eval_scale, eval_atom0543]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0543Coded : CoefficientMerge.Poly := [(nat_lit 749, Int.ofNat (nat_lit 1))]
theorem atom0543Coded_decode : atom0543 = SparsePolynomial.decodeCubic 21 atom0543Coded := by decide +kernel
theorem atom0543Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23400181324800 : Int) atom0543Coded) := by
  have h := atom0543_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0543Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0544 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0544 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0544 = ((g 1) * (g 14) * (g 15)) := by
  norm_num [atom0544, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0544_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44739847756800 : Int) atom0544) := by
  rw [SparsePolynomial.eval_scale, eval_atom0544]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0544Coded : CoefficientMerge.Poly := [(nat_lit 750, Int.ofNat (nat_lit 1))]
theorem atom0544Coded_decode : atom0544 = SparsePolynomial.decodeCubic 21 atom0544Coded := by decide +kernel
theorem atom0544Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44739847756800 : Int) atom0544Coded) := by
  have h := atom0544_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0544Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0545 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0545 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0545 = ((g 1) * (g 14) * (g 16)) := by
  norm_num [atom0545, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0545_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38224548633600 : Int) atom0545) := by
  rw [SparsePolynomial.eval_scale, eval_atom0545]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0545Coded : CoefficientMerge.Poly := [(nat_lit 751, Int.ofNat (nat_lit 1))]
theorem atom0545Coded_decode : atom0545 = SparsePolynomial.decodeCubic 21 atom0545Coded := by decide +kernel
theorem atom0545Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38224548633600 : Int) atom0545Coded) := by
  have h := atom0545_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0545Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0546 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0546 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0546 = ((g 1) * (g 14) * (g 17)) := by
  norm_num [atom0546, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0546_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49103153164800 : Int) atom0546) := by
  rw [SparsePolynomial.eval_scale, eval_atom0546]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0546Coded : CoefficientMerge.Poly := [(nat_lit 752, Int.ofNat (nat_lit 1))]
theorem atom0546Coded_decode : atom0546 = SparsePolynomial.decodeCubic 21 atom0546Coded := by decide +kernel
theorem atom0546Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49103153164800 : Int) atom0546Coded) := by
  have h := atom0546_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0546Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0547 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0547 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0547 = ((g 1) * (g 14) * (g 18)) := by
  norm_num [atom0547, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0547_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45640598169600 : Int) atom0547) := by
  rw [SparsePolynomial.eval_scale, eval_atom0547]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0547Coded : CoefficientMerge.Poly := [(nat_lit 753, Int.ofNat (nat_lit 1))]
theorem atom0547Coded_decode : atom0547 = SparsePolynomial.decodeCubic 21 atom0547Coded := by decide +kernel
theorem atom0547Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (45640598169600 : Int) atom0547Coded) := by
  have h := atom0547_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0547Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0548 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0548 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0548 = ((g 1) * (g 14) * (g 19)) := by
  norm_num [atom0548, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0548_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35787754598400 : Int) atom0548) := by
  rw [SparsePolynomial.eval_scale, eval_atom0548]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0548Coded : CoefficientMerge.Poly := [(nat_lit 754, Int.ofNat (nat_lit 1))]
theorem atom0548Coded_decode : atom0548 = SparsePolynomial.decodeCubic 21 atom0548Coded := by decide +kernel
theorem atom0548Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35787754598400 : Int) atom0548Coded) := by
  have h := atom0548_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0548Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0549 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0549 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0549 = ((g 1) * (g 14) * (g 20)) := by
  norm_num [atom0549, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0549_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41321119795200 : Int) atom0549) := by
  rw [SparsePolynomial.eval_scale, eval_atom0549]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0549Coded : CoefficientMerge.Poly := [(nat_lit 755, Int.ofNat (nat_lit 1))]
theorem atom0549Coded_decode : atom0549 = SparsePolynomial.decodeCubic 21 atom0549Coded := by decide +kernel
theorem atom0549Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41321119795200 : Int) atom0549Coded) := by
  have h := atom0549_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0549Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0550 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0550 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0550 = ((g 1) * (g 15) * (g 15)) := by
  norm_num [atom0550, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0550_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28066300416000 : Int) atom0550) := by
  rw [SparsePolynomial.eval_scale, eval_atom0550]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0550Coded : CoefficientMerge.Poly := [(nat_lit 771, Int.ofNat (nat_lit 1))]
theorem atom0550Coded_decode : atom0550 = SparsePolynomial.decodeCubic 21 atom0550Coded := by decide +kernel
theorem atom0550Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28066300416000 : Int) atom0550Coded) := by
  have h := atom0550_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0550Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0551 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0551 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0551 = ((g 1) * (g 15) * (g 16)) := by
  norm_num [atom0551, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0551_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46229500800000 : Int) atom0551) := by
  rw [SparsePolynomial.eval_scale, eval_atom0551]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0551Coded : CoefficientMerge.Poly := [(nat_lit 772, Int.ofNat (nat_lit 1))]
theorem atom0551Coded_decode : atom0551 = SparsePolynomial.decodeCubic 21 atom0551Coded := by decide +kernel
theorem atom0551Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46229500800000 : Int) atom0551Coded) := by
  have h := atom0551_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0551Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0552 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0552 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0552 = ((g 1) * (g 15) * (g 17)) := by
  norm_num [atom0552, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0552_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61253619033600 : Int) atom0552) := by
  rw [SparsePolynomial.eval_scale, eval_atom0552]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0552Coded : CoefficientMerge.Poly := [(nat_lit 773, Int.ofNat (nat_lit 1))]
theorem atom0552Coded_decode : atom0552 = SparsePolynomial.decodeCubic 21 atom0552Coded := by decide +kernel
theorem atom0552Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (61253619033600 : Int) atom0552Coded) := by
  have h := atom0552_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0552Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0553 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0553 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0553 = ((g 1) * (g 15) * (g 18)) := by
  norm_num [atom0553, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0553_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57872247552000 : Int) atom0553) := by
  rw [SparsePolynomial.eval_scale, eval_atom0553]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0553Coded : CoefficientMerge.Poly := [(nat_lit 774, Int.ofNat (nat_lit 1))]
theorem atom0553Coded_decode : atom0553 = SparsePolynomial.decodeCubic 21 atom0553Coded := by decide +kernel
theorem atom0553Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (57872247552000 : Int) atom0553Coded) := by
  have h := atom0553_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0553Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0554 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0554 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0554 = ((g 1) * (g 15) * (g 19)) := by
  norm_num [atom0554, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0554_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36902417126400 : Int) atom0554) := by
  rw [SparsePolynomial.eval_scale, eval_atom0554]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0554Coded : CoefficientMerge.Poly := [(nat_lit 775, Int.ofNat (nat_lit 1))]
theorem atom0554Coded_decode : atom0554 = SparsePolynomial.decodeCubic 21 atom0554Coded := by decide +kernel
theorem atom0554Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36902417126400 : Int) atom0554Coded) := by
  have h := atom0554_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0554Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0555 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0555 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0555 = ((g 1) * (g 15) * (g 20)) := by
  norm_num [atom0555, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0555_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42460507857600 : Int) atom0555) := by
  rw [SparsePolynomial.eval_scale, eval_atom0555]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0555Coded : CoefficientMerge.Poly := [(nat_lit 776, Int.ofNat (nat_lit 1))]
theorem atom0555Coded_decode : atom0555 = SparsePolynomial.decodeCubic 21 atom0555Coded := by decide +kernel
theorem atom0555Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42460507857600 : Int) atom0555Coded) := by
  have h := atom0555_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0555Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0556 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0556 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0556 = ((g 1) * (g 16) * (g 16)) := by
  norm_num [atom0556, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0556_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17241316485120 : Int) atom0556) := by
  rw [SparsePolynomial.eval_scale, eval_atom0556]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0556Coded : CoefficientMerge.Poly := [(nat_lit 793, Int.ofNat (nat_lit 1))]
theorem atom0556Coded_decode : atom0556 = SparsePolynomial.decodeCubic 21 atom0556Coded := by decide +kernel
theorem atom0556Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17241316485120 : Int) atom0556Coded) := by
  have h := atom0556_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0556Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0557 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0557 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0557 = ((g 1) * (g 16) * (g 17)) := by
  norm_num [atom0557, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0557_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44781522508800 : Int) atom0557) := by
  rw [SparsePolynomial.eval_scale, eval_atom0557]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0557Coded : CoefficientMerge.Poly := [(nat_lit 794, Int.ofNat (nat_lit 1))]
theorem atom0557Coded_decode : atom0557 = SparsePolynomial.decodeCubic 21 atom0557Coded := by decide +kernel
theorem atom0557Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44781522508800 : Int) atom0557Coded) := by
  have h := atom0557_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0557Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0558 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0558 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0558 = ((g 1) * (g 16) * (g 18)) := by
  norm_num [atom0558, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0558_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48663717580800 : Int) atom0558) := by
  rw [SparsePolynomial.eval_scale, eval_atom0558]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0558Coded : CoefficientMerge.Poly := [(nat_lit 795, Int.ofNat (nat_lit 1))]
theorem atom0558Coded_decode : atom0558 = SparsePolynomial.decodeCubic 21 atom0558Coded := by decide +kernel
theorem atom0558Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48663717580800 : Int) atom0558Coded) := by
  have h := atom0558_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0558Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0559 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0559 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0559 = ((g 1) * (g 16) * (g 19)) := by
  norm_num [atom0559, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0559_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34016536512000 : Int) atom0559) := by
  rw [SparsePolynomial.eval_scale, eval_atom0559]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0559Coded : CoefficientMerge.Poly := [(nat_lit 796, Int.ofNat (nat_lit 1))]
theorem atom0559Coded_decode : atom0559 = SparsePolynomial.decodeCubic 21 atom0559Coded := by decide +kernel
theorem atom0559Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34016536512000 : Int) atom0559Coded) := by
  have h := atom0559_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0559Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0560 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0560 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0560 = ((g 1) * (g 16) * (g 20)) := by
  norm_num [atom0560, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0560_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35468416670400 : Int) atom0560) := by
  rw [SparsePolynomial.eval_scale, eval_atom0560]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0560Coded : CoefficientMerge.Poly := [(nat_lit 797, Int.ofNat (nat_lit 1))]
theorem atom0560Coded_decode : atom0560 = SparsePolynomial.decodeCubic 21 atom0560Coded := by decide +kernel
theorem atom0560Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35468416670400 : Int) atom0560Coded) := by
  have h := atom0560_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0560Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0561 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0561 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0561 = ((g 1) * (g 17) * (g 17)) := by
  norm_num [atom0561, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0561_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32332095129600 : Int) atom0561) := by
  rw [SparsePolynomial.eval_scale, eval_atom0561]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0561Coded : CoefficientMerge.Poly := [(nat_lit 815, Int.ofNat (nat_lit 1))]
theorem atom0561Coded_decode : atom0561 = SparsePolynomial.decodeCubic 21 atom0561Coded := by decide +kernel
theorem atom0561Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32332095129600 : Int) atom0561Coded) := by
  have h := atom0561_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0561Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0562 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0562 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0562 = ((g 1) * (g 17) * (g 18)) := by
  norm_num [atom0562, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0562_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52531326489600 : Int) atom0562) := by
  rw [SparsePolynomial.eval_scale, eval_atom0562]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0562Coded : CoefficientMerge.Poly := [(nat_lit 816, Int.ofNat (nat_lit 1))]
theorem atom0562Coded_decode : atom0562 = SparsePolynomial.decodeCubic 21 atom0562Coded := by decide +kernel
theorem atom0562Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52531326489600 : Int) atom0562Coded) := by
  have h := atom0562_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0562Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0563 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0563 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0563 = ((g 1) * (g 17) * (g 19)) := by
  norm_num [atom0563, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0563_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38858347584000 : Int) atom0563) := by
  rw [SparsePolynomial.eval_scale, eval_atom0563]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0563Coded : CoefficientMerge.Poly := [(nat_lit 817, Int.ofNat (nat_lit 1))]
theorem atom0563Coded_decode : atom0563 = SparsePolynomial.decodeCubic 21 atom0563Coded := by decide +kernel
theorem atom0563Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38858347584000 : Int) atom0563Coded) := by
  have h := atom0563_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0563Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0564 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0564 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0564 = ((g 1) * (g 17) * (g 20)) := by
  norm_num [atom0564, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0564_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43189020907200 : Int) atom0564) := by
  rw [SparsePolynomial.eval_scale, eval_atom0564]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0564Coded : CoefficientMerge.Poly := [(nat_lit 818, Int.ofNat (nat_lit 1))]
theorem atom0564Coded_decode : atom0564 = SparsePolynomial.decodeCubic 21 atom0564Coded := by decide +kernel
theorem atom0564Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43189020907200 : Int) atom0564Coded) := by
  have h := atom0564_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0564Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0565 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0565 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0565 = ((g 1) * (g 18) * (g 18)) := by
  norm_num [atom0565, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0565_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19281084480000 : Int) atom0565) := by
  rw [SparsePolynomial.eval_scale, eval_atom0565]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0565Coded : CoefficientMerge.Poly := [(nat_lit 837, Int.ofNat (nat_lit 1))]
theorem atom0565Coded_decode : atom0565 = SparsePolynomial.decodeCubic 21 atom0565Coded := by decide +kernel
theorem atom0565Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19281084480000 : Int) atom0565Coded) := by
  have h := atom0565_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0565Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0566 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0566 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0566 = ((g 1) * (g 18) * (g 19)) := by
  norm_num [atom0566, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0566_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24781267526400 : Int) atom0566) := by
  rw [SparsePolynomial.eval_scale, eval_atom0566]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0566Coded : CoefficientMerge.Poly := [(nat_lit 838, Int.ofNat (nat_lit 1))]
theorem atom0566Coded_decode : atom0566 = SparsePolynomial.decodeCubic 21 atom0566Coded := by decide +kernel
theorem atom0566Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24781267526400 : Int) atom0566Coded) := by
  have h := atom0566_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0566Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0567 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0567 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0567 = ((g 1) * (g 18) * (g 20)) := by
  norm_num [atom0567, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0567_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28558072771200 : Int) atom0567) := by
  rw [SparsePolynomial.eval_scale, eval_atom0567]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0567Coded : CoefficientMerge.Poly := [(nat_lit 839, Int.ofNat (nat_lit 1))]
theorem atom0567Coded_decode : atom0567 = SparsePolynomial.decodeCubic 21 atom0567Coded := by decide +kernel
theorem atom0567Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28558072771200 : Int) atom0567Coded) := by
  have h := atom0567_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0567Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0568 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0568 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0568 = ((g 1) * (g 19) * (g 19)) := by
  norm_num [atom0568, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0568_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4012462944000 : Int) atom0568) := by
  rw [SparsePolynomial.eval_scale, eval_atom0568]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0568Coded : CoefficientMerge.Poly := [(nat_lit 859, Int.ofNat (nat_lit 1))]
theorem atom0568Coded_decode : atom0568 = SparsePolynomial.decodeCubic 21 atom0568Coded := by decide +kernel
theorem atom0568Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4012462944000 : Int) atom0568Coded) := by
  have h := atom0568_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0568Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0569 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0569 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0569 = ((g 1) * (g 19) * (g 20)) := by
  norm_num [atom0569, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0569_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9601239110400 : Int) atom0569) := by
  rw [SparsePolynomial.eval_scale, eval_atom0569]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0569Coded : CoefficientMerge.Poly := [(nat_lit 860, Int.ofNat (nat_lit 1))]
theorem atom0569Coded_decode : atom0569 = SparsePolynomial.decodeCubic 21 atom0569Coded := by decide +kernel
theorem atom0569Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9601239110400 : Int) atom0569Coded) := by
  have h := atom0569_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0569Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0570 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0570 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0570 = ((g 1) * (g 20) * (g 20)) := by
  norm_num [atom0570, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0570_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3467695795200 : Int) atom0570) := by
  rw [SparsePolynomial.eval_scale, eval_atom0570]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0570Coded : CoefficientMerge.Poly := [(nat_lit 881, Int.ofNat (nat_lit 1))]
theorem atom0570Coded_decode : atom0570 = SparsePolynomial.decodeCubic 21 atom0570Coded := by decide +kernel
theorem atom0570Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3467695795200 : Int) atom0570Coded) := by
  have h := atom0570_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0570Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0571 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 2], Int.ofNat (nat_lit 1))]
theorem eval_atom0571 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0571 = ((g 2) * (g 2) * (g 2)) := by
  norm_num [atom0571, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0571_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4679649676800 : Int) atom0571) := by
  rw [SparsePolynomial.eval_scale, eval_atom0571]
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 2) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0571Coded : CoefficientMerge.Poly := [(nat_lit 926, Int.ofNat (nat_lit 1))]
theorem atom0571Coded_decode : atom0571 = SparsePolynomial.decodeCubic 21 atom0571Coded := by decide +kernel
theorem atom0571Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4679649676800 : Int) atom0571Coded) := by
  have h := atom0571_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0571Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0572 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0572 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0572 = ((g 2) * (g 2) * (g 3)) := by
  norm_num [atom0572, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0572_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13261906828800 : Int) atom0572) := by
  rw [SparsePolynomial.eval_scale, eval_atom0572]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0572Coded : CoefficientMerge.Poly := [(nat_lit 927, Int.ofNat (nat_lit 1))]
theorem atom0572Coded_decode : atom0572 = SparsePolynomial.decodeCubic 21 atom0572Coded := by decide +kernel
theorem atom0572Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13261906828800 : Int) atom0572Coded) := by
  have h := atom0572_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0572Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0573 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0573 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0573 = ((g 2) * (g 2) * (g 4)) := by
  norm_num [atom0573, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0573_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12484864627200 : Int) atom0573) := by
  rw [SparsePolynomial.eval_scale, eval_atom0573]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0573Coded : CoefficientMerge.Poly := [(nat_lit 928, Int.ofNat (nat_lit 1))]
theorem atom0573Coded_decode : atom0573 = SparsePolynomial.decodeCubic 21 atom0573Coded := by decide +kernel
theorem atom0573Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12484864627200 : Int) atom0573Coded) := by
  have h := atom0573_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0573Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0574 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0574 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0574 = ((g 2) * (g 2) * (g 5)) := by
  norm_num [atom0574, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0574_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13199200388352 : Int) atom0574) := by
  rw [SparsePolynomial.eval_scale, eval_atom0574]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0574Coded : CoefficientMerge.Poly := [(nat_lit 929, Int.ofNat (nat_lit 1))]
theorem atom0574Coded_decode : atom0574 = SparsePolynomial.decodeCubic 21 atom0574Coded := by decide +kernel
theorem atom0574Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13199200388352 : Int) atom0574Coded) := by
  have h := atom0574_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0574Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0575 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0575 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0575 = ((g 2) * (g 2) * (g 6)) := by
  norm_num [atom0575, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0575_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12875483174400 : Int) atom0575) := by
  rw [SparsePolynomial.eval_scale, eval_atom0575]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0575Coded : CoefficientMerge.Poly := [(nat_lit 930, Int.ofNat (nat_lit 1))]
theorem atom0575Coded_decode : atom0575 = SparsePolynomial.decodeCubic 21 atom0575Coded := by decide +kernel
theorem atom0575Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12875483174400 : Int) atom0575Coded) := by
  have h := atom0575_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0575Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block008 : CoefficientMerge.Poly := [(nat_lit 642, Int.ofNat (nat_lit 30403816464000)), (nat_lit 643, Int.ofNat (nat_lit 29787423120000)), (nat_lit 644, Int.ofNat (nat_lit 30487147689600)), (nat_lit 645, Int.ofNat (nat_lit 39992545152000)), (nat_lit 646, Int.ofNat (nat_lit 34392272014800)), (nat_lit 647, Int.ofNat (nat_lit 41077582963200)), (nat_lit 648, Int.ofNat (nat_lit 39334036518000)), (nat_lit 649, Int.ofNat (nat_lit 35737719620400)), (nat_lit 650, Int.ofNat (nat_lit 36469257174000)), (nat_lit 661, Int.ofNat (nat_lit 22070559672000)), (nat_lit 662, Int.ofNat (nat_lit 39833095538880)), (nat_lit 663, Int.ofNat (nat_lit 33381177081280)), (nat_lit 664, Int.ofNat (nat_lit 32429753193600)), (nat_lit 665, Int.ofNat (nat_lit 32838570172800)), (nat_lit 666, Int.ofNat (nat_lit 42138109440000)), (nat_lit 667, Int.ofNat (nat_lit 36296339511600)), (nat_lit 668, Int.ofNat (nat_lit 43895810649600)), (nat_lit 669, Int.ofNat (nat_lit 40925209222800)), (nat_lit 670, Int.ofNat (nat_lit 36790085077200)), (nat_lit 671, Int.ofNat (nat_lit 37409995299600)), (nat_lit 683, Int.ofNat (nat_lit 23509942041600)), (nat_lit 684, Int.ofNat (nat_lit 39142615079680)), (nat_lit 685, Int.ofNat (nat_lit 34691663462400)), (nat_lit 686, Int.ofNat (nat_lit 34725489926400)), (nat_lit 687, Int.ofNat (nat_lit 43659826560000)), (nat_lit 688, Int.ofNat (nat_lit 37535436288000)), (nat_lit 689, Int.ofNat (nat_lit 46090191168000)), (nat_lit 690, Int.ofNat (nat_lit 41618641075200)), (nat_lit 691, Int.ofNat (nat_lit 37129480819200)), (nat_lit 692, Int.ofNat (nat_lit 37510611264000)), (nat_lit 705, Int.ofNat (nat_lit 21593669171200)), (nat_lit 706, Int.ofNat (nat_lit 37959288304000)), (nat_lit 707, Int.ofNat (nat_lit 34193114233600)), (nat_lit 708, Int.ofNat (nat_lit 41082437401600)), (nat_lit 709, Int.ofNat (nat_lit 36148462828800)), (nat_lit 710, Int.ofNat (nat_lit 44185465408000)), (nat_lit 711, Int.ofNat (nat_lit 40050247014400)), (nat_lit 712, Int.ofNat (nat_lit 36979376806400)), (nat_lit 713, Int.ofNat (nat_lit 37173350995200)), (nat_lit 727, Int.ofNat (nat_lit 21868118640000)), (nat_lit 728, Int.ofNat (nat_lit 39387741782400)), (nat_lit 729, Int.ofNat (nat_lit 42390720640800)), (nat_lit 730, Int.ofNat (nat_lit 36777587119200)), (nat_lit 731, Int.ofNat (nat_lit 45766897344000)), (nat_lit 732, Int.ofNat (nat_lit 41968010649600)), (nat_lit 733, Int.ofNat (nat_lit 35490237040800)), (nat_lit 734, Int.ofNat (nat_lit 38348256844800)), (nat_lit 749, Int.ofNat (nat_lit 23400181324800)), (nat_lit 750, Int.ofNat (nat_lit 44739847756800)), (nat_lit 751, Int.ofNat (nat_lit 38224548633600)), (nat_lit 752, Int.ofNat (nat_lit 49103153164800)), (nat_lit 753, Int.ofNat (nat_lit 45640598169600)), (nat_lit 754, Int.ofNat (nat_lit 35787754598400)), (nat_lit 755, Int.ofNat (nat_lit 41321119795200)), (nat_lit 771, Int.ofNat (nat_lit 28066300416000)), (nat_lit 772, Int.ofNat (nat_lit 46229500800000)), (nat_lit 773, Int.ofNat (nat_lit 61253619033600)), (nat_lit 774, Int.ofNat (nat_lit 57872247552000)), (nat_lit 775, Int.ofNat (nat_lit 36902417126400)), (nat_lit 776, Int.ofNat (nat_lit 42460507857600)), (nat_lit 793, Int.ofNat (nat_lit 17241316485120)), (nat_lit 794, Int.ofNat (nat_lit 44781522508800)), (nat_lit 795, Int.ofNat (nat_lit 48663717580800)), (nat_lit 796, Int.ofNat (nat_lit 34016536512000)), (nat_lit 797, Int.ofNat (nat_lit 35468416670400)), (nat_lit 815, Int.ofNat (nat_lit 32332095129600)), (nat_lit 816, Int.ofNat (nat_lit 52531326489600)), (nat_lit 817, Int.ofNat (nat_lit 38858347584000)), (nat_lit 818, Int.ofNat (nat_lit 43189020907200)), (nat_lit 837, Int.ofNat (nat_lit 19281084480000)), (nat_lit 838, Int.ofNat (nat_lit 24781267526400)), (nat_lit 839, Int.ofNat (nat_lit 28558072771200)), (nat_lit 859, Int.ofNat (nat_lit 4012462944000)), (nat_lit 860, Int.ofNat (nat_lit 9601239110400)), (nat_lit 881, Int.ofNat (nat_lit 3467695795200)), (nat_lit 926, Int.ofNat (nat_lit 4679649676800)), (nat_lit 927, Int.ofNat (nat_lit 13261906828800)), (nat_lit 928, Int.ofNat (nat_lit 12484864627200)), (nat_lit 929, Int.ofNat (nat_lit 13199200388352)), (nat_lit 930, Int.ofNat (nat_lit 12875483174400))]
def block008_data_flat000 : CoefficientMerge.Poly := [(nat_lit 642, Int.ofNat (nat_lit 30403816464000))]
theorem block008_data_flat000_step : block008_data_flat000 = (CoefficientMerge.scale (30403816464000 : Int) atom0496Coded) := by decide +kernel
theorem block008_data_flat000_original : block008_data_flat000 = (CoefficientMerge.scale (30403816464000 : Int) atom0496Coded) := by
  rw [block008_data_flat000_step]
def block008_data_flat001 : CoefficientMerge.Poly := [(nat_lit 643, Int.ofNat (nat_lit 29787423120000))]
theorem block008_data_flat001_step : block008_data_flat001 = (CoefficientMerge.scale (29787423120000 : Int) atom0497Coded) := by decide +kernel
theorem block008_data_flat001_original : block008_data_flat001 = (CoefficientMerge.scale (29787423120000 : Int) atom0497Coded) := by
  rw [block008_data_flat001_step]
def block008_data_flat002 : CoefficientMerge.Poly := [(nat_lit 642, Int.ofNat (nat_lit 30403816464000)), (nat_lit 643, Int.ofNat (nat_lit 29787423120000))]
theorem block008_data_flat002_step : block008_data_flat002 = (CoefficientMerge.fastMerge block008_data_flat000 block008_data_flat001) := by decide +kernel
theorem block008_data_flat002_original : block008_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30403816464000 : Int) atom0496Coded) (CoefficientMerge.scale (29787423120000 : Int) atom0497Coded)) := by
  rw [block008_data_flat002_step, block008_data_flat000_original, block008_data_flat001_original]
def block008_data_flat003 : CoefficientMerge.Poly := [(nat_lit 644, Int.ofNat (nat_lit 30487147689600))]
theorem block008_data_flat003_step : block008_data_flat003 = (CoefficientMerge.scale (30487147689600 : Int) atom0498Coded) := by decide +kernel
theorem block008_data_flat003_original : block008_data_flat003 = (CoefficientMerge.scale (30487147689600 : Int) atom0498Coded) := by
  rw [block008_data_flat003_step]
def block008_data_flat004 : CoefficientMerge.Poly := [(nat_lit 645, Int.ofNat (nat_lit 39992545152000))]
theorem block008_data_flat004_step : block008_data_flat004 = (CoefficientMerge.scale (39992545152000 : Int) atom0499Coded) := by decide +kernel
theorem block008_data_flat004_original : block008_data_flat004 = (CoefficientMerge.scale (39992545152000 : Int) atom0499Coded) := by
  rw [block008_data_flat004_step]
def block008_data_flat005 : CoefficientMerge.Poly := [(nat_lit 646, Int.ofNat (nat_lit 34392272014800))]
theorem block008_data_flat005_step : block008_data_flat005 = (CoefficientMerge.scale (34392272014800 : Int) atom0500Coded) := by decide +kernel
theorem block008_data_flat005_original : block008_data_flat005 = (CoefficientMerge.scale (34392272014800 : Int) atom0500Coded) := by
  rw [block008_data_flat005_step]
def block008_data_flat006 : CoefficientMerge.Poly := [(nat_lit 645, Int.ofNat (nat_lit 39992545152000)), (nat_lit 646, Int.ofNat (nat_lit 34392272014800))]
theorem block008_data_flat006_step : block008_data_flat006 = (CoefficientMerge.fastMerge block008_data_flat004 block008_data_flat005) := by decide +kernel
theorem block008_data_flat006_original : block008_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (39992545152000 : Int) atom0499Coded) (CoefficientMerge.scale (34392272014800 : Int) atom0500Coded)) := by
  rw [block008_data_flat006_step, block008_data_flat004_original, block008_data_flat005_original]
def block008_data_flat007 : CoefficientMerge.Poly := [(nat_lit 644, Int.ofNat (nat_lit 30487147689600)), (nat_lit 645, Int.ofNat (nat_lit 39992545152000)), (nat_lit 646, Int.ofNat (nat_lit 34392272014800))]
theorem block008_data_flat007_step : block008_data_flat007 = (CoefficientMerge.fastMerge block008_data_flat003 block008_data_flat006) := by decide +kernel
theorem block008_data_flat007_original : block008_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30487147689600 : Int) atom0498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39992545152000 : Int) atom0499Coded) (CoefficientMerge.scale (34392272014800 : Int) atom0500Coded))) := by
  rw [block008_data_flat007_step, block008_data_flat003_original, block008_data_flat006_original]
def block008_data_flat008 : CoefficientMerge.Poly := [(nat_lit 642, Int.ofNat (nat_lit 30403816464000)), (nat_lit 643, Int.ofNat (nat_lit 29787423120000)), (nat_lit 644, Int.ofNat (nat_lit 30487147689600)), (nat_lit 645, Int.ofNat (nat_lit 39992545152000)), (nat_lit 646, Int.ofNat (nat_lit 34392272014800))]
theorem block008_data_flat008_step : block008_data_flat008 = (CoefficientMerge.fastMerge block008_data_flat002 block008_data_flat007) := by decide +kernel
theorem block008_data_flat008_original : block008_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30403816464000 : Int) atom0496Coded) (CoefficientMerge.scale (29787423120000 : Int) atom0497Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30487147689600 : Int) atom0498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39992545152000 : Int) atom0499Coded) (CoefficientMerge.scale (34392272014800 : Int) atom0500Coded)))) := by
  rw [block008_data_flat008_step, block008_data_flat002_original, block008_data_flat007_original]
def block008_data_flat009 : CoefficientMerge.Poly := [(nat_lit 647, Int.ofNat (nat_lit 41077582963200))]
theorem block008_data_flat009_step : block008_data_flat009 = (CoefficientMerge.scale (41077582963200 : Int) atom0501Coded) := by decide +kernel
theorem block008_data_flat009_original : block008_data_flat009 = (CoefficientMerge.scale (41077582963200 : Int) atom0501Coded) := by
  rw [block008_data_flat009_step]
def block008_data_flat010 : CoefficientMerge.Poly := [(nat_lit 648, Int.ofNat (nat_lit 39334036518000))]
theorem block008_data_flat010_step : block008_data_flat010 = (CoefficientMerge.scale (39334036518000 : Int) atom0502Coded) := by decide +kernel
theorem block008_data_flat010_original : block008_data_flat010 = (CoefficientMerge.scale (39334036518000 : Int) atom0502Coded) := by
  rw [block008_data_flat010_step]
def block008_data_flat011 : CoefficientMerge.Poly := [(nat_lit 647, Int.ofNat (nat_lit 41077582963200)), (nat_lit 648, Int.ofNat (nat_lit 39334036518000))]
theorem block008_data_flat011_step : block008_data_flat011 = (CoefficientMerge.fastMerge block008_data_flat009 block008_data_flat010) := by decide +kernel
theorem block008_data_flat011_original : block008_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (41077582963200 : Int) atom0501Coded) (CoefficientMerge.scale (39334036518000 : Int) atom0502Coded)) := by
  rw [block008_data_flat011_step, block008_data_flat009_original, block008_data_flat010_original]
def block008_data_flat012 : CoefficientMerge.Poly := [(nat_lit 649, Int.ofNat (nat_lit 35737719620400))]
theorem block008_data_flat012_step : block008_data_flat012 = (CoefficientMerge.scale (35737719620400 : Int) atom0503Coded) := by decide +kernel
theorem block008_data_flat012_original : block008_data_flat012 = (CoefficientMerge.scale (35737719620400 : Int) atom0503Coded) := by
  rw [block008_data_flat012_step]
def block008_data_flat013 : CoefficientMerge.Poly := [(nat_lit 650, Int.ofNat (nat_lit 36469257174000))]
theorem block008_data_flat013_step : block008_data_flat013 = (CoefficientMerge.scale (36469257174000 : Int) atom0504Coded) := by decide +kernel
theorem block008_data_flat013_original : block008_data_flat013 = (CoefficientMerge.scale (36469257174000 : Int) atom0504Coded) := by
  rw [block008_data_flat013_step]
def block008_data_flat014 : CoefficientMerge.Poly := [(nat_lit 661, Int.ofNat (nat_lit 22070559672000))]
theorem block008_data_flat014_step : block008_data_flat014 = (CoefficientMerge.scale (22070559672000 : Int) atom0505Coded) := by decide +kernel
theorem block008_data_flat014_original : block008_data_flat014 = (CoefficientMerge.scale (22070559672000 : Int) atom0505Coded) := by
  rw [block008_data_flat014_step]
def block008_data_flat015 : CoefficientMerge.Poly := [(nat_lit 650, Int.ofNat (nat_lit 36469257174000)), (nat_lit 661, Int.ofNat (nat_lit 22070559672000))]
theorem block008_data_flat015_step : block008_data_flat015 = (CoefficientMerge.fastMerge block008_data_flat013 block008_data_flat014) := by decide +kernel
theorem block008_data_flat015_original : block008_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36469257174000 : Int) atom0504Coded) (CoefficientMerge.scale (22070559672000 : Int) atom0505Coded)) := by
  rw [block008_data_flat015_step, block008_data_flat013_original, block008_data_flat014_original]
def block008_data_flat016 : CoefficientMerge.Poly := [(nat_lit 649, Int.ofNat (nat_lit 35737719620400)), (nat_lit 650, Int.ofNat (nat_lit 36469257174000)), (nat_lit 661, Int.ofNat (nat_lit 22070559672000))]
theorem block008_data_flat016_step : block008_data_flat016 = (CoefficientMerge.fastMerge block008_data_flat012 block008_data_flat015) := by decide +kernel
theorem block008_data_flat016_original : block008_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35737719620400 : Int) atom0503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36469257174000 : Int) atom0504Coded) (CoefficientMerge.scale (22070559672000 : Int) atom0505Coded))) := by
  rw [block008_data_flat016_step, block008_data_flat012_original, block008_data_flat015_original]
def block008_data_flat017 : CoefficientMerge.Poly := [(nat_lit 647, Int.ofNat (nat_lit 41077582963200)), (nat_lit 648, Int.ofNat (nat_lit 39334036518000)), (nat_lit 649, Int.ofNat (nat_lit 35737719620400)), (nat_lit 650, Int.ofNat (nat_lit 36469257174000)), (nat_lit 661, Int.ofNat (nat_lit 22070559672000))]
theorem block008_data_flat017_step : block008_data_flat017 = (CoefficientMerge.fastMerge block008_data_flat011 block008_data_flat016) := by decide +kernel
theorem block008_data_flat017_original : block008_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41077582963200 : Int) atom0501Coded) (CoefficientMerge.scale (39334036518000 : Int) atom0502Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35737719620400 : Int) atom0503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36469257174000 : Int) atom0504Coded) (CoefficientMerge.scale (22070559672000 : Int) atom0505Coded)))) := by
  rw [block008_data_flat017_step, block008_data_flat011_original, block008_data_flat016_original]
def block008_data_flat018 : CoefficientMerge.Poly := [(nat_lit 642, Int.ofNat (nat_lit 30403816464000)), (nat_lit 643, Int.ofNat (nat_lit 29787423120000)), (nat_lit 644, Int.ofNat (nat_lit 30487147689600)), (nat_lit 645, Int.ofNat (nat_lit 39992545152000)), (nat_lit 646, Int.ofNat (nat_lit 34392272014800)), (nat_lit 647, Int.ofNat (nat_lit 41077582963200)), (nat_lit 648, Int.ofNat (nat_lit 39334036518000)), (nat_lit 649, Int.ofNat (nat_lit 35737719620400)), (nat_lit 650, Int.ofNat (nat_lit 36469257174000)), (nat_lit 661, Int.ofNat (nat_lit 22070559672000))]
theorem block008_data_flat018_step : block008_data_flat018 = (CoefficientMerge.fastMerge block008_data_flat008 block008_data_flat017) := by decide +kernel
theorem block008_data_flat018_original : block008_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30403816464000 : Int) atom0496Coded) (CoefficientMerge.scale (29787423120000 : Int) atom0497Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30487147689600 : Int) atom0498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39992545152000 : Int) atom0499Coded) (CoefficientMerge.scale (34392272014800 : Int) atom0500Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41077582963200 : Int) atom0501Coded) (CoefficientMerge.scale (39334036518000 : Int) atom0502Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35737719620400 : Int) atom0503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36469257174000 : Int) atom0504Coded) (CoefficientMerge.scale (22070559672000 : Int) atom0505Coded))))) := by
  rw [block008_data_flat018_step, block008_data_flat008_original, block008_data_flat017_original]
def block008_data_flat019 : CoefficientMerge.Poly := [(nat_lit 662, Int.ofNat (nat_lit 39833095538880))]
theorem block008_data_flat019_step : block008_data_flat019 = (CoefficientMerge.scale (39833095538880 : Int) atom0506Coded) := by decide +kernel
theorem block008_data_flat019_original : block008_data_flat019 = (CoefficientMerge.scale (39833095538880 : Int) atom0506Coded) := by
  rw [block008_data_flat019_step]
def block008_data_flat020 : CoefficientMerge.Poly := [(nat_lit 663, Int.ofNat (nat_lit 33381177081280))]
theorem block008_data_flat020_step : block008_data_flat020 = (CoefficientMerge.scale (33381177081280 : Int) atom0507Coded) := by decide +kernel
theorem block008_data_flat020_original : block008_data_flat020 = (CoefficientMerge.scale (33381177081280 : Int) atom0507Coded) := by
  rw [block008_data_flat020_step]
def block008_data_flat021 : CoefficientMerge.Poly := [(nat_lit 662, Int.ofNat (nat_lit 39833095538880)), (nat_lit 663, Int.ofNat (nat_lit 33381177081280))]
theorem block008_data_flat021_step : block008_data_flat021 = (CoefficientMerge.fastMerge block008_data_flat019 block008_data_flat020) := by decide +kernel
theorem block008_data_flat021_original : block008_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (39833095538880 : Int) atom0506Coded) (CoefficientMerge.scale (33381177081280 : Int) atom0507Coded)) := by
  rw [block008_data_flat021_step, block008_data_flat019_original, block008_data_flat020_original]
def block008_data_flat022 : CoefficientMerge.Poly := [(nat_lit 664, Int.ofNat (nat_lit 32429753193600))]
theorem block008_data_flat022_step : block008_data_flat022 = (CoefficientMerge.scale (32429753193600 : Int) atom0508Coded) := by decide +kernel
theorem block008_data_flat022_original : block008_data_flat022 = (CoefficientMerge.scale (32429753193600 : Int) atom0508Coded) := by
  rw [block008_data_flat022_step]
def block008_data_flat023 : CoefficientMerge.Poly := [(nat_lit 665, Int.ofNat (nat_lit 32838570172800))]
theorem block008_data_flat023_step : block008_data_flat023 = (CoefficientMerge.scale (32838570172800 : Int) atom0509Coded) := by decide +kernel
theorem block008_data_flat023_original : block008_data_flat023 = (CoefficientMerge.scale (32838570172800 : Int) atom0509Coded) := by
  rw [block008_data_flat023_step]
def block008_data_flat024 : CoefficientMerge.Poly := [(nat_lit 666, Int.ofNat (nat_lit 42138109440000))]
theorem block008_data_flat024_step : block008_data_flat024 = (CoefficientMerge.scale (42138109440000 : Int) atom0510Coded) := by decide +kernel
theorem block008_data_flat024_original : block008_data_flat024 = (CoefficientMerge.scale (42138109440000 : Int) atom0510Coded) := by
  rw [block008_data_flat024_step]
def block008_data_flat025 : CoefficientMerge.Poly := [(nat_lit 665, Int.ofNat (nat_lit 32838570172800)), (nat_lit 666, Int.ofNat (nat_lit 42138109440000))]
theorem block008_data_flat025_step : block008_data_flat025 = (CoefficientMerge.fastMerge block008_data_flat023 block008_data_flat024) := by decide +kernel
theorem block008_data_flat025_original : block008_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (32838570172800 : Int) atom0509Coded) (CoefficientMerge.scale (42138109440000 : Int) atom0510Coded)) := by
  rw [block008_data_flat025_step, block008_data_flat023_original, block008_data_flat024_original]
def block008_data_flat026 : CoefficientMerge.Poly := [(nat_lit 664, Int.ofNat (nat_lit 32429753193600)), (nat_lit 665, Int.ofNat (nat_lit 32838570172800)), (nat_lit 666, Int.ofNat (nat_lit 42138109440000))]
theorem block008_data_flat026_step : block008_data_flat026 = (CoefficientMerge.fastMerge block008_data_flat022 block008_data_flat025) := by decide +kernel
theorem block008_data_flat026_original : block008_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (32429753193600 : Int) atom0508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32838570172800 : Int) atom0509Coded) (CoefficientMerge.scale (42138109440000 : Int) atom0510Coded))) := by
  rw [block008_data_flat026_step, block008_data_flat022_original, block008_data_flat025_original]
def block008_data_flat027 : CoefficientMerge.Poly := [(nat_lit 662, Int.ofNat (nat_lit 39833095538880)), (nat_lit 663, Int.ofNat (nat_lit 33381177081280)), (nat_lit 664, Int.ofNat (nat_lit 32429753193600)), (nat_lit 665, Int.ofNat (nat_lit 32838570172800)), (nat_lit 666, Int.ofNat (nat_lit 42138109440000))]
theorem block008_data_flat027_step : block008_data_flat027 = (CoefficientMerge.fastMerge block008_data_flat021 block008_data_flat026) := by decide +kernel
theorem block008_data_flat027_original : block008_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39833095538880 : Int) atom0506Coded) (CoefficientMerge.scale (33381177081280 : Int) atom0507Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32429753193600 : Int) atom0508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32838570172800 : Int) atom0509Coded) (CoefficientMerge.scale (42138109440000 : Int) atom0510Coded)))) := by
  rw [block008_data_flat027_step, block008_data_flat021_original, block008_data_flat026_original]
def block008_data_flat028 : CoefficientMerge.Poly := [(nat_lit 667, Int.ofNat (nat_lit 36296339511600))]
theorem block008_data_flat028_step : block008_data_flat028 = (CoefficientMerge.scale (36296339511600 : Int) atom0511Coded) := by decide +kernel
theorem block008_data_flat028_original : block008_data_flat028 = (CoefficientMerge.scale (36296339511600 : Int) atom0511Coded) := by
  rw [block008_data_flat028_step]
def block008_data_flat029 : CoefficientMerge.Poly := [(nat_lit 668, Int.ofNat (nat_lit 43895810649600))]
theorem block008_data_flat029_step : block008_data_flat029 = (CoefficientMerge.scale (43895810649600 : Int) atom0512Coded) := by decide +kernel
theorem block008_data_flat029_original : block008_data_flat029 = (CoefficientMerge.scale (43895810649600 : Int) atom0512Coded) := by
  rw [block008_data_flat029_step]
def block008_data_flat030 : CoefficientMerge.Poly := [(nat_lit 667, Int.ofNat (nat_lit 36296339511600)), (nat_lit 668, Int.ofNat (nat_lit 43895810649600))]
theorem block008_data_flat030_step : block008_data_flat030 = (CoefficientMerge.fastMerge block008_data_flat028 block008_data_flat029) := by decide +kernel
theorem block008_data_flat030_original : block008_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36296339511600 : Int) atom0511Coded) (CoefficientMerge.scale (43895810649600 : Int) atom0512Coded)) := by
  rw [block008_data_flat030_step, block008_data_flat028_original, block008_data_flat029_original]
def block008_data_flat031 : CoefficientMerge.Poly := [(nat_lit 669, Int.ofNat (nat_lit 40925209222800))]
theorem block008_data_flat031_step : block008_data_flat031 = (CoefficientMerge.scale (40925209222800 : Int) atom0513Coded) := by decide +kernel
theorem block008_data_flat031_original : block008_data_flat031 = (CoefficientMerge.scale (40925209222800 : Int) atom0513Coded) := by
  rw [block008_data_flat031_step]
def block008_data_flat032 : CoefficientMerge.Poly := [(nat_lit 670, Int.ofNat (nat_lit 36790085077200))]
theorem block008_data_flat032_step : block008_data_flat032 = (CoefficientMerge.scale (36790085077200 : Int) atom0514Coded) := by decide +kernel
theorem block008_data_flat032_original : block008_data_flat032 = (CoefficientMerge.scale (36790085077200 : Int) atom0514Coded) := by
  rw [block008_data_flat032_step]
def block008_data_flat033 : CoefficientMerge.Poly := [(nat_lit 671, Int.ofNat (nat_lit 37409995299600))]
theorem block008_data_flat033_step : block008_data_flat033 = (CoefficientMerge.scale (37409995299600 : Int) atom0515Coded) := by decide +kernel
theorem block008_data_flat033_original : block008_data_flat033 = (CoefficientMerge.scale (37409995299600 : Int) atom0515Coded) := by
  rw [block008_data_flat033_step]
def block008_data_flat034 : CoefficientMerge.Poly := [(nat_lit 670, Int.ofNat (nat_lit 36790085077200)), (nat_lit 671, Int.ofNat (nat_lit 37409995299600))]
theorem block008_data_flat034_step : block008_data_flat034 = (CoefficientMerge.fastMerge block008_data_flat032 block008_data_flat033) := by decide +kernel
theorem block008_data_flat034_original : block008_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36790085077200 : Int) atom0514Coded) (CoefficientMerge.scale (37409995299600 : Int) atom0515Coded)) := by
  rw [block008_data_flat034_step, block008_data_flat032_original, block008_data_flat033_original]
def block008_data_flat035 : CoefficientMerge.Poly := [(nat_lit 669, Int.ofNat (nat_lit 40925209222800)), (nat_lit 670, Int.ofNat (nat_lit 36790085077200)), (nat_lit 671, Int.ofNat (nat_lit 37409995299600))]
theorem block008_data_flat035_step : block008_data_flat035 = (CoefficientMerge.fastMerge block008_data_flat031 block008_data_flat034) := by decide +kernel
theorem block008_data_flat035_original : block008_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40925209222800 : Int) atom0513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36790085077200 : Int) atom0514Coded) (CoefficientMerge.scale (37409995299600 : Int) atom0515Coded))) := by
  rw [block008_data_flat035_step, block008_data_flat031_original, block008_data_flat034_original]
def block008_data_flat036 : CoefficientMerge.Poly := [(nat_lit 667, Int.ofNat (nat_lit 36296339511600)), (nat_lit 668, Int.ofNat (nat_lit 43895810649600)), (nat_lit 669, Int.ofNat (nat_lit 40925209222800)), (nat_lit 670, Int.ofNat (nat_lit 36790085077200)), (nat_lit 671, Int.ofNat (nat_lit 37409995299600))]
theorem block008_data_flat036_step : block008_data_flat036 = (CoefficientMerge.fastMerge block008_data_flat030 block008_data_flat035) := by decide +kernel
theorem block008_data_flat036_original : block008_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36296339511600 : Int) atom0511Coded) (CoefficientMerge.scale (43895810649600 : Int) atom0512Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40925209222800 : Int) atom0513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36790085077200 : Int) atom0514Coded) (CoefficientMerge.scale (37409995299600 : Int) atom0515Coded)))) := by
  rw [block008_data_flat036_step, block008_data_flat030_original, block008_data_flat035_original]
def block008_data_flat037 : CoefficientMerge.Poly := [(nat_lit 662, Int.ofNat (nat_lit 39833095538880)), (nat_lit 663, Int.ofNat (nat_lit 33381177081280)), (nat_lit 664, Int.ofNat (nat_lit 32429753193600)), (nat_lit 665, Int.ofNat (nat_lit 32838570172800)), (nat_lit 666, Int.ofNat (nat_lit 42138109440000)), (nat_lit 667, Int.ofNat (nat_lit 36296339511600)), (nat_lit 668, Int.ofNat (nat_lit 43895810649600)), (nat_lit 669, Int.ofNat (nat_lit 40925209222800)), (nat_lit 670, Int.ofNat (nat_lit 36790085077200)), (nat_lit 671, Int.ofNat (nat_lit 37409995299600))]
theorem block008_data_flat037_step : block008_data_flat037 = (CoefficientMerge.fastMerge block008_data_flat027 block008_data_flat036) := by decide +kernel
theorem block008_data_flat037_original : block008_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39833095538880 : Int) atom0506Coded) (CoefficientMerge.scale (33381177081280 : Int) atom0507Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32429753193600 : Int) atom0508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32838570172800 : Int) atom0509Coded) (CoefficientMerge.scale (42138109440000 : Int) atom0510Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36296339511600 : Int) atom0511Coded) (CoefficientMerge.scale (43895810649600 : Int) atom0512Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40925209222800 : Int) atom0513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36790085077200 : Int) atom0514Coded) (CoefficientMerge.scale (37409995299600 : Int) atom0515Coded))))) := by
  rw [block008_data_flat037_step, block008_data_flat027_original, block008_data_flat036_original]
def block008_data_flat038 : CoefficientMerge.Poly := [(nat_lit 642, Int.ofNat (nat_lit 30403816464000)), (nat_lit 643, Int.ofNat (nat_lit 29787423120000)), (nat_lit 644, Int.ofNat (nat_lit 30487147689600)), (nat_lit 645, Int.ofNat (nat_lit 39992545152000)), (nat_lit 646, Int.ofNat (nat_lit 34392272014800)), (nat_lit 647, Int.ofNat (nat_lit 41077582963200)), (nat_lit 648, Int.ofNat (nat_lit 39334036518000)), (nat_lit 649, Int.ofNat (nat_lit 35737719620400)), (nat_lit 650, Int.ofNat (nat_lit 36469257174000)), (nat_lit 661, Int.ofNat (nat_lit 22070559672000)), (nat_lit 662, Int.ofNat (nat_lit 39833095538880)), (nat_lit 663, Int.ofNat (nat_lit 33381177081280)), (nat_lit 664, Int.ofNat (nat_lit 32429753193600)), (nat_lit 665, Int.ofNat (nat_lit 32838570172800)), (nat_lit 666, Int.ofNat (nat_lit 42138109440000)), (nat_lit 667, Int.ofNat (nat_lit 36296339511600)), (nat_lit 668, Int.ofNat (nat_lit 43895810649600)), (nat_lit 669, Int.ofNat (nat_lit 40925209222800)), (nat_lit 670, Int.ofNat (nat_lit 36790085077200)), (nat_lit 671, Int.ofNat (nat_lit 37409995299600))]
theorem block008_data_flat038_step : block008_data_flat038 = (CoefficientMerge.fastMerge block008_data_flat018 block008_data_flat037) := by decide +kernel
theorem block008_data_flat038_original : block008_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30403816464000 : Int) atom0496Coded) (CoefficientMerge.scale (29787423120000 : Int) atom0497Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30487147689600 : Int) atom0498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39992545152000 : Int) atom0499Coded) (CoefficientMerge.scale (34392272014800 : Int) atom0500Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41077582963200 : Int) atom0501Coded) (CoefficientMerge.scale (39334036518000 : Int) atom0502Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35737719620400 : Int) atom0503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36469257174000 : Int) atom0504Coded) (CoefficientMerge.scale (22070559672000 : Int) atom0505Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39833095538880 : Int) atom0506Coded) (CoefficientMerge.scale (33381177081280 : Int) atom0507Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32429753193600 : Int) atom0508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32838570172800 : Int) atom0509Coded) (CoefficientMerge.scale (42138109440000 : Int) atom0510Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36296339511600 : Int) atom0511Coded) (CoefficientMerge.scale (43895810649600 : Int) atom0512Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40925209222800 : Int) atom0513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36790085077200 : Int) atom0514Coded) (CoefficientMerge.scale (37409995299600 : Int) atom0515Coded)))))) := by
  rw [block008_data_flat038_step, block008_data_flat018_original, block008_data_flat037_original]
def block008_data_flat039 : CoefficientMerge.Poly := [(nat_lit 683, Int.ofNat (nat_lit 23509942041600))]
theorem block008_data_flat039_step : block008_data_flat039 = (CoefficientMerge.scale (23509942041600 : Int) atom0516Coded) := by decide +kernel
theorem block008_data_flat039_original : block008_data_flat039 = (CoefficientMerge.scale (23509942041600 : Int) atom0516Coded) := by
  rw [block008_data_flat039_step]
def block008_data_flat040 : CoefficientMerge.Poly := [(nat_lit 684, Int.ofNat (nat_lit 39142615079680))]
theorem block008_data_flat040_step : block008_data_flat040 = (CoefficientMerge.scale (39142615079680 : Int) atom0517Coded) := by decide +kernel
theorem block008_data_flat040_original : block008_data_flat040 = (CoefficientMerge.scale (39142615079680 : Int) atom0517Coded) := by
  rw [block008_data_flat040_step]
def block008_data_flat041 : CoefficientMerge.Poly := [(nat_lit 683, Int.ofNat (nat_lit 23509942041600)), (nat_lit 684, Int.ofNat (nat_lit 39142615079680))]
theorem block008_data_flat041_step : block008_data_flat041 = (CoefficientMerge.fastMerge block008_data_flat039 block008_data_flat040) := by decide +kernel
theorem block008_data_flat041_original : block008_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23509942041600 : Int) atom0516Coded) (CoefficientMerge.scale (39142615079680 : Int) atom0517Coded)) := by
  rw [block008_data_flat041_step, block008_data_flat039_original, block008_data_flat040_original]
def block008_data_flat042 : CoefficientMerge.Poly := [(nat_lit 685, Int.ofNat (nat_lit 34691663462400))]
theorem block008_data_flat042_step : block008_data_flat042 = (CoefficientMerge.scale (34691663462400 : Int) atom0518Coded) := by decide +kernel
theorem block008_data_flat042_original : block008_data_flat042 = (CoefficientMerge.scale (34691663462400 : Int) atom0518Coded) := by
  rw [block008_data_flat042_step]
def block008_data_flat043 : CoefficientMerge.Poly := [(nat_lit 686, Int.ofNat (nat_lit 34725489926400))]
theorem block008_data_flat043_step : block008_data_flat043 = (CoefficientMerge.scale (34725489926400 : Int) atom0519Coded) := by decide +kernel
theorem block008_data_flat043_original : block008_data_flat043 = (CoefficientMerge.scale (34725489926400 : Int) atom0519Coded) := by
  rw [block008_data_flat043_step]
def block008_data_flat044 : CoefficientMerge.Poly := [(nat_lit 687, Int.ofNat (nat_lit 43659826560000))]
theorem block008_data_flat044_step : block008_data_flat044 = (CoefficientMerge.scale (43659826560000 : Int) atom0520Coded) := by decide +kernel
theorem block008_data_flat044_original : block008_data_flat044 = (CoefficientMerge.scale (43659826560000 : Int) atom0520Coded) := by
  rw [block008_data_flat044_step]
def block008_data_flat045 : CoefficientMerge.Poly := [(nat_lit 686, Int.ofNat (nat_lit 34725489926400)), (nat_lit 687, Int.ofNat (nat_lit 43659826560000))]
theorem block008_data_flat045_step : block008_data_flat045 = (CoefficientMerge.fastMerge block008_data_flat043 block008_data_flat044) := by decide +kernel
theorem block008_data_flat045_original : block008_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34725489926400 : Int) atom0519Coded) (CoefficientMerge.scale (43659826560000 : Int) atom0520Coded)) := by
  rw [block008_data_flat045_step, block008_data_flat043_original, block008_data_flat044_original]
def block008_data_flat046 : CoefficientMerge.Poly := [(nat_lit 685, Int.ofNat (nat_lit 34691663462400)), (nat_lit 686, Int.ofNat (nat_lit 34725489926400)), (nat_lit 687, Int.ofNat (nat_lit 43659826560000))]
theorem block008_data_flat046_step : block008_data_flat046 = (CoefficientMerge.fastMerge block008_data_flat042 block008_data_flat045) := by decide +kernel
theorem block008_data_flat046_original : block008_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34691663462400 : Int) atom0518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34725489926400 : Int) atom0519Coded) (CoefficientMerge.scale (43659826560000 : Int) atom0520Coded))) := by
  rw [block008_data_flat046_step, block008_data_flat042_original, block008_data_flat045_original]
def block008_data_flat047 : CoefficientMerge.Poly := [(nat_lit 683, Int.ofNat (nat_lit 23509942041600)), (nat_lit 684, Int.ofNat (nat_lit 39142615079680)), (nat_lit 685, Int.ofNat (nat_lit 34691663462400)), (nat_lit 686, Int.ofNat (nat_lit 34725489926400)), (nat_lit 687, Int.ofNat (nat_lit 43659826560000))]
theorem block008_data_flat047_step : block008_data_flat047 = (CoefficientMerge.fastMerge block008_data_flat041 block008_data_flat046) := by decide +kernel
theorem block008_data_flat047_original : block008_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23509942041600 : Int) atom0516Coded) (CoefficientMerge.scale (39142615079680 : Int) atom0517Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34691663462400 : Int) atom0518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34725489926400 : Int) atom0519Coded) (CoefficientMerge.scale (43659826560000 : Int) atom0520Coded)))) := by
  rw [block008_data_flat047_step, block008_data_flat041_original, block008_data_flat046_original]
def block008_data_flat048 : CoefficientMerge.Poly := [(nat_lit 688, Int.ofNat (nat_lit 37535436288000))]
theorem block008_data_flat048_step : block008_data_flat048 = (CoefficientMerge.scale (37535436288000 : Int) atom0521Coded) := by decide +kernel
theorem block008_data_flat048_original : block008_data_flat048 = (CoefficientMerge.scale (37535436288000 : Int) atom0521Coded) := by
  rw [block008_data_flat048_step]
def block008_data_flat049 : CoefficientMerge.Poly := [(nat_lit 689, Int.ofNat (nat_lit 46090191168000))]
theorem block008_data_flat049_step : block008_data_flat049 = (CoefficientMerge.scale (46090191168000 : Int) atom0522Coded) := by decide +kernel
theorem block008_data_flat049_original : block008_data_flat049 = (CoefficientMerge.scale (46090191168000 : Int) atom0522Coded) := by
  rw [block008_data_flat049_step]
def block008_data_flat050 : CoefficientMerge.Poly := [(nat_lit 688, Int.ofNat (nat_lit 37535436288000)), (nat_lit 689, Int.ofNat (nat_lit 46090191168000))]
theorem block008_data_flat050_step : block008_data_flat050 = (CoefficientMerge.fastMerge block008_data_flat048 block008_data_flat049) := by decide +kernel
theorem block008_data_flat050_original : block008_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (37535436288000 : Int) atom0521Coded) (CoefficientMerge.scale (46090191168000 : Int) atom0522Coded)) := by
  rw [block008_data_flat050_step, block008_data_flat048_original, block008_data_flat049_original]
def block008_data_flat051 : CoefficientMerge.Poly := [(nat_lit 690, Int.ofNat (nat_lit 41618641075200))]
theorem block008_data_flat051_step : block008_data_flat051 = (CoefficientMerge.scale (41618641075200 : Int) atom0523Coded) := by decide +kernel
theorem block008_data_flat051_original : block008_data_flat051 = (CoefficientMerge.scale (41618641075200 : Int) atom0523Coded) := by
  rw [block008_data_flat051_step]
def block008_data_flat052 : CoefficientMerge.Poly := [(nat_lit 691, Int.ofNat (nat_lit 37129480819200))]
theorem block008_data_flat052_step : block008_data_flat052 = (CoefficientMerge.scale (37129480819200 : Int) atom0524Coded) := by decide +kernel
theorem block008_data_flat052_original : block008_data_flat052 = (CoefficientMerge.scale (37129480819200 : Int) atom0524Coded) := by
  rw [block008_data_flat052_step]
def block008_data_flat053 : CoefficientMerge.Poly := [(nat_lit 692, Int.ofNat (nat_lit 37510611264000))]
theorem block008_data_flat053_step : block008_data_flat053 = (CoefficientMerge.scale (37510611264000 : Int) atom0525Coded) := by decide +kernel
theorem block008_data_flat053_original : block008_data_flat053 = (CoefficientMerge.scale (37510611264000 : Int) atom0525Coded) := by
  rw [block008_data_flat053_step]
def block008_data_flat054 : CoefficientMerge.Poly := [(nat_lit 691, Int.ofNat (nat_lit 37129480819200)), (nat_lit 692, Int.ofNat (nat_lit 37510611264000))]
theorem block008_data_flat054_step : block008_data_flat054 = (CoefficientMerge.fastMerge block008_data_flat052 block008_data_flat053) := by decide +kernel
theorem block008_data_flat054_original : block008_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (37129480819200 : Int) atom0524Coded) (CoefficientMerge.scale (37510611264000 : Int) atom0525Coded)) := by
  rw [block008_data_flat054_step, block008_data_flat052_original, block008_data_flat053_original]
def block008_data_flat055 : CoefficientMerge.Poly := [(nat_lit 690, Int.ofNat (nat_lit 41618641075200)), (nat_lit 691, Int.ofNat (nat_lit 37129480819200)), (nat_lit 692, Int.ofNat (nat_lit 37510611264000))]
theorem block008_data_flat055_step : block008_data_flat055 = (CoefficientMerge.fastMerge block008_data_flat051 block008_data_flat054) := by decide +kernel
theorem block008_data_flat055_original : block008_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (41618641075200 : Int) atom0523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37129480819200 : Int) atom0524Coded) (CoefficientMerge.scale (37510611264000 : Int) atom0525Coded))) := by
  rw [block008_data_flat055_step, block008_data_flat051_original, block008_data_flat054_original]
def block008_data_flat056 : CoefficientMerge.Poly := [(nat_lit 688, Int.ofNat (nat_lit 37535436288000)), (nat_lit 689, Int.ofNat (nat_lit 46090191168000)), (nat_lit 690, Int.ofNat (nat_lit 41618641075200)), (nat_lit 691, Int.ofNat (nat_lit 37129480819200)), (nat_lit 692, Int.ofNat (nat_lit 37510611264000))]
theorem block008_data_flat056_step : block008_data_flat056 = (CoefficientMerge.fastMerge block008_data_flat050 block008_data_flat055) := by decide +kernel
theorem block008_data_flat056_original : block008_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37535436288000 : Int) atom0521Coded) (CoefficientMerge.scale (46090191168000 : Int) atom0522Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41618641075200 : Int) atom0523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37129480819200 : Int) atom0524Coded) (CoefficientMerge.scale (37510611264000 : Int) atom0525Coded)))) := by
  rw [block008_data_flat056_step, block008_data_flat050_original, block008_data_flat055_original]
def block008_data_flat057 : CoefficientMerge.Poly := [(nat_lit 683, Int.ofNat (nat_lit 23509942041600)), (nat_lit 684, Int.ofNat (nat_lit 39142615079680)), (nat_lit 685, Int.ofNat (nat_lit 34691663462400)), (nat_lit 686, Int.ofNat (nat_lit 34725489926400)), (nat_lit 687, Int.ofNat (nat_lit 43659826560000)), (nat_lit 688, Int.ofNat (nat_lit 37535436288000)), (nat_lit 689, Int.ofNat (nat_lit 46090191168000)), (nat_lit 690, Int.ofNat (nat_lit 41618641075200)), (nat_lit 691, Int.ofNat (nat_lit 37129480819200)), (nat_lit 692, Int.ofNat (nat_lit 37510611264000))]
theorem block008_data_flat057_step : block008_data_flat057 = (CoefficientMerge.fastMerge block008_data_flat047 block008_data_flat056) := by decide +kernel
theorem block008_data_flat057_original : block008_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23509942041600 : Int) atom0516Coded) (CoefficientMerge.scale (39142615079680 : Int) atom0517Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34691663462400 : Int) atom0518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34725489926400 : Int) atom0519Coded) (CoefficientMerge.scale (43659826560000 : Int) atom0520Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37535436288000 : Int) atom0521Coded) (CoefficientMerge.scale (46090191168000 : Int) atom0522Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41618641075200 : Int) atom0523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37129480819200 : Int) atom0524Coded) (CoefficientMerge.scale (37510611264000 : Int) atom0525Coded))))) := by
  rw [block008_data_flat057_step, block008_data_flat047_original, block008_data_flat056_original]
def block008_data_flat058 : CoefficientMerge.Poly := [(nat_lit 705, Int.ofNat (nat_lit 21593669171200))]
theorem block008_data_flat058_step : block008_data_flat058 = (CoefficientMerge.scale (21593669171200 : Int) atom0526Coded) := by decide +kernel
theorem block008_data_flat058_original : block008_data_flat058 = (CoefficientMerge.scale (21593669171200 : Int) atom0526Coded) := by
  rw [block008_data_flat058_step]
def block008_data_flat059 : CoefficientMerge.Poly := [(nat_lit 706, Int.ofNat (nat_lit 37959288304000))]
theorem block008_data_flat059_step : block008_data_flat059 = (CoefficientMerge.scale (37959288304000 : Int) atom0527Coded) := by decide +kernel
theorem block008_data_flat059_original : block008_data_flat059 = (CoefficientMerge.scale (37959288304000 : Int) atom0527Coded) := by
  rw [block008_data_flat059_step]
def block008_data_flat060 : CoefficientMerge.Poly := [(nat_lit 705, Int.ofNat (nat_lit 21593669171200)), (nat_lit 706, Int.ofNat (nat_lit 37959288304000))]
theorem block008_data_flat060_step : block008_data_flat060 = (CoefficientMerge.fastMerge block008_data_flat058 block008_data_flat059) := by decide +kernel
theorem block008_data_flat060_original : block008_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21593669171200 : Int) atom0526Coded) (CoefficientMerge.scale (37959288304000 : Int) atom0527Coded)) := by
  rw [block008_data_flat060_step, block008_data_flat058_original, block008_data_flat059_original]
def block008_data_flat061 : CoefficientMerge.Poly := [(nat_lit 707, Int.ofNat (nat_lit 34193114233600))]
theorem block008_data_flat061_step : block008_data_flat061 = (CoefficientMerge.scale (34193114233600 : Int) atom0528Coded) := by decide +kernel
theorem block008_data_flat061_original : block008_data_flat061 = (CoefficientMerge.scale (34193114233600 : Int) atom0528Coded) := by
  rw [block008_data_flat061_step]
def block008_data_flat062 : CoefficientMerge.Poly := [(nat_lit 708, Int.ofNat (nat_lit 41082437401600))]
theorem block008_data_flat062_step : block008_data_flat062 = (CoefficientMerge.scale (41082437401600 : Int) atom0529Coded) := by decide +kernel
theorem block008_data_flat062_original : block008_data_flat062 = (CoefficientMerge.scale (41082437401600 : Int) atom0529Coded) := by
  rw [block008_data_flat062_step]
def block008_data_flat063 : CoefficientMerge.Poly := [(nat_lit 709, Int.ofNat (nat_lit 36148462828800))]
theorem block008_data_flat063_step : block008_data_flat063 = (CoefficientMerge.scale (36148462828800 : Int) atom0530Coded) := by decide +kernel
theorem block008_data_flat063_original : block008_data_flat063 = (CoefficientMerge.scale (36148462828800 : Int) atom0530Coded) := by
  rw [block008_data_flat063_step]
def block008_data_flat064 : CoefficientMerge.Poly := [(nat_lit 708, Int.ofNat (nat_lit 41082437401600)), (nat_lit 709, Int.ofNat (nat_lit 36148462828800))]
theorem block008_data_flat064_step : block008_data_flat064 = (CoefficientMerge.fastMerge block008_data_flat062 block008_data_flat063) := by decide +kernel
theorem block008_data_flat064_original : block008_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (41082437401600 : Int) atom0529Coded) (CoefficientMerge.scale (36148462828800 : Int) atom0530Coded)) := by
  rw [block008_data_flat064_step, block008_data_flat062_original, block008_data_flat063_original]
def block008_data_flat065 : CoefficientMerge.Poly := [(nat_lit 707, Int.ofNat (nat_lit 34193114233600)), (nat_lit 708, Int.ofNat (nat_lit 41082437401600)), (nat_lit 709, Int.ofNat (nat_lit 36148462828800))]
theorem block008_data_flat065_step : block008_data_flat065 = (CoefficientMerge.fastMerge block008_data_flat061 block008_data_flat064) := by decide +kernel
theorem block008_data_flat065_original : block008_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34193114233600 : Int) atom0528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41082437401600 : Int) atom0529Coded) (CoefficientMerge.scale (36148462828800 : Int) atom0530Coded))) := by
  rw [block008_data_flat065_step, block008_data_flat061_original, block008_data_flat064_original]
def block008_data_flat066 : CoefficientMerge.Poly := [(nat_lit 705, Int.ofNat (nat_lit 21593669171200)), (nat_lit 706, Int.ofNat (nat_lit 37959288304000)), (nat_lit 707, Int.ofNat (nat_lit 34193114233600)), (nat_lit 708, Int.ofNat (nat_lit 41082437401600)), (nat_lit 709, Int.ofNat (nat_lit 36148462828800))]
theorem block008_data_flat066_step : block008_data_flat066 = (CoefficientMerge.fastMerge block008_data_flat060 block008_data_flat065) := by decide +kernel
theorem block008_data_flat066_original : block008_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21593669171200 : Int) atom0526Coded) (CoefficientMerge.scale (37959288304000 : Int) atom0527Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34193114233600 : Int) atom0528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41082437401600 : Int) atom0529Coded) (CoefficientMerge.scale (36148462828800 : Int) atom0530Coded)))) := by
  rw [block008_data_flat066_step, block008_data_flat060_original, block008_data_flat065_original]
def block008_data_flat067 : CoefficientMerge.Poly := [(nat_lit 710, Int.ofNat (nat_lit 44185465408000))]
theorem block008_data_flat067_step : block008_data_flat067 = (CoefficientMerge.scale (44185465408000 : Int) atom0531Coded) := by decide +kernel
theorem block008_data_flat067_original : block008_data_flat067 = (CoefficientMerge.scale (44185465408000 : Int) atom0531Coded) := by
  rw [block008_data_flat067_step]
def block008_data_flat068 : CoefficientMerge.Poly := [(nat_lit 711, Int.ofNat (nat_lit 40050247014400))]
theorem block008_data_flat068_step : block008_data_flat068 = (CoefficientMerge.scale (40050247014400 : Int) atom0532Coded) := by decide +kernel
theorem block008_data_flat068_original : block008_data_flat068 = (CoefficientMerge.scale (40050247014400 : Int) atom0532Coded) := by
  rw [block008_data_flat068_step]
def block008_data_flat069 : CoefficientMerge.Poly := [(nat_lit 710, Int.ofNat (nat_lit 44185465408000)), (nat_lit 711, Int.ofNat (nat_lit 40050247014400))]
theorem block008_data_flat069_step : block008_data_flat069 = (CoefficientMerge.fastMerge block008_data_flat067 block008_data_flat068) := by decide +kernel
theorem block008_data_flat069_original : block008_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (44185465408000 : Int) atom0531Coded) (CoefficientMerge.scale (40050247014400 : Int) atom0532Coded)) := by
  rw [block008_data_flat069_step, block008_data_flat067_original, block008_data_flat068_original]
def block008_data_flat070 : CoefficientMerge.Poly := [(nat_lit 712, Int.ofNat (nat_lit 36979376806400))]
theorem block008_data_flat070_step : block008_data_flat070 = (CoefficientMerge.scale (36979376806400 : Int) atom0533Coded) := by decide +kernel
theorem block008_data_flat070_original : block008_data_flat070 = (CoefficientMerge.scale (36979376806400 : Int) atom0533Coded) := by
  rw [block008_data_flat070_step]
def block008_data_flat071 : CoefficientMerge.Poly := [(nat_lit 713, Int.ofNat (nat_lit 37173350995200))]
theorem block008_data_flat071_step : block008_data_flat071 = (CoefficientMerge.scale (37173350995200 : Int) atom0534Coded) := by decide +kernel
theorem block008_data_flat071_original : block008_data_flat071 = (CoefficientMerge.scale (37173350995200 : Int) atom0534Coded) := by
  rw [block008_data_flat071_step]
def block008_data_flat072 : CoefficientMerge.Poly := [(nat_lit 727, Int.ofNat (nat_lit 21868118640000))]
theorem block008_data_flat072_step : block008_data_flat072 = (CoefficientMerge.scale (21868118640000 : Int) atom0535Coded) := by decide +kernel
theorem block008_data_flat072_original : block008_data_flat072 = (CoefficientMerge.scale (21868118640000 : Int) atom0535Coded) := by
  rw [block008_data_flat072_step]
def block008_data_flat073 : CoefficientMerge.Poly := [(nat_lit 713, Int.ofNat (nat_lit 37173350995200)), (nat_lit 727, Int.ofNat (nat_lit 21868118640000))]
theorem block008_data_flat073_step : block008_data_flat073 = (CoefficientMerge.fastMerge block008_data_flat071 block008_data_flat072) := by decide +kernel
theorem block008_data_flat073_original : block008_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (37173350995200 : Int) atom0534Coded) (CoefficientMerge.scale (21868118640000 : Int) atom0535Coded)) := by
  rw [block008_data_flat073_step, block008_data_flat071_original, block008_data_flat072_original]
def block008_data_flat074 : CoefficientMerge.Poly := [(nat_lit 712, Int.ofNat (nat_lit 36979376806400)), (nat_lit 713, Int.ofNat (nat_lit 37173350995200)), (nat_lit 727, Int.ofNat (nat_lit 21868118640000))]
theorem block008_data_flat074_step : block008_data_flat074 = (CoefficientMerge.fastMerge block008_data_flat070 block008_data_flat073) := by decide +kernel
theorem block008_data_flat074_original : block008_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36979376806400 : Int) atom0533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37173350995200 : Int) atom0534Coded) (CoefficientMerge.scale (21868118640000 : Int) atom0535Coded))) := by
  rw [block008_data_flat074_step, block008_data_flat070_original, block008_data_flat073_original]
def block008_data_flat075 : CoefficientMerge.Poly := [(nat_lit 710, Int.ofNat (nat_lit 44185465408000)), (nat_lit 711, Int.ofNat (nat_lit 40050247014400)), (nat_lit 712, Int.ofNat (nat_lit 36979376806400)), (nat_lit 713, Int.ofNat (nat_lit 37173350995200)), (nat_lit 727, Int.ofNat (nat_lit 21868118640000))]
theorem block008_data_flat075_step : block008_data_flat075 = (CoefficientMerge.fastMerge block008_data_flat069 block008_data_flat074) := by decide +kernel
theorem block008_data_flat075_original : block008_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44185465408000 : Int) atom0531Coded) (CoefficientMerge.scale (40050247014400 : Int) atom0532Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36979376806400 : Int) atom0533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37173350995200 : Int) atom0534Coded) (CoefficientMerge.scale (21868118640000 : Int) atom0535Coded)))) := by
  rw [block008_data_flat075_step, block008_data_flat069_original, block008_data_flat074_original]
def block008_data_flat076 : CoefficientMerge.Poly := [(nat_lit 705, Int.ofNat (nat_lit 21593669171200)), (nat_lit 706, Int.ofNat (nat_lit 37959288304000)), (nat_lit 707, Int.ofNat (nat_lit 34193114233600)), (nat_lit 708, Int.ofNat (nat_lit 41082437401600)), (nat_lit 709, Int.ofNat (nat_lit 36148462828800)), (nat_lit 710, Int.ofNat (nat_lit 44185465408000)), (nat_lit 711, Int.ofNat (nat_lit 40050247014400)), (nat_lit 712, Int.ofNat (nat_lit 36979376806400)), (nat_lit 713, Int.ofNat (nat_lit 37173350995200)), (nat_lit 727, Int.ofNat (nat_lit 21868118640000))]
theorem block008_data_flat076_step : block008_data_flat076 = (CoefficientMerge.fastMerge block008_data_flat066 block008_data_flat075) := by decide +kernel
theorem block008_data_flat076_original : block008_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21593669171200 : Int) atom0526Coded) (CoefficientMerge.scale (37959288304000 : Int) atom0527Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34193114233600 : Int) atom0528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41082437401600 : Int) atom0529Coded) (CoefficientMerge.scale (36148462828800 : Int) atom0530Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44185465408000 : Int) atom0531Coded) (CoefficientMerge.scale (40050247014400 : Int) atom0532Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36979376806400 : Int) atom0533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37173350995200 : Int) atom0534Coded) (CoefficientMerge.scale (21868118640000 : Int) atom0535Coded))))) := by
  rw [block008_data_flat076_step, block008_data_flat066_original, block008_data_flat075_original]
def block008_data_flat077 : CoefficientMerge.Poly := [(nat_lit 683, Int.ofNat (nat_lit 23509942041600)), (nat_lit 684, Int.ofNat (nat_lit 39142615079680)), (nat_lit 685, Int.ofNat (nat_lit 34691663462400)), (nat_lit 686, Int.ofNat (nat_lit 34725489926400)), (nat_lit 687, Int.ofNat (nat_lit 43659826560000)), (nat_lit 688, Int.ofNat (nat_lit 37535436288000)), (nat_lit 689, Int.ofNat (nat_lit 46090191168000)), (nat_lit 690, Int.ofNat (nat_lit 41618641075200)), (nat_lit 691, Int.ofNat (nat_lit 37129480819200)), (nat_lit 692, Int.ofNat (nat_lit 37510611264000)), (nat_lit 705, Int.ofNat (nat_lit 21593669171200)), (nat_lit 706, Int.ofNat (nat_lit 37959288304000)), (nat_lit 707, Int.ofNat (nat_lit 34193114233600)), (nat_lit 708, Int.ofNat (nat_lit 41082437401600)), (nat_lit 709, Int.ofNat (nat_lit 36148462828800)), (nat_lit 710, Int.ofNat (nat_lit 44185465408000)), (nat_lit 711, Int.ofNat (nat_lit 40050247014400)), (nat_lit 712, Int.ofNat (nat_lit 36979376806400)), (nat_lit 713, Int.ofNat (nat_lit 37173350995200)), (nat_lit 727, Int.ofNat (nat_lit 21868118640000))]
theorem block008_data_flat077_step : block008_data_flat077 = (CoefficientMerge.fastMerge block008_data_flat057 block008_data_flat076) := by decide +kernel
theorem block008_data_flat077_original : block008_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23509942041600 : Int) atom0516Coded) (CoefficientMerge.scale (39142615079680 : Int) atom0517Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34691663462400 : Int) atom0518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34725489926400 : Int) atom0519Coded) (CoefficientMerge.scale (43659826560000 : Int) atom0520Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37535436288000 : Int) atom0521Coded) (CoefficientMerge.scale (46090191168000 : Int) atom0522Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41618641075200 : Int) atom0523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37129480819200 : Int) atom0524Coded) (CoefficientMerge.scale (37510611264000 : Int) atom0525Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21593669171200 : Int) atom0526Coded) (CoefficientMerge.scale (37959288304000 : Int) atom0527Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34193114233600 : Int) atom0528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41082437401600 : Int) atom0529Coded) (CoefficientMerge.scale (36148462828800 : Int) atom0530Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44185465408000 : Int) atom0531Coded) (CoefficientMerge.scale (40050247014400 : Int) atom0532Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36979376806400 : Int) atom0533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37173350995200 : Int) atom0534Coded) (CoefficientMerge.scale (21868118640000 : Int) atom0535Coded)))))) := by
  rw [block008_data_flat077_step, block008_data_flat057_original, block008_data_flat076_original]
def block008_data_flat078 : CoefficientMerge.Poly := [(nat_lit 642, Int.ofNat (nat_lit 30403816464000)), (nat_lit 643, Int.ofNat (nat_lit 29787423120000)), (nat_lit 644, Int.ofNat (nat_lit 30487147689600)), (nat_lit 645, Int.ofNat (nat_lit 39992545152000)), (nat_lit 646, Int.ofNat (nat_lit 34392272014800)), (nat_lit 647, Int.ofNat (nat_lit 41077582963200)), (nat_lit 648, Int.ofNat (nat_lit 39334036518000)), (nat_lit 649, Int.ofNat (nat_lit 35737719620400)), (nat_lit 650, Int.ofNat (nat_lit 36469257174000)), (nat_lit 661, Int.ofNat (nat_lit 22070559672000)), (nat_lit 662, Int.ofNat (nat_lit 39833095538880)), (nat_lit 663, Int.ofNat (nat_lit 33381177081280)), (nat_lit 664, Int.ofNat (nat_lit 32429753193600)), (nat_lit 665, Int.ofNat (nat_lit 32838570172800)), (nat_lit 666, Int.ofNat (nat_lit 42138109440000)), (nat_lit 667, Int.ofNat (nat_lit 36296339511600)), (nat_lit 668, Int.ofNat (nat_lit 43895810649600)), (nat_lit 669, Int.ofNat (nat_lit 40925209222800)), (nat_lit 670, Int.ofNat (nat_lit 36790085077200)), (nat_lit 671, Int.ofNat (nat_lit 37409995299600)), (nat_lit 683, Int.ofNat (nat_lit 23509942041600)), (nat_lit 684, Int.ofNat (nat_lit 39142615079680)), (nat_lit 685, Int.ofNat (nat_lit 34691663462400)), (nat_lit 686, Int.ofNat (nat_lit 34725489926400)), (nat_lit 687, Int.ofNat (nat_lit 43659826560000)), (nat_lit 688, Int.ofNat (nat_lit 37535436288000)), (nat_lit 689, Int.ofNat (nat_lit 46090191168000)), (nat_lit 690, Int.ofNat (nat_lit 41618641075200)), (nat_lit 691, Int.ofNat (nat_lit 37129480819200)), (nat_lit 692, Int.ofNat (nat_lit 37510611264000)), (nat_lit 705, Int.ofNat (nat_lit 21593669171200)), (nat_lit 706, Int.ofNat (nat_lit 37959288304000)), (nat_lit 707, Int.ofNat (nat_lit 34193114233600)), (nat_lit 708, Int.ofNat (nat_lit 41082437401600)), (nat_lit 709, Int.ofNat (nat_lit 36148462828800)), (nat_lit 710, Int.ofNat (nat_lit 44185465408000)), (nat_lit 711, Int.ofNat (nat_lit 40050247014400)), (nat_lit 712, Int.ofNat (nat_lit 36979376806400)), (nat_lit 713, Int.ofNat (nat_lit 37173350995200)), (nat_lit 727, Int.ofNat (nat_lit 21868118640000))]
theorem block008_data_flat078_step : block008_data_flat078 = (CoefficientMerge.fastMerge block008_data_flat038 block008_data_flat077) := by decide +kernel
theorem block008_data_flat078_original : block008_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30403816464000 : Int) atom0496Coded) (CoefficientMerge.scale (29787423120000 : Int) atom0497Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30487147689600 : Int) atom0498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39992545152000 : Int) atom0499Coded) (CoefficientMerge.scale (34392272014800 : Int) atom0500Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41077582963200 : Int) atom0501Coded) (CoefficientMerge.scale (39334036518000 : Int) atom0502Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35737719620400 : Int) atom0503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36469257174000 : Int) atom0504Coded) (CoefficientMerge.scale (22070559672000 : Int) atom0505Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39833095538880 : Int) atom0506Coded) (CoefficientMerge.scale (33381177081280 : Int) atom0507Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32429753193600 : Int) atom0508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32838570172800 : Int) atom0509Coded) (CoefficientMerge.scale (42138109440000 : Int) atom0510Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36296339511600 : Int) atom0511Coded) (CoefficientMerge.scale (43895810649600 : Int) atom0512Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40925209222800 : Int) atom0513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36790085077200 : Int) atom0514Coded) (CoefficientMerge.scale (37409995299600 : Int) atom0515Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23509942041600 : Int) atom0516Coded) (CoefficientMerge.scale (39142615079680 : Int) atom0517Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34691663462400 : Int) atom0518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34725489926400 : Int) atom0519Coded) (CoefficientMerge.scale (43659826560000 : Int) atom0520Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37535436288000 : Int) atom0521Coded) (CoefficientMerge.scale (46090191168000 : Int) atom0522Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41618641075200 : Int) atom0523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37129480819200 : Int) atom0524Coded) (CoefficientMerge.scale (37510611264000 : Int) atom0525Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21593669171200 : Int) atom0526Coded) (CoefficientMerge.scale (37959288304000 : Int) atom0527Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34193114233600 : Int) atom0528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41082437401600 : Int) atom0529Coded) (CoefficientMerge.scale (36148462828800 : Int) atom0530Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44185465408000 : Int) atom0531Coded) (CoefficientMerge.scale (40050247014400 : Int) atom0532Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36979376806400 : Int) atom0533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37173350995200 : Int) atom0534Coded) (CoefficientMerge.scale (21868118640000 : Int) atom0535Coded))))))) := by
  rw [block008_data_flat078_step, block008_data_flat038_original, block008_data_flat077_original]
def block008_data_flat079 : CoefficientMerge.Poly := [(nat_lit 728, Int.ofNat (nat_lit 39387741782400))]
theorem block008_data_flat079_step : block008_data_flat079 = (CoefficientMerge.scale (39387741782400 : Int) atom0536Coded) := by decide +kernel
theorem block008_data_flat079_original : block008_data_flat079 = (CoefficientMerge.scale (39387741782400 : Int) atom0536Coded) := by
  rw [block008_data_flat079_step]
def block008_data_flat080 : CoefficientMerge.Poly := [(nat_lit 729, Int.ofNat (nat_lit 42390720640800))]
theorem block008_data_flat080_step : block008_data_flat080 = (CoefficientMerge.scale (42390720640800 : Int) atom0537Coded) := by decide +kernel
theorem block008_data_flat080_original : block008_data_flat080 = (CoefficientMerge.scale (42390720640800 : Int) atom0537Coded) := by
  rw [block008_data_flat080_step]
def block008_data_flat081 : CoefficientMerge.Poly := [(nat_lit 728, Int.ofNat (nat_lit 39387741782400)), (nat_lit 729, Int.ofNat (nat_lit 42390720640800))]
theorem block008_data_flat081_step : block008_data_flat081 = (CoefficientMerge.fastMerge block008_data_flat079 block008_data_flat080) := by decide +kernel
theorem block008_data_flat081_original : block008_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (39387741782400 : Int) atom0536Coded) (CoefficientMerge.scale (42390720640800 : Int) atom0537Coded)) := by
  rw [block008_data_flat081_step, block008_data_flat079_original, block008_data_flat080_original]
def block008_data_flat082 : CoefficientMerge.Poly := [(nat_lit 730, Int.ofNat (nat_lit 36777587119200))]
theorem block008_data_flat082_step : block008_data_flat082 = (CoefficientMerge.scale (36777587119200 : Int) atom0538Coded) := by decide +kernel
theorem block008_data_flat082_original : block008_data_flat082 = (CoefficientMerge.scale (36777587119200 : Int) atom0538Coded) := by
  rw [block008_data_flat082_step]
def block008_data_flat083 : CoefficientMerge.Poly := [(nat_lit 731, Int.ofNat (nat_lit 45766897344000))]
theorem block008_data_flat083_step : block008_data_flat083 = (CoefficientMerge.scale (45766897344000 : Int) atom0539Coded) := by decide +kernel
theorem block008_data_flat083_original : block008_data_flat083 = (CoefficientMerge.scale (45766897344000 : Int) atom0539Coded) := by
  rw [block008_data_flat083_step]
def block008_data_flat084 : CoefficientMerge.Poly := [(nat_lit 732, Int.ofNat (nat_lit 41968010649600))]
theorem block008_data_flat084_step : block008_data_flat084 = (CoefficientMerge.scale (41968010649600 : Int) atom0540Coded) := by decide +kernel
theorem block008_data_flat084_original : block008_data_flat084 = (CoefficientMerge.scale (41968010649600 : Int) atom0540Coded) := by
  rw [block008_data_flat084_step]
def block008_data_flat085 : CoefficientMerge.Poly := [(nat_lit 731, Int.ofNat (nat_lit 45766897344000)), (nat_lit 732, Int.ofNat (nat_lit 41968010649600))]
theorem block008_data_flat085_step : block008_data_flat085 = (CoefficientMerge.fastMerge block008_data_flat083 block008_data_flat084) := by decide +kernel
theorem block008_data_flat085_original : block008_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (45766897344000 : Int) atom0539Coded) (CoefficientMerge.scale (41968010649600 : Int) atom0540Coded)) := by
  rw [block008_data_flat085_step, block008_data_flat083_original, block008_data_flat084_original]
def block008_data_flat086 : CoefficientMerge.Poly := [(nat_lit 730, Int.ofNat (nat_lit 36777587119200)), (nat_lit 731, Int.ofNat (nat_lit 45766897344000)), (nat_lit 732, Int.ofNat (nat_lit 41968010649600))]
theorem block008_data_flat086_step : block008_data_flat086 = (CoefficientMerge.fastMerge block008_data_flat082 block008_data_flat085) := by decide +kernel
theorem block008_data_flat086_original : block008_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36777587119200 : Int) atom0538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45766897344000 : Int) atom0539Coded) (CoefficientMerge.scale (41968010649600 : Int) atom0540Coded))) := by
  rw [block008_data_flat086_step, block008_data_flat082_original, block008_data_flat085_original]
def block008_data_flat087 : CoefficientMerge.Poly := [(nat_lit 728, Int.ofNat (nat_lit 39387741782400)), (nat_lit 729, Int.ofNat (nat_lit 42390720640800)), (nat_lit 730, Int.ofNat (nat_lit 36777587119200)), (nat_lit 731, Int.ofNat (nat_lit 45766897344000)), (nat_lit 732, Int.ofNat (nat_lit 41968010649600))]
theorem block008_data_flat087_step : block008_data_flat087 = (CoefficientMerge.fastMerge block008_data_flat081 block008_data_flat086) := by decide +kernel
theorem block008_data_flat087_original : block008_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39387741782400 : Int) atom0536Coded) (CoefficientMerge.scale (42390720640800 : Int) atom0537Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36777587119200 : Int) atom0538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45766897344000 : Int) atom0539Coded) (CoefficientMerge.scale (41968010649600 : Int) atom0540Coded)))) := by
  rw [block008_data_flat087_step, block008_data_flat081_original, block008_data_flat086_original]
def block008_data_flat088 : CoefficientMerge.Poly := [(nat_lit 733, Int.ofNat (nat_lit 35490237040800))]
theorem block008_data_flat088_step : block008_data_flat088 = (CoefficientMerge.scale (35490237040800 : Int) atom0541Coded) := by decide +kernel
theorem block008_data_flat088_original : block008_data_flat088 = (CoefficientMerge.scale (35490237040800 : Int) atom0541Coded) := by
  rw [block008_data_flat088_step]
def block008_data_flat089 : CoefficientMerge.Poly := [(nat_lit 734, Int.ofNat (nat_lit 38348256844800))]
theorem block008_data_flat089_step : block008_data_flat089 = (CoefficientMerge.scale (38348256844800 : Int) atom0542Coded) := by decide +kernel
theorem block008_data_flat089_original : block008_data_flat089 = (CoefficientMerge.scale (38348256844800 : Int) atom0542Coded) := by
  rw [block008_data_flat089_step]
def block008_data_flat090 : CoefficientMerge.Poly := [(nat_lit 733, Int.ofNat (nat_lit 35490237040800)), (nat_lit 734, Int.ofNat (nat_lit 38348256844800))]
theorem block008_data_flat090_step : block008_data_flat090 = (CoefficientMerge.fastMerge block008_data_flat088 block008_data_flat089) := by decide +kernel
theorem block008_data_flat090_original : block008_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35490237040800 : Int) atom0541Coded) (CoefficientMerge.scale (38348256844800 : Int) atom0542Coded)) := by
  rw [block008_data_flat090_step, block008_data_flat088_original, block008_data_flat089_original]
def block008_data_flat091 : CoefficientMerge.Poly := [(nat_lit 749, Int.ofNat (nat_lit 23400181324800))]
theorem block008_data_flat091_step : block008_data_flat091 = (CoefficientMerge.scale (23400181324800 : Int) atom0543Coded) := by decide +kernel
theorem block008_data_flat091_original : block008_data_flat091 = (CoefficientMerge.scale (23400181324800 : Int) atom0543Coded) := by
  rw [block008_data_flat091_step]
def block008_data_flat092 : CoefficientMerge.Poly := [(nat_lit 750, Int.ofNat (nat_lit 44739847756800))]
theorem block008_data_flat092_step : block008_data_flat092 = (CoefficientMerge.scale (44739847756800 : Int) atom0544Coded) := by decide +kernel
theorem block008_data_flat092_original : block008_data_flat092 = (CoefficientMerge.scale (44739847756800 : Int) atom0544Coded) := by
  rw [block008_data_flat092_step]
def block008_data_flat093 : CoefficientMerge.Poly := [(nat_lit 751, Int.ofNat (nat_lit 38224548633600))]
theorem block008_data_flat093_step : block008_data_flat093 = (CoefficientMerge.scale (38224548633600 : Int) atom0545Coded) := by decide +kernel
theorem block008_data_flat093_original : block008_data_flat093 = (CoefficientMerge.scale (38224548633600 : Int) atom0545Coded) := by
  rw [block008_data_flat093_step]
def block008_data_flat094 : CoefficientMerge.Poly := [(nat_lit 750, Int.ofNat (nat_lit 44739847756800)), (nat_lit 751, Int.ofNat (nat_lit 38224548633600))]
theorem block008_data_flat094_step : block008_data_flat094 = (CoefficientMerge.fastMerge block008_data_flat092 block008_data_flat093) := by decide +kernel
theorem block008_data_flat094_original : block008_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (44739847756800 : Int) atom0544Coded) (CoefficientMerge.scale (38224548633600 : Int) atom0545Coded)) := by
  rw [block008_data_flat094_step, block008_data_flat092_original, block008_data_flat093_original]
def block008_data_flat095 : CoefficientMerge.Poly := [(nat_lit 749, Int.ofNat (nat_lit 23400181324800)), (nat_lit 750, Int.ofNat (nat_lit 44739847756800)), (nat_lit 751, Int.ofNat (nat_lit 38224548633600))]
theorem block008_data_flat095_step : block008_data_flat095 = (CoefficientMerge.fastMerge block008_data_flat091 block008_data_flat094) := by decide +kernel
theorem block008_data_flat095_original : block008_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23400181324800 : Int) atom0543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44739847756800 : Int) atom0544Coded) (CoefficientMerge.scale (38224548633600 : Int) atom0545Coded))) := by
  rw [block008_data_flat095_step, block008_data_flat091_original, block008_data_flat094_original]
def block008_data_flat096 : CoefficientMerge.Poly := [(nat_lit 733, Int.ofNat (nat_lit 35490237040800)), (nat_lit 734, Int.ofNat (nat_lit 38348256844800)), (nat_lit 749, Int.ofNat (nat_lit 23400181324800)), (nat_lit 750, Int.ofNat (nat_lit 44739847756800)), (nat_lit 751, Int.ofNat (nat_lit 38224548633600))]
theorem block008_data_flat096_step : block008_data_flat096 = (CoefficientMerge.fastMerge block008_data_flat090 block008_data_flat095) := by decide +kernel
theorem block008_data_flat096_original : block008_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35490237040800 : Int) atom0541Coded) (CoefficientMerge.scale (38348256844800 : Int) atom0542Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23400181324800 : Int) atom0543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44739847756800 : Int) atom0544Coded) (CoefficientMerge.scale (38224548633600 : Int) atom0545Coded)))) := by
  rw [block008_data_flat096_step, block008_data_flat090_original, block008_data_flat095_original]
def block008_data_flat097 : CoefficientMerge.Poly := [(nat_lit 728, Int.ofNat (nat_lit 39387741782400)), (nat_lit 729, Int.ofNat (nat_lit 42390720640800)), (nat_lit 730, Int.ofNat (nat_lit 36777587119200)), (nat_lit 731, Int.ofNat (nat_lit 45766897344000)), (nat_lit 732, Int.ofNat (nat_lit 41968010649600)), (nat_lit 733, Int.ofNat (nat_lit 35490237040800)), (nat_lit 734, Int.ofNat (nat_lit 38348256844800)), (nat_lit 749, Int.ofNat (nat_lit 23400181324800)), (nat_lit 750, Int.ofNat (nat_lit 44739847756800)), (nat_lit 751, Int.ofNat (nat_lit 38224548633600))]
theorem block008_data_flat097_step : block008_data_flat097 = (CoefficientMerge.fastMerge block008_data_flat087 block008_data_flat096) := by decide +kernel
theorem block008_data_flat097_original : block008_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39387741782400 : Int) atom0536Coded) (CoefficientMerge.scale (42390720640800 : Int) atom0537Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36777587119200 : Int) atom0538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45766897344000 : Int) atom0539Coded) (CoefficientMerge.scale (41968010649600 : Int) atom0540Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35490237040800 : Int) atom0541Coded) (CoefficientMerge.scale (38348256844800 : Int) atom0542Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23400181324800 : Int) atom0543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44739847756800 : Int) atom0544Coded) (CoefficientMerge.scale (38224548633600 : Int) atom0545Coded))))) := by
  rw [block008_data_flat097_step, block008_data_flat087_original, block008_data_flat096_original]
def block008_data_flat098 : CoefficientMerge.Poly := [(nat_lit 752, Int.ofNat (nat_lit 49103153164800))]
theorem block008_data_flat098_step : block008_data_flat098 = (CoefficientMerge.scale (49103153164800 : Int) atom0546Coded) := by decide +kernel
theorem block008_data_flat098_original : block008_data_flat098 = (CoefficientMerge.scale (49103153164800 : Int) atom0546Coded) := by
  rw [block008_data_flat098_step]
def block008_data_flat099 : CoefficientMerge.Poly := [(nat_lit 753, Int.ofNat (nat_lit 45640598169600))]
theorem block008_data_flat099_step : block008_data_flat099 = (CoefficientMerge.scale (45640598169600 : Int) atom0547Coded) := by decide +kernel
theorem block008_data_flat099_original : block008_data_flat099 = (CoefficientMerge.scale (45640598169600 : Int) atom0547Coded) := by
  rw [block008_data_flat099_step]
def block008_data_flat100 : CoefficientMerge.Poly := [(nat_lit 752, Int.ofNat (nat_lit 49103153164800)), (nat_lit 753, Int.ofNat (nat_lit 45640598169600))]
theorem block008_data_flat100_step : block008_data_flat100 = (CoefficientMerge.fastMerge block008_data_flat098 block008_data_flat099) := by decide +kernel
theorem block008_data_flat100_original : block008_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (49103153164800 : Int) atom0546Coded) (CoefficientMerge.scale (45640598169600 : Int) atom0547Coded)) := by
  rw [block008_data_flat100_step, block008_data_flat098_original, block008_data_flat099_original]
def block008_data_flat101 : CoefficientMerge.Poly := [(nat_lit 754, Int.ofNat (nat_lit 35787754598400))]
theorem block008_data_flat101_step : block008_data_flat101 = (CoefficientMerge.scale (35787754598400 : Int) atom0548Coded) := by decide +kernel
theorem block008_data_flat101_original : block008_data_flat101 = (CoefficientMerge.scale (35787754598400 : Int) atom0548Coded) := by
  rw [block008_data_flat101_step]
def block008_data_flat102 : CoefficientMerge.Poly := [(nat_lit 755, Int.ofNat (nat_lit 41321119795200))]
theorem block008_data_flat102_step : block008_data_flat102 = (CoefficientMerge.scale (41321119795200 : Int) atom0549Coded) := by decide +kernel
theorem block008_data_flat102_original : block008_data_flat102 = (CoefficientMerge.scale (41321119795200 : Int) atom0549Coded) := by
  rw [block008_data_flat102_step]
def block008_data_flat103 : CoefficientMerge.Poly := [(nat_lit 771, Int.ofNat (nat_lit 28066300416000))]
theorem block008_data_flat103_step : block008_data_flat103 = (CoefficientMerge.scale (28066300416000 : Int) atom0550Coded) := by decide +kernel
theorem block008_data_flat103_original : block008_data_flat103 = (CoefficientMerge.scale (28066300416000 : Int) atom0550Coded) := by
  rw [block008_data_flat103_step]
def block008_data_flat104 : CoefficientMerge.Poly := [(nat_lit 755, Int.ofNat (nat_lit 41321119795200)), (nat_lit 771, Int.ofNat (nat_lit 28066300416000))]
theorem block008_data_flat104_step : block008_data_flat104 = (CoefficientMerge.fastMerge block008_data_flat102 block008_data_flat103) := by decide +kernel
theorem block008_data_flat104_original : block008_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (41321119795200 : Int) atom0549Coded) (CoefficientMerge.scale (28066300416000 : Int) atom0550Coded)) := by
  rw [block008_data_flat104_step, block008_data_flat102_original, block008_data_flat103_original]
def block008_data_flat105 : CoefficientMerge.Poly := [(nat_lit 754, Int.ofNat (nat_lit 35787754598400)), (nat_lit 755, Int.ofNat (nat_lit 41321119795200)), (nat_lit 771, Int.ofNat (nat_lit 28066300416000))]
theorem block008_data_flat105_step : block008_data_flat105 = (CoefficientMerge.fastMerge block008_data_flat101 block008_data_flat104) := by decide +kernel
theorem block008_data_flat105_original : block008_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35787754598400 : Int) atom0548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41321119795200 : Int) atom0549Coded) (CoefficientMerge.scale (28066300416000 : Int) atom0550Coded))) := by
  rw [block008_data_flat105_step, block008_data_flat101_original, block008_data_flat104_original]
def block008_data_flat106 : CoefficientMerge.Poly := [(nat_lit 752, Int.ofNat (nat_lit 49103153164800)), (nat_lit 753, Int.ofNat (nat_lit 45640598169600)), (nat_lit 754, Int.ofNat (nat_lit 35787754598400)), (nat_lit 755, Int.ofNat (nat_lit 41321119795200)), (nat_lit 771, Int.ofNat (nat_lit 28066300416000))]
theorem block008_data_flat106_step : block008_data_flat106 = (CoefficientMerge.fastMerge block008_data_flat100 block008_data_flat105) := by decide +kernel
theorem block008_data_flat106_original : block008_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49103153164800 : Int) atom0546Coded) (CoefficientMerge.scale (45640598169600 : Int) atom0547Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35787754598400 : Int) atom0548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41321119795200 : Int) atom0549Coded) (CoefficientMerge.scale (28066300416000 : Int) atom0550Coded)))) := by
  rw [block008_data_flat106_step, block008_data_flat100_original, block008_data_flat105_original]
def block008_data_flat107 : CoefficientMerge.Poly := [(nat_lit 772, Int.ofNat (nat_lit 46229500800000))]
theorem block008_data_flat107_step : block008_data_flat107 = (CoefficientMerge.scale (46229500800000 : Int) atom0551Coded) := by decide +kernel
theorem block008_data_flat107_original : block008_data_flat107 = (CoefficientMerge.scale (46229500800000 : Int) atom0551Coded) := by
  rw [block008_data_flat107_step]
def block008_data_flat108 : CoefficientMerge.Poly := [(nat_lit 773, Int.ofNat (nat_lit 61253619033600))]
theorem block008_data_flat108_step : block008_data_flat108 = (CoefficientMerge.scale (61253619033600 : Int) atom0552Coded) := by decide +kernel
theorem block008_data_flat108_original : block008_data_flat108 = (CoefficientMerge.scale (61253619033600 : Int) atom0552Coded) := by
  rw [block008_data_flat108_step]
def block008_data_flat109 : CoefficientMerge.Poly := [(nat_lit 772, Int.ofNat (nat_lit 46229500800000)), (nat_lit 773, Int.ofNat (nat_lit 61253619033600))]
theorem block008_data_flat109_step : block008_data_flat109 = (CoefficientMerge.fastMerge block008_data_flat107 block008_data_flat108) := by decide +kernel
theorem block008_data_flat109_original : block008_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46229500800000 : Int) atom0551Coded) (CoefficientMerge.scale (61253619033600 : Int) atom0552Coded)) := by
  rw [block008_data_flat109_step, block008_data_flat107_original, block008_data_flat108_original]
def block008_data_flat110 : CoefficientMerge.Poly := [(nat_lit 774, Int.ofNat (nat_lit 57872247552000))]
theorem block008_data_flat110_step : block008_data_flat110 = (CoefficientMerge.scale (57872247552000 : Int) atom0553Coded) := by decide +kernel
theorem block008_data_flat110_original : block008_data_flat110 = (CoefficientMerge.scale (57872247552000 : Int) atom0553Coded) := by
  rw [block008_data_flat110_step]
def block008_data_flat111 : CoefficientMerge.Poly := [(nat_lit 775, Int.ofNat (nat_lit 36902417126400))]
theorem block008_data_flat111_step : block008_data_flat111 = (CoefficientMerge.scale (36902417126400 : Int) atom0554Coded) := by decide +kernel
theorem block008_data_flat111_original : block008_data_flat111 = (CoefficientMerge.scale (36902417126400 : Int) atom0554Coded) := by
  rw [block008_data_flat111_step]
def block008_data_flat112 : CoefficientMerge.Poly := [(nat_lit 776, Int.ofNat (nat_lit 42460507857600))]
theorem block008_data_flat112_step : block008_data_flat112 = (CoefficientMerge.scale (42460507857600 : Int) atom0555Coded) := by decide +kernel
theorem block008_data_flat112_original : block008_data_flat112 = (CoefficientMerge.scale (42460507857600 : Int) atom0555Coded) := by
  rw [block008_data_flat112_step]
def block008_data_flat113 : CoefficientMerge.Poly := [(nat_lit 775, Int.ofNat (nat_lit 36902417126400)), (nat_lit 776, Int.ofNat (nat_lit 42460507857600))]
theorem block008_data_flat113_step : block008_data_flat113 = (CoefficientMerge.fastMerge block008_data_flat111 block008_data_flat112) := by decide +kernel
theorem block008_data_flat113_original : block008_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36902417126400 : Int) atom0554Coded) (CoefficientMerge.scale (42460507857600 : Int) atom0555Coded)) := by
  rw [block008_data_flat113_step, block008_data_flat111_original, block008_data_flat112_original]
def block008_data_flat114 : CoefficientMerge.Poly := [(nat_lit 774, Int.ofNat (nat_lit 57872247552000)), (nat_lit 775, Int.ofNat (nat_lit 36902417126400)), (nat_lit 776, Int.ofNat (nat_lit 42460507857600))]
theorem block008_data_flat114_step : block008_data_flat114 = (CoefficientMerge.fastMerge block008_data_flat110 block008_data_flat113) := by decide +kernel
theorem block008_data_flat114_original : block008_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (57872247552000 : Int) atom0553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36902417126400 : Int) atom0554Coded) (CoefficientMerge.scale (42460507857600 : Int) atom0555Coded))) := by
  rw [block008_data_flat114_step, block008_data_flat110_original, block008_data_flat113_original]
def block008_data_flat115 : CoefficientMerge.Poly := [(nat_lit 772, Int.ofNat (nat_lit 46229500800000)), (nat_lit 773, Int.ofNat (nat_lit 61253619033600)), (nat_lit 774, Int.ofNat (nat_lit 57872247552000)), (nat_lit 775, Int.ofNat (nat_lit 36902417126400)), (nat_lit 776, Int.ofNat (nat_lit 42460507857600))]
theorem block008_data_flat115_step : block008_data_flat115 = (CoefficientMerge.fastMerge block008_data_flat109 block008_data_flat114) := by decide +kernel
theorem block008_data_flat115_original : block008_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46229500800000 : Int) atom0551Coded) (CoefficientMerge.scale (61253619033600 : Int) atom0552Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57872247552000 : Int) atom0553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36902417126400 : Int) atom0554Coded) (CoefficientMerge.scale (42460507857600 : Int) atom0555Coded)))) := by
  rw [block008_data_flat115_step, block008_data_flat109_original, block008_data_flat114_original]
def block008_data_flat116 : CoefficientMerge.Poly := [(nat_lit 752, Int.ofNat (nat_lit 49103153164800)), (nat_lit 753, Int.ofNat (nat_lit 45640598169600)), (nat_lit 754, Int.ofNat (nat_lit 35787754598400)), (nat_lit 755, Int.ofNat (nat_lit 41321119795200)), (nat_lit 771, Int.ofNat (nat_lit 28066300416000)), (nat_lit 772, Int.ofNat (nat_lit 46229500800000)), (nat_lit 773, Int.ofNat (nat_lit 61253619033600)), (nat_lit 774, Int.ofNat (nat_lit 57872247552000)), (nat_lit 775, Int.ofNat (nat_lit 36902417126400)), (nat_lit 776, Int.ofNat (nat_lit 42460507857600))]
theorem block008_data_flat116_step : block008_data_flat116 = (CoefficientMerge.fastMerge block008_data_flat106 block008_data_flat115) := by decide +kernel
theorem block008_data_flat116_original : block008_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49103153164800 : Int) atom0546Coded) (CoefficientMerge.scale (45640598169600 : Int) atom0547Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35787754598400 : Int) atom0548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41321119795200 : Int) atom0549Coded) (CoefficientMerge.scale (28066300416000 : Int) atom0550Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46229500800000 : Int) atom0551Coded) (CoefficientMerge.scale (61253619033600 : Int) atom0552Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57872247552000 : Int) atom0553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36902417126400 : Int) atom0554Coded) (CoefficientMerge.scale (42460507857600 : Int) atom0555Coded))))) := by
  rw [block008_data_flat116_step, block008_data_flat106_original, block008_data_flat115_original]
def block008_data_flat117 : CoefficientMerge.Poly := [(nat_lit 728, Int.ofNat (nat_lit 39387741782400)), (nat_lit 729, Int.ofNat (nat_lit 42390720640800)), (nat_lit 730, Int.ofNat (nat_lit 36777587119200)), (nat_lit 731, Int.ofNat (nat_lit 45766897344000)), (nat_lit 732, Int.ofNat (nat_lit 41968010649600)), (nat_lit 733, Int.ofNat (nat_lit 35490237040800)), (nat_lit 734, Int.ofNat (nat_lit 38348256844800)), (nat_lit 749, Int.ofNat (nat_lit 23400181324800)), (nat_lit 750, Int.ofNat (nat_lit 44739847756800)), (nat_lit 751, Int.ofNat (nat_lit 38224548633600)), (nat_lit 752, Int.ofNat (nat_lit 49103153164800)), (nat_lit 753, Int.ofNat (nat_lit 45640598169600)), (nat_lit 754, Int.ofNat (nat_lit 35787754598400)), (nat_lit 755, Int.ofNat (nat_lit 41321119795200)), (nat_lit 771, Int.ofNat (nat_lit 28066300416000)), (nat_lit 772, Int.ofNat (nat_lit 46229500800000)), (nat_lit 773, Int.ofNat (nat_lit 61253619033600)), (nat_lit 774, Int.ofNat (nat_lit 57872247552000)), (nat_lit 775, Int.ofNat (nat_lit 36902417126400)), (nat_lit 776, Int.ofNat (nat_lit 42460507857600))]
theorem block008_data_flat117_step : block008_data_flat117 = (CoefficientMerge.fastMerge block008_data_flat097 block008_data_flat116) := by decide +kernel
theorem block008_data_flat117_original : block008_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39387741782400 : Int) atom0536Coded) (CoefficientMerge.scale (42390720640800 : Int) atom0537Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36777587119200 : Int) atom0538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45766897344000 : Int) atom0539Coded) (CoefficientMerge.scale (41968010649600 : Int) atom0540Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35490237040800 : Int) atom0541Coded) (CoefficientMerge.scale (38348256844800 : Int) atom0542Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23400181324800 : Int) atom0543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44739847756800 : Int) atom0544Coded) (CoefficientMerge.scale (38224548633600 : Int) atom0545Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49103153164800 : Int) atom0546Coded) (CoefficientMerge.scale (45640598169600 : Int) atom0547Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35787754598400 : Int) atom0548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41321119795200 : Int) atom0549Coded) (CoefficientMerge.scale (28066300416000 : Int) atom0550Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46229500800000 : Int) atom0551Coded) (CoefficientMerge.scale (61253619033600 : Int) atom0552Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57872247552000 : Int) atom0553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36902417126400 : Int) atom0554Coded) (CoefficientMerge.scale (42460507857600 : Int) atom0555Coded)))))) := by
  rw [block008_data_flat117_step, block008_data_flat097_original, block008_data_flat116_original]
def block008_data_flat118 : CoefficientMerge.Poly := [(nat_lit 793, Int.ofNat (nat_lit 17241316485120))]
theorem block008_data_flat118_step : block008_data_flat118 = (CoefficientMerge.scale (17241316485120 : Int) atom0556Coded) := by decide +kernel
theorem block008_data_flat118_original : block008_data_flat118 = (CoefficientMerge.scale (17241316485120 : Int) atom0556Coded) := by
  rw [block008_data_flat118_step]
def block008_data_flat119 : CoefficientMerge.Poly := [(nat_lit 794, Int.ofNat (nat_lit 44781522508800))]
theorem block008_data_flat119_step : block008_data_flat119 = (CoefficientMerge.scale (44781522508800 : Int) atom0557Coded) := by decide +kernel
theorem block008_data_flat119_original : block008_data_flat119 = (CoefficientMerge.scale (44781522508800 : Int) atom0557Coded) := by
  rw [block008_data_flat119_step]
def block008_data_flat120 : CoefficientMerge.Poly := [(nat_lit 793, Int.ofNat (nat_lit 17241316485120)), (nat_lit 794, Int.ofNat (nat_lit 44781522508800))]
theorem block008_data_flat120_step : block008_data_flat120 = (CoefficientMerge.fastMerge block008_data_flat118 block008_data_flat119) := by decide +kernel
theorem block008_data_flat120_original : block008_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17241316485120 : Int) atom0556Coded) (CoefficientMerge.scale (44781522508800 : Int) atom0557Coded)) := by
  rw [block008_data_flat120_step, block008_data_flat118_original, block008_data_flat119_original]
def block008_data_flat121 : CoefficientMerge.Poly := [(nat_lit 795, Int.ofNat (nat_lit 48663717580800))]
theorem block008_data_flat121_step : block008_data_flat121 = (CoefficientMerge.scale (48663717580800 : Int) atom0558Coded) := by decide +kernel
theorem block008_data_flat121_original : block008_data_flat121 = (CoefficientMerge.scale (48663717580800 : Int) atom0558Coded) := by
  rw [block008_data_flat121_step]
def block008_data_flat122 : CoefficientMerge.Poly := [(nat_lit 796, Int.ofNat (nat_lit 34016536512000))]
theorem block008_data_flat122_step : block008_data_flat122 = (CoefficientMerge.scale (34016536512000 : Int) atom0559Coded) := by decide +kernel
theorem block008_data_flat122_original : block008_data_flat122 = (CoefficientMerge.scale (34016536512000 : Int) atom0559Coded) := by
  rw [block008_data_flat122_step]
def block008_data_flat123 : CoefficientMerge.Poly := [(nat_lit 797, Int.ofNat (nat_lit 35468416670400))]
theorem block008_data_flat123_step : block008_data_flat123 = (CoefficientMerge.scale (35468416670400 : Int) atom0560Coded) := by decide +kernel
theorem block008_data_flat123_original : block008_data_flat123 = (CoefficientMerge.scale (35468416670400 : Int) atom0560Coded) := by
  rw [block008_data_flat123_step]
def block008_data_flat124 : CoefficientMerge.Poly := [(nat_lit 796, Int.ofNat (nat_lit 34016536512000)), (nat_lit 797, Int.ofNat (nat_lit 35468416670400))]
theorem block008_data_flat124_step : block008_data_flat124 = (CoefficientMerge.fastMerge block008_data_flat122 block008_data_flat123) := by decide +kernel
theorem block008_data_flat124_original : block008_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34016536512000 : Int) atom0559Coded) (CoefficientMerge.scale (35468416670400 : Int) atom0560Coded)) := by
  rw [block008_data_flat124_step, block008_data_flat122_original, block008_data_flat123_original]
def block008_data_flat125 : CoefficientMerge.Poly := [(nat_lit 795, Int.ofNat (nat_lit 48663717580800)), (nat_lit 796, Int.ofNat (nat_lit 34016536512000)), (nat_lit 797, Int.ofNat (nat_lit 35468416670400))]
theorem block008_data_flat125_step : block008_data_flat125 = (CoefficientMerge.fastMerge block008_data_flat121 block008_data_flat124) := by decide +kernel
theorem block008_data_flat125_original : block008_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48663717580800 : Int) atom0558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34016536512000 : Int) atom0559Coded) (CoefficientMerge.scale (35468416670400 : Int) atom0560Coded))) := by
  rw [block008_data_flat125_step, block008_data_flat121_original, block008_data_flat124_original]
def block008_data_flat126 : CoefficientMerge.Poly := [(nat_lit 793, Int.ofNat (nat_lit 17241316485120)), (nat_lit 794, Int.ofNat (nat_lit 44781522508800)), (nat_lit 795, Int.ofNat (nat_lit 48663717580800)), (nat_lit 796, Int.ofNat (nat_lit 34016536512000)), (nat_lit 797, Int.ofNat (nat_lit 35468416670400))]
theorem block008_data_flat126_step : block008_data_flat126 = (CoefficientMerge.fastMerge block008_data_flat120 block008_data_flat125) := by decide +kernel
theorem block008_data_flat126_original : block008_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17241316485120 : Int) atom0556Coded) (CoefficientMerge.scale (44781522508800 : Int) atom0557Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48663717580800 : Int) atom0558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34016536512000 : Int) atom0559Coded) (CoefficientMerge.scale (35468416670400 : Int) atom0560Coded)))) := by
  rw [block008_data_flat126_step, block008_data_flat120_original, block008_data_flat125_original]
def block008_data_flat127 : CoefficientMerge.Poly := [(nat_lit 815, Int.ofNat (nat_lit 32332095129600))]
theorem block008_data_flat127_step : block008_data_flat127 = (CoefficientMerge.scale (32332095129600 : Int) atom0561Coded) := by decide +kernel
theorem block008_data_flat127_original : block008_data_flat127 = (CoefficientMerge.scale (32332095129600 : Int) atom0561Coded) := by
  rw [block008_data_flat127_step]
def block008_data_flat128 : CoefficientMerge.Poly := [(nat_lit 816, Int.ofNat (nat_lit 52531326489600))]
theorem block008_data_flat128_step : block008_data_flat128 = (CoefficientMerge.scale (52531326489600 : Int) atom0562Coded) := by decide +kernel
theorem block008_data_flat128_original : block008_data_flat128 = (CoefficientMerge.scale (52531326489600 : Int) atom0562Coded) := by
  rw [block008_data_flat128_step]
def block008_data_flat129 : CoefficientMerge.Poly := [(nat_lit 815, Int.ofNat (nat_lit 32332095129600)), (nat_lit 816, Int.ofNat (nat_lit 52531326489600))]
theorem block008_data_flat129_step : block008_data_flat129 = (CoefficientMerge.fastMerge block008_data_flat127 block008_data_flat128) := by decide +kernel
theorem block008_data_flat129_original : block008_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (32332095129600 : Int) atom0561Coded) (CoefficientMerge.scale (52531326489600 : Int) atom0562Coded)) := by
  rw [block008_data_flat129_step, block008_data_flat127_original, block008_data_flat128_original]
def block008_data_flat130 : CoefficientMerge.Poly := [(nat_lit 817, Int.ofNat (nat_lit 38858347584000))]
theorem block008_data_flat130_step : block008_data_flat130 = (CoefficientMerge.scale (38858347584000 : Int) atom0563Coded) := by decide +kernel
theorem block008_data_flat130_original : block008_data_flat130 = (CoefficientMerge.scale (38858347584000 : Int) atom0563Coded) := by
  rw [block008_data_flat130_step]
def block008_data_flat131 : CoefficientMerge.Poly := [(nat_lit 818, Int.ofNat (nat_lit 43189020907200))]
theorem block008_data_flat131_step : block008_data_flat131 = (CoefficientMerge.scale (43189020907200 : Int) atom0564Coded) := by decide +kernel
theorem block008_data_flat131_original : block008_data_flat131 = (CoefficientMerge.scale (43189020907200 : Int) atom0564Coded) := by
  rw [block008_data_flat131_step]
def block008_data_flat132 : CoefficientMerge.Poly := [(nat_lit 837, Int.ofNat (nat_lit 19281084480000))]
theorem block008_data_flat132_step : block008_data_flat132 = (CoefficientMerge.scale (19281084480000 : Int) atom0565Coded) := by decide +kernel
theorem block008_data_flat132_original : block008_data_flat132 = (CoefficientMerge.scale (19281084480000 : Int) atom0565Coded) := by
  rw [block008_data_flat132_step]
def block008_data_flat133 : CoefficientMerge.Poly := [(nat_lit 818, Int.ofNat (nat_lit 43189020907200)), (nat_lit 837, Int.ofNat (nat_lit 19281084480000))]
theorem block008_data_flat133_step : block008_data_flat133 = (CoefficientMerge.fastMerge block008_data_flat131 block008_data_flat132) := by decide +kernel
theorem block008_data_flat133_original : block008_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (43189020907200 : Int) atom0564Coded) (CoefficientMerge.scale (19281084480000 : Int) atom0565Coded)) := by
  rw [block008_data_flat133_step, block008_data_flat131_original, block008_data_flat132_original]
def block008_data_flat134 : CoefficientMerge.Poly := [(nat_lit 817, Int.ofNat (nat_lit 38858347584000)), (nat_lit 818, Int.ofNat (nat_lit 43189020907200)), (nat_lit 837, Int.ofNat (nat_lit 19281084480000))]
theorem block008_data_flat134_step : block008_data_flat134 = (CoefficientMerge.fastMerge block008_data_flat130 block008_data_flat133) := by decide +kernel
theorem block008_data_flat134_original : block008_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (38858347584000 : Int) atom0563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43189020907200 : Int) atom0564Coded) (CoefficientMerge.scale (19281084480000 : Int) atom0565Coded))) := by
  rw [block008_data_flat134_step, block008_data_flat130_original, block008_data_flat133_original]
def block008_data_flat135 : CoefficientMerge.Poly := [(nat_lit 815, Int.ofNat (nat_lit 32332095129600)), (nat_lit 816, Int.ofNat (nat_lit 52531326489600)), (nat_lit 817, Int.ofNat (nat_lit 38858347584000)), (nat_lit 818, Int.ofNat (nat_lit 43189020907200)), (nat_lit 837, Int.ofNat (nat_lit 19281084480000))]
theorem block008_data_flat135_step : block008_data_flat135 = (CoefficientMerge.fastMerge block008_data_flat129 block008_data_flat134) := by decide +kernel
theorem block008_data_flat135_original : block008_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32332095129600 : Int) atom0561Coded) (CoefficientMerge.scale (52531326489600 : Int) atom0562Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38858347584000 : Int) atom0563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43189020907200 : Int) atom0564Coded) (CoefficientMerge.scale (19281084480000 : Int) atom0565Coded)))) := by
  rw [block008_data_flat135_step, block008_data_flat129_original, block008_data_flat134_original]
def block008_data_flat136 : CoefficientMerge.Poly := [(nat_lit 793, Int.ofNat (nat_lit 17241316485120)), (nat_lit 794, Int.ofNat (nat_lit 44781522508800)), (nat_lit 795, Int.ofNat (nat_lit 48663717580800)), (nat_lit 796, Int.ofNat (nat_lit 34016536512000)), (nat_lit 797, Int.ofNat (nat_lit 35468416670400)), (nat_lit 815, Int.ofNat (nat_lit 32332095129600)), (nat_lit 816, Int.ofNat (nat_lit 52531326489600)), (nat_lit 817, Int.ofNat (nat_lit 38858347584000)), (nat_lit 818, Int.ofNat (nat_lit 43189020907200)), (nat_lit 837, Int.ofNat (nat_lit 19281084480000))]
theorem block008_data_flat136_step : block008_data_flat136 = (CoefficientMerge.fastMerge block008_data_flat126 block008_data_flat135) := by decide +kernel
theorem block008_data_flat136_original : block008_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17241316485120 : Int) atom0556Coded) (CoefficientMerge.scale (44781522508800 : Int) atom0557Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48663717580800 : Int) atom0558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34016536512000 : Int) atom0559Coded) (CoefficientMerge.scale (35468416670400 : Int) atom0560Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32332095129600 : Int) atom0561Coded) (CoefficientMerge.scale (52531326489600 : Int) atom0562Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38858347584000 : Int) atom0563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43189020907200 : Int) atom0564Coded) (CoefficientMerge.scale (19281084480000 : Int) atom0565Coded))))) := by
  rw [block008_data_flat136_step, block008_data_flat126_original, block008_data_flat135_original]
def block008_data_flat137 : CoefficientMerge.Poly := [(nat_lit 838, Int.ofNat (nat_lit 24781267526400))]
theorem block008_data_flat137_step : block008_data_flat137 = (CoefficientMerge.scale (24781267526400 : Int) atom0566Coded) := by decide +kernel
theorem block008_data_flat137_original : block008_data_flat137 = (CoefficientMerge.scale (24781267526400 : Int) atom0566Coded) := by
  rw [block008_data_flat137_step]
def block008_data_flat138 : CoefficientMerge.Poly := [(nat_lit 839, Int.ofNat (nat_lit 28558072771200))]
theorem block008_data_flat138_step : block008_data_flat138 = (CoefficientMerge.scale (28558072771200 : Int) atom0567Coded) := by decide +kernel
theorem block008_data_flat138_original : block008_data_flat138 = (CoefficientMerge.scale (28558072771200 : Int) atom0567Coded) := by
  rw [block008_data_flat138_step]
def block008_data_flat139 : CoefficientMerge.Poly := [(nat_lit 838, Int.ofNat (nat_lit 24781267526400)), (nat_lit 839, Int.ofNat (nat_lit 28558072771200))]
theorem block008_data_flat139_step : block008_data_flat139 = (CoefficientMerge.fastMerge block008_data_flat137 block008_data_flat138) := by decide +kernel
theorem block008_data_flat139_original : block008_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24781267526400 : Int) atom0566Coded) (CoefficientMerge.scale (28558072771200 : Int) atom0567Coded)) := by
  rw [block008_data_flat139_step, block008_data_flat137_original, block008_data_flat138_original]
def block008_data_flat140 : CoefficientMerge.Poly := [(nat_lit 859, Int.ofNat (nat_lit 4012462944000))]
theorem block008_data_flat140_step : block008_data_flat140 = (CoefficientMerge.scale (4012462944000 : Int) atom0568Coded) := by decide +kernel
theorem block008_data_flat140_original : block008_data_flat140 = (CoefficientMerge.scale (4012462944000 : Int) atom0568Coded) := by
  rw [block008_data_flat140_step]
def block008_data_flat141 : CoefficientMerge.Poly := [(nat_lit 860, Int.ofNat (nat_lit 9601239110400))]
theorem block008_data_flat141_step : block008_data_flat141 = (CoefficientMerge.scale (9601239110400 : Int) atom0569Coded) := by decide +kernel
theorem block008_data_flat141_original : block008_data_flat141 = (CoefficientMerge.scale (9601239110400 : Int) atom0569Coded) := by
  rw [block008_data_flat141_step]
def block008_data_flat142 : CoefficientMerge.Poly := [(nat_lit 881, Int.ofNat (nat_lit 3467695795200))]
theorem block008_data_flat142_step : block008_data_flat142 = (CoefficientMerge.scale (3467695795200 : Int) atom0570Coded) := by decide +kernel
theorem block008_data_flat142_original : block008_data_flat142 = (CoefficientMerge.scale (3467695795200 : Int) atom0570Coded) := by
  rw [block008_data_flat142_step]
def block008_data_flat143 : CoefficientMerge.Poly := [(nat_lit 860, Int.ofNat (nat_lit 9601239110400)), (nat_lit 881, Int.ofNat (nat_lit 3467695795200))]
theorem block008_data_flat143_step : block008_data_flat143 = (CoefficientMerge.fastMerge block008_data_flat141 block008_data_flat142) := by decide +kernel
theorem block008_data_flat143_original : block008_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9601239110400 : Int) atom0569Coded) (CoefficientMerge.scale (3467695795200 : Int) atom0570Coded)) := by
  rw [block008_data_flat143_step, block008_data_flat141_original, block008_data_flat142_original]
def block008_data_flat144 : CoefficientMerge.Poly := [(nat_lit 859, Int.ofNat (nat_lit 4012462944000)), (nat_lit 860, Int.ofNat (nat_lit 9601239110400)), (nat_lit 881, Int.ofNat (nat_lit 3467695795200))]
theorem block008_data_flat144_step : block008_data_flat144 = (CoefficientMerge.fastMerge block008_data_flat140 block008_data_flat143) := by decide +kernel
theorem block008_data_flat144_original : block008_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4012462944000 : Int) atom0568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9601239110400 : Int) atom0569Coded) (CoefficientMerge.scale (3467695795200 : Int) atom0570Coded))) := by
  rw [block008_data_flat144_step, block008_data_flat140_original, block008_data_flat143_original]
def block008_data_flat145 : CoefficientMerge.Poly := [(nat_lit 838, Int.ofNat (nat_lit 24781267526400)), (nat_lit 839, Int.ofNat (nat_lit 28558072771200)), (nat_lit 859, Int.ofNat (nat_lit 4012462944000)), (nat_lit 860, Int.ofNat (nat_lit 9601239110400)), (nat_lit 881, Int.ofNat (nat_lit 3467695795200))]
theorem block008_data_flat145_step : block008_data_flat145 = (CoefficientMerge.fastMerge block008_data_flat139 block008_data_flat144) := by decide +kernel
theorem block008_data_flat145_original : block008_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24781267526400 : Int) atom0566Coded) (CoefficientMerge.scale (28558072771200 : Int) atom0567Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4012462944000 : Int) atom0568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9601239110400 : Int) atom0569Coded) (CoefficientMerge.scale (3467695795200 : Int) atom0570Coded)))) := by
  rw [block008_data_flat145_step, block008_data_flat139_original, block008_data_flat144_original]
def block008_data_flat146 : CoefficientMerge.Poly := [(nat_lit 926, Int.ofNat (nat_lit 4679649676800))]
theorem block008_data_flat146_step : block008_data_flat146 = (CoefficientMerge.scale (4679649676800 : Int) atom0571Coded) := by decide +kernel
theorem block008_data_flat146_original : block008_data_flat146 = (CoefficientMerge.scale (4679649676800 : Int) atom0571Coded) := by
  rw [block008_data_flat146_step]
def block008_data_flat147 : CoefficientMerge.Poly := [(nat_lit 927, Int.ofNat (nat_lit 13261906828800))]
theorem block008_data_flat147_step : block008_data_flat147 = (CoefficientMerge.scale (13261906828800 : Int) atom0572Coded) := by decide +kernel
theorem block008_data_flat147_original : block008_data_flat147 = (CoefficientMerge.scale (13261906828800 : Int) atom0572Coded) := by
  rw [block008_data_flat147_step]
def block008_data_flat148 : CoefficientMerge.Poly := [(nat_lit 926, Int.ofNat (nat_lit 4679649676800)), (nat_lit 927, Int.ofNat (nat_lit 13261906828800))]
theorem block008_data_flat148_step : block008_data_flat148 = (CoefficientMerge.fastMerge block008_data_flat146 block008_data_flat147) := by decide +kernel
theorem block008_data_flat148_original : block008_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4679649676800 : Int) atom0571Coded) (CoefficientMerge.scale (13261906828800 : Int) atom0572Coded)) := by
  rw [block008_data_flat148_step, block008_data_flat146_original, block008_data_flat147_original]
def block008_data_flat149 : CoefficientMerge.Poly := [(nat_lit 928, Int.ofNat (nat_lit 12484864627200))]
theorem block008_data_flat149_step : block008_data_flat149 = (CoefficientMerge.scale (12484864627200 : Int) atom0573Coded) := by decide +kernel
theorem block008_data_flat149_original : block008_data_flat149 = (CoefficientMerge.scale (12484864627200 : Int) atom0573Coded) := by
  rw [block008_data_flat149_step]
def block008_data_flat150 : CoefficientMerge.Poly := [(nat_lit 929, Int.ofNat (nat_lit 13199200388352))]
theorem block008_data_flat150_step : block008_data_flat150 = (CoefficientMerge.scale (13199200388352 : Int) atom0574Coded) := by decide +kernel
theorem block008_data_flat150_original : block008_data_flat150 = (CoefficientMerge.scale (13199200388352 : Int) atom0574Coded) := by
  rw [block008_data_flat150_step]
def block008_data_flat151 : CoefficientMerge.Poly := [(nat_lit 930, Int.ofNat (nat_lit 12875483174400))]
theorem block008_data_flat151_step : block008_data_flat151 = (CoefficientMerge.scale (12875483174400 : Int) atom0575Coded) := by decide +kernel
theorem block008_data_flat151_original : block008_data_flat151 = (CoefficientMerge.scale (12875483174400 : Int) atom0575Coded) := by
  rw [block008_data_flat151_step]
def block008_data_flat152 : CoefficientMerge.Poly := [(nat_lit 929, Int.ofNat (nat_lit 13199200388352)), (nat_lit 930, Int.ofNat (nat_lit 12875483174400))]
theorem block008_data_flat152_step : block008_data_flat152 = (CoefficientMerge.fastMerge block008_data_flat150 block008_data_flat151) := by decide +kernel
theorem block008_data_flat152_original : block008_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13199200388352 : Int) atom0574Coded) (CoefficientMerge.scale (12875483174400 : Int) atom0575Coded)) := by
  rw [block008_data_flat152_step, block008_data_flat150_original, block008_data_flat151_original]
def block008_data_flat153 : CoefficientMerge.Poly := [(nat_lit 928, Int.ofNat (nat_lit 12484864627200)), (nat_lit 929, Int.ofNat (nat_lit 13199200388352)), (nat_lit 930, Int.ofNat (nat_lit 12875483174400))]
theorem block008_data_flat153_step : block008_data_flat153 = (CoefficientMerge.fastMerge block008_data_flat149 block008_data_flat152) := by decide +kernel
theorem block008_data_flat153_original : block008_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12484864627200 : Int) atom0573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13199200388352 : Int) atom0574Coded) (CoefficientMerge.scale (12875483174400 : Int) atom0575Coded))) := by
  rw [block008_data_flat153_step, block008_data_flat149_original, block008_data_flat152_original]
def block008_data_flat154 : CoefficientMerge.Poly := [(nat_lit 926, Int.ofNat (nat_lit 4679649676800)), (nat_lit 927, Int.ofNat (nat_lit 13261906828800)), (nat_lit 928, Int.ofNat (nat_lit 12484864627200)), (nat_lit 929, Int.ofNat (nat_lit 13199200388352)), (nat_lit 930, Int.ofNat (nat_lit 12875483174400))]
theorem block008_data_flat154_step : block008_data_flat154 = (CoefficientMerge.fastMerge block008_data_flat148 block008_data_flat153) := by decide +kernel
theorem block008_data_flat154_original : block008_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4679649676800 : Int) atom0571Coded) (CoefficientMerge.scale (13261906828800 : Int) atom0572Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12484864627200 : Int) atom0573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13199200388352 : Int) atom0574Coded) (CoefficientMerge.scale (12875483174400 : Int) atom0575Coded)))) := by
  rw [block008_data_flat154_step, block008_data_flat148_original, block008_data_flat153_original]
def block008_data_flat155 : CoefficientMerge.Poly := [(nat_lit 838, Int.ofNat (nat_lit 24781267526400)), (nat_lit 839, Int.ofNat (nat_lit 28558072771200)), (nat_lit 859, Int.ofNat (nat_lit 4012462944000)), (nat_lit 860, Int.ofNat (nat_lit 9601239110400)), (nat_lit 881, Int.ofNat (nat_lit 3467695795200)), (nat_lit 926, Int.ofNat (nat_lit 4679649676800)), (nat_lit 927, Int.ofNat (nat_lit 13261906828800)), (nat_lit 928, Int.ofNat (nat_lit 12484864627200)), (nat_lit 929, Int.ofNat (nat_lit 13199200388352)), (nat_lit 930, Int.ofNat (nat_lit 12875483174400))]
theorem block008_data_flat155_step : block008_data_flat155 = (CoefficientMerge.fastMerge block008_data_flat145 block008_data_flat154) := by decide +kernel
theorem block008_data_flat155_original : block008_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24781267526400 : Int) atom0566Coded) (CoefficientMerge.scale (28558072771200 : Int) atom0567Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4012462944000 : Int) atom0568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9601239110400 : Int) atom0569Coded) (CoefficientMerge.scale (3467695795200 : Int) atom0570Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4679649676800 : Int) atom0571Coded) (CoefficientMerge.scale (13261906828800 : Int) atom0572Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12484864627200 : Int) atom0573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13199200388352 : Int) atom0574Coded) (CoefficientMerge.scale (12875483174400 : Int) atom0575Coded))))) := by
  rw [block008_data_flat155_step, block008_data_flat145_original, block008_data_flat154_original]
def block008_data_flat156 : CoefficientMerge.Poly := [(nat_lit 793, Int.ofNat (nat_lit 17241316485120)), (nat_lit 794, Int.ofNat (nat_lit 44781522508800)), (nat_lit 795, Int.ofNat (nat_lit 48663717580800)), (nat_lit 796, Int.ofNat (nat_lit 34016536512000)), (nat_lit 797, Int.ofNat (nat_lit 35468416670400)), (nat_lit 815, Int.ofNat (nat_lit 32332095129600)), (nat_lit 816, Int.ofNat (nat_lit 52531326489600)), (nat_lit 817, Int.ofNat (nat_lit 38858347584000)), (nat_lit 818, Int.ofNat (nat_lit 43189020907200)), (nat_lit 837, Int.ofNat (nat_lit 19281084480000)), (nat_lit 838, Int.ofNat (nat_lit 24781267526400)), (nat_lit 839, Int.ofNat (nat_lit 28558072771200)), (nat_lit 859, Int.ofNat (nat_lit 4012462944000)), (nat_lit 860, Int.ofNat (nat_lit 9601239110400)), (nat_lit 881, Int.ofNat (nat_lit 3467695795200)), (nat_lit 926, Int.ofNat (nat_lit 4679649676800)), (nat_lit 927, Int.ofNat (nat_lit 13261906828800)), (nat_lit 928, Int.ofNat (nat_lit 12484864627200)), (nat_lit 929, Int.ofNat (nat_lit 13199200388352)), (nat_lit 930, Int.ofNat (nat_lit 12875483174400))]
theorem block008_data_flat156_step : block008_data_flat156 = (CoefficientMerge.fastMerge block008_data_flat136 block008_data_flat155) := by decide +kernel
theorem block008_data_flat156_original : block008_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17241316485120 : Int) atom0556Coded) (CoefficientMerge.scale (44781522508800 : Int) atom0557Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48663717580800 : Int) atom0558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34016536512000 : Int) atom0559Coded) (CoefficientMerge.scale (35468416670400 : Int) atom0560Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32332095129600 : Int) atom0561Coded) (CoefficientMerge.scale (52531326489600 : Int) atom0562Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38858347584000 : Int) atom0563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43189020907200 : Int) atom0564Coded) (CoefficientMerge.scale (19281084480000 : Int) atom0565Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24781267526400 : Int) atom0566Coded) (CoefficientMerge.scale (28558072771200 : Int) atom0567Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4012462944000 : Int) atom0568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9601239110400 : Int) atom0569Coded) (CoefficientMerge.scale (3467695795200 : Int) atom0570Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4679649676800 : Int) atom0571Coded) (CoefficientMerge.scale (13261906828800 : Int) atom0572Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12484864627200 : Int) atom0573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13199200388352 : Int) atom0574Coded) (CoefficientMerge.scale (12875483174400 : Int) atom0575Coded)))))) := by
  rw [block008_data_flat156_step, block008_data_flat136_original, block008_data_flat155_original]
def block008_data_flat157 : CoefficientMerge.Poly := [(nat_lit 728, Int.ofNat (nat_lit 39387741782400)), (nat_lit 729, Int.ofNat (nat_lit 42390720640800)), (nat_lit 730, Int.ofNat (nat_lit 36777587119200)), (nat_lit 731, Int.ofNat (nat_lit 45766897344000)), (nat_lit 732, Int.ofNat (nat_lit 41968010649600)), (nat_lit 733, Int.ofNat (nat_lit 35490237040800)), (nat_lit 734, Int.ofNat (nat_lit 38348256844800)), (nat_lit 749, Int.ofNat (nat_lit 23400181324800)), (nat_lit 750, Int.ofNat (nat_lit 44739847756800)), (nat_lit 751, Int.ofNat (nat_lit 38224548633600)), (nat_lit 752, Int.ofNat (nat_lit 49103153164800)), (nat_lit 753, Int.ofNat (nat_lit 45640598169600)), (nat_lit 754, Int.ofNat (nat_lit 35787754598400)), (nat_lit 755, Int.ofNat (nat_lit 41321119795200)), (nat_lit 771, Int.ofNat (nat_lit 28066300416000)), (nat_lit 772, Int.ofNat (nat_lit 46229500800000)), (nat_lit 773, Int.ofNat (nat_lit 61253619033600)), (nat_lit 774, Int.ofNat (nat_lit 57872247552000)), (nat_lit 775, Int.ofNat (nat_lit 36902417126400)), (nat_lit 776, Int.ofNat (nat_lit 42460507857600)), (nat_lit 793, Int.ofNat (nat_lit 17241316485120)), (nat_lit 794, Int.ofNat (nat_lit 44781522508800)), (nat_lit 795, Int.ofNat (nat_lit 48663717580800)), (nat_lit 796, Int.ofNat (nat_lit 34016536512000)), (nat_lit 797, Int.ofNat (nat_lit 35468416670400)), (nat_lit 815, Int.ofNat (nat_lit 32332095129600)), (nat_lit 816, Int.ofNat (nat_lit 52531326489600)), (nat_lit 817, Int.ofNat (nat_lit 38858347584000)), (nat_lit 818, Int.ofNat (nat_lit 43189020907200)), (nat_lit 837, Int.ofNat (nat_lit 19281084480000)), (nat_lit 838, Int.ofNat (nat_lit 24781267526400)), (nat_lit 839, Int.ofNat (nat_lit 28558072771200)), (nat_lit 859, Int.ofNat (nat_lit 4012462944000)), (nat_lit 860, Int.ofNat (nat_lit 9601239110400)), (nat_lit 881, Int.ofNat (nat_lit 3467695795200)), (nat_lit 926, Int.ofNat (nat_lit 4679649676800)), (nat_lit 927, Int.ofNat (nat_lit 13261906828800)), (nat_lit 928, Int.ofNat (nat_lit 12484864627200)), (nat_lit 929, Int.ofNat (nat_lit 13199200388352)), (nat_lit 930, Int.ofNat (nat_lit 12875483174400))]
theorem block008_data_flat157_step : block008_data_flat157 = (CoefficientMerge.fastMerge block008_data_flat117 block008_data_flat156) := by decide +kernel
theorem block008_data_flat157_original : block008_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39387741782400 : Int) atom0536Coded) (CoefficientMerge.scale (42390720640800 : Int) atom0537Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36777587119200 : Int) atom0538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45766897344000 : Int) atom0539Coded) (CoefficientMerge.scale (41968010649600 : Int) atom0540Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35490237040800 : Int) atom0541Coded) (CoefficientMerge.scale (38348256844800 : Int) atom0542Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23400181324800 : Int) atom0543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44739847756800 : Int) atom0544Coded) (CoefficientMerge.scale (38224548633600 : Int) atom0545Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49103153164800 : Int) atom0546Coded) (CoefficientMerge.scale (45640598169600 : Int) atom0547Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35787754598400 : Int) atom0548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41321119795200 : Int) atom0549Coded) (CoefficientMerge.scale (28066300416000 : Int) atom0550Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46229500800000 : Int) atom0551Coded) (CoefficientMerge.scale (61253619033600 : Int) atom0552Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57872247552000 : Int) atom0553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36902417126400 : Int) atom0554Coded) (CoefficientMerge.scale (42460507857600 : Int) atom0555Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17241316485120 : Int) atom0556Coded) (CoefficientMerge.scale (44781522508800 : Int) atom0557Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48663717580800 : Int) atom0558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34016536512000 : Int) atom0559Coded) (CoefficientMerge.scale (35468416670400 : Int) atom0560Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32332095129600 : Int) atom0561Coded) (CoefficientMerge.scale (52531326489600 : Int) atom0562Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38858347584000 : Int) atom0563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43189020907200 : Int) atom0564Coded) (CoefficientMerge.scale (19281084480000 : Int) atom0565Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24781267526400 : Int) atom0566Coded) (CoefficientMerge.scale (28558072771200 : Int) atom0567Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4012462944000 : Int) atom0568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9601239110400 : Int) atom0569Coded) (CoefficientMerge.scale (3467695795200 : Int) atom0570Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4679649676800 : Int) atom0571Coded) (CoefficientMerge.scale (13261906828800 : Int) atom0572Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12484864627200 : Int) atom0573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13199200388352 : Int) atom0574Coded) (CoefficientMerge.scale (12875483174400 : Int) atom0575Coded))))))) := by
  rw [block008_data_flat157_step, block008_data_flat117_original, block008_data_flat156_original]
def block008_data_flat158 : CoefficientMerge.Poly := [(nat_lit 642, Int.ofNat (nat_lit 30403816464000)), (nat_lit 643, Int.ofNat (nat_lit 29787423120000)), (nat_lit 644, Int.ofNat (nat_lit 30487147689600)), (nat_lit 645, Int.ofNat (nat_lit 39992545152000)), (nat_lit 646, Int.ofNat (nat_lit 34392272014800)), (nat_lit 647, Int.ofNat (nat_lit 41077582963200)), (nat_lit 648, Int.ofNat (nat_lit 39334036518000)), (nat_lit 649, Int.ofNat (nat_lit 35737719620400)), (nat_lit 650, Int.ofNat (nat_lit 36469257174000)), (nat_lit 661, Int.ofNat (nat_lit 22070559672000)), (nat_lit 662, Int.ofNat (nat_lit 39833095538880)), (nat_lit 663, Int.ofNat (nat_lit 33381177081280)), (nat_lit 664, Int.ofNat (nat_lit 32429753193600)), (nat_lit 665, Int.ofNat (nat_lit 32838570172800)), (nat_lit 666, Int.ofNat (nat_lit 42138109440000)), (nat_lit 667, Int.ofNat (nat_lit 36296339511600)), (nat_lit 668, Int.ofNat (nat_lit 43895810649600)), (nat_lit 669, Int.ofNat (nat_lit 40925209222800)), (nat_lit 670, Int.ofNat (nat_lit 36790085077200)), (nat_lit 671, Int.ofNat (nat_lit 37409995299600)), (nat_lit 683, Int.ofNat (nat_lit 23509942041600)), (nat_lit 684, Int.ofNat (nat_lit 39142615079680)), (nat_lit 685, Int.ofNat (nat_lit 34691663462400)), (nat_lit 686, Int.ofNat (nat_lit 34725489926400)), (nat_lit 687, Int.ofNat (nat_lit 43659826560000)), (nat_lit 688, Int.ofNat (nat_lit 37535436288000)), (nat_lit 689, Int.ofNat (nat_lit 46090191168000)), (nat_lit 690, Int.ofNat (nat_lit 41618641075200)), (nat_lit 691, Int.ofNat (nat_lit 37129480819200)), (nat_lit 692, Int.ofNat (nat_lit 37510611264000)), (nat_lit 705, Int.ofNat (nat_lit 21593669171200)), (nat_lit 706, Int.ofNat (nat_lit 37959288304000)), (nat_lit 707, Int.ofNat (nat_lit 34193114233600)), (nat_lit 708, Int.ofNat (nat_lit 41082437401600)), (nat_lit 709, Int.ofNat (nat_lit 36148462828800)), (nat_lit 710, Int.ofNat (nat_lit 44185465408000)), (nat_lit 711, Int.ofNat (nat_lit 40050247014400)), (nat_lit 712, Int.ofNat (nat_lit 36979376806400)), (nat_lit 713, Int.ofNat (nat_lit 37173350995200)), (nat_lit 727, Int.ofNat (nat_lit 21868118640000)), (nat_lit 728, Int.ofNat (nat_lit 39387741782400)), (nat_lit 729, Int.ofNat (nat_lit 42390720640800)), (nat_lit 730, Int.ofNat (nat_lit 36777587119200)), (nat_lit 731, Int.ofNat (nat_lit 45766897344000)), (nat_lit 732, Int.ofNat (nat_lit 41968010649600)), (nat_lit 733, Int.ofNat (nat_lit 35490237040800)), (nat_lit 734, Int.ofNat (nat_lit 38348256844800)), (nat_lit 749, Int.ofNat (nat_lit 23400181324800)), (nat_lit 750, Int.ofNat (nat_lit 44739847756800)), (nat_lit 751, Int.ofNat (nat_lit 38224548633600)), (nat_lit 752, Int.ofNat (nat_lit 49103153164800)), (nat_lit 753, Int.ofNat (nat_lit 45640598169600)), (nat_lit 754, Int.ofNat (nat_lit 35787754598400)), (nat_lit 755, Int.ofNat (nat_lit 41321119795200)), (nat_lit 771, Int.ofNat (nat_lit 28066300416000)), (nat_lit 772, Int.ofNat (nat_lit 46229500800000)), (nat_lit 773, Int.ofNat (nat_lit 61253619033600)), (nat_lit 774, Int.ofNat (nat_lit 57872247552000)), (nat_lit 775, Int.ofNat (nat_lit 36902417126400)), (nat_lit 776, Int.ofNat (nat_lit 42460507857600)), (nat_lit 793, Int.ofNat (nat_lit 17241316485120)), (nat_lit 794, Int.ofNat (nat_lit 44781522508800)), (nat_lit 795, Int.ofNat (nat_lit 48663717580800)), (nat_lit 796, Int.ofNat (nat_lit 34016536512000)), (nat_lit 797, Int.ofNat (nat_lit 35468416670400)), (nat_lit 815, Int.ofNat (nat_lit 32332095129600)), (nat_lit 816, Int.ofNat (nat_lit 52531326489600)), (nat_lit 817, Int.ofNat (nat_lit 38858347584000)), (nat_lit 818, Int.ofNat (nat_lit 43189020907200)), (nat_lit 837, Int.ofNat (nat_lit 19281084480000)), (nat_lit 838, Int.ofNat (nat_lit 24781267526400)), (nat_lit 839, Int.ofNat (nat_lit 28558072771200)), (nat_lit 859, Int.ofNat (nat_lit 4012462944000)), (nat_lit 860, Int.ofNat (nat_lit 9601239110400)), (nat_lit 881, Int.ofNat (nat_lit 3467695795200)), (nat_lit 926, Int.ofNat (nat_lit 4679649676800)), (nat_lit 927, Int.ofNat (nat_lit 13261906828800)), (nat_lit 928, Int.ofNat (nat_lit 12484864627200)), (nat_lit 929, Int.ofNat (nat_lit 13199200388352)), (nat_lit 930, Int.ofNat (nat_lit 12875483174400))]
theorem block008_data_flat158_step : block008_data_flat158 = (CoefficientMerge.fastMerge block008_data_flat078 block008_data_flat157) := by decide +kernel
theorem block008_data_flat158_original : block008_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30403816464000 : Int) atom0496Coded) (CoefficientMerge.scale (29787423120000 : Int) atom0497Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30487147689600 : Int) atom0498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39992545152000 : Int) atom0499Coded) (CoefficientMerge.scale (34392272014800 : Int) atom0500Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41077582963200 : Int) atom0501Coded) (CoefficientMerge.scale (39334036518000 : Int) atom0502Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35737719620400 : Int) atom0503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36469257174000 : Int) atom0504Coded) (CoefficientMerge.scale (22070559672000 : Int) atom0505Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39833095538880 : Int) atom0506Coded) (CoefficientMerge.scale (33381177081280 : Int) atom0507Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32429753193600 : Int) atom0508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32838570172800 : Int) atom0509Coded) (CoefficientMerge.scale (42138109440000 : Int) atom0510Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36296339511600 : Int) atom0511Coded) (CoefficientMerge.scale (43895810649600 : Int) atom0512Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40925209222800 : Int) atom0513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36790085077200 : Int) atom0514Coded) (CoefficientMerge.scale (37409995299600 : Int) atom0515Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23509942041600 : Int) atom0516Coded) (CoefficientMerge.scale (39142615079680 : Int) atom0517Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34691663462400 : Int) atom0518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34725489926400 : Int) atom0519Coded) (CoefficientMerge.scale (43659826560000 : Int) atom0520Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37535436288000 : Int) atom0521Coded) (CoefficientMerge.scale (46090191168000 : Int) atom0522Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41618641075200 : Int) atom0523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37129480819200 : Int) atom0524Coded) (CoefficientMerge.scale (37510611264000 : Int) atom0525Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21593669171200 : Int) atom0526Coded) (CoefficientMerge.scale (37959288304000 : Int) atom0527Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34193114233600 : Int) atom0528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41082437401600 : Int) atom0529Coded) (CoefficientMerge.scale (36148462828800 : Int) atom0530Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44185465408000 : Int) atom0531Coded) (CoefficientMerge.scale (40050247014400 : Int) atom0532Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36979376806400 : Int) atom0533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37173350995200 : Int) atom0534Coded) (CoefficientMerge.scale (21868118640000 : Int) atom0535Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39387741782400 : Int) atom0536Coded) (CoefficientMerge.scale (42390720640800 : Int) atom0537Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36777587119200 : Int) atom0538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45766897344000 : Int) atom0539Coded) (CoefficientMerge.scale (41968010649600 : Int) atom0540Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35490237040800 : Int) atom0541Coded) (CoefficientMerge.scale (38348256844800 : Int) atom0542Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23400181324800 : Int) atom0543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44739847756800 : Int) atom0544Coded) (CoefficientMerge.scale (38224548633600 : Int) atom0545Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49103153164800 : Int) atom0546Coded) (CoefficientMerge.scale (45640598169600 : Int) atom0547Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35787754598400 : Int) atom0548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41321119795200 : Int) atom0549Coded) (CoefficientMerge.scale (28066300416000 : Int) atom0550Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46229500800000 : Int) atom0551Coded) (CoefficientMerge.scale (61253619033600 : Int) atom0552Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57872247552000 : Int) atom0553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36902417126400 : Int) atom0554Coded) (CoefficientMerge.scale (42460507857600 : Int) atom0555Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17241316485120 : Int) atom0556Coded) (CoefficientMerge.scale (44781522508800 : Int) atom0557Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48663717580800 : Int) atom0558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34016536512000 : Int) atom0559Coded) (CoefficientMerge.scale (35468416670400 : Int) atom0560Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32332095129600 : Int) atom0561Coded) (CoefficientMerge.scale (52531326489600 : Int) atom0562Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38858347584000 : Int) atom0563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43189020907200 : Int) atom0564Coded) (CoefficientMerge.scale (19281084480000 : Int) atom0565Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24781267526400 : Int) atom0566Coded) (CoefficientMerge.scale (28558072771200 : Int) atom0567Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4012462944000 : Int) atom0568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9601239110400 : Int) atom0569Coded) (CoefficientMerge.scale (3467695795200 : Int) atom0570Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4679649676800 : Int) atom0571Coded) (CoefficientMerge.scale (13261906828800 : Int) atom0572Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12484864627200 : Int) atom0573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13199200388352 : Int) atom0574Coded) (CoefficientMerge.scale (12875483174400 : Int) atom0575Coded)))))))) := by
  rw [block008_data_flat158_step, block008_data_flat078_original, block008_data_flat157_original]
def block008_data_flat159 : CoefficientMerge.Poly := [(nat_lit 642, Int.ofNat (nat_lit 30403816464000)), (nat_lit 643, Int.ofNat (nat_lit 29787423120000)), (nat_lit 644, Int.ofNat (nat_lit 30487147689600)), (nat_lit 645, Int.ofNat (nat_lit 39992545152000)), (nat_lit 646, Int.ofNat (nat_lit 34392272014800)), (nat_lit 647, Int.ofNat (nat_lit 41077582963200)), (nat_lit 648, Int.ofNat (nat_lit 39334036518000)), (nat_lit 649, Int.ofNat (nat_lit 35737719620400)), (nat_lit 650, Int.ofNat (nat_lit 36469257174000)), (nat_lit 661, Int.ofNat (nat_lit 22070559672000)), (nat_lit 662, Int.ofNat (nat_lit 39833095538880)), (nat_lit 663, Int.ofNat (nat_lit 33381177081280)), (nat_lit 664, Int.ofNat (nat_lit 32429753193600)), (nat_lit 665, Int.ofNat (nat_lit 32838570172800)), (nat_lit 666, Int.ofNat (nat_lit 42138109440000)), (nat_lit 667, Int.ofNat (nat_lit 36296339511600)), (nat_lit 668, Int.ofNat (nat_lit 43895810649600)), (nat_lit 669, Int.ofNat (nat_lit 40925209222800)), (nat_lit 670, Int.ofNat (nat_lit 36790085077200)), (nat_lit 671, Int.ofNat (nat_lit 37409995299600)), (nat_lit 683, Int.ofNat (nat_lit 23509942041600)), (nat_lit 684, Int.ofNat (nat_lit 39142615079680)), (nat_lit 685, Int.ofNat (nat_lit 34691663462400)), (nat_lit 686, Int.ofNat (nat_lit 34725489926400)), (nat_lit 687, Int.ofNat (nat_lit 43659826560000)), (nat_lit 688, Int.ofNat (nat_lit 37535436288000)), (nat_lit 689, Int.ofNat (nat_lit 46090191168000)), (nat_lit 690, Int.ofNat (nat_lit 41618641075200)), (nat_lit 691, Int.ofNat (nat_lit 37129480819200)), (nat_lit 692, Int.ofNat (nat_lit 37510611264000)), (nat_lit 705, Int.ofNat (nat_lit 21593669171200)), (nat_lit 706, Int.ofNat (nat_lit 37959288304000)), (nat_lit 707, Int.ofNat (nat_lit 34193114233600)), (nat_lit 708, Int.ofNat (nat_lit 41082437401600)), (nat_lit 709, Int.ofNat (nat_lit 36148462828800)), (nat_lit 710, Int.ofNat (nat_lit 44185465408000)), (nat_lit 711, Int.ofNat (nat_lit 40050247014400)), (nat_lit 712, Int.ofNat (nat_lit 36979376806400)), (nat_lit 713, Int.ofNat (nat_lit 37173350995200)), (nat_lit 727, Int.ofNat (nat_lit 21868118640000)), (nat_lit 728, Int.ofNat (nat_lit 39387741782400)), (nat_lit 729, Int.ofNat (nat_lit 42390720640800)), (nat_lit 730, Int.ofNat (nat_lit 36777587119200)), (nat_lit 731, Int.ofNat (nat_lit 45766897344000)), (nat_lit 732, Int.ofNat (nat_lit 41968010649600)), (nat_lit 733, Int.ofNat (nat_lit 35490237040800)), (nat_lit 734, Int.ofNat (nat_lit 38348256844800)), (nat_lit 749, Int.ofNat (nat_lit 23400181324800)), (nat_lit 750, Int.ofNat (nat_lit 44739847756800)), (nat_lit 751, Int.ofNat (nat_lit 38224548633600)), (nat_lit 752, Int.ofNat (nat_lit 49103153164800)), (nat_lit 753, Int.ofNat (nat_lit 45640598169600)), (nat_lit 754, Int.ofNat (nat_lit 35787754598400)), (nat_lit 755, Int.ofNat (nat_lit 41321119795200)), (nat_lit 771, Int.ofNat (nat_lit 28066300416000)), (nat_lit 772, Int.ofNat (nat_lit 46229500800000)), (nat_lit 773, Int.ofNat (nat_lit 61253619033600)), (nat_lit 774, Int.ofNat (nat_lit 57872247552000)), (nat_lit 775, Int.ofNat (nat_lit 36902417126400)), (nat_lit 776, Int.ofNat (nat_lit 42460507857600)), (nat_lit 793, Int.ofNat (nat_lit 17241316485120)), (nat_lit 794, Int.ofNat (nat_lit 44781522508800)), (nat_lit 795, Int.ofNat (nat_lit 48663717580800)), (nat_lit 796, Int.ofNat (nat_lit 34016536512000)), (nat_lit 797, Int.ofNat (nat_lit 35468416670400)), (nat_lit 815, Int.ofNat (nat_lit 32332095129600)), (nat_lit 816, Int.ofNat (nat_lit 52531326489600)), (nat_lit 817, Int.ofNat (nat_lit 38858347584000)), (nat_lit 818, Int.ofNat (nat_lit 43189020907200)), (nat_lit 837, Int.ofNat (nat_lit 19281084480000)), (nat_lit 838, Int.ofNat (nat_lit 24781267526400)), (nat_lit 839, Int.ofNat (nat_lit 28558072771200)), (nat_lit 859, Int.ofNat (nat_lit 4012462944000)), (nat_lit 860, Int.ofNat (nat_lit 9601239110400)), (nat_lit 881, Int.ofNat (nat_lit 3467695795200)), (nat_lit 926, Int.ofNat (nat_lit 4679649676800)), (nat_lit 927, Int.ofNat (nat_lit 13261906828800)), (nat_lit 928, Int.ofNat (nat_lit 12484864627200)), (nat_lit 929, Int.ofNat (nat_lit 13199200388352)), (nat_lit 930, Int.ofNat (nat_lit 12875483174400))]
theorem block008_data_flat159_step : block008_data_flat159 = (CoefficientMerge.trim block008_data_flat158) := by decide +kernel
theorem block008_data_flat159_original : block008_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30403816464000 : Int) atom0496Coded) (CoefficientMerge.scale (29787423120000 : Int) atom0497Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30487147689600 : Int) atom0498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39992545152000 : Int) atom0499Coded) (CoefficientMerge.scale (34392272014800 : Int) atom0500Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41077582963200 : Int) atom0501Coded) (CoefficientMerge.scale (39334036518000 : Int) atom0502Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35737719620400 : Int) atom0503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36469257174000 : Int) atom0504Coded) (CoefficientMerge.scale (22070559672000 : Int) atom0505Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39833095538880 : Int) atom0506Coded) (CoefficientMerge.scale (33381177081280 : Int) atom0507Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32429753193600 : Int) atom0508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32838570172800 : Int) atom0509Coded) (CoefficientMerge.scale (42138109440000 : Int) atom0510Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36296339511600 : Int) atom0511Coded) (CoefficientMerge.scale (43895810649600 : Int) atom0512Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40925209222800 : Int) atom0513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36790085077200 : Int) atom0514Coded) (CoefficientMerge.scale (37409995299600 : Int) atom0515Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23509942041600 : Int) atom0516Coded) (CoefficientMerge.scale (39142615079680 : Int) atom0517Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34691663462400 : Int) atom0518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34725489926400 : Int) atom0519Coded) (CoefficientMerge.scale (43659826560000 : Int) atom0520Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37535436288000 : Int) atom0521Coded) (CoefficientMerge.scale (46090191168000 : Int) atom0522Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41618641075200 : Int) atom0523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37129480819200 : Int) atom0524Coded) (CoefficientMerge.scale (37510611264000 : Int) atom0525Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21593669171200 : Int) atom0526Coded) (CoefficientMerge.scale (37959288304000 : Int) atom0527Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34193114233600 : Int) atom0528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41082437401600 : Int) atom0529Coded) (CoefficientMerge.scale (36148462828800 : Int) atom0530Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44185465408000 : Int) atom0531Coded) (CoefficientMerge.scale (40050247014400 : Int) atom0532Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36979376806400 : Int) atom0533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37173350995200 : Int) atom0534Coded) (CoefficientMerge.scale (21868118640000 : Int) atom0535Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39387741782400 : Int) atom0536Coded) (CoefficientMerge.scale (42390720640800 : Int) atom0537Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36777587119200 : Int) atom0538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45766897344000 : Int) atom0539Coded) (CoefficientMerge.scale (41968010649600 : Int) atom0540Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35490237040800 : Int) atom0541Coded) (CoefficientMerge.scale (38348256844800 : Int) atom0542Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23400181324800 : Int) atom0543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44739847756800 : Int) atom0544Coded) (CoefficientMerge.scale (38224548633600 : Int) atom0545Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49103153164800 : Int) atom0546Coded) (CoefficientMerge.scale (45640598169600 : Int) atom0547Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35787754598400 : Int) atom0548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41321119795200 : Int) atom0549Coded) (CoefficientMerge.scale (28066300416000 : Int) atom0550Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46229500800000 : Int) atom0551Coded) (CoefficientMerge.scale (61253619033600 : Int) atom0552Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57872247552000 : Int) atom0553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36902417126400 : Int) atom0554Coded) (CoefficientMerge.scale (42460507857600 : Int) atom0555Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17241316485120 : Int) atom0556Coded) (CoefficientMerge.scale (44781522508800 : Int) atom0557Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48663717580800 : Int) atom0558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34016536512000 : Int) atom0559Coded) (CoefficientMerge.scale (35468416670400 : Int) atom0560Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32332095129600 : Int) atom0561Coded) (CoefficientMerge.scale (52531326489600 : Int) atom0562Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38858347584000 : Int) atom0563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43189020907200 : Int) atom0564Coded) (CoefficientMerge.scale (19281084480000 : Int) atom0565Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24781267526400 : Int) atom0566Coded) (CoefficientMerge.scale (28558072771200 : Int) atom0567Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4012462944000 : Int) atom0568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9601239110400 : Int) atom0569Coded) (CoefficientMerge.scale (3467695795200 : Int) atom0570Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4679649676800 : Int) atom0571Coded) (CoefficientMerge.scale (13261906828800 : Int) atom0572Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12484864627200 : Int) atom0573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13199200388352 : Int) atom0574Coded) (CoefficientMerge.scale (12875483174400 : Int) atom0575Coded))))))))) := by
  rw [block008_data_flat159_step, block008_data_flat158_original]
theorem block008_data : block008 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30403816464000 : Int) atom0496Coded) (CoefficientMerge.scale (29787423120000 : Int) atom0497Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30487147689600 : Int) atom0498Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39992545152000 : Int) atom0499Coded) (CoefficientMerge.scale (34392272014800 : Int) atom0500Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (41077582963200 : Int) atom0501Coded) (CoefficientMerge.scale (39334036518000 : Int) atom0502Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35737719620400 : Int) atom0503Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36469257174000 : Int) atom0504Coded) (CoefficientMerge.scale (22070559672000 : Int) atom0505Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39833095538880 : Int) atom0506Coded) (CoefficientMerge.scale (33381177081280 : Int) atom0507Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32429753193600 : Int) atom0508Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32838570172800 : Int) atom0509Coded) (CoefficientMerge.scale (42138109440000 : Int) atom0510Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36296339511600 : Int) atom0511Coded) (CoefficientMerge.scale (43895810649600 : Int) atom0512Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40925209222800 : Int) atom0513Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36790085077200 : Int) atom0514Coded) (CoefficientMerge.scale (37409995299600 : Int) atom0515Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (23509942041600 : Int) atom0516Coded) (CoefficientMerge.scale (39142615079680 : Int) atom0517Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34691663462400 : Int) atom0518Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34725489926400 : Int) atom0519Coded) (CoefficientMerge.scale (43659826560000 : Int) atom0520Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (37535436288000 : Int) atom0521Coded) (CoefficientMerge.scale (46090191168000 : Int) atom0522Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41618641075200 : Int) atom0523Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37129480819200 : Int) atom0524Coded) (CoefficientMerge.scale (37510611264000 : Int) atom0525Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21593669171200 : Int) atom0526Coded) (CoefficientMerge.scale (37959288304000 : Int) atom0527Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34193114233600 : Int) atom0528Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41082437401600 : Int) atom0529Coded) (CoefficientMerge.scale (36148462828800 : Int) atom0530Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44185465408000 : Int) atom0531Coded) (CoefficientMerge.scale (40050247014400 : Int) atom0532Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36979376806400 : Int) atom0533Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (37173350995200 : Int) atom0534Coded) (CoefficientMerge.scale (21868118640000 : Int) atom0535Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39387741782400 : Int) atom0536Coded) (CoefficientMerge.scale (42390720640800 : Int) atom0537Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36777587119200 : Int) atom0538Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45766897344000 : Int) atom0539Coded) (CoefficientMerge.scale (41968010649600 : Int) atom0540Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35490237040800 : Int) atom0541Coded) (CoefficientMerge.scale (38348256844800 : Int) atom0542Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23400181324800 : Int) atom0543Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (44739847756800 : Int) atom0544Coded) (CoefficientMerge.scale (38224548633600 : Int) atom0545Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49103153164800 : Int) atom0546Coded) (CoefficientMerge.scale (45640598169600 : Int) atom0547Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35787754598400 : Int) atom0548Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (41321119795200 : Int) atom0549Coded) (CoefficientMerge.scale (28066300416000 : Int) atom0550Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (46229500800000 : Int) atom0551Coded) (CoefficientMerge.scale (61253619033600 : Int) atom0552Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57872247552000 : Int) atom0553Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36902417126400 : Int) atom0554Coded) (CoefficientMerge.scale (42460507857600 : Int) atom0555Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17241316485120 : Int) atom0556Coded) (CoefficientMerge.scale (44781522508800 : Int) atom0557Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48663717580800 : Int) atom0558Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34016536512000 : Int) atom0559Coded) (CoefficientMerge.scale (35468416670400 : Int) atom0560Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32332095129600 : Int) atom0561Coded) (CoefficientMerge.scale (52531326489600 : Int) atom0562Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38858347584000 : Int) atom0563Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43189020907200 : Int) atom0564Coded) (CoefficientMerge.scale (19281084480000 : Int) atom0565Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24781267526400 : Int) atom0566Coded) (CoefficientMerge.scale (28558072771200 : Int) atom0567Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4012462944000 : Int) atom0568Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9601239110400 : Int) atom0569Coded) (CoefficientMerge.scale (3467695795200 : Int) atom0570Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4679649676800 : Int) atom0571Coded) (CoefficientMerge.scale (13261906828800 : Int) atom0572Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12484864627200 : Int) atom0573Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13199200388352 : Int) atom0574Coded) (CoefficientMerge.scale (12875483174400 : Int) atom0575Coded)))))))) := by
  have h : block008 = block008_data_flat159 := by decide +kernel
  exact h.trans block008_data_flat159_original
theorem block008_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block008 := by
  rw [block008_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0496Coded_nonneg g hg hA hB) (atom0497Coded_nonneg g hg hA hB)) (add_nonneg (atom0498Coded_nonneg g hg hA hB) (add_nonneg (atom0499Coded_nonneg g hg hA hB) (atom0500Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0501Coded_nonneg g hg hA hB) (atom0502Coded_nonneg g hg hA hB)) (add_nonneg (atom0503Coded_nonneg g hg hA hB) (add_nonneg (atom0504Coded_nonneg g hg hA hB) (atom0505Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0506Coded_nonneg g hg hA hB) (atom0507Coded_nonneg g hg hA hB)) (add_nonneg (atom0508Coded_nonneg g hg hA hB) (add_nonneg (atom0509Coded_nonneg g hg hA hB) (atom0510Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0511Coded_nonneg g hg hA hB) (atom0512Coded_nonneg g hg hA hB)) (add_nonneg (atom0513Coded_nonneg g hg hA hB) (add_nonneg (atom0514Coded_nonneg g hg hA hB) (atom0515Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0516Coded_nonneg g hg hA hB) (atom0517Coded_nonneg g hg hA hB)) (add_nonneg (atom0518Coded_nonneg g hg hA hB) (add_nonneg (atom0519Coded_nonneg g hg hA hB) (atom0520Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0521Coded_nonneg g hg hA hB) (atom0522Coded_nonneg g hg hA hB)) (add_nonneg (atom0523Coded_nonneg g hg hA hB) (add_nonneg (atom0524Coded_nonneg g hg hA hB) (atom0525Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0526Coded_nonneg g hg hA hB) (atom0527Coded_nonneg g hg hA hB)) (add_nonneg (atom0528Coded_nonneg g hg hA hB) (add_nonneg (atom0529Coded_nonneg g hg hA hB) (atom0530Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0531Coded_nonneg g hg hA hB) (atom0532Coded_nonneg g hg hA hB)) (add_nonneg (atom0533Coded_nonneg g hg hA hB) (add_nonneg (atom0534Coded_nonneg g hg hA hB) (atom0535Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0536Coded_nonneg g hg hA hB) (atom0537Coded_nonneg g hg hA hB)) (add_nonneg (atom0538Coded_nonneg g hg hA hB) (add_nonneg (atom0539Coded_nonneg g hg hA hB) (atom0540Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0541Coded_nonneg g hg hA hB) (atom0542Coded_nonneg g hg hA hB)) (add_nonneg (atom0543Coded_nonneg g hg hA hB) (add_nonneg (atom0544Coded_nonneg g hg hA hB) (atom0545Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0546Coded_nonneg g hg hA hB) (atom0547Coded_nonneg g hg hA hB)) (add_nonneg (atom0548Coded_nonneg g hg hA hB) (add_nonneg (atom0549Coded_nonneg g hg hA hB) (atom0550Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0551Coded_nonneg g hg hA hB) (atom0552Coded_nonneg g hg hA hB)) (add_nonneg (atom0553Coded_nonneg g hg hA hB) (add_nonneg (atom0554Coded_nonneg g hg hA hB) (atom0555Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0556Coded_nonneg g hg hA hB) (atom0557Coded_nonneg g hg hA hB)) (add_nonneg (atom0558Coded_nonneg g hg hA hB) (add_nonneg (atom0559Coded_nonneg g hg hA hB) (atom0560Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0561Coded_nonneg g hg hA hB) (atom0562Coded_nonneg g hg hA hB)) (add_nonneg (atom0563Coded_nonneg g hg hA hB) (add_nonneg (atom0564Coded_nonneg g hg hA hB) (atom0565Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0566Coded_nonneg g hg hA hB) (atom0567Coded_nonneg g hg hA hB)) (add_nonneg (atom0568Coded_nonneg g hg hA hB) (add_nonneg (atom0569Coded_nonneg g hg hA hB) (atom0570Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0571Coded_nonneg g hg hA hB) (atom0572Coded_nonneg g hg hA hB)) (add_nonneg (atom0573Coded_nonneg g hg hA hB) (add_nonneg (atom0574Coded_nonneg g hg hA hB) (atom0575Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
