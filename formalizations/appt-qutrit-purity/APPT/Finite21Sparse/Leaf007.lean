-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom0416 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0416 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0416 = ((g 1) * (g 3) * (g 19)) := by
  norm_num [atom0416, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0416_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14423604249600 : Int) atom0416) := by
  rw [SparsePolynomial.eval_scale, eval_atom0416]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 3) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0416Coded : CoefficientMerge.Poly := [(nat_lit 523, Int.ofNat (nat_lit 1))]
theorem atom0416Coded_decode : atom0416 = SparsePolynomial.decodeCubic 21 atom0416Coded := by decide +kernel
theorem atom0416Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14423604249600 : Int) atom0416Coded) := by
  have h := atom0416_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0416Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0417 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0417 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0417 = ((g 1) * (g 3) * (g 20)) := by
  norm_num [atom0417, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0417_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11360537395200 : Int) atom0417) := by
  rw [SparsePolynomial.eval_scale, eval_atom0417]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 3) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0417Coded : CoefficientMerge.Poly := [(nat_lit 524, Int.ofNat (nat_lit 1))]
theorem atom0417Coded_decode : atom0417 = SparsePolynomial.decodeCubic 21 atom0417Coded := by decide +kernel
theorem atom0417Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11360537395200 : Int) atom0417Coded) := by
  have h := atom0417_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0417Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0418 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0418 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0418 = ((g 1) * (g 4) * (g 4)) := by
  norm_num [atom0418, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0418_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7526146622400 : Int) atom0418) := by
  rw [SparsePolynomial.eval_scale, eval_atom0418]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0418Coded : CoefficientMerge.Poly := [(nat_lit 529, Int.ofNat (nat_lit 1))]
theorem atom0418Coded_decode : atom0418 = SparsePolynomial.decodeCubic 21 atom0418Coded := by decide +kernel
theorem atom0418Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7526146622400 : Int) atom0418Coded) := by
  have h := atom0418_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0418Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0419 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0419 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0419 = ((g 1) * (g 4) * (g 5)) := by
  norm_num [atom0419, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0419_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14464310141952 : Int) atom0419) := by
  rw [SparsePolynomial.eval_scale, eval_atom0419]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0419Coded : CoefficientMerge.Poly := [(nat_lit 530, Int.ofNat (nat_lit 1))]
theorem atom0419Coded_decode : atom0419 = SparsePolynomial.decodeCubic 21 atom0419Coded := by decide +kernel
theorem atom0419Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14464310141952 : Int) atom0419Coded) := by
  have h := atom0419_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0419Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0420 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0420 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0420 = ((g 1) * (g 4) * (g 6)) := by
  norm_num [atom0420, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0420_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14992217856000 : Int) atom0420) := by
  rw [SparsePolynomial.eval_scale, eval_atom0420]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0420Coded : CoefficientMerge.Poly := [(nat_lit 531, Int.ofNat (nat_lit 1))]
theorem atom0420Coded_decode : atom0420 = SparsePolynomial.decodeCubic 21 atom0420Coded := by decide +kernel
theorem atom0420Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14992217856000 : Int) atom0420Coded) := by
  have h := atom0420_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0420Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0421 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0421 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0421 = ((g 1) * (g 4) * (g 7)) := by
  norm_num [atom0421, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0421_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17536417636608 : Int) atom0421) := by
  rw [SparsePolynomial.eval_scale, eval_atom0421]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0421Coded : CoefficientMerge.Poly := [(nat_lit 532, Int.ofNat (nat_lit 1))]
theorem atom0421Coded_decode : atom0421 = SparsePolynomial.decodeCubic 21 atom0421Coded := by decide +kernel
theorem atom0421Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17536417636608 : Int) atom0421Coded) := by
  have h := atom0421_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0421Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0422 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0422 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0422 = ((g 1) * (g 4) * (g 8)) := by
  norm_num [atom0422, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0422_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18177375283200 : Int) atom0422) := by
  rw [SparsePolynomial.eval_scale, eval_atom0422]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0422Coded : CoefficientMerge.Poly := [(nat_lit 533, Int.ofNat (nat_lit 1))]
theorem atom0422Coded_decode : atom0422 = SparsePolynomial.decodeCubic 21 atom0422Coded := by decide +kernel
theorem atom0422Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18177375283200 : Int) atom0422Coded) := by
  have h := atom0422_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0422Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0423 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0423 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0423 = ((g 1) * (g 4) * (g 9)) := by
  norm_num [atom0423, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0423_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18668342246400 : Int) atom0423) := by
  rw [SparsePolynomial.eval_scale, eval_atom0423]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0423Coded : CoefficientMerge.Poly := [(nat_lit 534, Int.ofNat (nat_lit 1))]
theorem atom0423Coded_decode : atom0423 = SparsePolynomial.decodeCubic 21 atom0423Coded := by decide +kernel
theorem atom0423Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18668342246400 : Int) atom0423Coded) := by
  have h := atom0423_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0423Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0424 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0424 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0424 = ((g 1) * (g 4) * (g 10)) := by
  norm_num [atom0424, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0424_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19159309209600 : Int) atom0424) := by
  rw [SparsePolynomial.eval_scale, eval_atom0424]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0424Coded : CoefficientMerge.Poly := [(nat_lit 535, Int.ofNat (nat_lit 1))]
theorem atom0424Coded_decode : atom0424 = SparsePolynomial.decodeCubic 21 atom0424Coded := by decide +kernel
theorem atom0424Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19159309209600 : Int) atom0424Coded) := by
  have h := atom0424_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0424Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0425 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0425 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0425 = ((g 1) * (g 4) * (g 11)) := by
  norm_num [atom0425, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0425_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19026429004800 : Int) atom0425) := by
  rw [SparsePolynomial.eval_scale, eval_atom0425]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0425Coded : CoefficientMerge.Poly := [(nat_lit 536, Int.ofNat (nat_lit 1))]
theorem atom0425Coded_decode : atom0425 = SparsePolynomial.decodeCubic 21 atom0425Coded := by decide +kernel
theorem atom0425Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19026429004800 : Int) atom0425Coded) := by
  have h := atom0425_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0425Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0426 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0426 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0426 = ((g 1) * (g 4) * (g 12)) := by
  norm_num [atom0426, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0426_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15199948444800 : Int) atom0426) := by
  rw [SparsePolynomial.eval_scale, eval_atom0426]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0426Coded : CoefficientMerge.Poly := [(nat_lit 537, Int.ofNat (nat_lit 1))]
theorem atom0426Coded_decode : atom0426 = SparsePolynomial.decodeCubic 21 atom0426Coded := by decide +kernel
theorem atom0426Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15199948444800 : Int) atom0426Coded) := by
  have h := atom0426_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0426Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0427 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0427 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0427 = ((g 1) * (g 4) * (g 13)) := by
  norm_num [atom0427, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0427_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14776849180800 : Int) atom0427) := by
  rw [SparsePolynomial.eval_scale, eval_atom0427]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0427Coded : CoefficientMerge.Poly := [(nat_lit 538, Int.ofNat (nat_lit 1))]
theorem atom0427Coded_decode : atom0427 = SparsePolynomial.decodeCubic 21 atom0427Coded := by decide +kernel
theorem atom0427Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14776849180800 : Int) atom0427Coded) := by
  have h := atom0427_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0427Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0428 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0428 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0428 = ((g 1) * (g 4) * (g 14)) := by
  norm_num [atom0428, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0428_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15669867830400 : Int) atom0428) := by
  rw [SparsePolynomial.eval_scale, eval_atom0428]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0428Coded : CoefficientMerge.Poly := [(nat_lit 539, Int.ofNat (nat_lit 1))]
theorem atom0428Coded_decode : atom0428 = SparsePolynomial.decodeCubic 21 atom0428Coded := by decide +kernel
theorem atom0428Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15669867830400 : Int) atom0428Coded) := by
  have h := atom0428_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0428Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0429 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0429 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0429 = ((g 1) * (g 4) * (g 15)) := by
  norm_num [atom0429, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0429_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24880813977600 : Int) atom0429) := by
  rw [SparsePolynomial.eval_scale, eval_atom0429]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0429Coded : CoefficientMerge.Poly := [(nat_lit 540, Int.ofNat (nat_lit 1))]
theorem atom0429Coded_decode : atom0429 = SparsePolynomial.decodeCubic 21 atom0429Coded := by decide +kernel
theorem atom0429Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24880813977600 : Int) atom0429Coded) := by
  have h := atom0429_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0429Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0430 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0430 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0430 = ((g 1) * (g 4) * (g 16)) := by
  norm_num [atom0430, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0430_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18272069247600 : Int) atom0430) := by
  rw [SparsePolynomial.eval_scale, eval_atom0430]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 4) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0430Coded : CoefficientMerge.Poly := [(nat_lit 541, Int.ofNat (nat_lit 1))]
theorem atom0430Coded_decode : atom0430 = SparsePolynomial.decodeCubic 21 atom0430Coded := by decide +kernel
theorem atom0430Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18272069247600 : Int) atom0430Coded) := by
  have h := atom0430_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0430Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0431 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0431 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0431 = ((g 1) * (g 4) * (g 17)) := by
  norm_num [atom0431, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0431_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22602534796800 : Int) atom0431) := by
  rw [SparsePolynomial.eval_scale, eval_atom0431]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 4) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0431Coded : CoefficientMerge.Poly := [(nat_lit 542, Int.ofNat (nat_lit 1))]
theorem atom0431Coded_decode : atom0431 = SparsePolynomial.decodeCubic 21 atom0431Coded := by decide +kernel
theorem atom0431Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22602534796800 : Int) atom0431Coded) := by
  have h := atom0431_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0431Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0432 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0432 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0432 = ((g 1) * (g 4) * (g 18)) := by
  norm_num [atom0432, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0432_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20221399774800 : Int) atom0432) := by
  rw [SparsePolynomial.eval_scale, eval_atom0432]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0432Coded : CoefficientMerge.Poly := [(nat_lit 543, Int.ofNat (nat_lit 1))]
theorem atom0432Coded_decode : atom0432 = SparsePolynomial.decodeCubic 21 atom0432Coded := by decide +kernel
theorem atom0432Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20221399774800 : Int) atom0432Coded) := by
  have h := atom0432_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0432Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0433 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0433 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0433 = ((g 1) * (g 4) * (g 19)) := by
  norm_num [atom0433, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0433_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21663695768400 : Int) atom0433) := by
  rw [SparsePolynomial.eval_scale, eval_atom0433]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 4) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0433Coded : CoefficientMerge.Poly := [(nat_lit 544, Int.ofNat (nat_lit 1))]
theorem atom0433Coded_decode : atom0433 = SparsePolynomial.decodeCubic 21 atom0433Coded := by decide +kernel
theorem atom0433Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21663695768400 : Int) atom0433Coded) := by
  have h := atom0433_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0433Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0434 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0434 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0434 = ((g 1) * (g 4) * (g 20)) := by
  norm_num [atom0434, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0434_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17565700194000 : Int) atom0434) := by
  rw [SparsePolynomial.eval_scale, eval_atom0434]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 4) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0434Coded : CoefficientMerge.Poly := [(nat_lit 545, Int.ofNat (nat_lit 1))]
theorem atom0434Coded_decode : atom0434 = SparsePolynomial.decodeCubic 21 atom0434Coded := by decide +kernel
theorem atom0434Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17565700194000 : Int) atom0434Coded) := by
  have h := atom0434_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0434Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0435 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0435 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0435 = ((g 1) * (g 5) * (g 5)) := by
  norm_num [atom0435, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0435_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11219811941376 : Int) atom0435) := by
  rw [SparsePolynomial.eval_scale, eval_atom0435]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0435Coded : CoefficientMerge.Poly := [(nat_lit 551, Int.ofNat (nat_lit 1))]
theorem atom0435Coded_decode : atom0435 = SparsePolynomial.decodeCubic 21 atom0435Coded := by decide +kernel
theorem atom0435Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11219811941376 : Int) atom0435Coded) := by
  have h := atom0435_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0435Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0436 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0436 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0436 = ((g 1) * (g 5) * (g 6)) := by
  norm_num [atom0436, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0436_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19865648451456 : Int) atom0436) := by
  rw [SparsePolynomial.eval_scale, eval_atom0436]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0436Coded : CoefficientMerge.Poly := [(nat_lit 552, Int.ofNat (nat_lit 1))]
theorem atom0436Coded_decode : atom0436 = SparsePolynomial.decodeCubic 21 atom0436Coded := by decide +kernel
theorem atom0436Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19865648451456 : Int) atom0436Coded) := by
  have h := atom0436_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0436Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0437 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0437 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0437 = ((g 1) * (g 5) * (g 7)) := by
  norm_num [atom0437, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0437_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19588073217408 : Int) atom0437) := by
  rw [SparsePolynomial.eval_scale, eval_atom0437]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0437Coded : CoefficientMerge.Poly := [(nat_lit 553, Int.ofNat (nat_lit 1))]
theorem atom0437Coded_decode : atom0437 = SparsePolynomial.decodeCubic 21 atom0437Coded := by decide +kernel
theorem atom0437Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19588073217408 : Int) atom0437Coded) := by
  have h := atom0437_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0437Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0438 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0438 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0438 = ((g 1) * (g 5) * (g 8)) := by
  norm_num [atom0438, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0438_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20097013768704 : Int) atom0438) := by
  rw [SparsePolynomial.eval_scale, eval_atom0438]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0438Coded : CoefficientMerge.Poly := [(nat_lit 554, Int.ofNat (nat_lit 1))]
theorem atom0438Coded_decode : atom0438 = SparsePolynomial.decodeCubic 21 atom0438Coded := by decide +kernel
theorem atom0438Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20097013768704 : Int) atom0438Coded) := by
  have h := atom0438_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0438Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0439 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0439 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0439 = ((g 1) * (g 5) * (g 9)) := by
  norm_num [atom0439, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0439_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21289155007104 : Int) atom0439) := by
  rw [SparsePolynomial.eval_scale, eval_atom0439]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0439Coded : CoefficientMerge.Poly := [(nat_lit 555, Int.ofNat (nat_lit 1))]
theorem atom0439Coded_decode : atom0439 = SparsePolynomial.decodeCubic 21 atom0439Coded := by decide +kernel
theorem atom0439Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21289155007104 : Int) atom0439Coded) := by
  have h := atom0439_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0439Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0440 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0440 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0440 = ((g 1) * (g 5) * (g 10)) := by
  norm_num [atom0440, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0440_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21751611093504 : Int) atom0440) := by
  rw [SparsePolynomial.eval_scale, eval_atom0440]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0440Coded : CoefficientMerge.Poly := [(nat_lit 556, Int.ofNat (nat_lit 1))]
theorem atom0440Coded_decode : atom0440 = SparsePolynomial.decodeCubic 21 atom0440Coded := by decide +kernel
theorem atom0440Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21751611093504 : Int) atom0440Coded) := by
  have h := atom0440_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0440Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0441 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0441 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0441 = ((g 1) * (g 5) * (g 11)) := by
  norm_num [atom0441, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0441_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21955062587904 : Int) atom0441) := by
  rw [SparsePolynomial.eval_scale, eval_atom0441]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0441Coded : CoefficientMerge.Poly := [(nat_lit 557, Int.ofNat (nat_lit 1))]
theorem atom0441Coded_decode : atom0441 = SparsePolynomial.decodeCubic 21 atom0441Coded := by decide +kernel
theorem atom0441Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21955062587904 : Int) atom0441Coded) := by
  have h := atom0441_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0441Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0442 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0442 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0442 = ((g 1) * (g 5) * (g 12)) := by
  norm_num [atom0442, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0442_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18753888376704 : Int) atom0442) := by
  rw [SparsePolynomial.eval_scale, eval_atom0442]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0442Coded : CoefficientMerge.Poly := [(nat_lit 558, Int.ofNat (nat_lit 1))]
theorem atom0442Coded_decode : atom0442 = SparsePolynomial.decodeCubic 21 atom0442Coded := by decide +kernel
theorem atom0442Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18753888376704 : Int) atom0442Coded) := by
  have h := atom0442_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0442Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0443 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0443 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0443 = ((g 1) * (g 5) * (g 13)) := by
  norm_num [atom0443, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0443_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18329339407104 : Int) atom0443) := by
  rw [SparsePolynomial.eval_scale, eval_atom0443]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0443Coded : CoefficientMerge.Poly := [(nat_lit 559, Int.ofNat (nat_lit 1))]
theorem atom0443Coded_decode : atom0443 = SparsePolynomial.decodeCubic 21 atom0443Coded := by decide +kernel
theorem atom0443Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18329339407104 : Int) atom0443Coded) := by
  have h := atom0443_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0443Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0444 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0444 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0444 = ((g 1) * (g 5) * (g 14)) := by
  norm_num [atom0444, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0444_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19351865090304 : Int) atom0444) := by
  rw [SparsePolynomial.eval_scale, eval_atom0444]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0444Coded : CoefficientMerge.Poly := [(nat_lit 560, Int.ofNat (nat_lit 1))]
theorem atom0444Coded_decode : atom0444 = SparsePolynomial.decodeCubic 21 atom0444Coded := by decide +kernel
theorem atom0444Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19351865090304 : Int) atom0444Coded) := by
  have h := atom0444_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0444Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0445 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0445 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0445 = ((g 1) * (g 5) * (g 15)) := by
  norm_num [atom0445, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0445_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29154774357504 : Int) atom0445) := by
  rw [SparsePolynomial.eval_scale, eval_atom0445]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0445Coded : CoefficientMerge.Poly := [(nat_lit 561, Int.ofNat (nat_lit 1))]
theorem atom0445Coded_decode : atom0445 = SparsePolynomial.decodeCubic 21 atom0445Coded := by decide +kernel
theorem atom0445Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29154774357504 : Int) atom0445Coded) := by
  have h := atom0445_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0445Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0446 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0446 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0446 = ((g 1) * (g 5) * (g 16)) := by
  norm_num [atom0446, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0446_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22695246099072 : Int) atom0446) := by
  rw [SparsePolynomial.eval_scale, eval_atom0446]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0446Coded : CoefficientMerge.Poly := [(nat_lit 562, Int.ofNat (nat_lit 1))]
theorem atom0446Coded_decode : atom0446 = SparsePolynomial.decodeCubic 21 atom0446Coded := by decide +kernel
theorem atom0446Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22695246099072 : Int) atom0446Coded) := by
  have h := atom0446_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0446Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0447 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0447 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0447 = ((g 1) * (g 5) * (g 17)) := by
  norm_num [atom0447, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0447_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27549158575104 : Int) atom0447) := by
  rw [SparsePolynomial.eval_scale, eval_atom0447]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0447Coded : CoefficientMerge.Poly := [(nat_lit 563, Int.ofNat (nat_lit 1))]
theorem atom0447Coded_decode : atom0447 = SparsePolynomial.decodeCubic 21 atom0447Coded := by decide +kernel
theorem atom0447Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27549158575104 : Int) atom0447Coded) := by
  have h := atom0447_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0447Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0448 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0448 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0448 = ((g 1) * (g 5) * (g 18)) := by
  norm_num [atom0448, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0448_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25867921742208 : Int) atom0448) := by
  rw [SparsePolynomial.eval_scale, eval_atom0448]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0448Coded : CoefficientMerge.Poly := [(nat_lit 564, Int.ofNat (nat_lit 1))]
theorem atom0448Coded_decode : atom0448 = SparsePolynomial.decodeCubic 21 atom0448Coded := by decide +kernel
theorem atom0448Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25867921742208 : Int) atom0448Coded) := by
  have h := atom0448_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0448Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0449 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0449 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0449 = ((g 1) * (g 5) * (g 19)) := by
  norm_num [atom0449, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0449_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27674310760320 : Int) atom0449) := by
  rw [SparsePolynomial.eval_scale, eval_atom0449]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0449Coded : CoefficientMerge.Poly := [(nat_lit 565, Int.ofNat (nat_lit 1))]
theorem atom0449Coded_decode : atom0449 = SparsePolynomial.decodeCubic 21 atom0449Coded := by decide +kernel
theorem atom0449Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27674310760320 : Int) atom0449Coded) := by
  have h := atom0449_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0449Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0450 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0450 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0450 = ((g 1) * (g 5) * (g 20)) := by
  norm_num [atom0450, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0450_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23463825855168 : Int) atom0450) := by
  rw [SparsePolynomial.eval_scale, eval_atom0450]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0450Coded : CoefficientMerge.Poly := [(nat_lit 566, Int.ofNat (nat_lit 1))]
theorem atom0450Coded_decode : atom0450 = SparsePolynomial.decodeCubic 21 atom0450Coded := by decide +kernel
theorem atom0450Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23463825855168 : Int) atom0450Coded) := by
  have h := atom0450_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0450Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0451 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0451 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0451 = ((g 1) * (g 6) * (g 6)) := by
  norm_num [atom0451, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0451_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14524199424000 : Int) atom0451) := by
  rw [SparsePolynomial.eval_scale, eval_atom0451]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0451Coded : CoefficientMerge.Poly := [(nat_lit 573, Int.ofNat (nat_lit 1))]
theorem atom0451Coded_decode : atom0451 = SparsePolynomial.decodeCubic 21 atom0451Coded := by decide +kernel
theorem atom0451Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14524199424000 : Int) atom0451Coded) := by
  have h := atom0451_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0451Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0452 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0452 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0452 = ((g 1) * (g 6) * (g 7)) := by
  norm_num [atom0452, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0452_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25592052764160 : Int) atom0452) := by
  rw [SparsePolynomial.eval_scale, eval_atom0452]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0452Coded : CoefficientMerge.Poly := [(nat_lit 574, Int.ofNat (nat_lit 1))]
theorem atom0452Coded_decode : atom0452 = SparsePolynomial.decodeCubic 21 atom0452Coded := by decide +kernel
theorem atom0452Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25592052764160 : Int) atom0452Coded) := by
  have h := atom0452_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0452Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0453 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0453 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0453 = ((g 1) * (g 6) * (g 8)) := by
  norm_num [atom0453, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0453_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23065383297600 : Int) atom0453) := by
  rw [SparsePolynomial.eval_scale, eval_atom0453]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0453Coded : CoefficientMerge.Poly := [(nat_lit 575, Int.ofNat (nat_lit 1))]
theorem atom0453Coded_decode : atom0453 = SparsePolynomial.decodeCubic 21 atom0453Coded := by decide +kernel
theorem atom0453Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23065383297600 : Int) atom0453Coded) := by
  have h := atom0453_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0453Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0454 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0454 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0454 = ((g 1) * (g 6) * (g 9)) := by
  norm_num [atom0454, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0454_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22222382918400 : Int) atom0454) := by
  rw [SparsePolynomial.eval_scale, eval_atom0454]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0454Coded : CoefficientMerge.Poly := [(nat_lit 576, Int.ofNat (nat_lit 1))]
theorem atom0454Coded_decode : atom0454 = SparsePolynomial.decodeCubic 21 atom0454Coded := by decide +kernel
theorem atom0454Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22222382918400 : Int) atom0454Coded) := by
  have h := atom0454_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0454Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0455 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0455 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0455 = ((g 1) * (g 6) * (g 10)) := by
  norm_num [atom0455, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0455_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22859770147200 : Int) atom0455) := by
  rw [SparsePolynomial.eval_scale, eval_atom0455]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0455Coded : CoefficientMerge.Poly := [(nat_lit 577, Int.ofNat (nat_lit 1))]
theorem atom0455Coded_decode : atom0455 = SparsePolynomial.decodeCubic 21 atom0455Coded := by decide +kernel
theorem atom0455Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22859770147200 : Int) atom0455Coded) := by
  have h := atom0455_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0455Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0456 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0456 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0456 = ((g 1) * (g 6) * (g 11)) := by
  norm_num [atom0456, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0456_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22899764966400 : Int) atom0456) := by
  rw [SparsePolynomial.eval_scale, eval_atom0456]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0456Coded : CoefficientMerge.Poly := [(nat_lit 578, Int.ofNat (nat_lit 1))]
theorem atom0456Coded_decode : atom0456 = SparsePolynomial.decodeCubic 21 atom0456Coded := by decide +kernel
theorem atom0456Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22899764966400 : Int) atom0456Coded) := by
  have h := atom0456_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0456Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0457 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0457 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0457 = ((g 1) * (g 6) * (g 12)) := by
  norm_num [atom0457, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0457_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20036978572800 : Int) atom0457) := by
  rw [SparsePolynomial.eval_scale, eval_atom0457]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0457Coded : CoefficientMerge.Poly := [(nat_lit 579, Int.ofNat (nat_lit 1))]
theorem atom0457Coded_decode : atom0457 = SparsePolynomial.decodeCubic 21 atom0457Coded := by decide +kernel
theorem atom0457Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20036978572800 : Int) atom0457Coded) := by
  have h := atom0457_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0457Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0458 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0458 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0458 = ((g 1) * (g 6) * (g 13)) := by
  norm_num [atom0458, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0458_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19788810451200 : Int) atom0458) := by
  rw [SparsePolynomial.eval_scale, eval_atom0458]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0458Coded : CoefficientMerge.Poly := [(nat_lit 580, Int.ofNat (nat_lit 1))]
theorem atom0458Coded_decode : atom0458 = SparsePolynomial.decodeCubic 21 atom0458Coded := by decide +kernel
theorem atom0458Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19788810451200 : Int) atom0458Coded) := by
  have h := atom0458_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0458Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0459 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0459 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0459 = ((g 1) * (g 6) * (g 14)) := by
  norm_num [atom0459, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0459_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20856760243200 : Int) atom0459) := by
  rw [SparsePolynomial.eval_scale, eval_atom0459]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0459Coded : CoefficientMerge.Poly := [(nat_lit 581, Int.ofNat (nat_lit 1))]
theorem atom0459Coded_decode : atom0459 = SparsePolynomial.decodeCubic 21 atom0459Coded := by decide +kernel
theorem atom0459Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20856760243200 : Int) atom0459Coded) := by
  have h := atom0459_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0459Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0460 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0460 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0460 = ((g 1) * (g 6) * (g 15)) := by
  norm_num [atom0460, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0460_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31352628787200 : Int) atom0460) := by
  rw [SparsePolynomial.eval_scale, eval_atom0460]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0460Coded : CoefficientMerge.Poly := [(nat_lit 582, Int.ofNat (nat_lit 1))]
theorem atom0460Coded_decode : atom0460 = SparsePolynomial.decodeCubic 21 atom0460Coded := by decide +kernel
theorem atom0460Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31352628787200 : Int) atom0460Coded) := by
  have h := atom0460_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0460Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0461 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0461 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0461 = ((g 1) * (g 6) * (g 16)) := by
  norm_num [atom0461, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0461_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25110779097600 : Int) atom0461) := by
  rw [SparsePolynomial.eval_scale, eval_atom0461]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0461Coded : CoefficientMerge.Poly := [(nat_lit 583, Int.ofNat (nat_lit 1))]
theorem atom0461Coded_decode : atom0461 = SparsePolynomial.decodeCubic 21 atom0461Coded := by decide +kernel
theorem atom0461Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25110779097600 : Int) atom0461Coded) := by
  have h := atom0461_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0461Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0462 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0462 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0462 = ((g 1) * (g 6) * (g 17)) := by
  norm_num [atom0462, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0462_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30419676403200 : Int) atom0462) := by
  rw [SparsePolynomial.eval_scale, eval_atom0462]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0462Coded : CoefficientMerge.Poly := [(nat_lit 584, Int.ofNat (nat_lit 1))]
theorem atom0462Coded_decode : atom0462 = SparsePolynomial.decodeCubic 21 atom0462Coded := by decide +kernel
theorem atom0462Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30419676403200 : Int) atom0462Coded) := by
  have h := atom0462_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0462Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0463 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0463 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0463 = ((g 1) * (g 6) * (g 18)) := by
  norm_num [atom0463, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0463_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30013882214400 : Int) atom0463) := by
  rw [SparsePolynomial.eval_scale, eval_atom0463]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0463Coded : CoefficientMerge.Poly := [(nat_lit 585, Int.ofNat (nat_lit 1))]
theorem atom0463Coded_decode : atom0463 = SparsePolynomial.decodeCubic 21 atom0463Coded := by decide +kernel
theorem atom0463Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30013882214400 : Int) atom0463Coded) := by
  have h := atom0463_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0463Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0464 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0464 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0464 = ((g 1) * (g 6) * (g 19)) := by
  norm_num [atom0464, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0464_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33459931814400 : Int) atom0464) := by
  rw [SparsePolynomial.eval_scale, eval_atom0464]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0464Coded : CoefficientMerge.Poly := [(nat_lit 586, Int.ofNat (nat_lit 1))]
theorem atom0464Coded_decode : atom0464 = SparsePolynomial.decodeCubic 21 atom0464Coded := by decide +kernel
theorem atom0464Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33459931814400 : Int) atom0464Coded) := by
  have h := atom0464_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0464Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0465 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0465 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0465 = ((g 1) * (g 6) * (g 20)) := by
  norm_num [atom0465, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0465_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32426062099200 : Int) atom0465) := by
  rw [SparsePolynomial.eval_scale, eval_atom0465]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0465Coded : CoefficientMerge.Poly := [(nat_lit 587, Int.ofNat (nat_lit 1))]
theorem atom0465Coded_decode : atom0465 = SparsePolynomial.decodeCubic 21 atom0465Coded := by decide +kernel
theorem atom0465Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32426062099200 : Int) atom0465Coded) := by
  have h := atom0465_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0465Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0466 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0466 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0466 = ((g 1) * (g 7) * (g 7)) := by
  norm_num [atom0466, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0466_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16601669556480 : Int) atom0466) := by
  rw [SparsePolynomial.eval_scale, eval_atom0466]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0466Coded : CoefficientMerge.Poly := [(nat_lit 595, Int.ofNat (nat_lit 1))]
theorem atom0466Coded_decode : atom0466 = SparsePolynomial.decodeCubic 21 atom0466Coded := by decide +kernel
theorem atom0466Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16601669556480 : Int) atom0466Coded) := by
  have h := atom0466_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0466Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0467 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0467 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0467 = ((g 1) * (g 7) * (g 8)) := by
  norm_num [atom0467, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0467_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29149185627360 : Int) atom0467) := by
  rw [SparsePolynomial.eval_scale, eval_atom0467]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0467Coded : CoefficientMerge.Poly := [(nat_lit 596, Int.ofNat (nat_lit 1))]
theorem atom0467Coded_decode : atom0467 = SparsePolynomial.decodeCubic 21 atom0467Coded := by decide +kernel
theorem atom0467Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29149185627360 : Int) atom0467Coded) := by
  have h := atom0467_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0467Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0468 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0468 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0468 = ((g 1) * (g 7) * (g 9)) := by
  norm_num [atom0468, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0468_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27058453117056 : Int) atom0468) := by
  rw [SparsePolynomial.eval_scale, eval_atom0468]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0468Coded : CoefficientMerge.Poly := [(nat_lit 597, Int.ofNat (nat_lit 1))]
theorem atom0468Coded_decode : atom0468 = SparsePolynomial.decodeCubic 21 atom0468Coded := by decide +kernel
theorem atom0468Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27058453117056 : Int) atom0468Coded) := by
  have h := atom0468_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0468Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0469 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0469 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0469 = ((g 1) * (g 7) * (g 10)) := by
  norm_num [atom0469, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0469_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27527674496256 : Int) atom0469) := by
  rw [SparsePolynomial.eval_scale, eval_atom0469]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0469Coded : CoefficientMerge.Poly := [(nat_lit 598, Int.ofNat (nat_lit 1))]
theorem atom0469Coded_decode : atom0469 = SparsePolynomial.decodeCubic 21 atom0469Coded := by decide +kernel
theorem atom0469Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27527674496256 : Int) atom0469Coded) := by
  have h := atom0469_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0469Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0470 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0470 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0470 = ((g 1) * (g 7) * (g 11)) := by
  norm_num [atom0470, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0470_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27658517533056 : Int) atom0470) := by
  rw [SparsePolynomial.eval_scale, eval_atom0470]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0470Coded : CoefficientMerge.Poly := [(nat_lit 599, Int.ofNat (nat_lit 1))]
theorem atom0470Coded_decode : atom0470 = SparsePolynomial.decodeCubic 21 atom0470Coded := by decide +kernel
theorem atom0470Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27658517533056 : Int) atom0470Coded) := by
  have h := atom0470_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0470Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0471 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0471 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0471 = ((g 1) * (g 7) * (g 12)) := by
  norm_num [atom0471, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0471_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24757072323456 : Int) atom0471) := by
  rw [SparsePolynomial.eval_scale, eval_atom0471]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0471Coded : CoefficientMerge.Poly := [(nat_lit 600, Int.ofNat (nat_lit 1))]
theorem atom0471Coded_decode : atom0471 = SparsePolynomial.decodeCubic 21 atom0471Coded := by decide +kernel
theorem atom0471Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24757072323456 : Int) atom0471Coded) := by
  have h := atom0471_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0471Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0472 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0472 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0472 = ((g 1) * (g 7) * (g 13)) := by
  norm_num [atom0472, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0472_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24470245385856 : Int) atom0472) := by
  rw [SparsePolynomial.eval_scale, eval_atom0472]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0472Coded : CoefficientMerge.Poly := [(nat_lit 601, Int.ofNat (nat_lit 1))]
theorem atom0472Coded_decode : atom0472 = SparsePolynomial.decodeCubic 21 atom0472Coded := by decide +kernel
theorem atom0472Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24470245385856 : Int) atom0472Coded) := by
  have h := atom0472_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0472Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0473 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0473 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0473 = ((g 1) * (g 7) * (g 14)) := by
  norm_num [atom0473, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0473_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25499536361856 : Int) atom0473) := by
  rw [SparsePolynomial.eval_scale, eval_atom0473]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0473Coded : CoefficientMerge.Poly := [(nat_lit 602, Int.ofNat (nat_lit 1))]
theorem atom0473Coded_decode : atom0473 = SparsePolynomial.decodeCubic 21 atom0473Coded := by decide +kernel
theorem atom0473Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25499536361856 : Int) atom0473Coded) := by
  have h := atom0473_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0473Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0474 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0474 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0474 = ((g 1) * (g 7) * (g 15)) := by
  norm_num [atom0474, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0474_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35551425892608 : Int) atom0474) := by
  rw [SparsePolynomial.eval_scale, eval_atom0474]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0474Coded : CoefficientMerge.Poly := [(nat_lit 603, Int.ofNat (nat_lit 1))]
theorem atom0474Coded_decode : atom0474 = SparsePolynomial.decodeCubic 21 atom0474Coded := by decide +kernel
theorem atom0474Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35551425892608 : Int) atom0474Coded) := by
  have h := atom0474_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0474Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0475 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0475 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0475 = ((g 1) * (g 7) * (g 16)) := by
  norm_num [atom0475, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0475_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29604979281024 : Int) atom0475) := by
  rw [SparsePolynomial.eval_scale, eval_atom0475]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0475Coded : CoefficientMerge.Poly := [(nat_lit 604, Int.ofNat (nat_lit 1))]
theorem atom0475Coded_decode : atom0475 = SparsePolynomial.decodeCubic 21 atom0475Coded := by decide +kernel
theorem atom0475Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29604979281024 : Int) atom0475Coded) := by
  have h := atom0475_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0475Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0476 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0476 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0476 = ((g 1) * (g 7) * (g 17)) := by
  norm_num [atom0476, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0476_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35291136907008 : Int) atom0476) := by
  rw [SparsePolynomial.eval_scale, eval_atom0476]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0476Coded : CoefficientMerge.Poly := [(nat_lit 605, Int.ofNat (nat_lit 1))]
theorem atom0476Coded_decode : atom0476 = SparsePolynomial.decodeCubic 21 atom0476Coded := by decide +kernel
theorem atom0476Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35291136907008 : Int) atom0476Coded) := by
  have h := atom0476_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0476Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0477 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0477 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0477 = ((g 1) * (g 7) * (g 18)) := by
  norm_num [atom0477, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0477_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34288248159360 : Int) atom0477) := by
  rw [SparsePolynomial.eval_scale, eval_atom0477]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0477Coded : CoefficientMerge.Poly := [(nat_lit 606, Int.ofNat (nat_lit 1))]
theorem atom0477Coded_decode : atom0477 = SparsePolynomial.decodeCubic 21 atom0477Coded := by decide +kernel
theorem atom0477Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34288248159360 : Int) atom0477Coded) := by
  have h := atom0477_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0477Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0478 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0478 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0478 = ((g 1) * (g 7) * (g 19)) := by
  norm_num [atom0478, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0478_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34242389905920 : Int) atom0478) := by
  rw [SparsePolynomial.eval_scale, eval_atom0478]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0478Coded : CoefficientMerge.Poly := [(nat_lit 607, Int.ofNat (nat_lit 1))]
theorem atom0478Coded_decode : atom0478 = SparsePolynomial.decodeCubic 21 atom0478Coded := by decide +kernel
theorem atom0478Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34242389905920 : Int) atom0478Coded) := by
  have h := atom0478_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0478Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0479 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0479 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0479 = ((g 1) * (g 7) * (g 20)) := by
  norm_num [atom0479, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0479_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32868397290240 : Int) atom0479) := by
  rw [SparsePolynomial.eval_scale, eval_atom0479]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0479Coded : CoefficientMerge.Poly := [(nat_lit 608, Int.ofNat (nat_lit 1))]
theorem atom0479Coded_decode : atom0479 = SparsePolynomial.decodeCubic 21 atom0479Coded := by decide +kernel
theorem atom0479Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32868397290240 : Int) atom0479Coded) := by
  have h := atom0479_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0479Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0480 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0480 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0480 = ((g 1) * (g 8) * (g 8)) := by
  norm_num [atom0480, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0480_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18294922245600 : Int) atom0480) := by
  rw [SparsePolynomial.eval_scale, eval_atom0480]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0480Coded : CoefficientMerge.Poly := [(nat_lit 617, Int.ofNat (nat_lit 1))]
theorem atom0480Coded_decode : atom0480 = SparsePolynomial.decodeCubic 21 atom0480Coded := by decide +kernel
theorem atom0480Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18294922245600 : Int) atom0480Coded) := by
  have h := atom0480_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0480Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0481 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0481 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0481 = ((g 1) * (g 8) * (g 9)) := by
  norm_num [atom0481, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0481_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32761969339680 : Int) atom0481) := by
  rw [SparsePolynomial.eval_scale, eval_atom0481]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0481Coded : CoefficientMerge.Poly := [(nat_lit 618, Int.ofNat (nat_lit 1))]
theorem atom0481Coded_decode : atom0481 = SparsePolynomial.decodeCubic 21 atom0481Coded := by decide +kernel
theorem atom0481Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32761969339680 : Int) atom0481Coded) := by
  have h := atom0481_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0481Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0482 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0482 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0482 = ((g 1) * (g 8) * (g 10)) := by
  norm_num [atom0482, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0482_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31025713320000 : Int) atom0482) := by
  rw [SparsePolynomial.eval_scale, eval_atom0482]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0482Coded : CoefficientMerge.Poly := [(nat_lit 619, Int.ofNat (nat_lit 1))]
theorem atom0482Coded_decode : atom0482 = SparsePolynomial.decodeCubic 21 atom0482Coded := by decide +kernel
theorem atom0482Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31025713320000 : Int) atom0482Coded) := by
  have h := atom0482_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0482Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0483 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0483 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0483 = ((g 1) * (g 8) * (g 11)) := by
  norm_num [atom0483, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0483_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30904307582400 : Int) atom0483) := by
  rw [SparsePolynomial.eval_scale, eval_atom0483]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0483Coded : CoefficientMerge.Poly := [(nat_lit 620, Int.ofNat (nat_lit 1))]
theorem atom0483Coded_decode : atom0483 = SparsePolynomial.decodeCubic 21 atom0483Coded := by decide +kernel
theorem atom0483Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30904307582400 : Int) atom0483Coded) := by
  have h := atom0483_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0483Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0484 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0484 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0484 = ((g 1) * (g 8) * (g 12)) := by
  norm_num [atom0484, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0484_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27666530673600 : Int) atom0484) := by
  rw [SparsePolynomial.eval_scale, eval_atom0484]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0484Coded : CoefficientMerge.Poly := [(nat_lit 621, Int.ofNat (nat_lit 1))]
theorem atom0484Coded_decode : atom0484 = SparsePolynomial.decodeCubic 21 atom0484Coded := by decide +kernel
theorem atom0484Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27666530673600 : Int) atom0484Coded) := by
  have h := atom0484_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0484Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0485 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0485 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0485 = ((g 1) * (g 8) * (g 13)) := by
  norm_num [atom0485, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0485_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27256961995200 : Int) atom0485) := by
  rw [SparsePolynomial.eval_scale, eval_atom0485]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0485Coded : CoefficientMerge.Poly := [(nat_lit 622, Int.ofNat (nat_lit 1))]
theorem atom0485Coded_decode : atom0485 = SparsePolynomial.decodeCubic 21 atom0485Coded := by decide +kernel
theorem atom0485Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27256961995200 : Int) atom0485Coded) := by
  have h := atom0485_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0485Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0486 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0486 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0486 = ((g 1) * (g 8) * (g 14)) := by
  norm_num [atom0486, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0486_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28163511230400 : Int) atom0486) := by
  rw [SparsePolynomial.eval_scale, eval_atom0486]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0486Coded : CoefficientMerge.Poly := [(nat_lit 623, Int.ofNat (nat_lit 1))]
theorem atom0486Coded_decode : atom0486 = SparsePolynomial.decodeCubic 21 atom0486Coded := by decide +kernel
theorem atom0486Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28163511230400 : Int) atom0486Coded) := by
  have h := atom0486_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0486Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0487 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0487 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0487 = ((g 1) * (g 8) * (g 15)) := by
  norm_num [atom0487, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0487_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37846980864000 : Int) atom0487) := by
  rw [SparsePolynomial.eval_scale, eval_atom0487]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 1) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0487Coded : CoefficientMerge.Poly := [(nat_lit 624, Int.ofNat (nat_lit 1))]
theorem atom0487Coded_decode : atom0487 = SparsePolynomial.decodeCubic 21 atom0487Coded := by decide +kernel
theorem atom0487Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37846980864000 : Int) atom0487Coded) := by
  have h := atom0487_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0487Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0488 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0488 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0488 = ((g 1) * (g 8) * (g 16)) := by
  norm_num [atom0488, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0488_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32247885612600 : Int) atom0488) := by
  rw [SparsePolynomial.eval_scale, eval_atom0488]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 1) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0488Coded : CoefficientMerge.Poly := [(nat_lit 625, Int.ofNat (nat_lit 1))]
theorem atom0488Coded_decode : atom0488 = SparsePolynomial.decodeCubic 21 atom0488Coded := by decide +kernel
theorem atom0488Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32247885612600 : Int) atom0488Coded) := by
  have h := atom0488_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0488Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0489 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0489 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0489 = ((g 1) * (g 8) * (g 17)) := by
  norm_num [atom0489, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0489_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38259355276800 : Int) atom0489) := by
  rw [SparsePolynomial.eval_scale, eval_atom0489]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 1) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0489Coded : CoefficientMerge.Poly := [(nat_lit 626, Int.ofNat (nat_lit 1))]
theorem atom0489Coded_decode : atom0489 = SparsePolynomial.decodeCubic 21 atom0489Coded := by decide +kernel
theorem atom0489Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38259355276800 : Int) atom0489Coded) := by
  have h := atom0489_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0489Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0490 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0490 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0490 = ((g 1) * (g 8) * (g 18)) := by
  norm_num [atom0490, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0490_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (37134500898600 : Int) atom0490) := by
  rw [SparsePolynomial.eval_scale, eval_atom0490]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 1) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0490Coded : CoefficientMerge.Poly := [(nat_lit 627, Int.ofNat (nat_lit 1))]
theorem atom0490Coded_decode : atom0490 = SparsePolynomial.decodeCubic 21 atom0490Coded := by decide +kernel
theorem atom0490Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (37134500898600 : Int) atom0490Coded) := by
  have h := atom0490_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0490Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0491 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0491 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0491 = ((g 1) * (g 8) * (g 19)) := by
  norm_num [atom0491, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0491_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34636711842600 : Int) atom0491) := by
  rw [SparsePolynomial.eval_scale, eval_atom0491]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 1) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0491Coded : CoefficientMerge.Poly := [(nat_lit 628, Int.ofNat (nat_lit 1))]
theorem atom0491Coded_decode : atom0491 = SparsePolynomial.decodeCubic 21 atom0491Coded := by decide +kernel
theorem atom0491Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34636711842600 : Int) atom0491Coded) := by
  have h := atom0491_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0491Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0492 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0492 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0492 = ((g 1) * (g 8) * (g 20)) := by
  norm_num [atom0492, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0492_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34485486071400 : Int) atom0492) := by
  rw [SparsePolynomial.eval_scale, eval_atom0492]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 1) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0492Coded : CoefficientMerge.Poly := [(nat_lit 629, Int.ofNat (nat_lit 1))]
theorem atom0492Coded_decode : atom0492 = SparsePolynomial.decodeCubic 21 atom0492Coded := by decide +kernel
theorem atom0492Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34485486071400 : Int) atom0492Coded) := by
  have h := atom0492_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0492Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0493 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0493 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0493 = ((g 1) * (g 9) * (g 9)) := by
  norm_num [atom0493, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0493_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20214453268800 : Int) atom0493) := by
  rw [SparsePolynomial.eval_scale, eval_atom0493]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0493Coded : CoefficientMerge.Poly := [(nat_lit 639, Int.ofNat (nat_lit 1))]
theorem atom0493Coded_decode : atom0493 = SparsePolynomial.decodeCubic 21 atom0493Coded := by decide +kernel
theorem atom0493Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20214453268800 : Int) atom0493Coded) := by
  have h := atom0493_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0493Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0494 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0494 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0494 = ((g 1) * (g 9) * (g 10)) := by
  norm_num [atom0494, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0494_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36537606766080 : Int) atom0494) := by
  rw [SparsePolynomial.eval_scale, eval_atom0494]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0494Coded : CoefficientMerge.Poly := [(nat_lit 640, Int.ofNat (nat_lit 1))]
theorem atom0494Coded_decode : atom0494 = SparsePolynomial.decodeCubic 21 atom0494Coded := by decide +kernel
theorem atom0494Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36537606766080 : Int) atom0494Coded) := by
  have h := atom0494_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0494Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0495 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0495 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom0495 = ((g 1) * (g 9) * (g 11)) := by
  norm_num [atom0495, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0495_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33634828080000 : Int) atom0495) := by
  rw [SparsePolynomial.eval_scale, eval_atom0495]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0495Coded : CoefficientMerge.Poly := [(nat_lit 641, Int.ofNat (nat_lit 1))]
theorem atom0495Coded_decode : atom0495 = SparsePolynomial.decodeCubic 21 atom0495Coded := by decide +kernel
theorem atom0495Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33634828080000 : Int) atom0495Coded) := by
  have h := atom0495_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0495Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block007 : CoefficientMerge.Poly := [(nat_lit 523, Int.ofNat (nat_lit 14423604249600)), (nat_lit 524, Int.ofNat (nat_lit 11360537395200)), (nat_lit 529, Int.ofNat (nat_lit 7526146622400)), (nat_lit 530, Int.ofNat (nat_lit 14464310141952)), (nat_lit 531, Int.ofNat (nat_lit 14992217856000)), (nat_lit 532, Int.ofNat (nat_lit 17536417636608)), (nat_lit 533, Int.ofNat (nat_lit 18177375283200)), (nat_lit 534, Int.ofNat (nat_lit 18668342246400)), (nat_lit 535, Int.ofNat (nat_lit 19159309209600)), (nat_lit 536, Int.ofNat (nat_lit 19026429004800)), (nat_lit 537, Int.ofNat (nat_lit 15199948444800)), (nat_lit 538, Int.ofNat (nat_lit 14776849180800)), (nat_lit 539, Int.ofNat (nat_lit 15669867830400)), (nat_lit 540, Int.ofNat (nat_lit 24880813977600)), (nat_lit 541, Int.ofNat (nat_lit 18272069247600)), (nat_lit 542, Int.ofNat (nat_lit 22602534796800)), (nat_lit 543, Int.ofNat (nat_lit 20221399774800)), (nat_lit 544, Int.ofNat (nat_lit 21663695768400)), (nat_lit 545, Int.ofNat (nat_lit 17565700194000)), (nat_lit 551, Int.ofNat (nat_lit 11219811941376)), (nat_lit 552, Int.ofNat (nat_lit 19865648451456)), (nat_lit 553, Int.ofNat (nat_lit 19588073217408)), (nat_lit 554, Int.ofNat (nat_lit 20097013768704)), (nat_lit 555, Int.ofNat (nat_lit 21289155007104)), (nat_lit 556, Int.ofNat (nat_lit 21751611093504)), (nat_lit 557, Int.ofNat (nat_lit 21955062587904)), (nat_lit 558, Int.ofNat (nat_lit 18753888376704)), (nat_lit 559, Int.ofNat (nat_lit 18329339407104)), (nat_lit 560, Int.ofNat (nat_lit 19351865090304)), (nat_lit 561, Int.ofNat (nat_lit 29154774357504)), (nat_lit 562, Int.ofNat (nat_lit 22695246099072)), (nat_lit 563, Int.ofNat (nat_lit 27549158575104)), (nat_lit 564, Int.ofNat (nat_lit 25867921742208)), (nat_lit 565, Int.ofNat (nat_lit 27674310760320)), (nat_lit 566, Int.ofNat (nat_lit 23463825855168)), (nat_lit 573, Int.ofNat (nat_lit 14524199424000)), (nat_lit 574, Int.ofNat (nat_lit 25592052764160)), (nat_lit 575, Int.ofNat (nat_lit 23065383297600)), (nat_lit 576, Int.ofNat (nat_lit 22222382918400)), (nat_lit 577, Int.ofNat (nat_lit 22859770147200)), (nat_lit 578, Int.ofNat (nat_lit 22899764966400)), (nat_lit 579, Int.ofNat (nat_lit 20036978572800)), (nat_lit 580, Int.ofNat (nat_lit 19788810451200)), (nat_lit 581, Int.ofNat (nat_lit 20856760243200)), (nat_lit 582, Int.ofNat (nat_lit 31352628787200)), (nat_lit 583, Int.ofNat (nat_lit 25110779097600)), (nat_lit 584, Int.ofNat (nat_lit 30419676403200)), (nat_lit 585, Int.ofNat (nat_lit 30013882214400)), (nat_lit 586, Int.ofNat (nat_lit 33459931814400)), (nat_lit 587, Int.ofNat (nat_lit 32426062099200)), (nat_lit 595, Int.ofNat (nat_lit 16601669556480)), (nat_lit 596, Int.ofNat (nat_lit 29149185627360)), (nat_lit 597, Int.ofNat (nat_lit 27058453117056)), (nat_lit 598, Int.ofNat (nat_lit 27527674496256)), (nat_lit 599, Int.ofNat (nat_lit 27658517533056)), (nat_lit 600, Int.ofNat (nat_lit 24757072323456)), (nat_lit 601, Int.ofNat (nat_lit 24470245385856)), (nat_lit 602, Int.ofNat (nat_lit 25499536361856)), (nat_lit 603, Int.ofNat (nat_lit 35551425892608)), (nat_lit 604, Int.ofNat (nat_lit 29604979281024)), (nat_lit 605, Int.ofNat (nat_lit 35291136907008)), (nat_lit 606, Int.ofNat (nat_lit 34288248159360)), (nat_lit 607, Int.ofNat (nat_lit 34242389905920)), (nat_lit 608, Int.ofNat (nat_lit 32868397290240)), (nat_lit 617, Int.ofNat (nat_lit 18294922245600)), (nat_lit 618, Int.ofNat (nat_lit 32761969339680)), (nat_lit 619, Int.ofNat (nat_lit 31025713320000)), (nat_lit 620, Int.ofNat (nat_lit 30904307582400)), (nat_lit 621, Int.ofNat (nat_lit 27666530673600)), (nat_lit 622, Int.ofNat (nat_lit 27256961995200)), (nat_lit 623, Int.ofNat (nat_lit 28163511230400)), (nat_lit 624, Int.ofNat (nat_lit 37846980864000)), (nat_lit 625, Int.ofNat (nat_lit 32247885612600)), (nat_lit 626, Int.ofNat (nat_lit 38259355276800)), (nat_lit 627, Int.ofNat (nat_lit 37134500898600)), (nat_lit 628, Int.ofNat (nat_lit 34636711842600)), (nat_lit 629, Int.ofNat (nat_lit 34485486071400)), (nat_lit 639, Int.ofNat (nat_lit 20214453268800)), (nat_lit 640, Int.ofNat (nat_lit 36537606766080)), (nat_lit 641, Int.ofNat (nat_lit 33634828080000))]
def block007_data_flat000 : CoefficientMerge.Poly := [(nat_lit 523, Int.ofNat (nat_lit 14423604249600))]
theorem block007_data_flat000_step : block007_data_flat000 = (CoefficientMerge.scale (14423604249600 : Int) atom0416Coded) := by decide +kernel
theorem block007_data_flat000_original : block007_data_flat000 = (CoefficientMerge.scale (14423604249600 : Int) atom0416Coded) := by
  rw [block007_data_flat000_step]
def block007_data_flat001 : CoefficientMerge.Poly := [(nat_lit 524, Int.ofNat (nat_lit 11360537395200))]
theorem block007_data_flat001_step : block007_data_flat001 = (CoefficientMerge.scale (11360537395200 : Int) atom0417Coded) := by decide +kernel
theorem block007_data_flat001_original : block007_data_flat001 = (CoefficientMerge.scale (11360537395200 : Int) atom0417Coded) := by
  rw [block007_data_flat001_step]
def block007_data_flat002 : CoefficientMerge.Poly := [(nat_lit 523, Int.ofNat (nat_lit 14423604249600)), (nat_lit 524, Int.ofNat (nat_lit 11360537395200))]
theorem block007_data_flat002_step : block007_data_flat002 = (CoefficientMerge.fastMerge block007_data_flat000 block007_data_flat001) := by decide +kernel
theorem block007_data_flat002_original : block007_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14423604249600 : Int) atom0416Coded) (CoefficientMerge.scale (11360537395200 : Int) atom0417Coded)) := by
  rw [block007_data_flat002_step, block007_data_flat000_original, block007_data_flat001_original]
def block007_data_flat003 : CoefficientMerge.Poly := [(nat_lit 529, Int.ofNat (nat_lit 7526146622400))]
theorem block007_data_flat003_step : block007_data_flat003 = (CoefficientMerge.scale (7526146622400 : Int) atom0418Coded) := by decide +kernel
theorem block007_data_flat003_original : block007_data_flat003 = (CoefficientMerge.scale (7526146622400 : Int) atom0418Coded) := by
  rw [block007_data_flat003_step]
def block007_data_flat004 : CoefficientMerge.Poly := [(nat_lit 530, Int.ofNat (nat_lit 14464310141952))]
theorem block007_data_flat004_step : block007_data_flat004 = (CoefficientMerge.scale (14464310141952 : Int) atom0419Coded) := by decide +kernel
theorem block007_data_flat004_original : block007_data_flat004 = (CoefficientMerge.scale (14464310141952 : Int) atom0419Coded) := by
  rw [block007_data_flat004_step]
def block007_data_flat005 : CoefficientMerge.Poly := [(nat_lit 531, Int.ofNat (nat_lit 14992217856000))]
theorem block007_data_flat005_step : block007_data_flat005 = (CoefficientMerge.scale (14992217856000 : Int) atom0420Coded) := by decide +kernel
theorem block007_data_flat005_original : block007_data_flat005 = (CoefficientMerge.scale (14992217856000 : Int) atom0420Coded) := by
  rw [block007_data_flat005_step]
def block007_data_flat006 : CoefficientMerge.Poly := [(nat_lit 530, Int.ofNat (nat_lit 14464310141952)), (nat_lit 531, Int.ofNat (nat_lit 14992217856000))]
theorem block007_data_flat006_step : block007_data_flat006 = (CoefficientMerge.fastMerge block007_data_flat004 block007_data_flat005) := by decide +kernel
theorem block007_data_flat006_original : block007_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14464310141952 : Int) atom0419Coded) (CoefficientMerge.scale (14992217856000 : Int) atom0420Coded)) := by
  rw [block007_data_flat006_step, block007_data_flat004_original, block007_data_flat005_original]
def block007_data_flat007 : CoefficientMerge.Poly := [(nat_lit 529, Int.ofNat (nat_lit 7526146622400)), (nat_lit 530, Int.ofNat (nat_lit 14464310141952)), (nat_lit 531, Int.ofNat (nat_lit 14992217856000))]
theorem block007_data_flat007_step : block007_data_flat007 = (CoefficientMerge.fastMerge block007_data_flat003 block007_data_flat006) := by decide +kernel
theorem block007_data_flat007_original : block007_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7526146622400 : Int) atom0418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14464310141952 : Int) atom0419Coded) (CoefficientMerge.scale (14992217856000 : Int) atom0420Coded))) := by
  rw [block007_data_flat007_step, block007_data_flat003_original, block007_data_flat006_original]
def block007_data_flat008 : CoefficientMerge.Poly := [(nat_lit 523, Int.ofNat (nat_lit 14423604249600)), (nat_lit 524, Int.ofNat (nat_lit 11360537395200)), (nat_lit 529, Int.ofNat (nat_lit 7526146622400)), (nat_lit 530, Int.ofNat (nat_lit 14464310141952)), (nat_lit 531, Int.ofNat (nat_lit 14992217856000))]
theorem block007_data_flat008_step : block007_data_flat008 = (CoefficientMerge.fastMerge block007_data_flat002 block007_data_flat007) := by decide +kernel
theorem block007_data_flat008_original : block007_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14423604249600 : Int) atom0416Coded) (CoefficientMerge.scale (11360537395200 : Int) atom0417Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7526146622400 : Int) atom0418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14464310141952 : Int) atom0419Coded) (CoefficientMerge.scale (14992217856000 : Int) atom0420Coded)))) := by
  rw [block007_data_flat008_step, block007_data_flat002_original, block007_data_flat007_original]
def block007_data_flat009 : CoefficientMerge.Poly := [(nat_lit 532, Int.ofNat (nat_lit 17536417636608))]
theorem block007_data_flat009_step : block007_data_flat009 = (CoefficientMerge.scale (17536417636608 : Int) atom0421Coded) := by decide +kernel
theorem block007_data_flat009_original : block007_data_flat009 = (CoefficientMerge.scale (17536417636608 : Int) atom0421Coded) := by
  rw [block007_data_flat009_step]
def block007_data_flat010 : CoefficientMerge.Poly := [(nat_lit 533, Int.ofNat (nat_lit 18177375283200))]
theorem block007_data_flat010_step : block007_data_flat010 = (CoefficientMerge.scale (18177375283200 : Int) atom0422Coded) := by decide +kernel
theorem block007_data_flat010_original : block007_data_flat010 = (CoefficientMerge.scale (18177375283200 : Int) atom0422Coded) := by
  rw [block007_data_flat010_step]
def block007_data_flat011 : CoefficientMerge.Poly := [(nat_lit 532, Int.ofNat (nat_lit 17536417636608)), (nat_lit 533, Int.ofNat (nat_lit 18177375283200))]
theorem block007_data_flat011_step : block007_data_flat011 = (CoefficientMerge.fastMerge block007_data_flat009 block007_data_flat010) := by decide +kernel
theorem block007_data_flat011_original : block007_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17536417636608 : Int) atom0421Coded) (CoefficientMerge.scale (18177375283200 : Int) atom0422Coded)) := by
  rw [block007_data_flat011_step, block007_data_flat009_original, block007_data_flat010_original]
def block007_data_flat012 : CoefficientMerge.Poly := [(nat_lit 534, Int.ofNat (nat_lit 18668342246400))]
theorem block007_data_flat012_step : block007_data_flat012 = (CoefficientMerge.scale (18668342246400 : Int) atom0423Coded) := by decide +kernel
theorem block007_data_flat012_original : block007_data_flat012 = (CoefficientMerge.scale (18668342246400 : Int) atom0423Coded) := by
  rw [block007_data_flat012_step]
def block007_data_flat013 : CoefficientMerge.Poly := [(nat_lit 535, Int.ofNat (nat_lit 19159309209600))]
theorem block007_data_flat013_step : block007_data_flat013 = (CoefficientMerge.scale (19159309209600 : Int) atom0424Coded) := by decide +kernel
theorem block007_data_flat013_original : block007_data_flat013 = (CoefficientMerge.scale (19159309209600 : Int) atom0424Coded) := by
  rw [block007_data_flat013_step]
def block007_data_flat014 : CoefficientMerge.Poly := [(nat_lit 536, Int.ofNat (nat_lit 19026429004800))]
theorem block007_data_flat014_step : block007_data_flat014 = (CoefficientMerge.scale (19026429004800 : Int) atom0425Coded) := by decide +kernel
theorem block007_data_flat014_original : block007_data_flat014 = (CoefficientMerge.scale (19026429004800 : Int) atom0425Coded) := by
  rw [block007_data_flat014_step]
def block007_data_flat015 : CoefficientMerge.Poly := [(nat_lit 535, Int.ofNat (nat_lit 19159309209600)), (nat_lit 536, Int.ofNat (nat_lit 19026429004800))]
theorem block007_data_flat015_step : block007_data_flat015 = (CoefficientMerge.fastMerge block007_data_flat013 block007_data_flat014) := by decide +kernel
theorem block007_data_flat015_original : block007_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19159309209600 : Int) atom0424Coded) (CoefficientMerge.scale (19026429004800 : Int) atom0425Coded)) := by
  rw [block007_data_flat015_step, block007_data_flat013_original, block007_data_flat014_original]
def block007_data_flat016 : CoefficientMerge.Poly := [(nat_lit 534, Int.ofNat (nat_lit 18668342246400)), (nat_lit 535, Int.ofNat (nat_lit 19159309209600)), (nat_lit 536, Int.ofNat (nat_lit 19026429004800))]
theorem block007_data_flat016_step : block007_data_flat016 = (CoefficientMerge.fastMerge block007_data_flat012 block007_data_flat015) := by decide +kernel
theorem block007_data_flat016_original : block007_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18668342246400 : Int) atom0423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19159309209600 : Int) atom0424Coded) (CoefficientMerge.scale (19026429004800 : Int) atom0425Coded))) := by
  rw [block007_data_flat016_step, block007_data_flat012_original, block007_data_flat015_original]
def block007_data_flat017 : CoefficientMerge.Poly := [(nat_lit 532, Int.ofNat (nat_lit 17536417636608)), (nat_lit 533, Int.ofNat (nat_lit 18177375283200)), (nat_lit 534, Int.ofNat (nat_lit 18668342246400)), (nat_lit 535, Int.ofNat (nat_lit 19159309209600)), (nat_lit 536, Int.ofNat (nat_lit 19026429004800))]
theorem block007_data_flat017_step : block007_data_flat017 = (CoefficientMerge.fastMerge block007_data_flat011 block007_data_flat016) := by decide +kernel
theorem block007_data_flat017_original : block007_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17536417636608 : Int) atom0421Coded) (CoefficientMerge.scale (18177375283200 : Int) atom0422Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18668342246400 : Int) atom0423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19159309209600 : Int) atom0424Coded) (CoefficientMerge.scale (19026429004800 : Int) atom0425Coded)))) := by
  rw [block007_data_flat017_step, block007_data_flat011_original, block007_data_flat016_original]
def block007_data_flat018 : CoefficientMerge.Poly := [(nat_lit 523, Int.ofNat (nat_lit 14423604249600)), (nat_lit 524, Int.ofNat (nat_lit 11360537395200)), (nat_lit 529, Int.ofNat (nat_lit 7526146622400)), (nat_lit 530, Int.ofNat (nat_lit 14464310141952)), (nat_lit 531, Int.ofNat (nat_lit 14992217856000)), (nat_lit 532, Int.ofNat (nat_lit 17536417636608)), (nat_lit 533, Int.ofNat (nat_lit 18177375283200)), (nat_lit 534, Int.ofNat (nat_lit 18668342246400)), (nat_lit 535, Int.ofNat (nat_lit 19159309209600)), (nat_lit 536, Int.ofNat (nat_lit 19026429004800))]
theorem block007_data_flat018_step : block007_data_flat018 = (CoefficientMerge.fastMerge block007_data_flat008 block007_data_flat017) := by decide +kernel
theorem block007_data_flat018_original : block007_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14423604249600 : Int) atom0416Coded) (CoefficientMerge.scale (11360537395200 : Int) atom0417Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7526146622400 : Int) atom0418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14464310141952 : Int) atom0419Coded) (CoefficientMerge.scale (14992217856000 : Int) atom0420Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17536417636608 : Int) atom0421Coded) (CoefficientMerge.scale (18177375283200 : Int) atom0422Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18668342246400 : Int) atom0423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19159309209600 : Int) atom0424Coded) (CoefficientMerge.scale (19026429004800 : Int) atom0425Coded))))) := by
  rw [block007_data_flat018_step, block007_data_flat008_original, block007_data_flat017_original]
def block007_data_flat019 : CoefficientMerge.Poly := [(nat_lit 537, Int.ofNat (nat_lit 15199948444800))]
theorem block007_data_flat019_step : block007_data_flat019 = (CoefficientMerge.scale (15199948444800 : Int) atom0426Coded) := by decide +kernel
theorem block007_data_flat019_original : block007_data_flat019 = (CoefficientMerge.scale (15199948444800 : Int) atom0426Coded) := by
  rw [block007_data_flat019_step]
def block007_data_flat020 : CoefficientMerge.Poly := [(nat_lit 538, Int.ofNat (nat_lit 14776849180800))]
theorem block007_data_flat020_step : block007_data_flat020 = (CoefficientMerge.scale (14776849180800 : Int) atom0427Coded) := by decide +kernel
theorem block007_data_flat020_original : block007_data_flat020 = (CoefficientMerge.scale (14776849180800 : Int) atom0427Coded) := by
  rw [block007_data_flat020_step]
def block007_data_flat021 : CoefficientMerge.Poly := [(nat_lit 537, Int.ofNat (nat_lit 15199948444800)), (nat_lit 538, Int.ofNat (nat_lit 14776849180800))]
theorem block007_data_flat021_step : block007_data_flat021 = (CoefficientMerge.fastMerge block007_data_flat019 block007_data_flat020) := by decide +kernel
theorem block007_data_flat021_original : block007_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15199948444800 : Int) atom0426Coded) (CoefficientMerge.scale (14776849180800 : Int) atom0427Coded)) := by
  rw [block007_data_flat021_step, block007_data_flat019_original, block007_data_flat020_original]
def block007_data_flat022 : CoefficientMerge.Poly := [(nat_lit 539, Int.ofNat (nat_lit 15669867830400))]
theorem block007_data_flat022_step : block007_data_flat022 = (CoefficientMerge.scale (15669867830400 : Int) atom0428Coded) := by decide +kernel
theorem block007_data_flat022_original : block007_data_flat022 = (CoefficientMerge.scale (15669867830400 : Int) atom0428Coded) := by
  rw [block007_data_flat022_step]
def block007_data_flat023 : CoefficientMerge.Poly := [(nat_lit 540, Int.ofNat (nat_lit 24880813977600))]
theorem block007_data_flat023_step : block007_data_flat023 = (CoefficientMerge.scale (24880813977600 : Int) atom0429Coded) := by decide +kernel
theorem block007_data_flat023_original : block007_data_flat023 = (CoefficientMerge.scale (24880813977600 : Int) atom0429Coded) := by
  rw [block007_data_flat023_step]
def block007_data_flat024 : CoefficientMerge.Poly := [(nat_lit 541, Int.ofNat (nat_lit 18272069247600))]
theorem block007_data_flat024_step : block007_data_flat024 = (CoefficientMerge.scale (18272069247600 : Int) atom0430Coded) := by decide +kernel
theorem block007_data_flat024_original : block007_data_flat024 = (CoefficientMerge.scale (18272069247600 : Int) atom0430Coded) := by
  rw [block007_data_flat024_step]
def block007_data_flat025 : CoefficientMerge.Poly := [(nat_lit 540, Int.ofNat (nat_lit 24880813977600)), (nat_lit 541, Int.ofNat (nat_lit 18272069247600))]
theorem block007_data_flat025_step : block007_data_flat025 = (CoefficientMerge.fastMerge block007_data_flat023 block007_data_flat024) := by decide +kernel
theorem block007_data_flat025_original : block007_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24880813977600 : Int) atom0429Coded) (CoefficientMerge.scale (18272069247600 : Int) atom0430Coded)) := by
  rw [block007_data_flat025_step, block007_data_flat023_original, block007_data_flat024_original]
def block007_data_flat026 : CoefficientMerge.Poly := [(nat_lit 539, Int.ofNat (nat_lit 15669867830400)), (nat_lit 540, Int.ofNat (nat_lit 24880813977600)), (nat_lit 541, Int.ofNat (nat_lit 18272069247600))]
theorem block007_data_flat026_step : block007_data_flat026 = (CoefficientMerge.fastMerge block007_data_flat022 block007_data_flat025) := by decide +kernel
theorem block007_data_flat026_original : block007_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15669867830400 : Int) atom0428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24880813977600 : Int) atom0429Coded) (CoefficientMerge.scale (18272069247600 : Int) atom0430Coded))) := by
  rw [block007_data_flat026_step, block007_data_flat022_original, block007_data_flat025_original]
def block007_data_flat027 : CoefficientMerge.Poly := [(nat_lit 537, Int.ofNat (nat_lit 15199948444800)), (nat_lit 538, Int.ofNat (nat_lit 14776849180800)), (nat_lit 539, Int.ofNat (nat_lit 15669867830400)), (nat_lit 540, Int.ofNat (nat_lit 24880813977600)), (nat_lit 541, Int.ofNat (nat_lit 18272069247600))]
theorem block007_data_flat027_step : block007_data_flat027 = (CoefficientMerge.fastMerge block007_data_flat021 block007_data_flat026) := by decide +kernel
theorem block007_data_flat027_original : block007_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15199948444800 : Int) atom0426Coded) (CoefficientMerge.scale (14776849180800 : Int) atom0427Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15669867830400 : Int) atom0428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24880813977600 : Int) atom0429Coded) (CoefficientMerge.scale (18272069247600 : Int) atom0430Coded)))) := by
  rw [block007_data_flat027_step, block007_data_flat021_original, block007_data_flat026_original]
def block007_data_flat028 : CoefficientMerge.Poly := [(nat_lit 542, Int.ofNat (nat_lit 22602534796800))]
theorem block007_data_flat028_step : block007_data_flat028 = (CoefficientMerge.scale (22602534796800 : Int) atom0431Coded) := by decide +kernel
theorem block007_data_flat028_original : block007_data_flat028 = (CoefficientMerge.scale (22602534796800 : Int) atom0431Coded) := by
  rw [block007_data_flat028_step]
def block007_data_flat029 : CoefficientMerge.Poly := [(nat_lit 543, Int.ofNat (nat_lit 20221399774800))]
theorem block007_data_flat029_step : block007_data_flat029 = (CoefficientMerge.scale (20221399774800 : Int) atom0432Coded) := by decide +kernel
theorem block007_data_flat029_original : block007_data_flat029 = (CoefficientMerge.scale (20221399774800 : Int) atom0432Coded) := by
  rw [block007_data_flat029_step]
def block007_data_flat030 : CoefficientMerge.Poly := [(nat_lit 542, Int.ofNat (nat_lit 22602534796800)), (nat_lit 543, Int.ofNat (nat_lit 20221399774800))]
theorem block007_data_flat030_step : block007_data_flat030 = (CoefficientMerge.fastMerge block007_data_flat028 block007_data_flat029) := by decide +kernel
theorem block007_data_flat030_original : block007_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22602534796800 : Int) atom0431Coded) (CoefficientMerge.scale (20221399774800 : Int) atom0432Coded)) := by
  rw [block007_data_flat030_step, block007_data_flat028_original, block007_data_flat029_original]
def block007_data_flat031 : CoefficientMerge.Poly := [(nat_lit 544, Int.ofNat (nat_lit 21663695768400))]
theorem block007_data_flat031_step : block007_data_flat031 = (CoefficientMerge.scale (21663695768400 : Int) atom0433Coded) := by decide +kernel
theorem block007_data_flat031_original : block007_data_flat031 = (CoefficientMerge.scale (21663695768400 : Int) atom0433Coded) := by
  rw [block007_data_flat031_step]
def block007_data_flat032 : CoefficientMerge.Poly := [(nat_lit 545, Int.ofNat (nat_lit 17565700194000))]
theorem block007_data_flat032_step : block007_data_flat032 = (CoefficientMerge.scale (17565700194000 : Int) atom0434Coded) := by decide +kernel
theorem block007_data_flat032_original : block007_data_flat032 = (CoefficientMerge.scale (17565700194000 : Int) atom0434Coded) := by
  rw [block007_data_flat032_step]
def block007_data_flat033 : CoefficientMerge.Poly := [(nat_lit 551, Int.ofNat (nat_lit 11219811941376))]
theorem block007_data_flat033_step : block007_data_flat033 = (CoefficientMerge.scale (11219811941376 : Int) atom0435Coded) := by decide +kernel
theorem block007_data_flat033_original : block007_data_flat033 = (CoefficientMerge.scale (11219811941376 : Int) atom0435Coded) := by
  rw [block007_data_flat033_step]
def block007_data_flat034 : CoefficientMerge.Poly := [(nat_lit 545, Int.ofNat (nat_lit 17565700194000)), (nat_lit 551, Int.ofNat (nat_lit 11219811941376))]
theorem block007_data_flat034_step : block007_data_flat034 = (CoefficientMerge.fastMerge block007_data_flat032 block007_data_flat033) := by decide +kernel
theorem block007_data_flat034_original : block007_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17565700194000 : Int) atom0434Coded) (CoefficientMerge.scale (11219811941376 : Int) atom0435Coded)) := by
  rw [block007_data_flat034_step, block007_data_flat032_original, block007_data_flat033_original]
def block007_data_flat035 : CoefficientMerge.Poly := [(nat_lit 544, Int.ofNat (nat_lit 21663695768400)), (nat_lit 545, Int.ofNat (nat_lit 17565700194000)), (nat_lit 551, Int.ofNat (nat_lit 11219811941376))]
theorem block007_data_flat035_step : block007_data_flat035 = (CoefficientMerge.fastMerge block007_data_flat031 block007_data_flat034) := by decide +kernel
theorem block007_data_flat035_original : block007_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21663695768400 : Int) atom0433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17565700194000 : Int) atom0434Coded) (CoefficientMerge.scale (11219811941376 : Int) atom0435Coded))) := by
  rw [block007_data_flat035_step, block007_data_flat031_original, block007_data_flat034_original]
def block007_data_flat036 : CoefficientMerge.Poly := [(nat_lit 542, Int.ofNat (nat_lit 22602534796800)), (nat_lit 543, Int.ofNat (nat_lit 20221399774800)), (nat_lit 544, Int.ofNat (nat_lit 21663695768400)), (nat_lit 545, Int.ofNat (nat_lit 17565700194000)), (nat_lit 551, Int.ofNat (nat_lit 11219811941376))]
theorem block007_data_flat036_step : block007_data_flat036 = (CoefficientMerge.fastMerge block007_data_flat030 block007_data_flat035) := by decide +kernel
theorem block007_data_flat036_original : block007_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22602534796800 : Int) atom0431Coded) (CoefficientMerge.scale (20221399774800 : Int) atom0432Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21663695768400 : Int) atom0433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17565700194000 : Int) atom0434Coded) (CoefficientMerge.scale (11219811941376 : Int) atom0435Coded)))) := by
  rw [block007_data_flat036_step, block007_data_flat030_original, block007_data_flat035_original]
def block007_data_flat037 : CoefficientMerge.Poly := [(nat_lit 537, Int.ofNat (nat_lit 15199948444800)), (nat_lit 538, Int.ofNat (nat_lit 14776849180800)), (nat_lit 539, Int.ofNat (nat_lit 15669867830400)), (nat_lit 540, Int.ofNat (nat_lit 24880813977600)), (nat_lit 541, Int.ofNat (nat_lit 18272069247600)), (nat_lit 542, Int.ofNat (nat_lit 22602534796800)), (nat_lit 543, Int.ofNat (nat_lit 20221399774800)), (nat_lit 544, Int.ofNat (nat_lit 21663695768400)), (nat_lit 545, Int.ofNat (nat_lit 17565700194000)), (nat_lit 551, Int.ofNat (nat_lit 11219811941376))]
theorem block007_data_flat037_step : block007_data_flat037 = (CoefficientMerge.fastMerge block007_data_flat027 block007_data_flat036) := by decide +kernel
theorem block007_data_flat037_original : block007_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15199948444800 : Int) atom0426Coded) (CoefficientMerge.scale (14776849180800 : Int) atom0427Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15669867830400 : Int) atom0428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24880813977600 : Int) atom0429Coded) (CoefficientMerge.scale (18272069247600 : Int) atom0430Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22602534796800 : Int) atom0431Coded) (CoefficientMerge.scale (20221399774800 : Int) atom0432Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21663695768400 : Int) atom0433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17565700194000 : Int) atom0434Coded) (CoefficientMerge.scale (11219811941376 : Int) atom0435Coded))))) := by
  rw [block007_data_flat037_step, block007_data_flat027_original, block007_data_flat036_original]
def block007_data_flat038 : CoefficientMerge.Poly := [(nat_lit 523, Int.ofNat (nat_lit 14423604249600)), (nat_lit 524, Int.ofNat (nat_lit 11360537395200)), (nat_lit 529, Int.ofNat (nat_lit 7526146622400)), (nat_lit 530, Int.ofNat (nat_lit 14464310141952)), (nat_lit 531, Int.ofNat (nat_lit 14992217856000)), (nat_lit 532, Int.ofNat (nat_lit 17536417636608)), (nat_lit 533, Int.ofNat (nat_lit 18177375283200)), (nat_lit 534, Int.ofNat (nat_lit 18668342246400)), (nat_lit 535, Int.ofNat (nat_lit 19159309209600)), (nat_lit 536, Int.ofNat (nat_lit 19026429004800)), (nat_lit 537, Int.ofNat (nat_lit 15199948444800)), (nat_lit 538, Int.ofNat (nat_lit 14776849180800)), (nat_lit 539, Int.ofNat (nat_lit 15669867830400)), (nat_lit 540, Int.ofNat (nat_lit 24880813977600)), (nat_lit 541, Int.ofNat (nat_lit 18272069247600)), (nat_lit 542, Int.ofNat (nat_lit 22602534796800)), (nat_lit 543, Int.ofNat (nat_lit 20221399774800)), (nat_lit 544, Int.ofNat (nat_lit 21663695768400)), (nat_lit 545, Int.ofNat (nat_lit 17565700194000)), (nat_lit 551, Int.ofNat (nat_lit 11219811941376))]
theorem block007_data_flat038_step : block007_data_flat038 = (CoefficientMerge.fastMerge block007_data_flat018 block007_data_flat037) := by decide +kernel
theorem block007_data_flat038_original : block007_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14423604249600 : Int) atom0416Coded) (CoefficientMerge.scale (11360537395200 : Int) atom0417Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7526146622400 : Int) atom0418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14464310141952 : Int) atom0419Coded) (CoefficientMerge.scale (14992217856000 : Int) atom0420Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17536417636608 : Int) atom0421Coded) (CoefficientMerge.scale (18177375283200 : Int) atom0422Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18668342246400 : Int) atom0423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19159309209600 : Int) atom0424Coded) (CoefficientMerge.scale (19026429004800 : Int) atom0425Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15199948444800 : Int) atom0426Coded) (CoefficientMerge.scale (14776849180800 : Int) atom0427Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15669867830400 : Int) atom0428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24880813977600 : Int) atom0429Coded) (CoefficientMerge.scale (18272069247600 : Int) atom0430Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22602534796800 : Int) atom0431Coded) (CoefficientMerge.scale (20221399774800 : Int) atom0432Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21663695768400 : Int) atom0433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17565700194000 : Int) atom0434Coded) (CoefficientMerge.scale (11219811941376 : Int) atom0435Coded)))))) := by
  rw [block007_data_flat038_step, block007_data_flat018_original, block007_data_flat037_original]
def block007_data_flat039 : CoefficientMerge.Poly := [(nat_lit 552, Int.ofNat (nat_lit 19865648451456))]
theorem block007_data_flat039_step : block007_data_flat039 = (CoefficientMerge.scale (19865648451456 : Int) atom0436Coded) := by decide +kernel
theorem block007_data_flat039_original : block007_data_flat039 = (CoefficientMerge.scale (19865648451456 : Int) atom0436Coded) := by
  rw [block007_data_flat039_step]
def block007_data_flat040 : CoefficientMerge.Poly := [(nat_lit 553, Int.ofNat (nat_lit 19588073217408))]
theorem block007_data_flat040_step : block007_data_flat040 = (CoefficientMerge.scale (19588073217408 : Int) atom0437Coded) := by decide +kernel
theorem block007_data_flat040_original : block007_data_flat040 = (CoefficientMerge.scale (19588073217408 : Int) atom0437Coded) := by
  rw [block007_data_flat040_step]
def block007_data_flat041 : CoefficientMerge.Poly := [(nat_lit 552, Int.ofNat (nat_lit 19865648451456)), (nat_lit 553, Int.ofNat (nat_lit 19588073217408))]
theorem block007_data_flat041_step : block007_data_flat041 = (CoefficientMerge.fastMerge block007_data_flat039 block007_data_flat040) := by decide +kernel
theorem block007_data_flat041_original : block007_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19865648451456 : Int) atom0436Coded) (CoefficientMerge.scale (19588073217408 : Int) atom0437Coded)) := by
  rw [block007_data_flat041_step, block007_data_flat039_original, block007_data_flat040_original]
def block007_data_flat042 : CoefficientMerge.Poly := [(nat_lit 554, Int.ofNat (nat_lit 20097013768704))]
theorem block007_data_flat042_step : block007_data_flat042 = (CoefficientMerge.scale (20097013768704 : Int) atom0438Coded) := by decide +kernel
theorem block007_data_flat042_original : block007_data_flat042 = (CoefficientMerge.scale (20097013768704 : Int) atom0438Coded) := by
  rw [block007_data_flat042_step]
def block007_data_flat043 : CoefficientMerge.Poly := [(nat_lit 555, Int.ofNat (nat_lit 21289155007104))]
theorem block007_data_flat043_step : block007_data_flat043 = (CoefficientMerge.scale (21289155007104 : Int) atom0439Coded) := by decide +kernel
theorem block007_data_flat043_original : block007_data_flat043 = (CoefficientMerge.scale (21289155007104 : Int) atom0439Coded) := by
  rw [block007_data_flat043_step]
def block007_data_flat044 : CoefficientMerge.Poly := [(nat_lit 556, Int.ofNat (nat_lit 21751611093504))]
theorem block007_data_flat044_step : block007_data_flat044 = (CoefficientMerge.scale (21751611093504 : Int) atom0440Coded) := by decide +kernel
theorem block007_data_flat044_original : block007_data_flat044 = (CoefficientMerge.scale (21751611093504 : Int) atom0440Coded) := by
  rw [block007_data_flat044_step]
def block007_data_flat045 : CoefficientMerge.Poly := [(nat_lit 555, Int.ofNat (nat_lit 21289155007104)), (nat_lit 556, Int.ofNat (nat_lit 21751611093504))]
theorem block007_data_flat045_step : block007_data_flat045 = (CoefficientMerge.fastMerge block007_data_flat043 block007_data_flat044) := by decide +kernel
theorem block007_data_flat045_original : block007_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21289155007104 : Int) atom0439Coded) (CoefficientMerge.scale (21751611093504 : Int) atom0440Coded)) := by
  rw [block007_data_flat045_step, block007_data_flat043_original, block007_data_flat044_original]
def block007_data_flat046 : CoefficientMerge.Poly := [(nat_lit 554, Int.ofNat (nat_lit 20097013768704)), (nat_lit 555, Int.ofNat (nat_lit 21289155007104)), (nat_lit 556, Int.ofNat (nat_lit 21751611093504))]
theorem block007_data_flat046_step : block007_data_flat046 = (CoefficientMerge.fastMerge block007_data_flat042 block007_data_flat045) := by decide +kernel
theorem block007_data_flat046_original : block007_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20097013768704 : Int) atom0438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21289155007104 : Int) atom0439Coded) (CoefficientMerge.scale (21751611093504 : Int) atom0440Coded))) := by
  rw [block007_data_flat046_step, block007_data_flat042_original, block007_data_flat045_original]
def block007_data_flat047 : CoefficientMerge.Poly := [(nat_lit 552, Int.ofNat (nat_lit 19865648451456)), (nat_lit 553, Int.ofNat (nat_lit 19588073217408)), (nat_lit 554, Int.ofNat (nat_lit 20097013768704)), (nat_lit 555, Int.ofNat (nat_lit 21289155007104)), (nat_lit 556, Int.ofNat (nat_lit 21751611093504))]
theorem block007_data_flat047_step : block007_data_flat047 = (CoefficientMerge.fastMerge block007_data_flat041 block007_data_flat046) := by decide +kernel
theorem block007_data_flat047_original : block007_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19865648451456 : Int) atom0436Coded) (CoefficientMerge.scale (19588073217408 : Int) atom0437Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20097013768704 : Int) atom0438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21289155007104 : Int) atom0439Coded) (CoefficientMerge.scale (21751611093504 : Int) atom0440Coded)))) := by
  rw [block007_data_flat047_step, block007_data_flat041_original, block007_data_flat046_original]
def block007_data_flat048 : CoefficientMerge.Poly := [(nat_lit 557, Int.ofNat (nat_lit 21955062587904))]
theorem block007_data_flat048_step : block007_data_flat048 = (CoefficientMerge.scale (21955062587904 : Int) atom0441Coded) := by decide +kernel
theorem block007_data_flat048_original : block007_data_flat048 = (CoefficientMerge.scale (21955062587904 : Int) atom0441Coded) := by
  rw [block007_data_flat048_step]
def block007_data_flat049 : CoefficientMerge.Poly := [(nat_lit 558, Int.ofNat (nat_lit 18753888376704))]
theorem block007_data_flat049_step : block007_data_flat049 = (CoefficientMerge.scale (18753888376704 : Int) atom0442Coded) := by decide +kernel
theorem block007_data_flat049_original : block007_data_flat049 = (CoefficientMerge.scale (18753888376704 : Int) atom0442Coded) := by
  rw [block007_data_flat049_step]
def block007_data_flat050 : CoefficientMerge.Poly := [(nat_lit 557, Int.ofNat (nat_lit 21955062587904)), (nat_lit 558, Int.ofNat (nat_lit 18753888376704))]
theorem block007_data_flat050_step : block007_data_flat050 = (CoefficientMerge.fastMerge block007_data_flat048 block007_data_flat049) := by decide +kernel
theorem block007_data_flat050_original : block007_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21955062587904 : Int) atom0441Coded) (CoefficientMerge.scale (18753888376704 : Int) atom0442Coded)) := by
  rw [block007_data_flat050_step, block007_data_flat048_original, block007_data_flat049_original]
def block007_data_flat051 : CoefficientMerge.Poly := [(nat_lit 559, Int.ofNat (nat_lit 18329339407104))]
theorem block007_data_flat051_step : block007_data_flat051 = (CoefficientMerge.scale (18329339407104 : Int) atom0443Coded) := by decide +kernel
theorem block007_data_flat051_original : block007_data_flat051 = (CoefficientMerge.scale (18329339407104 : Int) atom0443Coded) := by
  rw [block007_data_flat051_step]
def block007_data_flat052 : CoefficientMerge.Poly := [(nat_lit 560, Int.ofNat (nat_lit 19351865090304))]
theorem block007_data_flat052_step : block007_data_flat052 = (CoefficientMerge.scale (19351865090304 : Int) atom0444Coded) := by decide +kernel
theorem block007_data_flat052_original : block007_data_flat052 = (CoefficientMerge.scale (19351865090304 : Int) atom0444Coded) := by
  rw [block007_data_flat052_step]
def block007_data_flat053 : CoefficientMerge.Poly := [(nat_lit 561, Int.ofNat (nat_lit 29154774357504))]
theorem block007_data_flat053_step : block007_data_flat053 = (CoefficientMerge.scale (29154774357504 : Int) atom0445Coded) := by decide +kernel
theorem block007_data_flat053_original : block007_data_flat053 = (CoefficientMerge.scale (29154774357504 : Int) atom0445Coded) := by
  rw [block007_data_flat053_step]
def block007_data_flat054 : CoefficientMerge.Poly := [(nat_lit 560, Int.ofNat (nat_lit 19351865090304)), (nat_lit 561, Int.ofNat (nat_lit 29154774357504))]
theorem block007_data_flat054_step : block007_data_flat054 = (CoefficientMerge.fastMerge block007_data_flat052 block007_data_flat053) := by decide +kernel
theorem block007_data_flat054_original : block007_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19351865090304 : Int) atom0444Coded) (CoefficientMerge.scale (29154774357504 : Int) atom0445Coded)) := by
  rw [block007_data_flat054_step, block007_data_flat052_original, block007_data_flat053_original]
def block007_data_flat055 : CoefficientMerge.Poly := [(nat_lit 559, Int.ofNat (nat_lit 18329339407104)), (nat_lit 560, Int.ofNat (nat_lit 19351865090304)), (nat_lit 561, Int.ofNat (nat_lit 29154774357504))]
theorem block007_data_flat055_step : block007_data_flat055 = (CoefficientMerge.fastMerge block007_data_flat051 block007_data_flat054) := by decide +kernel
theorem block007_data_flat055_original : block007_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18329339407104 : Int) atom0443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19351865090304 : Int) atom0444Coded) (CoefficientMerge.scale (29154774357504 : Int) atom0445Coded))) := by
  rw [block007_data_flat055_step, block007_data_flat051_original, block007_data_flat054_original]
def block007_data_flat056 : CoefficientMerge.Poly := [(nat_lit 557, Int.ofNat (nat_lit 21955062587904)), (nat_lit 558, Int.ofNat (nat_lit 18753888376704)), (nat_lit 559, Int.ofNat (nat_lit 18329339407104)), (nat_lit 560, Int.ofNat (nat_lit 19351865090304)), (nat_lit 561, Int.ofNat (nat_lit 29154774357504))]
theorem block007_data_flat056_step : block007_data_flat056 = (CoefficientMerge.fastMerge block007_data_flat050 block007_data_flat055) := by decide +kernel
theorem block007_data_flat056_original : block007_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21955062587904 : Int) atom0441Coded) (CoefficientMerge.scale (18753888376704 : Int) atom0442Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18329339407104 : Int) atom0443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19351865090304 : Int) atom0444Coded) (CoefficientMerge.scale (29154774357504 : Int) atom0445Coded)))) := by
  rw [block007_data_flat056_step, block007_data_flat050_original, block007_data_flat055_original]
def block007_data_flat057 : CoefficientMerge.Poly := [(nat_lit 552, Int.ofNat (nat_lit 19865648451456)), (nat_lit 553, Int.ofNat (nat_lit 19588073217408)), (nat_lit 554, Int.ofNat (nat_lit 20097013768704)), (nat_lit 555, Int.ofNat (nat_lit 21289155007104)), (nat_lit 556, Int.ofNat (nat_lit 21751611093504)), (nat_lit 557, Int.ofNat (nat_lit 21955062587904)), (nat_lit 558, Int.ofNat (nat_lit 18753888376704)), (nat_lit 559, Int.ofNat (nat_lit 18329339407104)), (nat_lit 560, Int.ofNat (nat_lit 19351865090304)), (nat_lit 561, Int.ofNat (nat_lit 29154774357504))]
theorem block007_data_flat057_step : block007_data_flat057 = (CoefficientMerge.fastMerge block007_data_flat047 block007_data_flat056) := by decide +kernel
theorem block007_data_flat057_original : block007_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19865648451456 : Int) atom0436Coded) (CoefficientMerge.scale (19588073217408 : Int) atom0437Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20097013768704 : Int) atom0438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21289155007104 : Int) atom0439Coded) (CoefficientMerge.scale (21751611093504 : Int) atom0440Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21955062587904 : Int) atom0441Coded) (CoefficientMerge.scale (18753888376704 : Int) atom0442Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18329339407104 : Int) atom0443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19351865090304 : Int) atom0444Coded) (CoefficientMerge.scale (29154774357504 : Int) atom0445Coded))))) := by
  rw [block007_data_flat057_step, block007_data_flat047_original, block007_data_flat056_original]
def block007_data_flat058 : CoefficientMerge.Poly := [(nat_lit 562, Int.ofNat (nat_lit 22695246099072))]
theorem block007_data_flat058_step : block007_data_flat058 = (CoefficientMerge.scale (22695246099072 : Int) atom0446Coded) := by decide +kernel
theorem block007_data_flat058_original : block007_data_flat058 = (CoefficientMerge.scale (22695246099072 : Int) atom0446Coded) := by
  rw [block007_data_flat058_step]
def block007_data_flat059 : CoefficientMerge.Poly := [(nat_lit 563, Int.ofNat (nat_lit 27549158575104))]
theorem block007_data_flat059_step : block007_data_flat059 = (CoefficientMerge.scale (27549158575104 : Int) atom0447Coded) := by decide +kernel
theorem block007_data_flat059_original : block007_data_flat059 = (CoefficientMerge.scale (27549158575104 : Int) atom0447Coded) := by
  rw [block007_data_flat059_step]
def block007_data_flat060 : CoefficientMerge.Poly := [(nat_lit 562, Int.ofNat (nat_lit 22695246099072)), (nat_lit 563, Int.ofNat (nat_lit 27549158575104))]
theorem block007_data_flat060_step : block007_data_flat060 = (CoefficientMerge.fastMerge block007_data_flat058 block007_data_flat059) := by decide +kernel
theorem block007_data_flat060_original : block007_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22695246099072 : Int) atom0446Coded) (CoefficientMerge.scale (27549158575104 : Int) atom0447Coded)) := by
  rw [block007_data_flat060_step, block007_data_flat058_original, block007_data_flat059_original]
def block007_data_flat061 : CoefficientMerge.Poly := [(nat_lit 564, Int.ofNat (nat_lit 25867921742208))]
theorem block007_data_flat061_step : block007_data_flat061 = (CoefficientMerge.scale (25867921742208 : Int) atom0448Coded) := by decide +kernel
theorem block007_data_flat061_original : block007_data_flat061 = (CoefficientMerge.scale (25867921742208 : Int) atom0448Coded) := by
  rw [block007_data_flat061_step]
def block007_data_flat062 : CoefficientMerge.Poly := [(nat_lit 565, Int.ofNat (nat_lit 27674310760320))]
theorem block007_data_flat062_step : block007_data_flat062 = (CoefficientMerge.scale (27674310760320 : Int) atom0449Coded) := by decide +kernel
theorem block007_data_flat062_original : block007_data_flat062 = (CoefficientMerge.scale (27674310760320 : Int) atom0449Coded) := by
  rw [block007_data_flat062_step]
def block007_data_flat063 : CoefficientMerge.Poly := [(nat_lit 566, Int.ofNat (nat_lit 23463825855168))]
theorem block007_data_flat063_step : block007_data_flat063 = (CoefficientMerge.scale (23463825855168 : Int) atom0450Coded) := by decide +kernel
theorem block007_data_flat063_original : block007_data_flat063 = (CoefficientMerge.scale (23463825855168 : Int) atom0450Coded) := by
  rw [block007_data_flat063_step]
def block007_data_flat064 : CoefficientMerge.Poly := [(nat_lit 565, Int.ofNat (nat_lit 27674310760320)), (nat_lit 566, Int.ofNat (nat_lit 23463825855168))]
theorem block007_data_flat064_step : block007_data_flat064 = (CoefficientMerge.fastMerge block007_data_flat062 block007_data_flat063) := by decide +kernel
theorem block007_data_flat064_original : block007_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27674310760320 : Int) atom0449Coded) (CoefficientMerge.scale (23463825855168 : Int) atom0450Coded)) := by
  rw [block007_data_flat064_step, block007_data_flat062_original, block007_data_flat063_original]
def block007_data_flat065 : CoefficientMerge.Poly := [(nat_lit 564, Int.ofNat (nat_lit 25867921742208)), (nat_lit 565, Int.ofNat (nat_lit 27674310760320)), (nat_lit 566, Int.ofNat (nat_lit 23463825855168))]
theorem block007_data_flat065_step : block007_data_flat065 = (CoefficientMerge.fastMerge block007_data_flat061 block007_data_flat064) := by decide +kernel
theorem block007_data_flat065_original : block007_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25867921742208 : Int) atom0448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27674310760320 : Int) atom0449Coded) (CoefficientMerge.scale (23463825855168 : Int) atom0450Coded))) := by
  rw [block007_data_flat065_step, block007_data_flat061_original, block007_data_flat064_original]
def block007_data_flat066 : CoefficientMerge.Poly := [(nat_lit 562, Int.ofNat (nat_lit 22695246099072)), (nat_lit 563, Int.ofNat (nat_lit 27549158575104)), (nat_lit 564, Int.ofNat (nat_lit 25867921742208)), (nat_lit 565, Int.ofNat (nat_lit 27674310760320)), (nat_lit 566, Int.ofNat (nat_lit 23463825855168))]
theorem block007_data_flat066_step : block007_data_flat066 = (CoefficientMerge.fastMerge block007_data_flat060 block007_data_flat065) := by decide +kernel
theorem block007_data_flat066_original : block007_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22695246099072 : Int) atom0446Coded) (CoefficientMerge.scale (27549158575104 : Int) atom0447Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25867921742208 : Int) atom0448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27674310760320 : Int) atom0449Coded) (CoefficientMerge.scale (23463825855168 : Int) atom0450Coded)))) := by
  rw [block007_data_flat066_step, block007_data_flat060_original, block007_data_flat065_original]
def block007_data_flat067 : CoefficientMerge.Poly := [(nat_lit 573, Int.ofNat (nat_lit 14524199424000))]
theorem block007_data_flat067_step : block007_data_flat067 = (CoefficientMerge.scale (14524199424000 : Int) atom0451Coded) := by decide +kernel
theorem block007_data_flat067_original : block007_data_flat067 = (CoefficientMerge.scale (14524199424000 : Int) atom0451Coded) := by
  rw [block007_data_flat067_step]
def block007_data_flat068 : CoefficientMerge.Poly := [(nat_lit 574, Int.ofNat (nat_lit 25592052764160))]
theorem block007_data_flat068_step : block007_data_flat068 = (CoefficientMerge.scale (25592052764160 : Int) atom0452Coded) := by decide +kernel
theorem block007_data_flat068_original : block007_data_flat068 = (CoefficientMerge.scale (25592052764160 : Int) atom0452Coded) := by
  rw [block007_data_flat068_step]
def block007_data_flat069 : CoefficientMerge.Poly := [(nat_lit 573, Int.ofNat (nat_lit 14524199424000)), (nat_lit 574, Int.ofNat (nat_lit 25592052764160))]
theorem block007_data_flat069_step : block007_data_flat069 = (CoefficientMerge.fastMerge block007_data_flat067 block007_data_flat068) := by decide +kernel
theorem block007_data_flat069_original : block007_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14524199424000 : Int) atom0451Coded) (CoefficientMerge.scale (25592052764160 : Int) atom0452Coded)) := by
  rw [block007_data_flat069_step, block007_data_flat067_original, block007_data_flat068_original]
def block007_data_flat070 : CoefficientMerge.Poly := [(nat_lit 575, Int.ofNat (nat_lit 23065383297600))]
theorem block007_data_flat070_step : block007_data_flat070 = (CoefficientMerge.scale (23065383297600 : Int) atom0453Coded) := by decide +kernel
theorem block007_data_flat070_original : block007_data_flat070 = (CoefficientMerge.scale (23065383297600 : Int) atom0453Coded) := by
  rw [block007_data_flat070_step]
def block007_data_flat071 : CoefficientMerge.Poly := [(nat_lit 576, Int.ofNat (nat_lit 22222382918400))]
theorem block007_data_flat071_step : block007_data_flat071 = (CoefficientMerge.scale (22222382918400 : Int) atom0454Coded) := by decide +kernel
theorem block007_data_flat071_original : block007_data_flat071 = (CoefficientMerge.scale (22222382918400 : Int) atom0454Coded) := by
  rw [block007_data_flat071_step]
def block007_data_flat072 : CoefficientMerge.Poly := [(nat_lit 577, Int.ofNat (nat_lit 22859770147200))]
theorem block007_data_flat072_step : block007_data_flat072 = (CoefficientMerge.scale (22859770147200 : Int) atom0455Coded) := by decide +kernel
theorem block007_data_flat072_original : block007_data_flat072 = (CoefficientMerge.scale (22859770147200 : Int) atom0455Coded) := by
  rw [block007_data_flat072_step]
def block007_data_flat073 : CoefficientMerge.Poly := [(nat_lit 576, Int.ofNat (nat_lit 22222382918400)), (nat_lit 577, Int.ofNat (nat_lit 22859770147200))]
theorem block007_data_flat073_step : block007_data_flat073 = (CoefficientMerge.fastMerge block007_data_flat071 block007_data_flat072) := by decide +kernel
theorem block007_data_flat073_original : block007_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22222382918400 : Int) atom0454Coded) (CoefficientMerge.scale (22859770147200 : Int) atom0455Coded)) := by
  rw [block007_data_flat073_step, block007_data_flat071_original, block007_data_flat072_original]
def block007_data_flat074 : CoefficientMerge.Poly := [(nat_lit 575, Int.ofNat (nat_lit 23065383297600)), (nat_lit 576, Int.ofNat (nat_lit 22222382918400)), (nat_lit 577, Int.ofNat (nat_lit 22859770147200))]
theorem block007_data_flat074_step : block007_data_flat074 = (CoefficientMerge.fastMerge block007_data_flat070 block007_data_flat073) := by decide +kernel
theorem block007_data_flat074_original : block007_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23065383297600 : Int) atom0453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22222382918400 : Int) atom0454Coded) (CoefficientMerge.scale (22859770147200 : Int) atom0455Coded))) := by
  rw [block007_data_flat074_step, block007_data_flat070_original, block007_data_flat073_original]
def block007_data_flat075 : CoefficientMerge.Poly := [(nat_lit 573, Int.ofNat (nat_lit 14524199424000)), (nat_lit 574, Int.ofNat (nat_lit 25592052764160)), (nat_lit 575, Int.ofNat (nat_lit 23065383297600)), (nat_lit 576, Int.ofNat (nat_lit 22222382918400)), (nat_lit 577, Int.ofNat (nat_lit 22859770147200))]
theorem block007_data_flat075_step : block007_data_flat075 = (CoefficientMerge.fastMerge block007_data_flat069 block007_data_flat074) := by decide +kernel
theorem block007_data_flat075_original : block007_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14524199424000 : Int) atom0451Coded) (CoefficientMerge.scale (25592052764160 : Int) atom0452Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23065383297600 : Int) atom0453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22222382918400 : Int) atom0454Coded) (CoefficientMerge.scale (22859770147200 : Int) atom0455Coded)))) := by
  rw [block007_data_flat075_step, block007_data_flat069_original, block007_data_flat074_original]
def block007_data_flat076 : CoefficientMerge.Poly := [(nat_lit 562, Int.ofNat (nat_lit 22695246099072)), (nat_lit 563, Int.ofNat (nat_lit 27549158575104)), (nat_lit 564, Int.ofNat (nat_lit 25867921742208)), (nat_lit 565, Int.ofNat (nat_lit 27674310760320)), (nat_lit 566, Int.ofNat (nat_lit 23463825855168)), (nat_lit 573, Int.ofNat (nat_lit 14524199424000)), (nat_lit 574, Int.ofNat (nat_lit 25592052764160)), (nat_lit 575, Int.ofNat (nat_lit 23065383297600)), (nat_lit 576, Int.ofNat (nat_lit 22222382918400)), (nat_lit 577, Int.ofNat (nat_lit 22859770147200))]
theorem block007_data_flat076_step : block007_data_flat076 = (CoefficientMerge.fastMerge block007_data_flat066 block007_data_flat075) := by decide +kernel
theorem block007_data_flat076_original : block007_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22695246099072 : Int) atom0446Coded) (CoefficientMerge.scale (27549158575104 : Int) atom0447Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25867921742208 : Int) atom0448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27674310760320 : Int) atom0449Coded) (CoefficientMerge.scale (23463825855168 : Int) atom0450Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14524199424000 : Int) atom0451Coded) (CoefficientMerge.scale (25592052764160 : Int) atom0452Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23065383297600 : Int) atom0453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22222382918400 : Int) atom0454Coded) (CoefficientMerge.scale (22859770147200 : Int) atom0455Coded))))) := by
  rw [block007_data_flat076_step, block007_data_flat066_original, block007_data_flat075_original]
def block007_data_flat077 : CoefficientMerge.Poly := [(nat_lit 552, Int.ofNat (nat_lit 19865648451456)), (nat_lit 553, Int.ofNat (nat_lit 19588073217408)), (nat_lit 554, Int.ofNat (nat_lit 20097013768704)), (nat_lit 555, Int.ofNat (nat_lit 21289155007104)), (nat_lit 556, Int.ofNat (nat_lit 21751611093504)), (nat_lit 557, Int.ofNat (nat_lit 21955062587904)), (nat_lit 558, Int.ofNat (nat_lit 18753888376704)), (nat_lit 559, Int.ofNat (nat_lit 18329339407104)), (nat_lit 560, Int.ofNat (nat_lit 19351865090304)), (nat_lit 561, Int.ofNat (nat_lit 29154774357504)), (nat_lit 562, Int.ofNat (nat_lit 22695246099072)), (nat_lit 563, Int.ofNat (nat_lit 27549158575104)), (nat_lit 564, Int.ofNat (nat_lit 25867921742208)), (nat_lit 565, Int.ofNat (nat_lit 27674310760320)), (nat_lit 566, Int.ofNat (nat_lit 23463825855168)), (nat_lit 573, Int.ofNat (nat_lit 14524199424000)), (nat_lit 574, Int.ofNat (nat_lit 25592052764160)), (nat_lit 575, Int.ofNat (nat_lit 23065383297600)), (nat_lit 576, Int.ofNat (nat_lit 22222382918400)), (nat_lit 577, Int.ofNat (nat_lit 22859770147200))]
theorem block007_data_flat077_step : block007_data_flat077 = (CoefficientMerge.fastMerge block007_data_flat057 block007_data_flat076) := by decide +kernel
theorem block007_data_flat077_original : block007_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19865648451456 : Int) atom0436Coded) (CoefficientMerge.scale (19588073217408 : Int) atom0437Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20097013768704 : Int) atom0438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21289155007104 : Int) atom0439Coded) (CoefficientMerge.scale (21751611093504 : Int) atom0440Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21955062587904 : Int) atom0441Coded) (CoefficientMerge.scale (18753888376704 : Int) atom0442Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18329339407104 : Int) atom0443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19351865090304 : Int) atom0444Coded) (CoefficientMerge.scale (29154774357504 : Int) atom0445Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22695246099072 : Int) atom0446Coded) (CoefficientMerge.scale (27549158575104 : Int) atom0447Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25867921742208 : Int) atom0448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27674310760320 : Int) atom0449Coded) (CoefficientMerge.scale (23463825855168 : Int) atom0450Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14524199424000 : Int) atom0451Coded) (CoefficientMerge.scale (25592052764160 : Int) atom0452Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23065383297600 : Int) atom0453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22222382918400 : Int) atom0454Coded) (CoefficientMerge.scale (22859770147200 : Int) atom0455Coded)))))) := by
  rw [block007_data_flat077_step, block007_data_flat057_original, block007_data_flat076_original]
def block007_data_flat078 : CoefficientMerge.Poly := [(nat_lit 523, Int.ofNat (nat_lit 14423604249600)), (nat_lit 524, Int.ofNat (nat_lit 11360537395200)), (nat_lit 529, Int.ofNat (nat_lit 7526146622400)), (nat_lit 530, Int.ofNat (nat_lit 14464310141952)), (nat_lit 531, Int.ofNat (nat_lit 14992217856000)), (nat_lit 532, Int.ofNat (nat_lit 17536417636608)), (nat_lit 533, Int.ofNat (nat_lit 18177375283200)), (nat_lit 534, Int.ofNat (nat_lit 18668342246400)), (nat_lit 535, Int.ofNat (nat_lit 19159309209600)), (nat_lit 536, Int.ofNat (nat_lit 19026429004800)), (nat_lit 537, Int.ofNat (nat_lit 15199948444800)), (nat_lit 538, Int.ofNat (nat_lit 14776849180800)), (nat_lit 539, Int.ofNat (nat_lit 15669867830400)), (nat_lit 540, Int.ofNat (nat_lit 24880813977600)), (nat_lit 541, Int.ofNat (nat_lit 18272069247600)), (nat_lit 542, Int.ofNat (nat_lit 22602534796800)), (nat_lit 543, Int.ofNat (nat_lit 20221399774800)), (nat_lit 544, Int.ofNat (nat_lit 21663695768400)), (nat_lit 545, Int.ofNat (nat_lit 17565700194000)), (nat_lit 551, Int.ofNat (nat_lit 11219811941376)), (nat_lit 552, Int.ofNat (nat_lit 19865648451456)), (nat_lit 553, Int.ofNat (nat_lit 19588073217408)), (nat_lit 554, Int.ofNat (nat_lit 20097013768704)), (nat_lit 555, Int.ofNat (nat_lit 21289155007104)), (nat_lit 556, Int.ofNat (nat_lit 21751611093504)), (nat_lit 557, Int.ofNat (nat_lit 21955062587904)), (nat_lit 558, Int.ofNat (nat_lit 18753888376704)), (nat_lit 559, Int.ofNat (nat_lit 18329339407104)), (nat_lit 560, Int.ofNat (nat_lit 19351865090304)), (nat_lit 561, Int.ofNat (nat_lit 29154774357504)), (nat_lit 562, Int.ofNat (nat_lit 22695246099072)), (nat_lit 563, Int.ofNat (nat_lit 27549158575104)), (nat_lit 564, Int.ofNat (nat_lit 25867921742208)), (nat_lit 565, Int.ofNat (nat_lit 27674310760320)), (nat_lit 566, Int.ofNat (nat_lit 23463825855168)), (nat_lit 573, Int.ofNat (nat_lit 14524199424000)), (nat_lit 574, Int.ofNat (nat_lit 25592052764160)), (nat_lit 575, Int.ofNat (nat_lit 23065383297600)), (nat_lit 576, Int.ofNat (nat_lit 22222382918400)), (nat_lit 577, Int.ofNat (nat_lit 22859770147200))]
theorem block007_data_flat078_step : block007_data_flat078 = (CoefficientMerge.fastMerge block007_data_flat038 block007_data_flat077) := by decide +kernel
theorem block007_data_flat078_original : block007_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14423604249600 : Int) atom0416Coded) (CoefficientMerge.scale (11360537395200 : Int) atom0417Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7526146622400 : Int) atom0418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14464310141952 : Int) atom0419Coded) (CoefficientMerge.scale (14992217856000 : Int) atom0420Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17536417636608 : Int) atom0421Coded) (CoefficientMerge.scale (18177375283200 : Int) atom0422Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18668342246400 : Int) atom0423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19159309209600 : Int) atom0424Coded) (CoefficientMerge.scale (19026429004800 : Int) atom0425Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15199948444800 : Int) atom0426Coded) (CoefficientMerge.scale (14776849180800 : Int) atom0427Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15669867830400 : Int) atom0428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24880813977600 : Int) atom0429Coded) (CoefficientMerge.scale (18272069247600 : Int) atom0430Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22602534796800 : Int) atom0431Coded) (CoefficientMerge.scale (20221399774800 : Int) atom0432Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21663695768400 : Int) atom0433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17565700194000 : Int) atom0434Coded) (CoefficientMerge.scale (11219811941376 : Int) atom0435Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19865648451456 : Int) atom0436Coded) (CoefficientMerge.scale (19588073217408 : Int) atom0437Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20097013768704 : Int) atom0438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21289155007104 : Int) atom0439Coded) (CoefficientMerge.scale (21751611093504 : Int) atom0440Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21955062587904 : Int) atom0441Coded) (CoefficientMerge.scale (18753888376704 : Int) atom0442Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18329339407104 : Int) atom0443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19351865090304 : Int) atom0444Coded) (CoefficientMerge.scale (29154774357504 : Int) atom0445Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22695246099072 : Int) atom0446Coded) (CoefficientMerge.scale (27549158575104 : Int) atom0447Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25867921742208 : Int) atom0448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27674310760320 : Int) atom0449Coded) (CoefficientMerge.scale (23463825855168 : Int) atom0450Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14524199424000 : Int) atom0451Coded) (CoefficientMerge.scale (25592052764160 : Int) atom0452Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23065383297600 : Int) atom0453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22222382918400 : Int) atom0454Coded) (CoefficientMerge.scale (22859770147200 : Int) atom0455Coded))))))) := by
  rw [block007_data_flat078_step, block007_data_flat038_original, block007_data_flat077_original]
def block007_data_flat079 : CoefficientMerge.Poly := [(nat_lit 578, Int.ofNat (nat_lit 22899764966400))]
theorem block007_data_flat079_step : block007_data_flat079 = (CoefficientMerge.scale (22899764966400 : Int) atom0456Coded) := by decide +kernel
theorem block007_data_flat079_original : block007_data_flat079 = (CoefficientMerge.scale (22899764966400 : Int) atom0456Coded) := by
  rw [block007_data_flat079_step]
def block007_data_flat080 : CoefficientMerge.Poly := [(nat_lit 579, Int.ofNat (nat_lit 20036978572800))]
theorem block007_data_flat080_step : block007_data_flat080 = (CoefficientMerge.scale (20036978572800 : Int) atom0457Coded) := by decide +kernel
theorem block007_data_flat080_original : block007_data_flat080 = (CoefficientMerge.scale (20036978572800 : Int) atom0457Coded) := by
  rw [block007_data_flat080_step]
def block007_data_flat081 : CoefficientMerge.Poly := [(nat_lit 578, Int.ofNat (nat_lit 22899764966400)), (nat_lit 579, Int.ofNat (nat_lit 20036978572800))]
theorem block007_data_flat081_step : block007_data_flat081 = (CoefficientMerge.fastMerge block007_data_flat079 block007_data_flat080) := by decide +kernel
theorem block007_data_flat081_original : block007_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22899764966400 : Int) atom0456Coded) (CoefficientMerge.scale (20036978572800 : Int) atom0457Coded)) := by
  rw [block007_data_flat081_step, block007_data_flat079_original, block007_data_flat080_original]
def block007_data_flat082 : CoefficientMerge.Poly := [(nat_lit 580, Int.ofNat (nat_lit 19788810451200))]
theorem block007_data_flat082_step : block007_data_flat082 = (CoefficientMerge.scale (19788810451200 : Int) atom0458Coded) := by decide +kernel
theorem block007_data_flat082_original : block007_data_flat082 = (CoefficientMerge.scale (19788810451200 : Int) atom0458Coded) := by
  rw [block007_data_flat082_step]
def block007_data_flat083 : CoefficientMerge.Poly := [(nat_lit 581, Int.ofNat (nat_lit 20856760243200))]
theorem block007_data_flat083_step : block007_data_flat083 = (CoefficientMerge.scale (20856760243200 : Int) atom0459Coded) := by decide +kernel
theorem block007_data_flat083_original : block007_data_flat083 = (CoefficientMerge.scale (20856760243200 : Int) atom0459Coded) := by
  rw [block007_data_flat083_step]
def block007_data_flat084 : CoefficientMerge.Poly := [(nat_lit 582, Int.ofNat (nat_lit 31352628787200))]
theorem block007_data_flat084_step : block007_data_flat084 = (CoefficientMerge.scale (31352628787200 : Int) atom0460Coded) := by decide +kernel
theorem block007_data_flat084_original : block007_data_flat084 = (CoefficientMerge.scale (31352628787200 : Int) atom0460Coded) := by
  rw [block007_data_flat084_step]
def block007_data_flat085 : CoefficientMerge.Poly := [(nat_lit 581, Int.ofNat (nat_lit 20856760243200)), (nat_lit 582, Int.ofNat (nat_lit 31352628787200))]
theorem block007_data_flat085_step : block007_data_flat085 = (CoefficientMerge.fastMerge block007_data_flat083 block007_data_flat084) := by decide +kernel
theorem block007_data_flat085_original : block007_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20856760243200 : Int) atom0459Coded) (CoefficientMerge.scale (31352628787200 : Int) atom0460Coded)) := by
  rw [block007_data_flat085_step, block007_data_flat083_original, block007_data_flat084_original]
def block007_data_flat086 : CoefficientMerge.Poly := [(nat_lit 580, Int.ofNat (nat_lit 19788810451200)), (nat_lit 581, Int.ofNat (nat_lit 20856760243200)), (nat_lit 582, Int.ofNat (nat_lit 31352628787200))]
theorem block007_data_flat086_step : block007_data_flat086 = (CoefficientMerge.fastMerge block007_data_flat082 block007_data_flat085) := by decide +kernel
theorem block007_data_flat086_original : block007_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (19788810451200 : Int) atom0458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20856760243200 : Int) atom0459Coded) (CoefficientMerge.scale (31352628787200 : Int) atom0460Coded))) := by
  rw [block007_data_flat086_step, block007_data_flat082_original, block007_data_flat085_original]
def block007_data_flat087 : CoefficientMerge.Poly := [(nat_lit 578, Int.ofNat (nat_lit 22899764966400)), (nat_lit 579, Int.ofNat (nat_lit 20036978572800)), (nat_lit 580, Int.ofNat (nat_lit 19788810451200)), (nat_lit 581, Int.ofNat (nat_lit 20856760243200)), (nat_lit 582, Int.ofNat (nat_lit 31352628787200))]
theorem block007_data_flat087_step : block007_data_flat087 = (CoefficientMerge.fastMerge block007_data_flat081 block007_data_flat086) := by decide +kernel
theorem block007_data_flat087_original : block007_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22899764966400 : Int) atom0456Coded) (CoefficientMerge.scale (20036978572800 : Int) atom0457Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19788810451200 : Int) atom0458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20856760243200 : Int) atom0459Coded) (CoefficientMerge.scale (31352628787200 : Int) atom0460Coded)))) := by
  rw [block007_data_flat087_step, block007_data_flat081_original, block007_data_flat086_original]
def block007_data_flat088 : CoefficientMerge.Poly := [(nat_lit 583, Int.ofNat (nat_lit 25110779097600))]
theorem block007_data_flat088_step : block007_data_flat088 = (CoefficientMerge.scale (25110779097600 : Int) atom0461Coded) := by decide +kernel
theorem block007_data_flat088_original : block007_data_flat088 = (CoefficientMerge.scale (25110779097600 : Int) atom0461Coded) := by
  rw [block007_data_flat088_step]
def block007_data_flat089 : CoefficientMerge.Poly := [(nat_lit 584, Int.ofNat (nat_lit 30419676403200))]
theorem block007_data_flat089_step : block007_data_flat089 = (CoefficientMerge.scale (30419676403200 : Int) atom0462Coded) := by decide +kernel
theorem block007_data_flat089_original : block007_data_flat089 = (CoefficientMerge.scale (30419676403200 : Int) atom0462Coded) := by
  rw [block007_data_flat089_step]
def block007_data_flat090 : CoefficientMerge.Poly := [(nat_lit 583, Int.ofNat (nat_lit 25110779097600)), (nat_lit 584, Int.ofNat (nat_lit 30419676403200))]
theorem block007_data_flat090_step : block007_data_flat090 = (CoefficientMerge.fastMerge block007_data_flat088 block007_data_flat089) := by decide +kernel
theorem block007_data_flat090_original : block007_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25110779097600 : Int) atom0461Coded) (CoefficientMerge.scale (30419676403200 : Int) atom0462Coded)) := by
  rw [block007_data_flat090_step, block007_data_flat088_original, block007_data_flat089_original]
def block007_data_flat091 : CoefficientMerge.Poly := [(nat_lit 585, Int.ofNat (nat_lit 30013882214400))]
theorem block007_data_flat091_step : block007_data_flat091 = (CoefficientMerge.scale (30013882214400 : Int) atom0463Coded) := by decide +kernel
theorem block007_data_flat091_original : block007_data_flat091 = (CoefficientMerge.scale (30013882214400 : Int) atom0463Coded) := by
  rw [block007_data_flat091_step]
def block007_data_flat092 : CoefficientMerge.Poly := [(nat_lit 586, Int.ofNat (nat_lit 33459931814400))]
theorem block007_data_flat092_step : block007_data_flat092 = (CoefficientMerge.scale (33459931814400 : Int) atom0464Coded) := by decide +kernel
theorem block007_data_flat092_original : block007_data_flat092 = (CoefficientMerge.scale (33459931814400 : Int) atom0464Coded) := by
  rw [block007_data_flat092_step]
def block007_data_flat093 : CoefficientMerge.Poly := [(nat_lit 587, Int.ofNat (nat_lit 32426062099200))]
theorem block007_data_flat093_step : block007_data_flat093 = (CoefficientMerge.scale (32426062099200 : Int) atom0465Coded) := by decide +kernel
theorem block007_data_flat093_original : block007_data_flat093 = (CoefficientMerge.scale (32426062099200 : Int) atom0465Coded) := by
  rw [block007_data_flat093_step]
def block007_data_flat094 : CoefficientMerge.Poly := [(nat_lit 586, Int.ofNat (nat_lit 33459931814400)), (nat_lit 587, Int.ofNat (nat_lit 32426062099200))]
theorem block007_data_flat094_step : block007_data_flat094 = (CoefficientMerge.fastMerge block007_data_flat092 block007_data_flat093) := by decide +kernel
theorem block007_data_flat094_original : block007_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (33459931814400 : Int) atom0464Coded) (CoefficientMerge.scale (32426062099200 : Int) atom0465Coded)) := by
  rw [block007_data_flat094_step, block007_data_flat092_original, block007_data_flat093_original]
def block007_data_flat095 : CoefficientMerge.Poly := [(nat_lit 585, Int.ofNat (nat_lit 30013882214400)), (nat_lit 586, Int.ofNat (nat_lit 33459931814400)), (nat_lit 587, Int.ofNat (nat_lit 32426062099200))]
theorem block007_data_flat095_step : block007_data_flat095 = (CoefficientMerge.fastMerge block007_data_flat091 block007_data_flat094) := by decide +kernel
theorem block007_data_flat095_original : block007_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30013882214400 : Int) atom0463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33459931814400 : Int) atom0464Coded) (CoefficientMerge.scale (32426062099200 : Int) atom0465Coded))) := by
  rw [block007_data_flat095_step, block007_data_flat091_original, block007_data_flat094_original]
def block007_data_flat096 : CoefficientMerge.Poly := [(nat_lit 583, Int.ofNat (nat_lit 25110779097600)), (nat_lit 584, Int.ofNat (nat_lit 30419676403200)), (nat_lit 585, Int.ofNat (nat_lit 30013882214400)), (nat_lit 586, Int.ofNat (nat_lit 33459931814400)), (nat_lit 587, Int.ofNat (nat_lit 32426062099200))]
theorem block007_data_flat096_step : block007_data_flat096 = (CoefficientMerge.fastMerge block007_data_flat090 block007_data_flat095) := by decide +kernel
theorem block007_data_flat096_original : block007_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25110779097600 : Int) atom0461Coded) (CoefficientMerge.scale (30419676403200 : Int) atom0462Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30013882214400 : Int) atom0463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33459931814400 : Int) atom0464Coded) (CoefficientMerge.scale (32426062099200 : Int) atom0465Coded)))) := by
  rw [block007_data_flat096_step, block007_data_flat090_original, block007_data_flat095_original]
def block007_data_flat097 : CoefficientMerge.Poly := [(nat_lit 578, Int.ofNat (nat_lit 22899764966400)), (nat_lit 579, Int.ofNat (nat_lit 20036978572800)), (nat_lit 580, Int.ofNat (nat_lit 19788810451200)), (nat_lit 581, Int.ofNat (nat_lit 20856760243200)), (nat_lit 582, Int.ofNat (nat_lit 31352628787200)), (nat_lit 583, Int.ofNat (nat_lit 25110779097600)), (nat_lit 584, Int.ofNat (nat_lit 30419676403200)), (nat_lit 585, Int.ofNat (nat_lit 30013882214400)), (nat_lit 586, Int.ofNat (nat_lit 33459931814400)), (nat_lit 587, Int.ofNat (nat_lit 32426062099200))]
theorem block007_data_flat097_step : block007_data_flat097 = (CoefficientMerge.fastMerge block007_data_flat087 block007_data_flat096) := by decide +kernel
theorem block007_data_flat097_original : block007_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22899764966400 : Int) atom0456Coded) (CoefficientMerge.scale (20036978572800 : Int) atom0457Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19788810451200 : Int) atom0458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20856760243200 : Int) atom0459Coded) (CoefficientMerge.scale (31352628787200 : Int) atom0460Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25110779097600 : Int) atom0461Coded) (CoefficientMerge.scale (30419676403200 : Int) atom0462Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30013882214400 : Int) atom0463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33459931814400 : Int) atom0464Coded) (CoefficientMerge.scale (32426062099200 : Int) atom0465Coded))))) := by
  rw [block007_data_flat097_step, block007_data_flat087_original, block007_data_flat096_original]
def block007_data_flat098 : CoefficientMerge.Poly := [(nat_lit 595, Int.ofNat (nat_lit 16601669556480))]
theorem block007_data_flat098_step : block007_data_flat098 = (CoefficientMerge.scale (16601669556480 : Int) atom0466Coded) := by decide +kernel
theorem block007_data_flat098_original : block007_data_flat098 = (CoefficientMerge.scale (16601669556480 : Int) atom0466Coded) := by
  rw [block007_data_flat098_step]
def block007_data_flat099 : CoefficientMerge.Poly := [(nat_lit 596, Int.ofNat (nat_lit 29149185627360))]
theorem block007_data_flat099_step : block007_data_flat099 = (CoefficientMerge.scale (29149185627360 : Int) atom0467Coded) := by decide +kernel
theorem block007_data_flat099_original : block007_data_flat099 = (CoefficientMerge.scale (29149185627360 : Int) atom0467Coded) := by
  rw [block007_data_flat099_step]
def block007_data_flat100 : CoefficientMerge.Poly := [(nat_lit 595, Int.ofNat (nat_lit 16601669556480)), (nat_lit 596, Int.ofNat (nat_lit 29149185627360))]
theorem block007_data_flat100_step : block007_data_flat100 = (CoefficientMerge.fastMerge block007_data_flat098 block007_data_flat099) := by decide +kernel
theorem block007_data_flat100_original : block007_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16601669556480 : Int) atom0466Coded) (CoefficientMerge.scale (29149185627360 : Int) atom0467Coded)) := by
  rw [block007_data_flat100_step, block007_data_flat098_original, block007_data_flat099_original]
def block007_data_flat101 : CoefficientMerge.Poly := [(nat_lit 597, Int.ofNat (nat_lit 27058453117056))]
theorem block007_data_flat101_step : block007_data_flat101 = (CoefficientMerge.scale (27058453117056 : Int) atom0468Coded) := by decide +kernel
theorem block007_data_flat101_original : block007_data_flat101 = (CoefficientMerge.scale (27058453117056 : Int) atom0468Coded) := by
  rw [block007_data_flat101_step]
def block007_data_flat102 : CoefficientMerge.Poly := [(nat_lit 598, Int.ofNat (nat_lit 27527674496256))]
theorem block007_data_flat102_step : block007_data_flat102 = (CoefficientMerge.scale (27527674496256 : Int) atom0469Coded) := by decide +kernel
theorem block007_data_flat102_original : block007_data_flat102 = (CoefficientMerge.scale (27527674496256 : Int) atom0469Coded) := by
  rw [block007_data_flat102_step]
def block007_data_flat103 : CoefficientMerge.Poly := [(nat_lit 599, Int.ofNat (nat_lit 27658517533056))]
theorem block007_data_flat103_step : block007_data_flat103 = (CoefficientMerge.scale (27658517533056 : Int) atom0470Coded) := by decide +kernel
theorem block007_data_flat103_original : block007_data_flat103 = (CoefficientMerge.scale (27658517533056 : Int) atom0470Coded) := by
  rw [block007_data_flat103_step]
def block007_data_flat104 : CoefficientMerge.Poly := [(nat_lit 598, Int.ofNat (nat_lit 27527674496256)), (nat_lit 599, Int.ofNat (nat_lit 27658517533056))]
theorem block007_data_flat104_step : block007_data_flat104 = (CoefficientMerge.fastMerge block007_data_flat102 block007_data_flat103) := by decide +kernel
theorem block007_data_flat104_original : block007_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27527674496256 : Int) atom0469Coded) (CoefficientMerge.scale (27658517533056 : Int) atom0470Coded)) := by
  rw [block007_data_flat104_step, block007_data_flat102_original, block007_data_flat103_original]
def block007_data_flat105 : CoefficientMerge.Poly := [(nat_lit 597, Int.ofNat (nat_lit 27058453117056)), (nat_lit 598, Int.ofNat (nat_lit 27527674496256)), (nat_lit 599, Int.ofNat (nat_lit 27658517533056))]
theorem block007_data_flat105_step : block007_data_flat105 = (CoefficientMerge.fastMerge block007_data_flat101 block007_data_flat104) := by decide +kernel
theorem block007_data_flat105_original : block007_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27058453117056 : Int) atom0468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27527674496256 : Int) atom0469Coded) (CoefficientMerge.scale (27658517533056 : Int) atom0470Coded))) := by
  rw [block007_data_flat105_step, block007_data_flat101_original, block007_data_flat104_original]
def block007_data_flat106 : CoefficientMerge.Poly := [(nat_lit 595, Int.ofNat (nat_lit 16601669556480)), (nat_lit 596, Int.ofNat (nat_lit 29149185627360)), (nat_lit 597, Int.ofNat (nat_lit 27058453117056)), (nat_lit 598, Int.ofNat (nat_lit 27527674496256)), (nat_lit 599, Int.ofNat (nat_lit 27658517533056))]
theorem block007_data_flat106_step : block007_data_flat106 = (CoefficientMerge.fastMerge block007_data_flat100 block007_data_flat105) := by decide +kernel
theorem block007_data_flat106_original : block007_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16601669556480 : Int) atom0466Coded) (CoefficientMerge.scale (29149185627360 : Int) atom0467Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27058453117056 : Int) atom0468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27527674496256 : Int) atom0469Coded) (CoefficientMerge.scale (27658517533056 : Int) atom0470Coded)))) := by
  rw [block007_data_flat106_step, block007_data_flat100_original, block007_data_flat105_original]
def block007_data_flat107 : CoefficientMerge.Poly := [(nat_lit 600, Int.ofNat (nat_lit 24757072323456))]
theorem block007_data_flat107_step : block007_data_flat107 = (CoefficientMerge.scale (24757072323456 : Int) atom0471Coded) := by decide +kernel
theorem block007_data_flat107_original : block007_data_flat107 = (CoefficientMerge.scale (24757072323456 : Int) atom0471Coded) := by
  rw [block007_data_flat107_step]
def block007_data_flat108 : CoefficientMerge.Poly := [(nat_lit 601, Int.ofNat (nat_lit 24470245385856))]
theorem block007_data_flat108_step : block007_data_flat108 = (CoefficientMerge.scale (24470245385856 : Int) atom0472Coded) := by decide +kernel
theorem block007_data_flat108_original : block007_data_flat108 = (CoefficientMerge.scale (24470245385856 : Int) atom0472Coded) := by
  rw [block007_data_flat108_step]
def block007_data_flat109 : CoefficientMerge.Poly := [(nat_lit 600, Int.ofNat (nat_lit 24757072323456)), (nat_lit 601, Int.ofNat (nat_lit 24470245385856))]
theorem block007_data_flat109_step : block007_data_flat109 = (CoefficientMerge.fastMerge block007_data_flat107 block007_data_flat108) := by decide +kernel
theorem block007_data_flat109_original : block007_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24757072323456 : Int) atom0471Coded) (CoefficientMerge.scale (24470245385856 : Int) atom0472Coded)) := by
  rw [block007_data_flat109_step, block007_data_flat107_original, block007_data_flat108_original]
def block007_data_flat110 : CoefficientMerge.Poly := [(nat_lit 602, Int.ofNat (nat_lit 25499536361856))]
theorem block007_data_flat110_step : block007_data_flat110 = (CoefficientMerge.scale (25499536361856 : Int) atom0473Coded) := by decide +kernel
theorem block007_data_flat110_original : block007_data_flat110 = (CoefficientMerge.scale (25499536361856 : Int) atom0473Coded) := by
  rw [block007_data_flat110_step]
def block007_data_flat111 : CoefficientMerge.Poly := [(nat_lit 603, Int.ofNat (nat_lit 35551425892608))]
theorem block007_data_flat111_step : block007_data_flat111 = (CoefficientMerge.scale (35551425892608 : Int) atom0474Coded) := by decide +kernel
theorem block007_data_flat111_original : block007_data_flat111 = (CoefficientMerge.scale (35551425892608 : Int) atom0474Coded) := by
  rw [block007_data_flat111_step]
def block007_data_flat112 : CoefficientMerge.Poly := [(nat_lit 604, Int.ofNat (nat_lit 29604979281024))]
theorem block007_data_flat112_step : block007_data_flat112 = (CoefficientMerge.scale (29604979281024 : Int) atom0475Coded) := by decide +kernel
theorem block007_data_flat112_original : block007_data_flat112 = (CoefficientMerge.scale (29604979281024 : Int) atom0475Coded) := by
  rw [block007_data_flat112_step]
def block007_data_flat113 : CoefficientMerge.Poly := [(nat_lit 603, Int.ofNat (nat_lit 35551425892608)), (nat_lit 604, Int.ofNat (nat_lit 29604979281024))]
theorem block007_data_flat113_step : block007_data_flat113 = (CoefficientMerge.fastMerge block007_data_flat111 block007_data_flat112) := by decide +kernel
theorem block007_data_flat113_original : block007_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35551425892608 : Int) atom0474Coded) (CoefficientMerge.scale (29604979281024 : Int) atom0475Coded)) := by
  rw [block007_data_flat113_step, block007_data_flat111_original, block007_data_flat112_original]
def block007_data_flat114 : CoefficientMerge.Poly := [(nat_lit 602, Int.ofNat (nat_lit 25499536361856)), (nat_lit 603, Int.ofNat (nat_lit 35551425892608)), (nat_lit 604, Int.ofNat (nat_lit 29604979281024))]
theorem block007_data_flat114_step : block007_data_flat114 = (CoefficientMerge.fastMerge block007_data_flat110 block007_data_flat113) := by decide +kernel
theorem block007_data_flat114_original : block007_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25499536361856 : Int) atom0473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35551425892608 : Int) atom0474Coded) (CoefficientMerge.scale (29604979281024 : Int) atom0475Coded))) := by
  rw [block007_data_flat114_step, block007_data_flat110_original, block007_data_flat113_original]
def block007_data_flat115 : CoefficientMerge.Poly := [(nat_lit 600, Int.ofNat (nat_lit 24757072323456)), (nat_lit 601, Int.ofNat (nat_lit 24470245385856)), (nat_lit 602, Int.ofNat (nat_lit 25499536361856)), (nat_lit 603, Int.ofNat (nat_lit 35551425892608)), (nat_lit 604, Int.ofNat (nat_lit 29604979281024))]
theorem block007_data_flat115_step : block007_data_flat115 = (CoefficientMerge.fastMerge block007_data_flat109 block007_data_flat114) := by decide +kernel
theorem block007_data_flat115_original : block007_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24757072323456 : Int) atom0471Coded) (CoefficientMerge.scale (24470245385856 : Int) atom0472Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25499536361856 : Int) atom0473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35551425892608 : Int) atom0474Coded) (CoefficientMerge.scale (29604979281024 : Int) atom0475Coded)))) := by
  rw [block007_data_flat115_step, block007_data_flat109_original, block007_data_flat114_original]
def block007_data_flat116 : CoefficientMerge.Poly := [(nat_lit 595, Int.ofNat (nat_lit 16601669556480)), (nat_lit 596, Int.ofNat (nat_lit 29149185627360)), (nat_lit 597, Int.ofNat (nat_lit 27058453117056)), (nat_lit 598, Int.ofNat (nat_lit 27527674496256)), (nat_lit 599, Int.ofNat (nat_lit 27658517533056)), (nat_lit 600, Int.ofNat (nat_lit 24757072323456)), (nat_lit 601, Int.ofNat (nat_lit 24470245385856)), (nat_lit 602, Int.ofNat (nat_lit 25499536361856)), (nat_lit 603, Int.ofNat (nat_lit 35551425892608)), (nat_lit 604, Int.ofNat (nat_lit 29604979281024))]
theorem block007_data_flat116_step : block007_data_flat116 = (CoefficientMerge.fastMerge block007_data_flat106 block007_data_flat115) := by decide +kernel
theorem block007_data_flat116_original : block007_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16601669556480 : Int) atom0466Coded) (CoefficientMerge.scale (29149185627360 : Int) atom0467Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27058453117056 : Int) atom0468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27527674496256 : Int) atom0469Coded) (CoefficientMerge.scale (27658517533056 : Int) atom0470Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24757072323456 : Int) atom0471Coded) (CoefficientMerge.scale (24470245385856 : Int) atom0472Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25499536361856 : Int) atom0473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35551425892608 : Int) atom0474Coded) (CoefficientMerge.scale (29604979281024 : Int) atom0475Coded))))) := by
  rw [block007_data_flat116_step, block007_data_flat106_original, block007_data_flat115_original]
def block007_data_flat117 : CoefficientMerge.Poly := [(nat_lit 578, Int.ofNat (nat_lit 22899764966400)), (nat_lit 579, Int.ofNat (nat_lit 20036978572800)), (nat_lit 580, Int.ofNat (nat_lit 19788810451200)), (nat_lit 581, Int.ofNat (nat_lit 20856760243200)), (nat_lit 582, Int.ofNat (nat_lit 31352628787200)), (nat_lit 583, Int.ofNat (nat_lit 25110779097600)), (nat_lit 584, Int.ofNat (nat_lit 30419676403200)), (nat_lit 585, Int.ofNat (nat_lit 30013882214400)), (nat_lit 586, Int.ofNat (nat_lit 33459931814400)), (nat_lit 587, Int.ofNat (nat_lit 32426062099200)), (nat_lit 595, Int.ofNat (nat_lit 16601669556480)), (nat_lit 596, Int.ofNat (nat_lit 29149185627360)), (nat_lit 597, Int.ofNat (nat_lit 27058453117056)), (nat_lit 598, Int.ofNat (nat_lit 27527674496256)), (nat_lit 599, Int.ofNat (nat_lit 27658517533056)), (nat_lit 600, Int.ofNat (nat_lit 24757072323456)), (nat_lit 601, Int.ofNat (nat_lit 24470245385856)), (nat_lit 602, Int.ofNat (nat_lit 25499536361856)), (nat_lit 603, Int.ofNat (nat_lit 35551425892608)), (nat_lit 604, Int.ofNat (nat_lit 29604979281024))]
theorem block007_data_flat117_step : block007_data_flat117 = (CoefficientMerge.fastMerge block007_data_flat097 block007_data_flat116) := by decide +kernel
theorem block007_data_flat117_original : block007_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22899764966400 : Int) atom0456Coded) (CoefficientMerge.scale (20036978572800 : Int) atom0457Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19788810451200 : Int) atom0458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20856760243200 : Int) atom0459Coded) (CoefficientMerge.scale (31352628787200 : Int) atom0460Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25110779097600 : Int) atom0461Coded) (CoefficientMerge.scale (30419676403200 : Int) atom0462Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30013882214400 : Int) atom0463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33459931814400 : Int) atom0464Coded) (CoefficientMerge.scale (32426062099200 : Int) atom0465Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16601669556480 : Int) atom0466Coded) (CoefficientMerge.scale (29149185627360 : Int) atom0467Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27058453117056 : Int) atom0468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27527674496256 : Int) atom0469Coded) (CoefficientMerge.scale (27658517533056 : Int) atom0470Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24757072323456 : Int) atom0471Coded) (CoefficientMerge.scale (24470245385856 : Int) atom0472Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25499536361856 : Int) atom0473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35551425892608 : Int) atom0474Coded) (CoefficientMerge.scale (29604979281024 : Int) atom0475Coded)))))) := by
  rw [block007_data_flat117_step, block007_data_flat097_original, block007_data_flat116_original]
def block007_data_flat118 : CoefficientMerge.Poly := [(nat_lit 605, Int.ofNat (nat_lit 35291136907008))]
theorem block007_data_flat118_step : block007_data_flat118 = (CoefficientMerge.scale (35291136907008 : Int) atom0476Coded) := by decide +kernel
theorem block007_data_flat118_original : block007_data_flat118 = (CoefficientMerge.scale (35291136907008 : Int) atom0476Coded) := by
  rw [block007_data_flat118_step]
def block007_data_flat119 : CoefficientMerge.Poly := [(nat_lit 606, Int.ofNat (nat_lit 34288248159360))]
theorem block007_data_flat119_step : block007_data_flat119 = (CoefficientMerge.scale (34288248159360 : Int) atom0477Coded) := by decide +kernel
theorem block007_data_flat119_original : block007_data_flat119 = (CoefficientMerge.scale (34288248159360 : Int) atom0477Coded) := by
  rw [block007_data_flat119_step]
def block007_data_flat120 : CoefficientMerge.Poly := [(nat_lit 605, Int.ofNat (nat_lit 35291136907008)), (nat_lit 606, Int.ofNat (nat_lit 34288248159360))]
theorem block007_data_flat120_step : block007_data_flat120 = (CoefficientMerge.fastMerge block007_data_flat118 block007_data_flat119) := by decide +kernel
theorem block007_data_flat120_original : block007_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35291136907008 : Int) atom0476Coded) (CoefficientMerge.scale (34288248159360 : Int) atom0477Coded)) := by
  rw [block007_data_flat120_step, block007_data_flat118_original, block007_data_flat119_original]
def block007_data_flat121 : CoefficientMerge.Poly := [(nat_lit 607, Int.ofNat (nat_lit 34242389905920))]
theorem block007_data_flat121_step : block007_data_flat121 = (CoefficientMerge.scale (34242389905920 : Int) atom0478Coded) := by decide +kernel
theorem block007_data_flat121_original : block007_data_flat121 = (CoefficientMerge.scale (34242389905920 : Int) atom0478Coded) := by
  rw [block007_data_flat121_step]
def block007_data_flat122 : CoefficientMerge.Poly := [(nat_lit 608, Int.ofNat (nat_lit 32868397290240))]
theorem block007_data_flat122_step : block007_data_flat122 = (CoefficientMerge.scale (32868397290240 : Int) atom0479Coded) := by decide +kernel
theorem block007_data_flat122_original : block007_data_flat122 = (CoefficientMerge.scale (32868397290240 : Int) atom0479Coded) := by
  rw [block007_data_flat122_step]
def block007_data_flat123 : CoefficientMerge.Poly := [(nat_lit 617, Int.ofNat (nat_lit 18294922245600))]
theorem block007_data_flat123_step : block007_data_flat123 = (CoefficientMerge.scale (18294922245600 : Int) atom0480Coded) := by decide +kernel
theorem block007_data_flat123_original : block007_data_flat123 = (CoefficientMerge.scale (18294922245600 : Int) atom0480Coded) := by
  rw [block007_data_flat123_step]
def block007_data_flat124 : CoefficientMerge.Poly := [(nat_lit 608, Int.ofNat (nat_lit 32868397290240)), (nat_lit 617, Int.ofNat (nat_lit 18294922245600))]
theorem block007_data_flat124_step : block007_data_flat124 = (CoefficientMerge.fastMerge block007_data_flat122 block007_data_flat123) := by decide +kernel
theorem block007_data_flat124_original : block007_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (32868397290240 : Int) atom0479Coded) (CoefficientMerge.scale (18294922245600 : Int) atom0480Coded)) := by
  rw [block007_data_flat124_step, block007_data_flat122_original, block007_data_flat123_original]
def block007_data_flat125 : CoefficientMerge.Poly := [(nat_lit 607, Int.ofNat (nat_lit 34242389905920)), (nat_lit 608, Int.ofNat (nat_lit 32868397290240)), (nat_lit 617, Int.ofNat (nat_lit 18294922245600))]
theorem block007_data_flat125_step : block007_data_flat125 = (CoefficientMerge.fastMerge block007_data_flat121 block007_data_flat124) := by decide +kernel
theorem block007_data_flat125_original : block007_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34242389905920 : Int) atom0478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32868397290240 : Int) atom0479Coded) (CoefficientMerge.scale (18294922245600 : Int) atom0480Coded))) := by
  rw [block007_data_flat125_step, block007_data_flat121_original, block007_data_flat124_original]
def block007_data_flat126 : CoefficientMerge.Poly := [(nat_lit 605, Int.ofNat (nat_lit 35291136907008)), (nat_lit 606, Int.ofNat (nat_lit 34288248159360)), (nat_lit 607, Int.ofNat (nat_lit 34242389905920)), (nat_lit 608, Int.ofNat (nat_lit 32868397290240)), (nat_lit 617, Int.ofNat (nat_lit 18294922245600))]
theorem block007_data_flat126_step : block007_data_flat126 = (CoefficientMerge.fastMerge block007_data_flat120 block007_data_flat125) := by decide +kernel
theorem block007_data_flat126_original : block007_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35291136907008 : Int) atom0476Coded) (CoefficientMerge.scale (34288248159360 : Int) atom0477Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34242389905920 : Int) atom0478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32868397290240 : Int) atom0479Coded) (CoefficientMerge.scale (18294922245600 : Int) atom0480Coded)))) := by
  rw [block007_data_flat126_step, block007_data_flat120_original, block007_data_flat125_original]
def block007_data_flat127 : CoefficientMerge.Poly := [(nat_lit 618, Int.ofNat (nat_lit 32761969339680))]
theorem block007_data_flat127_step : block007_data_flat127 = (CoefficientMerge.scale (32761969339680 : Int) atom0481Coded) := by decide +kernel
theorem block007_data_flat127_original : block007_data_flat127 = (CoefficientMerge.scale (32761969339680 : Int) atom0481Coded) := by
  rw [block007_data_flat127_step]
def block007_data_flat128 : CoefficientMerge.Poly := [(nat_lit 619, Int.ofNat (nat_lit 31025713320000))]
theorem block007_data_flat128_step : block007_data_flat128 = (CoefficientMerge.scale (31025713320000 : Int) atom0482Coded) := by decide +kernel
theorem block007_data_flat128_original : block007_data_flat128 = (CoefficientMerge.scale (31025713320000 : Int) atom0482Coded) := by
  rw [block007_data_flat128_step]
def block007_data_flat129 : CoefficientMerge.Poly := [(nat_lit 618, Int.ofNat (nat_lit 32761969339680)), (nat_lit 619, Int.ofNat (nat_lit 31025713320000))]
theorem block007_data_flat129_step : block007_data_flat129 = (CoefficientMerge.fastMerge block007_data_flat127 block007_data_flat128) := by decide +kernel
theorem block007_data_flat129_original : block007_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (32761969339680 : Int) atom0481Coded) (CoefficientMerge.scale (31025713320000 : Int) atom0482Coded)) := by
  rw [block007_data_flat129_step, block007_data_flat127_original, block007_data_flat128_original]
def block007_data_flat130 : CoefficientMerge.Poly := [(nat_lit 620, Int.ofNat (nat_lit 30904307582400))]
theorem block007_data_flat130_step : block007_data_flat130 = (CoefficientMerge.scale (30904307582400 : Int) atom0483Coded) := by decide +kernel
theorem block007_data_flat130_original : block007_data_flat130 = (CoefficientMerge.scale (30904307582400 : Int) atom0483Coded) := by
  rw [block007_data_flat130_step]
def block007_data_flat131 : CoefficientMerge.Poly := [(nat_lit 621, Int.ofNat (nat_lit 27666530673600))]
theorem block007_data_flat131_step : block007_data_flat131 = (CoefficientMerge.scale (27666530673600 : Int) atom0484Coded) := by decide +kernel
theorem block007_data_flat131_original : block007_data_flat131 = (CoefficientMerge.scale (27666530673600 : Int) atom0484Coded) := by
  rw [block007_data_flat131_step]
def block007_data_flat132 : CoefficientMerge.Poly := [(nat_lit 622, Int.ofNat (nat_lit 27256961995200))]
theorem block007_data_flat132_step : block007_data_flat132 = (CoefficientMerge.scale (27256961995200 : Int) atom0485Coded) := by decide +kernel
theorem block007_data_flat132_original : block007_data_flat132 = (CoefficientMerge.scale (27256961995200 : Int) atom0485Coded) := by
  rw [block007_data_flat132_step]
def block007_data_flat133 : CoefficientMerge.Poly := [(nat_lit 621, Int.ofNat (nat_lit 27666530673600)), (nat_lit 622, Int.ofNat (nat_lit 27256961995200))]
theorem block007_data_flat133_step : block007_data_flat133 = (CoefficientMerge.fastMerge block007_data_flat131 block007_data_flat132) := by decide +kernel
theorem block007_data_flat133_original : block007_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27666530673600 : Int) atom0484Coded) (CoefficientMerge.scale (27256961995200 : Int) atom0485Coded)) := by
  rw [block007_data_flat133_step, block007_data_flat131_original, block007_data_flat132_original]
def block007_data_flat134 : CoefficientMerge.Poly := [(nat_lit 620, Int.ofNat (nat_lit 30904307582400)), (nat_lit 621, Int.ofNat (nat_lit 27666530673600)), (nat_lit 622, Int.ofNat (nat_lit 27256961995200))]
theorem block007_data_flat134_step : block007_data_flat134 = (CoefficientMerge.fastMerge block007_data_flat130 block007_data_flat133) := by decide +kernel
theorem block007_data_flat134_original : block007_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30904307582400 : Int) atom0483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27666530673600 : Int) atom0484Coded) (CoefficientMerge.scale (27256961995200 : Int) atom0485Coded))) := by
  rw [block007_data_flat134_step, block007_data_flat130_original, block007_data_flat133_original]
def block007_data_flat135 : CoefficientMerge.Poly := [(nat_lit 618, Int.ofNat (nat_lit 32761969339680)), (nat_lit 619, Int.ofNat (nat_lit 31025713320000)), (nat_lit 620, Int.ofNat (nat_lit 30904307582400)), (nat_lit 621, Int.ofNat (nat_lit 27666530673600)), (nat_lit 622, Int.ofNat (nat_lit 27256961995200))]
theorem block007_data_flat135_step : block007_data_flat135 = (CoefficientMerge.fastMerge block007_data_flat129 block007_data_flat134) := by decide +kernel
theorem block007_data_flat135_original : block007_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32761969339680 : Int) atom0481Coded) (CoefficientMerge.scale (31025713320000 : Int) atom0482Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30904307582400 : Int) atom0483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27666530673600 : Int) atom0484Coded) (CoefficientMerge.scale (27256961995200 : Int) atom0485Coded)))) := by
  rw [block007_data_flat135_step, block007_data_flat129_original, block007_data_flat134_original]
def block007_data_flat136 : CoefficientMerge.Poly := [(nat_lit 605, Int.ofNat (nat_lit 35291136907008)), (nat_lit 606, Int.ofNat (nat_lit 34288248159360)), (nat_lit 607, Int.ofNat (nat_lit 34242389905920)), (nat_lit 608, Int.ofNat (nat_lit 32868397290240)), (nat_lit 617, Int.ofNat (nat_lit 18294922245600)), (nat_lit 618, Int.ofNat (nat_lit 32761969339680)), (nat_lit 619, Int.ofNat (nat_lit 31025713320000)), (nat_lit 620, Int.ofNat (nat_lit 30904307582400)), (nat_lit 621, Int.ofNat (nat_lit 27666530673600)), (nat_lit 622, Int.ofNat (nat_lit 27256961995200))]
theorem block007_data_flat136_step : block007_data_flat136 = (CoefficientMerge.fastMerge block007_data_flat126 block007_data_flat135) := by decide +kernel
theorem block007_data_flat136_original : block007_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35291136907008 : Int) atom0476Coded) (CoefficientMerge.scale (34288248159360 : Int) atom0477Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34242389905920 : Int) atom0478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32868397290240 : Int) atom0479Coded) (CoefficientMerge.scale (18294922245600 : Int) atom0480Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32761969339680 : Int) atom0481Coded) (CoefficientMerge.scale (31025713320000 : Int) atom0482Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30904307582400 : Int) atom0483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27666530673600 : Int) atom0484Coded) (CoefficientMerge.scale (27256961995200 : Int) atom0485Coded))))) := by
  rw [block007_data_flat136_step, block007_data_flat126_original, block007_data_flat135_original]
def block007_data_flat137 : CoefficientMerge.Poly := [(nat_lit 623, Int.ofNat (nat_lit 28163511230400))]
theorem block007_data_flat137_step : block007_data_flat137 = (CoefficientMerge.scale (28163511230400 : Int) atom0486Coded) := by decide +kernel
theorem block007_data_flat137_original : block007_data_flat137 = (CoefficientMerge.scale (28163511230400 : Int) atom0486Coded) := by
  rw [block007_data_flat137_step]
def block007_data_flat138 : CoefficientMerge.Poly := [(nat_lit 624, Int.ofNat (nat_lit 37846980864000))]
theorem block007_data_flat138_step : block007_data_flat138 = (CoefficientMerge.scale (37846980864000 : Int) atom0487Coded) := by decide +kernel
theorem block007_data_flat138_original : block007_data_flat138 = (CoefficientMerge.scale (37846980864000 : Int) atom0487Coded) := by
  rw [block007_data_flat138_step]
def block007_data_flat139 : CoefficientMerge.Poly := [(nat_lit 623, Int.ofNat (nat_lit 28163511230400)), (nat_lit 624, Int.ofNat (nat_lit 37846980864000))]
theorem block007_data_flat139_step : block007_data_flat139 = (CoefficientMerge.fastMerge block007_data_flat137 block007_data_flat138) := by decide +kernel
theorem block007_data_flat139_original : block007_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28163511230400 : Int) atom0486Coded) (CoefficientMerge.scale (37846980864000 : Int) atom0487Coded)) := by
  rw [block007_data_flat139_step, block007_data_flat137_original, block007_data_flat138_original]
def block007_data_flat140 : CoefficientMerge.Poly := [(nat_lit 625, Int.ofNat (nat_lit 32247885612600))]
theorem block007_data_flat140_step : block007_data_flat140 = (CoefficientMerge.scale (32247885612600 : Int) atom0488Coded) := by decide +kernel
theorem block007_data_flat140_original : block007_data_flat140 = (CoefficientMerge.scale (32247885612600 : Int) atom0488Coded) := by
  rw [block007_data_flat140_step]
def block007_data_flat141 : CoefficientMerge.Poly := [(nat_lit 626, Int.ofNat (nat_lit 38259355276800))]
theorem block007_data_flat141_step : block007_data_flat141 = (CoefficientMerge.scale (38259355276800 : Int) atom0489Coded) := by decide +kernel
theorem block007_data_flat141_original : block007_data_flat141 = (CoefficientMerge.scale (38259355276800 : Int) atom0489Coded) := by
  rw [block007_data_flat141_step]
def block007_data_flat142 : CoefficientMerge.Poly := [(nat_lit 627, Int.ofNat (nat_lit 37134500898600))]
theorem block007_data_flat142_step : block007_data_flat142 = (CoefficientMerge.scale (37134500898600 : Int) atom0490Coded) := by decide +kernel
theorem block007_data_flat142_original : block007_data_flat142 = (CoefficientMerge.scale (37134500898600 : Int) atom0490Coded) := by
  rw [block007_data_flat142_step]
def block007_data_flat143 : CoefficientMerge.Poly := [(nat_lit 626, Int.ofNat (nat_lit 38259355276800)), (nat_lit 627, Int.ofNat (nat_lit 37134500898600))]
theorem block007_data_flat143_step : block007_data_flat143 = (CoefficientMerge.fastMerge block007_data_flat141 block007_data_flat142) := by decide +kernel
theorem block007_data_flat143_original : block007_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (38259355276800 : Int) atom0489Coded) (CoefficientMerge.scale (37134500898600 : Int) atom0490Coded)) := by
  rw [block007_data_flat143_step, block007_data_flat141_original, block007_data_flat142_original]
def block007_data_flat144 : CoefficientMerge.Poly := [(nat_lit 625, Int.ofNat (nat_lit 32247885612600)), (nat_lit 626, Int.ofNat (nat_lit 38259355276800)), (nat_lit 627, Int.ofNat (nat_lit 37134500898600))]
theorem block007_data_flat144_step : block007_data_flat144 = (CoefficientMerge.fastMerge block007_data_flat140 block007_data_flat143) := by decide +kernel
theorem block007_data_flat144_original : block007_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (32247885612600 : Int) atom0488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38259355276800 : Int) atom0489Coded) (CoefficientMerge.scale (37134500898600 : Int) atom0490Coded))) := by
  rw [block007_data_flat144_step, block007_data_flat140_original, block007_data_flat143_original]
def block007_data_flat145 : CoefficientMerge.Poly := [(nat_lit 623, Int.ofNat (nat_lit 28163511230400)), (nat_lit 624, Int.ofNat (nat_lit 37846980864000)), (nat_lit 625, Int.ofNat (nat_lit 32247885612600)), (nat_lit 626, Int.ofNat (nat_lit 38259355276800)), (nat_lit 627, Int.ofNat (nat_lit 37134500898600))]
theorem block007_data_flat145_step : block007_data_flat145 = (CoefficientMerge.fastMerge block007_data_flat139 block007_data_flat144) := by decide +kernel
theorem block007_data_flat145_original : block007_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (28163511230400 : Int) atom0486Coded) (CoefficientMerge.scale (37846980864000 : Int) atom0487Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32247885612600 : Int) atom0488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38259355276800 : Int) atom0489Coded) (CoefficientMerge.scale (37134500898600 : Int) atom0490Coded)))) := by
  rw [block007_data_flat145_step, block007_data_flat139_original, block007_data_flat144_original]
def block007_data_flat146 : CoefficientMerge.Poly := [(nat_lit 628, Int.ofNat (nat_lit 34636711842600))]
theorem block007_data_flat146_step : block007_data_flat146 = (CoefficientMerge.scale (34636711842600 : Int) atom0491Coded) := by decide +kernel
theorem block007_data_flat146_original : block007_data_flat146 = (CoefficientMerge.scale (34636711842600 : Int) atom0491Coded) := by
  rw [block007_data_flat146_step]
def block007_data_flat147 : CoefficientMerge.Poly := [(nat_lit 629, Int.ofNat (nat_lit 34485486071400))]
theorem block007_data_flat147_step : block007_data_flat147 = (CoefficientMerge.scale (34485486071400 : Int) atom0492Coded) := by decide +kernel
theorem block007_data_flat147_original : block007_data_flat147 = (CoefficientMerge.scale (34485486071400 : Int) atom0492Coded) := by
  rw [block007_data_flat147_step]
def block007_data_flat148 : CoefficientMerge.Poly := [(nat_lit 628, Int.ofNat (nat_lit 34636711842600)), (nat_lit 629, Int.ofNat (nat_lit 34485486071400))]
theorem block007_data_flat148_step : block007_data_flat148 = (CoefficientMerge.fastMerge block007_data_flat146 block007_data_flat147) := by decide +kernel
theorem block007_data_flat148_original : block007_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34636711842600 : Int) atom0491Coded) (CoefficientMerge.scale (34485486071400 : Int) atom0492Coded)) := by
  rw [block007_data_flat148_step, block007_data_flat146_original, block007_data_flat147_original]
def block007_data_flat149 : CoefficientMerge.Poly := [(nat_lit 639, Int.ofNat (nat_lit 20214453268800))]
theorem block007_data_flat149_step : block007_data_flat149 = (CoefficientMerge.scale (20214453268800 : Int) atom0493Coded) := by decide +kernel
theorem block007_data_flat149_original : block007_data_flat149 = (CoefficientMerge.scale (20214453268800 : Int) atom0493Coded) := by
  rw [block007_data_flat149_step]
def block007_data_flat150 : CoefficientMerge.Poly := [(nat_lit 640, Int.ofNat (nat_lit 36537606766080))]
theorem block007_data_flat150_step : block007_data_flat150 = (CoefficientMerge.scale (36537606766080 : Int) atom0494Coded) := by decide +kernel
theorem block007_data_flat150_original : block007_data_flat150 = (CoefficientMerge.scale (36537606766080 : Int) atom0494Coded) := by
  rw [block007_data_flat150_step]
def block007_data_flat151 : CoefficientMerge.Poly := [(nat_lit 641, Int.ofNat (nat_lit 33634828080000))]
theorem block007_data_flat151_step : block007_data_flat151 = (CoefficientMerge.scale (33634828080000 : Int) atom0495Coded) := by decide +kernel
theorem block007_data_flat151_original : block007_data_flat151 = (CoefficientMerge.scale (33634828080000 : Int) atom0495Coded) := by
  rw [block007_data_flat151_step]
def block007_data_flat152 : CoefficientMerge.Poly := [(nat_lit 640, Int.ofNat (nat_lit 36537606766080)), (nat_lit 641, Int.ofNat (nat_lit 33634828080000))]
theorem block007_data_flat152_step : block007_data_flat152 = (CoefficientMerge.fastMerge block007_data_flat150 block007_data_flat151) := by decide +kernel
theorem block007_data_flat152_original : block007_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36537606766080 : Int) atom0494Coded) (CoefficientMerge.scale (33634828080000 : Int) atom0495Coded)) := by
  rw [block007_data_flat152_step, block007_data_flat150_original, block007_data_flat151_original]
def block007_data_flat153 : CoefficientMerge.Poly := [(nat_lit 639, Int.ofNat (nat_lit 20214453268800)), (nat_lit 640, Int.ofNat (nat_lit 36537606766080)), (nat_lit 641, Int.ofNat (nat_lit 33634828080000))]
theorem block007_data_flat153_step : block007_data_flat153 = (CoefficientMerge.fastMerge block007_data_flat149 block007_data_flat152) := by decide +kernel
theorem block007_data_flat153_original : block007_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20214453268800 : Int) atom0493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36537606766080 : Int) atom0494Coded) (CoefficientMerge.scale (33634828080000 : Int) atom0495Coded))) := by
  rw [block007_data_flat153_step, block007_data_flat149_original, block007_data_flat152_original]
def block007_data_flat154 : CoefficientMerge.Poly := [(nat_lit 628, Int.ofNat (nat_lit 34636711842600)), (nat_lit 629, Int.ofNat (nat_lit 34485486071400)), (nat_lit 639, Int.ofNat (nat_lit 20214453268800)), (nat_lit 640, Int.ofNat (nat_lit 36537606766080)), (nat_lit 641, Int.ofNat (nat_lit 33634828080000))]
theorem block007_data_flat154_step : block007_data_flat154 = (CoefficientMerge.fastMerge block007_data_flat148 block007_data_flat153) := by decide +kernel
theorem block007_data_flat154_original : block007_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34636711842600 : Int) atom0491Coded) (CoefficientMerge.scale (34485486071400 : Int) atom0492Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20214453268800 : Int) atom0493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36537606766080 : Int) atom0494Coded) (CoefficientMerge.scale (33634828080000 : Int) atom0495Coded)))) := by
  rw [block007_data_flat154_step, block007_data_flat148_original, block007_data_flat153_original]
def block007_data_flat155 : CoefficientMerge.Poly := [(nat_lit 623, Int.ofNat (nat_lit 28163511230400)), (nat_lit 624, Int.ofNat (nat_lit 37846980864000)), (nat_lit 625, Int.ofNat (nat_lit 32247885612600)), (nat_lit 626, Int.ofNat (nat_lit 38259355276800)), (nat_lit 627, Int.ofNat (nat_lit 37134500898600)), (nat_lit 628, Int.ofNat (nat_lit 34636711842600)), (nat_lit 629, Int.ofNat (nat_lit 34485486071400)), (nat_lit 639, Int.ofNat (nat_lit 20214453268800)), (nat_lit 640, Int.ofNat (nat_lit 36537606766080)), (nat_lit 641, Int.ofNat (nat_lit 33634828080000))]
theorem block007_data_flat155_step : block007_data_flat155 = (CoefficientMerge.fastMerge block007_data_flat145 block007_data_flat154) := by decide +kernel
theorem block007_data_flat155_original : block007_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (28163511230400 : Int) atom0486Coded) (CoefficientMerge.scale (37846980864000 : Int) atom0487Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32247885612600 : Int) atom0488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38259355276800 : Int) atom0489Coded) (CoefficientMerge.scale (37134500898600 : Int) atom0490Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34636711842600 : Int) atom0491Coded) (CoefficientMerge.scale (34485486071400 : Int) atom0492Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20214453268800 : Int) atom0493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36537606766080 : Int) atom0494Coded) (CoefficientMerge.scale (33634828080000 : Int) atom0495Coded))))) := by
  rw [block007_data_flat155_step, block007_data_flat145_original, block007_data_flat154_original]
def block007_data_flat156 : CoefficientMerge.Poly := [(nat_lit 605, Int.ofNat (nat_lit 35291136907008)), (nat_lit 606, Int.ofNat (nat_lit 34288248159360)), (nat_lit 607, Int.ofNat (nat_lit 34242389905920)), (nat_lit 608, Int.ofNat (nat_lit 32868397290240)), (nat_lit 617, Int.ofNat (nat_lit 18294922245600)), (nat_lit 618, Int.ofNat (nat_lit 32761969339680)), (nat_lit 619, Int.ofNat (nat_lit 31025713320000)), (nat_lit 620, Int.ofNat (nat_lit 30904307582400)), (nat_lit 621, Int.ofNat (nat_lit 27666530673600)), (nat_lit 622, Int.ofNat (nat_lit 27256961995200)), (nat_lit 623, Int.ofNat (nat_lit 28163511230400)), (nat_lit 624, Int.ofNat (nat_lit 37846980864000)), (nat_lit 625, Int.ofNat (nat_lit 32247885612600)), (nat_lit 626, Int.ofNat (nat_lit 38259355276800)), (nat_lit 627, Int.ofNat (nat_lit 37134500898600)), (nat_lit 628, Int.ofNat (nat_lit 34636711842600)), (nat_lit 629, Int.ofNat (nat_lit 34485486071400)), (nat_lit 639, Int.ofNat (nat_lit 20214453268800)), (nat_lit 640, Int.ofNat (nat_lit 36537606766080)), (nat_lit 641, Int.ofNat (nat_lit 33634828080000))]
theorem block007_data_flat156_step : block007_data_flat156 = (CoefficientMerge.fastMerge block007_data_flat136 block007_data_flat155) := by decide +kernel
theorem block007_data_flat156_original : block007_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35291136907008 : Int) atom0476Coded) (CoefficientMerge.scale (34288248159360 : Int) atom0477Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34242389905920 : Int) atom0478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32868397290240 : Int) atom0479Coded) (CoefficientMerge.scale (18294922245600 : Int) atom0480Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32761969339680 : Int) atom0481Coded) (CoefficientMerge.scale (31025713320000 : Int) atom0482Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30904307582400 : Int) atom0483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27666530673600 : Int) atom0484Coded) (CoefficientMerge.scale (27256961995200 : Int) atom0485Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (28163511230400 : Int) atom0486Coded) (CoefficientMerge.scale (37846980864000 : Int) atom0487Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32247885612600 : Int) atom0488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38259355276800 : Int) atom0489Coded) (CoefficientMerge.scale (37134500898600 : Int) atom0490Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34636711842600 : Int) atom0491Coded) (CoefficientMerge.scale (34485486071400 : Int) atom0492Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20214453268800 : Int) atom0493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36537606766080 : Int) atom0494Coded) (CoefficientMerge.scale (33634828080000 : Int) atom0495Coded)))))) := by
  rw [block007_data_flat156_step, block007_data_flat136_original, block007_data_flat155_original]
def block007_data_flat157 : CoefficientMerge.Poly := [(nat_lit 578, Int.ofNat (nat_lit 22899764966400)), (nat_lit 579, Int.ofNat (nat_lit 20036978572800)), (nat_lit 580, Int.ofNat (nat_lit 19788810451200)), (nat_lit 581, Int.ofNat (nat_lit 20856760243200)), (nat_lit 582, Int.ofNat (nat_lit 31352628787200)), (nat_lit 583, Int.ofNat (nat_lit 25110779097600)), (nat_lit 584, Int.ofNat (nat_lit 30419676403200)), (nat_lit 585, Int.ofNat (nat_lit 30013882214400)), (nat_lit 586, Int.ofNat (nat_lit 33459931814400)), (nat_lit 587, Int.ofNat (nat_lit 32426062099200)), (nat_lit 595, Int.ofNat (nat_lit 16601669556480)), (nat_lit 596, Int.ofNat (nat_lit 29149185627360)), (nat_lit 597, Int.ofNat (nat_lit 27058453117056)), (nat_lit 598, Int.ofNat (nat_lit 27527674496256)), (nat_lit 599, Int.ofNat (nat_lit 27658517533056)), (nat_lit 600, Int.ofNat (nat_lit 24757072323456)), (nat_lit 601, Int.ofNat (nat_lit 24470245385856)), (nat_lit 602, Int.ofNat (nat_lit 25499536361856)), (nat_lit 603, Int.ofNat (nat_lit 35551425892608)), (nat_lit 604, Int.ofNat (nat_lit 29604979281024)), (nat_lit 605, Int.ofNat (nat_lit 35291136907008)), (nat_lit 606, Int.ofNat (nat_lit 34288248159360)), (nat_lit 607, Int.ofNat (nat_lit 34242389905920)), (nat_lit 608, Int.ofNat (nat_lit 32868397290240)), (nat_lit 617, Int.ofNat (nat_lit 18294922245600)), (nat_lit 618, Int.ofNat (nat_lit 32761969339680)), (nat_lit 619, Int.ofNat (nat_lit 31025713320000)), (nat_lit 620, Int.ofNat (nat_lit 30904307582400)), (nat_lit 621, Int.ofNat (nat_lit 27666530673600)), (nat_lit 622, Int.ofNat (nat_lit 27256961995200)), (nat_lit 623, Int.ofNat (nat_lit 28163511230400)), (nat_lit 624, Int.ofNat (nat_lit 37846980864000)), (nat_lit 625, Int.ofNat (nat_lit 32247885612600)), (nat_lit 626, Int.ofNat (nat_lit 38259355276800)), (nat_lit 627, Int.ofNat (nat_lit 37134500898600)), (nat_lit 628, Int.ofNat (nat_lit 34636711842600)), (nat_lit 629, Int.ofNat (nat_lit 34485486071400)), (nat_lit 639, Int.ofNat (nat_lit 20214453268800)), (nat_lit 640, Int.ofNat (nat_lit 36537606766080)), (nat_lit 641, Int.ofNat (nat_lit 33634828080000))]
theorem block007_data_flat157_step : block007_data_flat157 = (CoefficientMerge.fastMerge block007_data_flat117 block007_data_flat156) := by decide +kernel
theorem block007_data_flat157_original : block007_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22899764966400 : Int) atom0456Coded) (CoefficientMerge.scale (20036978572800 : Int) atom0457Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19788810451200 : Int) atom0458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20856760243200 : Int) atom0459Coded) (CoefficientMerge.scale (31352628787200 : Int) atom0460Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25110779097600 : Int) atom0461Coded) (CoefficientMerge.scale (30419676403200 : Int) atom0462Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30013882214400 : Int) atom0463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33459931814400 : Int) atom0464Coded) (CoefficientMerge.scale (32426062099200 : Int) atom0465Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16601669556480 : Int) atom0466Coded) (CoefficientMerge.scale (29149185627360 : Int) atom0467Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27058453117056 : Int) atom0468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27527674496256 : Int) atom0469Coded) (CoefficientMerge.scale (27658517533056 : Int) atom0470Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24757072323456 : Int) atom0471Coded) (CoefficientMerge.scale (24470245385856 : Int) atom0472Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25499536361856 : Int) atom0473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35551425892608 : Int) atom0474Coded) (CoefficientMerge.scale (29604979281024 : Int) atom0475Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35291136907008 : Int) atom0476Coded) (CoefficientMerge.scale (34288248159360 : Int) atom0477Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34242389905920 : Int) atom0478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32868397290240 : Int) atom0479Coded) (CoefficientMerge.scale (18294922245600 : Int) atom0480Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32761969339680 : Int) atom0481Coded) (CoefficientMerge.scale (31025713320000 : Int) atom0482Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30904307582400 : Int) atom0483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27666530673600 : Int) atom0484Coded) (CoefficientMerge.scale (27256961995200 : Int) atom0485Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (28163511230400 : Int) atom0486Coded) (CoefficientMerge.scale (37846980864000 : Int) atom0487Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32247885612600 : Int) atom0488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38259355276800 : Int) atom0489Coded) (CoefficientMerge.scale (37134500898600 : Int) atom0490Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34636711842600 : Int) atom0491Coded) (CoefficientMerge.scale (34485486071400 : Int) atom0492Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20214453268800 : Int) atom0493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36537606766080 : Int) atom0494Coded) (CoefficientMerge.scale (33634828080000 : Int) atom0495Coded))))))) := by
  rw [block007_data_flat157_step, block007_data_flat117_original, block007_data_flat156_original]
def block007_data_flat158 : CoefficientMerge.Poly := [(nat_lit 523, Int.ofNat (nat_lit 14423604249600)), (nat_lit 524, Int.ofNat (nat_lit 11360537395200)), (nat_lit 529, Int.ofNat (nat_lit 7526146622400)), (nat_lit 530, Int.ofNat (nat_lit 14464310141952)), (nat_lit 531, Int.ofNat (nat_lit 14992217856000)), (nat_lit 532, Int.ofNat (nat_lit 17536417636608)), (nat_lit 533, Int.ofNat (nat_lit 18177375283200)), (nat_lit 534, Int.ofNat (nat_lit 18668342246400)), (nat_lit 535, Int.ofNat (nat_lit 19159309209600)), (nat_lit 536, Int.ofNat (nat_lit 19026429004800)), (nat_lit 537, Int.ofNat (nat_lit 15199948444800)), (nat_lit 538, Int.ofNat (nat_lit 14776849180800)), (nat_lit 539, Int.ofNat (nat_lit 15669867830400)), (nat_lit 540, Int.ofNat (nat_lit 24880813977600)), (nat_lit 541, Int.ofNat (nat_lit 18272069247600)), (nat_lit 542, Int.ofNat (nat_lit 22602534796800)), (nat_lit 543, Int.ofNat (nat_lit 20221399774800)), (nat_lit 544, Int.ofNat (nat_lit 21663695768400)), (nat_lit 545, Int.ofNat (nat_lit 17565700194000)), (nat_lit 551, Int.ofNat (nat_lit 11219811941376)), (nat_lit 552, Int.ofNat (nat_lit 19865648451456)), (nat_lit 553, Int.ofNat (nat_lit 19588073217408)), (nat_lit 554, Int.ofNat (nat_lit 20097013768704)), (nat_lit 555, Int.ofNat (nat_lit 21289155007104)), (nat_lit 556, Int.ofNat (nat_lit 21751611093504)), (nat_lit 557, Int.ofNat (nat_lit 21955062587904)), (nat_lit 558, Int.ofNat (nat_lit 18753888376704)), (nat_lit 559, Int.ofNat (nat_lit 18329339407104)), (nat_lit 560, Int.ofNat (nat_lit 19351865090304)), (nat_lit 561, Int.ofNat (nat_lit 29154774357504)), (nat_lit 562, Int.ofNat (nat_lit 22695246099072)), (nat_lit 563, Int.ofNat (nat_lit 27549158575104)), (nat_lit 564, Int.ofNat (nat_lit 25867921742208)), (nat_lit 565, Int.ofNat (nat_lit 27674310760320)), (nat_lit 566, Int.ofNat (nat_lit 23463825855168)), (nat_lit 573, Int.ofNat (nat_lit 14524199424000)), (nat_lit 574, Int.ofNat (nat_lit 25592052764160)), (nat_lit 575, Int.ofNat (nat_lit 23065383297600)), (nat_lit 576, Int.ofNat (nat_lit 22222382918400)), (nat_lit 577, Int.ofNat (nat_lit 22859770147200)), (nat_lit 578, Int.ofNat (nat_lit 22899764966400)), (nat_lit 579, Int.ofNat (nat_lit 20036978572800)), (nat_lit 580, Int.ofNat (nat_lit 19788810451200)), (nat_lit 581, Int.ofNat (nat_lit 20856760243200)), (nat_lit 582, Int.ofNat (nat_lit 31352628787200)), (nat_lit 583, Int.ofNat (nat_lit 25110779097600)), (nat_lit 584, Int.ofNat (nat_lit 30419676403200)), (nat_lit 585, Int.ofNat (nat_lit 30013882214400)), (nat_lit 586, Int.ofNat (nat_lit 33459931814400)), (nat_lit 587, Int.ofNat (nat_lit 32426062099200)), (nat_lit 595, Int.ofNat (nat_lit 16601669556480)), (nat_lit 596, Int.ofNat (nat_lit 29149185627360)), (nat_lit 597, Int.ofNat (nat_lit 27058453117056)), (nat_lit 598, Int.ofNat (nat_lit 27527674496256)), (nat_lit 599, Int.ofNat (nat_lit 27658517533056)), (nat_lit 600, Int.ofNat (nat_lit 24757072323456)), (nat_lit 601, Int.ofNat (nat_lit 24470245385856)), (nat_lit 602, Int.ofNat (nat_lit 25499536361856)), (nat_lit 603, Int.ofNat (nat_lit 35551425892608)), (nat_lit 604, Int.ofNat (nat_lit 29604979281024)), (nat_lit 605, Int.ofNat (nat_lit 35291136907008)), (nat_lit 606, Int.ofNat (nat_lit 34288248159360)), (nat_lit 607, Int.ofNat (nat_lit 34242389905920)), (nat_lit 608, Int.ofNat (nat_lit 32868397290240)), (nat_lit 617, Int.ofNat (nat_lit 18294922245600)), (nat_lit 618, Int.ofNat (nat_lit 32761969339680)), (nat_lit 619, Int.ofNat (nat_lit 31025713320000)), (nat_lit 620, Int.ofNat (nat_lit 30904307582400)), (nat_lit 621, Int.ofNat (nat_lit 27666530673600)), (nat_lit 622, Int.ofNat (nat_lit 27256961995200)), (nat_lit 623, Int.ofNat (nat_lit 28163511230400)), (nat_lit 624, Int.ofNat (nat_lit 37846980864000)), (nat_lit 625, Int.ofNat (nat_lit 32247885612600)), (nat_lit 626, Int.ofNat (nat_lit 38259355276800)), (nat_lit 627, Int.ofNat (nat_lit 37134500898600)), (nat_lit 628, Int.ofNat (nat_lit 34636711842600)), (nat_lit 629, Int.ofNat (nat_lit 34485486071400)), (nat_lit 639, Int.ofNat (nat_lit 20214453268800)), (nat_lit 640, Int.ofNat (nat_lit 36537606766080)), (nat_lit 641, Int.ofNat (nat_lit 33634828080000))]
theorem block007_data_flat158_step : block007_data_flat158 = (CoefficientMerge.fastMerge block007_data_flat078 block007_data_flat157) := by decide +kernel
theorem block007_data_flat158_original : block007_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14423604249600 : Int) atom0416Coded) (CoefficientMerge.scale (11360537395200 : Int) atom0417Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7526146622400 : Int) atom0418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14464310141952 : Int) atom0419Coded) (CoefficientMerge.scale (14992217856000 : Int) atom0420Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17536417636608 : Int) atom0421Coded) (CoefficientMerge.scale (18177375283200 : Int) atom0422Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18668342246400 : Int) atom0423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19159309209600 : Int) atom0424Coded) (CoefficientMerge.scale (19026429004800 : Int) atom0425Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15199948444800 : Int) atom0426Coded) (CoefficientMerge.scale (14776849180800 : Int) atom0427Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15669867830400 : Int) atom0428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24880813977600 : Int) atom0429Coded) (CoefficientMerge.scale (18272069247600 : Int) atom0430Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22602534796800 : Int) atom0431Coded) (CoefficientMerge.scale (20221399774800 : Int) atom0432Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21663695768400 : Int) atom0433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17565700194000 : Int) atom0434Coded) (CoefficientMerge.scale (11219811941376 : Int) atom0435Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19865648451456 : Int) atom0436Coded) (CoefficientMerge.scale (19588073217408 : Int) atom0437Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20097013768704 : Int) atom0438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21289155007104 : Int) atom0439Coded) (CoefficientMerge.scale (21751611093504 : Int) atom0440Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21955062587904 : Int) atom0441Coded) (CoefficientMerge.scale (18753888376704 : Int) atom0442Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18329339407104 : Int) atom0443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19351865090304 : Int) atom0444Coded) (CoefficientMerge.scale (29154774357504 : Int) atom0445Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22695246099072 : Int) atom0446Coded) (CoefficientMerge.scale (27549158575104 : Int) atom0447Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25867921742208 : Int) atom0448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27674310760320 : Int) atom0449Coded) (CoefficientMerge.scale (23463825855168 : Int) atom0450Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14524199424000 : Int) atom0451Coded) (CoefficientMerge.scale (25592052764160 : Int) atom0452Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23065383297600 : Int) atom0453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22222382918400 : Int) atom0454Coded) (CoefficientMerge.scale (22859770147200 : Int) atom0455Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22899764966400 : Int) atom0456Coded) (CoefficientMerge.scale (20036978572800 : Int) atom0457Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19788810451200 : Int) atom0458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20856760243200 : Int) atom0459Coded) (CoefficientMerge.scale (31352628787200 : Int) atom0460Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25110779097600 : Int) atom0461Coded) (CoefficientMerge.scale (30419676403200 : Int) atom0462Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30013882214400 : Int) atom0463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33459931814400 : Int) atom0464Coded) (CoefficientMerge.scale (32426062099200 : Int) atom0465Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16601669556480 : Int) atom0466Coded) (CoefficientMerge.scale (29149185627360 : Int) atom0467Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27058453117056 : Int) atom0468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27527674496256 : Int) atom0469Coded) (CoefficientMerge.scale (27658517533056 : Int) atom0470Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24757072323456 : Int) atom0471Coded) (CoefficientMerge.scale (24470245385856 : Int) atom0472Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25499536361856 : Int) atom0473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35551425892608 : Int) atom0474Coded) (CoefficientMerge.scale (29604979281024 : Int) atom0475Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35291136907008 : Int) atom0476Coded) (CoefficientMerge.scale (34288248159360 : Int) atom0477Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34242389905920 : Int) atom0478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32868397290240 : Int) atom0479Coded) (CoefficientMerge.scale (18294922245600 : Int) atom0480Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32761969339680 : Int) atom0481Coded) (CoefficientMerge.scale (31025713320000 : Int) atom0482Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30904307582400 : Int) atom0483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27666530673600 : Int) atom0484Coded) (CoefficientMerge.scale (27256961995200 : Int) atom0485Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (28163511230400 : Int) atom0486Coded) (CoefficientMerge.scale (37846980864000 : Int) atom0487Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32247885612600 : Int) atom0488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38259355276800 : Int) atom0489Coded) (CoefficientMerge.scale (37134500898600 : Int) atom0490Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34636711842600 : Int) atom0491Coded) (CoefficientMerge.scale (34485486071400 : Int) atom0492Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20214453268800 : Int) atom0493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36537606766080 : Int) atom0494Coded) (CoefficientMerge.scale (33634828080000 : Int) atom0495Coded)))))))) := by
  rw [block007_data_flat158_step, block007_data_flat078_original, block007_data_flat157_original]
def block007_data_flat159 : CoefficientMerge.Poly := [(nat_lit 523, Int.ofNat (nat_lit 14423604249600)), (nat_lit 524, Int.ofNat (nat_lit 11360537395200)), (nat_lit 529, Int.ofNat (nat_lit 7526146622400)), (nat_lit 530, Int.ofNat (nat_lit 14464310141952)), (nat_lit 531, Int.ofNat (nat_lit 14992217856000)), (nat_lit 532, Int.ofNat (nat_lit 17536417636608)), (nat_lit 533, Int.ofNat (nat_lit 18177375283200)), (nat_lit 534, Int.ofNat (nat_lit 18668342246400)), (nat_lit 535, Int.ofNat (nat_lit 19159309209600)), (nat_lit 536, Int.ofNat (nat_lit 19026429004800)), (nat_lit 537, Int.ofNat (nat_lit 15199948444800)), (nat_lit 538, Int.ofNat (nat_lit 14776849180800)), (nat_lit 539, Int.ofNat (nat_lit 15669867830400)), (nat_lit 540, Int.ofNat (nat_lit 24880813977600)), (nat_lit 541, Int.ofNat (nat_lit 18272069247600)), (nat_lit 542, Int.ofNat (nat_lit 22602534796800)), (nat_lit 543, Int.ofNat (nat_lit 20221399774800)), (nat_lit 544, Int.ofNat (nat_lit 21663695768400)), (nat_lit 545, Int.ofNat (nat_lit 17565700194000)), (nat_lit 551, Int.ofNat (nat_lit 11219811941376)), (nat_lit 552, Int.ofNat (nat_lit 19865648451456)), (nat_lit 553, Int.ofNat (nat_lit 19588073217408)), (nat_lit 554, Int.ofNat (nat_lit 20097013768704)), (nat_lit 555, Int.ofNat (nat_lit 21289155007104)), (nat_lit 556, Int.ofNat (nat_lit 21751611093504)), (nat_lit 557, Int.ofNat (nat_lit 21955062587904)), (nat_lit 558, Int.ofNat (nat_lit 18753888376704)), (nat_lit 559, Int.ofNat (nat_lit 18329339407104)), (nat_lit 560, Int.ofNat (nat_lit 19351865090304)), (nat_lit 561, Int.ofNat (nat_lit 29154774357504)), (nat_lit 562, Int.ofNat (nat_lit 22695246099072)), (nat_lit 563, Int.ofNat (nat_lit 27549158575104)), (nat_lit 564, Int.ofNat (nat_lit 25867921742208)), (nat_lit 565, Int.ofNat (nat_lit 27674310760320)), (nat_lit 566, Int.ofNat (nat_lit 23463825855168)), (nat_lit 573, Int.ofNat (nat_lit 14524199424000)), (nat_lit 574, Int.ofNat (nat_lit 25592052764160)), (nat_lit 575, Int.ofNat (nat_lit 23065383297600)), (nat_lit 576, Int.ofNat (nat_lit 22222382918400)), (nat_lit 577, Int.ofNat (nat_lit 22859770147200)), (nat_lit 578, Int.ofNat (nat_lit 22899764966400)), (nat_lit 579, Int.ofNat (nat_lit 20036978572800)), (nat_lit 580, Int.ofNat (nat_lit 19788810451200)), (nat_lit 581, Int.ofNat (nat_lit 20856760243200)), (nat_lit 582, Int.ofNat (nat_lit 31352628787200)), (nat_lit 583, Int.ofNat (nat_lit 25110779097600)), (nat_lit 584, Int.ofNat (nat_lit 30419676403200)), (nat_lit 585, Int.ofNat (nat_lit 30013882214400)), (nat_lit 586, Int.ofNat (nat_lit 33459931814400)), (nat_lit 587, Int.ofNat (nat_lit 32426062099200)), (nat_lit 595, Int.ofNat (nat_lit 16601669556480)), (nat_lit 596, Int.ofNat (nat_lit 29149185627360)), (nat_lit 597, Int.ofNat (nat_lit 27058453117056)), (nat_lit 598, Int.ofNat (nat_lit 27527674496256)), (nat_lit 599, Int.ofNat (nat_lit 27658517533056)), (nat_lit 600, Int.ofNat (nat_lit 24757072323456)), (nat_lit 601, Int.ofNat (nat_lit 24470245385856)), (nat_lit 602, Int.ofNat (nat_lit 25499536361856)), (nat_lit 603, Int.ofNat (nat_lit 35551425892608)), (nat_lit 604, Int.ofNat (nat_lit 29604979281024)), (nat_lit 605, Int.ofNat (nat_lit 35291136907008)), (nat_lit 606, Int.ofNat (nat_lit 34288248159360)), (nat_lit 607, Int.ofNat (nat_lit 34242389905920)), (nat_lit 608, Int.ofNat (nat_lit 32868397290240)), (nat_lit 617, Int.ofNat (nat_lit 18294922245600)), (nat_lit 618, Int.ofNat (nat_lit 32761969339680)), (nat_lit 619, Int.ofNat (nat_lit 31025713320000)), (nat_lit 620, Int.ofNat (nat_lit 30904307582400)), (nat_lit 621, Int.ofNat (nat_lit 27666530673600)), (nat_lit 622, Int.ofNat (nat_lit 27256961995200)), (nat_lit 623, Int.ofNat (nat_lit 28163511230400)), (nat_lit 624, Int.ofNat (nat_lit 37846980864000)), (nat_lit 625, Int.ofNat (nat_lit 32247885612600)), (nat_lit 626, Int.ofNat (nat_lit 38259355276800)), (nat_lit 627, Int.ofNat (nat_lit 37134500898600)), (nat_lit 628, Int.ofNat (nat_lit 34636711842600)), (nat_lit 629, Int.ofNat (nat_lit 34485486071400)), (nat_lit 639, Int.ofNat (nat_lit 20214453268800)), (nat_lit 640, Int.ofNat (nat_lit 36537606766080)), (nat_lit 641, Int.ofNat (nat_lit 33634828080000))]
theorem block007_data_flat159_step : block007_data_flat159 = (CoefficientMerge.trim block007_data_flat158) := by decide +kernel
theorem block007_data_flat159_original : block007_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14423604249600 : Int) atom0416Coded) (CoefficientMerge.scale (11360537395200 : Int) atom0417Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7526146622400 : Int) atom0418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14464310141952 : Int) atom0419Coded) (CoefficientMerge.scale (14992217856000 : Int) atom0420Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17536417636608 : Int) atom0421Coded) (CoefficientMerge.scale (18177375283200 : Int) atom0422Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18668342246400 : Int) atom0423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19159309209600 : Int) atom0424Coded) (CoefficientMerge.scale (19026429004800 : Int) atom0425Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15199948444800 : Int) atom0426Coded) (CoefficientMerge.scale (14776849180800 : Int) atom0427Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15669867830400 : Int) atom0428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24880813977600 : Int) atom0429Coded) (CoefficientMerge.scale (18272069247600 : Int) atom0430Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22602534796800 : Int) atom0431Coded) (CoefficientMerge.scale (20221399774800 : Int) atom0432Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21663695768400 : Int) atom0433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17565700194000 : Int) atom0434Coded) (CoefficientMerge.scale (11219811941376 : Int) atom0435Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19865648451456 : Int) atom0436Coded) (CoefficientMerge.scale (19588073217408 : Int) atom0437Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20097013768704 : Int) atom0438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21289155007104 : Int) atom0439Coded) (CoefficientMerge.scale (21751611093504 : Int) atom0440Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21955062587904 : Int) atom0441Coded) (CoefficientMerge.scale (18753888376704 : Int) atom0442Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18329339407104 : Int) atom0443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19351865090304 : Int) atom0444Coded) (CoefficientMerge.scale (29154774357504 : Int) atom0445Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22695246099072 : Int) atom0446Coded) (CoefficientMerge.scale (27549158575104 : Int) atom0447Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25867921742208 : Int) atom0448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27674310760320 : Int) atom0449Coded) (CoefficientMerge.scale (23463825855168 : Int) atom0450Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14524199424000 : Int) atom0451Coded) (CoefficientMerge.scale (25592052764160 : Int) atom0452Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23065383297600 : Int) atom0453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22222382918400 : Int) atom0454Coded) (CoefficientMerge.scale (22859770147200 : Int) atom0455Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22899764966400 : Int) atom0456Coded) (CoefficientMerge.scale (20036978572800 : Int) atom0457Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19788810451200 : Int) atom0458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20856760243200 : Int) atom0459Coded) (CoefficientMerge.scale (31352628787200 : Int) atom0460Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25110779097600 : Int) atom0461Coded) (CoefficientMerge.scale (30419676403200 : Int) atom0462Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30013882214400 : Int) atom0463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33459931814400 : Int) atom0464Coded) (CoefficientMerge.scale (32426062099200 : Int) atom0465Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16601669556480 : Int) atom0466Coded) (CoefficientMerge.scale (29149185627360 : Int) atom0467Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27058453117056 : Int) atom0468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27527674496256 : Int) atom0469Coded) (CoefficientMerge.scale (27658517533056 : Int) atom0470Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24757072323456 : Int) atom0471Coded) (CoefficientMerge.scale (24470245385856 : Int) atom0472Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25499536361856 : Int) atom0473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35551425892608 : Int) atom0474Coded) (CoefficientMerge.scale (29604979281024 : Int) atom0475Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35291136907008 : Int) atom0476Coded) (CoefficientMerge.scale (34288248159360 : Int) atom0477Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34242389905920 : Int) atom0478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32868397290240 : Int) atom0479Coded) (CoefficientMerge.scale (18294922245600 : Int) atom0480Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32761969339680 : Int) atom0481Coded) (CoefficientMerge.scale (31025713320000 : Int) atom0482Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30904307582400 : Int) atom0483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27666530673600 : Int) atom0484Coded) (CoefficientMerge.scale (27256961995200 : Int) atom0485Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (28163511230400 : Int) atom0486Coded) (CoefficientMerge.scale (37846980864000 : Int) atom0487Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32247885612600 : Int) atom0488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38259355276800 : Int) atom0489Coded) (CoefficientMerge.scale (37134500898600 : Int) atom0490Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34636711842600 : Int) atom0491Coded) (CoefficientMerge.scale (34485486071400 : Int) atom0492Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20214453268800 : Int) atom0493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36537606766080 : Int) atom0494Coded) (CoefficientMerge.scale (33634828080000 : Int) atom0495Coded))))))))) := by
  rw [block007_data_flat159_step, block007_data_flat158_original]
theorem block007_data : block007 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14423604249600 : Int) atom0416Coded) (CoefficientMerge.scale (11360537395200 : Int) atom0417Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7526146622400 : Int) atom0418Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14464310141952 : Int) atom0419Coded) (CoefficientMerge.scale (14992217856000 : Int) atom0420Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (17536417636608 : Int) atom0421Coded) (CoefficientMerge.scale (18177375283200 : Int) atom0422Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18668342246400 : Int) atom0423Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19159309209600 : Int) atom0424Coded) (CoefficientMerge.scale (19026429004800 : Int) atom0425Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15199948444800 : Int) atom0426Coded) (CoefficientMerge.scale (14776849180800 : Int) atom0427Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15669867830400 : Int) atom0428Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24880813977600 : Int) atom0429Coded) (CoefficientMerge.scale (18272069247600 : Int) atom0430Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22602534796800 : Int) atom0431Coded) (CoefficientMerge.scale (20221399774800 : Int) atom0432Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21663695768400 : Int) atom0433Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17565700194000 : Int) atom0434Coded) (CoefficientMerge.scale (11219811941376 : Int) atom0435Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (19865648451456 : Int) atom0436Coded) (CoefficientMerge.scale (19588073217408 : Int) atom0437Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20097013768704 : Int) atom0438Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21289155007104 : Int) atom0439Coded) (CoefficientMerge.scale (21751611093504 : Int) atom0440Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21955062587904 : Int) atom0441Coded) (CoefficientMerge.scale (18753888376704 : Int) atom0442Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18329339407104 : Int) atom0443Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19351865090304 : Int) atom0444Coded) (CoefficientMerge.scale (29154774357504 : Int) atom0445Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22695246099072 : Int) atom0446Coded) (CoefficientMerge.scale (27549158575104 : Int) atom0447Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25867921742208 : Int) atom0448Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27674310760320 : Int) atom0449Coded) (CoefficientMerge.scale (23463825855168 : Int) atom0450Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (14524199424000 : Int) atom0451Coded) (CoefficientMerge.scale (25592052764160 : Int) atom0452Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23065383297600 : Int) atom0453Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22222382918400 : Int) atom0454Coded) (CoefficientMerge.scale (22859770147200 : Int) atom0455Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22899764966400 : Int) atom0456Coded) (CoefficientMerge.scale (20036978572800 : Int) atom0457Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (19788810451200 : Int) atom0458Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20856760243200 : Int) atom0459Coded) (CoefficientMerge.scale (31352628787200 : Int) atom0460Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25110779097600 : Int) atom0461Coded) (CoefficientMerge.scale (30419676403200 : Int) atom0462Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30013882214400 : Int) atom0463Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33459931814400 : Int) atom0464Coded) (CoefficientMerge.scale (32426062099200 : Int) atom0465Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16601669556480 : Int) atom0466Coded) (CoefficientMerge.scale (29149185627360 : Int) atom0467Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27058453117056 : Int) atom0468Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27527674496256 : Int) atom0469Coded) (CoefficientMerge.scale (27658517533056 : Int) atom0470Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24757072323456 : Int) atom0471Coded) (CoefficientMerge.scale (24470245385856 : Int) atom0472Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25499536361856 : Int) atom0473Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35551425892608 : Int) atom0474Coded) (CoefficientMerge.scale (29604979281024 : Int) atom0475Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (35291136907008 : Int) atom0476Coded) (CoefficientMerge.scale (34288248159360 : Int) atom0477Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34242389905920 : Int) atom0478Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32868397290240 : Int) atom0479Coded) (CoefficientMerge.scale (18294922245600 : Int) atom0480Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32761969339680 : Int) atom0481Coded) (CoefficientMerge.scale (31025713320000 : Int) atom0482Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30904307582400 : Int) atom0483Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (27666530673600 : Int) atom0484Coded) (CoefficientMerge.scale (27256961995200 : Int) atom0485Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (28163511230400 : Int) atom0486Coded) (CoefficientMerge.scale (37846980864000 : Int) atom0487Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32247885612600 : Int) atom0488Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (38259355276800 : Int) atom0489Coded) (CoefficientMerge.scale (37134500898600 : Int) atom0490Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34636711842600 : Int) atom0491Coded) (CoefficientMerge.scale (34485486071400 : Int) atom0492Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (20214453268800 : Int) atom0493Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (36537606766080 : Int) atom0494Coded) (CoefficientMerge.scale (33634828080000 : Int) atom0495Coded)))))))) := by
  have h : block007 = block007_data_flat159 := by decide +kernel
  exact h.trans block007_data_flat159_original
theorem block007_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block007 := by
  rw [block007_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0416Coded_nonneg g hg hA hB) (atom0417Coded_nonneg g hg hA hB)) (add_nonneg (atom0418Coded_nonneg g hg hA hB) (add_nonneg (atom0419Coded_nonneg g hg hA hB) (atom0420Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0421Coded_nonneg g hg hA hB) (atom0422Coded_nonneg g hg hA hB)) (add_nonneg (atom0423Coded_nonneg g hg hA hB) (add_nonneg (atom0424Coded_nonneg g hg hA hB) (atom0425Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0426Coded_nonneg g hg hA hB) (atom0427Coded_nonneg g hg hA hB)) (add_nonneg (atom0428Coded_nonneg g hg hA hB) (add_nonneg (atom0429Coded_nonneg g hg hA hB) (atom0430Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0431Coded_nonneg g hg hA hB) (atom0432Coded_nonneg g hg hA hB)) (add_nonneg (atom0433Coded_nonneg g hg hA hB) (add_nonneg (atom0434Coded_nonneg g hg hA hB) (atom0435Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0436Coded_nonneg g hg hA hB) (atom0437Coded_nonneg g hg hA hB)) (add_nonneg (atom0438Coded_nonneg g hg hA hB) (add_nonneg (atom0439Coded_nonneg g hg hA hB) (atom0440Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0441Coded_nonneg g hg hA hB) (atom0442Coded_nonneg g hg hA hB)) (add_nonneg (atom0443Coded_nonneg g hg hA hB) (add_nonneg (atom0444Coded_nonneg g hg hA hB) (atom0445Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0446Coded_nonneg g hg hA hB) (atom0447Coded_nonneg g hg hA hB)) (add_nonneg (atom0448Coded_nonneg g hg hA hB) (add_nonneg (atom0449Coded_nonneg g hg hA hB) (atom0450Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0451Coded_nonneg g hg hA hB) (atom0452Coded_nonneg g hg hA hB)) (add_nonneg (atom0453Coded_nonneg g hg hA hB) (add_nonneg (atom0454Coded_nonneg g hg hA hB) (atom0455Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0456Coded_nonneg g hg hA hB) (atom0457Coded_nonneg g hg hA hB)) (add_nonneg (atom0458Coded_nonneg g hg hA hB) (add_nonneg (atom0459Coded_nonneg g hg hA hB) (atom0460Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0461Coded_nonneg g hg hA hB) (atom0462Coded_nonneg g hg hA hB)) (add_nonneg (atom0463Coded_nonneg g hg hA hB) (add_nonneg (atom0464Coded_nonneg g hg hA hB) (atom0465Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0466Coded_nonneg g hg hA hB) (atom0467Coded_nonneg g hg hA hB)) (add_nonneg (atom0468Coded_nonneg g hg hA hB) (add_nonneg (atom0469Coded_nonneg g hg hA hB) (atom0470Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0471Coded_nonneg g hg hA hB) (atom0472Coded_nonneg g hg hA hB)) (add_nonneg (atom0473Coded_nonneg g hg hA hB) (add_nonneg (atom0474Coded_nonneg g hg hA hB) (atom0475Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0476Coded_nonneg g hg hA hB) (atom0477Coded_nonneg g hg hA hB)) (add_nonneg (atom0478Coded_nonneg g hg hA hB) (add_nonneg (atom0479Coded_nonneg g hg hA hB) (atom0480Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0481Coded_nonneg g hg hA hB) (atom0482Coded_nonneg g hg hA hB)) (add_nonneg (atom0483Coded_nonneg g hg hA hB) (add_nonneg (atom0484Coded_nonneg g hg hA hB) (atom0485Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0486Coded_nonneg g hg hA hB) (atom0487Coded_nonneg g hg hA hB)) (add_nonneg (atom0488Coded_nonneg g hg hA hB) (add_nonneg (atom0489Coded_nonneg g hg hA hB) (atom0490Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0491Coded_nonneg g hg hA hB) (atom0492Coded_nonneg g hg hA hB)) (add_nonneg (atom0493Coded_nonneg g hg hA hB) (add_nonneg (atom0494Coded_nonneg g hg hA hB) (atom0495Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
