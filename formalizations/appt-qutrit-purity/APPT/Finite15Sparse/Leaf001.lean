-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def atom0073 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0073 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0073 = ((g 0) * (g 0) * (g 11)) := by
  norm_num [atom0073, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0073_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4008960 : Int) atom0073) := by
  rw [SparsePolynomial.eval_scale, eval_atom0073]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 0) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0073Coded : CoefficientMerge.Poly := [(nat_lit 11, Int.ofNat (nat_lit 1))]
theorem atom0073Coded_decode : atom0073 = SparsePolynomial.decodeCubic 15 atom0073Coded := by decide +kernel
theorem atom0073Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (4008960 : Int) atom0073Coded) := by
  have h := atom0073_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0073Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0074 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 0, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0074 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0074 = ((g 0) * (g 0) * (g 12)) := by
  norm_num [atom0074, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0074_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2108160 : Int) atom0074) := by
  rw [SparsePolynomial.eval_scale, eval_atom0074]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 0) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0074Coded : CoefficientMerge.Poly := [(nat_lit 12, Int.ofNat (nat_lit 1))]
theorem atom0074Coded_decode : atom0074 = SparsePolynomial.decodeCubic 15 atom0074Coded := by decide +kernel
theorem atom0074Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (2108160 : Int) atom0074Coded) := by
  have h := atom0074_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0074Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0075 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 1], Int.ofNat (nat_lit 1))]
theorem eval_atom0075 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0075 = ((g 0) * (g 1) * (g 1)) := by
  norm_num [atom0075, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0075_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2816640 : Int) atom0075) := by
  rw [SparsePolynomial.eval_scale, eval_atom0075]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have ht : 0 ≤ ((g 0) * (g 1) * (g 1)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0075Coded : CoefficientMerge.Poly := [(nat_lit 16, Int.ofNat (nat_lit 1))]
theorem atom0075Coded_decode : atom0075 = SparsePolynomial.decodeCubic 15 atom0075Coded := by decide +kernel
theorem atom0075Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (2816640 : Int) atom0075Coded) := by
  have h := atom0075_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0075Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0076 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 2], Int.ofNat (nat_lit 1))]
theorem eval_atom0076 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0076 = ((g 0) * (g 1) * (g 2)) := by
  norm_num [atom0076, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0076_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21556800 : Int) atom0076) := by
  rw [SparsePolynomial.eval_scale, eval_atom0076]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0076Coded : CoefficientMerge.Poly := [(nat_lit 17, Int.ofNat (nat_lit 1))]
theorem atom0076Coded_decode : atom0076 = SparsePolynomial.decodeCubic 15 atom0076Coded := by decide +kernel
theorem atom0076Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (21556800 : Int) atom0076Coded) := by
  have h := atom0076_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0076Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0077 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0077 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0077 = ((g 0) * (g 1) * (g 3)) := by
  norm_num [atom0077, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0077_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21798720 : Int) atom0077) := by
  rw [SparsePolynomial.eval_scale, eval_atom0077]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0077Coded : CoefficientMerge.Poly := [(nat_lit 18, Int.ofNat (nat_lit 1))]
theorem atom0077Coded_decode : atom0077 = SparsePolynomial.decodeCubic 15 atom0077Coded := by decide +kernel
theorem atom0077Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (21798720 : Int) atom0077Coded) := by
  have h := atom0077_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0077Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0078 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0078 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0078 = ((g 0) * (g 1) * (g 4)) := by
  norm_num [atom0078, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0078_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22040640 : Int) atom0078) := by
  rw [SparsePolynomial.eval_scale, eval_atom0078]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0078Coded : CoefficientMerge.Poly := [(nat_lit 19, Int.ofNat (nat_lit 1))]
theorem atom0078Coded_decode : atom0078 = SparsePolynomial.decodeCubic 15 atom0078Coded := by decide +kernel
theorem atom0078Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (22040640 : Int) atom0078Coded) := by
  have h := atom0078_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0078Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0079 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0079 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0079 = ((g 0) * (g 1) * (g 5)) := by
  norm_num [atom0079, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0079_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22282560 : Int) atom0079) := by
  rw [SparsePolynomial.eval_scale, eval_atom0079]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0079Coded : CoefficientMerge.Poly := [(nat_lit 20, Int.ofNat (nat_lit 1))]
theorem atom0079Coded_decode : atom0079 = SparsePolynomial.decodeCubic 15 atom0079Coded := by decide +kernel
theorem atom0079Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (22282560 : Int) atom0079Coded) := by
  have h := atom0079_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0079Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0080 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0080 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0080 = ((g 0) * (g 1) * (g 6)) := by
  norm_num [atom0080, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0080_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22524480 : Int) atom0080) := by
  rw [SparsePolynomial.eval_scale, eval_atom0080]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0080Coded : CoefficientMerge.Poly := [(nat_lit 21, Int.ofNat (nat_lit 1))]
theorem atom0080Coded_decode : atom0080 = SparsePolynomial.decodeCubic 15 atom0080Coded := by decide +kernel
theorem atom0080Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (22524480 : Int) atom0080Coded) := by
  have h := atom0080_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0080Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0081 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0081 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0081 = ((g 0) * (g 1) * (g 7)) := by
  norm_num [atom0081, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0081_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22766400 : Int) atom0081) := by
  rw [SparsePolynomial.eval_scale, eval_atom0081]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 1) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0081Coded : CoefficientMerge.Poly := [(nat_lit 22, Int.ofNat (nat_lit 1))]
theorem atom0081Coded_decode : atom0081 = SparsePolynomial.decodeCubic 15 atom0081Coded := by decide +kernel
theorem atom0081Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (22766400 : Int) atom0081Coded) := by
  have h := atom0081_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0081Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0082 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0082 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0082 = ((g 0) * (g 1) * (g 8)) := by
  norm_num [atom0082, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0082_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23878080 : Int) atom0082) := by
  rw [SparsePolynomial.eval_scale, eval_atom0082]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 1) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0082Coded : CoefficientMerge.Poly := [(nat_lit 23, Int.ofNat (nat_lit 1))]
theorem atom0082Coded_decode : atom0082 = SparsePolynomial.decodeCubic 15 atom0082Coded := by decide +kernel
theorem atom0082Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (23878080 : Int) atom0082Coded) := by
  have h := atom0082_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0082Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0083 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0083 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0083 = ((g 0) * (g 1) * (g 9)) := by
  norm_num [atom0083, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0083_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47524320 : Int) atom0083) := by
  rw [SparsePolynomial.eval_scale, eval_atom0083]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 1) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0083Coded : CoefficientMerge.Poly := [(nat_lit 24, Int.ofNat (nat_lit 1))]
theorem atom0083Coded_decode : atom0083 = SparsePolynomial.decodeCubic 15 atom0083Coded := by decide +kernel
theorem atom0083Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (47524320 : Int) atom0083Coded) := by
  have h := atom0083_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0083Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0084 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0084 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0084 = ((g 0) * (g 1) * (g 10)) := by
  norm_num [atom0084, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0084_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19913040 : Int) atom0084) := by
  rw [SparsePolynomial.eval_scale, eval_atom0084]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 1) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0084Coded : CoefficientMerge.Poly := [(nat_lit 25, Int.ofNat (nat_lit 1))]
theorem atom0084Coded_decode : atom0084 = SparsePolynomial.decodeCubic 15 atom0084Coded := by decide +kernel
theorem atom0084Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (19913040 : Int) atom0084Coded) := by
  have h := atom0084_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0084Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0085 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0085 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0085 = ((g 0) * (g 1) * (g 11)) := by
  norm_num [atom0085, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0085_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8791200 : Int) atom0085) := by
  rw [SparsePolynomial.eval_scale, eval_atom0085]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 1) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0085Coded : CoefficientMerge.Poly := [(nat_lit 26, Int.ofNat (nat_lit 1))]
theorem atom0085Coded_decode : atom0085 = SparsePolynomial.decodeCubic 15 atom0085Coded := by decide +kernel
theorem atom0085Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (8791200 : Int) atom0085Coded) := by
  have h := atom0085_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0085Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0086 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0086 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0086 = ((g 0) * (g 1) * (g 12)) := by
  norm_num [atom0086, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0086_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4471920 : Int) atom0086) := by
  rw [SparsePolynomial.eval_scale, eval_atom0086]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 1) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0086Coded : CoefficientMerge.Poly := [(nat_lit 27, Int.ofNat (nat_lit 1))]
theorem atom0086Coded_decode : atom0086 = SparsePolynomial.decodeCubic 15 atom0086Coded := by decide +kernel
theorem atom0086Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (4471920 : Int) atom0086Coded) := by
  have h := atom0086_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0086Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0087 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 1, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0087 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0087 = ((g 0) * (g 1) * (g 13)) := by
  norm_num [atom0087, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0087_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2792880 : Int) atom0087) := by
  rw [SparsePolynomial.eval_scale, eval_atom0087]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 1) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0087Coded : CoefficientMerge.Poly := [(nat_lit 28, Int.ofNat (nat_lit 1))]
theorem atom0087Coded_decode : atom0087 = SparsePolynomial.decodeCubic 15 atom0087Coded := by decide +kernel
theorem atom0087Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (2792880 : Int) atom0087Coded) := by
  have h := atom0087_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0087Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0088 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 2], Int.ofNat (nat_lit 1))]
theorem eval_atom0088 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0088 = ((g 0) * (g 2) * (g 2)) := by
  norm_num [atom0088, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0088_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24606720 : Int) atom0088) := by
  rw [SparsePolynomial.eval_scale, eval_atom0088]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 0) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0088Coded : CoefficientMerge.Poly := [(nat_lit 32, Int.ofNat (nat_lit 1))]
theorem atom0088Coded_decode : atom0088 = SparsePolynomial.decodeCubic 15 atom0088Coded := by decide +kernel
theorem atom0088Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (24606720 : Int) atom0088Coded) := by
  have h := atom0088_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0088Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0089 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0089 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0089 = ((g 0) * (g 2) * (g 3)) := by
  norm_num [atom0089, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0089_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51598080 : Int) atom0089) := by
  rw [SparsePolynomial.eval_scale, eval_atom0089]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0089Coded : CoefficientMerge.Poly := [(nat_lit 33, Int.ofNat (nat_lit 1))]
theorem atom0089Coded_decode : atom0089 = SparsePolynomial.decodeCubic 15 atom0089Coded := by decide +kernel
theorem atom0089Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (51598080 : Int) atom0089Coded) := by
  have h := atom0089_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0089Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0090 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0090 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0090 = ((g 0) * (g 2) * (g 4)) := by
  norm_num [atom0090, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0090_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53982720 : Int) atom0090) := by
  rw [SparsePolynomial.eval_scale, eval_atom0090]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0090Coded : CoefficientMerge.Poly := [(nat_lit 34, Int.ofNat (nat_lit 1))]
theorem atom0090Coded_decode : atom0090 = SparsePolynomial.decodeCubic 15 atom0090Coded := by decide +kernel
theorem atom0090Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (53982720 : Int) atom0090Coded) := by
  have h := atom0090_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0090Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0091 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0091 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0091 = ((g 0) * (g 2) * (g 5)) := by
  norm_num [atom0091, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0091_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56367360 : Int) atom0091) := by
  rw [SparsePolynomial.eval_scale, eval_atom0091]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0091Coded : CoefficientMerge.Poly := [(nat_lit 35, Int.ofNat (nat_lit 1))]
theorem atom0091Coded_decode : atom0091 = SparsePolynomial.decodeCubic 15 atom0091Coded := by decide +kernel
theorem atom0091Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (56367360 : Int) atom0091Coded) := by
  have h := atom0091_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0091Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0092 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0092 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0092 = ((g 0) * (g 2) * (g 6)) := by
  norm_num [atom0092, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0092_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58752000 : Int) atom0092) := by
  rw [SparsePolynomial.eval_scale, eval_atom0092]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0092Coded : CoefficientMerge.Poly := [(nat_lit 36, Int.ofNat (nat_lit 1))]
theorem atom0092Coded_decode : atom0092 = SparsePolynomial.decodeCubic 15 atom0092Coded := by decide +kernel
theorem atom0092Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (58752000 : Int) atom0092Coded) := by
  have h := atom0092_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0092Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0093 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0093 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0093 = ((g 0) * (g 2) * (g 7)) := by
  norm_num [atom0093, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0093_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61136640 : Int) atom0093) := by
  rw [SparsePolynomial.eval_scale, eval_atom0093]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0093Coded : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 1))]
theorem atom0093Coded_decode : atom0093 = SparsePolynomial.decodeCubic 15 atom0093Coded := by decide +kernel
theorem atom0093Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (61136640 : Int) atom0093Coded) := by
  have h := atom0093_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0093Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0094 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0094 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0094 = ((g 0) * (g 2) * (g 8)) := by
  norm_num [atom0094, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0094_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63521280 : Int) atom0094) := by
  rw [SparsePolynomial.eval_scale, eval_atom0094]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0094Coded : CoefficientMerge.Poly := [(nat_lit 38, Int.ofNat (nat_lit 1))]
theorem atom0094Coded_decode : atom0094 = SparsePolynomial.decodeCubic 15 atom0094Coded := by decide +kernel
theorem atom0094Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (63521280 : Int) atom0094Coded) := by
  have h := atom0094_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0094Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0095 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0095 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0095 = ((g 0) * (g 2) * (g 9)) := by
  norm_num [atom0095, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0095_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (80002080 : Int) atom0095) := by
  rw [SparsePolynomial.eval_scale, eval_atom0095]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0095Coded : CoefficientMerge.Poly := [(nat_lit 39, Int.ofNat (nat_lit 1))]
theorem atom0095Coded_decode : atom0095 = SparsePolynomial.decodeCubic 15 atom0095Coded := by decide +kernel
theorem atom0095Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (80002080 : Int) atom0095Coded) := by
  have h := atom0095_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0095Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0096 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0096 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0096 = ((g 0) * (g 2) * (g 10)) := by
  norm_num [atom0096, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0096_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48319200 : Int) atom0096) := by
  rw [SparsePolynomial.eval_scale, eval_atom0096]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0096Coded : CoefficientMerge.Poly := [(nat_lit 40, Int.ofNat (nat_lit 1))]
theorem atom0096Coded_decode : atom0096 = SparsePolynomial.decodeCubic 15 atom0096Coded := by decide +kernel
theorem atom0096Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (48319200 : Int) atom0096Coded) := by
  have h := atom0096_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0096Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0097 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0097 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0097 = ((g 0) * (g 2) * (g 11)) := by
  norm_num [atom0097, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0097_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33558840 : Int) atom0097) := by
  rw [SparsePolynomial.eval_scale, eval_atom0097]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0097Coded : CoefficientMerge.Poly := [(nat_lit 41, Int.ofNat (nat_lit 1))]
theorem atom0097Coded_decode : atom0097 = SparsePolynomial.decodeCubic 15 atom0097Coded := by decide +kernel
theorem atom0097Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (33558840 : Int) atom0097Coded) := by
  have h := atom0097_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0097Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0098 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0098 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0098 = ((g 0) * (g 2) * (g 12)) := by
  norm_num [atom0098, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0098_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9119520 : Int) atom0098) := by
  rw [SparsePolynomial.eval_scale, eval_atom0098]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0098Coded : CoefficientMerge.Poly := [(nat_lit 42, Int.ofNat (nat_lit 1))]
theorem atom0098Coded_decode : atom0098 = SparsePolynomial.decodeCubic 15 atom0098Coded := by decide +kernel
theorem atom0098Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (9119520 : Int) atom0098Coded) := by
  have h := atom0098_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0098Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0099 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 2, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0099 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0099 = ((g 0) * (g 2) * (g 13)) := by
  norm_num [atom0099, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0099_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10851840 : Int) atom0099) := by
  rw [SparsePolynomial.eval_scale, eval_atom0099]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0099Coded : CoefficientMerge.Poly := [(nat_lit 43, Int.ofNat (nat_lit 1))]
theorem atom0099Coded_decode : atom0099 = SparsePolynomial.decodeCubic 15 atom0099Coded := by decide +kernel
theorem atom0099Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (10851840 : Int) atom0099Coded) := by
  have h := atom0099_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0099Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0100 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0100 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0100 = ((g 0) * (g 3) * (g 3)) := by
  norm_num [atom0100, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0100_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25790400 : Int) atom0100) := by
  rw [SparsePolynomial.eval_scale, eval_atom0100]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 0) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0100Coded : CoefficientMerge.Poly := [(nat_lit 48, Int.ofNat (nat_lit 1))]
theorem atom0100Coded_decode : atom0100 = SparsePolynomial.decodeCubic 15 atom0100Coded := by decide +kernel
theorem atom0100Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (25790400 : Int) atom0100Coded) := by
  have h := atom0100_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0100Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0101 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0101 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0101 = ((g 0) * (g 3) * (g 4)) := by
  norm_num [atom0101, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0101_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53758080 : Int) atom0101) := by
  rw [SparsePolynomial.eval_scale, eval_atom0101]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0101Coded : CoefficientMerge.Poly := [(nat_lit 49, Int.ofNat (nat_lit 1))]
theorem atom0101Coded_decode : atom0101 = SparsePolynomial.decodeCubic 15 atom0101Coded := by decide +kernel
theorem atom0101Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (53758080 : Int) atom0101Coded) := by
  have h := atom0101_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0101Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0102 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0102 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0102 = ((g 0) * (g 3) * (g 5)) := by
  norm_num [atom0102, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0102_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57335040 : Int) atom0102) := by
  rw [SparsePolynomial.eval_scale, eval_atom0102]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0102Coded : CoefficientMerge.Poly := [(nat_lit 50, Int.ofNat (nat_lit 1))]
theorem atom0102Coded_decode : atom0102 = SparsePolynomial.decodeCubic 15 atom0102Coded := by decide +kernel
theorem atom0102Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (57335040 : Int) atom0102Coded) := by
  have h := atom0102_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0102Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0103 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0103 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0103 = ((g 0) * (g 3) * (g 6)) := by
  norm_num [atom0103, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0103_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60912000 : Int) atom0103) := by
  rw [SparsePolynomial.eval_scale, eval_atom0103]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0103Coded : CoefficientMerge.Poly := [(nat_lit 51, Int.ofNat (nat_lit 1))]
theorem atom0103Coded_decode : atom0103 = SparsePolynomial.decodeCubic 15 atom0103Coded := by decide +kernel
theorem atom0103Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (60912000 : Int) atom0103Coded) := by
  have h := atom0103_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0103Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0104 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0104 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0104 = ((g 0) * (g 3) * (g 7)) := by
  norm_num [atom0104, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0104_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64601280 : Int) atom0104) := by
  rw [SparsePolynomial.eval_scale, eval_atom0104]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0104Coded : CoefficientMerge.Poly := [(nat_lit 52, Int.ofNat (nat_lit 1))]
theorem atom0104Coded_decode : atom0104 = SparsePolynomial.decodeCubic 15 atom0104Coded := by decide +kernel
theorem atom0104Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (64601280 : Int) atom0104Coded) := by
  have h := atom0104_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0104Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0105 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0105 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0105 = ((g 0) * (g 3) * (g 8)) := by
  norm_num [atom0105, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0105_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68290560 : Int) atom0105) := by
  rw [SparsePolynomial.eval_scale, eval_atom0105]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0105Coded : CoefficientMerge.Poly := [(nat_lit 53, Int.ofNat (nat_lit 1))]
theorem atom0105Coded_decode : atom0105 = SparsePolynomial.decodeCubic 15 atom0105Coded := by decide +kernel
theorem atom0105Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (68290560 : Int) atom0105Coded) := by
  have h := atom0105_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0105Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0106 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0106 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0106 = ((g 0) * (g 3) * (g 9)) := by
  norm_num [atom0106, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0106_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (85263840 : Int) atom0106) := by
  rw [SparsePolynomial.eval_scale, eval_atom0106]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0106Coded : CoefficientMerge.Poly := [(nat_lit 54, Int.ofNat (nat_lit 1))]
theorem atom0106Coded_decode : atom0106 = SparsePolynomial.decodeCubic 15 atom0106Coded := by decide +kernel
theorem atom0106Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (85263840 : Int) atom0106Coded) := by
  have h := atom0106_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0106Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0107 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0107 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0107 = ((g 0) * (g 3) * (g 10)) := by
  norm_num [atom0107, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0107_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54403380 : Int) atom0107) := by
  rw [SparsePolynomial.eval_scale, eval_atom0107]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0107Coded : CoefficientMerge.Poly := [(nat_lit 55, Int.ofNat (nat_lit 1))]
theorem atom0107Coded_decode : atom0107 = SparsePolynomial.decodeCubic 15 atom0107Coded := by decide +kernel
theorem atom0107Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (54403380 : Int) atom0107Coded) := by
  have h := atom0107_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0107Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0108 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0108 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0108 = ((g 0) * (g 3) * (g 11)) := by
  norm_num [atom0108, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0108_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38354040 : Int) atom0108) := by
  rw [SparsePolynomial.eval_scale, eval_atom0108]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0108Coded : CoefficientMerge.Poly := [(nat_lit 56, Int.ofNat (nat_lit 1))]
theorem atom0108Coded_decode : atom0108 = SparsePolynomial.decodeCubic 15 atom0108Coded := by decide +kernel
theorem atom0108Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (38354040 : Int) atom0108Coded) := by
  have h := atom0108_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0108Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0109 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0109 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0109 = ((g 0) * (g 3) * (g 12)) := by
  norm_num [atom0109, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0109_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15224220 : Int) atom0109) := by
  rw [SparsePolynomial.eval_scale, eval_atom0109]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0109Coded : CoefficientMerge.Poly := [(nat_lit 57, Int.ofNat (nat_lit 1))]
theorem atom0109Coded_decode : atom0109 = SparsePolynomial.decodeCubic 15 atom0109Coded := by decide +kernel
theorem atom0109Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (15224220 : Int) atom0109Coded) := by
  have h := atom0109_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0109Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0110 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0110 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0110 = ((g 0) * (g 3) * (g 13)) := by
  norm_num [atom0110, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0110_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18271980 : Int) atom0110) := by
  rw [SparsePolynomial.eval_scale, eval_atom0110]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0110Coded : CoefficientMerge.Poly := [(nat_lit 58, Int.ofNat (nat_lit 1))]
theorem atom0110Coded_decode : atom0110 = SparsePolynomial.decodeCubic 15 atom0110Coded := by decide +kernel
theorem atom0110Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (18271980 : Int) atom0110Coded) := by
  have h := atom0110_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0110Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0111 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 3, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0111 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0111 = ((g 0) * (g 3) * (g 14)) := by
  norm_num [atom0111, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0111_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1041660 : Int) atom0111) := by
  rw [SparsePolynomial.eval_scale, eval_atom0111]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0111Coded : CoefficientMerge.Poly := [(nat_lit 59, Int.ofNat (nat_lit 1))]
theorem atom0111Coded_decode : atom0111 = SparsePolynomial.decodeCubic 15 atom0111Coded := by decide +kernel
theorem atom0111Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (1041660 : Int) atom0111Coded) := by
  have h := atom0111_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0111Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0112 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0112 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0112 = ((g 0) * (g 4) * (g 4)) := by
  norm_num [atom0112, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0112_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33416640 : Int) atom0112) := by
  rw [SparsePolynomial.eval_scale, eval_atom0112]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 0) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0112Coded : CoefficientMerge.Poly := [(nat_lit 64, Int.ofNat (nat_lit 1))]
theorem atom0112Coded_decode : atom0112 = SparsePolynomial.decodeCubic 15 atom0112Coded := by decide +kernel
theorem atom0112Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (33416640 : Int) atom0112Coded) := by
  have h := atom0112_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0112Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0113 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0113 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0113 = ((g 0) * (g 4) * (g 5)) := by
  norm_num [atom0113, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0113_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62148960 : Int) atom0113) := by
  rw [SparsePolynomial.eval_scale, eval_atom0113]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0113Coded : CoefficientMerge.Poly := [(nat_lit 65, Int.ofNat (nat_lit 1))]
theorem atom0113Coded_decode : atom0113 = SparsePolynomial.decodeCubic 15 atom0113Coded := by decide +kernel
theorem atom0113Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (62148960 : Int) atom0113Coded) := by
  have h := atom0113_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0113Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0114 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0114 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0114 = ((g 0) * (g 4) * (g 6)) := by
  norm_num [atom0114, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0114_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (66313440 : Int) atom0114) := by
  rw [SparsePolynomial.eval_scale, eval_atom0114]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0114Coded : CoefficientMerge.Poly := [(nat_lit 66, Int.ofNat (nat_lit 1))]
theorem atom0114Coded_decode : atom0114 = SparsePolynomial.decodeCubic 15 atom0114Coded := by decide +kernel
theorem atom0114Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (66313440 : Int) atom0114Coded) := by
  have h := atom0114_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0114Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0115 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0115 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0115 = ((g 0) * (g 4) * (g 7)) := by
  norm_num [atom0115, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0115_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (70477920 : Int) atom0115) := by
  rw [SparsePolynomial.eval_scale, eval_atom0115]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0115Coded : CoefficientMerge.Poly := [(nat_lit 67, Int.ofNat (nat_lit 1))]
theorem atom0115Coded_decode : atom0115 = SparsePolynomial.decodeCubic 15 atom0115Coded := by decide +kernel
theorem atom0115Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (70477920 : Int) atom0115Coded) := by
  have h := atom0115_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0115Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0116 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0116 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0116 = ((g 0) * (g 4) * (g 8)) := by
  norm_num [atom0116, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0116_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74642400 : Int) atom0116) := by
  rw [SparsePolynomial.eval_scale, eval_atom0116]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0116Coded : CoefficientMerge.Poly := [(nat_lit 68, Int.ofNat (nat_lit 1))]
theorem atom0116Coded_decode : atom0116 = SparsePolynomial.decodeCubic 15 atom0116Coded := by decide +kernel
theorem atom0116Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (74642400 : Int) atom0116Coded) := by
  have h := atom0116_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0116Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0117 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0117 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0117 = ((g 0) * (g 4) * (g 9)) := by
  norm_num [atom0117, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0117_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90525600 : Int) atom0117) := by
  rw [SparsePolynomial.eval_scale, eval_atom0117]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0117Coded : CoefficientMerge.Poly := [(nat_lit 69, Int.ofNat (nat_lit 1))]
theorem atom0117Coded_decode : atom0117 = SparsePolynomial.decodeCubic 15 atom0117Coded := by decide +kernel
theorem atom0117Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (90525600 : Int) atom0117Coded) := by
  have h := atom0117_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0117Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0118 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0118 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0118 = ((g 0) * (g 4) * (g 10)) := by
  norm_num [atom0118, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0118_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61395660 : Int) atom0118) := by
  rw [SparsePolynomial.eval_scale, eval_atom0118]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0118Coded : CoefficientMerge.Poly := [(nat_lit 70, Int.ofNat (nat_lit 1))]
theorem atom0118Coded_decode : atom0118 = SparsePolynomial.decodeCubic 15 atom0118Coded := by decide +kernel
theorem atom0118Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (61395660 : Int) atom0118Coded) := by
  have h := atom0118_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0118Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0119 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0119 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0119 = ((g 0) * (g 4) * (g 11)) := by
  norm_num [atom0119, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0119_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43149240 : Int) atom0119) := by
  rw [SparsePolynomial.eval_scale, eval_atom0119]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0119Coded : CoefficientMerge.Poly := [(nat_lit 71, Int.ofNat (nat_lit 1))]
theorem atom0119Coded_decode : atom0119 = SparsePolynomial.decodeCubic 15 atom0119Coded := by decide +kernel
theorem atom0119Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (43149240 : Int) atom0119Coded) := by
  have h := atom0119_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0119Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0120 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0120 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0120 = ((g 0) * (g 4) * (g 12)) := by
  norm_num [atom0120, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0120_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22546980 : Int) atom0120) := by
  rw [SparsePolynomial.eval_scale, eval_atom0120]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0120Coded : CoefficientMerge.Poly := [(nat_lit 72, Int.ofNat (nat_lit 1))]
theorem atom0120Coded_decode : atom0120 = SparsePolynomial.decodeCubic 15 atom0120Coded := by decide +kernel
theorem atom0120Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (22546980 : Int) atom0120Coded) := by
  have h := atom0120_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0120Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0121 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0121 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0121 = ((g 0) * (g 4) * (g 13)) := by
  norm_num [atom0121, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0121_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25656660 : Int) atom0121) := by
  rw [SparsePolynomial.eval_scale, eval_atom0121]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0121Coded : CoefficientMerge.Poly := [(nat_lit 73, Int.ofNat (nat_lit 1))]
theorem atom0121Coded_decode : atom0121 = SparsePolynomial.decodeCubic 15 atom0121Coded := by decide +kernel
theorem atom0121Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (25656660 : Int) atom0121Coded) := by
  have h := atom0121_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0121Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0122 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 4, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0122 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0122 = ((g 0) * (g 4) * (g 14)) := by
  norm_num [atom0122, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0122_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8488260 : Int) atom0122) := by
  rw [SparsePolynomial.eval_scale, eval_atom0122]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0122Coded : CoefficientMerge.Poly := [(nat_lit 74, Int.ofNat (nat_lit 1))]
theorem atom0122Coded_decode : atom0122 = SparsePolynomial.decodeCubic 15 atom0122Coded := by decide +kernel
theorem atom0122Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (8488260 : Int) atom0122Coded) := by
  have h := atom0122_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0122Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0123 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0123 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0123 = ((g 0) * (g 5) * (g 5)) := by
  norm_num [atom0123, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0123_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39827520 : Int) atom0123) := by
  rw [SparsePolynomial.eval_scale, eval_atom0123]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 0) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0123Coded : CoefficientMerge.Poly := [(nat_lit 80, Int.ofNat (nat_lit 1))]
theorem atom0123Coded_decode : atom0123 = SparsePolynomial.decodeCubic 15 atom0123Coded := by decide +kernel
theorem atom0123Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (39827520 : Int) atom0123Coded) := by
  have h := atom0123_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0123Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0124 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0124 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0124 = ((g 0) * (g 5) * (g 6)) := by
  norm_num [atom0124, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0124_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74807712 : Int) atom0124) := by
  rw [SparsePolynomial.eval_scale, eval_atom0124]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0124Coded : CoefficientMerge.Poly := [(nat_lit 81, Int.ofNat (nat_lit 1))]
theorem atom0124Coded_decode : atom0124 = SparsePolynomial.decodeCubic 15 atom0124Coded := by decide +kernel
theorem atom0124Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (74807712 : Int) atom0124Coded) := by
  have h := atom0124_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0124Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0125 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0125 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0125 = ((g 0) * (g 5) * (g 7)) := by
  norm_num [atom0125, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0125_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (77670720 : Int) atom0125) := by
  rw [SparsePolynomial.eval_scale, eval_atom0125]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0125Coded : CoefficientMerge.Poly := [(nat_lit 82, Int.ofNat (nat_lit 1))]
theorem atom0125Coded_decode : atom0125 = SparsePolynomial.decodeCubic 15 atom0125Coded := by decide +kernel
theorem atom0125Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (77670720 : Int) atom0125Coded) := by
  have h := atom0125_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0125Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0126 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0126 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0126 = ((g 0) * (g 5) * (g 8)) := by
  norm_num [atom0126, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0126_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82012320 : Int) atom0126) := by
  rw [SparsePolynomial.eval_scale, eval_atom0126]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0126Coded : CoefficientMerge.Poly := [(nat_lit 83, Int.ofNat (nat_lit 1))]
theorem atom0126Coded_decode : atom0126 = SparsePolynomial.decodeCubic 15 atom0126Coded := by decide +kernel
theorem atom0126Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (82012320 : Int) atom0126Coded) := by
  have h := atom0126_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0126Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0127 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0127 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0127 = ((g 0) * (g 5) * (g 9)) := by
  norm_num [atom0127, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0127_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95787360 : Int) atom0127) := by
  rw [SparsePolynomial.eval_scale, eval_atom0127]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0127Coded : CoefficientMerge.Poly := [(nat_lit 84, Int.ofNat (nat_lit 1))]
theorem atom0127Coded_decode : atom0127 = SparsePolynomial.decodeCubic 15 atom0127Coded := by decide +kernel
theorem atom0127Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (95787360 : Int) atom0127Coded) := by
  have h := atom0127_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0127Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0128 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0128 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0128 = ((g 0) * (g 5) * (g 10)) := by
  norm_num [atom0128, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0128_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68358420 : Int) atom0128) := by
  rw [SparsePolynomial.eval_scale, eval_atom0128]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0128Coded : CoefficientMerge.Poly := [(nat_lit 85, Int.ofNat (nat_lit 1))]
theorem atom0128Coded_decode : atom0128 = SparsePolynomial.decodeCubic 15 atom0128Coded := by decide +kernel
theorem atom0128Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (68358420 : Int) atom0128Coded) := by
  have h := atom0128_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0128Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0129 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0129 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0129 = ((g 0) * (g 5) * (g 11)) := by
  norm_num [atom0129, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0129_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47944440 : Int) atom0129) := by
  rw [SparsePolynomial.eval_scale, eval_atom0129]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0129Coded : CoefficientMerge.Poly := [(nat_lit 86, Int.ofNat (nat_lit 1))]
theorem atom0129Coded_decode : atom0129 = SparsePolynomial.decodeCubic 15 atom0129Coded := by decide +kernel
theorem atom0129Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (47944440 : Int) atom0129Coded) := by
  have h := atom0129_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0129Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0130 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0130 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0130 = ((g 0) * (g 5) * (g 12)) := by
  norm_num [atom0130, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0130_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28341180 : Int) atom0130) := by
  rw [SparsePolynomial.eval_scale, eval_atom0130]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0130Coded : CoefficientMerge.Poly := [(nat_lit 87, Int.ofNat (nat_lit 1))]
theorem atom0130Coded_decode : atom0130 = SparsePolynomial.decodeCubic 15 atom0130Coded := by decide +kernel
theorem atom0130Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (28341180 : Int) atom0130Coded) := by
  have h := atom0130_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0130Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0131 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0131 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0131 = ((g 0) * (g 5) * (g 13)) := by
  norm_num [atom0131, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0131_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30612780 : Int) atom0131) := by
  rw [SparsePolynomial.eval_scale, eval_atom0131]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0131Coded : CoefficientMerge.Poly := [(nat_lit 88, Int.ofNat (nat_lit 1))]
theorem atom0131Coded_decode : atom0131 = SparsePolynomial.decodeCubic 15 atom0131Coded := by decide +kernel
theorem atom0131Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (30612780 : Int) atom0131Coded) := by
  have h := atom0131_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0131Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0132 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 5, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0132 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0132 = ((g 0) * (g 5) * (g 14)) := by
  norm_num [atom0132, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0132_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12606300 : Int) atom0132) := by
  rw [SparsePolynomial.eval_scale, eval_atom0132]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0132Coded : CoefficientMerge.Poly := [(nat_lit 89, Int.ofNat (nat_lit 1))]
theorem atom0132Coded_decode : atom0132 = SparsePolynomial.decodeCubic 15 atom0132Coded := by decide +kernel
theorem atom0132Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (12606300 : Int) atom0132Coded) := by
  have h := atom0132_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0132Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0133 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0133 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0133 = ((g 0) * (g 6) * (g 6)) := by
  norm_num [atom0133, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0133_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47183040 : Int) atom0133) := by
  rw [SparsePolynomial.eval_scale, eval_atom0133]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 0) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0133Coded : CoefficientMerge.Poly := [(nat_lit 96, Int.ofNat (nat_lit 1))]
theorem atom0133Coded_decode : atom0133 = SparsePolynomial.decodeCubic 15 atom0133Coded := by decide +kernel
theorem atom0133Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (47183040 : Int) atom0133Coded) := by
  have h := atom0133_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0133Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0134 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0134 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0134 = ((g 0) * (g 6) * (g 7)) := by
  norm_num [atom0134, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0134_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89196672 : Int) atom0134) := by
  rw [SparsePolynomial.eval_scale, eval_atom0134]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0134Coded : CoefficientMerge.Poly := [(nat_lit 97, Int.ofNat (nat_lit 1))]
theorem atom0134Coded_decode : atom0134 = SparsePolynomial.decodeCubic 15 atom0134Coded := by decide +kernel
theorem atom0134Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (89196672 : Int) atom0134Coded) := by
  have h := atom0134_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0134Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0135 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0135 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0135 = ((g 0) * (g 6) * (g 8)) := by
  norm_num [atom0135, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0135_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89320320 : Int) atom0135) := by
  rw [SparsePolynomial.eval_scale, eval_atom0135]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0135Coded : CoefficientMerge.Poly := [(nat_lit 98, Int.ofNat (nat_lit 1))]
theorem atom0135Coded_decode : atom0135 = SparsePolynomial.decodeCubic 15 atom0135Coded := by decide +kernel
theorem atom0135Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (89320320 : Int) atom0135Coded) := by
  have h := atom0135_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0135Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0136 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0136 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0136 = ((g 0) * (g 6) * (g 9)) := by
  norm_num [atom0136, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0136_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101049120 : Int) atom0136) := by
  rw [SparsePolynomial.eval_scale, eval_atom0136]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0136Coded : CoefficientMerge.Poly := [(nat_lit 99, Int.ofNat (nat_lit 1))]
theorem atom0136Coded_decode : atom0136 = SparsePolynomial.decodeCubic 15 atom0136Coded := by decide +kernel
theorem atom0136Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (101049120 : Int) atom0136Coded) := by
  have h := atom0136_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0136Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0137 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0137 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0137 = ((g 0) * (g 6) * (g 10)) := by
  norm_num [atom0137, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0137_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74616660 : Int) atom0137) := by
  rw [SparsePolynomial.eval_scale, eval_atom0137]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0137Coded : CoefficientMerge.Poly := [(nat_lit 100, Int.ofNat (nat_lit 1))]
theorem atom0137Coded_decode : atom0137 = SparsePolynomial.decodeCubic 15 atom0137Coded := by decide +kernel
theorem atom0137Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (74616660 : Int) atom0137Coded) := by
  have h := atom0137_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0137Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0138 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0138 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0138 = ((g 0) * (g 6) * (g 11)) := by
  norm_num [atom0138, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0138_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52739640 : Int) atom0138) := by
  rw [SparsePolynomial.eval_scale, eval_atom0138]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0138Coded : CoefficientMerge.Poly := [(nat_lit 101, Int.ofNat (nat_lit 1))]
theorem atom0138Coded_decode : atom0138 = SparsePolynomial.decodeCubic 15 atom0138Coded := by decide +kernel
theorem atom0138Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (52739640 : Int) atom0138Coded) := by
  have h := atom0138_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0138Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0139 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0139 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0139 = ((g 0) * (g 6) * (g 12)) := by
  norm_num [atom0139, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0139_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32741820 : Int) atom0139) := by
  rw [SparsePolynomial.eval_scale, eval_atom0139]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0139Coded : CoefficientMerge.Poly := [(nat_lit 102, Int.ofNat (nat_lit 1))]
theorem atom0139Coded_decode : atom0139 = SparsePolynomial.decodeCubic 15 atom0139Coded := by decide +kernel
theorem atom0139Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (32741820 : Int) atom0139Coded) := by
  have h := atom0139_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0139Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0140 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0140 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0140 = ((g 0) * (g 6) * (g 13)) := by
  norm_num [atom0140, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0140_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33815340 : Int) atom0140) := by
  rw [SparsePolynomial.eval_scale, eval_atom0140]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0140Coded : CoefficientMerge.Poly := [(nat_lit 103, Int.ofNat (nat_lit 1))]
theorem atom0140Coded_decode : atom0140 = SparsePolynomial.decodeCubic 15 atom0140Coded := by decide +kernel
theorem atom0140Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (33815340 : Int) atom0140Coded) := by
  have h := atom0140_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0140Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0141 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0141 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0141 = ((g 0) * (g 6) * (g 14)) := by
  norm_num [atom0141, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0141_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14610780 : Int) atom0141) := by
  rw [SparsePolynomial.eval_scale, eval_atom0141]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0141Coded : CoefficientMerge.Poly := [(nat_lit 104, Int.ofNat (nat_lit 1))]
theorem atom0141Coded_decode : atom0141 = SparsePolynomial.decodeCubic 15 atom0141Coded := by decide +kernel
theorem atom0141Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (14610780 : Int) atom0141Coded) := by
  have h := atom0141_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0141Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0142 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0142 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0142 = ((g 0) * (g 7) * (g 7)) := by
  norm_num [atom0142, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0142_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54378240 : Int) atom0142) := by
  rw [SparsePolynomial.eval_scale, eval_atom0142]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 0) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0142Coded : CoefficientMerge.Poly := [(nat_lit 112, Int.ofNat (nat_lit 1))]
theorem atom0142Coded_decode : atom0142 = SparsePolynomial.decodeCubic 15 atom0142Coded := by decide +kernel
theorem atom0142Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (54378240 : Int) atom0142Coded) := by
  have h := atom0142_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0142Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0143 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0143 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0143 = ((g 0) * (g 7) * (g 8)) := by
  norm_num [atom0143, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0143_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102218720 : Int) atom0143) := by
  rw [SparsePolynomial.eval_scale, eval_atom0143]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0143Coded : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 1))]
theorem atom0143Coded_decode : atom0143 = SparsePolynomial.decodeCubic 15 atom0143Coded := by decide +kernel
theorem atom0143Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (102218720 : Int) atom0143Coded) := by
  have h := atom0143_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0143Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0144 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0144 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0144 = ((g 0) * (g 7) * (g 9)) := by
  norm_num [atom0144, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0144_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (106800960 : Int) atom0144) := by
  rw [SparsePolynomial.eval_scale, eval_atom0144]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0144Coded : CoefficientMerge.Poly := [(nat_lit 114, Int.ofNat (nat_lit 1))]
theorem atom0144Coded_decode : atom0144 = SparsePolynomial.decodeCubic 15 atom0144Coded := by decide +kernel
theorem atom0144Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (106800960 : Int) atom0144Coded) := by
  have h := atom0144_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0144Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0145 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0145 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0145 = ((g 0) * (g 7) * (g 10)) := by
  norm_num [atom0145, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0145_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (80515680 : Int) atom0145) := by
  rw [SparsePolynomial.eval_scale, eval_atom0145]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0145Coded : CoefficientMerge.Poly := [(nat_lit 115, Int.ofNat (nat_lit 1))]
theorem atom0145Coded_decode : atom0145 = SparsePolynomial.decodeCubic 15 atom0145Coded := by decide +kernel
theorem atom0145Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (80515680 : Int) atom0145Coded) := by
  have h := atom0145_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0145Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0146 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0146 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0146 = ((g 0) * (g 7) * (g 11)) := by
  norm_num [atom0146, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0146_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57534840 : Int) atom0146) := by
  rw [SparsePolynomial.eval_scale, eval_atom0146]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0146Coded : CoefficientMerge.Poly := [(nat_lit 116, Int.ofNat (nat_lit 1))]
theorem atom0146Coded_decode : atom0146 = SparsePolynomial.decodeCubic 15 atom0146Coded := by decide +kernel
theorem atom0146Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (57534840 : Int) atom0146Coded) := by
  have h := atom0146_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0146Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0147 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0147 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0147 = ((g 0) * (g 7) * (g 12)) := by
  norm_num [atom0147, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0147_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35679840 : Int) atom0147) := by
  rw [SparsePolynomial.eval_scale, eval_atom0147]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0147Coded : CoefficientMerge.Poly := [(nat_lit 117, Int.ofNat (nat_lit 1))]
theorem atom0147Coded_decode : atom0147 = SparsePolynomial.decodeCubic 15 atom0147Coded := by decide +kernel
theorem atom0147Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (35679840 : Int) atom0147Coded) := by
  have h := atom0147_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0147Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0148 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0148 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0148 = ((g 0) * (g 7) * (g 13)) := by
  norm_num [atom0148, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0148_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34919040 : Int) atom0148) := by
  rw [SparsePolynomial.eval_scale, eval_atom0148]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0148Coded : CoefficientMerge.Poly := [(nat_lit 118, Int.ofNat (nat_lit 1))]
theorem atom0148Coded_decode : atom0148 = SparsePolynomial.decodeCubic 15 atom0148Coded := by decide +kernel
theorem atom0148Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (34919040 : Int) atom0148Coded) := by
  have h := atom0148_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0148Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0149 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0149 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0149 = ((g 0) * (g 7) * (g 14)) := by
  norm_num [atom0149, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0149_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13880160 : Int) atom0149) := by
  rw [SparsePolynomial.eval_scale, eval_atom0149]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0149Coded : CoefficientMerge.Poly := [(nat_lit 119, Int.ofNat (nat_lit 1))]
theorem atom0149Coded_decode : atom0149 = SparsePolynomial.decodeCubic 15 atom0149Coded := by decide +kernel
theorem atom0149Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (13880160 : Int) atom0149Coded) := by
  have h := atom0149_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0149Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0150 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0150 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0150 = ((g 0) * (g 8) * (g 8)) := by
  norm_num [atom0150, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0150_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60480000 : Int) atom0150) := by
  rw [SparsePolynomial.eval_scale, eval_atom0150]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 0) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0150Coded : CoefficientMerge.Poly := [(nat_lit 128, Int.ofNat (nat_lit 1))]
theorem atom0150Coded_decode : atom0150 = SparsePolynomial.decodeCubic 15 atom0150Coded := by decide +kernel
theorem atom0150Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (60480000 : Int) atom0150Coded) := by
  have h := atom0150_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0150Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0151 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0151 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0151 = ((g 0) * (g 8) * (g 9)) := by
  norm_num [atom0151, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0151_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (114342840 : Int) atom0151) := by
  rw [SparsePolynomial.eval_scale, eval_atom0151]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0151Coded : CoefficientMerge.Poly := [(nat_lit 129, Int.ofNat (nat_lit 1))]
theorem atom0151Coded_decode : atom0151 = SparsePolynomial.decodeCubic 15 atom0151Coded := by decide +kernel
theorem atom0151Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (114342840 : Int) atom0151Coded) := by
  have h := atom0151_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0151Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0152 : SparsePolynomial.Poly := [([nat_lit 0, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0152 (g : Fin 15 → ℝ) : SparsePolynomial.eval (gapValues g) atom0152 = ((g 0) * (g 8) * (g 10)) := by
  norm_num [atom0152, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0152_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (86347080 : Int) atom0152) := by
  rw [SparsePolynomial.eval_scale, eval_atom0152]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0152Coded : CoefficientMerge.Poly := [(nat_lit 130, Int.ofNat (nat_lit 1))]
theorem atom0152Coded_decode : atom0152 = SparsePolynomial.decodeCubic 15 atom0152Coded := by decide +kernel
theorem atom0152Coded_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) (CoefficientMerge.scale (86347080 : Int) atom0152Coded) := by
  have h := atom0152_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0152Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block001 : CoefficientMerge.Poly := [(nat_lit 11, Int.ofNat (nat_lit 4008960)), (nat_lit 12, Int.ofNat (nat_lit 2108160)), (nat_lit 16, Int.ofNat (nat_lit 2816640)), (nat_lit 17, Int.ofNat (nat_lit 21556800)), (nat_lit 18, Int.ofNat (nat_lit 21798720)), (nat_lit 19, Int.ofNat (nat_lit 22040640)), (nat_lit 20, Int.ofNat (nat_lit 22282560)), (nat_lit 21, Int.ofNat (nat_lit 22524480)), (nat_lit 22, Int.ofNat (nat_lit 22766400)), (nat_lit 23, Int.ofNat (nat_lit 23878080)), (nat_lit 24, Int.ofNat (nat_lit 47524320)), (nat_lit 25, Int.ofNat (nat_lit 19913040)), (nat_lit 26, Int.ofNat (nat_lit 8791200)), (nat_lit 27, Int.ofNat (nat_lit 4471920)), (nat_lit 28, Int.ofNat (nat_lit 2792880)), (nat_lit 32, Int.ofNat (nat_lit 24606720)), (nat_lit 33, Int.ofNat (nat_lit 51598080)), (nat_lit 34, Int.ofNat (nat_lit 53982720)), (nat_lit 35, Int.ofNat (nat_lit 56367360)), (nat_lit 36, Int.ofNat (nat_lit 58752000)), (nat_lit 37, Int.ofNat (nat_lit 61136640)), (nat_lit 38, Int.ofNat (nat_lit 63521280)), (nat_lit 39, Int.ofNat (nat_lit 80002080)), (nat_lit 40, Int.ofNat (nat_lit 48319200)), (nat_lit 41, Int.ofNat (nat_lit 33558840)), (nat_lit 42, Int.ofNat (nat_lit 9119520)), (nat_lit 43, Int.ofNat (nat_lit 10851840)), (nat_lit 48, Int.ofNat (nat_lit 25790400)), (nat_lit 49, Int.ofNat (nat_lit 53758080)), (nat_lit 50, Int.ofNat (nat_lit 57335040)), (nat_lit 51, Int.ofNat (nat_lit 60912000)), (nat_lit 52, Int.ofNat (nat_lit 64601280)), (nat_lit 53, Int.ofNat (nat_lit 68290560)), (nat_lit 54, Int.ofNat (nat_lit 85263840)), (nat_lit 55, Int.ofNat (nat_lit 54403380)), (nat_lit 56, Int.ofNat (nat_lit 38354040)), (nat_lit 57, Int.ofNat (nat_lit 15224220)), (nat_lit 58, Int.ofNat (nat_lit 18271980)), (nat_lit 59, Int.ofNat (nat_lit 1041660)), (nat_lit 64, Int.ofNat (nat_lit 33416640)), (nat_lit 65, Int.ofNat (nat_lit 62148960)), (nat_lit 66, Int.ofNat (nat_lit 66313440)), (nat_lit 67, Int.ofNat (nat_lit 70477920)), (nat_lit 68, Int.ofNat (nat_lit 74642400)), (nat_lit 69, Int.ofNat (nat_lit 90525600)), (nat_lit 70, Int.ofNat (nat_lit 61395660)), (nat_lit 71, Int.ofNat (nat_lit 43149240)), (nat_lit 72, Int.ofNat (nat_lit 22546980)), (nat_lit 73, Int.ofNat (nat_lit 25656660)), (nat_lit 74, Int.ofNat (nat_lit 8488260)), (nat_lit 80, Int.ofNat (nat_lit 39827520)), (nat_lit 81, Int.ofNat (nat_lit 74807712)), (nat_lit 82, Int.ofNat (nat_lit 77670720)), (nat_lit 83, Int.ofNat (nat_lit 82012320)), (nat_lit 84, Int.ofNat (nat_lit 95787360)), (nat_lit 85, Int.ofNat (nat_lit 68358420)), (nat_lit 86, Int.ofNat (nat_lit 47944440)), (nat_lit 87, Int.ofNat (nat_lit 28341180)), (nat_lit 88, Int.ofNat (nat_lit 30612780)), (nat_lit 89, Int.ofNat (nat_lit 12606300)), (nat_lit 96, Int.ofNat (nat_lit 47183040)), (nat_lit 97, Int.ofNat (nat_lit 89196672)), (nat_lit 98, Int.ofNat (nat_lit 89320320)), (nat_lit 99, Int.ofNat (nat_lit 101049120)), (nat_lit 100, Int.ofNat (nat_lit 74616660)), (nat_lit 101, Int.ofNat (nat_lit 52739640)), (nat_lit 102, Int.ofNat (nat_lit 32741820)), (nat_lit 103, Int.ofNat (nat_lit 33815340)), (nat_lit 104, Int.ofNat (nat_lit 14610780)), (nat_lit 112, Int.ofNat (nat_lit 54378240)), (nat_lit 113, Int.ofNat (nat_lit 102218720)), (nat_lit 114, Int.ofNat (nat_lit 106800960)), (nat_lit 115, Int.ofNat (nat_lit 80515680)), (nat_lit 116, Int.ofNat (nat_lit 57534840)), (nat_lit 117, Int.ofNat (nat_lit 35679840)), (nat_lit 118, Int.ofNat (nat_lit 34919040)), (nat_lit 119, Int.ofNat (nat_lit 13880160)), (nat_lit 128, Int.ofNat (nat_lit 60480000)), (nat_lit 129, Int.ofNat (nat_lit 114342840)), (nat_lit 130, Int.ofNat (nat_lit 86347080))]
def block001_data_flat000 : CoefficientMerge.Poly := [(nat_lit 11, Int.ofNat (nat_lit 4008960))]
theorem block001_data_flat000_step : block001_data_flat000 = (CoefficientMerge.scale (4008960 : Int) atom0073Coded) := by decide +kernel
theorem block001_data_flat000_original : block001_data_flat000 = (CoefficientMerge.scale (4008960 : Int) atom0073Coded) := by
  rw [block001_data_flat000_step]
def block001_data_flat001 : CoefficientMerge.Poly := [(nat_lit 12, Int.ofNat (nat_lit 2108160))]
theorem block001_data_flat001_step : block001_data_flat001 = (CoefficientMerge.scale (2108160 : Int) atom0074Coded) := by decide +kernel
theorem block001_data_flat001_original : block001_data_flat001 = (CoefficientMerge.scale (2108160 : Int) atom0074Coded) := by
  rw [block001_data_flat001_step]
def block001_data_flat002 : CoefficientMerge.Poly := [(nat_lit 11, Int.ofNat (nat_lit 4008960)), (nat_lit 12, Int.ofNat (nat_lit 2108160))]
theorem block001_data_flat002_step : block001_data_flat002 = (CoefficientMerge.fastMerge block001_data_flat000 block001_data_flat001) := by decide +kernel
theorem block001_data_flat002_original : block001_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4008960 : Int) atom0073Coded) (CoefficientMerge.scale (2108160 : Int) atom0074Coded)) := by
  rw [block001_data_flat002_step, block001_data_flat000_original, block001_data_flat001_original]
def block001_data_flat003 : CoefficientMerge.Poly := [(nat_lit 16, Int.ofNat (nat_lit 2816640))]
theorem block001_data_flat003_step : block001_data_flat003 = (CoefficientMerge.scale (2816640 : Int) atom0075Coded) := by decide +kernel
theorem block001_data_flat003_original : block001_data_flat003 = (CoefficientMerge.scale (2816640 : Int) atom0075Coded) := by
  rw [block001_data_flat003_step]
def block001_data_flat004 : CoefficientMerge.Poly := [(nat_lit 17, Int.ofNat (nat_lit 21556800))]
theorem block001_data_flat004_step : block001_data_flat004 = (CoefficientMerge.scale (21556800 : Int) atom0076Coded) := by decide +kernel
theorem block001_data_flat004_original : block001_data_flat004 = (CoefficientMerge.scale (21556800 : Int) atom0076Coded) := by
  rw [block001_data_flat004_step]
def block001_data_flat005 : CoefficientMerge.Poly := [(nat_lit 18, Int.ofNat (nat_lit 21798720))]
theorem block001_data_flat005_step : block001_data_flat005 = (CoefficientMerge.scale (21798720 : Int) atom0077Coded) := by decide +kernel
theorem block001_data_flat005_original : block001_data_flat005 = (CoefficientMerge.scale (21798720 : Int) atom0077Coded) := by
  rw [block001_data_flat005_step]
def block001_data_flat006 : CoefficientMerge.Poly := [(nat_lit 17, Int.ofNat (nat_lit 21556800)), (nat_lit 18, Int.ofNat (nat_lit 21798720))]
theorem block001_data_flat006_step : block001_data_flat006 = (CoefficientMerge.fastMerge block001_data_flat004 block001_data_flat005) := by decide +kernel
theorem block001_data_flat006_original : block001_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21556800 : Int) atom0076Coded) (CoefficientMerge.scale (21798720 : Int) atom0077Coded)) := by
  rw [block001_data_flat006_step, block001_data_flat004_original, block001_data_flat005_original]
def block001_data_flat007 : CoefficientMerge.Poly := [(nat_lit 16, Int.ofNat (nat_lit 2816640)), (nat_lit 17, Int.ofNat (nat_lit 21556800)), (nat_lit 18, Int.ofNat (nat_lit 21798720))]
theorem block001_data_flat007_step : block001_data_flat007 = (CoefficientMerge.fastMerge block001_data_flat003 block001_data_flat006) := by decide +kernel
theorem block001_data_flat007_original : block001_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2816640 : Int) atom0075Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21556800 : Int) atom0076Coded) (CoefficientMerge.scale (21798720 : Int) atom0077Coded))) := by
  rw [block001_data_flat007_step, block001_data_flat003_original, block001_data_flat006_original]
def block001_data_flat008 : CoefficientMerge.Poly := [(nat_lit 11, Int.ofNat (nat_lit 4008960)), (nat_lit 12, Int.ofNat (nat_lit 2108160)), (nat_lit 16, Int.ofNat (nat_lit 2816640)), (nat_lit 17, Int.ofNat (nat_lit 21556800)), (nat_lit 18, Int.ofNat (nat_lit 21798720))]
theorem block001_data_flat008_step : block001_data_flat008 = (CoefficientMerge.fastMerge block001_data_flat002 block001_data_flat007) := by decide +kernel
theorem block001_data_flat008_original : block001_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4008960 : Int) atom0073Coded) (CoefficientMerge.scale (2108160 : Int) atom0074Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2816640 : Int) atom0075Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21556800 : Int) atom0076Coded) (CoefficientMerge.scale (21798720 : Int) atom0077Coded)))) := by
  rw [block001_data_flat008_step, block001_data_flat002_original, block001_data_flat007_original]
def block001_data_flat009 : CoefficientMerge.Poly := [(nat_lit 19, Int.ofNat (nat_lit 22040640))]
theorem block001_data_flat009_step : block001_data_flat009 = (CoefficientMerge.scale (22040640 : Int) atom0078Coded) := by decide +kernel
theorem block001_data_flat009_original : block001_data_flat009 = (CoefficientMerge.scale (22040640 : Int) atom0078Coded) := by
  rw [block001_data_flat009_step]
def block001_data_flat010 : CoefficientMerge.Poly := [(nat_lit 20, Int.ofNat (nat_lit 22282560))]
theorem block001_data_flat010_step : block001_data_flat010 = (CoefficientMerge.scale (22282560 : Int) atom0079Coded) := by decide +kernel
theorem block001_data_flat010_original : block001_data_flat010 = (CoefficientMerge.scale (22282560 : Int) atom0079Coded) := by
  rw [block001_data_flat010_step]
def block001_data_flat011 : CoefficientMerge.Poly := [(nat_lit 19, Int.ofNat (nat_lit 22040640)), (nat_lit 20, Int.ofNat (nat_lit 22282560))]
theorem block001_data_flat011_step : block001_data_flat011 = (CoefficientMerge.fastMerge block001_data_flat009 block001_data_flat010) := by decide +kernel
theorem block001_data_flat011_original : block001_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22040640 : Int) atom0078Coded) (CoefficientMerge.scale (22282560 : Int) atom0079Coded)) := by
  rw [block001_data_flat011_step, block001_data_flat009_original, block001_data_flat010_original]
def block001_data_flat012 : CoefficientMerge.Poly := [(nat_lit 21, Int.ofNat (nat_lit 22524480))]
theorem block001_data_flat012_step : block001_data_flat012 = (CoefficientMerge.scale (22524480 : Int) atom0080Coded) := by decide +kernel
theorem block001_data_flat012_original : block001_data_flat012 = (CoefficientMerge.scale (22524480 : Int) atom0080Coded) := by
  rw [block001_data_flat012_step]
def block001_data_flat013 : CoefficientMerge.Poly := [(nat_lit 22, Int.ofNat (nat_lit 22766400))]
theorem block001_data_flat013_step : block001_data_flat013 = (CoefficientMerge.scale (22766400 : Int) atom0081Coded) := by decide +kernel
theorem block001_data_flat013_original : block001_data_flat013 = (CoefficientMerge.scale (22766400 : Int) atom0081Coded) := by
  rw [block001_data_flat013_step]
def block001_data_flat014 : CoefficientMerge.Poly := [(nat_lit 23, Int.ofNat (nat_lit 23878080))]
theorem block001_data_flat014_step : block001_data_flat014 = (CoefficientMerge.scale (23878080 : Int) atom0082Coded) := by decide +kernel
theorem block001_data_flat014_original : block001_data_flat014 = (CoefficientMerge.scale (23878080 : Int) atom0082Coded) := by
  rw [block001_data_flat014_step]
def block001_data_flat015 : CoefficientMerge.Poly := [(nat_lit 22, Int.ofNat (nat_lit 22766400)), (nat_lit 23, Int.ofNat (nat_lit 23878080))]
theorem block001_data_flat015_step : block001_data_flat015 = (CoefficientMerge.fastMerge block001_data_flat013 block001_data_flat014) := by decide +kernel
theorem block001_data_flat015_original : block001_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22766400 : Int) atom0081Coded) (CoefficientMerge.scale (23878080 : Int) atom0082Coded)) := by
  rw [block001_data_flat015_step, block001_data_flat013_original, block001_data_flat014_original]
def block001_data_flat016 : CoefficientMerge.Poly := [(nat_lit 21, Int.ofNat (nat_lit 22524480)), (nat_lit 22, Int.ofNat (nat_lit 22766400)), (nat_lit 23, Int.ofNat (nat_lit 23878080))]
theorem block001_data_flat016_step : block001_data_flat016 = (CoefficientMerge.fastMerge block001_data_flat012 block001_data_flat015) := by decide +kernel
theorem block001_data_flat016_original : block001_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22524480 : Int) atom0080Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22766400 : Int) atom0081Coded) (CoefficientMerge.scale (23878080 : Int) atom0082Coded))) := by
  rw [block001_data_flat016_step, block001_data_flat012_original, block001_data_flat015_original]
def block001_data_flat017 : CoefficientMerge.Poly := [(nat_lit 19, Int.ofNat (nat_lit 22040640)), (nat_lit 20, Int.ofNat (nat_lit 22282560)), (nat_lit 21, Int.ofNat (nat_lit 22524480)), (nat_lit 22, Int.ofNat (nat_lit 22766400)), (nat_lit 23, Int.ofNat (nat_lit 23878080))]
theorem block001_data_flat017_step : block001_data_flat017 = (CoefficientMerge.fastMerge block001_data_flat011 block001_data_flat016) := by decide +kernel
theorem block001_data_flat017_original : block001_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22040640 : Int) atom0078Coded) (CoefficientMerge.scale (22282560 : Int) atom0079Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22524480 : Int) atom0080Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22766400 : Int) atom0081Coded) (CoefficientMerge.scale (23878080 : Int) atom0082Coded)))) := by
  rw [block001_data_flat017_step, block001_data_flat011_original, block001_data_flat016_original]
def block001_data_flat018 : CoefficientMerge.Poly := [(nat_lit 11, Int.ofNat (nat_lit 4008960)), (nat_lit 12, Int.ofNat (nat_lit 2108160)), (nat_lit 16, Int.ofNat (nat_lit 2816640)), (nat_lit 17, Int.ofNat (nat_lit 21556800)), (nat_lit 18, Int.ofNat (nat_lit 21798720)), (nat_lit 19, Int.ofNat (nat_lit 22040640)), (nat_lit 20, Int.ofNat (nat_lit 22282560)), (nat_lit 21, Int.ofNat (nat_lit 22524480)), (nat_lit 22, Int.ofNat (nat_lit 22766400)), (nat_lit 23, Int.ofNat (nat_lit 23878080))]
theorem block001_data_flat018_step : block001_data_flat018 = (CoefficientMerge.fastMerge block001_data_flat008 block001_data_flat017) := by decide +kernel
theorem block001_data_flat018_original : block001_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4008960 : Int) atom0073Coded) (CoefficientMerge.scale (2108160 : Int) atom0074Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2816640 : Int) atom0075Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21556800 : Int) atom0076Coded) (CoefficientMerge.scale (21798720 : Int) atom0077Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22040640 : Int) atom0078Coded) (CoefficientMerge.scale (22282560 : Int) atom0079Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22524480 : Int) atom0080Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22766400 : Int) atom0081Coded) (CoefficientMerge.scale (23878080 : Int) atom0082Coded))))) := by
  rw [block001_data_flat018_step, block001_data_flat008_original, block001_data_flat017_original]
def block001_data_flat019 : CoefficientMerge.Poly := [(nat_lit 24, Int.ofNat (nat_lit 47524320))]
theorem block001_data_flat019_step : block001_data_flat019 = (CoefficientMerge.scale (47524320 : Int) atom0083Coded) := by decide +kernel
theorem block001_data_flat019_original : block001_data_flat019 = (CoefficientMerge.scale (47524320 : Int) atom0083Coded) := by
  rw [block001_data_flat019_step]
def block001_data_flat020 : CoefficientMerge.Poly := [(nat_lit 25, Int.ofNat (nat_lit 19913040))]
theorem block001_data_flat020_step : block001_data_flat020 = (CoefficientMerge.scale (19913040 : Int) atom0084Coded) := by decide +kernel
theorem block001_data_flat020_original : block001_data_flat020 = (CoefficientMerge.scale (19913040 : Int) atom0084Coded) := by
  rw [block001_data_flat020_step]
def block001_data_flat021 : CoefficientMerge.Poly := [(nat_lit 24, Int.ofNat (nat_lit 47524320)), (nat_lit 25, Int.ofNat (nat_lit 19913040))]
theorem block001_data_flat021_step : block001_data_flat021 = (CoefficientMerge.fastMerge block001_data_flat019 block001_data_flat020) := by decide +kernel
theorem block001_data_flat021_original : block001_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (47524320 : Int) atom0083Coded) (CoefficientMerge.scale (19913040 : Int) atom0084Coded)) := by
  rw [block001_data_flat021_step, block001_data_flat019_original, block001_data_flat020_original]
def block001_data_flat022 : CoefficientMerge.Poly := [(nat_lit 26, Int.ofNat (nat_lit 8791200))]
theorem block001_data_flat022_step : block001_data_flat022 = (CoefficientMerge.scale (8791200 : Int) atom0085Coded) := by decide +kernel
theorem block001_data_flat022_original : block001_data_flat022 = (CoefficientMerge.scale (8791200 : Int) atom0085Coded) := by
  rw [block001_data_flat022_step]
def block001_data_flat023 : CoefficientMerge.Poly := [(nat_lit 27, Int.ofNat (nat_lit 4471920))]
theorem block001_data_flat023_step : block001_data_flat023 = (CoefficientMerge.scale (4471920 : Int) atom0086Coded) := by decide +kernel
theorem block001_data_flat023_original : block001_data_flat023 = (CoefficientMerge.scale (4471920 : Int) atom0086Coded) := by
  rw [block001_data_flat023_step]
def block001_data_flat024 : CoefficientMerge.Poly := [(nat_lit 28, Int.ofNat (nat_lit 2792880))]
theorem block001_data_flat024_step : block001_data_flat024 = (CoefficientMerge.scale (2792880 : Int) atom0087Coded) := by decide +kernel
theorem block001_data_flat024_original : block001_data_flat024 = (CoefficientMerge.scale (2792880 : Int) atom0087Coded) := by
  rw [block001_data_flat024_step]
def block001_data_flat025 : CoefficientMerge.Poly := [(nat_lit 27, Int.ofNat (nat_lit 4471920)), (nat_lit 28, Int.ofNat (nat_lit 2792880))]
theorem block001_data_flat025_step : block001_data_flat025 = (CoefficientMerge.fastMerge block001_data_flat023 block001_data_flat024) := by decide +kernel
theorem block001_data_flat025_original : block001_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4471920 : Int) atom0086Coded) (CoefficientMerge.scale (2792880 : Int) atom0087Coded)) := by
  rw [block001_data_flat025_step, block001_data_flat023_original, block001_data_flat024_original]
def block001_data_flat026 : CoefficientMerge.Poly := [(nat_lit 26, Int.ofNat (nat_lit 8791200)), (nat_lit 27, Int.ofNat (nat_lit 4471920)), (nat_lit 28, Int.ofNat (nat_lit 2792880))]
theorem block001_data_flat026_step : block001_data_flat026 = (CoefficientMerge.fastMerge block001_data_flat022 block001_data_flat025) := by decide +kernel
theorem block001_data_flat026_original : block001_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8791200 : Int) atom0085Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4471920 : Int) atom0086Coded) (CoefficientMerge.scale (2792880 : Int) atom0087Coded))) := by
  rw [block001_data_flat026_step, block001_data_flat022_original, block001_data_flat025_original]
def block001_data_flat027 : CoefficientMerge.Poly := [(nat_lit 24, Int.ofNat (nat_lit 47524320)), (nat_lit 25, Int.ofNat (nat_lit 19913040)), (nat_lit 26, Int.ofNat (nat_lit 8791200)), (nat_lit 27, Int.ofNat (nat_lit 4471920)), (nat_lit 28, Int.ofNat (nat_lit 2792880))]
theorem block001_data_flat027_step : block001_data_flat027 = (CoefficientMerge.fastMerge block001_data_flat021 block001_data_flat026) := by decide +kernel
theorem block001_data_flat027_original : block001_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47524320 : Int) atom0083Coded) (CoefficientMerge.scale (19913040 : Int) atom0084Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8791200 : Int) atom0085Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4471920 : Int) atom0086Coded) (CoefficientMerge.scale (2792880 : Int) atom0087Coded)))) := by
  rw [block001_data_flat027_step, block001_data_flat021_original, block001_data_flat026_original]
def block001_data_flat028 : CoefficientMerge.Poly := [(nat_lit 32, Int.ofNat (nat_lit 24606720))]
theorem block001_data_flat028_step : block001_data_flat028 = (CoefficientMerge.scale (24606720 : Int) atom0088Coded) := by decide +kernel
theorem block001_data_flat028_original : block001_data_flat028 = (CoefficientMerge.scale (24606720 : Int) atom0088Coded) := by
  rw [block001_data_flat028_step]
def block001_data_flat029 : CoefficientMerge.Poly := [(nat_lit 33, Int.ofNat (nat_lit 51598080))]
theorem block001_data_flat029_step : block001_data_flat029 = (CoefficientMerge.scale (51598080 : Int) atom0089Coded) := by decide +kernel
theorem block001_data_flat029_original : block001_data_flat029 = (CoefficientMerge.scale (51598080 : Int) atom0089Coded) := by
  rw [block001_data_flat029_step]
def block001_data_flat030 : CoefficientMerge.Poly := [(nat_lit 32, Int.ofNat (nat_lit 24606720)), (nat_lit 33, Int.ofNat (nat_lit 51598080))]
theorem block001_data_flat030_step : block001_data_flat030 = (CoefficientMerge.fastMerge block001_data_flat028 block001_data_flat029) := by decide +kernel
theorem block001_data_flat030_original : block001_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24606720 : Int) atom0088Coded) (CoefficientMerge.scale (51598080 : Int) atom0089Coded)) := by
  rw [block001_data_flat030_step, block001_data_flat028_original, block001_data_flat029_original]
def block001_data_flat031 : CoefficientMerge.Poly := [(nat_lit 34, Int.ofNat (nat_lit 53982720))]
theorem block001_data_flat031_step : block001_data_flat031 = (CoefficientMerge.scale (53982720 : Int) atom0090Coded) := by decide +kernel
theorem block001_data_flat031_original : block001_data_flat031 = (CoefficientMerge.scale (53982720 : Int) atom0090Coded) := by
  rw [block001_data_flat031_step]
def block001_data_flat032 : CoefficientMerge.Poly := [(nat_lit 35, Int.ofNat (nat_lit 56367360))]
theorem block001_data_flat032_step : block001_data_flat032 = (CoefficientMerge.scale (56367360 : Int) atom0091Coded) := by decide +kernel
theorem block001_data_flat032_original : block001_data_flat032 = (CoefficientMerge.scale (56367360 : Int) atom0091Coded) := by
  rw [block001_data_flat032_step]
def block001_data_flat033 : CoefficientMerge.Poly := [(nat_lit 36, Int.ofNat (nat_lit 58752000))]
theorem block001_data_flat033_step : block001_data_flat033 = (CoefficientMerge.scale (58752000 : Int) atom0092Coded) := by decide +kernel
theorem block001_data_flat033_original : block001_data_flat033 = (CoefficientMerge.scale (58752000 : Int) atom0092Coded) := by
  rw [block001_data_flat033_step]
def block001_data_flat034 : CoefficientMerge.Poly := [(nat_lit 35, Int.ofNat (nat_lit 56367360)), (nat_lit 36, Int.ofNat (nat_lit 58752000))]
theorem block001_data_flat034_step : block001_data_flat034 = (CoefficientMerge.fastMerge block001_data_flat032 block001_data_flat033) := by decide +kernel
theorem block001_data_flat034_original : block001_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (56367360 : Int) atom0091Coded) (CoefficientMerge.scale (58752000 : Int) atom0092Coded)) := by
  rw [block001_data_flat034_step, block001_data_flat032_original, block001_data_flat033_original]
def block001_data_flat035 : CoefficientMerge.Poly := [(nat_lit 34, Int.ofNat (nat_lit 53982720)), (nat_lit 35, Int.ofNat (nat_lit 56367360)), (nat_lit 36, Int.ofNat (nat_lit 58752000))]
theorem block001_data_flat035_step : block001_data_flat035 = (CoefficientMerge.fastMerge block001_data_flat031 block001_data_flat034) := by decide +kernel
theorem block001_data_flat035_original : block001_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (53982720 : Int) atom0090Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56367360 : Int) atom0091Coded) (CoefficientMerge.scale (58752000 : Int) atom0092Coded))) := by
  rw [block001_data_flat035_step, block001_data_flat031_original, block001_data_flat034_original]
def block001_data_flat036 : CoefficientMerge.Poly := [(nat_lit 32, Int.ofNat (nat_lit 24606720)), (nat_lit 33, Int.ofNat (nat_lit 51598080)), (nat_lit 34, Int.ofNat (nat_lit 53982720)), (nat_lit 35, Int.ofNat (nat_lit 56367360)), (nat_lit 36, Int.ofNat (nat_lit 58752000))]
theorem block001_data_flat036_step : block001_data_flat036 = (CoefficientMerge.fastMerge block001_data_flat030 block001_data_flat035) := by decide +kernel
theorem block001_data_flat036_original : block001_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24606720 : Int) atom0088Coded) (CoefficientMerge.scale (51598080 : Int) atom0089Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53982720 : Int) atom0090Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56367360 : Int) atom0091Coded) (CoefficientMerge.scale (58752000 : Int) atom0092Coded)))) := by
  rw [block001_data_flat036_step, block001_data_flat030_original, block001_data_flat035_original]
def block001_data_flat037 : CoefficientMerge.Poly := [(nat_lit 24, Int.ofNat (nat_lit 47524320)), (nat_lit 25, Int.ofNat (nat_lit 19913040)), (nat_lit 26, Int.ofNat (nat_lit 8791200)), (nat_lit 27, Int.ofNat (nat_lit 4471920)), (nat_lit 28, Int.ofNat (nat_lit 2792880)), (nat_lit 32, Int.ofNat (nat_lit 24606720)), (nat_lit 33, Int.ofNat (nat_lit 51598080)), (nat_lit 34, Int.ofNat (nat_lit 53982720)), (nat_lit 35, Int.ofNat (nat_lit 56367360)), (nat_lit 36, Int.ofNat (nat_lit 58752000))]
theorem block001_data_flat037_step : block001_data_flat037 = (CoefficientMerge.fastMerge block001_data_flat027 block001_data_flat036) := by decide +kernel
theorem block001_data_flat037_original : block001_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47524320 : Int) atom0083Coded) (CoefficientMerge.scale (19913040 : Int) atom0084Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8791200 : Int) atom0085Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4471920 : Int) atom0086Coded) (CoefficientMerge.scale (2792880 : Int) atom0087Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24606720 : Int) atom0088Coded) (CoefficientMerge.scale (51598080 : Int) atom0089Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53982720 : Int) atom0090Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56367360 : Int) atom0091Coded) (CoefficientMerge.scale (58752000 : Int) atom0092Coded))))) := by
  rw [block001_data_flat037_step, block001_data_flat027_original, block001_data_flat036_original]
def block001_data_flat038 : CoefficientMerge.Poly := [(nat_lit 11, Int.ofNat (nat_lit 4008960)), (nat_lit 12, Int.ofNat (nat_lit 2108160)), (nat_lit 16, Int.ofNat (nat_lit 2816640)), (nat_lit 17, Int.ofNat (nat_lit 21556800)), (nat_lit 18, Int.ofNat (nat_lit 21798720)), (nat_lit 19, Int.ofNat (nat_lit 22040640)), (nat_lit 20, Int.ofNat (nat_lit 22282560)), (nat_lit 21, Int.ofNat (nat_lit 22524480)), (nat_lit 22, Int.ofNat (nat_lit 22766400)), (nat_lit 23, Int.ofNat (nat_lit 23878080)), (nat_lit 24, Int.ofNat (nat_lit 47524320)), (nat_lit 25, Int.ofNat (nat_lit 19913040)), (nat_lit 26, Int.ofNat (nat_lit 8791200)), (nat_lit 27, Int.ofNat (nat_lit 4471920)), (nat_lit 28, Int.ofNat (nat_lit 2792880)), (nat_lit 32, Int.ofNat (nat_lit 24606720)), (nat_lit 33, Int.ofNat (nat_lit 51598080)), (nat_lit 34, Int.ofNat (nat_lit 53982720)), (nat_lit 35, Int.ofNat (nat_lit 56367360)), (nat_lit 36, Int.ofNat (nat_lit 58752000))]
theorem block001_data_flat038_step : block001_data_flat038 = (CoefficientMerge.fastMerge block001_data_flat018 block001_data_flat037) := by decide +kernel
theorem block001_data_flat038_original : block001_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4008960 : Int) atom0073Coded) (CoefficientMerge.scale (2108160 : Int) atom0074Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2816640 : Int) atom0075Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21556800 : Int) atom0076Coded) (CoefficientMerge.scale (21798720 : Int) atom0077Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22040640 : Int) atom0078Coded) (CoefficientMerge.scale (22282560 : Int) atom0079Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22524480 : Int) atom0080Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22766400 : Int) atom0081Coded) (CoefficientMerge.scale (23878080 : Int) atom0082Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47524320 : Int) atom0083Coded) (CoefficientMerge.scale (19913040 : Int) atom0084Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8791200 : Int) atom0085Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4471920 : Int) atom0086Coded) (CoefficientMerge.scale (2792880 : Int) atom0087Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24606720 : Int) atom0088Coded) (CoefficientMerge.scale (51598080 : Int) atom0089Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53982720 : Int) atom0090Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56367360 : Int) atom0091Coded) (CoefficientMerge.scale (58752000 : Int) atom0092Coded)))))) := by
  rw [block001_data_flat038_step, block001_data_flat018_original, block001_data_flat037_original]
def block001_data_flat039 : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 61136640))]
theorem block001_data_flat039_step : block001_data_flat039 = (CoefficientMerge.scale (61136640 : Int) atom0093Coded) := by decide +kernel
theorem block001_data_flat039_original : block001_data_flat039 = (CoefficientMerge.scale (61136640 : Int) atom0093Coded) := by
  rw [block001_data_flat039_step]
def block001_data_flat040 : CoefficientMerge.Poly := [(nat_lit 38, Int.ofNat (nat_lit 63521280))]
theorem block001_data_flat040_step : block001_data_flat040 = (CoefficientMerge.scale (63521280 : Int) atom0094Coded) := by decide +kernel
theorem block001_data_flat040_original : block001_data_flat040 = (CoefficientMerge.scale (63521280 : Int) atom0094Coded) := by
  rw [block001_data_flat040_step]
def block001_data_flat041 : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 61136640)), (nat_lit 38, Int.ofNat (nat_lit 63521280))]
theorem block001_data_flat041_step : block001_data_flat041 = (CoefficientMerge.fastMerge block001_data_flat039 block001_data_flat040) := by decide +kernel
theorem block001_data_flat041_original : block001_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (61136640 : Int) atom0093Coded) (CoefficientMerge.scale (63521280 : Int) atom0094Coded)) := by
  rw [block001_data_flat041_step, block001_data_flat039_original, block001_data_flat040_original]
def block001_data_flat042 : CoefficientMerge.Poly := [(nat_lit 39, Int.ofNat (nat_lit 80002080))]
theorem block001_data_flat042_step : block001_data_flat042 = (CoefficientMerge.scale (80002080 : Int) atom0095Coded) := by decide +kernel
theorem block001_data_flat042_original : block001_data_flat042 = (CoefficientMerge.scale (80002080 : Int) atom0095Coded) := by
  rw [block001_data_flat042_step]
def block001_data_flat043 : CoefficientMerge.Poly := [(nat_lit 40, Int.ofNat (nat_lit 48319200))]
theorem block001_data_flat043_step : block001_data_flat043 = (CoefficientMerge.scale (48319200 : Int) atom0096Coded) := by decide +kernel
theorem block001_data_flat043_original : block001_data_flat043 = (CoefficientMerge.scale (48319200 : Int) atom0096Coded) := by
  rw [block001_data_flat043_step]
def block001_data_flat044 : CoefficientMerge.Poly := [(nat_lit 41, Int.ofNat (nat_lit 33558840))]
theorem block001_data_flat044_step : block001_data_flat044 = (CoefficientMerge.scale (33558840 : Int) atom0097Coded) := by decide +kernel
theorem block001_data_flat044_original : block001_data_flat044 = (CoefficientMerge.scale (33558840 : Int) atom0097Coded) := by
  rw [block001_data_flat044_step]
def block001_data_flat045 : CoefficientMerge.Poly := [(nat_lit 40, Int.ofNat (nat_lit 48319200)), (nat_lit 41, Int.ofNat (nat_lit 33558840))]
theorem block001_data_flat045_step : block001_data_flat045 = (CoefficientMerge.fastMerge block001_data_flat043 block001_data_flat044) := by decide +kernel
theorem block001_data_flat045_original : block001_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48319200 : Int) atom0096Coded) (CoefficientMerge.scale (33558840 : Int) atom0097Coded)) := by
  rw [block001_data_flat045_step, block001_data_flat043_original, block001_data_flat044_original]
def block001_data_flat046 : CoefficientMerge.Poly := [(nat_lit 39, Int.ofNat (nat_lit 80002080)), (nat_lit 40, Int.ofNat (nat_lit 48319200)), (nat_lit 41, Int.ofNat (nat_lit 33558840))]
theorem block001_data_flat046_step : block001_data_flat046 = (CoefficientMerge.fastMerge block001_data_flat042 block001_data_flat045) := by decide +kernel
theorem block001_data_flat046_original : block001_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (80002080 : Int) atom0095Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48319200 : Int) atom0096Coded) (CoefficientMerge.scale (33558840 : Int) atom0097Coded))) := by
  rw [block001_data_flat046_step, block001_data_flat042_original, block001_data_flat045_original]
def block001_data_flat047 : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 61136640)), (nat_lit 38, Int.ofNat (nat_lit 63521280)), (nat_lit 39, Int.ofNat (nat_lit 80002080)), (nat_lit 40, Int.ofNat (nat_lit 48319200)), (nat_lit 41, Int.ofNat (nat_lit 33558840))]
theorem block001_data_flat047_step : block001_data_flat047 = (CoefficientMerge.fastMerge block001_data_flat041 block001_data_flat046) := by decide +kernel
theorem block001_data_flat047_original : block001_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61136640 : Int) atom0093Coded) (CoefficientMerge.scale (63521280 : Int) atom0094Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80002080 : Int) atom0095Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48319200 : Int) atom0096Coded) (CoefficientMerge.scale (33558840 : Int) atom0097Coded)))) := by
  rw [block001_data_flat047_step, block001_data_flat041_original, block001_data_flat046_original]
def block001_data_flat048 : CoefficientMerge.Poly := [(nat_lit 42, Int.ofNat (nat_lit 9119520))]
theorem block001_data_flat048_step : block001_data_flat048 = (CoefficientMerge.scale (9119520 : Int) atom0098Coded) := by decide +kernel
theorem block001_data_flat048_original : block001_data_flat048 = (CoefficientMerge.scale (9119520 : Int) atom0098Coded) := by
  rw [block001_data_flat048_step]
def block001_data_flat049 : CoefficientMerge.Poly := [(nat_lit 43, Int.ofNat (nat_lit 10851840))]
theorem block001_data_flat049_step : block001_data_flat049 = (CoefficientMerge.scale (10851840 : Int) atom0099Coded) := by decide +kernel
theorem block001_data_flat049_original : block001_data_flat049 = (CoefficientMerge.scale (10851840 : Int) atom0099Coded) := by
  rw [block001_data_flat049_step]
def block001_data_flat050 : CoefficientMerge.Poly := [(nat_lit 42, Int.ofNat (nat_lit 9119520)), (nat_lit 43, Int.ofNat (nat_lit 10851840))]
theorem block001_data_flat050_step : block001_data_flat050 = (CoefficientMerge.fastMerge block001_data_flat048 block001_data_flat049) := by decide +kernel
theorem block001_data_flat050_original : block001_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9119520 : Int) atom0098Coded) (CoefficientMerge.scale (10851840 : Int) atom0099Coded)) := by
  rw [block001_data_flat050_step, block001_data_flat048_original, block001_data_flat049_original]
def block001_data_flat051 : CoefficientMerge.Poly := [(nat_lit 48, Int.ofNat (nat_lit 25790400))]
theorem block001_data_flat051_step : block001_data_flat051 = (CoefficientMerge.scale (25790400 : Int) atom0100Coded) := by decide +kernel
theorem block001_data_flat051_original : block001_data_flat051 = (CoefficientMerge.scale (25790400 : Int) atom0100Coded) := by
  rw [block001_data_flat051_step]
def block001_data_flat052 : CoefficientMerge.Poly := [(nat_lit 49, Int.ofNat (nat_lit 53758080))]
theorem block001_data_flat052_step : block001_data_flat052 = (CoefficientMerge.scale (53758080 : Int) atom0101Coded) := by decide +kernel
theorem block001_data_flat052_original : block001_data_flat052 = (CoefficientMerge.scale (53758080 : Int) atom0101Coded) := by
  rw [block001_data_flat052_step]
def block001_data_flat053 : CoefficientMerge.Poly := [(nat_lit 50, Int.ofNat (nat_lit 57335040))]
theorem block001_data_flat053_step : block001_data_flat053 = (CoefficientMerge.scale (57335040 : Int) atom0102Coded) := by decide +kernel
theorem block001_data_flat053_original : block001_data_flat053 = (CoefficientMerge.scale (57335040 : Int) atom0102Coded) := by
  rw [block001_data_flat053_step]
def block001_data_flat054 : CoefficientMerge.Poly := [(nat_lit 49, Int.ofNat (nat_lit 53758080)), (nat_lit 50, Int.ofNat (nat_lit 57335040))]
theorem block001_data_flat054_step : block001_data_flat054 = (CoefficientMerge.fastMerge block001_data_flat052 block001_data_flat053) := by decide +kernel
theorem block001_data_flat054_original : block001_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (53758080 : Int) atom0101Coded) (CoefficientMerge.scale (57335040 : Int) atom0102Coded)) := by
  rw [block001_data_flat054_step, block001_data_flat052_original, block001_data_flat053_original]
def block001_data_flat055 : CoefficientMerge.Poly := [(nat_lit 48, Int.ofNat (nat_lit 25790400)), (nat_lit 49, Int.ofNat (nat_lit 53758080)), (nat_lit 50, Int.ofNat (nat_lit 57335040))]
theorem block001_data_flat055_step : block001_data_flat055 = (CoefficientMerge.fastMerge block001_data_flat051 block001_data_flat054) := by decide +kernel
theorem block001_data_flat055_original : block001_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25790400 : Int) atom0100Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53758080 : Int) atom0101Coded) (CoefficientMerge.scale (57335040 : Int) atom0102Coded))) := by
  rw [block001_data_flat055_step, block001_data_flat051_original, block001_data_flat054_original]
def block001_data_flat056 : CoefficientMerge.Poly := [(nat_lit 42, Int.ofNat (nat_lit 9119520)), (nat_lit 43, Int.ofNat (nat_lit 10851840)), (nat_lit 48, Int.ofNat (nat_lit 25790400)), (nat_lit 49, Int.ofNat (nat_lit 53758080)), (nat_lit 50, Int.ofNat (nat_lit 57335040))]
theorem block001_data_flat056_step : block001_data_flat056 = (CoefficientMerge.fastMerge block001_data_flat050 block001_data_flat055) := by decide +kernel
theorem block001_data_flat056_original : block001_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9119520 : Int) atom0098Coded) (CoefficientMerge.scale (10851840 : Int) atom0099Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25790400 : Int) atom0100Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53758080 : Int) atom0101Coded) (CoefficientMerge.scale (57335040 : Int) atom0102Coded)))) := by
  rw [block001_data_flat056_step, block001_data_flat050_original, block001_data_flat055_original]
def block001_data_flat057 : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 61136640)), (nat_lit 38, Int.ofNat (nat_lit 63521280)), (nat_lit 39, Int.ofNat (nat_lit 80002080)), (nat_lit 40, Int.ofNat (nat_lit 48319200)), (nat_lit 41, Int.ofNat (nat_lit 33558840)), (nat_lit 42, Int.ofNat (nat_lit 9119520)), (nat_lit 43, Int.ofNat (nat_lit 10851840)), (nat_lit 48, Int.ofNat (nat_lit 25790400)), (nat_lit 49, Int.ofNat (nat_lit 53758080)), (nat_lit 50, Int.ofNat (nat_lit 57335040))]
theorem block001_data_flat057_step : block001_data_flat057 = (CoefficientMerge.fastMerge block001_data_flat047 block001_data_flat056) := by decide +kernel
theorem block001_data_flat057_original : block001_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61136640 : Int) atom0093Coded) (CoefficientMerge.scale (63521280 : Int) atom0094Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80002080 : Int) atom0095Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48319200 : Int) atom0096Coded) (CoefficientMerge.scale (33558840 : Int) atom0097Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9119520 : Int) atom0098Coded) (CoefficientMerge.scale (10851840 : Int) atom0099Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25790400 : Int) atom0100Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53758080 : Int) atom0101Coded) (CoefficientMerge.scale (57335040 : Int) atom0102Coded))))) := by
  rw [block001_data_flat057_step, block001_data_flat047_original, block001_data_flat056_original]
def block001_data_flat058 : CoefficientMerge.Poly := [(nat_lit 51, Int.ofNat (nat_lit 60912000))]
theorem block001_data_flat058_step : block001_data_flat058 = (CoefficientMerge.scale (60912000 : Int) atom0103Coded) := by decide +kernel
theorem block001_data_flat058_original : block001_data_flat058 = (CoefficientMerge.scale (60912000 : Int) atom0103Coded) := by
  rw [block001_data_flat058_step]
def block001_data_flat059 : CoefficientMerge.Poly := [(nat_lit 52, Int.ofNat (nat_lit 64601280))]
theorem block001_data_flat059_step : block001_data_flat059 = (CoefficientMerge.scale (64601280 : Int) atom0104Coded) := by decide +kernel
theorem block001_data_flat059_original : block001_data_flat059 = (CoefficientMerge.scale (64601280 : Int) atom0104Coded) := by
  rw [block001_data_flat059_step]
def block001_data_flat060 : CoefficientMerge.Poly := [(nat_lit 51, Int.ofNat (nat_lit 60912000)), (nat_lit 52, Int.ofNat (nat_lit 64601280))]
theorem block001_data_flat060_step : block001_data_flat060 = (CoefficientMerge.fastMerge block001_data_flat058 block001_data_flat059) := by decide +kernel
theorem block001_data_flat060_original : block001_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (60912000 : Int) atom0103Coded) (CoefficientMerge.scale (64601280 : Int) atom0104Coded)) := by
  rw [block001_data_flat060_step, block001_data_flat058_original, block001_data_flat059_original]
def block001_data_flat061 : CoefficientMerge.Poly := [(nat_lit 53, Int.ofNat (nat_lit 68290560))]
theorem block001_data_flat061_step : block001_data_flat061 = (CoefficientMerge.scale (68290560 : Int) atom0105Coded) := by decide +kernel
theorem block001_data_flat061_original : block001_data_flat061 = (CoefficientMerge.scale (68290560 : Int) atom0105Coded) := by
  rw [block001_data_flat061_step]
def block001_data_flat062 : CoefficientMerge.Poly := [(nat_lit 54, Int.ofNat (nat_lit 85263840))]
theorem block001_data_flat062_step : block001_data_flat062 = (CoefficientMerge.scale (85263840 : Int) atom0106Coded) := by decide +kernel
theorem block001_data_flat062_original : block001_data_flat062 = (CoefficientMerge.scale (85263840 : Int) atom0106Coded) := by
  rw [block001_data_flat062_step]
def block001_data_flat063 : CoefficientMerge.Poly := [(nat_lit 55, Int.ofNat (nat_lit 54403380))]
theorem block001_data_flat063_step : block001_data_flat063 = (CoefficientMerge.scale (54403380 : Int) atom0107Coded) := by decide +kernel
theorem block001_data_flat063_original : block001_data_flat063 = (CoefficientMerge.scale (54403380 : Int) atom0107Coded) := by
  rw [block001_data_flat063_step]
def block001_data_flat064 : CoefficientMerge.Poly := [(nat_lit 54, Int.ofNat (nat_lit 85263840)), (nat_lit 55, Int.ofNat (nat_lit 54403380))]
theorem block001_data_flat064_step : block001_data_flat064 = (CoefficientMerge.fastMerge block001_data_flat062 block001_data_flat063) := by decide +kernel
theorem block001_data_flat064_original : block001_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (85263840 : Int) atom0106Coded) (CoefficientMerge.scale (54403380 : Int) atom0107Coded)) := by
  rw [block001_data_flat064_step, block001_data_flat062_original, block001_data_flat063_original]
def block001_data_flat065 : CoefficientMerge.Poly := [(nat_lit 53, Int.ofNat (nat_lit 68290560)), (nat_lit 54, Int.ofNat (nat_lit 85263840)), (nat_lit 55, Int.ofNat (nat_lit 54403380))]
theorem block001_data_flat065_step : block001_data_flat065 = (CoefficientMerge.fastMerge block001_data_flat061 block001_data_flat064) := by decide +kernel
theorem block001_data_flat065_original : block001_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (68290560 : Int) atom0105Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (85263840 : Int) atom0106Coded) (CoefficientMerge.scale (54403380 : Int) atom0107Coded))) := by
  rw [block001_data_flat065_step, block001_data_flat061_original, block001_data_flat064_original]
def block001_data_flat066 : CoefficientMerge.Poly := [(nat_lit 51, Int.ofNat (nat_lit 60912000)), (nat_lit 52, Int.ofNat (nat_lit 64601280)), (nat_lit 53, Int.ofNat (nat_lit 68290560)), (nat_lit 54, Int.ofNat (nat_lit 85263840)), (nat_lit 55, Int.ofNat (nat_lit 54403380))]
theorem block001_data_flat066_step : block001_data_flat066 = (CoefficientMerge.fastMerge block001_data_flat060 block001_data_flat065) := by decide +kernel
theorem block001_data_flat066_original : block001_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60912000 : Int) atom0103Coded) (CoefficientMerge.scale (64601280 : Int) atom0104Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68290560 : Int) atom0105Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (85263840 : Int) atom0106Coded) (CoefficientMerge.scale (54403380 : Int) atom0107Coded)))) := by
  rw [block001_data_flat066_step, block001_data_flat060_original, block001_data_flat065_original]
def block001_data_flat067 : CoefficientMerge.Poly := [(nat_lit 56, Int.ofNat (nat_lit 38354040))]
theorem block001_data_flat067_step : block001_data_flat067 = (CoefficientMerge.scale (38354040 : Int) atom0108Coded) := by decide +kernel
theorem block001_data_flat067_original : block001_data_flat067 = (CoefficientMerge.scale (38354040 : Int) atom0108Coded) := by
  rw [block001_data_flat067_step]
def block001_data_flat068 : CoefficientMerge.Poly := [(nat_lit 57, Int.ofNat (nat_lit 15224220))]
theorem block001_data_flat068_step : block001_data_flat068 = (CoefficientMerge.scale (15224220 : Int) atom0109Coded) := by decide +kernel
theorem block001_data_flat068_original : block001_data_flat068 = (CoefficientMerge.scale (15224220 : Int) atom0109Coded) := by
  rw [block001_data_flat068_step]
def block001_data_flat069 : CoefficientMerge.Poly := [(nat_lit 56, Int.ofNat (nat_lit 38354040)), (nat_lit 57, Int.ofNat (nat_lit 15224220))]
theorem block001_data_flat069_step : block001_data_flat069 = (CoefficientMerge.fastMerge block001_data_flat067 block001_data_flat068) := by decide +kernel
theorem block001_data_flat069_original : block001_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (38354040 : Int) atom0108Coded) (CoefficientMerge.scale (15224220 : Int) atom0109Coded)) := by
  rw [block001_data_flat069_step, block001_data_flat067_original, block001_data_flat068_original]
def block001_data_flat070 : CoefficientMerge.Poly := [(nat_lit 58, Int.ofNat (nat_lit 18271980))]
theorem block001_data_flat070_step : block001_data_flat070 = (CoefficientMerge.scale (18271980 : Int) atom0110Coded) := by decide +kernel
theorem block001_data_flat070_original : block001_data_flat070 = (CoefficientMerge.scale (18271980 : Int) atom0110Coded) := by
  rw [block001_data_flat070_step]
def block001_data_flat071 : CoefficientMerge.Poly := [(nat_lit 59, Int.ofNat (nat_lit 1041660))]
theorem block001_data_flat071_step : block001_data_flat071 = (CoefficientMerge.scale (1041660 : Int) atom0111Coded) := by decide +kernel
theorem block001_data_flat071_original : block001_data_flat071 = (CoefficientMerge.scale (1041660 : Int) atom0111Coded) := by
  rw [block001_data_flat071_step]
def block001_data_flat072 : CoefficientMerge.Poly := [(nat_lit 64, Int.ofNat (nat_lit 33416640))]
theorem block001_data_flat072_step : block001_data_flat072 = (CoefficientMerge.scale (33416640 : Int) atom0112Coded) := by decide +kernel
theorem block001_data_flat072_original : block001_data_flat072 = (CoefficientMerge.scale (33416640 : Int) atom0112Coded) := by
  rw [block001_data_flat072_step]
def block001_data_flat073 : CoefficientMerge.Poly := [(nat_lit 59, Int.ofNat (nat_lit 1041660)), (nat_lit 64, Int.ofNat (nat_lit 33416640))]
theorem block001_data_flat073_step : block001_data_flat073 = (CoefficientMerge.fastMerge block001_data_flat071 block001_data_flat072) := by decide +kernel
theorem block001_data_flat073_original : block001_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1041660 : Int) atom0111Coded) (CoefficientMerge.scale (33416640 : Int) atom0112Coded)) := by
  rw [block001_data_flat073_step, block001_data_flat071_original, block001_data_flat072_original]
def block001_data_flat074 : CoefficientMerge.Poly := [(nat_lit 58, Int.ofNat (nat_lit 18271980)), (nat_lit 59, Int.ofNat (nat_lit 1041660)), (nat_lit 64, Int.ofNat (nat_lit 33416640))]
theorem block001_data_flat074_step : block001_data_flat074 = (CoefficientMerge.fastMerge block001_data_flat070 block001_data_flat073) := by decide +kernel
theorem block001_data_flat074_original : block001_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18271980 : Int) atom0110Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1041660 : Int) atom0111Coded) (CoefficientMerge.scale (33416640 : Int) atom0112Coded))) := by
  rw [block001_data_flat074_step, block001_data_flat070_original, block001_data_flat073_original]
def block001_data_flat075 : CoefficientMerge.Poly := [(nat_lit 56, Int.ofNat (nat_lit 38354040)), (nat_lit 57, Int.ofNat (nat_lit 15224220)), (nat_lit 58, Int.ofNat (nat_lit 18271980)), (nat_lit 59, Int.ofNat (nat_lit 1041660)), (nat_lit 64, Int.ofNat (nat_lit 33416640))]
theorem block001_data_flat075_step : block001_data_flat075 = (CoefficientMerge.fastMerge block001_data_flat069 block001_data_flat074) := by decide +kernel
theorem block001_data_flat075_original : block001_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38354040 : Int) atom0108Coded) (CoefficientMerge.scale (15224220 : Int) atom0109Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18271980 : Int) atom0110Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1041660 : Int) atom0111Coded) (CoefficientMerge.scale (33416640 : Int) atom0112Coded)))) := by
  rw [block001_data_flat075_step, block001_data_flat069_original, block001_data_flat074_original]
def block001_data_flat076 : CoefficientMerge.Poly := [(nat_lit 51, Int.ofNat (nat_lit 60912000)), (nat_lit 52, Int.ofNat (nat_lit 64601280)), (nat_lit 53, Int.ofNat (nat_lit 68290560)), (nat_lit 54, Int.ofNat (nat_lit 85263840)), (nat_lit 55, Int.ofNat (nat_lit 54403380)), (nat_lit 56, Int.ofNat (nat_lit 38354040)), (nat_lit 57, Int.ofNat (nat_lit 15224220)), (nat_lit 58, Int.ofNat (nat_lit 18271980)), (nat_lit 59, Int.ofNat (nat_lit 1041660)), (nat_lit 64, Int.ofNat (nat_lit 33416640))]
theorem block001_data_flat076_step : block001_data_flat076 = (CoefficientMerge.fastMerge block001_data_flat066 block001_data_flat075) := by decide +kernel
theorem block001_data_flat076_original : block001_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60912000 : Int) atom0103Coded) (CoefficientMerge.scale (64601280 : Int) atom0104Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68290560 : Int) atom0105Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (85263840 : Int) atom0106Coded) (CoefficientMerge.scale (54403380 : Int) atom0107Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38354040 : Int) atom0108Coded) (CoefficientMerge.scale (15224220 : Int) atom0109Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18271980 : Int) atom0110Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1041660 : Int) atom0111Coded) (CoefficientMerge.scale (33416640 : Int) atom0112Coded))))) := by
  rw [block001_data_flat076_step, block001_data_flat066_original, block001_data_flat075_original]
def block001_data_flat077 : CoefficientMerge.Poly := [(nat_lit 37, Int.ofNat (nat_lit 61136640)), (nat_lit 38, Int.ofNat (nat_lit 63521280)), (nat_lit 39, Int.ofNat (nat_lit 80002080)), (nat_lit 40, Int.ofNat (nat_lit 48319200)), (nat_lit 41, Int.ofNat (nat_lit 33558840)), (nat_lit 42, Int.ofNat (nat_lit 9119520)), (nat_lit 43, Int.ofNat (nat_lit 10851840)), (nat_lit 48, Int.ofNat (nat_lit 25790400)), (nat_lit 49, Int.ofNat (nat_lit 53758080)), (nat_lit 50, Int.ofNat (nat_lit 57335040)), (nat_lit 51, Int.ofNat (nat_lit 60912000)), (nat_lit 52, Int.ofNat (nat_lit 64601280)), (nat_lit 53, Int.ofNat (nat_lit 68290560)), (nat_lit 54, Int.ofNat (nat_lit 85263840)), (nat_lit 55, Int.ofNat (nat_lit 54403380)), (nat_lit 56, Int.ofNat (nat_lit 38354040)), (nat_lit 57, Int.ofNat (nat_lit 15224220)), (nat_lit 58, Int.ofNat (nat_lit 18271980)), (nat_lit 59, Int.ofNat (nat_lit 1041660)), (nat_lit 64, Int.ofNat (nat_lit 33416640))]
theorem block001_data_flat077_step : block001_data_flat077 = (CoefficientMerge.fastMerge block001_data_flat057 block001_data_flat076) := by decide +kernel
theorem block001_data_flat077_original : block001_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61136640 : Int) atom0093Coded) (CoefficientMerge.scale (63521280 : Int) atom0094Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80002080 : Int) atom0095Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48319200 : Int) atom0096Coded) (CoefficientMerge.scale (33558840 : Int) atom0097Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9119520 : Int) atom0098Coded) (CoefficientMerge.scale (10851840 : Int) atom0099Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25790400 : Int) atom0100Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53758080 : Int) atom0101Coded) (CoefficientMerge.scale (57335040 : Int) atom0102Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60912000 : Int) atom0103Coded) (CoefficientMerge.scale (64601280 : Int) atom0104Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68290560 : Int) atom0105Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (85263840 : Int) atom0106Coded) (CoefficientMerge.scale (54403380 : Int) atom0107Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38354040 : Int) atom0108Coded) (CoefficientMerge.scale (15224220 : Int) atom0109Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18271980 : Int) atom0110Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1041660 : Int) atom0111Coded) (CoefficientMerge.scale (33416640 : Int) atom0112Coded)))))) := by
  rw [block001_data_flat077_step, block001_data_flat057_original, block001_data_flat076_original]
def block001_data_flat078 : CoefficientMerge.Poly := [(nat_lit 11, Int.ofNat (nat_lit 4008960)), (nat_lit 12, Int.ofNat (nat_lit 2108160)), (nat_lit 16, Int.ofNat (nat_lit 2816640)), (nat_lit 17, Int.ofNat (nat_lit 21556800)), (nat_lit 18, Int.ofNat (nat_lit 21798720)), (nat_lit 19, Int.ofNat (nat_lit 22040640)), (nat_lit 20, Int.ofNat (nat_lit 22282560)), (nat_lit 21, Int.ofNat (nat_lit 22524480)), (nat_lit 22, Int.ofNat (nat_lit 22766400)), (nat_lit 23, Int.ofNat (nat_lit 23878080)), (nat_lit 24, Int.ofNat (nat_lit 47524320)), (nat_lit 25, Int.ofNat (nat_lit 19913040)), (nat_lit 26, Int.ofNat (nat_lit 8791200)), (nat_lit 27, Int.ofNat (nat_lit 4471920)), (nat_lit 28, Int.ofNat (nat_lit 2792880)), (nat_lit 32, Int.ofNat (nat_lit 24606720)), (nat_lit 33, Int.ofNat (nat_lit 51598080)), (nat_lit 34, Int.ofNat (nat_lit 53982720)), (nat_lit 35, Int.ofNat (nat_lit 56367360)), (nat_lit 36, Int.ofNat (nat_lit 58752000)), (nat_lit 37, Int.ofNat (nat_lit 61136640)), (nat_lit 38, Int.ofNat (nat_lit 63521280)), (nat_lit 39, Int.ofNat (nat_lit 80002080)), (nat_lit 40, Int.ofNat (nat_lit 48319200)), (nat_lit 41, Int.ofNat (nat_lit 33558840)), (nat_lit 42, Int.ofNat (nat_lit 9119520)), (nat_lit 43, Int.ofNat (nat_lit 10851840)), (nat_lit 48, Int.ofNat (nat_lit 25790400)), (nat_lit 49, Int.ofNat (nat_lit 53758080)), (nat_lit 50, Int.ofNat (nat_lit 57335040)), (nat_lit 51, Int.ofNat (nat_lit 60912000)), (nat_lit 52, Int.ofNat (nat_lit 64601280)), (nat_lit 53, Int.ofNat (nat_lit 68290560)), (nat_lit 54, Int.ofNat (nat_lit 85263840)), (nat_lit 55, Int.ofNat (nat_lit 54403380)), (nat_lit 56, Int.ofNat (nat_lit 38354040)), (nat_lit 57, Int.ofNat (nat_lit 15224220)), (nat_lit 58, Int.ofNat (nat_lit 18271980)), (nat_lit 59, Int.ofNat (nat_lit 1041660)), (nat_lit 64, Int.ofNat (nat_lit 33416640))]
theorem block001_data_flat078_step : block001_data_flat078 = (CoefficientMerge.fastMerge block001_data_flat038 block001_data_flat077) := by decide +kernel
theorem block001_data_flat078_original : block001_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4008960 : Int) atom0073Coded) (CoefficientMerge.scale (2108160 : Int) atom0074Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2816640 : Int) atom0075Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21556800 : Int) atom0076Coded) (CoefficientMerge.scale (21798720 : Int) atom0077Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22040640 : Int) atom0078Coded) (CoefficientMerge.scale (22282560 : Int) atom0079Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22524480 : Int) atom0080Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22766400 : Int) atom0081Coded) (CoefficientMerge.scale (23878080 : Int) atom0082Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47524320 : Int) atom0083Coded) (CoefficientMerge.scale (19913040 : Int) atom0084Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8791200 : Int) atom0085Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4471920 : Int) atom0086Coded) (CoefficientMerge.scale (2792880 : Int) atom0087Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24606720 : Int) atom0088Coded) (CoefficientMerge.scale (51598080 : Int) atom0089Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53982720 : Int) atom0090Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56367360 : Int) atom0091Coded) (CoefficientMerge.scale (58752000 : Int) atom0092Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61136640 : Int) atom0093Coded) (CoefficientMerge.scale (63521280 : Int) atom0094Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80002080 : Int) atom0095Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48319200 : Int) atom0096Coded) (CoefficientMerge.scale (33558840 : Int) atom0097Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9119520 : Int) atom0098Coded) (CoefficientMerge.scale (10851840 : Int) atom0099Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25790400 : Int) atom0100Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53758080 : Int) atom0101Coded) (CoefficientMerge.scale (57335040 : Int) atom0102Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60912000 : Int) atom0103Coded) (CoefficientMerge.scale (64601280 : Int) atom0104Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68290560 : Int) atom0105Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (85263840 : Int) atom0106Coded) (CoefficientMerge.scale (54403380 : Int) atom0107Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38354040 : Int) atom0108Coded) (CoefficientMerge.scale (15224220 : Int) atom0109Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18271980 : Int) atom0110Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1041660 : Int) atom0111Coded) (CoefficientMerge.scale (33416640 : Int) atom0112Coded))))))) := by
  rw [block001_data_flat078_step, block001_data_flat038_original, block001_data_flat077_original]
def block001_data_flat079 : CoefficientMerge.Poly := [(nat_lit 65, Int.ofNat (nat_lit 62148960))]
theorem block001_data_flat079_step : block001_data_flat079 = (CoefficientMerge.scale (62148960 : Int) atom0113Coded) := by decide +kernel
theorem block001_data_flat079_original : block001_data_flat079 = (CoefficientMerge.scale (62148960 : Int) atom0113Coded) := by
  rw [block001_data_flat079_step]
def block001_data_flat080 : CoefficientMerge.Poly := [(nat_lit 66, Int.ofNat (nat_lit 66313440))]
theorem block001_data_flat080_step : block001_data_flat080 = (CoefficientMerge.scale (66313440 : Int) atom0114Coded) := by decide +kernel
theorem block001_data_flat080_original : block001_data_flat080 = (CoefficientMerge.scale (66313440 : Int) atom0114Coded) := by
  rw [block001_data_flat080_step]
def block001_data_flat081 : CoefficientMerge.Poly := [(nat_lit 65, Int.ofNat (nat_lit 62148960)), (nat_lit 66, Int.ofNat (nat_lit 66313440))]
theorem block001_data_flat081_step : block001_data_flat081 = (CoefficientMerge.fastMerge block001_data_flat079 block001_data_flat080) := by decide +kernel
theorem block001_data_flat081_original : block001_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (62148960 : Int) atom0113Coded) (CoefficientMerge.scale (66313440 : Int) atom0114Coded)) := by
  rw [block001_data_flat081_step, block001_data_flat079_original, block001_data_flat080_original]
def block001_data_flat082 : CoefficientMerge.Poly := [(nat_lit 67, Int.ofNat (nat_lit 70477920))]
theorem block001_data_flat082_step : block001_data_flat082 = (CoefficientMerge.scale (70477920 : Int) atom0115Coded) := by decide +kernel
theorem block001_data_flat082_original : block001_data_flat082 = (CoefficientMerge.scale (70477920 : Int) atom0115Coded) := by
  rw [block001_data_flat082_step]
def block001_data_flat083 : CoefficientMerge.Poly := [(nat_lit 68, Int.ofNat (nat_lit 74642400))]
theorem block001_data_flat083_step : block001_data_flat083 = (CoefficientMerge.scale (74642400 : Int) atom0116Coded) := by decide +kernel
theorem block001_data_flat083_original : block001_data_flat083 = (CoefficientMerge.scale (74642400 : Int) atom0116Coded) := by
  rw [block001_data_flat083_step]
def block001_data_flat084 : CoefficientMerge.Poly := [(nat_lit 69, Int.ofNat (nat_lit 90525600))]
theorem block001_data_flat084_step : block001_data_flat084 = (CoefficientMerge.scale (90525600 : Int) atom0117Coded) := by decide +kernel
theorem block001_data_flat084_original : block001_data_flat084 = (CoefficientMerge.scale (90525600 : Int) atom0117Coded) := by
  rw [block001_data_flat084_step]
def block001_data_flat085 : CoefficientMerge.Poly := [(nat_lit 68, Int.ofNat (nat_lit 74642400)), (nat_lit 69, Int.ofNat (nat_lit 90525600))]
theorem block001_data_flat085_step : block001_data_flat085 = (CoefficientMerge.fastMerge block001_data_flat083 block001_data_flat084) := by decide +kernel
theorem block001_data_flat085_original : block001_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (74642400 : Int) atom0116Coded) (CoefficientMerge.scale (90525600 : Int) atom0117Coded)) := by
  rw [block001_data_flat085_step, block001_data_flat083_original, block001_data_flat084_original]
def block001_data_flat086 : CoefficientMerge.Poly := [(nat_lit 67, Int.ofNat (nat_lit 70477920)), (nat_lit 68, Int.ofNat (nat_lit 74642400)), (nat_lit 69, Int.ofNat (nat_lit 90525600))]
theorem block001_data_flat086_step : block001_data_flat086 = (CoefficientMerge.fastMerge block001_data_flat082 block001_data_flat085) := by decide +kernel
theorem block001_data_flat086_original : block001_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (70477920 : Int) atom0115Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74642400 : Int) atom0116Coded) (CoefficientMerge.scale (90525600 : Int) atom0117Coded))) := by
  rw [block001_data_flat086_step, block001_data_flat082_original, block001_data_flat085_original]
def block001_data_flat087 : CoefficientMerge.Poly := [(nat_lit 65, Int.ofNat (nat_lit 62148960)), (nat_lit 66, Int.ofNat (nat_lit 66313440)), (nat_lit 67, Int.ofNat (nat_lit 70477920)), (nat_lit 68, Int.ofNat (nat_lit 74642400)), (nat_lit 69, Int.ofNat (nat_lit 90525600))]
theorem block001_data_flat087_step : block001_data_flat087 = (CoefficientMerge.fastMerge block001_data_flat081 block001_data_flat086) := by decide +kernel
theorem block001_data_flat087_original : block001_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62148960 : Int) atom0113Coded) (CoefficientMerge.scale (66313440 : Int) atom0114Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70477920 : Int) atom0115Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74642400 : Int) atom0116Coded) (CoefficientMerge.scale (90525600 : Int) atom0117Coded)))) := by
  rw [block001_data_flat087_step, block001_data_flat081_original, block001_data_flat086_original]
def block001_data_flat088 : CoefficientMerge.Poly := [(nat_lit 70, Int.ofNat (nat_lit 61395660))]
theorem block001_data_flat088_step : block001_data_flat088 = (CoefficientMerge.scale (61395660 : Int) atom0118Coded) := by decide +kernel
theorem block001_data_flat088_original : block001_data_flat088 = (CoefficientMerge.scale (61395660 : Int) atom0118Coded) := by
  rw [block001_data_flat088_step]
def block001_data_flat089 : CoefficientMerge.Poly := [(nat_lit 71, Int.ofNat (nat_lit 43149240))]
theorem block001_data_flat089_step : block001_data_flat089 = (CoefficientMerge.scale (43149240 : Int) atom0119Coded) := by decide +kernel
theorem block001_data_flat089_original : block001_data_flat089 = (CoefficientMerge.scale (43149240 : Int) atom0119Coded) := by
  rw [block001_data_flat089_step]
def block001_data_flat090 : CoefficientMerge.Poly := [(nat_lit 70, Int.ofNat (nat_lit 61395660)), (nat_lit 71, Int.ofNat (nat_lit 43149240))]
theorem block001_data_flat090_step : block001_data_flat090 = (CoefficientMerge.fastMerge block001_data_flat088 block001_data_flat089) := by decide +kernel
theorem block001_data_flat090_original : block001_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (61395660 : Int) atom0118Coded) (CoefficientMerge.scale (43149240 : Int) atom0119Coded)) := by
  rw [block001_data_flat090_step, block001_data_flat088_original, block001_data_flat089_original]
def block001_data_flat091 : CoefficientMerge.Poly := [(nat_lit 72, Int.ofNat (nat_lit 22546980))]
theorem block001_data_flat091_step : block001_data_flat091 = (CoefficientMerge.scale (22546980 : Int) atom0120Coded) := by decide +kernel
theorem block001_data_flat091_original : block001_data_flat091 = (CoefficientMerge.scale (22546980 : Int) atom0120Coded) := by
  rw [block001_data_flat091_step]
def block001_data_flat092 : CoefficientMerge.Poly := [(nat_lit 73, Int.ofNat (nat_lit 25656660))]
theorem block001_data_flat092_step : block001_data_flat092 = (CoefficientMerge.scale (25656660 : Int) atom0121Coded) := by decide +kernel
theorem block001_data_flat092_original : block001_data_flat092 = (CoefficientMerge.scale (25656660 : Int) atom0121Coded) := by
  rw [block001_data_flat092_step]
def block001_data_flat093 : CoefficientMerge.Poly := [(nat_lit 74, Int.ofNat (nat_lit 8488260))]
theorem block001_data_flat093_step : block001_data_flat093 = (CoefficientMerge.scale (8488260 : Int) atom0122Coded) := by decide +kernel
theorem block001_data_flat093_original : block001_data_flat093 = (CoefficientMerge.scale (8488260 : Int) atom0122Coded) := by
  rw [block001_data_flat093_step]
def block001_data_flat094 : CoefficientMerge.Poly := [(nat_lit 73, Int.ofNat (nat_lit 25656660)), (nat_lit 74, Int.ofNat (nat_lit 8488260))]
theorem block001_data_flat094_step : block001_data_flat094 = (CoefficientMerge.fastMerge block001_data_flat092 block001_data_flat093) := by decide +kernel
theorem block001_data_flat094_original : block001_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25656660 : Int) atom0121Coded) (CoefficientMerge.scale (8488260 : Int) atom0122Coded)) := by
  rw [block001_data_flat094_step, block001_data_flat092_original, block001_data_flat093_original]
def block001_data_flat095 : CoefficientMerge.Poly := [(nat_lit 72, Int.ofNat (nat_lit 22546980)), (nat_lit 73, Int.ofNat (nat_lit 25656660)), (nat_lit 74, Int.ofNat (nat_lit 8488260))]
theorem block001_data_flat095_step : block001_data_flat095 = (CoefficientMerge.fastMerge block001_data_flat091 block001_data_flat094) := by decide +kernel
theorem block001_data_flat095_original : block001_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22546980 : Int) atom0120Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25656660 : Int) atom0121Coded) (CoefficientMerge.scale (8488260 : Int) atom0122Coded))) := by
  rw [block001_data_flat095_step, block001_data_flat091_original, block001_data_flat094_original]
def block001_data_flat096 : CoefficientMerge.Poly := [(nat_lit 70, Int.ofNat (nat_lit 61395660)), (nat_lit 71, Int.ofNat (nat_lit 43149240)), (nat_lit 72, Int.ofNat (nat_lit 22546980)), (nat_lit 73, Int.ofNat (nat_lit 25656660)), (nat_lit 74, Int.ofNat (nat_lit 8488260))]
theorem block001_data_flat096_step : block001_data_flat096 = (CoefficientMerge.fastMerge block001_data_flat090 block001_data_flat095) := by decide +kernel
theorem block001_data_flat096_original : block001_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61395660 : Int) atom0118Coded) (CoefficientMerge.scale (43149240 : Int) atom0119Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22546980 : Int) atom0120Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25656660 : Int) atom0121Coded) (CoefficientMerge.scale (8488260 : Int) atom0122Coded)))) := by
  rw [block001_data_flat096_step, block001_data_flat090_original, block001_data_flat095_original]
def block001_data_flat097 : CoefficientMerge.Poly := [(nat_lit 65, Int.ofNat (nat_lit 62148960)), (nat_lit 66, Int.ofNat (nat_lit 66313440)), (nat_lit 67, Int.ofNat (nat_lit 70477920)), (nat_lit 68, Int.ofNat (nat_lit 74642400)), (nat_lit 69, Int.ofNat (nat_lit 90525600)), (nat_lit 70, Int.ofNat (nat_lit 61395660)), (nat_lit 71, Int.ofNat (nat_lit 43149240)), (nat_lit 72, Int.ofNat (nat_lit 22546980)), (nat_lit 73, Int.ofNat (nat_lit 25656660)), (nat_lit 74, Int.ofNat (nat_lit 8488260))]
theorem block001_data_flat097_step : block001_data_flat097 = (CoefficientMerge.fastMerge block001_data_flat087 block001_data_flat096) := by decide +kernel
theorem block001_data_flat097_original : block001_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62148960 : Int) atom0113Coded) (CoefficientMerge.scale (66313440 : Int) atom0114Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70477920 : Int) atom0115Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74642400 : Int) atom0116Coded) (CoefficientMerge.scale (90525600 : Int) atom0117Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61395660 : Int) atom0118Coded) (CoefficientMerge.scale (43149240 : Int) atom0119Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22546980 : Int) atom0120Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25656660 : Int) atom0121Coded) (CoefficientMerge.scale (8488260 : Int) atom0122Coded))))) := by
  rw [block001_data_flat097_step, block001_data_flat087_original, block001_data_flat096_original]
def block001_data_flat098 : CoefficientMerge.Poly := [(nat_lit 80, Int.ofNat (nat_lit 39827520))]
theorem block001_data_flat098_step : block001_data_flat098 = (CoefficientMerge.scale (39827520 : Int) atom0123Coded) := by decide +kernel
theorem block001_data_flat098_original : block001_data_flat098 = (CoefficientMerge.scale (39827520 : Int) atom0123Coded) := by
  rw [block001_data_flat098_step]
def block001_data_flat099 : CoefficientMerge.Poly := [(nat_lit 81, Int.ofNat (nat_lit 74807712))]
theorem block001_data_flat099_step : block001_data_flat099 = (CoefficientMerge.scale (74807712 : Int) atom0124Coded) := by decide +kernel
theorem block001_data_flat099_original : block001_data_flat099 = (CoefficientMerge.scale (74807712 : Int) atom0124Coded) := by
  rw [block001_data_flat099_step]
def block001_data_flat100 : CoefficientMerge.Poly := [(nat_lit 80, Int.ofNat (nat_lit 39827520)), (nat_lit 81, Int.ofNat (nat_lit 74807712))]
theorem block001_data_flat100_step : block001_data_flat100 = (CoefficientMerge.fastMerge block001_data_flat098 block001_data_flat099) := by decide +kernel
theorem block001_data_flat100_original : block001_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (39827520 : Int) atom0123Coded) (CoefficientMerge.scale (74807712 : Int) atom0124Coded)) := by
  rw [block001_data_flat100_step, block001_data_flat098_original, block001_data_flat099_original]
def block001_data_flat101 : CoefficientMerge.Poly := [(nat_lit 82, Int.ofNat (nat_lit 77670720))]
theorem block001_data_flat101_step : block001_data_flat101 = (CoefficientMerge.scale (77670720 : Int) atom0125Coded) := by decide +kernel
theorem block001_data_flat101_original : block001_data_flat101 = (CoefficientMerge.scale (77670720 : Int) atom0125Coded) := by
  rw [block001_data_flat101_step]
def block001_data_flat102 : CoefficientMerge.Poly := [(nat_lit 83, Int.ofNat (nat_lit 82012320))]
theorem block001_data_flat102_step : block001_data_flat102 = (CoefficientMerge.scale (82012320 : Int) atom0126Coded) := by decide +kernel
theorem block001_data_flat102_original : block001_data_flat102 = (CoefficientMerge.scale (82012320 : Int) atom0126Coded) := by
  rw [block001_data_flat102_step]
def block001_data_flat103 : CoefficientMerge.Poly := [(nat_lit 84, Int.ofNat (nat_lit 95787360))]
theorem block001_data_flat103_step : block001_data_flat103 = (CoefficientMerge.scale (95787360 : Int) atom0127Coded) := by decide +kernel
theorem block001_data_flat103_original : block001_data_flat103 = (CoefficientMerge.scale (95787360 : Int) atom0127Coded) := by
  rw [block001_data_flat103_step]
def block001_data_flat104 : CoefficientMerge.Poly := [(nat_lit 83, Int.ofNat (nat_lit 82012320)), (nat_lit 84, Int.ofNat (nat_lit 95787360))]
theorem block001_data_flat104_step : block001_data_flat104 = (CoefficientMerge.fastMerge block001_data_flat102 block001_data_flat103) := by decide +kernel
theorem block001_data_flat104_original : block001_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (82012320 : Int) atom0126Coded) (CoefficientMerge.scale (95787360 : Int) atom0127Coded)) := by
  rw [block001_data_flat104_step, block001_data_flat102_original, block001_data_flat103_original]
def block001_data_flat105 : CoefficientMerge.Poly := [(nat_lit 82, Int.ofNat (nat_lit 77670720)), (nat_lit 83, Int.ofNat (nat_lit 82012320)), (nat_lit 84, Int.ofNat (nat_lit 95787360))]
theorem block001_data_flat105_step : block001_data_flat105 = (CoefficientMerge.fastMerge block001_data_flat101 block001_data_flat104) := by decide +kernel
theorem block001_data_flat105_original : block001_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (77670720 : Int) atom0125Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82012320 : Int) atom0126Coded) (CoefficientMerge.scale (95787360 : Int) atom0127Coded))) := by
  rw [block001_data_flat105_step, block001_data_flat101_original, block001_data_flat104_original]
def block001_data_flat106 : CoefficientMerge.Poly := [(nat_lit 80, Int.ofNat (nat_lit 39827520)), (nat_lit 81, Int.ofNat (nat_lit 74807712)), (nat_lit 82, Int.ofNat (nat_lit 77670720)), (nat_lit 83, Int.ofNat (nat_lit 82012320)), (nat_lit 84, Int.ofNat (nat_lit 95787360))]
theorem block001_data_flat106_step : block001_data_flat106 = (CoefficientMerge.fastMerge block001_data_flat100 block001_data_flat105) := by decide +kernel
theorem block001_data_flat106_original : block001_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39827520 : Int) atom0123Coded) (CoefficientMerge.scale (74807712 : Int) atom0124Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77670720 : Int) atom0125Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82012320 : Int) atom0126Coded) (CoefficientMerge.scale (95787360 : Int) atom0127Coded)))) := by
  rw [block001_data_flat106_step, block001_data_flat100_original, block001_data_flat105_original]
def block001_data_flat107 : CoefficientMerge.Poly := [(nat_lit 85, Int.ofNat (nat_lit 68358420))]
theorem block001_data_flat107_step : block001_data_flat107 = (CoefficientMerge.scale (68358420 : Int) atom0128Coded) := by decide +kernel
theorem block001_data_flat107_original : block001_data_flat107 = (CoefficientMerge.scale (68358420 : Int) atom0128Coded) := by
  rw [block001_data_flat107_step]
def block001_data_flat108 : CoefficientMerge.Poly := [(nat_lit 86, Int.ofNat (nat_lit 47944440))]
theorem block001_data_flat108_step : block001_data_flat108 = (CoefficientMerge.scale (47944440 : Int) atom0129Coded) := by decide +kernel
theorem block001_data_flat108_original : block001_data_flat108 = (CoefficientMerge.scale (47944440 : Int) atom0129Coded) := by
  rw [block001_data_flat108_step]
def block001_data_flat109 : CoefficientMerge.Poly := [(nat_lit 85, Int.ofNat (nat_lit 68358420)), (nat_lit 86, Int.ofNat (nat_lit 47944440))]
theorem block001_data_flat109_step : block001_data_flat109 = (CoefficientMerge.fastMerge block001_data_flat107 block001_data_flat108) := by decide +kernel
theorem block001_data_flat109_original : block001_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (68358420 : Int) atom0128Coded) (CoefficientMerge.scale (47944440 : Int) atom0129Coded)) := by
  rw [block001_data_flat109_step, block001_data_flat107_original, block001_data_flat108_original]
def block001_data_flat110 : CoefficientMerge.Poly := [(nat_lit 87, Int.ofNat (nat_lit 28341180))]
theorem block001_data_flat110_step : block001_data_flat110 = (CoefficientMerge.scale (28341180 : Int) atom0130Coded) := by decide +kernel
theorem block001_data_flat110_original : block001_data_flat110 = (CoefficientMerge.scale (28341180 : Int) atom0130Coded) := by
  rw [block001_data_flat110_step]
def block001_data_flat111 : CoefficientMerge.Poly := [(nat_lit 88, Int.ofNat (nat_lit 30612780))]
theorem block001_data_flat111_step : block001_data_flat111 = (CoefficientMerge.scale (30612780 : Int) atom0131Coded) := by decide +kernel
theorem block001_data_flat111_original : block001_data_flat111 = (CoefficientMerge.scale (30612780 : Int) atom0131Coded) := by
  rw [block001_data_flat111_step]
def block001_data_flat112 : CoefficientMerge.Poly := [(nat_lit 89, Int.ofNat (nat_lit 12606300))]
theorem block001_data_flat112_step : block001_data_flat112 = (CoefficientMerge.scale (12606300 : Int) atom0132Coded) := by decide +kernel
theorem block001_data_flat112_original : block001_data_flat112 = (CoefficientMerge.scale (12606300 : Int) atom0132Coded) := by
  rw [block001_data_flat112_step]
def block001_data_flat113 : CoefficientMerge.Poly := [(nat_lit 88, Int.ofNat (nat_lit 30612780)), (nat_lit 89, Int.ofNat (nat_lit 12606300))]
theorem block001_data_flat113_step : block001_data_flat113 = (CoefficientMerge.fastMerge block001_data_flat111 block001_data_flat112) := by decide +kernel
theorem block001_data_flat113_original : block001_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30612780 : Int) atom0131Coded) (CoefficientMerge.scale (12606300 : Int) atom0132Coded)) := by
  rw [block001_data_flat113_step, block001_data_flat111_original, block001_data_flat112_original]
def block001_data_flat114 : CoefficientMerge.Poly := [(nat_lit 87, Int.ofNat (nat_lit 28341180)), (nat_lit 88, Int.ofNat (nat_lit 30612780)), (nat_lit 89, Int.ofNat (nat_lit 12606300))]
theorem block001_data_flat114_step : block001_data_flat114 = (CoefficientMerge.fastMerge block001_data_flat110 block001_data_flat113) := by decide +kernel
theorem block001_data_flat114_original : block001_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28341180 : Int) atom0130Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30612780 : Int) atom0131Coded) (CoefficientMerge.scale (12606300 : Int) atom0132Coded))) := by
  rw [block001_data_flat114_step, block001_data_flat110_original, block001_data_flat113_original]
def block001_data_flat115 : CoefficientMerge.Poly := [(nat_lit 85, Int.ofNat (nat_lit 68358420)), (nat_lit 86, Int.ofNat (nat_lit 47944440)), (nat_lit 87, Int.ofNat (nat_lit 28341180)), (nat_lit 88, Int.ofNat (nat_lit 30612780)), (nat_lit 89, Int.ofNat (nat_lit 12606300))]
theorem block001_data_flat115_step : block001_data_flat115 = (CoefficientMerge.fastMerge block001_data_flat109 block001_data_flat114) := by decide +kernel
theorem block001_data_flat115_original : block001_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68358420 : Int) atom0128Coded) (CoefficientMerge.scale (47944440 : Int) atom0129Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28341180 : Int) atom0130Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30612780 : Int) atom0131Coded) (CoefficientMerge.scale (12606300 : Int) atom0132Coded)))) := by
  rw [block001_data_flat115_step, block001_data_flat109_original, block001_data_flat114_original]
def block001_data_flat116 : CoefficientMerge.Poly := [(nat_lit 80, Int.ofNat (nat_lit 39827520)), (nat_lit 81, Int.ofNat (nat_lit 74807712)), (nat_lit 82, Int.ofNat (nat_lit 77670720)), (nat_lit 83, Int.ofNat (nat_lit 82012320)), (nat_lit 84, Int.ofNat (nat_lit 95787360)), (nat_lit 85, Int.ofNat (nat_lit 68358420)), (nat_lit 86, Int.ofNat (nat_lit 47944440)), (nat_lit 87, Int.ofNat (nat_lit 28341180)), (nat_lit 88, Int.ofNat (nat_lit 30612780)), (nat_lit 89, Int.ofNat (nat_lit 12606300))]
theorem block001_data_flat116_step : block001_data_flat116 = (CoefficientMerge.fastMerge block001_data_flat106 block001_data_flat115) := by decide +kernel
theorem block001_data_flat116_original : block001_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39827520 : Int) atom0123Coded) (CoefficientMerge.scale (74807712 : Int) atom0124Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77670720 : Int) atom0125Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82012320 : Int) atom0126Coded) (CoefficientMerge.scale (95787360 : Int) atom0127Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68358420 : Int) atom0128Coded) (CoefficientMerge.scale (47944440 : Int) atom0129Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28341180 : Int) atom0130Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30612780 : Int) atom0131Coded) (CoefficientMerge.scale (12606300 : Int) atom0132Coded))))) := by
  rw [block001_data_flat116_step, block001_data_flat106_original, block001_data_flat115_original]
def block001_data_flat117 : CoefficientMerge.Poly := [(nat_lit 65, Int.ofNat (nat_lit 62148960)), (nat_lit 66, Int.ofNat (nat_lit 66313440)), (nat_lit 67, Int.ofNat (nat_lit 70477920)), (nat_lit 68, Int.ofNat (nat_lit 74642400)), (nat_lit 69, Int.ofNat (nat_lit 90525600)), (nat_lit 70, Int.ofNat (nat_lit 61395660)), (nat_lit 71, Int.ofNat (nat_lit 43149240)), (nat_lit 72, Int.ofNat (nat_lit 22546980)), (nat_lit 73, Int.ofNat (nat_lit 25656660)), (nat_lit 74, Int.ofNat (nat_lit 8488260)), (nat_lit 80, Int.ofNat (nat_lit 39827520)), (nat_lit 81, Int.ofNat (nat_lit 74807712)), (nat_lit 82, Int.ofNat (nat_lit 77670720)), (nat_lit 83, Int.ofNat (nat_lit 82012320)), (nat_lit 84, Int.ofNat (nat_lit 95787360)), (nat_lit 85, Int.ofNat (nat_lit 68358420)), (nat_lit 86, Int.ofNat (nat_lit 47944440)), (nat_lit 87, Int.ofNat (nat_lit 28341180)), (nat_lit 88, Int.ofNat (nat_lit 30612780)), (nat_lit 89, Int.ofNat (nat_lit 12606300))]
theorem block001_data_flat117_step : block001_data_flat117 = (CoefficientMerge.fastMerge block001_data_flat097 block001_data_flat116) := by decide +kernel
theorem block001_data_flat117_original : block001_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62148960 : Int) atom0113Coded) (CoefficientMerge.scale (66313440 : Int) atom0114Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70477920 : Int) atom0115Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74642400 : Int) atom0116Coded) (CoefficientMerge.scale (90525600 : Int) atom0117Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61395660 : Int) atom0118Coded) (CoefficientMerge.scale (43149240 : Int) atom0119Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22546980 : Int) atom0120Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25656660 : Int) atom0121Coded) (CoefficientMerge.scale (8488260 : Int) atom0122Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39827520 : Int) atom0123Coded) (CoefficientMerge.scale (74807712 : Int) atom0124Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77670720 : Int) atom0125Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82012320 : Int) atom0126Coded) (CoefficientMerge.scale (95787360 : Int) atom0127Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68358420 : Int) atom0128Coded) (CoefficientMerge.scale (47944440 : Int) atom0129Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28341180 : Int) atom0130Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30612780 : Int) atom0131Coded) (CoefficientMerge.scale (12606300 : Int) atom0132Coded)))))) := by
  rw [block001_data_flat117_step, block001_data_flat097_original, block001_data_flat116_original]
def block001_data_flat118 : CoefficientMerge.Poly := [(nat_lit 96, Int.ofNat (nat_lit 47183040))]
theorem block001_data_flat118_step : block001_data_flat118 = (CoefficientMerge.scale (47183040 : Int) atom0133Coded) := by decide +kernel
theorem block001_data_flat118_original : block001_data_flat118 = (CoefficientMerge.scale (47183040 : Int) atom0133Coded) := by
  rw [block001_data_flat118_step]
def block001_data_flat119 : CoefficientMerge.Poly := [(nat_lit 97, Int.ofNat (nat_lit 89196672))]
theorem block001_data_flat119_step : block001_data_flat119 = (CoefficientMerge.scale (89196672 : Int) atom0134Coded) := by decide +kernel
theorem block001_data_flat119_original : block001_data_flat119 = (CoefficientMerge.scale (89196672 : Int) atom0134Coded) := by
  rw [block001_data_flat119_step]
def block001_data_flat120 : CoefficientMerge.Poly := [(nat_lit 96, Int.ofNat (nat_lit 47183040)), (nat_lit 97, Int.ofNat (nat_lit 89196672))]
theorem block001_data_flat120_step : block001_data_flat120 = (CoefficientMerge.fastMerge block001_data_flat118 block001_data_flat119) := by decide +kernel
theorem block001_data_flat120_original : block001_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (47183040 : Int) atom0133Coded) (CoefficientMerge.scale (89196672 : Int) atom0134Coded)) := by
  rw [block001_data_flat120_step, block001_data_flat118_original, block001_data_flat119_original]
def block001_data_flat121 : CoefficientMerge.Poly := [(nat_lit 98, Int.ofNat (nat_lit 89320320))]
theorem block001_data_flat121_step : block001_data_flat121 = (CoefficientMerge.scale (89320320 : Int) atom0135Coded) := by decide +kernel
theorem block001_data_flat121_original : block001_data_flat121 = (CoefficientMerge.scale (89320320 : Int) atom0135Coded) := by
  rw [block001_data_flat121_step]
def block001_data_flat122 : CoefficientMerge.Poly := [(nat_lit 99, Int.ofNat (nat_lit 101049120))]
theorem block001_data_flat122_step : block001_data_flat122 = (CoefficientMerge.scale (101049120 : Int) atom0136Coded) := by decide +kernel
theorem block001_data_flat122_original : block001_data_flat122 = (CoefficientMerge.scale (101049120 : Int) atom0136Coded) := by
  rw [block001_data_flat122_step]
def block001_data_flat123 : CoefficientMerge.Poly := [(nat_lit 100, Int.ofNat (nat_lit 74616660))]
theorem block001_data_flat123_step : block001_data_flat123 = (CoefficientMerge.scale (74616660 : Int) atom0137Coded) := by decide +kernel
theorem block001_data_flat123_original : block001_data_flat123 = (CoefficientMerge.scale (74616660 : Int) atom0137Coded) := by
  rw [block001_data_flat123_step]
def block001_data_flat124 : CoefficientMerge.Poly := [(nat_lit 99, Int.ofNat (nat_lit 101049120)), (nat_lit 100, Int.ofNat (nat_lit 74616660))]
theorem block001_data_flat124_step : block001_data_flat124 = (CoefficientMerge.fastMerge block001_data_flat122 block001_data_flat123) := by decide +kernel
theorem block001_data_flat124_original : block001_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (101049120 : Int) atom0136Coded) (CoefficientMerge.scale (74616660 : Int) atom0137Coded)) := by
  rw [block001_data_flat124_step, block001_data_flat122_original, block001_data_flat123_original]
def block001_data_flat125 : CoefficientMerge.Poly := [(nat_lit 98, Int.ofNat (nat_lit 89320320)), (nat_lit 99, Int.ofNat (nat_lit 101049120)), (nat_lit 100, Int.ofNat (nat_lit 74616660))]
theorem block001_data_flat125_step : block001_data_flat125 = (CoefficientMerge.fastMerge block001_data_flat121 block001_data_flat124) := by decide +kernel
theorem block001_data_flat125_original : block001_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (89320320 : Int) atom0135Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101049120 : Int) atom0136Coded) (CoefficientMerge.scale (74616660 : Int) atom0137Coded))) := by
  rw [block001_data_flat125_step, block001_data_flat121_original, block001_data_flat124_original]
def block001_data_flat126 : CoefficientMerge.Poly := [(nat_lit 96, Int.ofNat (nat_lit 47183040)), (nat_lit 97, Int.ofNat (nat_lit 89196672)), (nat_lit 98, Int.ofNat (nat_lit 89320320)), (nat_lit 99, Int.ofNat (nat_lit 101049120)), (nat_lit 100, Int.ofNat (nat_lit 74616660))]
theorem block001_data_flat126_step : block001_data_flat126 = (CoefficientMerge.fastMerge block001_data_flat120 block001_data_flat125) := by decide +kernel
theorem block001_data_flat126_original : block001_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47183040 : Int) atom0133Coded) (CoefficientMerge.scale (89196672 : Int) atom0134Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89320320 : Int) atom0135Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101049120 : Int) atom0136Coded) (CoefficientMerge.scale (74616660 : Int) atom0137Coded)))) := by
  rw [block001_data_flat126_step, block001_data_flat120_original, block001_data_flat125_original]
def block001_data_flat127 : CoefficientMerge.Poly := [(nat_lit 101, Int.ofNat (nat_lit 52739640))]
theorem block001_data_flat127_step : block001_data_flat127 = (CoefficientMerge.scale (52739640 : Int) atom0138Coded) := by decide +kernel
theorem block001_data_flat127_original : block001_data_flat127 = (CoefficientMerge.scale (52739640 : Int) atom0138Coded) := by
  rw [block001_data_flat127_step]
def block001_data_flat128 : CoefficientMerge.Poly := [(nat_lit 102, Int.ofNat (nat_lit 32741820))]
theorem block001_data_flat128_step : block001_data_flat128 = (CoefficientMerge.scale (32741820 : Int) atom0139Coded) := by decide +kernel
theorem block001_data_flat128_original : block001_data_flat128 = (CoefficientMerge.scale (32741820 : Int) atom0139Coded) := by
  rw [block001_data_flat128_step]
def block001_data_flat129 : CoefficientMerge.Poly := [(nat_lit 101, Int.ofNat (nat_lit 52739640)), (nat_lit 102, Int.ofNat (nat_lit 32741820))]
theorem block001_data_flat129_step : block001_data_flat129 = (CoefficientMerge.fastMerge block001_data_flat127 block001_data_flat128) := by decide +kernel
theorem block001_data_flat129_original : block001_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (52739640 : Int) atom0138Coded) (CoefficientMerge.scale (32741820 : Int) atom0139Coded)) := by
  rw [block001_data_flat129_step, block001_data_flat127_original, block001_data_flat128_original]
def block001_data_flat130 : CoefficientMerge.Poly := [(nat_lit 103, Int.ofNat (nat_lit 33815340))]
theorem block001_data_flat130_step : block001_data_flat130 = (CoefficientMerge.scale (33815340 : Int) atom0140Coded) := by decide +kernel
theorem block001_data_flat130_original : block001_data_flat130 = (CoefficientMerge.scale (33815340 : Int) atom0140Coded) := by
  rw [block001_data_flat130_step]
def block001_data_flat131 : CoefficientMerge.Poly := [(nat_lit 104, Int.ofNat (nat_lit 14610780))]
theorem block001_data_flat131_step : block001_data_flat131 = (CoefficientMerge.scale (14610780 : Int) atom0141Coded) := by decide +kernel
theorem block001_data_flat131_original : block001_data_flat131 = (CoefficientMerge.scale (14610780 : Int) atom0141Coded) := by
  rw [block001_data_flat131_step]
def block001_data_flat132 : CoefficientMerge.Poly := [(nat_lit 112, Int.ofNat (nat_lit 54378240))]
theorem block001_data_flat132_step : block001_data_flat132 = (CoefficientMerge.scale (54378240 : Int) atom0142Coded) := by decide +kernel
theorem block001_data_flat132_original : block001_data_flat132 = (CoefficientMerge.scale (54378240 : Int) atom0142Coded) := by
  rw [block001_data_flat132_step]
def block001_data_flat133 : CoefficientMerge.Poly := [(nat_lit 104, Int.ofNat (nat_lit 14610780)), (nat_lit 112, Int.ofNat (nat_lit 54378240))]
theorem block001_data_flat133_step : block001_data_flat133 = (CoefficientMerge.fastMerge block001_data_flat131 block001_data_flat132) := by decide +kernel
theorem block001_data_flat133_original : block001_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14610780 : Int) atom0141Coded) (CoefficientMerge.scale (54378240 : Int) atom0142Coded)) := by
  rw [block001_data_flat133_step, block001_data_flat131_original, block001_data_flat132_original]
def block001_data_flat134 : CoefficientMerge.Poly := [(nat_lit 103, Int.ofNat (nat_lit 33815340)), (nat_lit 104, Int.ofNat (nat_lit 14610780)), (nat_lit 112, Int.ofNat (nat_lit 54378240))]
theorem block001_data_flat134_step : block001_data_flat134 = (CoefficientMerge.fastMerge block001_data_flat130 block001_data_flat133) := by decide +kernel
theorem block001_data_flat134_original : block001_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (33815340 : Int) atom0140Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14610780 : Int) atom0141Coded) (CoefficientMerge.scale (54378240 : Int) atom0142Coded))) := by
  rw [block001_data_flat134_step, block001_data_flat130_original, block001_data_flat133_original]
def block001_data_flat135 : CoefficientMerge.Poly := [(nat_lit 101, Int.ofNat (nat_lit 52739640)), (nat_lit 102, Int.ofNat (nat_lit 32741820)), (nat_lit 103, Int.ofNat (nat_lit 33815340)), (nat_lit 104, Int.ofNat (nat_lit 14610780)), (nat_lit 112, Int.ofNat (nat_lit 54378240))]
theorem block001_data_flat135_step : block001_data_flat135 = (CoefficientMerge.fastMerge block001_data_flat129 block001_data_flat134) := by decide +kernel
theorem block001_data_flat135_original : block001_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52739640 : Int) atom0138Coded) (CoefficientMerge.scale (32741820 : Int) atom0139Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33815340 : Int) atom0140Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14610780 : Int) atom0141Coded) (CoefficientMerge.scale (54378240 : Int) atom0142Coded)))) := by
  rw [block001_data_flat135_step, block001_data_flat129_original, block001_data_flat134_original]
def block001_data_flat136 : CoefficientMerge.Poly := [(nat_lit 96, Int.ofNat (nat_lit 47183040)), (nat_lit 97, Int.ofNat (nat_lit 89196672)), (nat_lit 98, Int.ofNat (nat_lit 89320320)), (nat_lit 99, Int.ofNat (nat_lit 101049120)), (nat_lit 100, Int.ofNat (nat_lit 74616660)), (nat_lit 101, Int.ofNat (nat_lit 52739640)), (nat_lit 102, Int.ofNat (nat_lit 32741820)), (nat_lit 103, Int.ofNat (nat_lit 33815340)), (nat_lit 104, Int.ofNat (nat_lit 14610780)), (nat_lit 112, Int.ofNat (nat_lit 54378240))]
theorem block001_data_flat136_step : block001_data_flat136 = (CoefficientMerge.fastMerge block001_data_flat126 block001_data_flat135) := by decide +kernel
theorem block001_data_flat136_original : block001_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47183040 : Int) atom0133Coded) (CoefficientMerge.scale (89196672 : Int) atom0134Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89320320 : Int) atom0135Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101049120 : Int) atom0136Coded) (CoefficientMerge.scale (74616660 : Int) atom0137Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52739640 : Int) atom0138Coded) (CoefficientMerge.scale (32741820 : Int) atom0139Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33815340 : Int) atom0140Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14610780 : Int) atom0141Coded) (CoefficientMerge.scale (54378240 : Int) atom0142Coded))))) := by
  rw [block001_data_flat136_step, block001_data_flat126_original, block001_data_flat135_original]
def block001_data_flat137 : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 102218720))]
theorem block001_data_flat137_step : block001_data_flat137 = (CoefficientMerge.scale (102218720 : Int) atom0143Coded) := by decide +kernel
theorem block001_data_flat137_original : block001_data_flat137 = (CoefficientMerge.scale (102218720 : Int) atom0143Coded) := by
  rw [block001_data_flat137_step]
def block001_data_flat138 : CoefficientMerge.Poly := [(nat_lit 114, Int.ofNat (nat_lit 106800960))]
theorem block001_data_flat138_step : block001_data_flat138 = (CoefficientMerge.scale (106800960 : Int) atom0144Coded) := by decide +kernel
theorem block001_data_flat138_original : block001_data_flat138 = (CoefficientMerge.scale (106800960 : Int) atom0144Coded) := by
  rw [block001_data_flat138_step]
def block001_data_flat139 : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 102218720)), (nat_lit 114, Int.ofNat (nat_lit 106800960))]
theorem block001_data_flat139_step : block001_data_flat139 = (CoefficientMerge.fastMerge block001_data_flat137 block001_data_flat138) := by decide +kernel
theorem block001_data_flat139_original : block001_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (102218720 : Int) atom0143Coded) (CoefficientMerge.scale (106800960 : Int) atom0144Coded)) := by
  rw [block001_data_flat139_step, block001_data_flat137_original, block001_data_flat138_original]
def block001_data_flat140 : CoefficientMerge.Poly := [(nat_lit 115, Int.ofNat (nat_lit 80515680))]
theorem block001_data_flat140_step : block001_data_flat140 = (CoefficientMerge.scale (80515680 : Int) atom0145Coded) := by decide +kernel
theorem block001_data_flat140_original : block001_data_flat140 = (CoefficientMerge.scale (80515680 : Int) atom0145Coded) := by
  rw [block001_data_flat140_step]
def block001_data_flat141 : CoefficientMerge.Poly := [(nat_lit 116, Int.ofNat (nat_lit 57534840))]
theorem block001_data_flat141_step : block001_data_flat141 = (CoefficientMerge.scale (57534840 : Int) atom0146Coded) := by decide +kernel
theorem block001_data_flat141_original : block001_data_flat141 = (CoefficientMerge.scale (57534840 : Int) atom0146Coded) := by
  rw [block001_data_flat141_step]
def block001_data_flat142 : CoefficientMerge.Poly := [(nat_lit 117, Int.ofNat (nat_lit 35679840))]
theorem block001_data_flat142_step : block001_data_flat142 = (CoefficientMerge.scale (35679840 : Int) atom0147Coded) := by decide +kernel
theorem block001_data_flat142_original : block001_data_flat142 = (CoefficientMerge.scale (35679840 : Int) atom0147Coded) := by
  rw [block001_data_flat142_step]
def block001_data_flat143 : CoefficientMerge.Poly := [(nat_lit 116, Int.ofNat (nat_lit 57534840)), (nat_lit 117, Int.ofNat (nat_lit 35679840))]
theorem block001_data_flat143_step : block001_data_flat143 = (CoefficientMerge.fastMerge block001_data_flat141 block001_data_flat142) := by decide +kernel
theorem block001_data_flat143_original : block001_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (57534840 : Int) atom0146Coded) (CoefficientMerge.scale (35679840 : Int) atom0147Coded)) := by
  rw [block001_data_flat143_step, block001_data_flat141_original, block001_data_flat142_original]
def block001_data_flat144 : CoefficientMerge.Poly := [(nat_lit 115, Int.ofNat (nat_lit 80515680)), (nat_lit 116, Int.ofNat (nat_lit 57534840)), (nat_lit 117, Int.ofNat (nat_lit 35679840))]
theorem block001_data_flat144_step : block001_data_flat144 = (CoefficientMerge.fastMerge block001_data_flat140 block001_data_flat143) := by decide +kernel
theorem block001_data_flat144_original : block001_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (80515680 : Int) atom0145Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57534840 : Int) atom0146Coded) (CoefficientMerge.scale (35679840 : Int) atom0147Coded))) := by
  rw [block001_data_flat144_step, block001_data_flat140_original, block001_data_flat143_original]
def block001_data_flat145 : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 102218720)), (nat_lit 114, Int.ofNat (nat_lit 106800960)), (nat_lit 115, Int.ofNat (nat_lit 80515680)), (nat_lit 116, Int.ofNat (nat_lit 57534840)), (nat_lit 117, Int.ofNat (nat_lit 35679840))]
theorem block001_data_flat145_step : block001_data_flat145 = (CoefficientMerge.fastMerge block001_data_flat139 block001_data_flat144) := by decide +kernel
theorem block001_data_flat145_original : block001_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (102218720 : Int) atom0143Coded) (CoefficientMerge.scale (106800960 : Int) atom0144Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80515680 : Int) atom0145Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57534840 : Int) atom0146Coded) (CoefficientMerge.scale (35679840 : Int) atom0147Coded)))) := by
  rw [block001_data_flat145_step, block001_data_flat139_original, block001_data_flat144_original]
def block001_data_flat146 : CoefficientMerge.Poly := [(nat_lit 118, Int.ofNat (nat_lit 34919040))]
theorem block001_data_flat146_step : block001_data_flat146 = (CoefficientMerge.scale (34919040 : Int) atom0148Coded) := by decide +kernel
theorem block001_data_flat146_original : block001_data_flat146 = (CoefficientMerge.scale (34919040 : Int) atom0148Coded) := by
  rw [block001_data_flat146_step]
def block001_data_flat147 : CoefficientMerge.Poly := [(nat_lit 119, Int.ofNat (nat_lit 13880160))]
theorem block001_data_flat147_step : block001_data_flat147 = (CoefficientMerge.scale (13880160 : Int) atom0149Coded) := by decide +kernel
theorem block001_data_flat147_original : block001_data_flat147 = (CoefficientMerge.scale (13880160 : Int) atom0149Coded) := by
  rw [block001_data_flat147_step]
def block001_data_flat148 : CoefficientMerge.Poly := [(nat_lit 118, Int.ofNat (nat_lit 34919040)), (nat_lit 119, Int.ofNat (nat_lit 13880160))]
theorem block001_data_flat148_step : block001_data_flat148 = (CoefficientMerge.fastMerge block001_data_flat146 block001_data_flat147) := by decide +kernel
theorem block001_data_flat148_original : block001_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34919040 : Int) atom0148Coded) (CoefficientMerge.scale (13880160 : Int) atom0149Coded)) := by
  rw [block001_data_flat148_step, block001_data_flat146_original, block001_data_flat147_original]
def block001_data_flat149 : CoefficientMerge.Poly := [(nat_lit 128, Int.ofNat (nat_lit 60480000))]
theorem block001_data_flat149_step : block001_data_flat149 = (CoefficientMerge.scale (60480000 : Int) atom0150Coded) := by decide +kernel
theorem block001_data_flat149_original : block001_data_flat149 = (CoefficientMerge.scale (60480000 : Int) atom0150Coded) := by
  rw [block001_data_flat149_step]
def block001_data_flat150 : CoefficientMerge.Poly := [(nat_lit 129, Int.ofNat (nat_lit 114342840))]
theorem block001_data_flat150_step : block001_data_flat150 = (CoefficientMerge.scale (114342840 : Int) atom0151Coded) := by decide +kernel
theorem block001_data_flat150_original : block001_data_flat150 = (CoefficientMerge.scale (114342840 : Int) atom0151Coded) := by
  rw [block001_data_flat150_step]
def block001_data_flat151 : CoefficientMerge.Poly := [(nat_lit 130, Int.ofNat (nat_lit 86347080))]
theorem block001_data_flat151_step : block001_data_flat151 = (CoefficientMerge.scale (86347080 : Int) atom0152Coded) := by decide +kernel
theorem block001_data_flat151_original : block001_data_flat151 = (CoefficientMerge.scale (86347080 : Int) atom0152Coded) := by
  rw [block001_data_flat151_step]
def block001_data_flat152 : CoefficientMerge.Poly := [(nat_lit 129, Int.ofNat (nat_lit 114342840)), (nat_lit 130, Int.ofNat (nat_lit 86347080))]
theorem block001_data_flat152_step : block001_data_flat152 = (CoefficientMerge.fastMerge block001_data_flat150 block001_data_flat151) := by decide +kernel
theorem block001_data_flat152_original : block001_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (114342840 : Int) atom0151Coded) (CoefficientMerge.scale (86347080 : Int) atom0152Coded)) := by
  rw [block001_data_flat152_step, block001_data_flat150_original, block001_data_flat151_original]
def block001_data_flat153 : CoefficientMerge.Poly := [(nat_lit 128, Int.ofNat (nat_lit 60480000)), (nat_lit 129, Int.ofNat (nat_lit 114342840)), (nat_lit 130, Int.ofNat (nat_lit 86347080))]
theorem block001_data_flat153_step : block001_data_flat153 = (CoefficientMerge.fastMerge block001_data_flat149 block001_data_flat152) := by decide +kernel
theorem block001_data_flat153_original : block001_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (60480000 : Int) atom0150Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114342840 : Int) atom0151Coded) (CoefficientMerge.scale (86347080 : Int) atom0152Coded))) := by
  rw [block001_data_flat153_step, block001_data_flat149_original, block001_data_flat152_original]
def block001_data_flat154 : CoefficientMerge.Poly := [(nat_lit 118, Int.ofNat (nat_lit 34919040)), (nat_lit 119, Int.ofNat (nat_lit 13880160)), (nat_lit 128, Int.ofNat (nat_lit 60480000)), (nat_lit 129, Int.ofNat (nat_lit 114342840)), (nat_lit 130, Int.ofNat (nat_lit 86347080))]
theorem block001_data_flat154_step : block001_data_flat154 = (CoefficientMerge.fastMerge block001_data_flat148 block001_data_flat153) := by decide +kernel
theorem block001_data_flat154_original : block001_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34919040 : Int) atom0148Coded) (CoefficientMerge.scale (13880160 : Int) atom0149Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60480000 : Int) atom0150Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114342840 : Int) atom0151Coded) (CoefficientMerge.scale (86347080 : Int) atom0152Coded)))) := by
  rw [block001_data_flat154_step, block001_data_flat148_original, block001_data_flat153_original]
def block001_data_flat155 : CoefficientMerge.Poly := [(nat_lit 113, Int.ofNat (nat_lit 102218720)), (nat_lit 114, Int.ofNat (nat_lit 106800960)), (nat_lit 115, Int.ofNat (nat_lit 80515680)), (nat_lit 116, Int.ofNat (nat_lit 57534840)), (nat_lit 117, Int.ofNat (nat_lit 35679840)), (nat_lit 118, Int.ofNat (nat_lit 34919040)), (nat_lit 119, Int.ofNat (nat_lit 13880160)), (nat_lit 128, Int.ofNat (nat_lit 60480000)), (nat_lit 129, Int.ofNat (nat_lit 114342840)), (nat_lit 130, Int.ofNat (nat_lit 86347080))]
theorem block001_data_flat155_step : block001_data_flat155 = (CoefficientMerge.fastMerge block001_data_flat145 block001_data_flat154) := by decide +kernel
theorem block001_data_flat155_original : block001_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (102218720 : Int) atom0143Coded) (CoefficientMerge.scale (106800960 : Int) atom0144Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80515680 : Int) atom0145Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57534840 : Int) atom0146Coded) (CoefficientMerge.scale (35679840 : Int) atom0147Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34919040 : Int) atom0148Coded) (CoefficientMerge.scale (13880160 : Int) atom0149Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60480000 : Int) atom0150Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114342840 : Int) atom0151Coded) (CoefficientMerge.scale (86347080 : Int) atom0152Coded))))) := by
  rw [block001_data_flat155_step, block001_data_flat145_original, block001_data_flat154_original]
def block001_data_flat156 : CoefficientMerge.Poly := [(nat_lit 96, Int.ofNat (nat_lit 47183040)), (nat_lit 97, Int.ofNat (nat_lit 89196672)), (nat_lit 98, Int.ofNat (nat_lit 89320320)), (nat_lit 99, Int.ofNat (nat_lit 101049120)), (nat_lit 100, Int.ofNat (nat_lit 74616660)), (nat_lit 101, Int.ofNat (nat_lit 52739640)), (nat_lit 102, Int.ofNat (nat_lit 32741820)), (nat_lit 103, Int.ofNat (nat_lit 33815340)), (nat_lit 104, Int.ofNat (nat_lit 14610780)), (nat_lit 112, Int.ofNat (nat_lit 54378240)), (nat_lit 113, Int.ofNat (nat_lit 102218720)), (nat_lit 114, Int.ofNat (nat_lit 106800960)), (nat_lit 115, Int.ofNat (nat_lit 80515680)), (nat_lit 116, Int.ofNat (nat_lit 57534840)), (nat_lit 117, Int.ofNat (nat_lit 35679840)), (nat_lit 118, Int.ofNat (nat_lit 34919040)), (nat_lit 119, Int.ofNat (nat_lit 13880160)), (nat_lit 128, Int.ofNat (nat_lit 60480000)), (nat_lit 129, Int.ofNat (nat_lit 114342840)), (nat_lit 130, Int.ofNat (nat_lit 86347080))]
theorem block001_data_flat156_step : block001_data_flat156 = (CoefficientMerge.fastMerge block001_data_flat136 block001_data_flat155) := by decide +kernel
theorem block001_data_flat156_original : block001_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47183040 : Int) atom0133Coded) (CoefficientMerge.scale (89196672 : Int) atom0134Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89320320 : Int) atom0135Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101049120 : Int) atom0136Coded) (CoefficientMerge.scale (74616660 : Int) atom0137Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52739640 : Int) atom0138Coded) (CoefficientMerge.scale (32741820 : Int) atom0139Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33815340 : Int) atom0140Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14610780 : Int) atom0141Coded) (CoefficientMerge.scale (54378240 : Int) atom0142Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (102218720 : Int) atom0143Coded) (CoefficientMerge.scale (106800960 : Int) atom0144Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80515680 : Int) atom0145Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57534840 : Int) atom0146Coded) (CoefficientMerge.scale (35679840 : Int) atom0147Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34919040 : Int) atom0148Coded) (CoefficientMerge.scale (13880160 : Int) atom0149Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60480000 : Int) atom0150Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114342840 : Int) atom0151Coded) (CoefficientMerge.scale (86347080 : Int) atom0152Coded)))))) := by
  rw [block001_data_flat156_step, block001_data_flat136_original, block001_data_flat155_original]
def block001_data_flat157 : CoefficientMerge.Poly := [(nat_lit 65, Int.ofNat (nat_lit 62148960)), (nat_lit 66, Int.ofNat (nat_lit 66313440)), (nat_lit 67, Int.ofNat (nat_lit 70477920)), (nat_lit 68, Int.ofNat (nat_lit 74642400)), (nat_lit 69, Int.ofNat (nat_lit 90525600)), (nat_lit 70, Int.ofNat (nat_lit 61395660)), (nat_lit 71, Int.ofNat (nat_lit 43149240)), (nat_lit 72, Int.ofNat (nat_lit 22546980)), (nat_lit 73, Int.ofNat (nat_lit 25656660)), (nat_lit 74, Int.ofNat (nat_lit 8488260)), (nat_lit 80, Int.ofNat (nat_lit 39827520)), (nat_lit 81, Int.ofNat (nat_lit 74807712)), (nat_lit 82, Int.ofNat (nat_lit 77670720)), (nat_lit 83, Int.ofNat (nat_lit 82012320)), (nat_lit 84, Int.ofNat (nat_lit 95787360)), (nat_lit 85, Int.ofNat (nat_lit 68358420)), (nat_lit 86, Int.ofNat (nat_lit 47944440)), (nat_lit 87, Int.ofNat (nat_lit 28341180)), (nat_lit 88, Int.ofNat (nat_lit 30612780)), (nat_lit 89, Int.ofNat (nat_lit 12606300)), (nat_lit 96, Int.ofNat (nat_lit 47183040)), (nat_lit 97, Int.ofNat (nat_lit 89196672)), (nat_lit 98, Int.ofNat (nat_lit 89320320)), (nat_lit 99, Int.ofNat (nat_lit 101049120)), (nat_lit 100, Int.ofNat (nat_lit 74616660)), (nat_lit 101, Int.ofNat (nat_lit 52739640)), (nat_lit 102, Int.ofNat (nat_lit 32741820)), (nat_lit 103, Int.ofNat (nat_lit 33815340)), (nat_lit 104, Int.ofNat (nat_lit 14610780)), (nat_lit 112, Int.ofNat (nat_lit 54378240)), (nat_lit 113, Int.ofNat (nat_lit 102218720)), (nat_lit 114, Int.ofNat (nat_lit 106800960)), (nat_lit 115, Int.ofNat (nat_lit 80515680)), (nat_lit 116, Int.ofNat (nat_lit 57534840)), (nat_lit 117, Int.ofNat (nat_lit 35679840)), (nat_lit 118, Int.ofNat (nat_lit 34919040)), (nat_lit 119, Int.ofNat (nat_lit 13880160)), (nat_lit 128, Int.ofNat (nat_lit 60480000)), (nat_lit 129, Int.ofNat (nat_lit 114342840)), (nat_lit 130, Int.ofNat (nat_lit 86347080))]
theorem block001_data_flat157_step : block001_data_flat157 = (CoefficientMerge.fastMerge block001_data_flat117 block001_data_flat156) := by decide +kernel
theorem block001_data_flat157_original : block001_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62148960 : Int) atom0113Coded) (CoefficientMerge.scale (66313440 : Int) atom0114Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70477920 : Int) atom0115Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74642400 : Int) atom0116Coded) (CoefficientMerge.scale (90525600 : Int) atom0117Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61395660 : Int) atom0118Coded) (CoefficientMerge.scale (43149240 : Int) atom0119Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22546980 : Int) atom0120Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25656660 : Int) atom0121Coded) (CoefficientMerge.scale (8488260 : Int) atom0122Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39827520 : Int) atom0123Coded) (CoefficientMerge.scale (74807712 : Int) atom0124Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77670720 : Int) atom0125Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82012320 : Int) atom0126Coded) (CoefficientMerge.scale (95787360 : Int) atom0127Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68358420 : Int) atom0128Coded) (CoefficientMerge.scale (47944440 : Int) atom0129Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28341180 : Int) atom0130Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30612780 : Int) atom0131Coded) (CoefficientMerge.scale (12606300 : Int) atom0132Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47183040 : Int) atom0133Coded) (CoefficientMerge.scale (89196672 : Int) atom0134Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89320320 : Int) atom0135Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101049120 : Int) atom0136Coded) (CoefficientMerge.scale (74616660 : Int) atom0137Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52739640 : Int) atom0138Coded) (CoefficientMerge.scale (32741820 : Int) atom0139Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33815340 : Int) atom0140Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14610780 : Int) atom0141Coded) (CoefficientMerge.scale (54378240 : Int) atom0142Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (102218720 : Int) atom0143Coded) (CoefficientMerge.scale (106800960 : Int) atom0144Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80515680 : Int) atom0145Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57534840 : Int) atom0146Coded) (CoefficientMerge.scale (35679840 : Int) atom0147Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34919040 : Int) atom0148Coded) (CoefficientMerge.scale (13880160 : Int) atom0149Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60480000 : Int) atom0150Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114342840 : Int) atom0151Coded) (CoefficientMerge.scale (86347080 : Int) atom0152Coded))))))) := by
  rw [block001_data_flat157_step, block001_data_flat117_original, block001_data_flat156_original]
def block001_data_flat158 : CoefficientMerge.Poly := [(nat_lit 11, Int.ofNat (nat_lit 4008960)), (nat_lit 12, Int.ofNat (nat_lit 2108160)), (nat_lit 16, Int.ofNat (nat_lit 2816640)), (nat_lit 17, Int.ofNat (nat_lit 21556800)), (nat_lit 18, Int.ofNat (nat_lit 21798720)), (nat_lit 19, Int.ofNat (nat_lit 22040640)), (nat_lit 20, Int.ofNat (nat_lit 22282560)), (nat_lit 21, Int.ofNat (nat_lit 22524480)), (nat_lit 22, Int.ofNat (nat_lit 22766400)), (nat_lit 23, Int.ofNat (nat_lit 23878080)), (nat_lit 24, Int.ofNat (nat_lit 47524320)), (nat_lit 25, Int.ofNat (nat_lit 19913040)), (nat_lit 26, Int.ofNat (nat_lit 8791200)), (nat_lit 27, Int.ofNat (nat_lit 4471920)), (nat_lit 28, Int.ofNat (nat_lit 2792880)), (nat_lit 32, Int.ofNat (nat_lit 24606720)), (nat_lit 33, Int.ofNat (nat_lit 51598080)), (nat_lit 34, Int.ofNat (nat_lit 53982720)), (nat_lit 35, Int.ofNat (nat_lit 56367360)), (nat_lit 36, Int.ofNat (nat_lit 58752000)), (nat_lit 37, Int.ofNat (nat_lit 61136640)), (nat_lit 38, Int.ofNat (nat_lit 63521280)), (nat_lit 39, Int.ofNat (nat_lit 80002080)), (nat_lit 40, Int.ofNat (nat_lit 48319200)), (nat_lit 41, Int.ofNat (nat_lit 33558840)), (nat_lit 42, Int.ofNat (nat_lit 9119520)), (nat_lit 43, Int.ofNat (nat_lit 10851840)), (nat_lit 48, Int.ofNat (nat_lit 25790400)), (nat_lit 49, Int.ofNat (nat_lit 53758080)), (nat_lit 50, Int.ofNat (nat_lit 57335040)), (nat_lit 51, Int.ofNat (nat_lit 60912000)), (nat_lit 52, Int.ofNat (nat_lit 64601280)), (nat_lit 53, Int.ofNat (nat_lit 68290560)), (nat_lit 54, Int.ofNat (nat_lit 85263840)), (nat_lit 55, Int.ofNat (nat_lit 54403380)), (nat_lit 56, Int.ofNat (nat_lit 38354040)), (nat_lit 57, Int.ofNat (nat_lit 15224220)), (nat_lit 58, Int.ofNat (nat_lit 18271980)), (nat_lit 59, Int.ofNat (nat_lit 1041660)), (nat_lit 64, Int.ofNat (nat_lit 33416640)), (nat_lit 65, Int.ofNat (nat_lit 62148960)), (nat_lit 66, Int.ofNat (nat_lit 66313440)), (nat_lit 67, Int.ofNat (nat_lit 70477920)), (nat_lit 68, Int.ofNat (nat_lit 74642400)), (nat_lit 69, Int.ofNat (nat_lit 90525600)), (nat_lit 70, Int.ofNat (nat_lit 61395660)), (nat_lit 71, Int.ofNat (nat_lit 43149240)), (nat_lit 72, Int.ofNat (nat_lit 22546980)), (nat_lit 73, Int.ofNat (nat_lit 25656660)), (nat_lit 74, Int.ofNat (nat_lit 8488260)), (nat_lit 80, Int.ofNat (nat_lit 39827520)), (nat_lit 81, Int.ofNat (nat_lit 74807712)), (nat_lit 82, Int.ofNat (nat_lit 77670720)), (nat_lit 83, Int.ofNat (nat_lit 82012320)), (nat_lit 84, Int.ofNat (nat_lit 95787360)), (nat_lit 85, Int.ofNat (nat_lit 68358420)), (nat_lit 86, Int.ofNat (nat_lit 47944440)), (nat_lit 87, Int.ofNat (nat_lit 28341180)), (nat_lit 88, Int.ofNat (nat_lit 30612780)), (nat_lit 89, Int.ofNat (nat_lit 12606300)), (nat_lit 96, Int.ofNat (nat_lit 47183040)), (nat_lit 97, Int.ofNat (nat_lit 89196672)), (nat_lit 98, Int.ofNat (nat_lit 89320320)), (nat_lit 99, Int.ofNat (nat_lit 101049120)), (nat_lit 100, Int.ofNat (nat_lit 74616660)), (nat_lit 101, Int.ofNat (nat_lit 52739640)), (nat_lit 102, Int.ofNat (nat_lit 32741820)), (nat_lit 103, Int.ofNat (nat_lit 33815340)), (nat_lit 104, Int.ofNat (nat_lit 14610780)), (nat_lit 112, Int.ofNat (nat_lit 54378240)), (nat_lit 113, Int.ofNat (nat_lit 102218720)), (nat_lit 114, Int.ofNat (nat_lit 106800960)), (nat_lit 115, Int.ofNat (nat_lit 80515680)), (nat_lit 116, Int.ofNat (nat_lit 57534840)), (nat_lit 117, Int.ofNat (nat_lit 35679840)), (nat_lit 118, Int.ofNat (nat_lit 34919040)), (nat_lit 119, Int.ofNat (nat_lit 13880160)), (nat_lit 128, Int.ofNat (nat_lit 60480000)), (nat_lit 129, Int.ofNat (nat_lit 114342840)), (nat_lit 130, Int.ofNat (nat_lit 86347080))]
theorem block001_data_flat158_step : block001_data_flat158 = (CoefficientMerge.fastMerge block001_data_flat078 block001_data_flat157) := by decide +kernel
theorem block001_data_flat158_original : block001_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4008960 : Int) atom0073Coded) (CoefficientMerge.scale (2108160 : Int) atom0074Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2816640 : Int) atom0075Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21556800 : Int) atom0076Coded) (CoefficientMerge.scale (21798720 : Int) atom0077Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22040640 : Int) atom0078Coded) (CoefficientMerge.scale (22282560 : Int) atom0079Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22524480 : Int) atom0080Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22766400 : Int) atom0081Coded) (CoefficientMerge.scale (23878080 : Int) atom0082Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47524320 : Int) atom0083Coded) (CoefficientMerge.scale (19913040 : Int) atom0084Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8791200 : Int) atom0085Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4471920 : Int) atom0086Coded) (CoefficientMerge.scale (2792880 : Int) atom0087Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24606720 : Int) atom0088Coded) (CoefficientMerge.scale (51598080 : Int) atom0089Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53982720 : Int) atom0090Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56367360 : Int) atom0091Coded) (CoefficientMerge.scale (58752000 : Int) atom0092Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61136640 : Int) atom0093Coded) (CoefficientMerge.scale (63521280 : Int) atom0094Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80002080 : Int) atom0095Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48319200 : Int) atom0096Coded) (CoefficientMerge.scale (33558840 : Int) atom0097Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9119520 : Int) atom0098Coded) (CoefficientMerge.scale (10851840 : Int) atom0099Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25790400 : Int) atom0100Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53758080 : Int) atom0101Coded) (CoefficientMerge.scale (57335040 : Int) atom0102Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60912000 : Int) atom0103Coded) (CoefficientMerge.scale (64601280 : Int) atom0104Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68290560 : Int) atom0105Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (85263840 : Int) atom0106Coded) (CoefficientMerge.scale (54403380 : Int) atom0107Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38354040 : Int) atom0108Coded) (CoefficientMerge.scale (15224220 : Int) atom0109Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18271980 : Int) atom0110Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1041660 : Int) atom0111Coded) (CoefficientMerge.scale (33416640 : Int) atom0112Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62148960 : Int) atom0113Coded) (CoefficientMerge.scale (66313440 : Int) atom0114Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70477920 : Int) atom0115Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74642400 : Int) atom0116Coded) (CoefficientMerge.scale (90525600 : Int) atom0117Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61395660 : Int) atom0118Coded) (CoefficientMerge.scale (43149240 : Int) atom0119Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22546980 : Int) atom0120Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25656660 : Int) atom0121Coded) (CoefficientMerge.scale (8488260 : Int) atom0122Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39827520 : Int) atom0123Coded) (CoefficientMerge.scale (74807712 : Int) atom0124Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77670720 : Int) atom0125Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82012320 : Int) atom0126Coded) (CoefficientMerge.scale (95787360 : Int) atom0127Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68358420 : Int) atom0128Coded) (CoefficientMerge.scale (47944440 : Int) atom0129Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28341180 : Int) atom0130Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30612780 : Int) atom0131Coded) (CoefficientMerge.scale (12606300 : Int) atom0132Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47183040 : Int) atom0133Coded) (CoefficientMerge.scale (89196672 : Int) atom0134Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89320320 : Int) atom0135Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101049120 : Int) atom0136Coded) (CoefficientMerge.scale (74616660 : Int) atom0137Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52739640 : Int) atom0138Coded) (CoefficientMerge.scale (32741820 : Int) atom0139Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33815340 : Int) atom0140Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14610780 : Int) atom0141Coded) (CoefficientMerge.scale (54378240 : Int) atom0142Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (102218720 : Int) atom0143Coded) (CoefficientMerge.scale (106800960 : Int) atom0144Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80515680 : Int) atom0145Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57534840 : Int) atom0146Coded) (CoefficientMerge.scale (35679840 : Int) atom0147Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34919040 : Int) atom0148Coded) (CoefficientMerge.scale (13880160 : Int) atom0149Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60480000 : Int) atom0150Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114342840 : Int) atom0151Coded) (CoefficientMerge.scale (86347080 : Int) atom0152Coded)))))))) := by
  rw [block001_data_flat158_step, block001_data_flat078_original, block001_data_flat157_original]
def block001_data_flat159 : CoefficientMerge.Poly := [(nat_lit 11, Int.ofNat (nat_lit 4008960)), (nat_lit 12, Int.ofNat (nat_lit 2108160)), (nat_lit 16, Int.ofNat (nat_lit 2816640)), (nat_lit 17, Int.ofNat (nat_lit 21556800)), (nat_lit 18, Int.ofNat (nat_lit 21798720)), (nat_lit 19, Int.ofNat (nat_lit 22040640)), (nat_lit 20, Int.ofNat (nat_lit 22282560)), (nat_lit 21, Int.ofNat (nat_lit 22524480)), (nat_lit 22, Int.ofNat (nat_lit 22766400)), (nat_lit 23, Int.ofNat (nat_lit 23878080)), (nat_lit 24, Int.ofNat (nat_lit 47524320)), (nat_lit 25, Int.ofNat (nat_lit 19913040)), (nat_lit 26, Int.ofNat (nat_lit 8791200)), (nat_lit 27, Int.ofNat (nat_lit 4471920)), (nat_lit 28, Int.ofNat (nat_lit 2792880)), (nat_lit 32, Int.ofNat (nat_lit 24606720)), (nat_lit 33, Int.ofNat (nat_lit 51598080)), (nat_lit 34, Int.ofNat (nat_lit 53982720)), (nat_lit 35, Int.ofNat (nat_lit 56367360)), (nat_lit 36, Int.ofNat (nat_lit 58752000)), (nat_lit 37, Int.ofNat (nat_lit 61136640)), (nat_lit 38, Int.ofNat (nat_lit 63521280)), (nat_lit 39, Int.ofNat (nat_lit 80002080)), (nat_lit 40, Int.ofNat (nat_lit 48319200)), (nat_lit 41, Int.ofNat (nat_lit 33558840)), (nat_lit 42, Int.ofNat (nat_lit 9119520)), (nat_lit 43, Int.ofNat (nat_lit 10851840)), (nat_lit 48, Int.ofNat (nat_lit 25790400)), (nat_lit 49, Int.ofNat (nat_lit 53758080)), (nat_lit 50, Int.ofNat (nat_lit 57335040)), (nat_lit 51, Int.ofNat (nat_lit 60912000)), (nat_lit 52, Int.ofNat (nat_lit 64601280)), (nat_lit 53, Int.ofNat (nat_lit 68290560)), (nat_lit 54, Int.ofNat (nat_lit 85263840)), (nat_lit 55, Int.ofNat (nat_lit 54403380)), (nat_lit 56, Int.ofNat (nat_lit 38354040)), (nat_lit 57, Int.ofNat (nat_lit 15224220)), (nat_lit 58, Int.ofNat (nat_lit 18271980)), (nat_lit 59, Int.ofNat (nat_lit 1041660)), (nat_lit 64, Int.ofNat (nat_lit 33416640)), (nat_lit 65, Int.ofNat (nat_lit 62148960)), (nat_lit 66, Int.ofNat (nat_lit 66313440)), (nat_lit 67, Int.ofNat (nat_lit 70477920)), (nat_lit 68, Int.ofNat (nat_lit 74642400)), (nat_lit 69, Int.ofNat (nat_lit 90525600)), (nat_lit 70, Int.ofNat (nat_lit 61395660)), (nat_lit 71, Int.ofNat (nat_lit 43149240)), (nat_lit 72, Int.ofNat (nat_lit 22546980)), (nat_lit 73, Int.ofNat (nat_lit 25656660)), (nat_lit 74, Int.ofNat (nat_lit 8488260)), (nat_lit 80, Int.ofNat (nat_lit 39827520)), (nat_lit 81, Int.ofNat (nat_lit 74807712)), (nat_lit 82, Int.ofNat (nat_lit 77670720)), (nat_lit 83, Int.ofNat (nat_lit 82012320)), (nat_lit 84, Int.ofNat (nat_lit 95787360)), (nat_lit 85, Int.ofNat (nat_lit 68358420)), (nat_lit 86, Int.ofNat (nat_lit 47944440)), (nat_lit 87, Int.ofNat (nat_lit 28341180)), (nat_lit 88, Int.ofNat (nat_lit 30612780)), (nat_lit 89, Int.ofNat (nat_lit 12606300)), (nat_lit 96, Int.ofNat (nat_lit 47183040)), (nat_lit 97, Int.ofNat (nat_lit 89196672)), (nat_lit 98, Int.ofNat (nat_lit 89320320)), (nat_lit 99, Int.ofNat (nat_lit 101049120)), (nat_lit 100, Int.ofNat (nat_lit 74616660)), (nat_lit 101, Int.ofNat (nat_lit 52739640)), (nat_lit 102, Int.ofNat (nat_lit 32741820)), (nat_lit 103, Int.ofNat (nat_lit 33815340)), (nat_lit 104, Int.ofNat (nat_lit 14610780)), (nat_lit 112, Int.ofNat (nat_lit 54378240)), (nat_lit 113, Int.ofNat (nat_lit 102218720)), (nat_lit 114, Int.ofNat (nat_lit 106800960)), (nat_lit 115, Int.ofNat (nat_lit 80515680)), (nat_lit 116, Int.ofNat (nat_lit 57534840)), (nat_lit 117, Int.ofNat (nat_lit 35679840)), (nat_lit 118, Int.ofNat (nat_lit 34919040)), (nat_lit 119, Int.ofNat (nat_lit 13880160)), (nat_lit 128, Int.ofNat (nat_lit 60480000)), (nat_lit 129, Int.ofNat (nat_lit 114342840)), (nat_lit 130, Int.ofNat (nat_lit 86347080))]
theorem block001_data_flat159_step : block001_data_flat159 = (CoefficientMerge.trim block001_data_flat158) := by decide +kernel
theorem block001_data_flat159_original : block001_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4008960 : Int) atom0073Coded) (CoefficientMerge.scale (2108160 : Int) atom0074Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2816640 : Int) atom0075Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21556800 : Int) atom0076Coded) (CoefficientMerge.scale (21798720 : Int) atom0077Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22040640 : Int) atom0078Coded) (CoefficientMerge.scale (22282560 : Int) atom0079Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22524480 : Int) atom0080Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22766400 : Int) atom0081Coded) (CoefficientMerge.scale (23878080 : Int) atom0082Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47524320 : Int) atom0083Coded) (CoefficientMerge.scale (19913040 : Int) atom0084Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8791200 : Int) atom0085Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4471920 : Int) atom0086Coded) (CoefficientMerge.scale (2792880 : Int) atom0087Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24606720 : Int) atom0088Coded) (CoefficientMerge.scale (51598080 : Int) atom0089Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53982720 : Int) atom0090Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56367360 : Int) atom0091Coded) (CoefficientMerge.scale (58752000 : Int) atom0092Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61136640 : Int) atom0093Coded) (CoefficientMerge.scale (63521280 : Int) atom0094Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80002080 : Int) atom0095Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48319200 : Int) atom0096Coded) (CoefficientMerge.scale (33558840 : Int) atom0097Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9119520 : Int) atom0098Coded) (CoefficientMerge.scale (10851840 : Int) atom0099Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25790400 : Int) atom0100Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53758080 : Int) atom0101Coded) (CoefficientMerge.scale (57335040 : Int) atom0102Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60912000 : Int) atom0103Coded) (CoefficientMerge.scale (64601280 : Int) atom0104Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68290560 : Int) atom0105Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (85263840 : Int) atom0106Coded) (CoefficientMerge.scale (54403380 : Int) atom0107Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38354040 : Int) atom0108Coded) (CoefficientMerge.scale (15224220 : Int) atom0109Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18271980 : Int) atom0110Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1041660 : Int) atom0111Coded) (CoefficientMerge.scale (33416640 : Int) atom0112Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62148960 : Int) atom0113Coded) (CoefficientMerge.scale (66313440 : Int) atom0114Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70477920 : Int) atom0115Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74642400 : Int) atom0116Coded) (CoefficientMerge.scale (90525600 : Int) atom0117Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61395660 : Int) atom0118Coded) (CoefficientMerge.scale (43149240 : Int) atom0119Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22546980 : Int) atom0120Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25656660 : Int) atom0121Coded) (CoefficientMerge.scale (8488260 : Int) atom0122Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39827520 : Int) atom0123Coded) (CoefficientMerge.scale (74807712 : Int) atom0124Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77670720 : Int) atom0125Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82012320 : Int) atom0126Coded) (CoefficientMerge.scale (95787360 : Int) atom0127Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68358420 : Int) atom0128Coded) (CoefficientMerge.scale (47944440 : Int) atom0129Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28341180 : Int) atom0130Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30612780 : Int) atom0131Coded) (CoefficientMerge.scale (12606300 : Int) atom0132Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47183040 : Int) atom0133Coded) (CoefficientMerge.scale (89196672 : Int) atom0134Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89320320 : Int) atom0135Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101049120 : Int) atom0136Coded) (CoefficientMerge.scale (74616660 : Int) atom0137Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52739640 : Int) atom0138Coded) (CoefficientMerge.scale (32741820 : Int) atom0139Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33815340 : Int) atom0140Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14610780 : Int) atom0141Coded) (CoefficientMerge.scale (54378240 : Int) atom0142Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (102218720 : Int) atom0143Coded) (CoefficientMerge.scale (106800960 : Int) atom0144Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80515680 : Int) atom0145Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57534840 : Int) atom0146Coded) (CoefficientMerge.scale (35679840 : Int) atom0147Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34919040 : Int) atom0148Coded) (CoefficientMerge.scale (13880160 : Int) atom0149Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60480000 : Int) atom0150Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114342840 : Int) atom0151Coded) (CoefficientMerge.scale (86347080 : Int) atom0152Coded))))))))) := by
  rw [block001_data_flat159_step, block001_data_flat158_original]
theorem block001_data : block001 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (4008960 : Int) atom0073Coded) (CoefficientMerge.scale (2108160 : Int) atom0074Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2816640 : Int) atom0075Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21556800 : Int) atom0076Coded) (CoefficientMerge.scale (21798720 : Int) atom0077Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (22040640 : Int) atom0078Coded) (CoefficientMerge.scale (22282560 : Int) atom0079Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22524480 : Int) atom0080Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22766400 : Int) atom0081Coded) (CoefficientMerge.scale (23878080 : Int) atom0082Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47524320 : Int) atom0083Coded) (CoefficientMerge.scale (19913040 : Int) atom0084Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8791200 : Int) atom0085Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4471920 : Int) atom0086Coded) (CoefficientMerge.scale (2792880 : Int) atom0087Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24606720 : Int) atom0088Coded) (CoefficientMerge.scale (51598080 : Int) atom0089Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53982720 : Int) atom0090Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56367360 : Int) atom0091Coded) (CoefficientMerge.scale (58752000 : Int) atom0092Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61136640 : Int) atom0093Coded) (CoefficientMerge.scale (63521280 : Int) atom0094Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80002080 : Int) atom0095Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48319200 : Int) atom0096Coded) (CoefficientMerge.scale (33558840 : Int) atom0097Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9119520 : Int) atom0098Coded) (CoefficientMerge.scale (10851840 : Int) atom0099Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25790400 : Int) atom0100Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53758080 : Int) atom0101Coded) (CoefficientMerge.scale (57335040 : Int) atom0102Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (60912000 : Int) atom0103Coded) (CoefficientMerge.scale (64601280 : Int) atom0104Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (68290560 : Int) atom0105Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (85263840 : Int) atom0106Coded) (CoefficientMerge.scale (54403380 : Int) atom0107Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (38354040 : Int) atom0108Coded) (CoefficientMerge.scale (15224220 : Int) atom0109Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18271980 : Int) atom0110Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1041660 : Int) atom0111Coded) (CoefficientMerge.scale (33416640 : Int) atom0112Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62148960 : Int) atom0113Coded) (CoefficientMerge.scale (66313440 : Int) atom0114Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (70477920 : Int) atom0115Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74642400 : Int) atom0116Coded) (CoefficientMerge.scale (90525600 : Int) atom0117Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (61395660 : Int) atom0118Coded) (CoefficientMerge.scale (43149240 : Int) atom0119Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22546980 : Int) atom0120Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25656660 : Int) atom0121Coded) (CoefficientMerge.scale (8488260 : Int) atom0122Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39827520 : Int) atom0123Coded) (CoefficientMerge.scale (74807712 : Int) atom0124Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (77670720 : Int) atom0125Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82012320 : Int) atom0126Coded) (CoefficientMerge.scale (95787360 : Int) atom0127Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68358420 : Int) atom0128Coded) (CoefficientMerge.scale (47944440 : Int) atom0129Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28341180 : Int) atom0130Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30612780 : Int) atom0131Coded) (CoefficientMerge.scale (12606300 : Int) atom0132Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (47183040 : Int) atom0133Coded) (CoefficientMerge.scale (89196672 : Int) atom0134Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (89320320 : Int) atom0135Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101049120 : Int) atom0136Coded) (CoefficientMerge.scale (74616660 : Int) atom0137Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52739640 : Int) atom0138Coded) (CoefficientMerge.scale (32741820 : Int) atom0139Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33815340 : Int) atom0140Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14610780 : Int) atom0141Coded) (CoefficientMerge.scale (54378240 : Int) atom0142Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (102218720 : Int) atom0143Coded) (CoefficientMerge.scale (106800960 : Int) atom0144Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80515680 : Int) atom0145Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57534840 : Int) atom0146Coded) (CoefficientMerge.scale (35679840 : Int) atom0147Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34919040 : Int) atom0148Coded) (CoefficientMerge.scale (13880160 : Int) atom0149Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60480000 : Int) atom0150Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114342840 : Int) atom0151Coded) (CoefficientMerge.scale (86347080 : Int) atom0152Coded)))))))) := by
  have h : block001 = block001_data_flat159 := by decide +kernel
  exact h.trans block001_data_flat159_original
theorem block001_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 15) block001 := by
  rw [block001_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0073Coded_nonneg g hg hA hB) (atom0074Coded_nonneg g hg hA hB)) (add_nonneg (atom0075Coded_nonneg g hg hA hB) (add_nonneg (atom0076Coded_nonneg g hg hA hB) (atom0077Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0078Coded_nonneg g hg hA hB) (atom0079Coded_nonneg g hg hA hB)) (add_nonneg (atom0080Coded_nonneg g hg hA hB) (add_nonneg (atom0081Coded_nonneg g hg hA hB) (atom0082Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0083Coded_nonneg g hg hA hB) (atom0084Coded_nonneg g hg hA hB)) (add_nonneg (atom0085Coded_nonneg g hg hA hB) (add_nonneg (atom0086Coded_nonneg g hg hA hB) (atom0087Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0088Coded_nonneg g hg hA hB) (atom0089Coded_nonneg g hg hA hB)) (add_nonneg (atom0090Coded_nonneg g hg hA hB) (add_nonneg (atom0091Coded_nonneg g hg hA hB) (atom0092Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0093Coded_nonneg g hg hA hB) (atom0094Coded_nonneg g hg hA hB)) (add_nonneg (atom0095Coded_nonneg g hg hA hB) (add_nonneg (atom0096Coded_nonneg g hg hA hB) (atom0097Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0098Coded_nonneg g hg hA hB) (atom0099Coded_nonneg g hg hA hB)) (add_nonneg (atom0100Coded_nonneg g hg hA hB) (add_nonneg (atom0101Coded_nonneg g hg hA hB) (atom0102Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0103Coded_nonneg g hg hA hB) (atom0104Coded_nonneg g hg hA hB)) (add_nonneg (atom0105Coded_nonneg g hg hA hB) (add_nonneg (atom0106Coded_nonneg g hg hA hB) (atom0107Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0108Coded_nonneg g hg hA hB) (atom0109Coded_nonneg g hg hA hB)) (add_nonneg (atom0110Coded_nonneg g hg hA hB) (add_nonneg (atom0111Coded_nonneg g hg hA hB) (atom0112Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0113Coded_nonneg g hg hA hB) (atom0114Coded_nonneg g hg hA hB)) (add_nonneg (atom0115Coded_nonneg g hg hA hB) (add_nonneg (atom0116Coded_nonneg g hg hA hB) (atom0117Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0118Coded_nonneg g hg hA hB) (atom0119Coded_nonneg g hg hA hB)) (add_nonneg (atom0120Coded_nonneg g hg hA hB) (add_nonneg (atom0121Coded_nonneg g hg hA hB) (atom0122Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0123Coded_nonneg g hg hA hB) (atom0124Coded_nonneg g hg hA hB)) (add_nonneg (atom0125Coded_nonneg g hg hA hB) (add_nonneg (atom0126Coded_nonneg g hg hA hB) (atom0127Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0128Coded_nonneg g hg hA hB) (atom0129Coded_nonneg g hg hA hB)) (add_nonneg (atom0130Coded_nonneg g hg hA hB) (add_nonneg (atom0131Coded_nonneg g hg hA hB) (atom0132Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0133Coded_nonneg g hg hA hB) (atom0134Coded_nonneg g hg hA hB)) (add_nonneg (atom0135Coded_nonneg g hg hA hB) (add_nonneg (atom0136Coded_nonneg g hg hA hB) (atom0137Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0138Coded_nonneg g hg hA hB) (atom0139Coded_nonneg g hg hA hB)) (add_nonneg (atom0140Coded_nonneg g hg hA hB) (add_nonneg (atom0141Coded_nonneg g hg hA hB) (atom0142Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0143Coded_nonneg g hg hA hB) (atom0144Coded_nonneg g hg hA hB)) (add_nonneg (atom0145Coded_nonneg g hg hA hB) (add_nonneg (atom0146Coded_nonneg g hg hA hB) (atom0147Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0148Coded_nonneg g hg hA hB) (atom0149Coded_nonneg g hg hA hB)) (add_nonneg (atom0150Coded_nonneg g hg hA hB) (add_nonneg (atom0151Coded_nonneg g hg hA hB) (atom0152Coded_nonneg g hg hA hB))))))))

end APPT.Finite15
