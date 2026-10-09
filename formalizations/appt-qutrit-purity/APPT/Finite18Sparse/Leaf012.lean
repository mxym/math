-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom0895 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0895 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0895 = ((g 6) * (g 16) * (g 16)) := by
  norm_num [atom0895, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0895_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (182136240 : Int) atom0895) := by
  rw [SparsePolynomial.eval_scale, eval_atom0895]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0895Coded : CoefficientMerge.Poly := [(nat_lit 2248, Int.ofNat (nat_lit 1))]
theorem atom0895Coded_decode : atom0895 = SparsePolynomial.decodeCubic 18 atom0895Coded := by decide +kernel
theorem atom0895Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (182136240 : Int) atom0895Coded) := by
  have h := atom0895_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0895Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0896 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0896 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0896 = ((g 6) * (g 16) * (g 17)) := by
  norm_num [atom0896, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0896_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5136502230 : Int) atom0896) := by
  rw [SparsePolynomial.eval_scale, eval_atom0896]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0896Coded : CoefficientMerge.Poly := [(nat_lit 2249, Int.ofNat (nat_lit 1))]
theorem atom0896Coded_decode : atom0896 = SparsePolynomial.decodeCubic 18 atom0896Coded := by decide +kernel
theorem atom0896Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5136502230 : Int) atom0896Coded) := by
  have h := atom0896_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0896Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0897 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0897 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0897 = ((g 6) * (g 17) * (g 17)) := by
  norm_num [atom0897, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0897_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4373859870 : Int) atom0897) := by
  rw [SparsePolynomial.eval_scale, eval_atom0897]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0897Coded : CoefficientMerge.Poly := [(nat_lit 2267, Int.ofNat (nat_lit 1))]
theorem atom0897Coded_decode : atom0897 = SparsePolynomial.decodeCubic 18 atom0897Coded := by decide +kernel
theorem atom0897Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4373859870 : Int) atom0897Coded) := by
  have h := atom0897_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0897Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0898 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0898 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0898 = ((g 7) * (g 7) * (g 7)) := by
  norm_num [atom0898, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0898_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (154863360 : Int) atom0898) := by
  rw [SparsePolynomial.eval_scale, eval_atom0898]
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 7) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0898Coded : CoefficientMerge.Poly := [(nat_lit 2401, Int.ofNat (nat_lit 1))]
theorem atom0898Coded_decode : atom0898 = SparsePolynomial.decodeCubic 18 atom0898Coded := by decide +kernel
theorem atom0898Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (154863360 : Int) atom0898Coded) := by
  have h := atom0898_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0898Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0899 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0899 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0899 = ((g 7) * (g 7) * (g 8)) := by
  norm_num [atom0899, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0899_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78704640 : Int) atom0899) := by
  rw [SparsePolynomial.eval_scale, eval_atom0899]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0899Coded : CoefficientMerge.Poly := [(nat_lit 2402, Int.ofNat (nat_lit 1))]
theorem atom0899Coded_decode : atom0899 = SparsePolynomial.decodeCubic 18 atom0899Coded := by decide +kernel
theorem atom0899Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (78704640 : Int) atom0899Coded) := by
  have h := atom0899_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0899Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0900 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0900 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0900 = ((g 7) * (g 7) * (g 12)) := by
  norm_num [atom0900, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0900_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (155020320 : Int) atom0900) := by
  rw [SparsePolynomial.eval_scale, eval_atom0900]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0900Coded : CoefficientMerge.Poly := [(nat_lit 2406, Int.ofNat (nat_lit 1))]
theorem atom0900Coded_decode : atom0900 = SparsePolynomial.decodeCubic 18 atom0900Coded := by decide +kernel
theorem atom0900Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (155020320 : Int) atom0900Coded) := by
  have h := atom0900_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0900Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0901 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0901 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0901 = ((g 7) * (g 8) * (g 8)) := by
  norm_num [atom0901, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0901_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (158595840 : Int) atom0901) := by
  rw [SparsePolynomial.eval_scale, eval_atom0901]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0901Coded : CoefficientMerge.Poly := [(nat_lit 2420, Int.ofNat (nat_lit 1))]
theorem atom0901Coded_decode : atom0901 = SparsePolynomial.decodeCubic 18 atom0901Coded := by decide +kernel
theorem atom0901Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (158595840 : Int) atom0901Coded) := by
  have h := atom0901_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0901Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0902 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0902 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0902 = ((g 7) * (g 8) * (g 10)) := by
  norm_num [atom0902, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0902_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103864320 : Int) atom0902) := by
  rw [SparsePolynomial.eval_scale, eval_atom0902]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0902Coded : CoefficientMerge.Poly := [(nat_lit 2422, Int.ofNat (nat_lit 1))]
theorem atom0902Coded_decode : atom0902 = SparsePolynomial.decodeCubic 18 atom0902Coded := by decide +kernel
theorem atom0902Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (103864320 : Int) atom0902Coded) := by
  have h := atom0902_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0902Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0903 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0903 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0903 = ((g 7) * (g 8) * (g 11)) := by
  norm_num [atom0903, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0903_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207728640 : Int) atom0903) := by
  rw [SparsePolynomial.eval_scale, eval_atom0903]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0903Coded : CoefficientMerge.Poly := [(nat_lit 2423, Int.ofNat (nat_lit 1))]
theorem atom0903Coded_decode : atom0903 = SparsePolynomial.decodeCubic 18 atom0903Coded := by decide +kernel
theorem atom0903Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (207728640 : Int) atom0903Coded) := by
  have h := atom0903_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0903Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0904 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0904 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0904 = ((g 7) * (g 8) * (g 12)) := by
  norm_num [atom0904, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0904_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (87669792 : Int) atom0904) := by
  rw [SparsePolynomial.eval_scale, eval_atom0904]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0904Coded : CoefficientMerge.Poly := [(nat_lit 2424, Int.ofNat (nat_lit 1))]
theorem atom0904Coded_decode : atom0904 = SparsePolynomial.decodeCubic 18 atom0904Coded := by decide +kernel
theorem atom0904Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (87669792 : Int) atom0904Coded) := by
  have h := atom0904_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0904Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0905 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0905 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0905 = ((g 7) * (g 8) * (g 15)) := by
  norm_num [atom0905, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0905_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1180247040 : Int) atom0905) := by
  rw [SparsePolynomial.eval_scale, eval_atom0905]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0905Coded : CoefficientMerge.Poly := [(nat_lit 2427, Int.ofNat (nat_lit 1))]
theorem atom0905Coded_decode : atom0905 = SparsePolynomial.decodeCubic 18 atom0905Coded := by decide +kernel
theorem atom0905Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1180247040 : Int) atom0905Coded) := by
  have h := atom0905_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0905Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0906 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0906 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0906 = ((g 7) * (g 8) * (g 16)) := by
  norm_num [atom0906, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0906_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2293143552 : Int) atom0906) := by
  rw [SparsePolynomial.eval_scale, eval_atom0906]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0906Coded : CoefficientMerge.Poly := [(nat_lit 2428, Int.ofNat (nat_lit 1))]
theorem atom0906Coded_decode : atom0906 = SparsePolynomial.decodeCubic 18 atom0906Coded := by decide +kernel
theorem atom0906Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2293143552 : Int) atom0906Coded) := by
  have h := atom0906_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0906Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0907 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0907 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0907 = ((g 7) * (g 8) * (g 17)) := by
  norm_num [atom0907, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0907_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3586383360 : Int) atom0907) := by
  rw [SparsePolynomial.eval_scale, eval_atom0907]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0907Coded : CoefficientMerge.Poly := [(nat_lit 2429, Int.ofNat (nat_lit 1))]
theorem atom0907Coded_decode : atom0907 = SparsePolynomial.decodeCubic 18 atom0907Coded := by decide +kernel
theorem atom0907Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3586383360 : Int) atom0907Coded) := by
  have h := atom0907_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0907Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0908 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0908 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0908 = ((g 7) * (g 9) * (g 9)) := by
  norm_num [atom0908, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0908_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (411045120 : Int) atom0908) := by
  rw [SparsePolynomial.eval_scale, eval_atom0908]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0908Coded : CoefficientMerge.Poly := [(nat_lit 2439, Int.ofNat (nat_lit 1))]
theorem atom0908Coded_decode : atom0908 = SparsePolynomial.decodeCubic 18 atom0908Coded := by decide +kernel
theorem atom0908Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (411045120 : Int) atom0908Coded) := by
  have h := atom0908_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0908Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0909 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0909 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0909 = ((g 7) * (g 9) * (g 10)) := by
  norm_num [atom0909, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0909_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (628784640 : Int) atom0909) := by
  rw [SparsePolynomial.eval_scale, eval_atom0909]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0909Coded : CoefficientMerge.Poly := [(nat_lit 2440, Int.ofNat (nat_lit 1))]
theorem atom0909Coded_decode : atom0909 = SparsePolynomial.decodeCubic 18 atom0909Coded := by decide +kernel
theorem atom0909Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (628784640 : Int) atom0909Coded) := by
  have h := atom0909_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0909Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0910 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0910 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0910 = ((g 7) * (g 9) * (g 11)) := by
  norm_num [atom0910, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0910_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (786193920 : Int) atom0910) := by
  rw [SparsePolynomial.eval_scale, eval_atom0910]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0910Coded : CoefficientMerge.Poly := [(nat_lit 2441, Int.ofNat (nat_lit 1))]
theorem atom0910Coded_decode : atom0910 = SparsePolynomial.decodeCubic 18 atom0910Coded := by decide +kernel
theorem atom0910Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (786193920 : Int) atom0910Coded) := by
  have h := atom0910_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0910Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0911 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0911 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0911 = ((g 7) * (g 9) * (g 12)) := by
  norm_num [atom0911, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0911_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (232689600 : Int) atom0911) := by
  rw [SparsePolynomial.eval_scale, eval_atom0911]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0911Coded : CoefficientMerge.Poly := [(nat_lit 2442, Int.ofNat (nat_lit 1))]
theorem atom0911Coded_decode : atom0911 = SparsePolynomial.decodeCubic 18 atom0911Coded := by decide +kernel
theorem atom0911Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (232689600 : Int) atom0911Coded) := by
  have h := atom0911_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0911Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0912 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0912 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0912 = ((g 7) * (g 9) * (g 13)) := by
  norm_num [atom0912, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0912_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13607520 : Int) atom0912) := by
  rw [SparsePolynomial.eval_scale, eval_atom0912]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0912Coded : CoefficientMerge.Poly := [(nat_lit 2443, Int.ofNat (nat_lit 1))]
theorem atom0912Coded_decode : atom0912 = SparsePolynomial.decodeCubic 18 atom0912Coded := by decide +kernel
theorem atom0912Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (13607520 : Int) atom0912Coded) := by
  have h := atom0912_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0912Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0913 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0913 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0913 = ((g 7) * (g 9) * (g 14)) := by
  norm_num [atom0913, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0913_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (701867040 : Int) atom0913) := by
  rw [SparsePolynomial.eval_scale, eval_atom0913]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0913Coded : CoefficientMerge.Poly := [(nat_lit 2444, Int.ofNat (nat_lit 1))]
theorem atom0913Coded_decode : atom0913 = SparsePolynomial.decodeCubic 18 atom0913Coded := by decide +kernel
theorem atom0913Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (701867040 : Int) atom0913Coded) := by
  have h := atom0913_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0913Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0914 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0914 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0914 = ((g 7) * (g 9) * (g 15)) := by
  norm_num [atom0914, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0914_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1929608160 : Int) atom0914) := by
  rw [SparsePolynomial.eval_scale, eval_atom0914]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0914Coded : CoefficientMerge.Poly := [(nat_lit 2445, Int.ofNat (nat_lit 1))]
theorem atom0914Coded_decode : atom0914 = SparsePolynomial.decodeCubic 18 atom0914Coded := by decide +kernel
theorem atom0914Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1929608160 : Int) atom0914Coded) := by
  have h := atom0914_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0914Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0915 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0915 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0915 = ((g 7) * (g 9) * (g 16)) := by
  norm_num [atom0915, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0915_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3909670560 : Int) atom0915) := by
  rw [SparsePolynomial.eval_scale, eval_atom0915]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0915Coded : CoefficientMerge.Poly := [(nat_lit 2446, Int.ofNat (nat_lit 1))]
theorem atom0915Coded_decode : atom0915 = SparsePolynomial.decodeCubic 18 atom0915Coded := by decide +kernel
theorem atom0915Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3909670560 : Int) atom0915Coded) := by
  have h := atom0915_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0915Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0916 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0916 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0916 = ((g 7) * (g 9) * (g 17)) := by
  norm_num [atom0916, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0916_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6267332160 : Int) atom0916) := by
  rw [SparsePolynomial.eval_scale, eval_atom0916]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0916Coded : CoefficientMerge.Poly := [(nat_lit 2447, Int.ofNat (nat_lit 1))]
theorem atom0916Coded_decode : atom0916 = SparsePolynomial.decodeCubic 18 atom0916Coded := by decide +kernel
theorem atom0916Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6267332160 : Int) atom0916Coded) := by
  have h := atom0916_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0916Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0917 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0917 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0917 = ((g 7) * (g 10) * (g 10)) := by
  norm_num [atom0917, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0917_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (891244800 : Int) atom0917) := by
  rw [SparsePolynomial.eval_scale, eval_atom0917]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0917Coded : CoefficientMerge.Poly := [(nat_lit 2458, Int.ofNat (nat_lit 1))]
theorem atom0917Coded_decode : atom0917 = SparsePolynomial.decodeCubic 18 atom0917Coded := by decide +kernel
theorem atom0917Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (891244800 : Int) atom0917Coded) := by
  have h := atom0917_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0917Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0918 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0918 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0918 = ((g 7) * (g 10) * (g 11)) := by
  norm_num [atom0918, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0918_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1609136640 : Int) atom0918) := by
  rw [SparsePolynomial.eval_scale, eval_atom0918]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0918Coded : CoefficientMerge.Poly := [(nat_lit 2459, Int.ofNat (nat_lit 1))]
theorem atom0918Coded_decode : atom0918 = SparsePolynomial.decodeCubic 18 atom0918Coded := by decide +kernel
theorem atom0918Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1609136640 : Int) atom0918Coded) := by
  have h := atom0918_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0918Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0919 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0919 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0919 = ((g 7) * (g 10) * (g 12)) := by
  norm_num [atom0919, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0919_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1344916800 : Int) atom0919) := by
  rw [SparsePolynomial.eval_scale, eval_atom0919]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0919Coded : CoefficientMerge.Poly := [(nat_lit 2460, Int.ofNat (nat_lit 1))]
theorem atom0919Coded_decode : atom0919 = SparsePolynomial.decodeCubic 18 atom0919Coded := by decide +kernel
theorem atom0919Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1344916800 : Int) atom0919Coded) := by
  have h := atom0919_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0919Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0920 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0920 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0920 = ((g 7) * (g 10) * (g 13)) := by
  norm_num [atom0920, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0920_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1404100320 : Int) atom0920) := by
  rw [SparsePolynomial.eval_scale, eval_atom0920]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0920Coded : CoefficientMerge.Poly := [(nat_lit 2461, Int.ofNat (nat_lit 1))]
theorem atom0920Coded_decode : atom0920 = SparsePolynomial.decodeCubic 18 atom0920Coded := by decide +kernel
theorem atom0920Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1404100320 : Int) atom0920Coded) := by
  have h := atom0920_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0920Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0921 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0921 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0921 = ((g 7) * (g 10) * (g 14)) := by
  norm_num [atom0921, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0921_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2940756000 : Int) atom0921) := by
  rw [SparsePolynomial.eval_scale, eval_atom0921]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0921Coded : CoefficientMerge.Poly := [(nat_lit 2462, Int.ofNat (nat_lit 1))]
theorem atom0921Coded_decode : atom0921 = SparsePolynomial.decodeCubic 18 atom0921Coded := by decide +kernel
theorem atom0921Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2940756000 : Int) atom0921Coded) := by
  have h := atom0921_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0921Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0922 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0922 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0922 = ((g 7) * (g 10) * (g 15)) := by
  norm_num [atom0922, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0922_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3706055520 : Int) atom0922) := by
  rw [SparsePolynomial.eval_scale, eval_atom0922]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0922Coded : CoefficientMerge.Poly := [(nat_lit 2463, Int.ofNat (nat_lit 1))]
theorem atom0922Coded_decode : atom0922 = SparsePolynomial.decodeCubic 18 atom0922Coded := by decide +kernel
theorem atom0922Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3706055520 : Int) atom0922Coded) := by
  have h := atom0922_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0922Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0923 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0923 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0923 = ((g 7) * (g 10) * (g 16)) := by
  norm_num [atom0923, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0923_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5793806880 : Int) atom0923) := by
  rw [SparsePolynomial.eval_scale, eval_atom0923]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0923Coded : CoefficientMerge.Poly := [(nat_lit 2464, Int.ofNat (nat_lit 1))]
theorem atom0923Coded_decode : atom0923 = SparsePolynomial.decodeCubic 18 atom0923Coded := by decide +kernel
theorem atom0923Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5793806880 : Int) atom0923Coded) := by
  have h := atom0923_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0923Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0924 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0924 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0924 = ((g 7) * (g 10) * (g 17)) := by
  norm_num [atom0924, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0924_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8475644160 : Int) atom0924) := by
  rw [SparsePolynomial.eval_scale, eval_atom0924]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0924Coded : CoefficientMerge.Poly := [(nat_lit 2465, Int.ofNat (nat_lit 1))]
theorem atom0924Coded_decode : atom0924 = SparsePolynomial.decodeCubic 18 atom0924Coded := by decide +kernel
theorem atom0924Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8475644160 : Int) atom0924Coded) := by
  have h := atom0924_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0924Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0925 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0925 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0925 = ((g 7) * (g 11) * (g 11)) := by
  norm_num [atom0925, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0925_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1725016320 : Int) atom0925) := by
  rw [SparsePolynomial.eval_scale, eval_atom0925]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0925Coded : CoefficientMerge.Poly := [(nat_lit 2477, Int.ofNat (nat_lit 1))]
theorem atom0925Coded_decode : atom0925 = SparsePolynomial.decodeCubic 18 atom0925Coded := by decide +kernel
theorem atom0925Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1725016320 : Int) atom0925Coded) := by
  have h := atom0925_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0925Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0926 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0926 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0926 = ((g 7) * (g 11) * (g 12)) := by
  norm_num [atom0926, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0926_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2334026880 : Int) atom0926) := by
  rw [SparsePolynomial.eval_scale, eval_atom0926]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0926Coded : CoefficientMerge.Poly := [(nat_lit 2478, Int.ofNat (nat_lit 1))]
theorem atom0926Coded_decode : atom0926 = SparsePolynomial.decodeCubic 18 atom0926Coded := by decide +kernel
theorem atom0926Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2334026880 : Int) atom0926Coded) := by
  have h := atom0926_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0926Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0927 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0927 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0927 = ((g 7) * (g 11) * (g 13)) := by
  norm_num [atom0927, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0927_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2590296480 : Int) atom0927) := by
  rw [SparsePolynomial.eval_scale, eval_atom0927]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0927Coded : CoefficientMerge.Poly := [(nat_lit 2479, Int.ofNat (nat_lit 1))]
theorem atom0927Coded_decode : atom0927 = SparsePolynomial.decodeCubic 18 atom0927Coded := by decide +kernel
theorem atom0927Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2590296480 : Int) atom0927Coded) := by
  have h := atom0927_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0927Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0928 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0928 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0928 = ((g 7) * (g 11) * (g 14)) := by
  norm_num [atom0928, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0928_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4993500960 : Int) atom0928) := by
  rw [SparsePolynomial.eval_scale, eval_atom0928]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0928Coded : CoefficientMerge.Poly := [(nat_lit 2480, Int.ofNat (nat_lit 1))]
theorem atom0928Coded_decode : atom0928 = SparsePolynomial.decodeCubic 18 atom0928Coded := by decide +kernel
theorem atom0928Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4993500960 : Int) atom0928Coded) := by
  have h := atom0928_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0928Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0929 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0929 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0929 = ((g 7) * (g 11) * (g 15)) := by
  norm_num [atom0929, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0929_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6174312480 : Int) atom0929) := by
  rw [SparsePolynomial.eval_scale, eval_atom0929]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0929Coded : CoefficientMerge.Poly := [(nat_lit 2481, Int.ofNat (nat_lit 1))]
theorem atom0929Coded_decode : atom0929 = SparsePolynomial.decodeCubic 18 atom0929Coded := by decide +kernel
theorem atom0929Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6174312480 : Int) atom0929Coded) := by
  have h := atom0929_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0929Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0930 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0930 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0930 = ((g 7) * (g 11) * (g 16)) := by
  norm_num [atom0930, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0930_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7280074080 : Int) atom0930) := by
  rw [SparsePolynomial.eval_scale, eval_atom0930]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0930Coded : CoefficientMerge.Poly := [(nat_lit 2482, Int.ofNat (nat_lit 1))]
theorem atom0930Coded_decode : atom0930 = SparsePolynomial.decodeCubic 18 atom0930Coded := by decide +kernel
theorem atom0930Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7280074080 : Int) atom0930Coded) := by
  have h := atom0930_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0930Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0931 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0931 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0931 = ((g 7) * (g 11) * (g 17)) := by
  norm_num [atom0931, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0931_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12177524160 : Int) atom0931) := by
  rw [SparsePolynomial.eval_scale, eval_atom0931]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0931Coded : CoefficientMerge.Poly := [(nat_lit 2483, Int.ofNat (nat_lit 1))]
theorem atom0931Coded_decode : atom0931 = SparsePolynomial.decodeCubic 18 atom0931Coded := by decide +kernel
theorem atom0931Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12177524160 : Int) atom0931Coded) := by
  have h := atom0931_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0931Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0932 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0932 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0932 = ((g 7) * (g 12) * (g 12)) := by
  norm_num [atom0932, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0932_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2643701760 : Int) atom0932) := by
  rw [SparsePolynomial.eval_scale, eval_atom0932]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0932Coded : CoefficientMerge.Poly := [(nat_lit 2496, Int.ofNat (nat_lit 1))]
theorem atom0932Coded_decode : atom0932 = SparsePolynomial.decodeCubic 18 atom0932Coded := by decide +kernel
theorem atom0932Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2643701760 : Int) atom0932Coded) := by
  have h := atom0932_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0932Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0933 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0933 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0933 = ((g 7) * (g 12) * (g 13)) := by
  norm_num [atom0933, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0933_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5717445840 : Int) atom0933) := by
  rw [SparsePolynomial.eval_scale, eval_atom0933]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0933Coded : CoefficientMerge.Poly := [(nat_lit 2497, Int.ofNat (nat_lit 1))]
theorem atom0933Coded_decode : atom0933 = SparsePolynomial.decodeCubic 18 atom0933Coded := by decide +kernel
theorem atom0933Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5717445840 : Int) atom0933Coded) := by
  have h := atom0933_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0933Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0934 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0934 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0934 = ((g 7) * (g 12) * (g 14)) := by
  norm_num [atom0934, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0934_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11409847200 : Int) atom0934) := by
  rw [SparsePolynomial.eval_scale, eval_atom0934]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0934Coded : CoefficientMerge.Poly := [(nat_lit 2498, Int.ofNat (nat_lit 1))]
theorem atom0934Coded_decode : atom0934 = SparsePolynomial.decodeCubic 18 atom0934Coded := by decide +kernel
theorem atom0934Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11409847200 : Int) atom0934Coded) := by
  have h := atom0934_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0934Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0935 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0935 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0935 = ((g 7) * (g 12) * (g 15)) := by
  norm_num [atom0935, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0935_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12355259760 : Int) atom0935) := by
  rw [SparsePolynomial.eval_scale, eval_atom0935]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0935Coded : CoefficientMerge.Poly := [(nat_lit 2499, Int.ofNat (nat_lit 1))]
theorem atom0935Coded_decode : atom0935 = SparsePolynomial.decodeCubic 18 atom0935Coded := by decide +kernel
theorem atom0935Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12355259760 : Int) atom0935Coded) := by
  have h := atom0935_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0935Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0936 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0936 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0936 = ((g 7) * (g 12) * (g 16)) := by
  norm_num [atom0936, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0936_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9602218800 : Int) atom0936) := by
  rw [SparsePolynomial.eval_scale, eval_atom0936]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0936Coded : CoefficientMerge.Poly := [(nat_lit 2500, Int.ofNat (nat_lit 1))]
theorem atom0936Coded_decode : atom0936 = SparsePolynomial.decodeCubic 18 atom0936Coded := by decide +kernel
theorem atom0936Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9602218800 : Int) atom0936Coded) := by
  have h := atom0936_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0936Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0937 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0937 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0937 = ((g 7) * (g 12) * (g 17)) := by
  norm_num [atom0937, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0937_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15732480240 : Int) atom0937) := by
  rw [SparsePolynomial.eval_scale, eval_atom0937]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0937Coded : CoefficientMerge.Poly := [(nat_lit 2501, Int.ofNat (nat_lit 1))]
theorem atom0937Coded_decode : atom0937 = SparsePolynomial.decodeCubic 18 atom0937Coded := by decide +kernel
theorem atom0937Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (15732480240 : Int) atom0937Coded) := by
  have h := atom0937_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0937Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0938 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0938 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0938 = ((g 7) * (g 13) * (g 13)) := by
  norm_num [atom0938, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0938_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2227212288 : Int) atom0938) := by
  rw [SparsePolynomial.eval_scale, eval_atom0938]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0938Coded : CoefficientMerge.Poly := [(nat_lit 2515, Int.ofNat (nat_lit 1))]
theorem atom0938Coded_decode : atom0938 = SparsePolynomial.decodeCubic 18 atom0938Coded := by decide +kernel
theorem atom0938Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2227212288 : Int) atom0938Coded) := by
  have h := atom0938_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0938Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0939 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0939 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0939 = ((g 7) * (g 13) * (g 14)) := by
  norm_num [atom0939, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0939_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9005351400 : Int) atom0939) := by
  rw [SparsePolynomial.eval_scale, eval_atom0939]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0939Coded : CoefficientMerge.Poly := [(nat_lit 2516, Int.ofNat (nat_lit 1))]
theorem atom0939Coded_decode : atom0939 = SparsePolynomial.decodeCubic 18 atom0939Coded := by decide +kernel
theorem atom0939Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (9005351400 : Int) atom0939Coded) := by
  have h := atom0939_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0939Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0940 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0940 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0940 = ((g 7) * (g 13) * (g 15)) := by
  norm_num [atom0940, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0940_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10554219720 : Int) atom0940) := by
  rw [SparsePolynomial.eval_scale, eval_atom0940]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0940Coded : CoefficientMerge.Poly := [(nat_lit 2517, Int.ofNat (nat_lit 1))]
theorem atom0940Coded_decode : atom0940 = SparsePolynomial.decodeCubic 18 atom0940Coded := by decide +kernel
theorem atom0940Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10554219720 : Int) atom0940Coded) := by
  have h := atom0940_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0940Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0941 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0941 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0941 = ((g 7) * (g 13) * (g 16)) := by
  norm_num [atom0941, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0941_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8388355680 : Int) atom0941) := by
  rw [SparsePolynomial.eval_scale, eval_atom0941]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0941Coded : CoefficientMerge.Poly := [(nat_lit 2518, Int.ofNat (nat_lit 1))]
theorem atom0941Coded_decode : atom0941 = SparsePolynomial.decodeCubic 18 atom0941Coded := by decide +kernel
theorem atom0941Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (8388355680 : Int) atom0941Coded) := by
  have h := atom0941_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0941Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0942 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0942 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0942 = ((g 7) * (g 13) * (g 17)) := by
  norm_num [atom0942, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0942_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11756106540 : Int) atom0942) := by
  rw [SparsePolynomial.eval_scale, eval_atom0942]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0942Coded : CoefficientMerge.Poly := [(nat_lit 2519, Int.ofNat (nat_lit 1))]
theorem atom0942Coded_decode : atom0942 = SparsePolynomial.decodeCubic 18 atom0942Coded := by decide +kernel
theorem atom0942Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11756106540 : Int) atom0942Coded) := by
  have h := atom0942_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0942Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0943 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0943 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0943 = ((g 7) * (g 14) * (g 14)) := by
  norm_num [atom0943, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0943_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7560675000 : Int) atom0943) := by
  rw [SparsePolynomial.eval_scale, eval_atom0943]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0943Coded : CoefficientMerge.Poly := [(nat_lit 2534, Int.ofNat (nat_lit 1))]
theorem atom0943Coded_decode : atom0943 = SparsePolynomial.decodeCubic 18 atom0943Coded := by decide +kernel
theorem atom0943Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7560675000 : Int) atom0943Coded) := by
  have h := atom0943_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0943Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0944 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0944 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0944 = ((g 7) * (g 14) * (g 15)) := by
  norm_num [atom0944, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0944_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12812030280 : Int) atom0944) := by
  rw [SparsePolynomial.eval_scale, eval_atom0944]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0944Coded : CoefficientMerge.Poly := [(nat_lit 2535, Int.ofNat (nat_lit 1))]
theorem atom0944Coded_decode : atom0944 = SparsePolynomial.decodeCubic 18 atom0944Coded := by decide +kernel
theorem atom0944Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (12812030280 : Int) atom0944Coded) := by
  have h := atom0944_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0944Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0945 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0945 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0945 = ((g 7) * (g 14) * (g 16)) := by
  norm_num [atom0945, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0945_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10325020320 : Int) atom0945) := by
  rw [SparsePolynomial.eval_scale, eval_atom0945]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0945Coded : CoefficientMerge.Poly := [(nat_lit 2536, Int.ofNat (nat_lit 1))]
theorem atom0945Coded_decode : atom0945 = SparsePolynomial.decodeCubic 18 atom0945Coded := by decide +kernel
theorem atom0945Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (10325020320 : Int) atom0945Coded) := by
  have h := atom0945_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0945Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0946 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0946 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0946 = ((g 7) * (g 14) * (g 17)) := by
  norm_num [atom0946, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0946_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14890848480 : Int) atom0946) := by
  rw [SparsePolynomial.eval_scale, eval_atom0946]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0946Coded : CoefficientMerge.Poly := [(nat_lit 2537, Int.ofNat (nat_lit 1))]
theorem atom0946Coded_decode : atom0946 = SparsePolynomial.decodeCubic 18 atom0946Coded := by decide +kernel
theorem atom0946Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (14890848480 : Int) atom0946Coded) := by
  have h := atom0946_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0946Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0947 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0947 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0947 = ((g 7) * (g 15) * (g 15)) := by
  norm_num [atom0947, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0947_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3863096280 : Int) atom0947) := by
  rw [SparsePolynomial.eval_scale, eval_atom0947]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0947Coded : CoefficientMerge.Poly := [(nat_lit 2553, Int.ofNat (nat_lit 1))]
theorem atom0947Coded_decode : atom0947 = SparsePolynomial.decodeCubic 18 atom0947Coded := by decide +kernel
theorem atom0947Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3863096280 : Int) atom0947Coded) := by
  have h := atom0947_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0947Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0948 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0948 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0948 = ((g 7) * (g 15) * (g 16)) := by
  norm_num [atom0948, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0948_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6214863960 : Int) atom0948) := by
  rw [SparsePolynomial.eval_scale, eval_atom0948]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0948Coded : CoefficientMerge.Poly := [(nat_lit 2554, Int.ofNat (nat_lit 1))]
theorem atom0948Coded_decode : atom0948 = SparsePolynomial.decodeCubic 18 atom0948Coded := by decide +kernel
theorem atom0948Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6214863960 : Int) atom0948Coded) := by
  have h := atom0948_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0948Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0949 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0949 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0949 = ((g 7) * (g 15) * (g 17)) := by
  norm_num [atom0949, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0949_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11200519260 : Int) atom0949) := by
  rw [SparsePolynomial.eval_scale, eval_atom0949]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0949Coded : CoefficientMerge.Poly := [(nat_lit 2555, Int.ofNat (nat_lit 1))]
theorem atom0949Coded_decode : atom0949 = SparsePolynomial.decodeCubic 18 atom0949Coded := by decide +kernel
theorem atom0949Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11200519260 : Int) atom0949Coded) := by
  have h := atom0949_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0949Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0950 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0950 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0950 = ((g 7) * (g 16) * (g 16)) := by
  norm_num [atom0950, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0950_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (928467360 : Int) atom0950) := by
  rw [SparsePolynomial.eval_scale, eval_atom0950]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0950Coded : CoefficientMerge.Poly := [(nat_lit 2572, Int.ofNat (nat_lit 1))]
theorem atom0950Coded_decode : atom0950 = SparsePolynomial.decodeCubic 18 atom0950Coded := by decide +kernel
theorem atom0950Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (928467360 : Int) atom0950Coded) := by
  have h := atom0950_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0950Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0951 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0951 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0951 = ((g 7) * (g 16) * (g 17)) := by
  norm_num [atom0951, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0951_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7244896500 : Int) atom0951) := by
  rw [SparsePolynomial.eval_scale, eval_atom0951]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0951Coded : CoefficientMerge.Poly := [(nat_lit 2573, Int.ofNat (nat_lit 1))]
theorem atom0951Coded_decode : atom0951 = SparsePolynomial.decodeCubic 18 atom0951Coded := by decide +kernel
theorem atom0951Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (7244896500 : Int) atom0951Coded) := by
  have h := atom0951_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0951Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0952 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0952 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0952 = ((g 7) * (g 17) * (g 17)) := by
  norm_num [atom0952, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0952_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5633486820 : Int) atom0952) := by
  rw [SparsePolynomial.eval_scale, eval_atom0952]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0952Coded : CoefficientMerge.Poly := [(nat_lit 2591, Int.ofNat (nat_lit 1))]
theorem atom0952Coded_decode : atom0952 = SparsePolynomial.decodeCubic 18 atom0952Coded := by decide +kernel
theorem atom0952Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (5633486820 : Int) atom0952Coded) := by
  have h := atom0952_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0952Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0953 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0953 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0953 = ((g 8) * (g 8) * (g 8)) := by
  norm_num [atom0953, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0953_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (114117120 : Int) atom0953) := by
  rw [SparsePolynomial.eval_scale, eval_atom0953]
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 8) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0953Coded : CoefficientMerge.Poly := [(nat_lit 2744, Int.ofNat (nat_lit 1))]
theorem atom0953Coded_decode : atom0953 = SparsePolynomial.decodeCubic 18 atom0953Coded := by decide +kernel
theorem atom0953Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (114117120 : Int) atom0953Coded) := by
  have h := atom0953_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0953Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0954 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0954 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0954 = ((g 8) * (g 9) * (g 9)) := by
  norm_num [atom0954, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0954_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (123425280 : Int) atom0954) := by
  rw [SparsePolynomial.eval_scale, eval_atom0954]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0954Coded : CoefficientMerge.Poly := [(nat_lit 2763, Int.ofNat (nat_lit 1))]
theorem atom0954Coded_decode : atom0954 = SparsePolynomial.decodeCubic 18 atom0954Coded := by decide +kernel
theorem atom0954Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (123425280 : Int) atom0954Coded) := by
  have h := atom0954_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0954Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0955 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0955 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0955 = ((g 8) * (g 9) * (g 11)) := by
  norm_num [atom0955, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0955_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (103864320 : Int) atom0955) := by
  rw [SparsePolynomial.eval_scale, eval_atom0955]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0955Coded : CoefficientMerge.Poly := [(nat_lit 2765, Int.ofNat (nat_lit 1))]
theorem atom0955Coded_decode : atom0955 = SparsePolynomial.decodeCubic 18 atom0955Coded := by decide +kernel
theorem atom0955Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (103864320 : Int) atom0955Coded) := by
  have h := atom0955_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0955Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0956 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0956 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0956 = ((g 8) * (g 9) * (g 13)) := by
  norm_num [atom0956, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0956_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (198804480 : Int) atom0956) := by
  rw [SparsePolynomial.eval_scale, eval_atom0956]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0956Coded : CoefficientMerge.Poly := [(nat_lit 2767, Int.ofNat (nat_lit 1))]
theorem atom0956Coded_decode : atom0956 = SparsePolynomial.decodeCubic 18 atom0956Coded := by decide +kernel
theorem atom0956Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (198804480 : Int) atom0956Coded) := by
  have h := atom0956_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0956Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0957 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0957 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0957 = ((g 8) * (g 9) * (g 14)) := by
  norm_num [atom0957, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0957_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (697544160 : Int) atom0957) := by
  rw [SparsePolynomial.eval_scale, eval_atom0957]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0957Coded : CoefficientMerge.Poly := [(nat_lit 2768, Int.ofNat (nat_lit 1))]
theorem atom0957Coded_decode : atom0957 = SparsePolynomial.decodeCubic 18 atom0957Coded := by decide +kernel
theorem atom0957Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (697544160 : Int) atom0957Coded) := by
  have h := atom0957_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0957Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0958 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0958 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0958 = ((g 8) * (g 9) * (g 15)) := by
  norm_num [atom0958, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0958_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1456949760 : Int) atom0958) := by
  rw [SparsePolynomial.eval_scale, eval_atom0958]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0958Coded : CoefficientMerge.Poly := [(nat_lit 2769, Int.ofNat (nat_lit 1))]
theorem atom0958Coded_decode : atom0958 = SparsePolynomial.decodeCubic 18 atom0958Coded := by decide +kernel
theorem atom0958Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1456949760 : Int) atom0958Coded) := by
  have h := atom0958_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0958Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0959 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0959 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0959 = ((g 8) * (g 9) * (g 16)) := by
  norm_num [atom0959, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0959_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2516290560 : Int) atom0959) := by
  rw [SparsePolynomial.eval_scale, eval_atom0959]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0959Coded : CoefficientMerge.Poly := [(nat_lit 2770, Int.ofNat (nat_lit 1))]
theorem atom0959Coded_decode : atom0959 = SparsePolynomial.decodeCubic 18 atom0959Coded := by decide +kernel
theorem atom0959Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (2516290560 : Int) atom0959Coded) := by
  have h := atom0959_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0959Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0960 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0960 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0960 = ((g 8) * (g 9) * (g 17)) := by
  norm_num [atom0960, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0960_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3703230720 : Int) atom0960) := by
  rw [SparsePolynomial.eval_scale, eval_atom0960]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0960Coded : CoefficientMerge.Poly := [(nat_lit 2771, Int.ofNat (nat_lit 1))]
theorem atom0960Coded_decode : atom0960 = SparsePolynomial.decodeCubic 18 atom0960Coded := by decide +kernel
theorem atom0960Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3703230720 : Int) atom0960Coded) := by
  have h := atom0960_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0960Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0961 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0961 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0961 = ((g 8) * (g 10) * (g 10)) := by
  norm_num [atom0961, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0961_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (446215680 : Int) atom0961) := by
  rw [SparsePolynomial.eval_scale, eval_atom0961]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0961Coded : CoefficientMerge.Poly := [(nat_lit 2782, Int.ofNat (nat_lit 1))]
theorem atom0961Coded_decode : atom0961 = SparsePolynomial.decodeCubic 18 atom0961Coded := by decide +kernel
theorem atom0961Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (446215680 : Int) atom0961Coded) := by
  have h := atom0961_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0961Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0962 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0962 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0962 = ((g 8) * (g 10) * (g 11)) := by
  norm_num [atom0962, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0962_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (715852800 : Int) atom0962) := by
  rw [SparsePolynomial.eval_scale, eval_atom0962]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0962Coded : CoefficientMerge.Poly := [(nat_lit 2783, Int.ofNat (nat_lit 1))]
theorem atom0962Coded_decode : atom0962 = SparsePolynomial.decodeCubic 18 atom0962Coded := by decide +kernel
theorem atom0962Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (715852800 : Int) atom0962Coded) := by
  have h := atom0962_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0962Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0963 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0963 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0963 = ((g 8) * (g 10) * (g 12)) := by
  norm_num [atom0963, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0963_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34334208 : Int) atom0963) := by
  rw [SparsePolynomial.eval_scale, eval_atom0963]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0963Coded : CoefficientMerge.Poly := [(nat_lit 2784, Int.ofNat (nat_lit 1))]
theorem atom0963Coded_decode : atom0963 = SparsePolynomial.decodeCubic 18 atom0963Coded := by decide +kernel
theorem atom0963Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (34334208 : Int) atom0963Coded) := by
  have h := atom0963_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0963Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0964 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0964 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0964 = ((g 8) * (g 10) * (g 14)) := by
  norm_num [atom0964, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0964_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1546800480 : Int) atom0964) := by
  rw [SparsePolynomial.eval_scale, eval_atom0964]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0964Coded : CoefficientMerge.Poly := [(nat_lit 2786, Int.ofNat (nat_lit 1))]
theorem atom0964Coded_decode : atom0964 = SparsePolynomial.decodeCubic 18 atom0964Coded := by decide +kernel
theorem atom0964Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1546800480 : Int) atom0964Coded) := by
  have h := atom0964_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0964Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0965 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0965 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0965 = ((g 8) * (g 10) * (g 15)) := by
  norm_num [atom0965, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0965_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1968756480 : Int) atom0965) := by
  rw [SparsePolynomial.eval_scale, eval_atom0965]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0965Coded : CoefficientMerge.Poly := [(nat_lit 2787, Int.ofNat (nat_lit 1))]
theorem atom0965Coded_decode : atom0965 = SparsePolynomial.decodeCubic 18 atom0965Coded := by decide +kernel
theorem atom0965Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1968756480 : Int) atom0965Coded) := by
  have h := atom0965_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0965Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0966 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0966 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0966 = ((g 8) * (g 10) * (g 16)) := by
  norm_num [atom0966, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0966_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3971847168 : Int) atom0966) := by
  rw [SparsePolynomial.eval_scale, eval_atom0966]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0966Coded : CoefficientMerge.Poly := [(nat_lit 2788, Int.ofNat (nat_lit 1))]
theorem atom0966Coded_decode : atom0966 = SparsePolynomial.decodeCubic 18 atom0966Coded := by decide +kernel
theorem atom0966Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3971847168 : Int) atom0966Coded) := by
  have h := atom0966_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0966Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0967 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0967 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0967 = ((g 8) * (g 10) * (g 17)) := by
  norm_num [atom0967, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0967_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6637222080 : Int) atom0967) := by
  rw [SparsePolynomial.eval_scale, eval_atom0967]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0967Coded : CoefficientMerge.Poly := [(nat_lit 2789, Int.ofNat (nat_lit 1))]
theorem atom0967Coded_decode : atom0967 = SparsePolynomial.decodeCubic 18 atom0967Coded := by decide +kernel
theorem atom0967Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6637222080 : Int) atom0967Coded) := by
  have h := atom0967_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0967Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0968 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0968 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0968 = ((g 8) * (g 11) * (g 11)) := by
  norm_num [atom0968, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0968_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1172897280 : Int) atom0968) := by
  rw [SparsePolynomial.eval_scale, eval_atom0968]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0968Coded : CoefficientMerge.Poly := [(nat_lit 2801, Int.ofNat (nat_lit 1))]
theorem atom0968Coded_decode : atom0968 = SparsePolynomial.decodeCubic 18 atom0968Coded := by decide +kernel
theorem atom0968Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1172897280 : Int) atom0968Coded) := by
  have h := atom0968_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0968Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0969 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0969 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0969 = ((g 8) * (g 11) * (g 12)) := by
  norm_num [atom0969, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0969_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (947796480 : Int) atom0969) := by
  rw [SparsePolynomial.eval_scale, eval_atom0969]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 8) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0969Coded : CoefficientMerge.Poly := [(nat_lit 2802, Int.ofNat (nat_lit 1))]
theorem atom0969Coded_decode : atom0969 = SparsePolynomial.decodeCubic 18 atom0969Coded := by decide +kernel
theorem atom0969Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (947796480 : Int) atom0969Coded) := by
  have h := atom0969_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0969Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0970 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0970 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0970 = ((g 8) * (g 11) * (g 13)) := by
  norm_num [atom0970, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0970_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1267307520 : Int) atom0970) := by
  rw [SparsePolynomial.eval_scale, eval_atom0970]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 8) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0970Coded : CoefficientMerge.Poly := [(nat_lit 2803, Int.ofNat (nat_lit 1))]
theorem atom0970Coded_decode : atom0970 = SparsePolynomial.decodeCubic 18 atom0970Coded := by decide +kernel
theorem atom0970Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (1267307520 : Int) atom0970Coded) := by
  have h := atom0970_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0970Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0971 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0971 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0971 = ((g 8) * (g 11) * (g 14)) := by
  norm_num [atom0971, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0971_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3880321440 : Int) atom0971) := by
  rw [SparsePolynomial.eval_scale, eval_atom0971]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 8) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0971Coded : CoefficientMerge.Poly := [(nat_lit 2804, Int.ofNat (nat_lit 1))]
theorem atom0971Coded_decode : atom0971 = SparsePolynomial.decodeCubic 18 atom0971Coded := by decide +kernel
theorem atom0971Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (3880321440 : Int) atom0971Coded) := by
  have h := atom0971_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0971Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0972 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0972 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0972 = ((g 8) * (g 11) * (g 15)) := by
  norm_num [atom0972, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0972_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4842781440 : Int) atom0972) := by
  rw [SparsePolynomial.eval_scale, eval_atom0972]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 8) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0972Coded : CoefficientMerge.Poly := [(nat_lit 2805, Int.ofNat (nat_lit 1))]
theorem atom0972Coded_decode : atom0972 = SparsePolynomial.decodeCubic 18 atom0972Coded := by decide +kernel
theorem atom0972Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (4842781440 : Int) atom0972Coded) := by
  have h := atom0972_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0972Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0973 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0973 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0973 = ((g 8) * (g 11) * (g 16)) := by
  norm_num [atom0973, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0973_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6031779840 : Int) atom0973) := by
  rw [SparsePolynomial.eval_scale, eval_atom0973]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 8) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0973Coded : CoefficientMerge.Poly := [(nat_lit 2806, Int.ofNat (nat_lit 1))]
theorem atom0973Coded_decode : atom0973 = SparsePolynomial.decodeCubic 18 atom0973Coded := by decide +kernel
theorem atom0973Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (6031779840 : Int) atom0973Coded) := by
  have h := atom0973_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0973Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0974 : SparsePolynomial.Poly := [([nat_lit 8, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0974 (g : Fin 18 → ℝ) : SparsePolynomial.eval (gapValues g) atom0974 = ((g 8) * (g 11) * (g 17)) := by
  norm_num [atom0974, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0974_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11064781440 : Int) atom0974) := by
  rw [SparsePolynomial.eval_scale, eval_atom0974]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 8) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0974Coded : CoefficientMerge.Poly := [(nat_lit 2807, Int.ofNat (nat_lit 1))]
theorem atom0974Coded_decode : atom0974 = SparsePolynomial.decodeCubic 18 atom0974Coded := by decide +kernel
theorem atom0974Coded_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) (CoefficientMerge.scale (11064781440 : Int) atom0974Coded) := by
  have h := atom0974_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0974Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block012 : CoefficientMerge.Poly := [(nat_lit 2248, Int.ofNat (nat_lit 182136240)), (nat_lit 2249, Int.ofNat (nat_lit 5136502230)), (nat_lit 2267, Int.ofNat (nat_lit 4373859870)), (nat_lit 2401, Int.ofNat (nat_lit 154863360)), (nat_lit 2402, Int.ofNat (nat_lit 78704640)), (nat_lit 2406, Int.ofNat (nat_lit 155020320)), (nat_lit 2420, Int.ofNat (nat_lit 158595840)), (nat_lit 2422, Int.ofNat (nat_lit 103864320)), (nat_lit 2423, Int.ofNat (nat_lit 207728640)), (nat_lit 2424, Int.ofNat (nat_lit 87669792)), (nat_lit 2427, Int.ofNat (nat_lit 1180247040)), (nat_lit 2428, Int.ofNat (nat_lit 2293143552)), (nat_lit 2429, Int.ofNat (nat_lit 3586383360)), (nat_lit 2439, Int.ofNat (nat_lit 411045120)), (nat_lit 2440, Int.ofNat (nat_lit 628784640)), (nat_lit 2441, Int.ofNat (nat_lit 786193920)), (nat_lit 2442, Int.ofNat (nat_lit 232689600)), (nat_lit 2443, Int.ofNat (nat_lit 13607520)), (nat_lit 2444, Int.ofNat (nat_lit 701867040)), (nat_lit 2445, Int.ofNat (nat_lit 1929608160)), (nat_lit 2446, Int.ofNat (nat_lit 3909670560)), (nat_lit 2447, Int.ofNat (nat_lit 6267332160)), (nat_lit 2458, Int.ofNat (nat_lit 891244800)), (nat_lit 2459, Int.ofNat (nat_lit 1609136640)), (nat_lit 2460, Int.ofNat (nat_lit 1344916800)), (nat_lit 2461, Int.ofNat (nat_lit 1404100320)), (nat_lit 2462, Int.ofNat (nat_lit 2940756000)), (nat_lit 2463, Int.ofNat (nat_lit 3706055520)), (nat_lit 2464, Int.ofNat (nat_lit 5793806880)), (nat_lit 2465, Int.ofNat (nat_lit 8475644160)), (nat_lit 2477, Int.ofNat (nat_lit 1725016320)), (nat_lit 2478, Int.ofNat (nat_lit 2334026880)), (nat_lit 2479, Int.ofNat (nat_lit 2590296480)), (nat_lit 2480, Int.ofNat (nat_lit 4993500960)), (nat_lit 2481, Int.ofNat (nat_lit 6174312480)), (nat_lit 2482, Int.ofNat (nat_lit 7280074080)), (nat_lit 2483, Int.ofNat (nat_lit 12177524160)), (nat_lit 2496, Int.ofNat (nat_lit 2643701760)), (nat_lit 2497, Int.ofNat (nat_lit 5717445840)), (nat_lit 2498, Int.ofNat (nat_lit 11409847200)), (nat_lit 2499, Int.ofNat (nat_lit 12355259760)), (nat_lit 2500, Int.ofNat (nat_lit 9602218800)), (nat_lit 2501, Int.ofNat (nat_lit 15732480240)), (nat_lit 2515, Int.ofNat (nat_lit 2227212288)), (nat_lit 2516, Int.ofNat (nat_lit 9005351400)), (nat_lit 2517, Int.ofNat (nat_lit 10554219720)), (nat_lit 2518, Int.ofNat (nat_lit 8388355680)), (nat_lit 2519, Int.ofNat (nat_lit 11756106540)), (nat_lit 2534, Int.ofNat (nat_lit 7560675000)), (nat_lit 2535, Int.ofNat (nat_lit 12812030280)), (nat_lit 2536, Int.ofNat (nat_lit 10325020320)), (nat_lit 2537, Int.ofNat (nat_lit 14890848480)), (nat_lit 2553, Int.ofNat (nat_lit 3863096280)), (nat_lit 2554, Int.ofNat (nat_lit 6214863960)), (nat_lit 2555, Int.ofNat (nat_lit 11200519260)), (nat_lit 2572, Int.ofNat (nat_lit 928467360)), (nat_lit 2573, Int.ofNat (nat_lit 7244896500)), (nat_lit 2591, Int.ofNat (nat_lit 5633486820)), (nat_lit 2744, Int.ofNat (nat_lit 114117120)), (nat_lit 2763, Int.ofNat (nat_lit 123425280)), (nat_lit 2765, Int.ofNat (nat_lit 103864320)), (nat_lit 2767, Int.ofNat (nat_lit 198804480)), (nat_lit 2768, Int.ofNat (nat_lit 697544160)), (nat_lit 2769, Int.ofNat (nat_lit 1456949760)), (nat_lit 2770, Int.ofNat (nat_lit 2516290560)), (nat_lit 2771, Int.ofNat (nat_lit 3703230720)), (nat_lit 2782, Int.ofNat (nat_lit 446215680)), (nat_lit 2783, Int.ofNat (nat_lit 715852800)), (nat_lit 2784, Int.ofNat (nat_lit 34334208)), (nat_lit 2786, Int.ofNat (nat_lit 1546800480)), (nat_lit 2787, Int.ofNat (nat_lit 1968756480)), (nat_lit 2788, Int.ofNat (nat_lit 3971847168)), (nat_lit 2789, Int.ofNat (nat_lit 6637222080)), (nat_lit 2801, Int.ofNat (nat_lit 1172897280)), (nat_lit 2802, Int.ofNat (nat_lit 947796480)), (nat_lit 2803, Int.ofNat (nat_lit 1267307520)), (nat_lit 2804, Int.ofNat (nat_lit 3880321440)), (nat_lit 2805, Int.ofNat (nat_lit 4842781440)), (nat_lit 2806, Int.ofNat (nat_lit 6031779840)), (nat_lit 2807, Int.ofNat (nat_lit 11064781440))]
def block012_data_flat000 : CoefficientMerge.Poly := [(nat_lit 2248, Int.ofNat (nat_lit 182136240))]
theorem block012_data_flat000_step : block012_data_flat000 = (CoefficientMerge.scale (182136240 : Int) atom0895Coded) := by decide +kernel
theorem block012_data_flat000_original : block012_data_flat000 = (CoefficientMerge.scale (182136240 : Int) atom0895Coded) := by
  rw [block012_data_flat000_step]
def block012_data_flat001 : CoefficientMerge.Poly := [(nat_lit 2249, Int.ofNat (nat_lit 5136502230))]
theorem block012_data_flat001_step : block012_data_flat001 = (CoefficientMerge.scale (5136502230 : Int) atom0896Coded) := by decide +kernel
theorem block012_data_flat001_original : block012_data_flat001 = (CoefficientMerge.scale (5136502230 : Int) atom0896Coded) := by
  rw [block012_data_flat001_step]
def block012_data_flat002 : CoefficientMerge.Poly := [(nat_lit 2248, Int.ofNat (nat_lit 182136240)), (nat_lit 2249, Int.ofNat (nat_lit 5136502230))]
theorem block012_data_flat002_step : block012_data_flat002 = (CoefficientMerge.fastMerge block012_data_flat000 block012_data_flat001) := by decide +kernel
theorem block012_data_flat002_original : block012_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (182136240 : Int) atom0895Coded) (CoefficientMerge.scale (5136502230 : Int) atom0896Coded)) := by
  rw [block012_data_flat002_step, block012_data_flat000_original, block012_data_flat001_original]
def block012_data_flat003 : CoefficientMerge.Poly := [(nat_lit 2267, Int.ofNat (nat_lit 4373859870))]
theorem block012_data_flat003_step : block012_data_flat003 = (CoefficientMerge.scale (4373859870 : Int) atom0897Coded) := by decide +kernel
theorem block012_data_flat003_original : block012_data_flat003 = (CoefficientMerge.scale (4373859870 : Int) atom0897Coded) := by
  rw [block012_data_flat003_step]
def block012_data_flat004 : CoefficientMerge.Poly := [(nat_lit 2401, Int.ofNat (nat_lit 154863360))]
theorem block012_data_flat004_step : block012_data_flat004 = (CoefficientMerge.scale (154863360 : Int) atom0898Coded) := by decide +kernel
theorem block012_data_flat004_original : block012_data_flat004 = (CoefficientMerge.scale (154863360 : Int) atom0898Coded) := by
  rw [block012_data_flat004_step]
def block012_data_flat005 : CoefficientMerge.Poly := [(nat_lit 2402, Int.ofNat (nat_lit 78704640))]
theorem block012_data_flat005_step : block012_data_flat005 = (CoefficientMerge.scale (78704640 : Int) atom0899Coded) := by decide +kernel
theorem block012_data_flat005_original : block012_data_flat005 = (CoefficientMerge.scale (78704640 : Int) atom0899Coded) := by
  rw [block012_data_flat005_step]
def block012_data_flat006 : CoefficientMerge.Poly := [(nat_lit 2401, Int.ofNat (nat_lit 154863360)), (nat_lit 2402, Int.ofNat (nat_lit 78704640))]
theorem block012_data_flat006_step : block012_data_flat006 = (CoefficientMerge.fastMerge block012_data_flat004 block012_data_flat005) := by decide +kernel
theorem block012_data_flat006_original : block012_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (154863360 : Int) atom0898Coded) (CoefficientMerge.scale (78704640 : Int) atom0899Coded)) := by
  rw [block012_data_flat006_step, block012_data_flat004_original, block012_data_flat005_original]
def block012_data_flat007 : CoefficientMerge.Poly := [(nat_lit 2267, Int.ofNat (nat_lit 4373859870)), (nat_lit 2401, Int.ofNat (nat_lit 154863360)), (nat_lit 2402, Int.ofNat (nat_lit 78704640))]
theorem block012_data_flat007_step : block012_data_flat007 = (CoefficientMerge.fastMerge block012_data_flat003 block012_data_flat006) := by decide +kernel
theorem block012_data_flat007_original : block012_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4373859870 : Int) atom0897Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154863360 : Int) atom0898Coded) (CoefficientMerge.scale (78704640 : Int) atom0899Coded))) := by
  rw [block012_data_flat007_step, block012_data_flat003_original, block012_data_flat006_original]
def block012_data_flat008 : CoefficientMerge.Poly := [(nat_lit 2248, Int.ofNat (nat_lit 182136240)), (nat_lit 2249, Int.ofNat (nat_lit 5136502230)), (nat_lit 2267, Int.ofNat (nat_lit 4373859870)), (nat_lit 2401, Int.ofNat (nat_lit 154863360)), (nat_lit 2402, Int.ofNat (nat_lit 78704640))]
theorem block012_data_flat008_step : block012_data_flat008 = (CoefficientMerge.fastMerge block012_data_flat002 block012_data_flat007) := by decide +kernel
theorem block012_data_flat008_original : block012_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182136240 : Int) atom0895Coded) (CoefficientMerge.scale (5136502230 : Int) atom0896Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4373859870 : Int) atom0897Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154863360 : Int) atom0898Coded) (CoefficientMerge.scale (78704640 : Int) atom0899Coded)))) := by
  rw [block012_data_flat008_step, block012_data_flat002_original, block012_data_flat007_original]
def block012_data_flat009 : CoefficientMerge.Poly := [(nat_lit 2406, Int.ofNat (nat_lit 155020320))]
theorem block012_data_flat009_step : block012_data_flat009 = (CoefficientMerge.scale (155020320 : Int) atom0900Coded) := by decide +kernel
theorem block012_data_flat009_original : block012_data_flat009 = (CoefficientMerge.scale (155020320 : Int) atom0900Coded) := by
  rw [block012_data_flat009_step]
def block012_data_flat010 : CoefficientMerge.Poly := [(nat_lit 2420, Int.ofNat (nat_lit 158595840))]
theorem block012_data_flat010_step : block012_data_flat010 = (CoefficientMerge.scale (158595840 : Int) atom0901Coded) := by decide +kernel
theorem block012_data_flat010_original : block012_data_flat010 = (CoefficientMerge.scale (158595840 : Int) atom0901Coded) := by
  rw [block012_data_flat010_step]
def block012_data_flat011 : CoefficientMerge.Poly := [(nat_lit 2406, Int.ofNat (nat_lit 155020320)), (nat_lit 2420, Int.ofNat (nat_lit 158595840))]
theorem block012_data_flat011_step : block012_data_flat011 = (CoefficientMerge.fastMerge block012_data_flat009 block012_data_flat010) := by decide +kernel
theorem block012_data_flat011_original : block012_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (155020320 : Int) atom0900Coded) (CoefficientMerge.scale (158595840 : Int) atom0901Coded)) := by
  rw [block012_data_flat011_step, block012_data_flat009_original, block012_data_flat010_original]
def block012_data_flat012 : CoefficientMerge.Poly := [(nat_lit 2422, Int.ofNat (nat_lit 103864320))]
theorem block012_data_flat012_step : block012_data_flat012 = (CoefficientMerge.scale (103864320 : Int) atom0902Coded) := by decide +kernel
theorem block012_data_flat012_original : block012_data_flat012 = (CoefficientMerge.scale (103864320 : Int) atom0902Coded) := by
  rw [block012_data_flat012_step]
def block012_data_flat013 : CoefficientMerge.Poly := [(nat_lit 2423, Int.ofNat (nat_lit 207728640))]
theorem block012_data_flat013_step : block012_data_flat013 = (CoefficientMerge.scale (207728640 : Int) atom0903Coded) := by decide +kernel
theorem block012_data_flat013_original : block012_data_flat013 = (CoefficientMerge.scale (207728640 : Int) atom0903Coded) := by
  rw [block012_data_flat013_step]
def block012_data_flat014 : CoefficientMerge.Poly := [(nat_lit 2424, Int.ofNat (nat_lit 87669792))]
theorem block012_data_flat014_step : block012_data_flat014 = (CoefficientMerge.scale (87669792 : Int) atom0904Coded) := by decide +kernel
theorem block012_data_flat014_original : block012_data_flat014 = (CoefficientMerge.scale (87669792 : Int) atom0904Coded) := by
  rw [block012_data_flat014_step]
def block012_data_flat015 : CoefficientMerge.Poly := [(nat_lit 2423, Int.ofNat (nat_lit 207728640)), (nat_lit 2424, Int.ofNat (nat_lit 87669792))]
theorem block012_data_flat015_step : block012_data_flat015 = (CoefficientMerge.fastMerge block012_data_flat013 block012_data_flat014) := by decide +kernel
theorem block012_data_flat015_original : block012_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0903Coded) (CoefficientMerge.scale (87669792 : Int) atom0904Coded)) := by
  rw [block012_data_flat015_step, block012_data_flat013_original, block012_data_flat014_original]
def block012_data_flat016 : CoefficientMerge.Poly := [(nat_lit 2422, Int.ofNat (nat_lit 103864320)), (nat_lit 2423, Int.ofNat (nat_lit 207728640)), (nat_lit 2424, Int.ofNat (nat_lit 87669792))]
theorem block012_data_flat016_step : block012_data_flat016 = (CoefficientMerge.fastMerge block012_data_flat012 block012_data_flat015) := by decide +kernel
theorem block012_data_flat016_original : block012_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0902Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0903Coded) (CoefficientMerge.scale (87669792 : Int) atom0904Coded))) := by
  rw [block012_data_flat016_step, block012_data_flat012_original, block012_data_flat015_original]
def block012_data_flat017 : CoefficientMerge.Poly := [(nat_lit 2406, Int.ofNat (nat_lit 155020320)), (nat_lit 2420, Int.ofNat (nat_lit 158595840)), (nat_lit 2422, Int.ofNat (nat_lit 103864320)), (nat_lit 2423, Int.ofNat (nat_lit 207728640)), (nat_lit 2424, Int.ofNat (nat_lit 87669792))]
theorem block012_data_flat017_step : block012_data_flat017 = (CoefficientMerge.fastMerge block012_data_flat011 block012_data_flat016) := by decide +kernel
theorem block012_data_flat017_original : block012_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (155020320 : Int) atom0900Coded) (CoefficientMerge.scale (158595840 : Int) atom0901Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0902Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0903Coded) (CoefficientMerge.scale (87669792 : Int) atom0904Coded)))) := by
  rw [block012_data_flat017_step, block012_data_flat011_original, block012_data_flat016_original]
def block012_data_flat018 : CoefficientMerge.Poly := [(nat_lit 2248, Int.ofNat (nat_lit 182136240)), (nat_lit 2249, Int.ofNat (nat_lit 5136502230)), (nat_lit 2267, Int.ofNat (nat_lit 4373859870)), (nat_lit 2401, Int.ofNat (nat_lit 154863360)), (nat_lit 2402, Int.ofNat (nat_lit 78704640)), (nat_lit 2406, Int.ofNat (nat_lit 155020320)), (nat_lit 2420, Int.ofNat (nat_lit 158595840)), (nat_lit 2422, Int.ofNat (nat_lit 103864320)), (nat_lit 2423, Int.ofNat (nat_lit 207728640)), (nat_lit 2424, Int.ofNat (nat_lit 87669792))]
theorem block012_data_flat018_step : block012_data_flat018 = (CoefficientMerge.fastMerge block012_data_flat008 block012_data_flat017) := by decide +kernel
theorem block012_data_flat018_original : block012_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182136240 : Int) atom0895Coded) (CoefficientMerge.scale (5136502230 : Int) atom0896Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4373859870 : Int) atom0897Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154863360 : Int) atom0898Coded) (CoefficientMerge.scale (78704640 : Int) atom0899Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (155020320 : Int) atom0900Coded) (CoefficientMerge.scale (158595840 : Int) atom0901Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0902Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0903Coded) (CoefficientMerge.scale (87669792 : Int) atom0904Coded))))) := by
  rw [block012_data_flat018_step, block012_data_flat008_original, block012_data_flat017_original]
def block012_data_flat019 : CoefficientMerge.Poly := [(nat_lit 2427, Int.ofNat (nat_lit 1180247040))]
theorem block012_data_flat019_step : block012_data_flat019 = (CoefficientMerge.scale (1180247040 : Int) atom0905Coded) := by decide +kernel
theorem block012_data_flat019_original : block012_data_flat019 = (CoefficientMerge.scale (1180247040 : Int) atom0905Coded) := by
  rw [block012_data_flat019_step]
def block012_data_flat020 : CoefficientMerge.Poly := [(nat_lit 2428, Int.ofNat (nat_lit 2293143552))]
theorem block012_data_flat020_step : block012_data_flat020 = (CoefficientMerge.scale (2293143552 : Int) atom0906Coded) := by decide +kernel
theorem block012_data_flat020_original : block012_data_flat020 = (CoefficientMerge.scale (2293143552 : Int) atom0906Coded) := by
  rw [block012_data_flat020_step]
def block012_data_flat021 : CoefficientMerge.Poly := [(nat_lit 2427, Int.ofNat (nat_lit 1180247040)), (nat_lit 2428, Int.ofNat (nat_lit 2293143552))]
theorem block012_data_flat021_step : block012_data_flat021 = (CoefficientMerge.fastMerge block012_data_flat019 block012_data_flat020) := by decide +kernel
theorem block012_data_flat021_original : block012_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0905Coded) (CoefficientMerge.scale (2293143552 : Int) atom0906Coded)) := by
  rw [block012_data_flat021_step, block012_data_flat019_original, block012_data_flat020_original]
def block012_data_flat022 : CoefficientMerge.Poly := [(nat_lit 2429, Int.ofNat (nat_lit 3586383360))]
theorem block012_data_flat022_step : block012_data_flat022 = (CoefficientMerge.scale (3586383360 : Int) atom0907Coded) := by decide +kernel
theorem block012_data_flat022_original : block012_data_flat022 = (CoefficientMerge.scale (3586383360 : Int) atom0907Coded) := by
  rw [block012_data_flat022_step]
def block012_data_flat023 : CoefficientMerge.Poly := [(nat_lit 2439, Int.ofNat (nat_lit 411045120))]
theorem block012_data_flat023_step : block012_data_flat023 = (CoefficientMerge.scale (411045120 : Int) atom0908Coded) := by decide +kernel
theorem block012_data_flat023_original : block012_data_flat023 = (CoefficientMerge.scale (411045120 : Int) atom0908Coded) := by
  rw [block012_data_flat023_step]
def block012_data_flat024 : CoefficientMerge.Poly := [(nat_lit 2440, Int.ofNat (nat_lit 628784640))]
theorem block012_data_flat024_step : block012_data_flat024 = (CoefficientMerge.scale (628784640 : Int) atom0909Coded) := by decide +kernel
theorem block012_data_flat024_original : block012_data_flat024 = (CoefficientMerge.scale (628784640 : Int) atom0909Coded) := by
  rw [block012_data_flat024_step]
def block012_data_flat025 : CoefficientMerge.Poly := [(nat_lit 2439, Int.ofNat (nat_lit 411045120)), (nat_lit 2440, Int.ofNat (nat_lit 628784640))]
theorem block012_data_flat025_step : block012_data_flat025 = (CoefficientMerge.fastMerge block012_data_flat023 block012_data_flat024) := by decide +kernel
theorem block012_data_flat025_original : block012_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (411045120 : Int) atom0908Coded) (CoefficientMerge.scale (628784640 : Int) atom0909Coded)) := by
  rw [block012_data_flat025_step, block012_data_flat023_original, block012_data_flat024_original]
def block012_data_flat026 : CoefficientMerge.Poly := [(nat_lit 2429, Int.ofNat (nat_lit 3586383360)), (nat_lit 2439, Int.ofNat (nat_lit 411045120)), (nat_lit 2440, Int.ofNat (nat_lit 628784640))]
theorem block012_data_flat026_step : block012_data_flat026 = (CoefficientMerge.fastMerge block012_data_flat022 block012_data_flat025) := by decide +kernel
theorem block012_data_flat026_original : block012_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0907Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411045120 : Int) atom0908Coded) (CoefficientMerge.scale (628784640 : Int) atom0909Coded))) := by
  rw [block012_data_flat026_step, block012_data_flat022_original, block012_data_flat025_original]
def block012_data_flat027 : CoefficientMerge.Poly := [(nat_lit 2427, Int.ofNat (nat_lit 1180247040)), (nat_lit 2428, Int.ofNat (nat_lit 2293143552)), (nat_lit 2429, Int.ofNat (nat_lit 3586383360)), (nat_lit 2439, Int.ofNat (nat_lit 411045120)), (nat_lit 2440, Int.ofNat (nat_lit 628784640))]
theorem block012_data_flat027_step : block012_data_flat027 = (CoefficientMerge.fastMerge block012_data_flat021 block012_data_flat026) := by decide +kernel
theorem block012_data_flat027_original : block012_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0905Coded) (CoefficientMerge.scale (2293143552 : Int) atom0906Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0907Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411045120 : Int) atom0908Coded) (CoefficientMerge.scale (628784640 : Int) atom0909Coded)))) := by
  rw [block012_data_flat027_step, block012_data_flat021_original, block012_data_flat026_original]
def block012_data_flat028 : CoefficientMerge.Poly := [(nat_lit 2441, Int.ofNat (nat_lit 786193920))]
theorem block012_data_flat028_step : block012_data_flat028 = (CoefficientMerge.scale (786193920 : Int) atom0910Coded) := by decide +kernel
theorem block012_data_flat028_original : block012_data_flat028 = (CoefficientMerge.scale (786193920 : Int) atom0910Coded) := by
  rw [block012_data_flat028_step]
def block012_data_flat029 : CoefficientMerge.Poly := [(nat_lit 2442, Int.ofNat (nat_lit 232689600))]
theorem block012_data_flat029_step : block012_data_flat029 = (CoefficientMerge.scale (232689600 : Int) atom0911Coded) := by decide +kernel
theorem block012_data_flat029_original : block012_data_flat029 = (CoefficientMerge.scale (232689600 : Int) atom0911Coded) := by
  rw [block012_data_flat029_step]
def block012_data_flat030 : CoefficientMerge.Poly := [(nat_lit 2441, Int.ofNat (nat_lit 786193920)), (nat_lit 2442, Int.ofNat (nat_lit 232689600))]
theorem block012_data_flat030_step : block012_data_flat030 = (CoefficientMerge.fastMerge block012_data_flat028 block012_data_flat029) := by decide +kernel
theorem block012_data_flat030_original : block012_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (786193920 : Int) atom0910Coded) (CoefficientMerge.scale (232689600 : Int) atom0911Coded)) := by
  rw [block012_data_flat030_step, block012_data_flat028_original, block012_data_flat029_original]
def block012_data_flat031 : CoefficientMerge.Poly := [(nat_lit 2443, Int.ofNat (nat_lit 13607520))]
theorem block012_data_flat031_step : block012_data_flat031 = (CoefficientMerge.scale (13607520 : Int) atom0912Coded) := by decide +kernel
theorem block012_data_flat031_original : block012_data_flat031 = (CoefficientMerge.scale (13607520 : Int) atom0912Coded) := by
  rw [block012_data_flat031_step]
def block012_data_flat032 : CoefficientMerge.Poly := [(nat_lit 2444, Int.ofNat (nat_lit 701867040))]
theorem block012_data_flat032_step : block012_data_flat032 = (CoefficientMerge.scale (701867040 : Int) atom0913Coded) := by decide +kernel
theorem block012_data_flat032_original : block012_data_flat032 = (CoefficientMerge.scale (701867040 : Int) atom0913Coded) := by
  rw [block012_data_flat032_step]
def block012_data_flat033 : CoefficientMerge.Poly := [(nat_lit 2445, Int.ofNat (nat_lit 1929608160))]
theorem block012_data_flat033_step : block012_data_flat033 = (CoefficientMerge.scale (1929608160 : Int) atom0914Coded) := by decide +kernel
theorem block012_data_flat033_original : block012_data_flat033 = (CoefficientMerge.scale (1929608160 : Int) atom0914Coded) := by
  rw [block012_data_flat033_step]
def block012_data_flat034 : CoefficientMerge.Poly := [(nat_lit 2444, Int.ofNat (nat_lit 701867040)), (nat_lit 2445, Int.ofNat (nat_lit 1929608160))]
theorem block012_data_flat034_step : block012_data_flat034 = (CoefficientMerge.fastMerge block012_data_flat032 block012_data_flat033) := by decide +kernel
theorem block012_data_flat034_original : block012_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (701867040 : Int) atom0913Coded) (CoefficientMerge.scale (1929608160 : Int) atom0914Coded)) := by
  rw [block012_data_flat034_step, block012_data_flat032_original, block012_data_flat033_original]
def block012_data_flat035 : CoefficientMerge.Poly := [(nat_lit 2443, Int.ofNat (nat_lit 13607520)), (nat_lit 2444, Int.ofNat (nat_lit 701867040)), (nat_lit 2445, Int.ofNat (nat_lit 1929608160))]
theorem block012_data_flat035_step : block012_data_flat035 = (CoefficientMerge.fastMerge block012_data_flat031 block012_data_flat034) := by decide +kernel
theorem block012_data_flat035_original : block012_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13607520 : Int) atom0912Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (701867040 : Int) atom0913Coded) (CoefficientMerge.scale (1929608160 : Int) atom0914Coded))) := by
  rw [block012_data_flat035_step, block012_data_flat031_original, block012_data_flat034_original]
def block012_data_flat036 : CoefficientMerge.Poly := [(nat_lit 2441, Int.ofNat (nat_lit 786193920)), (nat_lit 2442, Int.ofNat (nat_lit 232689600)), (nat_lit 2443, Int.ofNat (nat_lit 13607520)), (nat_lit 2444, Int.ofNat (nat_lit 701867040)), (nat_lit 2445, Int.ofNat (nat_lit 1929608160))]
theorem block012_data_flat036_step : block012_data_flat036 = (CoefficientMerge.fastMerge block012_data_flat030 block012_data_flat035) := by decide +kernel
theorem block012_data_flat036_original : block012_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (786193920 : Int) atom0910Coded) (CoefficientMerge.scale (232689600 : Int) atom0911Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13607520 : Int) atom0912Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (701867040 : Int) atom0913Coded) (CoefficientMerge.scale (1929608160 : Int) atom0914Coded)))) := by
  rw [block012_data_flat036_step, block012_data_flat030_original, block012_data_flat035_original]
def block012_data_flat037 : CoefficientMerge.Poly := [(nat_lit 2427, Int.ofNat (nat_lit 1180247040)), (nat_lit 2428, Int.ofNat (nat_lit 2293143552)), (nat_lit 2429, Int.ofNat (nat_lit 3586383360)), (nat_lit 2439, Int.ofNat (nat_lit 411045120)), (nat_lit 2440, Int.ofNat (nat_lit 628784640)), (nat_lit 2441, Int.ofNat (nat_lit 786193920)), (nat_lit 2442, Int.ofNat (nat_lit 232689600)), (nat_lit 2443, Int.ofNat (nat_lit 13607520)), (nat_lit 2444, Int.ofNat (nat_lit 701867040)), (nat_lit 2445, Int.ofNat (nat_lit 1929608160))]
theorem block012_data_flat037_step : block012_data_flat037 = (CoefficientMerge.fastMerge block012_data_flat027 block012_data_flat036) := by decide +kernel
theorem block012_data_flat037_original : block012_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0905Coded) (CoefficientMerge.scale (2293143552 : Int) atom0906Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0907Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411045120 : Int) atom0908Coded) (CoefficientMerge.scale (628784640 : Int) atom0909Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (786193920 : Int) atom0910Coded) (CoefficientMerge.scale (232689600 : Int) atom0911Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13607520 : Int) atom0912Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (701867040 : Int) atom0913Coded) (CoefficientMerge.scale (1929608160 : Int) atom0914Coded))))) := by
  rw [block012_data_flat037_step, block012_data_flat027_original, block012_data_flat036_original]
def block012_data_flat038 : CoefficientMerge.Poly := [(nat_lit 2248, Int.ofNat (nat_lit 182136240)), (nat_lit 2249, Int.ofNat (nat_lit 5136502230)), (nat_lit 2267, Int.ofNat (nat_lit 4373859870)), (nat_lit 2401, Int.ofNat (nat_lit 154863360)), (nat_lit 2402, Int.ofNat (nat_lit 78704640)), (nat_lit 2406, Int.ofNat (nat_lit 155020320)), (nat_lit 2420, Int.ofNat (nat_lit 158595840)), (nat_lit 2422, Int.ofNat (nat_lit 103864320)), (nat_lit 2423, Int.ofNat (nat_lit 207728640)), (nat_lit 2424, Int.ofNat (nat_lit 87669792)), (nat_lit 2427, Int.ofNat (nat_lit 1180247040)), (nat_lit 2428, Int.ofNat (nat_lit 2293143552)), (nat_lit 2429, Int.ofNat (nat_lit 3586383360)), (nat_lit 2439, Int.ofNat (nat_lit 411045120)), (nat_lit 2440, Int.ofNat (nat_lit 628784640)), (nat_lit 2441, Int.ofNat (nat_lit 786193920)), (nat_lit 2442, Int.ofNat (nat_lit 232689600)), (nat_lit 2443, Int.ofNat (nat_lit 13607520)), (nat_lit 2444, Int.ofNat (nat_lit 701867040)), (nat_lit 2445, Int.ofNat (nat_lit 1929608160))]
theorem block012_data_flat038_step : block012_data_flat038 = (CoefficientMerge.fastMerge block012_data_flat018 block012_data_flat037) := by decide +kernel
theorem block012_data_flat038_original : block012_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182136240 : Int) atom0895Coded) (CoefficientMerge.scale (5136502230 : Int) atom0896Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4373859870 : Int) atom0897Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154863360 : Int) atom0898Coded) (CoefficientMerge.scale (78704640 : Int) atom0899Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (155020320 : Int) atom0900Coded) (CoefficientMerge.scale (158595840 : Int) atom0901Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0902Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0903Coded) (CoefficientMerge.scale (87669792 : Int) atom0904Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0905Coded) (CoefficientMerge.scale (2293143552 : Int) atom0906Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0907Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411045120 : Int) atom0908Coded) (CoefficientMerge.scale (628784640 : Int) atom0909Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (786193920 : Int) atom0910Coded) (CoefficientMerge.scale (232689600 : Int) atom0911Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13607520 : Int) atom0912Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (701867040 : Int) atom0913Coded) (CoefficientMerge.scale (1929608160 : Int) atom0914Coded)))))) := by
  rw [block012_data_flat038_step, block012_data_flat018_original, block012_data_flat037_original]
def block012_data_flat039 : CoefficientMerge.Poly := [(nat_lit 2446, Int.ofNat (nat_lit 3909670560))]
theorem block012_data_flat039_step : block012_data_flat039 = (CoefficientMerge.scale (3909670560 : Int) atom0915Coded) := by decide +kernel
theorem block012_data_flat039_original : block012_data_flat039 = (CoefficientMerge.scale (3909670560 : Int) atom0915Coded) := by
  rw [block012_data_flat039_step]
def block012_data_flat040 : CoefficientMerge.Poly := [(nat_lit 2447, Int.ofNat (nat_lit 6267332160))]
theorem block012_data_flat040_step : block012_data_flat040 = (CoefficientMerge.scale (6267332160 : Int) atom0916Coded) := by decide +kernel
theorem block012_data_flat040_original : block012_data_flat040 = (CoefficientMerge.scale (6267332160 : Int) atom0916Coded) := by
  rw [block012_data_flat040_step]
def block012_data_flat041 : CoefficientMerge.Poly := [(nat_lit 2446, Int.ofNat (nat_lit 3909670560)), (nat_lit 2447, Int.ofNat (nat_lit 6267332160))]
theorem block012_data_flat041_step : block012_data_flat041 = (CoefficientMerge.fastMerge block012_data_flat039 block012_data_flat040) := by decide +kernel
theorem block012_data_flat041_original : block012_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3909670560 : Int) atom0915Coded) (CoefficientMerge.scale (6267332160 : Int) atom0916Coded)) := by
  rw [block012_data_flat041_step, block012_data_flat039_original, block012_data_flat040_original]
def block012_data_flat042 : CoefficientMerge.Poly := [(nat_lit 2458, Int.ofNat (nat_lit 891244800))]
theorem block012_data_flat042_step : block012_data_flat042 = (CoefficientMerge.scale (891244800 : Int) atom0917Coded) := by decide +kernel
theorem block012_data_flat042_original : block012_data_flat042 = (CoefficientMerge.scale (891244800 : Int) atom0917Coded) := by
  rw [block012_data_flat042_step]
def block012_data_flat043 : CoefficientMerge.Poly := [(nat_lit 2459, Int.ofNat (nat_lit 1609136640))]
theorem block012_data_flat043_step : block012_data_flat043 = (CoefficientMerge.scale (1609136640 : Int) atom0918Coded) := by decide +kernel
theorem block012_data_flat043_original : block012_data_flat043 = (CoefficientMerge.scale (1609136640 : Int) atom0918Coded) := by
  rw [block012_data_flat043_step]
def block012_data_flat044 : CoefficientMerge.Poly := [(nat_lit 2460, Int.ofNat (nat_lit 1344916800))]
theorem block012_data_flat044_step : block012_data_flat044 = (CoefficientMerge.scale (1344916800 : Int) atom0919Coded) := by decide +kernel
theorem block012_data_flat044_original : block012_data_flat044 = (CoefficientMerge.scale (1344916800 : Int) atom0919Coded) := by
  rw [block012_data_flat044_step]
def block012_data_flat045 : CoefficientMerge.Poly := [(nat_lit 2459, Int.ofNat (nat_lit 1609136640)), (nat_lit 2460, Int.ofNat (nat_lit 1344916800))]
theorem block012_data_flat045_step : block012_data_flat045 = (CoefficientMerge.fastMerge block012_data_flat043 block012_data_flat044) := by decide +kernel
theorem block012_data_flat045_original : block012_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1609136640 : Int) atom0918Coded) (CoefficientMerge.scale (1344916800 : Int) atom0919Coded)) := by
  rw [block012_data_flat045_step, block012_data_flat043_original, block012_data_flat044_original]
def block012_data_flat046 : CoefficientMerge.Poly := [(nat_lit 2458, Int.ofNat (nat_lit 891244800)), (nat_lit 2459, Int.ofNat (nat_lit 1609136640)), (nat_lit 2460, Int.ofNat (nat_lit 1344916800))]
theorem block012_data_flat046_step : block012_data_flat046 = (CoefficientMerge.fastMerge block012_data_flat042 block012_data_flat045) := by decide +kernel
theorem block012_data_flat046_original : block012_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (891244800 : Int) atom0917Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1609136640 : Int) atom0918Coded) (CoefficientMerge.scale (1344916800 : Int) atom0919Coded))) := by
  rw [block012_data_flat046_step, block012_data_flat042_original, block012_data_flat045_original]
def block012_data_flat047 : CoefficientMerge.Poly := [(nat_lit 2446, Int.ofNat (nat_lit 3909670560)), (nat_lit 2447, Int.ofNat (nat_lit 6267332160)), (nat_lit 2458, Int.ofNat (nat_lit 891244800)), (nat_lit 2459, Int.ofNat (nat_lit 1609136640)), (nat_lit 2460, Int.ofNat (nat_lit 1344916800))]
theorem block012_data_flat047_step : block012_data_flat047 = (CoefficientMerge.fastMerge block012_data_flat041 block012_data_flat046) := by decide +kernel
theorem block012_data_flat047_original : block012_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3909670560 : Int) atom0915Coded) (CoefficientMerge.scale (6267332160 : Int) atom0916Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (891244800 : Int) atom0917Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1609136640 : Int) atom0918Coded) (CoefficientMerge.scale (1344916800 : Int) atom0919Coded)))) := by
  rw [block012_data_flat047_step, block012_data_flat041_original, block012_data_flat046_original]
def block012_data_flat048 : CoefficientMerge.Poly := [(nat_lit 2461, Int.ofNat (nat_lit 1404100320))]
theorem block012_data_flat048_step : block012_data_flat048 = (CoefficientMerge.scale (1404100320 : Int) atom0920Coded) := by decide +kernel
theorem block012_data_flat048_original : block012_data_flat048 = (CoefficientMerge.scale (1404100320 : Int) atom0920Coded) := by
  rw [block012_data_flat048_step]
def block012_data_flat049 : CoefficientMerge.Poly := [(nat_lit 2462, Int.ofNat (nat_lit 2940756000))]
theorem block012_data_flat049_step : block012_data_flat049 = (CoefficientMerge.scale (2940756000 : Int) atom0921Coded) := by decide +kernel
theorem block012_data_flat049_original : block012_data_flat049 = (CoefficientMerge.scale (2940756000 : Int) atom0921Coded) := by
  rw [block012_data_flat049_step]
def block012_data_flat050 : CoefficientMerge.Poly := [(nat_lit 2461, Int.ofNat (nat_lit 1404100320)), (nat_lit 2462, Int.ofNat (nat_lit 2940756000))]
theorem block012_data_flat050_step : block012_data_flat050 = (CoefficientMerge.fastMerge block012_data_flat048 block012_data_flat049) := by decide +kernel
theorem block012_data_flat050_original : block012_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1404100320 : Int) atom0920Coded) (CoefficientMerge.scale (2940756000 : Int) atom0921Coded)) := by
  rw [block012_data_flat050_step, block012_data_flat048_original, block012_data_flat049_original]
def block012_data_flat051 : CoefficientMerge.Poly := [(nat_lit 2463, Int.ofNat (nat_lit 3706055520))]
theorem block012_data_flat051_step : block012_data_flat051 = (CoefficientMerge.scale (3706055520 : Int) atom0922Coded) := by decide +kernel
theorem block012_data_flat051_original : block012_data_flat051 = (CoefficientMerge.scale (3706055520 : Int) atom0922Coded) := by
  rw [block012_data_flat051_step]
def block012_data_flat052 : CoefficientMerge.Poly := [(nat_lit 2464, Int.ofNat (nat_lit 5793806880))]
theorem block012_data_flat052_step : block012_data_flat052 = (CoefficientMerge.scale (5793806880 : Int) atom0923Coded) := by decide +kernel
theorem block012_data_flat052_original : block012_data_flat052 = (CoefficientMerge.scale (5793806880 : Int) atom0923Coded) := by
  rw [block012_data_flat052_step]
def block012_data_flat053 : CoefficientMerge.Poly := [(nat_lit 2465, Int.ofNat (nat_lit 8475644160))]
theorem block012_data_flat053_step : block012_data_flat053 = (CoefficientMerge.scale (8475644160 : Int) atom0924Coded) := by decide +kernel
theorem block012_data_flat053_original : block012_data_flat053 = (CoefficientMerge.scale (8475644160 : Int) atom0924Coded) := by
  rw [block012_data_flat053_step]
def block012_data_flat054 : CoefficientMerge.Poly := [(nat_lit 2464, Int.ofNat (nat_lit 5793806880)), (nat_lit 2465, Int.ofNat (nat_lit 8475644160))]
theorem block012_data_flat054_step : block012_data_flat054 = (CoefficientMerge.fastMerge block012_data_flat052 block012_data_flat053) := by decide +kernel
theorem block012_data_flat054_original : block012_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5793806880 : Int) atom0923Coded) (CoefficientMerge.scale (8475644160 : Int) atom0924Coded)) := by
  rw [block012_data_flat054_step, block012_data_flat052_original, block012_data_flat053_original]
def block012_data_flat055 : CoefficientMerge.Poly := [(nat_lit 2463, Int.ofNat (nat_lit 3706055520)), (nat_lit 2464, Int.ofNat (nat_lit 5793806880)), (nat_lit 2465, Int.ofNat (nat_lit 8475644160))]
theorem block012_data_flat055_step : block012_data_flat055 = (CoefficientMerge.fastMerge block012_data_flat051 block012_data_flat054) := by decide +kernel
theorem block012_data_flat055_original : block012_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3706055520 : Int) atom0922Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5793806880 : Int) atom0923Coded) (CoefficientMerge.scale (8475644160 : Int) atom0924Coded))) := by
  rw [block012_data_flat055_step, block012_data_flat051_original, block012_data_flat054_original]
def block012_data_flat056 : CoefficientMerge.Poly := [(nat_lit 2461, Int.ofNat (nat_lit 1404100320)), (nat_lit 2462, Int.ofNat (nat_lit 2940756000)), (nat_lit 2463, Int.ofNat (nat_lit 3706055520)), (nat_lit 2464, Int.ofNat (nat_lit 5793806880)), (nat_lit 2465, Int.ofNat (nat_lit 8475644160))]
theorem block012_data_flat056_step : block012_data_flat056 = (CoefficientMerge.fastMerge block012_data_flat050 block012_data_flat055) := by decide +kernel
theorem block012_data_flat056_original : block012_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1404100320 : Int) atom0920Coded) (CoefficientMerge.scale (2940756000 : Int) atom0921Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3706055520 : Int) atom0922Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5793806880 : Int) atom0923Coded) (CoefficientMerge.scale (8475644160 : Int) atom0924Coded)))) := by
  rw [block012_data_flat056_step, block012_data_flat050_original, block012_data_flat055_original]
def block012_data_flat057 : CoefficientMerge.Poly := [(nat_lit 2446, Int.ofNat (nat_lit 3909670560)), (nat_lit 2447, Int.ofNat (nat_lit 6267332160)), (nat_lit 2458, Int.ofNat (nat_lit 891244800)), (nat_lit 2459, Int.ofNat (nat_lit 1609136640)), (nat_lit 2460, Int.ofNat (nat_lit 1344916800)), (nat_lit 2461, Int.ofNat (nat_lit 1404100320)), (nat_lit 2462, Int.ofNat (nat_lit 2940756000)), (nat_lit 2463, Int.ofNat (nat_lit 3706055520)), (nat_lit 2464, Int.ofNat (nat_lit 5793806880)), (nat_lit 2465, Int.ofNat (nat_lit 8475644160))]
theorem block012_data_flat057_step : block012_data_flat057 = (CoefficientMerge.fastMerge block012_data_flat047 block012_data_flat056) := by decide +kernel
theorem block012_data_flat057_original : block012_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3909670560 : Int) atom0915Coded) (CoefficientMerge.scale (6267332160 : Int) atom0916Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (891244800 : Int) atom0917Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1609136640 : Int) atom0918Coded) (CoefficientMerge.scale (1344916800 : Int) atom0919Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1404100320 : Int) atom0920Coded) (CoefficientMerge.scale (2940756000 : Int) atom0921Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3706055520 : Int) atom0922Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5793806880 : Int) atom0923Coded) (CoefficientMerge.scale (8475644160 : Int) atom0924Coded))))) := by
  rw [block012_data_flat057_step, block012_data_flat047_original, block012_data_flat056_original]
def block012_data_flat058 : CoefficientMerge.Poly := [(nat_lit 2477, Int.ofNat (nat_lit 1725016320))]
theorem block012_data_flat058_step : block012_data_flat058 = (CoefficientMerge.scale (1725016320 : Int) atom0925Coded) := by decide +kernel
theorem block012_data_flat058_original : block012_data_flat058 = (CoefficientMerge.scale (1725016320 : Int) atom0925Coded) := by
  rw [block012_data_flat058_step]
def block012_data_flat059 : CoefficientMerge.Poly := [(nat_lit 2478, Int.ofNat (nat_lit 2334026880))]
theorem block012_data_flat059_step : block012_data_flat059 = (CoefficientMerge.scale (2334026880 : Int) atom0926Coded) := by decide +kernel
theorem block012_data_flat059_original : block012_data_flat059 = (CoefficientMerge.scale (2334026880 : Int) atom0926Coded) := by
  rw [block012_data_flat059_step]
def block012_data_flat060 : CoefficientMerge.Poly := [(nat_lit 2477, Int.ofNat (nat_lit 1725016320)), (nat_lit 2478, Int.ofNat (nat_lit 2334026880))]
theorem block012_data_flat060_step : block012_data_flat060 = (CoefficientMerge.fastMerge block012_data_flat058 block012_data_flat059) := by decide +kernel
theorem block012_data_flat060_original : block012_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1725016320 : Int) atom0925Coded) (CoefficientMerge.scale (2334026880 : Int) atom0926Coded)) := by
  rw [block012_data_flat060_step, block012_data_flat058_original, block012_data_flat059_original]
def block012_data_flat061 : CoefficientMerge.Poly := [(nat_lit 2479, Int.ofNat (nat_lit 2590296480))]
theorem block012_data_flat061_step : block012_data_flat061 = (CoefficientMerge.scale (2590296480 : Int) atom0927Coded) := by decide +kernel
theorem block012_data_flat061_original : block012_data_flat061 = (CoefficientMerge.scale (2590296480 : Int) atom0927Coded) := by
  rw [block012_data_flat061_step]
def block012_data_flat062 : CoefficientMerge.Poly := [(nat_lit 2480, Int.ofNat (nat_lit 4993500960))]
theorem block012_data_flat062_step : block012_data_flat062 = (CoefficientMerge.scale (4993500960 : Int) atom0928Coded) := by decide +kernel
theorem block012_data_flat062_original : block012_data_flat062 = (CoefficientMerge.scale (4993500960 : Int) atom0928Coded) := by
  rw [block012_data_flat062_step]
def block012_data_flat063 : CoefficientMerge.Poly := [(nat_lit 2481, Int.ofNat (nat_lit 6174312480))]
theorem block012_data_flat063_step : block012_data_flat063 = (CoefficientMerge.scale (6174312480 : Int) atom0929Coded) := by decide +kernel
theorem block012_data_flat063_original : block012_data_flat063 = (CoefficientMerge.scale (6174312480 : Int) atom0929Coded) := by
  rw [block012_data_flat063_step]
def block012_data_flat064 : CoefficientMerge.Poly := [(nat_lit 2480, Int.ofNat (nat_lit 4993500960)), (nat_lit 2481, Int.ofNat (nat_lit 6174312480))]
theorem block012_data_flat064_step : block012_data_flat064 = (CoefficientMerge.fastMerge block012_data_flat062 block012_data_flat063) := by decide +kernel
theorem block012_data_flat064_original : block012_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4993500960 : Int) atom0928Coded) (CoefficientMerge.scale (6174312480 : Int) atom0929Coded)) := by
  rw [block012_data_flat064_step, block012_data_flat062_original, block012_data_flat063_original]
def block012_data_flat065 : CoefficientMerge.Poly := [(nat_lit 2479, Int.ofNat (nat_lit 2590296480)), (nat_lit 2480, Int.ofNat (nat_lit 4993500960)), (nat_lit 2481, Int.ofNat (nat_lit 6174312480))]
theorem block012_data_flat065_step : block012_data_flat065 = (CoefficientMerge.fastMerge block012_data_flat061 block012_data_flat064) := by decide +kernel
theorem block012_data_flat065_original : block012_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2590296480 : Int) atom0927Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4993500960 : Int) atom0928Coded) (CoefficientMerge.scale (6174312480 : Int) atom0929Coded))) := by
  rw [block012_data_flat065_step, block012_data_flat061_original, block012_data_flat064_original]
def block012_data_flat066 : CoefficientMerge.Poly := [(nat_lit 2477, Int.ofNat (nat_lit 1725016320)), (nat_lit 2478, Int.ofNat (nat_lit 2334026880)), (nat_lit 2479, Int.ofNat (nat_lit 2590296480)), (nat_lit 2480, Int.ofNat (nat_lit 4993500960)), (nat_lit 2481, Int.ofNat (nat_lit 6174312480))]
theorem block012_data_flat066_step : block012_data_flat066 = (CoefficientMerge.fastMerge block012_data_flat060 block012_data_flat065) := by decide +kernel
theorem block012_data_flat066_original : block012_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1725016320 : Int) atom0925Coded) (CoefficientMerge.scale (2334026880 : Int) atom0926Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2590296480 : Int) atom0927Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4993500960 : Int) atom0928Coded) (CoefficientMerge.scale (6174312480 : Int) atom0929Coded)))) := by
  rw [block012_data_flat066_step, block012_data_flat060_original, block012_data_flat065_original]
def block012_data_flat067 : CoefficientMerge.Poly := [(nat_lit 2482, Int.ofNat (nat_lit 7280074080))]
theorem block012_data_flat067_step : block012_data_flat067 = (CoefficientMerge.scale (7280074080 : Int) atom0930Coded) := by decide +kernel
theorem block012_data_flat067_original : block012_data_flat067 = (CoefficientMerge.scale (7280074080 : Int) atom0930Coded) := by
  rw [block012_data_flat067_step]
def block012_data_flat068 : CoefficientMerge.Poly := [(nat_lit 2483, Int.ofNat (nat_lit 12177524160))]
theorem block012_data_flat068_step : block012_data_flat068 = (CoefficientMerge.scale (12177524160 : Int) atom0931Coded) := by decide +kernel
theorem block012_data_flat068_original : block012_data_flat068 = (CoefficientMerge.scale (12177524160 : Int) atom0931Coded) := by
  rw [block012_data_flat068_step]
def block012_data_flat069 : CoefficientMerge.Poly := [(nat_lit 2482, Int.ofNat (nat_lit 7280074080)), (nat_lit 2483, Int.ofNat (nat_lit 12177524160))]
theorem block012_data_flat069_step : block012_data_flat069 = (CoefficientMerge.fastMerge block012_data_flat067 block012_data_flat068) := by decide +kernel
theorem block012_data_flat069_original : block012_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7280074080 : Int) atom0930Coded) (CoefficientMerge.scale (12177524160 : Int) atom0931Coded)) := by
  rw [block012_data_flat069_step, block012_data_flat067_original, block012_data_flat068_original]
def block012_data_flat070 : CoefficientMerge.Poly := [(nat_lit 2496, Int.ofNat (nat_lit 2643701760))]
theorem block012_data_flat070_step : block012_data_flat070 = (CoefficientMerge.scale (2643701760 : Int) atom0932Coded) := by decide +kernel
theorem block012_data_flat070_original : block012_data_flat070 = (CoefficientMerge.scale (2643701760 : Int) atom0932Coded) := by
  rw [block012_data_flat070_step]
def block012_data_flat071 : CoefficientMerge.Poly := [(nat_lit 2497, Int.ofNat (nat_lit 5717445840))]
theorem block012_data_flat071_step : block012_data_flat071 = (CoefficientMerge.scale (5717445840 : Int) atom0933Coded) := by decide +kernel
theorem block012_data_flat071_original : block012_data_flat071 = (CoefficientMerge.scale (5717445840 : Int) atom0933Coded) := by
  rw [block012_data_flat071_step]
def block012_data_flat072 : CoefficientMerge.Poly := [(nat_lit 2498, Int.ofNat (nat_lit 11409847200))]
theorem block012_data_flat072_step : block012_data_flat072 = (CoefficientMerge.scale (11409847200 : Int) atom0934Coded) := by decide +kernel
theorem block012_data_flat072_original : block012_data_flat072 = (CoefficientMerge.scale (11409847200 : Int) atom0934Coded) := by
  rw [block012_data_flat072_step]
def block012_data_flat073 : CoefficientMerge.Poly := [(nat_lit 2497, Int.ofNat (nat_lit 5717445840)), (nat_lit 2498, Int.ofNat (nat_lit 11409847200))]
theorem block012_data_flat073_step : block012_data_flat073 = (CoefficientMerge.fastMerge block012_data_flat071 block012_data_flat072) := by decide +kernel
theorem block012_data_flat073_original : block012_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5717445840 : Int) atom0933Coded) (CoefficientMerge.scale (11409847200 : Int) atom0934Coded)) := by
  rw [block012_data_flat073_step, block012_data_flat071_original, block012_data_flat072_original]
def block012_data_flat074 : CoefficientMerge.Poly := [(nat_lit 2496, Int.ofNat (nat_lit 2643701760)), (nat_lit 2497, Int.ofNat (nat_lit 5717445840)), (nat_lit 2498, Int.ofNat (nat_lit 11409847200))]
theorem block012_data_flat074_step : block012_data_flat074 = (CoefficientMerge.fastMerge block012_data_flat070 block012_data_flat073) := by decide +kernel
theorem block012_data_flat074_original : block012_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2643701760 : Int) atom0932Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5717445840 : Int) atom0933Coded) (CoefficientMerge.scale (11409847200 : Int) atom0934Coded))) := by
  rw [block012_data_flat074_step, block012_data_flat070_original, block012_data_flat073_original]
def block012_data_flat075 : CoefficientMerge.Poly := [(nat_lit 2482, Int.ofNat (nat_lit 7280074080)), (nat_lit 2483, Int.ofNat (nat_lit 12177524160)), (nat_lit 2496, Int.ofNat (nat_lit 2643701760)), (nat_lit 2497, Int.ofNat (nat_lit 5717445840)), (nat_lit 2498, Int.ofNat (nat_lit 11409847200))]
theorem block012_data_flat075_step : block012_data_flat075 = (CoefficientMerge.fastMerge block012_data_flat069 block012_data_flat074) := by decide +kernel
theorem block012_data_flat075_original : block012_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7280074080 : Int) atom0930Coded) (CoefficientMerge.scale (12177524160 : Int) atom0931Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2643701760 : Int) atom0932Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5717445840 : Int) atom0933Coded) (CoefficientMerge.scale (11409847200 : Int) atom0934Coded)))) := by
  rw [block012_data_flat075_step, block012_data_flat069_original, block012_data_flat074_original]
def block012_data_flat076 : CoefficientMerge.Poly := [(nat_lit 2477, Int.ofNat (nat_lit 1725016320)), (nat_lit 2478, Int.ofNat (nat_lit 2334026880)), (nat_lit 2479, Int.ofNat (nat_lit 2590296480)), (nat_lit 2480, Int.ofNat (nat_lit 4993500960)), (nat_lit 2481, Int.ofNat (nat_lit 6174312480)), (nat_lit 2482, Int.ofNat (nat_lit 7280074080)), (nat_lit 2483, Int.ofNat (nat_lit 12177524160)), (nat_lit 2496, Int.ofNat (nat_lit 2643701760)), (nat_lit 2497, Int.ofNat (nat_lit 5717445840)), (nat_lit 2498, Int.ofNat (nat_lit 11409847200))]
theorem block012_data_flat076_step : block012_data_flat076 = (CoefficientMerge.fastMerge block012_data_flat066 block012_data_flat075) := by decide +kernel
theorem block012_data_flat076_original : block012_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1725016320 : Int) atom0925Coded) (CoefficientMerge.scale (2334026880 : Int) atom0926Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2590296480 : Int) atom0927Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4993500960 : Int) atom0928Coded) (CoefficientMerge.scale (6174312480 : Int) atom0929Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7280074080 : Int) atom0930Coded) (CoefficientMerge.scale (12177524160 : Int) atom0931Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2643701760 : Int) atom0932Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5717445840 : Int) atom0933Coded) (CoefficientMerge.scale (11409847200 : Int) atom0934Coded))))) := by
  rw [block012_data_flat076_step, block012_data_flat066_original, block012_data_flat075_original]
def block012_data_flat077 : CoefficientMerge.Poly := [(nat_lit 2446, Int.ofNat (nat_lit 3909670560)), (nat_lit 2447, Int.ofNat (nat_lit 6267332160)), (nat_lit 2458, Int.ofNat (nat_lit 891244800)), (nat_lit 2459, Int.ofNat (nat_lit 1609136640)), (nat_lit 2460, Int.ofNat (nat_lit 1344916800)), (nat_lit 2461, Int.ofNat (nat_lit 1404100320)), (nat_lit 2462, Int.ofNat (nat_lit 2940756000)), (nat_lit 2463, Int.ofNat (nat_lit 3706055520)), (nat_lit 2464, Int.ofNat (nat_lit 5793806880)), (nat_lit 2465, Int.ofNat (nat_lit 8475644160)), (nat_lit 2477, Int.ofNat (nat_lit 1725016320)), (nat_lit 2478, Int.ofNat (nat_lit 2334026880)), (nat_lit 2479, Int.ofNat (nat_lit 2590296480)), (nat_lit 2480, Int.ofNat (nat_lit 4993500960)), (nat_lit 2481, Int.ofNat (nat_lit 6174312480)), (nat_lit 2482, Int.ofNat (nat_lit 7280074080)), (nat_lit 2483, Int.ofNat (nat_lit 12177524160)), (nat_lit 2496, Int.ofNat (nat_lit 2643701760)), (nat_lit 2497, Int.ofNat (nat_lit 5717445840)), (nat_lit 2498, Int.ofNat (nat_lit 11409847200))]
theorem block012_data_flat077_step : block012_data_flat077 = (CoefficientMerge.fastMerge block012_data_flat057 block012_data_flat076) := by decide +kernel
theorem block012_data_flat077_original : block012_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3909670560 : Int) atom0915Coded) (CoefficientMerge.scale (6267332160 : Int) atom0916Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (891244800 : Int) atom0917Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1609136640 : Int) atom0918Coded) (CoefficientMerge.scale (1344916800 : Int) atom0919Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1404100320 : Int) atom0920Coded) (CoefficientMerge.scale (2940756000 : Int) atom0921Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3706055520 : Int) atom0922Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5793806880 : Int) atom0923Coded) (CoefficientMerge.scale (8475644160 : Int) atom0924Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1725016320 : Int) atom0925Coded) (CoefficientMerge.scale (2334026880 : Int) atom0926Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2590296480 : Int) atom0927Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4993500960 : Int) atom0928Coded) (CoefficientMerge.scale (6174312480 : Int) atom0929Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7280074080 : Int) atom0930Coded) (CoefficientMerge.scale (12177524160 : Int) atom0931Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2643701760 : Int) atom0932Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5717445840 : Int) atom0933Coded) (CoefficientMerge.scale (11409847200 : Int) atom0934Coded)))))) := by
  rw [block012_data_flat077_step, block012_data_flat057_original, block012_data_flat076_original]
def block012_data_flat078 : CoefficientMerge.Poly := [(nat_lit 2248, Int.ofNat (nat_lit 182136240)), (nat_lit 2249, Int.ofNat (nat_lit 5136502230)), (nat_lit 2267, Int.ofNat (nat_lit 4373859870)), (nat_lit 2401, Int.ofNat (nat_lit 154863360)), (nat_lit 2402, Int.ofNat (nat_lit 78704640)), (nat_lit 2406, Int.ofNat (nat_lit 155020320)), (nat_lit 2420, Int.ofNat (nat_lit 158595840)), (nat_lit 2422, Int.ofNat (nat_lit 103864320)), (nat_lit 2423, Int.ofNat (nat_lit 207728640)), (nat_lit 2424, Int.ofNat (nat_lit 87669792)), (nat_lit 2427, Int.ofNat (nat_lit 1180247040)), (nat_lit 2428, Int.ofNat (nat_lit 2293143552)), (nat_lit 2429, Int.ofNat (nat_lit 3586383360)), (nat_lit 2439, Int.ofNat (nat_lit 411045120)), (nat_lit 2440, Int.ofNat (nat_lit 628784640)), (nat_lit 2441, Int.ofNat (nat_lit 786193920)), (nat_lit 2442, Int.ofNat (nat_lit 232689600)), (nat_lit 2443, Int.ofNat (nat_lit 13607520)), (nat_lit 2444, Int.ofNat (nat_lit 701867040)), (nat_lit 2445, Int.ofNat (nat_lit 1929608160)), (nat_lit 2446, Int.ofNat (nat_lit 3909670560)), (nat_lit 2447, Int.ofNat (nat_lit 6267332160)), (nat_lit 2458, Int.ofNat (nat_lit 891244800)), (nat_lit 2459, Int.ofNat (nat_lit 1609136640)), (nat_lit 2460, Int.ofNat (nat_lit 1344916800)), (nat_lit 2461, Int.ofNat (nat_lit 1404100320)), (nat_lit 2462, Int.ofNat (nat_lit 2940756000)), (nat_lit 2463, Int.ofNat (nat_lit 3706055520)), (nat_lit 2464, Int.ofNat (nat_lit 5793806880)), (nat_lit 2465, Int.ofNat (nat_lit 8475644160)), (nat_lit 2477, Int.ofNat (nat_lit 1725016320)), (nat_lit 2478, Int.ofNat (nat_lit 2334026880)), (nat_lit 2479, Int.ofNat (nat_lit 2590296480)), (nat_lit 2480, Int.ofNat (nat_lit 4993500960)), (nat_lit 2481, Int.ofNat (nat_lit 6174312480)), (nat_lit 2482, Int.ofNat (nat_lit 7280074080)), (nat_lit 2483, Int.ofNat (nat_lit 12177524160)), (nat_lit 2496, Int.ofNat (nat_lit 2643701760)), (nat_lit 2497, Int.ofNat (nat_lit 5717445840)), (nat_lit 2498, Int.ofNat (nat_lit 11409847200))]
theorem block012_data_flat078_step : block012_data_flat078 = (CoefficientMerge.fastMerge block012_data_flat038 block012_data_flat077) := by decide +kernel
theorem block012_data_flat078_original : block012_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182136240 : Int) atom0895Coded) (CoefficientMerge.scale (5136502230 : Int) atom0896Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4373859870 : Int) atom0897Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154863360 : Int) atom0898Coded) (CoefficientMerge.scale (78704640 : Int) atom0899Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (155020320 : Int) atom0900Coded) (CoefficientMerge.scale (158595840 : Int) atom0901Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0902Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0903Coded) (CoefficientMerge.scale (87669792 : Int) atom0904Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0905Coded) (CoefficientMerge.scale (2293143552 : Int) atom0906Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0907Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411045120 : Int) atom0908Coded) (CoefficientMerge.scale (628784640 : Int) atom0909Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (786193920 : Int) atom0910Coded) (CoefficientMerge.scale (232689600 : Int) atom0911Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13607520 : Int) atom0912Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (701867040 : Int) atom0913Coded) (CoefficientMerge.scale (1929608160 : Int) atom0914Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3909670560 : Int) atom0915Coded) (CoefficientMerge.scale (6267332160 : Int) atom0916Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (891244800 : Int) atom0917Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1609136640 : Int) atom0918Coded) (CoefficientMerge.scale (1344916800 : Int) atom0919Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1404100320 : Int) atom0920Coded) (CoefficientMerge.scale (2940756000 : Int) atom0921Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3706055520 : Int) atom0922Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5793806880 : Int) atom0923Coded) (CoefficientMerge.scale (8475644160 : Int) atom0924Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1725016320 : Int) atom0925Coded) (CoefficientMerge.scale (2334026880 : Int) atom0926Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2590296480 : Int) atom0927Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4993500960 : Int) atom0928Coded) (CoefficientMerge.scale (6174312480 : Int) atom0929Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7280074080 : Int) atom0930Coded) (CoefficientMerge.scale (12177524160 : Int) atom0931Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2643701760 : Int) atom0932Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5717445840 : Int) atom0933Coded) (CoefficientMerge.scale (11409847200 : Int) atom0934Coded))))))) := by
  rw [block012_data_flat078_step, block012_data_flat038_original, block012_data_flat077_original]
def block012_data_flat079 : CoefficientMerge.Poly := [(nat_lit 2499, Int.ofNat (nat_lit 12355259760))]
theorem block012_data_flat079_step : block012_data_flat079 = (CoefficientMerge.scale (12355259760 : Int) atom0935Coded) := by decide +kernel
theorem block012_data_flat079_original : block012_data_flat079 = (CoefficientMerge.scale (12355259760 : Int) atom0935Coded) := by
  rw [block012_data_flat079_step]
def block012_data_flat080 : CoefficientMerge.Poly := [(nat_lit 2500, Int.ofNat (nat_lit 9602218800))]
theorem block012_data_flat080_step : block012_data_flat080 = (CoefficientMerge.scale (9602218800 : Int) atom0936Coded) := by decide +kernel
theorem block012_data_flat080_original : block012_data_flat080 = (CoefficientMerge.scale (9602218800 : Int) atom0936Coded) := by
  rw [block012_data_flat080_step]
def block012_data_flat081 : CoefficientMerge.Poly := [(nat_lit 2499, Int.ofNat (nat_lit 12355259760)), (nat_lit 2500, Int.ofNat (nat_lit 9602218800))]
theorem block012_data_flat081_step : block012_data_flat081 = (CoefficientMerge.fastMerge block012_data_flat079 block012_data_flat080) := by decide +kernel
theorem block012_data_flat081_original : block012_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12355259760 : Int) atom0935Coded) (CoefficientMerge.scale (9602218800 : Int) atom0936Coded)) := by
  rw [block012_data_flat081_step, block012_data_flat079_original, block012_data_flat080_original]
def block012_data_flat082 : CoefficientMerge.Poly := [(nat_lit 2501, Int.ofNat (nat_lit 15732480240))]
theorem block012_data_flat082_step : block012_data_flat082 = (CoefficientMerge.scale (15732480240 : Int) atom0937Coded) := by decide +kernel
theorem block012_data_flat082_original : block012_data_flat082 = (CoefficientMerge.scale (15732480240 : Int) atom0937Coded) := by
  rw [block012_data_flat082_step]
def block012_data_flat083 : CoefficientMerge.Poly := [(nat_lit 2515, Int.ofNat (nat_lit 2227212288))]
theorem block012_data_flat083_step : block012_data_flat083 = (CoefficientMerge.scale (2227212288 : Int) atom0938Coded) := by decide +kernel
theorem block012_data_flat083_original : block012_data_flat083 = (CoefficientMerge.scale (2227212288 : Int) atom0938Coded) := by
  rw [block012_data_flat083_step]
def block012_data_flat084 : CoefficientMerge.Poly := [(nat_lit 2516, Int.ofNat (nat_lit 9005351400))]
theorem block012_data_flat084_step : block012_data_flat084 = (CoefficientMerge.scale (9005351400 : Int) atom0939Coded) := by decide +kernel
theorem block012_data_flat084_original : block012_data_flat084 = (CoefficientMerge.scale (9005351400 : Int) atom0939Coded) := by
  rw [block012_data_flat084_step]
def block012_data_flat085 : CoefficientMerge.Poly := [(nat_lit 2515, Int.ofNat (nat_lit 2227212288)), (nat_lit 2516, Int.ofNat (nat_lit 9005351400))]
theorem block012_data_flat085_step : block012_data_flat085 = (CoefficientMerge.fastMerge block012_data_flat083 block012_data_flat084) := by decide +kernel
theorem block012_data_flat085_original : block012_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2227212288 : Int) atom0938Coded) (CoefficientMerge.scale (9005351400 : Int) atom0939Coded)) := by
  rw [block012_data_flat085_step, block012_data_flat083_original, block012_data_flat084_original]
def block012_data_flat086 : CoefficientMerge.Poly := [(nat_lit 2501, Int.ofNat (nat_lit 15732480240)), (nat_lit 2515, Int.ofNat (nat_lit 2227212288)), (nat_lit 2516, Int.ofNat (nat_lit 9005351400))]
theorem block012_data_flat086_step : block012_data_flat086 = (CoefficientMerge.fastMerge block012_data_flat082 block012_data_flat085) := by decide +kernel
theorem block012_data_flat086_original : block012_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15732480240 : Int) atom0937Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2227212288 : Int) atom0938Coded) (CoefficientMerge.scale (9005351400 : Int) atom0939Coded))) := by
  rw [block012_data_flat086_step, block012_data_flat082_original, block012_data_flat085_original]
def block012_data_flat087 : CoefficientMerge.Poly := [(nat_lit 2499, Int.ofNat (nat_lit 12355259760)), (nat_lit 2500, Int.ofNat (nat_lit 9602218800)), (nat_lit 2501, Int.ofNat (nat_lit 15732480240)), (nat_lit 2515, Int.ofNat (nat_lit 2227212288)), (nat_lit 2516, Int.ofNat (nat_lit 9005351400))]
theorem block012_data_flat087_step : block012_data_flat087 = (CoefficientMerge.fastMerge block012_data_flat081 block012_data_flat086) := by decide +kernel
theorem block012_data_flat087_original : block012_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12355259760 : Int) atom0935Coded) (CoefficientMerge.scale (9602218800 : Int) atom0936Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15732480240 : Int) atom0937Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2227212288 : Int) atom0938Coded) (CoefficientMerge.scale (9005351400 : Int) atom0939Coded)))) := by
  rw [block012_data_flat087_step, block012_data_flat081_original, block012_data_flat086_original]
def block012_data_flat088 : CoefficientMerge.Poly := [(nat_lit 2517, Int.ofNat (nat_lit 10554219720))]
theorem block012_data_flat088_step : block012_data_flat088 = (CoefficientMerge.scale (10554219720 : Int) atom0940Coded) := by decide +kernel
theorem block012_data_flat088_original : block012_data_flat088 = (CoefficientMerge.scale (10554219720 : Int) atom0940Coded) := by
  rw [block012_data_flat088_step]
def block012_data_flat089 : CoefficientMerge.Poly := [(nat_lit 2518, Int.ofNat (nat_lit 8388355680))]
theorem block012_data_flat089_step : block012_data_flat089 = (CoefficientMerge.scale (8388355680 : Int) atom0941Coded) := by decide +kernel
theorem block012_data_flat089_original : block012_data_flat089 = (CoefficientMerge.scale (8388355680 : Int) atom0941Coded) := by
  rw [block012_data_flat089_step]
def block012_data_flat090 : CoefficientMerge.Poly := [(nat_lit 2517, Int.ofNat (nat_lit 10554219720)), (nat_lit 2518, Int.ofNat (nat_lit 8388355680))]
theorem block012_data_flat090_step : block012_data_flat090 = (CoefficientMerge.fastMerge block012_data_flat088 block012_data_flat089) := by decide +kernel
theorem block012_data_flat090_original : block012_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10554219720 : Int) atom0940Coded) (CoefficientMerge.scale (8388355680 : Int) atom0941Coded)) := by
  rw [block012_data_flat090_step, block012_data_flat088_original, block012_data_flat089_original]
def block012_data_flat091 : CoefficientMerge.Poly := [(nat_lit 2519, Int.ofNat (nat_lit 11756106540))]
theorem block012_data_flat091_step : block012_data_flat091 = (CoefficientMerge.scale (11756106540 : Int) atom0942Coded) := by decide +kernel
theorem block012_data_flat091_original : block012_data_flat091 = (CoefficientMerge.scale (11756106540 : Int) atom0942Coded) := by
  rw [block012_data_flat091_step]
def block012_data_flat092 : CoefficientMerge.Poly := [(nat_lit 2534, Int.ofNat (nat_lit 7560675000))]
theorem block012_data_flat092_step : block012_data_flat092 = (CoefficientMerge.scale (7560675000 : Int) atom0943Coded) := by decide +kernel
theorem block012_data_flat092_original : block012_data_flat092 = (CoefficientMerge.scale (7560675000 : Int) atom0943Coded) := by
  rw [block012_data_flat092_step]
def block012_data_flat093 : CoefficientMerge.Poly := [(nat_lit 2535, Int.ofNat (nat_lit 12812030280))]
theorem block012_data_flat093_step : block012_data_flat093 = (CoefficientMerge.scale (12812030280 : Int) atom0944Coded) := by decide +kernel
theorem block012_data_flat093_original : block012_data_flat093 = (CoefficientMerge.scale (12812030280 : Int) atom0944Coded) := by
  rw [block012_data_flat093_step]
def block012_data_flat094 : CoefficientMerge.Poly := [(nat_lit 2534, Int.ofNat (nat_lit 7560675000)), (nat_lit 2535, Int.ofNat (nat_lit 12812030280))]
theorem block012_data_flat094_step : block012_data_flat094 = (CoefficientMerge.fastMerge block012_data_flat092 block012_data_flat093) := by decide +kernel
theorem block012_data_flat094_original : block012_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7560675000 : Int) atom0943Coded) (CoefficientMerge.scale (12812030280 : Int) atom0944Coded)) := by
  rw [block012_data_flat094_step, block012_data_flat092_original, block012_data_flat093_original]
def block012_data_flat095 : CoefficientMerge.Poly := [(nat_lit 2519, Int.ofNat (nat_lit 11756106540)), (nat_lit 2534, Int.ofNat (nat_lit 7560675000)), (nat_lit 2535, Int.ofNat (nat_lit 12812030280))]
theorem block012_data_flat095_step : block012_data_flat095 = (CoefficientMerge.fastMerge block012_data_flat091 block012_data_flat094) := by decide +kernel
theorem block012_data_flat095_original : block012_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11756106540 : Int) atom0942Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7560675000 : Int) atom0943Coded) (CoefficientMerge.scale (12812030280 : Int) atom0944Coded))) := by
  rw [block012_data_flat095_step, block012_data_flat091_original, block012_data_flat094_original]
def block012_data_flat096 : CoefficientMerge.Poly := [(nat_lit 2517, Int.ofNat (nat_lit 10554219720)), (nat_lit 2518, Int.ofNat (nat_lit 8388355680)), (nat_lit 2519, Int.ofNat (nat_lit 11756106540)), (nat_lit 2534, Int.ofNat (nat_lit 7560675000)), (nat_lit 2535, Int.ofNat (nat_lit 12812030280))]
theorem block012_data_flat096_step : block012_data_flat096 = (CoefficientMerge.fastMerge block012_data_flat090 block012_data_flat095) := by decide +kernel
theorem block012_data_flat096_original : block012_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10554219720 : Int) atom0940Coded) (CoefficientMerge.scale (8388355680 : Int) atom0941Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11756106540 : Int) atom0942Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7560675000 : Int) atom0943Coded) (CoefficientMerge.scale (12812030280 : Int) atom0944Coded)))) := by
  rw [block012_data_flat096_step, block012_data_flat090_original, block012_data_flat095_original]
def block012_data_flat097 : CoefficientMerge.Poly := [(nat_lit 2499, Int.ofNat (nat_lit 12355259760)), (nat_lit 2500, Int.ofNat (nat_lit 9602218800)), (nat_lit 2501, Int.ofNat (nat_lit 15732480240)), (nat_lit 2515, Int.ofNat (nat_lit 2227212288)), (nat_lit 2516, Int.ofNat (nat_lit 9005351400)), (nat_lit 2517, Int.ofNat (nat_lit 10554219720)), (nat_lit 2518, Int.ofNat (nat_lit 8388355680)), (nat_lit 2519, Int.ofNat (nat_lit 11756106540)), (nat_lit 2534, Int.ofNat (nat_lit 7560675000)), (nat_lit 2535, Int.ofNat (nat_lit 12812030280))]
theorem block012_data_flat097_step : block012_data_flat097 = (CoefficientMerge.fastMerge block012_data_flat087 block012_data_flat096) := by decide +kernel
theorem block012_data_flat097_original : block012_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12355259760 : Int) atom0935Coded) (CoefficientMerge.scale (9602218800 : Int) atom0936Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15732480240 : Int) atom0937Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2227212288 : Int) atom0938Coded) (CoefficientMerge.scale (9005351400 : Int) atom0939Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10554219720 : Int) atom0940Coded) (CoefficientMerge.scale (8388355680 : Int) atom0941Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11756106540 : Int) atom0942Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7560675000 : Int) atom0943Coded) (CoefficientMerge.scale (12812030280 : Int) atom0944Coded))))) := by
  rw [block012_data_flat097_step, block012_data_flat087_original, block012_data_flat096_original]
def block012_data_flat098 : CoefficientMerge.Poly := [(nat_lit 2536, Int.ofNat (nat_lit 10325020320))]
theorem block012_data_flat098_step : block012_data_flat098 = (CoefficientMerge.scale (10325020320 : Int) atom0945Coded) := by decide +kernel
theorem block012_data_flat098_original : block012_data_flat098 = (CoefficientMerge.scale (10325020320 : Int) atom0945Coded) := by
  rw [block012_data_flat098_step]
def block012_data_flat099 : CoefficientMerge.Poly := [(nat_lit 2537, Int.ofNat (nat_lit 14890848480))]
theorem block012_data_flat099_step : block012_data_flat099 = (CoefficientMerge.scale (14890848480 : Int) atom0946Coded) := by decide +kernel
theorem block012_data_flat099_original : block012_data_flat099 = (CoefficientMerge.scale (14890848480 : Int) atom0946Coded) := by
  rw [block012_data_flat099_step]
def block012_data_flat100 : CoefficientMerge.Poly := [(nat_lit 2536, Int.ofNat (nat_lit 10325020320)), (nat_lit 2537, Int.ofNat (nat_lit 14890848480))]
theorem block012_data_flat100_step : block012_data_flat100 = (CoefficientMerge.fastMerge block012_data_flat098 block012_data_flat099) := by decide +kernel
theorem block012_data_flat100_original : block012_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10325020320 : Int) atom0945Coded) (CoefficientMerge.scale (14890848480 : Int) atom0946Coded)) := by
  rw [block012_data_flat100_step, block012_data_flat098_original, block012_data_flat099_original]
def block012_data_flat101 : CoefficientMerge.Poly := [(nat_lit 2553, Int.ofNat (nat_lit 3863096280))]
theorem block012_data_flat101_step : block012_data_flat101 = (CoefficientMerge.scale (3863096280 : Int) atom0947Coded) := by decide +kernel
theorem block012_data_flat101_original : block012_data_flat101 = (CoefficientMerge.scale (3863096280 : Int) atom0947Coded) := by
  rw [block012_data_flat101_step]
def block012_data_flat102 : CoefficientMerge.Poly := [(nat_lit 2554, Int.ofNat (nat_lit 6214863960))]
theorem block012_data_flat102_step : block012_data_flat102 = (CoefficientMerge.scale (6214863960 : Int) atom0948Coded) := by decide +kernel
theorem block012_data_flat102_original : block012_data_flat102 = (CoefficientMerge.scale (6214863960 : Int) atom0948Coded) := by
  rw [block012_data_flat102_step]
def block012_data_flat103 : CoefficientMerge.Poly := [(nat_lit 2555, Int.ofNat (nat_lit 11200519260))]
theorem block012_data_flat103_step : block012_data_flat103 = (CoefficientMerge.scale (11200519260 : Int) atom0949Coded) := by decide +kernel
theorem block012_data_flat103_original : block012_data_flat103 = (CoefficientMerge.scale (11200519260 : Int) atom0949Coded) := by
  rw [block012_data_flat103_step]
def block012_data_flat104 : CoefficientMerge.Poly := [(nat_lit 2554, Int.ofNat (nat_lit 6214863960)), (nat_lit 2555, Int.ofNat (nat_lit 11200519260))]
theorem block012_data_flat104_step : block012_data_flat104 = (CoefficientMerge.fastMerge block012_data_flat102 block012_data_flat103) := by decide +kernel
theorem block012_data_flat104_original : block012_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6214863960 : Int) atom0948Coded) (CoefficientMerge.scale (11200519260 : Int) atom0949Coded)) := by
  rw [block012_data_flat104_step, block012_data_flat102_original, block012_data_flat103_original]
def block012_data_flat105 : CoefficientMerge.Poly := [(nat_lit 2553, Int.ofNat (nat_lit 3863096280)), (nat_lit 2554, Int.ofNat (nat_lit 6214863960)), (nat_lit 2555, Int.ofNat (nat_lit 11200519260))]
theorem block012_data_flat105_step : block012_data_flat105 = (CoefficientMerge.fastMerge block012_data_flat101 block012_data_flat104) := by decide +kernel
theorem block012_data_flat105_original : block012_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3863096280 : Int) atom0947Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6214863960 : Int) atom0948Coded) (CoefficientMerge.scale (11200519260 : Int) atom0949Coded))) := by
  rw [block012_data_flat105_step, block012_data_flat101_original, block012_data_flat104_original]
def block012_data_flat106 : CoefficientMerge.Poly := [(nat_lit 2536, Int.ofNat (nat_lit 10325020320)), (nat_lit 2537, Int.ofNat (nat_lit 14890848480)), (nat_lit 2553, Int.ofNat (nat_lit 3863096280)), (nat_lit 2554, Int.ofNat (nat_lit 6214863960)), (nat_lit 2555, Int.ofNat (nat_lit 11200519260))]
theorem block012_data_flat106_step : block012_data_flat106 = (CoefficientMerge.fastMerge block012_data_flat100 block012_data_flat105) := by decide +kernel
theorem block012_data_flat106_original : block012_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10325020320 : Int) atom0945Coded) (CoefficientMerge.scale (14890848480 : Int) atom0946Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3863096280 : Int) atom0947Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6214863960 : Int) atom0948Coded) (CoefficientMerge.scale (11200519260 : Int) atom0949Coded)))) := by
  rw [block012_data_flat106_step, block012_data_flat100_original, block012_data_flat105_original]
def block012_data_flat107 : CoefficientMerge.Poly := [(nat_lit 2572, Int.ofNat (nat_lit 928467360))]
theorem block012_data_flat107_step : block012_data_flat107 = (CoefficientMerge.scale (928467360 : Int) atom0950Coded) := by decide +kernel
theorem block012_data_flat107_original : block012_data_flat107 = (CoefficientMerge.scale (928467360 : Int) atom0950Coded) := by
  rw [block012_data_flat107_step]
def block012_data_flat108 : CoefficientMerge.Poly := [(nat_lit 2573, Int.ofNat (nat_lit 7244896500))]
theorem block012_data_flat108_step : block012_data_flat108 = (CoefficientMerge.scale (7244896500 : Int) atom0951Coded) := by decide +kernel
theorem block012_data_flat108_original : block012_data_flat108 = (CoefficientMerge.scale (7244896500 : Int) atom0951Coded) := by
  rw [block012_data_flat108_step]
def block012_data_flat109 : CoefficientMerge.Poly := [(nat_lit 2572, Int.ofNat (nat_lit 928467360)), (nat_lit 2573, Int.ofNat (nat_lit 7244896500))]
theorem block012_data_flat109_step : block012_data_flat109 = (CoefficientMerge.fastMerge block012_data_flat107 block012_data_flat108) := by decide +kernel
theorem block012_data_flat109_original : block012_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (928467360 : Int) atom0950Coded) (CoefficientMerge.scale (7244896500 : Int) atom0951Coded)) := by
  rw [block012_data_flat109_step, block012_data_flat107_original, block012_data_flat108_original]
def block012_data_flat110 : CoefficientMerge.Poly := [(nat_lit 2591, Int.ofNat (nat_lit 5633486820))]
theorem block012_data_flat110_step : block012_data_flat110 = (CoefficientMerge.scale (5633486820 : Int) atom0952Coded) := by decide +kernel
theorem block012_data_flat110_original : block012_data_flat110 = (CoefficientMerge.scale (5633486820 : Int) atom0952Coded) := by
  rw [block012_data_flat110_step]
def block012_data_flat111 : CoefficientMerge.Poly := [(nat_lit 2744, Int.ofNat (nat_lit 114117120))]
theorem block012_data_flat111_step : block012_data_flat111 = (CoefficientMerge.scale (114117120 : Int) atom0953Coded) := by decide +kernel
theorem block012_data_flat111_original : block012_data_flat111 = (CoefficientMerge.scale (114117120 : Int) atom0953Coded) := by
  rw [block012_data_flat111_step]
def block012_data_flat112 : CoefficientMerge.Poly := [(nat_lit 2763, Int.ofNat (nat_lit 123425280))]
theorem block012_data_flat112_step : block012_data_flat112 = (CoefficientMerge.scale (123425280 : Int) atom0954Coded) := by decide +kernel
theorem block012_data_flat112_original : block012_data_flat112 = (CoefficientMerge.scale (123425280 : Int) atom0954Coded) := by
  rw [block012_data_flat112_step]
def block012_data_flat113 : CoefficientMerge.Poly := [(nat_lit 2744, Int.ofNat (nat_lit 114117120)), (nat_lit 2763, Int.ofNat (nat_lit 123425280))]
theorem block012_data_flat113_step : block012_data_flat113 = (CoefficientMerge.fastMerge block012_data_flat111 block012_data_flat112) := by decide +kernel
theorem block012_data_flat113_original : block012_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (114117120 : Int) atom0953Coded) (CoefficientMerge.scale (123425280 : Int) atom0954Coded)) := by
  rw [block012_data_flat113_step, block012_data_flat111_original, block012_data_flat112_original]
def block012_data_flat114 : CoefficientMerge.Poly := [(nat_lit 2591, Int.ofNat (nat_lit 5633486820)), (nat_lit 2744, Int.ofNat (nat_lit 114117120)), (nat_lit 2763, Int.ofNat (nat_lit 123425280))]
theorem block012_data_flat114_step : block012_data_flat114 = (CoefficientMerge.fastMerge block012_data_flat110 block012_data_flat113) := by decide +kernel
theorem block012_data_flat114_original : block012_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5633486820 : Int) atom0952Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114117120 : Int) atom0953Coded) (CoefficientMerge.scale (123425280 : Int) atom0954Coded))) := by
  rw [block012_data_flat114_step, block012_data_flat110_original, block012_data_flat113_original]
def block012_data_flat115 : CoefficientMerge.Poly := [(nat_lit 2572, Int.ofNat (nat_lit 928467360)), (nat_lit 2573, Int.ofNat (nat_lit 7244896500)), (nat_lit 2591, Int.ofNat (nat_lit 5633486820)), (nat_lit 2744, Int.ofNat (nat_lit 114117120)), (nat_lit 2763, Int.ofNat (nat_lit 123425280))]
theorem block012_data_flat115_step : block012_data_flat115 = (CoefficientMerge.fastMerge block012_data_flat109 block012_data_flat114) := by decide +kernel
theorem block012_data_flat115_original : block012_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (928467360 : Int) atom0950Coded) (CoefficientMerge.scale (7244896500 : Int) atom0951Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5633486820 : Int) atom0952Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114117120 : Int) atom0953Coded) (CoefficientMerge.scale (123425280 : Int) atom0954Coded)))) := by
  rw [block012_data_flat115_step, block012_data_flat109_original, block012_data_flat114_original]
def block012_data_flat116 : CoefficientMerge.Poly := [(nat_lit 2536, Int.ofNat (nat_lit 10325020320)), (nat_lit 2537, Int.ofNat (nat_lit 14890848480)), (nat_lit 2553, Int.ofNat (nat_lit 3863096280)), (nat_lit 2554, Int.ofNat (nat_lit 6214863960)), (nat_lit 2555, Int.ofNat (nat_lit 11200519260)), (nat_lit 2572, Int.ofNat (nat_lit 928467360)), (nat_lit 2573, Int.ofNat (nat_lit 7244896500)), (nat_lit 2591, Int.ofNat (nat_lit 5633486820)), (nat_lit 2744, Int.ofNat (nat_lit 114117120)), (nat_lit 2763, Int.ofNat (nat_lit 123425280))]
theorem block012_data_flat116_step : block012_data_flat116 = (CoefficientMerge.fastMerge block012_data_flat106 block012_data_flat115) := by decide +kernel
theorem block012_data_flat116_original : block012_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10325020320 : Int) atom0945Coded) (CoefficientMerge.scale (14890848480 : Int) atom0946Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3863096280 : Int) atom0947Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6214863960 : Int) atom0948Coded) (CoefficientMerge.scale (11200519260 : Int) atom0949Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (928467360 : Int) atom0950Coded) (CoefficientMerge.scale (7244896500 : Int) atom0951Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5633486820 : Int) atom0952Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114117120 : Int) atom0953Coded) (CoefficientMerge.scale (123425280 : Int) atom0954Coded))))) := by
  rw [block012_data_flat116_step, block012_data_flat106_original, block012_data_flat115_original]
def block012_data_flat117 : CoefficientMerge.Poly := [(nat_lit 2499, Int.ofNat (nat_lit 12355259760)), (nat_lit 2500, Int.ofNat (nat_lit 9602218800)), (nat_lit 2501, Int.ofNat (nat_lit 15732480240)), (nat_lit 2515, Int.ofNat (nat_lit 2227212288)), (nat_lit 2516, Int.ofNat (nat_lit 9005351400)), (nat_lit 2517, Int.ofNat (nat_lit 10554219720)), (nat_lit 2518, Int.ofNat (nat_lit 8388355680)), (nat_lit 2519, Int.ofNat (nat_lit 11756106540)), (nat_lit 2534, Int.ofNat (nat_lit 7560675000)), (nat_lit 2535, Int.ofNat (nat_lit 12812030280)), (nat_lit 2536, Int.ofNat (nat_lit 10325020320)), (nat_lit 2537, Int.ofNat (nat_lit 14890848480)), (nat_lit 2553, Int.ofNat (nat_lit 3863096280)), (nat_lit 2554, Int.ofNat (nat_lit 6214863960)), (nat_lit 2555, Int.ofNat (nat_lit 11200519260)), (nat_lit 2572, Int.ofNat (nat_lit 928467360)), (nat_lit 2573, Int.ofNat (nat_lit 7244896500)), (nat_lit 2591, Int.ofNat (nat_lit 5633486820)), (nat_lit 2744, Int.ofNat (nat_lit 114117120)), (nat_lit 2763, Int.ofNat (nat_lit 123425280))]
theorem block012_data_flat117_step : block012_data_flat117 = (CoefficientMerge.fastMerge block012_data_flat097 block012_data_flat116) := by decide +kernel
theorem block012_data_flat117_original : block012_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12355259760 : Int) atom0935Coded) (CoefficientMerge.scale (9602218800 : Int) atom0936Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15732480240 : Int) atom0937Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2227212288 : Int) atom0938Coded) (CoefficientMerge.scale (9005351400 : Int) atom0939Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10554219720 : Int) atom0940Coded) (CoefficientMerge.scale (8388355680 : Int) atom0941Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11756106540 : Int) atom0942Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7560675000 : Int) atom0943Coded) (CoefficientMerge.scale (12812030280 : Int) atom0944Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10325020320 : Int) atom0945Coded) (CoefficientMerge.scale (14890848480 : Int) atom0946Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3863096280 : Int) atom0947Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6214863960 : Int) atom0948Coded) (CoefficientMerge.scale (11200519260 : Int) atom0949Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (928467360 : Int) atom0950Coded) (CoefficientMerge.scale (7244896500 : Int) atom0951Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5633486820 : Int) atom0952Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114117120 : Int) atom0953Coded) (CoefficientMerge.scale (123425280 : Int) atom0954Coded)))))) := by
  rw [block012_data_flat117_step, block012_data_flat097_original, block012_data_flat116_original]
def block012_data_flat118 : CoefficientMerge.Poly := [(nat_lit 2765, Int.ofNat (nat_lit 103864320))]
theorem block012_data_flat118_step : block012_data_flat118 = (CoefficientMerge.scale (103864320 : Int) atom0955Coded) := by decide +kernel
theorem block012_data_flat118_original : block012_data_flat118 = (CoefficientMerge.scale (103864320 : Int) atom0955Coded) := by
  rw [block012_data_flat118_step]
def block012_data_flat119 : CoefficientMerge.Poly := [(nat_lit 2767, Int.ofNat (nat_lit 198804480))]
theorem block012_data_flat119_step : block012_data_flat119 = (CoefficientMerge.scale (198804480 : Int) atom0956Coded) := by decide +kernel
theorem block012_data_flat119_original : block012_data_flat119 = (CoefficientMerge.scale (198804480 : Int) atom0956Coded) := by
  rw [block012_data_flat119_step]
def block012_data_flat120 : CoefficientMerge.Poly := [(nat_lit 2765, Int.ofNat (nat_lit 103864320)), (nat_lit 2767, Int.ofNat (nat_lit 198804480))]
theorem block012_data_flat120_step : block012_data_flat120 = (CoefficientMerge.fastMerge block012_data_flat118 block012_data_flat119) := by decide +kernel
theorem block012_data_flat120_original : block012_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0955Coded) (CoefficientMerge.scale (198804480 : Int) atom0956Coded)) := by
  rw [block012_data_flat120_step, block012_data_flat118_original, block012_data_flat119_original]
def block012_data_flat121 : CoefficientMerge.Poly := [(nat_lit 2768, Int.ofNat (nat_lit 697544160))]
theorem block012_data_flat121_step : block012_data_flat121 = (CoefficientMerge.scale (697544160 : Int) atom0957Coded) := by decide +kernel
theorem block012_data_flat121_original : block012_data_flat121 = (CoefficientMerge.scale (697544160 : Int) atom0957Coded) := by
  rw [block012_data_flat121_step]
def block012_data_flat122 : CoefficientMerge.Poly := [(nat_lit 2769, Int.ofNat (nat_lit 1456949760))]
theorem block012_data_flat122_step : block012_data_flat122 = (CoefficientMerge.scale (1456949760 : Int) atom0958Coded) := by decide +kernel
theorem block012_data_flat122_original : block012_data_flat122 = (CoefficientMerge.scale (1456949760 : Int) atom0958Coded) := by
  rw [block012_data_flat122_step]
def block012_data_flat123 : CoefficientMerge.Poly := [(nat_lit 2770, Int.ofNat (nat_lit 2516290560))]
theorem block012_data_flat123_step : block012_data_flat123 = (CoefficientMerge.scale (2516290560 : Int) atom0959Coded) := by decide +kernel
theorem block012_data_flat123_original : block012_data_flat123 = (CoefficientMerge.scale (2516290560 : Int) atom0959Coded) := by
  rw [block012_data_flat123_step]
def block012_data_flat124 : CoefficientMerge.Poly := [(nat_lit 2769, Int.ofNat (nat_lit 1456949760)), (nat_lit 2770, Int.ofNat (nat_lit 2516290560))]
theorem block012_data_flat124_step : block012_data_flat124 = (CoefficientMerge.fastMerge block012_data_flat122 block012_data_flat123) := by decide +kernel
theorem block012_data_flat124_original : block012_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1456949760 : Int) atom0958Coded) (CoefficientMerge.scale (2516290560 : Int) atom0959Coded)) := by
  rw [block012_data_flat124_step, block012_data_flat122_original, block012_data_flat123_original]
def block012_data_flat125 : CoefficientMerge.Poly := [(nat_lit 2768, Int.ofNat (nat_lit 697544160)), (nat_lit 2769, Int.ofNat (nat_lit 1456949760)), (nat_lit 2770, Int.ofNat (nat_lit 2516290560))]
theorem block012_data_flat125_step : block012_data_flat125 = (CoefficientMerge.fastMerge block012_data_flat121 block012_data_flat124) := by decide +kernel
theorem block012_data_flat125_original : block012_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (697544160 : Int) atom0957Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1456949760 : Int) atom0958Coded) (CoefficientMerge.scale (2516290560 : Int) atom0959Coded))) := by
  rw [block012_data_flat125_step, block012_data_flat121_original, block012_data_flat124_original]
def block012_data_flat126 : CoefficientMerge.Poly := [(nat_lit 2765, Int.ofNat (nat_lit 103864320)), (nat_lit 2767, Int.ofNat (nat_lit 198804480)), (nat_lit 2768, Int.ofNat (nat_lit 697544160)), (nat_lit 2769, Int.ofNat (nat_lit 1456949760)), (nat_lit 2770, Int.ofNat (nat_lit 2516290560))]
theorem block012_data_flat126_step : block012_data_flat126 = (CoefficientMerge.fastMerge block012_data_flat120 block012_data_flat125) := by decide +kernel
theorem block012_data_flat126_original : block012_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0955Coded) (CoefficientMerge.scale (198804480 : Int) atom0956Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (697544160 : Int) atom0957Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1456949760 : Int) atom0958Coded) (CoefficientMerge.scale (2516290560 : Int) atom0959Coded)))) := by
  rw [block012_data_flat126_step, block012_data_flat120_original, block012_data_flat125_original]
def block012_data_flat127 : CoefficientMerge.Poly := [(nat_lit 2771, Int.ofNat (nat_lit 3703230720))]
theorem block012_data_flat127_step : block012_data_flat127 = (CoefficientMerge.scale (3703230720 : Int) atom0960Coded) := by decide +kernel
theorem block012_data_flat127_original : block012_data_flat127 = (CoefficientMerge.scale (3703230720 : Int) atom0960Coded) := by
  rw [block012_data_flat127_step]
def block012_data_flat128 : CoefficientMerge.Poly := [(nat_lit 2782, Int.ofNat (nat_lit 446215680))]
theorem block012_data_flat128_step : block012_data_flat128 = (CoefficientMerge.scale (446215680 : Int) atom0961Coded) := by decide +kernel
theorem block012_data_flat128_original : block012_data_flat128 = (CoefficientMerge.scale (446215680 : Int) atom0961Coded) := by
  rw [block012_data_flat128_step]
def block012_data_flat129 : CoefficientMerge.Poly := [(nat_lit 2771, Int.ofNat (nat_lit 3703230720)), (nat_lit 2782, Int.ofNat (nat_lit 446215680))]
theorem block012_data_flat129_step : block012_data_flat129 = (CoefficientMerge.fastMerge block012_data_flat127 block012_data_flat128) := by decide +kernel
theorem block012_data_flat129_original : block012_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3703230720 : Int) atom0960Coded) (CoefficientMerge.scale (446215680 : Int) atom0961Coded)) := by
  rw [block012_data_flat129_step, block012_data_flat127_original, block012_data_flat128_original]
def block012_data_flat130 : CoefficientMerge.Poly := [(nat_lit 2783, Int.ofNat (nat_lit 715852800))]
theorem block012_data_flat130_step : block012_data_flat130 = (CoefficientMerge.scale (715852800 : Int) atom0962Coded) := by decide +kernel
theorem block012_data_flat130_original : block012_data_flat130 = (CoefficientMerge.scale (715852800 : Int) atom0962Coded) := by
  rw [block012_data_flat130_step]
def block012_data_flat131 : CoefficientMerge.Poly := [(nat_lit 2784, Int.ofNat (nat_lit 34334208))]
theorem block012_data_flat131_step : block012_data_flat131 = (CoefficientMerge.scale (34334208 : Int) atom0963Coded) := by decide +kernel
theorem block012_data_flat131_original : block012_data_flat131 = (CoefficientMerge.scale (34334208 : Int) atom0963Coded) := by
  rw [block012_data_flat131_step]
def block012_data_flat132 : CoefficientMerge.Poly := [(nat_lit 2786, Int.ofNat (nat_lit 1546800480))]
theorem block012_data_flat132_step : block012_data_flat132 = (CoefficientMerge.scale (1546800480 : Int) atom0964Coded) := by decide +kernel
theorem block012_data_flat132_original : block012_data_flat132 = (CoefficientMerge.scale (1546800480 : Int) atom0964Coded) := by
  rw [block012_data_flat132_step]
def block012_data_flat133 : CoefficientMerge.Poly := [(nat_lit 2784, Int.ofNat (nat_lit 34334208)), (nat_lit 2786, Int.ofNat (nat_lit 1546800480))]
theorem block012_data_flat133_step : block012_data_flat133 = (CoefficientMerge.fastMerge block012_data_flat131 block012_data_flat132) := by decide +kernel
theorem block012_data_flat133_original : block012_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34334208 : Int) atom0963Coded) (CoefficientMerge.scale (1546800480 : Int) atom0964Coded)) := by
  rw [block012_data_flat133_step, block012_data_flat131_original, block012_data_flat132_original]
def block012_data_flat134 : CoefficientMerge.Poly := [(nat_lit 2783, Int.ofNat (nat_lit 715852800)), (nat_lit 2784, Int.ofNat (nat_lit 34334208)), (nat_lit 2786, Int.ofNat (nat_lit 1546800480))]
theorem block012_data_flat134_step : block012_data_flat134 = (CoefficientMerge.fastMerge block012_data_flat130 block012_data_flat133) := by decide +kernel
theorem block012_data_flat134_original : block012_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (715852800 : Int) atom0962Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34334208 : Int) atom0963Coded) (CoefficientMerge.scale (1546800480 : Int) atom0964Coded))) := by
  rw [block012_data_flat134_step, block012_data_flat130_original, block012_data_flat133_original]
def block012_data_flat135 : CoefficientMerge.Poly := [(nat_lit 2771, Int.ofNat (nat_lit 3703230720)), (nat_lit 2782, Int.ofNat (nat_lit 446215680)), (nat_lit 2783, Int.ofNat (nat_lit 715852800)), (nat_lit 2784, Int.ofNat (nat_lit 34334208)), (nat_lit 2786, Int.ofNat (nat_lit 1546800480))]
theorem block012_data_flat135_step : block012_data_flat135 = (CoefficientMerge.fastMerge block012_data_flat129 block012_data_flat134) := by decide +kernel
theorem block012_data_flat135_original : block012_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3703230720 : Int) atom0960Coded) (CoefficientMerge.scale (446215680 : Int) atom0961Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (715852800 : Int) atom0962Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34334208 : Int) atom0963Coded) (CoefficientMerge.scale (1546800480 : Int) atom0964Coded)))) := by
  rw [block012_data_flat135_step, block012_data_flat129_original, block012_data_flat134_original]
def block012_data_flat136 : CoefficientMerge.Poly := [(nat_lit 2765, Int.ofNat (nat_lit 103864320)), (nat_lit 2767, Int.ofNat (nat_lit 198804480)), (nat_lit 2768, Int.ofNat (nat_lit 697544160)), (nat_lit 2769, Int.ofNat (nat_lit 1456949760)), (nat_lit 2770, Int.ofNat (nat_lit 2516290560)), (nat_lit 2771, Int.ofNat (nat_lit 3703230720)), (nat_lit 2782, Int.ofNat (nat_lit 446215680)), (nat_lit 2783, Int.ofNat (nat_lit 715852800)), (nat_lit 2784, Int.ofNat (nat_lit 34334208)), (nat_lit 2786, Int.ofNat (nat_lit 1546800480))]
theorem block012_data_flat136_step : block012_data_flat136 = (CoefficientMerge.fastMerge block012_data_flat126 block012_data_flat135) := by decide +kernel
theorem block012_data_flat136_original : block012_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0955Coded) (CoefficientMerge.scale (198804480 : Int) atom0956Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (697544160 : Int) atom0957Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1456949760 : Int) atom0958Coded) (CoefficientMerge.scale (2516290560 : Int) atom0959Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3703230720 : Int) atom0960Coded) (CoefficientMerge.scale (446215680 : Int) atom0961Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (715852800 : Int) atom0962Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34334208 : Int) atom0963Coded) (CoefficientMerge.scale (1546800480 : Int) atom0964Coded))))) := by
  rw [block012_data_flat136_step, block012_data_flat126_original, block012_data_flat135_original]
def block012_data_flat137 : CoefficientMerge.Poly := [(nat_lit 2787, Int.ofNat (nat_lit 1968756480))]
theorem block012_data_flat137_step : block012_data_flat137 = (CoefficientMerge.scale (1968756480 : Int) atom0965Coded) := by decide +kernel
theorem block012_data_flat137_original : block012_data_flat137 = (CoefficientMerge.scale (1968756480 : Int) atom0965Coded) := by
  rw [block012_data_flat137_step]
def block012_data_flat138 : CoefficientMerge.Poly := [(nat_lit 2788, Int.ofNat (nat_lit 3971847168))]
theorem block012_data_flat138_step : block012_data_flat138 = (CoefficientMerge.scale (3971847168 : Int) atom0966Coded) := by decide +kernel
theorem block012_data_flat138_original : block012_data_flat138 = (CoefficientMerge.scale (3971847168 : Int) atom0966Coded) := by
  rw [block012_data_flat138_step]
def block012_data_flat139 : CoefficientMerge.Poly := [(nat_lit 2787, Int.ofNat (nat_lit 1968756480)), (nat_lit 2788, Int.ofNat (nat_lit 3971847168))]
theorem block012_data_flat139_step : block012_data_flat139 = (CoefficientMerge.fastMerge block012_data_flat137 block012_data_flat138) := by decide +kernel
theorem block012_data_flat139_original : block012_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1968756480 : Int) atom0965Coded) (CoefficientMerge.scale (3971847168 : Int) atom0966Coded)) := by
  rw [block012_data_flat139_step, block012_data_flat137_original, block012_data_flat138_original]
def block012_data_flat140 : CoefficientMerge.Poly := [(nat_lit 2789, Int.ofNat (nat_lit 6637222080))]
theorem block012_data_flat140_step : block012_data_flat140 = (CoefficientMerge.scale (6637222080 : Int) atom0967Coded) := by decide +kernel
theorem block012_data_flat140_original : block012_data_flat140 = (CoefficientMerge.scale (6637222080 : Int) atom0967Coded) := by
  rw [block012_data_flat140_step]
def block012_data_flat141 : CoefficientMerge.Poly := [(nat_lit 2801, Int.ofNat (nat_lit 1172897280))]
theorem block012_data_flat141_step : block012_data_flat141 = (CoefficientMerge.scale (1172897280 : Int) atom0968Coded) := by decide +kernel
theorem block012_data_flat141_original : block012_data_flat141 = (CoefficientMerge.scale (1172897280 : Int) atom0968Coded) := by
  rw [block012_data_flat141_step]
def block012_data_flat142 : CoefficientMerge.Poly := [(nat_lit 2802, Int.ofNat (nat_lit 947796480))]
theorem block012_data_flat142_step : block012_data_flat142 = (CoefficientMerge.scale (947796480 : Int) atom0969Coded) := by decide +kernel
theorem block012_data_flat142_original : block012_data_flat142 = (CoefficientMerge.scale (947796480 : Int) atom0969Coded) := by
  rw [block012_data_flat142_step]
def block012_data_flat143 : CoefficientMerge.Poly := [(nat_lit 2801, Int.ofNat (nat_lit 1172897280)), (nat_lit 2802, Int.ofNat (nat_lit 947796480))]
theorem block012_data_flat143_step : block012_data_flat143 = (CoefficientMerge.fastMerge block012_data_flat141 block012_data_flat142) := by decide +kernel
theorem block012_data_flat143_original : block012_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1172897280 : Int) atom0968Coded) (CoefficientMerge.scale (947796480 : Int) atom0969Coded)) := by
  rw [block012_data_flat143_step, block012_data_flat141_original, block012_data_flat142_original]
def block012_data_flat144 : CoefficientMerge.Poly := [(nat_lit 2789, Int.ofNat (nat_lit 6637222080)), (nat_lit 2801, Int.ofNat (nat_lit 1172897280)), (nat_lit 2802, Int.ofNat (nat_lit 947796480))]
theorem block012_data_flat144_step : block012_data_flat144 = (CoefficientMerge.fastMerge block012_data_flat140 block012_data_flat143) := by decide +kernel
theorem block012_data_flat144_original : block012_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6637222080 : Int) atom0967Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1172897280 : Int) atom0968Coded) (CoefficientMerge.scale (947796480 : Int) atom0969Coded))) := by
  rw [block012_data_flat144_step, block012_data_flat140_original, block012_data_flat143_original]
def block012_data_flat145 : CoefficientMerge.Poly := [(nat_lit 2787, Int.ofNat (nat_lit 1968756480)), (nat_lit 2788, Int.ofNat (nat_lit 3971847168)), (nat_lit 2789, Int.ofNat (nat_lit 6637222080)), (nat_lit 2801, Int.ofNat (nat_lit 1172897280)), (nat_lit 2802, Int.ofNat (nat_lit 947796480))]
theorem block012_data_flat145_step : block012_data_flat145 = (CoefficientMerge.fastMerge block012_data_flat139 block012_data_flat144) := by decide +kernel
theorem block012_data_flat145_original : block012_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1968756480 : Int) atom0965Coded) (CoefficientMerge.scale (3971847168 : Int) atom0966Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6637222080 : Int) atom0967Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1172897280 : Int) atom0968Coded) (CoefficientMerge.scale (947796480 : Int) atom0969Coded)))) := by
  rw [block012_data_flat145_step, block012_data_flat139_original, block012_data_flat144_original]
def block012_data_flat146 : CoefficientMerge.Poly := [(nat_lit 2803, Int.ofNat (nat_lit 1267307520))]
theorem block012_data_flat146_step : block012_data_flat146 = (CoefficientMerge.scale (1267307520 : Int) atom0970Coded) := by decide +kernel
theorem block012_data_flat146_original : block012_data_flat146 = (CoefficientMerge.scale (1267307520 : Int) atom0970Coded) := by
  rw [block012_data_flat146_step]
def block012_data_flat147 : CoefficientMerge.Poly := [(nat_lit 2804, Int.ofNat (nat_lit 3880321440))]
theorem block012_data_flat147_step : block012_data_flat147 = (CoefficientMerge.scale (3880321440 : Int) atom0971Coded) := by decide +kernel
theorem block012_data_flat147_original : block012_data_flat147 = (CoefficientMerge.scale (3880321440 : Int) atom0971Coded) := by
  rw [block012_data_flat147_step]
def block012_data_flat148 : CoefficientMerge.Poly := [(nat_lit 2803, Int.ofNat (nat_lit 1267307520)), (nat_lit 2804, Int.ofNat (nat_lit 3880321440))]
theorem block012_data_flat148_step : block012_data_flat148 = (CoefficientMerge.fastMerge block012_data_flat146 block012_data_flat147) := by decide +kernel
theorem block012_data_flat148_original : block012_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1267307520 : Int) atom0970Coded) (CoefficientMerge.scale (3880321440 : Int) atom0971Coded)) := by
  rw [block012_data_flat148_step, block012_data_flat146_original, block012_data_flat147_original]
def block012_data_flat149 : CoefficientMerge.Poly := [(nat_lit 2805, Int.ofNat (nat_lit 4842781440))]
theorem block012_data_flat149_step : block012_data_flat149 = (CoefficientMerge.scale (4842781440 : Int) atom0972Coded) := by decide +kernel
theorem block012_data_flat149_original : block012_data_flat149 = (CoefficientMerge.scale (4842781440 : Int) atom0972Coded) := by
  rw [block012_data_flat149_step]
def block012_data_flat150 : CoefficientMerge.Poly := [(nat_lit 2806, Int.ofNat (nat_lit 6031779840))]
theorem block012_data_flat150_step : block012_data_flat150 = (CoefficientMerge.scale (6031779840 : Int) atom0973Coded) := by decide +kernel
theorem block012_data_flat150_original : block012_data_flat150 = (CoefficientMerge.scale (6031779840 : Int) atom0973Coded) := by
  rw [block012_data_flat150_step]
def block012_data_flat151 : CoefficientMerge.Poly := [(nat_lit 2807, Int.ofNat (nat_lit 11064781440))]
theorem block012_data_flat151_step : block012_data_flat151 = (CoefficientMerge.scale (11064781440 : Int) atom0974Coded) := by decide +kernel
theorem block012_data_flat151_original : block012_data_flat151 = (CoefficientMerge.scale (11064781440 : Int) atom0974Coded) := by
  rw [block012_data_flat151_step]
def block012_data_flat152 : CoefficientMerge.Poly := [(nat_lit 2806, Int.ofNat (nat_lit 6031779840)), (nat_lit 2807, Int.ofNat (nat_lit 11064781440))]
theorem block012_data_flat152_step : block012_data_flat152 = (CoefficientMerge.fastMerge block012_data_flat150 block012_data_flat151) := by decide +kernel
theorem block012_data_flat152_original : block012_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031779840 : Int) atom0973Coded) (CoefficientMerge.scale (11064781440 : Int) atom0974Coded)) := by
  rw [block012_data_flat152_step, block012_data_flat150_original, block012_data_flat151_original]
def block012_data_flat153 : CoefficientMerge.Poly := [(nat_lit 2805, Int.ofNat (nat_lit 4842781440)), (nat_lit 2806, Int.ofNat (nat_lit 6031779840)), (nat_lit 2807, Int.ofNat (nat_lit 11064781440))]
theorem block012_data_flat153_step : block012_data_flat153 = (CoefficientMerge.fastMerge block012_data_flat149 block012_data_flat152) := by decide +kernel
theorem block012_data_flat153_original : block012_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4842781440 : Int) atom0972Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031779840 : Int) atom0973Coded) (CoefficientMerge.scale (11064781440 : Int) atom0974Coded))) := by
  rw [block012_data_flat153_step, block012_data_flat149_original, block012_data_flat152_original]
def block012_data_flat154 : CoefficientMerge.Poly := [(nat_lit 2803, Int.ofNat (nat_lit 1267307520)), (nat_lit 2804, Int.ofNat (nat_lit 3880321440)), (nat_lit 2805, Int.ofNat (nat_lit 4842781440)), (nat_lit 2806, Int.ofNat (nat_lit 6031779840)), (nat_lit 2807, Int.ofNat (nat_lit 11064781440))]
theorem block012_data_flat154_step : block012_data_flat154 = (CoefficientMerge.fastMerge block012_data_flat148 block012_data_flat153) := by decide +kernel
theorem block012_data_flat154_original : block012_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1267307520 : Int) atom0970Coded) (CoefficientMerge.scale (3880321440 : Int) atom0971Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4842781440 : Int) atom0972Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031779840 : Int) atom0973Coded) (CoefficientMerge.scale (11064781440 : Int) atom0974Coded)))) := by
  rw [block012_data_flat154_step, block012_data_flat148_original, block012_data_flat153_original]
def block012_data_flat155 : CoefficientMerge.Poly := [(nat_lit 2787, Int.ofNat (nat_lit 1968756480)), (nat_lit 2788, Int.ofNat (nat_lit 3971847168)), (nat_lit 2789, Int.ofNat (nat_lit 6637222080)), (nat_lit 2801, Int.ofNat (nat_lit 1172897280)), (nat_lit 2802, Int.ofNat (nat_lit 947796480)), (nat_lit 2803, Int.ofNat (nat_lit 1267307520)), (nat_lit 2804, Int.ofNat (nat_lit 3880321440)), (nat_lit 2805, Int.ofNat (nat_lit 4842781440)), (nat_lit 2806, Int.ofNat (nat_lit 6031779840)), (nat_lit 2807, Int.ofNat (nat_lit 11064781440))]
theorem block012_data_flat155_step : block012_data_flat155 = (CoefficientMerge.fastMerge block012_data_flat145 block012_data_flat154) := by decide +kernel
theorem block012_data_flat155_original : block012_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1968756480 : Int) atom0965Coded) (CoefficientMerge.scale (3971847168 : Int) atom0966Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6637222080 : Int) atom0967Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1172897280 : Int) atom0968Coded) (CoefficientMerge.scale (947796480 : Int) atom0969Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1267307520 : Int) atom0970Coded) (CoefficientMerge.scale (3880321440 : Int) atom0971Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4842781440 : Int) atom0972Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031779840 : Int) atom0973Coded) (CoefficientMerge.scale (11064781440 : Int) atom0974Coded))))) := by
  rw [block012_data_flat155_step, block012_data_flat145_original, block012_data_flat154_original]
def block012_data_flat156 : CoefficientMerge.Poly := [(nat_lit 2765, Int.ofNat (nat_lit 103864320)), (nat_lit 2767, Int.ofNat (nat_lit 198804480)), (nat_lit 2768, Int.ofNat (nat_lit 697544160)), (nat_lit 2769, Int.ofNat (nat_lit 1456949760)), (nat_lit 2770, Int.ofNat (nat_lit 2516290560)), (nat_lit 2771, Int.ofNat (nat_lit 3703230720)), (nat_lit 2782, Int.ofNat (nat_lit 446215680)), (nat_lit 2783, Int.ofNat (nat_lit 715852800)), (nat_lit 2784, Int.ofNat (nat_lit 34334208)), (nat_lit 2786, Int.ofNat (nat_lit 1546800480)), (nat_lit 2787, Int.ofNat (nat_lit 1968756480)), (nat_lit 2788, Int.ofNat (nat_lit 3971847168)), (nat_lit 2789, Int.ofNat (nat_lit 6637222080)), (nat_lit 2801, Int.ofNat (nat_lit 1172897280)), (nat_lit 2802, Int.ofNat (nat_lit 947796480)), (nat_lit 2803, Int.ofNat (nat_lit 1267307520)), (nat_lit 2804, Int.ofNat (nat_lit 3880321440)), (nat_lit 2805, Int.ofNat (nat_lit 4842781440)), (nat_lit 2806, Int.ofNat (nat_lit 6031779840)), (nat_lit 2807, Int.ofNat (nat_lit 11064781440))]
theorem block012_data_flat156_step : block012_data_flat156 = (CoefficientMerge.fastMerge block012_data_flat136 block012_data_flat155) := by decide +kernel
theorem block012_data_flat156_original : block012_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0955Coded) (CoefficientMerge.scale (198804480 : Int) atom0956Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (697544160 : Int) atom0957Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1456949760 : Int) atom0958Coded) (CoefficientMerge.scale (2516290560 : Int) atom0959Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3703230720 : Int) atom0960Coded) (CoefficientMerge.scale (446215680 : Int) atom0961Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (715852800 : Int) atom0962Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34334208 : Int) atom0963Coded) (CoefficientMerge.scale (1546800480 : Int) atom0964Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1968756480 : Int) atom0965Coded) (CoefficientMerge.scale (3971847168 : Int) atom0966Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6637222080 : Int) atom0967Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1172897280 : Int) atom0968Coded) (CoefficientMerge.scale (947796480 : Int) atom0969Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1267307520 : Int) atom0970Coded) (CoefficientMerge.scale (3880321440 : Int) atom0971Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4842781440 : Int) atom0972Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031779840 : Int) atom0973Coded) (CoefficientMerge.scale (11064781440 : Int) atom0974Coded)))))) := by
  rw [block012_data_flat156_step, block012_data_flat136_original, block012_data_flat155_original]
def block012_data_flat157 : CoefficientMerge.Poly := [(nat_lit 2499, Int.ofNat (nat_lit 12355259760)), (nat_lit 2500, Int.ofNat (nat_lit 9602218800)), (nat_lit 2501, Int.ofNat (nat_lit 15732480240)), (nat_lit 2515, Int.ofNat (nat_lit 2227212288)), (nat_lit 2516, Int.ofNat (nat_lit 9005351400)), (nat_lit 2517, Int.ofNat (nat_lit 10554219720)), (nat_lit 2518, Int.ofNat (nat_lit 8388355680)), (nat_lit 2519, Int.ofNat (nat_lit 11756106540)), (nat_lit 2534, Int.ofNat (nat_lit 7560675000)), (nat_lit 2535, Int.ofNat (nat_lit 12812030280)), (nat_lit 2536, Int.ofNat (nat_lit 10325020320)), (nat_lit 2537, Int.ofNat (nat_lit 14890848480)), (nat_lit 2553, Int.ofNat (nat_lit 3863096280)), (nat_lit 2554, Int.ofNat (nat_lit 6214863960)), (nat_lit 2555, Int.ofNat (nat_lit 11200519260)), (nat_lit 2572, Int.ofNat (nat_lit 928467360)), (nat_lit 2573, Int.ofNat (nat_lit 7244896500)), (nat_lit 2591, Int.ofNat (nat_lit 5633486820)), (nat_lit 2744, Int.ofNat (nat_lit 114117120)), (nat_lit 2763, Int.ofNat (nat_lit 123425280)), (nat_lit 2765, Int.ofNat (nat_lit 103864320)), (nat_lit 2767, Int.ofNat (nat_lit 198804480)), (nat_lit 2768, Int.ofNat (nat_lit 697544160)), (nat_lit 2769, Int.ofNat (nat_lit 1456949760)), (nat_lit 2770, Int.ofNat (nat_lit 2516290560)), (nat_lit 2771, Int.ofNat (nat_lit 3703230720)), (nat_lit 2782, Int.ofNat (nat_lit 446215680)), (nat_lit 2783, Int.ofNat (nat_lit 715852800)), (nat_lit 2784, Int.ofNat (nat_lit 34334208)), (nat_lit 2786, Int.ofNat (nat_lit 1546800480)), (nat_lit 2787, Int.ofNat (nat_lit 1968756480)), (nat_lit 2788, Int.ofNat (nat_lit 3971847168)), (nat_lit 2789, Int.ofNat (nat_lit 6637222080)), (nat_lit 2801, Int.ofNat (nat_lit 1172897280)), (nat_lit 2802, Int.ofNat (nat_lit 947796480)), (nat_lit 2803, Int.ofNat (nat_lit 1267307520)), (nat_lit 2804, Int.ofNat (nat_lit 3880321440)), (nat_lit 2805, Int.ofNat (nat_lit 4842781440)), (nat_lit 2806, Int.ofNat (nat_lit 6031779840)), (nat_lit 2807, Int.ofNat (nat_lit 11064781440))]
theorem block012_data_flat157_step : block012_data_flat157 = (CoefficientMerge.fastMerge block012_data_flat117 block012_data_flat156) := by decide +kernel
theorem block012_data_flat157_original : block012_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12355259760 : Int) atom0935Coded) (CoefficientMerge.scale (9602218800 : Int) atom0936Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15732480240 : Int) atom0937Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2227212288 : Int) atom0938Coded) (CoefficientMerge.scale (9005351400 : Int) atom0939Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10554219720 : Int) atom0940Coded) (CoefficientMerge.scale (8388355680 : Int) atom0941Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11756106540 : Int) atom0942Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7560675000 : Int) atom0943Coded) (CoefficientMerge.scale (12812030280 : Int) atom0944Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10325020320 : Int) atom0945Coded) (CoefficientMerge.scale (14890848480 : Int) atom0946Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3863096280 : Int) atom0947Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6214863960 : Int) atom0948Coded) (CoefficientMerge.scale (11200519260 : Int) atom0949Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (928467360 : Int) atom0950Coded) (CoefficientMerge.scale (7244896500 : Int) atom0951Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5633486820 : Int) atom0952Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114117120 : Int) atom0953Coded) (CoefficientMerge.scale (123425280 : Int) atom0954Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0955Coded) (CoefficientMerge.scale (198804480 : Int) atom0956Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (697544160 : Int) atom0957Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1456949760 : Int) atom0958Coded) (CoefficientMerge.scale (2516290560 : Int) atom0959Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3703230720 : Int) atom0960Coded) (CoefficientMerge.scale (446215680 : Int) atom0961Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (715852800 : Int) atom0962Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34334208 : Int) atom0963Coded) (CoefficientMerge.scale (1546800480 : Int) atom0964Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1968756480 : Int) atom0965Coded) (CoefficientMerge.scale (3971847168 : Int) atom0966Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6637222080 : Int) atom0967Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1172897280 : Int) atom0968Coded) (CoefficientMerge.scale (947796480 : Int) atom0969Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1267307520 : Int) atom0970Coded) (CoefficientMerge.scale (3880321440 : Int) atom0971Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4842781440 : Int) atom0972Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031779840 : Int) atom0973Coded) (CoefficientMerge.scale (11064781440 : Int) atom0974Coded))))))) := by
  rw [block012_data_flat157_step, block012_data_flat117_original, block012_data_flat156_original]
def block012_data_flat158 : CoefficientMerge.Poly := [(nat_lit 2248, Int.ofNat (nat_lit 182136240)), (nat_lit 2249, Int.ofNat (nat_lit 5136502230)), (nat_lit 2267, Int.ofNat (nat_lit 4373859870)), (nat_lit 2401, Int.ofNat (nat_lit 154863360)), (nat_lit 2402, Int.ofNat (nat_lit 78704640)), (nat_lit 2406, Int.ofNat (nat_lit 155020320)), (nat_lit 2420, Int.ofNat (nat_lit 158595840)), (nat_lit 2422, Int.ofNat (nat_lit 103864320)), (nat_lit 2423, Int.ofNat (nat_lit 207728640)), (nat_lit 2424, Int.ofNat (nat_lit 87669792)), (nat_lit 2427, Int.ofNat (nat_lit 1180247040)), (nat_lit 2428, Int.ofNat (nat_lit 2293143552)), (nat_lit 2429, Int.ofNat (nat_lit 3586383360)), (nat_lit 2439, Int.ofNat (nat_lit 411045120)), (nat_lit 2440, Int.ofNat (nat_lit 628784640)), (nat_lit 2441, Int.ofNat (nat_lit 786193920)), (nat_lit 2442, Int.ofNat (nat_lit 232689600)), (nat_lit 2443, Int.ofNat (nat_lit 13607520)), (nat_lit 2444, Int.ofNat (nat_lit 701867040)), (nat_lit 2445, Int.ofNat (nat_lit 1929608160)), (nat_lit 2446, Int.ofNat (nat_lit 3909670560)), (nat_lit 2447, Int.ofNat (nat_lit 6267332160)), (nat_lit 2458, Int.ofNat (nat_lit 891244800)), (nat_lit 2459, Int.ofNat (nat_lit 1609136640)), (nat_lit 2460, Int.ofNat (nat_lit 1344916800)), (nat_lit 2461, Int.ofNat (nat_lit 1404100320)), (nat_lit 2462, Int.ofNat (nat_lit 2940756000)), (nat_lit 2463, Int.ofNat (nat_lit 3706055520)), (nat_lit 2464, Int.ofNat (nat_lit 5793806880)), (nat_lit 2465, Int.ofNat (nat_lit 8475644160)), (nat_lit 2477, Int.ofNat (nat_lit 1725016320)), (nat_lit 2478, Int.ofNat (nat_lit 2334026880)), (nat_lit 2479, Int.ofNat (nat_lit 2590296480)), (nat_lit 2480, Int.ofNat (nat_lit 4993500960)), (nat_lit 2481, Int.ofNat (nat_lit 6174312480)), (nat_lit 2482, Int.ofNat (nat_lit 7280074080)), (nat_lit 2483, Int.ofNat (nat_lit 12177524160)), (nat_lit 2496, Int.ofNat (nat_lit 2643701760)), (nat_lit 2497, Int.ofNat (nat_lit 5717445840)), (nat_lit 2498, Int.ofNat (nat_lit 11409847200)), (nat_lit 2499, Int.ofNat (nat_lit 12355259760)), (nat_lit 2500, Int.ofNat (nat_lit 9602218800)), (nat_lit 2501, Int.ofNat (nat_lit 15732480240)), (nat_lit 2515, Int.ofNat (nat_lit 2227212288)), (nat_lit 2516, Int.ofNat (nat_lit 9005351400)), (nat_lit 2517, Int.ofNat (nat_lit 10554219720)), (nat_lit 2518, Int.ofNat (nat_lit 8388355680)), (nat_lit 2519, Int.ofNat (nat_lit 11756106540)), (nat_lit 2534, Int.ofNat (nat_lit 7560675000)), (nat_lit 2535, Int.ofNat (nat_lit 12812030280)), (nat_lit 2536, Int.ofNat (nat_lit 10325020320)), (nat_lit 2537, Int.ofNat (nat_lit 14890848480)), (nat_lit 2553, Int.ofNat (nat_lit 3863096280)), (nat_lit 2554, Int.ofNat (nat_lit 6214863960)), (nat_lit 2555, Int.ofNat (nat_lit 11200519260)), (nat_lit 2572, Int.ofNat (nat_lit 928467360)), (nat_lit 2573, Int.ofNat (nat_lit 7244896500)), (nat_lit 2591, Int.ofNat (nat_lit 5633486820)), (nat_lit 2744, Int.ofNat (nat_lit 114117120)), (nat_lit 2763, Int.ofNat (nat_lit 123425280)), (nat_lit 2765, Int.ofNat (nat_lit 103864320)), (nat_lit 2767, Int.ofNat (nat_lit 198804480)), (nat_lit 2768, Int.ofNat (nat_lit 697544160)), (nat_lit 2769, Int.ofNat (nat_lit 1456949760)), (nat_lit 2770, Int.ofNat (nat_lit 2516290560)), (nat_lit 2771, Int.ofNat (nat_lit 3703230720)), (nat_lit 2782, Int.ofNat (nat_lit 446215680)), (nat_lit 2783, Int.ofNat (nat_lit 715852800)), (nat_lit 2784, Int.ofNat (nat_lit 34334208)), (nat_lit 2786, Int.ofNat (nat_lit 1546800480)), (nat_lit 2787, Int.ofNat (nat_lit 1968756480)), (nat_lit 2788, Int.ofNat (nat_lit 3971847168)), (nat_lit 2789, Int.ofNat (nat_lit 6637222080)), (nat_lit 2801, Int.ofNat (nat_lit 1172897280)), (nat_lit 2802, Int.ofNat (nat_lit 947796480)), (nat_lit 2803, Int.ofNat (nat_lit 1267307520)), (nat_lit 2804, Int.ofNat (nat_lit 3880321440)), (nat_lit 2805, Int.ofNat (nat_lit 4842781440)), (nat_lit 2806, Int.ofNat (nat_lit 6031779840)), (nat_lit 2807, Int.ofNat (nat_lit 11064781440))]
theorem block012_data_flat158_step : block012_data_flat158 = (CoefficientMerge.fastMerge block012_data_flat078 block012_data_flat157) := by decide +kernel
theorem block012_data_flat158_original : block012_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182136240 : Int) atom0895Coded) (CoefficientMerge.scale (5136502230 : Int) atom0896Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4373859870 : Int) atom0897Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154863360 : Int) atom0898Coded) (CoefficientMerge.scale (78704640 : Int) atom0899Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (155020320 : Int) atom0900Coded) (CoefficientMerge.scale (158595840 : Int) atom0901Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0902Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0903Coded) (CoefficientMerge.scale (87669792 : Int) atom0904Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0905Coded) (CoefficientMerge.scale (2293143552 : Int) atom0906Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0907Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411045120 : Int) atom0908Coded) (CoefficientMerge.scale (628784640 : Int) atom0909Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (786193920 : Int) atom0910Coded) (CoefficientMerge.scale (232689600 : Int) atom0911Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13607520 : Int) atom0912Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (701867040 : Int) atom0913Coded) (CoefficientMerge.scale (1929608160 : Int) atom0914Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3909670560 : Int) atom0915Coded) (CoefficientMerge.scale (6267332160 : Int) atom0916Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (891244800 : Int) atom0917Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1609136640 : Int) atom0918Coded) (CoefficientMerge.scale (1344916800 : Int) atom0919Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1404100320 : Int) atom0920Coded) (CoefficientMerge.scale (2940756000 : Int) atom0921Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3706055520 : Int) atom0922Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5793806880 : Int) atom0923Coded) (CoefficientMerge.scale (8475644160 : Int) atom0924Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1725016320 : Int) atom0925Coded) (CoefficientMerge.scale (2334026880 : Int) atom0926Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2590296480 : Int) atom0927Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4993500960 : Int) atom0928Coded) (CoefficientMerge.scale (6174312480 : Int) atom0929Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7280074080 : Int) atom0930Coded) (CoefficientMerge.scale (12177524160 : Int) atom0931Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2643701760 : Int) atom0932Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5717445840 : Int) atom0933Coded) (CoefficientMerge.scale (11409847200 : Int) atom0934Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12355259760 : Int) atom0935Coded) (CoefficientMerge.scale (9602218800 : Int) atom0936Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15732480240 : Int) atom0937Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2227212288 : Int) atom0938Coded) (CoefficientMerge.scale (9005351400 : Int) atom0939Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10554219720 : Int) atom0940Coded) (CoefficientMerge.scale (8388355680 : Int) atom0941Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11756106540 : Int) atom0942Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7560675000 : Int) atom0943Coded) (CoefficientMerge.scale (12812030280 : Int) atom0944Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10325020320 : Int) atom0945Coded) (CoefficientMerge.scale (14890848480 : Int) atom0946Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3863096280 : Int) atom0947Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6214863960 : Int) atom0948Coded) (CoefficientMerge.scale (11200519260 : Int) atom0949Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (928467360 : Int) atom0950Coded) (CoefficientMerge.scale (7244896500 : Int) atom0951Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5633486820 : Int) atom0952Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114117120 : Int) atom0953Coded) (CoefficientMerge.scale (123425280 : Int) atom0954Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0955Coded) (CoefficientMerge.scale (198804480 : Int) atom0956Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (697544160 : Int) atom0957Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1456949760 : Int) atom0958Coded) (CoefficientMerge.scale (2516290560 : Int) atom0959Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3703230720 : Int) atom0960Coded) (CoefficientMerge.scale (446215680 : Int) atom0961Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (715852800 : Int) atom0962Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34334208 : Int) atom0963Coded) (CoefficientMerge.scale (1546800480 : Int) atom0964Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1968756480 : Int) atom0965Coded) (CoefficientMerge.scale (3971847168 : Int) atom0966Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6637222080 : Int) atom0967Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1172897280 : Int) atom0968Coded) (CoefficientMerge.scale (947796480 : Int) atom0969Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1267307520 : Int) atom0970Coded) (CoefficientMerge.scale (3880321440 : Int) atom0971Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4842781440 : Int) atom0972Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031779840 : Int) atom0973Coded) (CoefficientMerge.scale (11064781440 : Int) atom0974Coded)))))))) := by
  rw [block012_data_flat158_step, block012_data_flat078_original, block012_data_flat157_original]
def block012_data_flat159 : CoefficientMerge.Poly := [(nat_lit 2248, Int.ofNat (nat_lit 182136240)), (nat_lit 2249, Int.ofNat (nat_lit 5136502230)), (nat_lit 2267, Int.ofNat (nat_lit 4373859870)), (nat_lit 2401, Int.ofNat (nat_lit 154863360)), (nat_lit 2402, Int.ofNat (nat_lit 78704640)), (nat_lit 2406, Int.ofNat (nat_lit 155020320)), (nat_lit 2420, Int.ofNat (nat_lit 158595840)), (nat_lit 2422, Int.ofNat (nat_lit 103864320)), (nat_lit 2423, Int.ofNat (nat_lit 207728640)), (nat_lit 2424, Int.ofNat (nat_lit 87669792)), (nat_lit 2427, Int.ofNat (nat_lit 1180247040)), (nat_lit 2428, Int.ofNat (nat_lit 2293143552)), (nat_lit 2429, Int.ofNat (nat_lit 3586383360)), (nat_lit 2439, Int.ofNat (nat_lit 411045120)), (nat_lit 2440, Int.ofNat (nat_lit 628784640)), (nat_lit 2441, Int.ofNat (nat_lit 786193920)), (nat_lit 2442, Int.ofNat (nat_lit 232689600)), (nat_lit 2443, Int.ofNat (nat_lit 13607520)), (nat_lit 2444, Int.ofNat (nat_lit 701867040)), (nat_lit 2445, Int.ofNat (nat_lit 1929608160)), (nat_lit 2446, Int.ofNat (nat_lit 3909670560)), (nat_lit 2447, Int.ofNat (nat_lit 6267332160)), (nat_lit 2458, Int.ofNat (nat_lit 891244800)), (nat_lit 2459, Int.ofNat (nat_lit 1609136640)), (nat_lit 2460, Int.ofNat (nat_lit 1344916800)), (nat_lit 2461, Int.ofNat (nat_lit 1404100320)), (nat_lit 2462, Int.ofNat (nat_lit 2940756000)), (nat_lit 2463, Int.ofNat (nat_lit 3706055520)), (nat_lit 2464, Int.ofNat (nat_lit 5793806880)), (nat_lit 2465, Int.ofNat (nat_lit 8475644160)), (nat_lit 2477, Int.ofNat (nat_lit 1725016320)), (nat_lit 2478, Int.ofNat (nat_lit 2334026880)), (nat_lit 2479, Int.ofNat (nat_lit 2590296480)), (nat_lit 2480, Int.ofNat (nat_lit 4993500960)), (nat_lit 2481, Int.ofNat (nat_lit 6174312480)), (nat_lit 2482, Int.ofNat (nat_lit 7280074080)), (nat_lit 2483, Int.ofNat (nat_lit 12177524160)), (nat_lit 2496, Int.ofNat (nat_lit 2643701760)), (nat_lit 2497, Int.ofNat (nat_lit 5717445840)), (nat_lit 2498, Int.ofNat (nat_lit 11409847200)), (nat_lit 2499, Int.ofNat (nat_lit 12355259760)), (nat_lit 2500, Int.ofNat (nat_lit 9602218800)), (nat_lit 2501, Int.ofNat (nat_lit 15732480240)), (nat_lit 2515, Int.ofNat (nat_lit 2227212288)), (nat_lit 2516, Int.ofNat (nat_lit 9005351400)), (nat_lit 2517, Int.ofNat (nat_lit 10554219720)), (nat_lit 2518, Int.ofNat (nat_lit 8388355680)), (nat_lit 2519, Int.ofNat (nat_lit 11756106540)), (nat_lit 2534, Int.ofNat (nat_lit 7560675000)), (nat_lit 2535, Int.ofNat (nat_lit 12812030280)), (nat_lit 2536, Int.ofNat (nat_lit 10325020320)), (nat_lit 2537, Int.ofNat (nat_lit 14890848480)), (nat_lit 2553, Int.ofNat (nat_lit 3863096280)), (nat_lit 2554, Int.ofNat (nat_lit 6214863960)), (nat_lit 2555, Int.ofNat (nat_lit 11200519260)), (nat_lit 2572, Int.ofNat (nat_lit 928467360)), (nat_lit 2573, Int.ofNat (nat_lit 7244896500)), (nat_lit 2591, Int.ofNat (nat_lit 5633486820)), (nat_lit 2744, Int.ofNat (nat_lit 114117120)), (nat_lit 2763, Int.ofNat (nat_lit 123425280)), (nat_lit 2765, Int.ofNat (nat_lit 103864320)), (nat_lit 2767, Int.ofNat (nat_lit 198804480)), (nat_lit 2768, Int.ofNat (nat_lit 697544160)), (nat_lit 2769, Int.ofNat (nat_lit 1456949760)), (nat_lit 2770, Int.ofNat (nat_lit 2516290560)), (nat_lit 2771, Int.ofNat (nat_lit 3703230720)), (nat_lit 2782, Int.ofNat (nat_lit 446215680)), (nat_lit 2783, Int.ofNat (nat_lit 715852800)), (nat_lit 2784, Int.ofNat (nat_lit 34334208)), (nat_lit 2786, Int.ofNat (nat_lit 1546800480)), (nat_lit 2787, Int.ofNat (nat_lit 1968756480)), (nat_lit 2788, Int.ofNat (nat_lit 3971847168)), (nat_lit 2789, Int.ofNat (nat_lit 6637222080)), (nat_lit 2801, Int.ofNat (nat_lit 1172897280)), (nat_lit 2802, Int.ofNat (nat_lit 947796480)), (nat_lit 2803, Int.ofNat (nat_lit 1267307520)), (nat_lit 2804, Int.ofNat (nat_lit 3880321440)), (nat_lit 2805, Int.ofNat (nat_lit 4842781440)), (nat_lit 2806, Int.ofNat (nat_lit 6031779840)), (nat_lit 2807, Int.ofNat (nat_lit 11064781440))]
theorem block012_data_flat159_step : block012_data_flat159 = (CoefficientMerge.trim block012_data_flat158) := by decide +kernel
theorem block012_data_flat159_original : block012_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182136240 : Int) atom0895Coded) (CoefficientMerge.scale (5136502230 : Int) atom0896Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4373859870 : Int) atom0897Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154863360 : Int) atom0898Coded) (CoefficientMerge.scale (78704640 : Int) atom0899Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (155020320 : Int) atom0900Coded) (CoefficientMerge.scale (158595840 : Int) atom0901Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0902Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0903Coded) (CoefficientMerge.scale (87669792 : Int) atom0904Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0905Coded) (CoefficientMerge.scale (2293143552 : Int) atom0906Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0907Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411045120 : Int) atom0908Coded) (CoefficientMerge.scale (628784640 : Int) atom0909Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (786193920 : Int) atom0910Coded) (CoefficientMerge.scale (232689600 : Int) atom0911Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13607520 : Int) atom0912Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (701867040 : Int) atom0913Coded) (CoefficientMerge.scale (1929608160 : Int) atom0914Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3909670560 : Int) atom0915Coded) (CoefficientMerge.scale (6267332160 : Int) atom0916Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (891244800 : Int) atom0917Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1609136640 : Int) atom0918Coded) (CoefficientMerge.scale (1344916800 : Int) atom0919Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1404100320 : Int) atom0920Coded) (CoefficientMerge.scale (2940756000 : Int) atom0921Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3706055520 : Int) atom0922Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5793806880 : Int) atom0923Coded) (CoefficientMerge.scale (8475644160 : Int) atom0924Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1725016320 : Int) atom0925Coded) (CoefficientMerge.scale (2334026880 : Int) atom0926Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2590296480 : Int) atom0927Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4993500960 : Int) atom0928Coded) (CoefficientMerge.scale (6174312480 : Int) atom0929Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7280074080 : Int) atom0930Coded) (CoefficientMerge.scale (12177524160 : Int) atom0931Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2643701760 : Int) atom0932Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5717445840 : Int) atom0933Coded) (CoefficientMerge.scale (11409847200 : Int) atom0934Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12355259760 : Int) atom0935Coded) (CoefficientMerge.scale (9602218800 : Int) atom0936Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15732480240 : Int) atom0937Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2227212288 : Int) atom0938Coded) (CoefficientMerge.scale (9005351400 : Int) atom0939Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10554219720 : Int) atom0940Coded) (CoefficientMerge.scale (8388355680 : Int) atom0941Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11756106540 : Int) atom0942Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7560675000 : Int) atom0943Coded) (CoefficientMerge.scale (12812030280 : Int) atom0944Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10325020320 : Int) atom0945Coded) (CoefficientMerge.scale (14890848480 : Int) atom0946Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3863096280 : Int) atom0947Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6214863960 : Int) atom0948Coded) (CoefficientMerge.scale (11200519260 : Int) atom0949Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (928467360 : Int) atom0950Coded) (CoefficientMerge.scale (7244896500 : Int) atom0951Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5633486820 : Int) atom0952Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114117120 : Int) atom0953Coded) (CoefficientMerge.scale (123425280 : Int) atom0954Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0955Coded) (CoefficientMerge.scale (198804480 : Int) atom0956Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (697544160 : Int) atom0957Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1456949760 : Int) atom0958Coded) (CoefficientMerge.scale (2516290560 : Int) atom0959Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3703230720 : Int) atom0960Coded) (CoefficientMerge.scale (446215680 : Int) atom0961Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (715852800 : Int) atom0962Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34334208 : Int) atom0963Coded) (CoefficientMerge.scale (1546800480 : Int) atom0964Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1968756480 : Int) atom0965Coded) (CoefficientMerge.scale (3971847168 : Int) atom0966Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6637222080 : Int) atom0967Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1172897280 : Int) atom0968Coded) (CoefficientMerge.scale (947796480 : Int) atom0969Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1267307520 : Int) atom0970Coded) (CoefficientMerge.scale (3880321440 : Int) atom0971Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4842781440 : Int) atom0972Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031779840 : Int) atom0973Coded) (CoefficientMerge.scale (11064781440 : Int) atom0974Coded))))))))) := by
  rw [block012_data_flat159_step, block012_data_flat158_original]
theorem block012_data : block012 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (182136240 : Int) atom0895Coded) (CoefficientMerge.scale (5136502230 : Int) atom0896Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4373859870 : Int) atom0897Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (154863360 : Int) atom0898Coded) (CoefficientMerge.scale (78704640 : Int) atom0899Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (155020320 : Int) atom0900Coded) (CoefficientMerge.scale (158595840 : Int) atom0901Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0902Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207728640 : Int) atom0903Coded) (CoefficientMerge.scale (87669792 : Int) atom0904Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1180247040 : Int) atom0905Coded) (CoefficientMerge.scale (2293143552 : Int) atom0906Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3586383360 : Int) atom0907Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411045120 : Int) atom0908Coded) (CoefficientMerge.scale (628784640 : Int) atom0909Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (786193920 : Int) atom0910Coded) (CoefficientMerge.scale (232689600 : Int) atom0911Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13607520 : Int) atom0912Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (701867040 : Int) atom0913Coded) (CoefficientMerge.scale (1929608160 : Int) atom0914Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3909670560 : Int) atom0915Coded) (CoefficientMerge.scale (6267332160 : Int) atom0916Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (891244800 : Int) atom0917Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1609136640 : Int) atom0918Coded) (CoefficientMerge.scale (1344916800 : Int) atom0919Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1404100320 : Int) atom0920Coded) (CoefficientMerge.scale (2940756000 : Int) atom0921Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3706055520 : Int) atom0922Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5793806880 : Int) atom0923Coded) (CoefficientMerge.scale (8475644160 : Int) atom0924Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1725016320 : Int) atom0925Coded) (CoefficientMerge.scale (2334026880 : Int) atom0926Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2590296480 : Int) atom0927Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4993500960 : Int) atom0928Coded) (CoefficientMerge.scale (6174312480 : Int) atom0929Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7280074080 : Int) atom0930Coded) (CoefficientMerge.scale (12177524160 : Int) atom0931Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2643701760 : Int) atom0932Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5717445840 : Int) atom0933Coded) (CoefficientMerge.scale (11409847200 : Int) atom0934Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (12355259760 : Int) atom0935Coded) (CoefficientMerge.scale (9602218800 : Int) atom0936Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15732480240 : Int) atom0937Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2227212288 : Int) atom0938Coded) (CoefficientMerge.scale (9005351400 : Int) atom0939Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10554219720 : Int) atom0940Coded) (CoefficientMerge.scale (8388355680 : Int) atom0941Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11756106540 : Int) atom0942Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7560675000 : Int) atom0943Coded) (CoefficientMerge.scale (12812030280 : Int) atom0944Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10325020320 : Int) atom0945Coded) (CoefficientMerge.scale (14890848480 : Int) atom0946Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3863096280 : Int) atom0947Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6214863960 : Int) atom0948Coded) (CoefficientMerge.scale (11200519260 : Int) atom0949Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (928467360 : Int) atom0950Coded) (CoefficientMerge.scale (7244896500 : Int) atom0951Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5633486820 : Int) atom0952Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114117120 : Int) atom0953Coded) (CoefficientMerge.scale (123425280 : Int) atom0954Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (103864320 : Int) atom0955Coded) (CoefficientMerge.scale (198804480 : Int) atom0956Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (697544160 : Int) atom0957Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1456949760 : Int) atom0958Coded) (CoefficientMerge.scale (2516290560 : Int) atom0959Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3703230720 : Int) atom0960Coded) (CoefficientMerge.scale (446215680 : Int) atom0961Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (715852800 : Int) atom0962Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (34334208 : Int) atom0963Coded) (CoefficientMerge.scale (1546800480 : Int) atom0964Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1968756480 : Int) atom0965Coded) (CoefficientMerge.scale (3971847168 : Int) atom0966Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6637222080 : Int) atom0967Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (1172897280 : Int) atom0968Coded) (CoefficientMerge.scale (947796480 : Int) atom0969Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1267307520 : Int) atom0970Coded) (CoefficientMerge.scale (3880321440 : Int) atom0971Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4842781440 : Int) atom0972Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031779840 : Int) atom0973Coded) (CoefficientMerge.scale (11064781440 : Int) atom0974Coded)))))))) := by
  have h : block012 = block012_data_flat159 := by decide +kernel
  exact h.trans block012_data_flat159_original
theorem block012_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 18) block012 := by
  rw [block012_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0895Coded_nonneg g hg hA hB) (atom0896Coded_nonneg g hg hA hB)) (add_nonneg (atom0897Coded_nonneg g hg hA hB) (add_nonneg (atom0898Coded_nonneg g hg hA hB) (atom0899Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0900Coded_nonneg g hg hA hB) (atom0901Coded_nonneg g hg hA hB)) (add_nonneg (atom0902Coded_nonneg g hg hA hB) (add_nonneg (atom0903Coded_nonneg g hg hA hB) (atom0904Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0905Coded_nonneg g hg hA hB) (atom0906Coded_nonneg g hg hA hB)) (add_nonneg (atom0907Coded_nonneg g hg hA hB) (add_nonneg (atom0908Coded_nonneg g hg hA hB) (atom0909Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0910Coded_nonneg g hg hA hB) (atom0911Coded_nonneg g hg hA hB)) (add_nonneg (atom0912Coded_nonneg g hg hA hB) (add_nonneg (atom0913Coded_nonneg g hg hA hB) (atom0914Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0915Coded_nonneg g hg hA hB) (atom0916Coded_nonneg g hg hA hB)) (add_nonneg (atom0917Coded_nonneg g hg hA hB) (add_nonneg (atom0918Coded_nonneg g hg hA hB) (atom0919Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0920Coded_nonneg g hg hA hB) (atom0921Coded_nonneg g hg hA hB)) (add_nonneg (atom0922Coded_nonneg g hg hA hB) (add_nonneg (atom0923Coded_nonneg g hg hA hB) (atom0924Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0925Coded_nonneg g hg hA hB) (atom0926Coded_nonneg g hg hA hB)) (add_nonneg (atom0927Coded_nonneg g hg hA hB) (add_nonneg (atom0928Coded_nonneg g hg hA hB) (atom0929Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0930Coded_nonneg g hg hA hB) (atom0931Coded_nonneg g hg hA hB)) (add_nonneg (atom0932Coded_nonneg g hg hA hB) (add_nonneg (atom0933Coded_nonneg g hg hA hB) (atom0934Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0935Coded_nonneg g hg hA hB) (atom0936Coded_nonneg g hg hA hB)) (add_nonneg (atom0937Coded_nonneg g hg hA hB) (add_nonneg (atom0938Coded_nonneg g hg hA hB) (atom0939Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0940Coded_nonneg g hg hA hB) (atom0941Coded_nonneg g hg hA hB)) (add_nonneg (atom0942Coded_nonneg g hg hA hB) (add_nonneg (atom0943Coded_nonneg g hg hA hB) (atom0944Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0945Coded_nonneg g hg hA hB) (atom0946Coded_nonneg g hg hA hB)) (add_nonneg (atom0947Coded_nonneg g hg hA hB) (add_nonneg (atom0948Coded_nonneg g hg hA hB) (atom0949Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0950Coded_nonneg g hg hA hB) (atom0951Coded_nonneg g hg hA hB)) (add_nonneg (atom0952Coded_nonneg g hg hA hB) (add_nonneg (atom0953Coded_nonneg g hg hA hB) (atom0954Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0955Coded_nonneg g hg hA hB) (atom0956Coded_nonneg g hg hA hB)) (add_nonneg (atom0957Coded_nonneg g hg hA hB) (add_nonneg (atom0958Coded_nonneg g hg hA hB) (atom0959Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0960Coded_nonneg g hg hA hB) (atom0961Coded_nonneg g hg hA hB)) (add_nonneg (atom0962Coded_nonneg g hg hA hB) (add_nonneg (atom0963Coded_nonneg g hg hA hB) (atom0964Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0965Coded_nonneg g hg hA hB) (atom0966Coded_nonneg g hg hA hB)) (add_nonneg (atom0967Coded_nonneg g hg hA hB) (add_nonneg (atom0968Coded_nonneg g hg hA hB) (atom0969Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0970Coded_nonneg g hg hA hB) (atom0971Coded_nonneg g hg hA hB)) (add_nonneg (atom0972Coded_nonneg g hg hA hB) (add_nonneg (atom0973Coded_nonneg g hg hA hB) (atom0974Coded_nonneg g hg hA hB))))))))

end APPT.Finite18
