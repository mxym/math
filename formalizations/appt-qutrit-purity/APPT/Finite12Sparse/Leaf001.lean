-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite12Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def atom0080 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 2, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0080 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0080 = ((g 1) * (g 2) * (g 11)) := by
  norm_num [atom0080, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0080_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62752 : Int) atom0080) := by
  rw [SparsePolynomial.eval_scale, eval_atom0080]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0080Coded : CoefficientMerge.Poly := [(nat_lit 179, Int.ofNat (nat_lit 1))]
theorem atom0080Coded_decode : atom0080 = SparsePolynomial.decodeCubic 12 atom0080Coded := by decide +kernel
theorem atom0080Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (62752 : Int) atom0080Coded) := by
  have h := atom0080_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0080Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0081 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0081 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0081 = ((g 1) * (g 3) * (g 3)) := by
  norm_num [atom0081, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0081_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17568 : Int) atom0081) := by
  rw [SparsePolynomial.eval_scale, eval_atom0081]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0081Coded : CoefficientMerge.Poly := [(nat_lit 183, Int.ofNat (nat_lit 1))]
theorem atom0081Coded_decode : atom0081 = SparsePolynomial.decodeCubic 12 atom0081Coded := by decide +kernel
theorem atom0081Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (17568 : Int) atom0081Coded) := by
  have h := atom0081_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0081Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0082 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0082 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0082 = ((g 1) * (g 3) * (g 4)) := by
  norm_num [atom0082, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0082_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24768 : Int) atom0082) := by
  rw [SparsePolynomial.eval_scale, eval_atom0082]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0082Coded : CoefficientMerge.Poly := [(nat_lit 184, Int.ofNat (nat_lit 1))]
theorem atom0082Coded_decode : atom0082 = SparsePolynomial.decodeCubic 12 atom0082Coded := by decide +kernel
theorem atom0082Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (24768 : Int) atom0082Coded) := by
  have h := atom0082_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0082Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0083 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0083 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0083 = ((g 1) * (g 3) * (g 5)) := by
  norm_num [atom0083, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0083_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28928 : Int) atom0083) := by
  rw [SparsePolynomial.eval_scale, eval_atom0083]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0083Coded : CoefficientMerge.Poly := [(nat_lit 185, Int.ofNat (nat_lit 1))]
theorem atom0083Coded_decode : atom0083 = SparsePolynomial.decodeCubic 12 atom0083Coded := by decide +kernel
theorem atom0083Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (28928 : Int) atom0083Coded) := by
  have h := atom0083_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0083Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0084 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0084 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0084 = ((g 1) * (g 3) * (g 6)) := by
  norm_num [atom0084, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0084_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (107136 : Int) atom0084) := by
  rw [SparsePolynomial.eval_scale, eval_atom0084]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0084Coded : CoefficientMerge.Poly := [(nat_lit 186, Int.ofNat (nat_lit 1))]
theorem atom0084Coded_decode : atom0084 = SparsePolynomial.decodeCubic 12 atom0084Coded := by decide +kernel
theorem atom0084Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (107136 : Int) atom0084Coded) := by
  have h := atom0084_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0084Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0085 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0085 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0085 = ((g 1) * (g 3) * (g 7)) := by
  norm_num [atom0085, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0085_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57088 : Int) atom0085) := by
  rw [SparsePolynomial.eval_scale, eval_atom0085]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0085Coded : CoefficientMerge.Poly := [(nat_lit 187, Int.ofNat (nat_lit 1))]
theorem atom0085Coded_decode : atom0085 = SparsePolynomial.decodeCubic 12 atom0085Coded := by decide +kernel
theorem atom0085Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (57088 : Int) atom0085Coded) := by
  have h := atom0085_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0085Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0086 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0086 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0086 = ((g 1) * (g 3) * (g 8)) := by
  norm_num [atom0086, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0086_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76416 : Int) atom0086) := by
  rw [SparsePolynomial.eval_scale, eval_atom0086]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0086Coded : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 1))]
theorem atom0086Coded_decode : atom0086 = SparsePolynomial.decodeCubic 12 atom0086Coded := by decide +kernel
theorem atom0086Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (76416 : Int) atom0086Coded) := by
  have h := atom0086_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0086Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0087 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0087 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0087 = ((g 1) * (g 3) * (g 9)) := by
  norm_num [atom0087, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0087_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (82560 : Int) atom0087) := by
  rw [SparsePolynomial.eval_scale, eval_atom0087]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0087Coded : CoefficientMerge.Poly := [(nat_lit 189, Int.ofNat (nat_lit 1))]
theorem atom0087Coded_decode : atom0087 = SparsePolynomial.decodeCubic 12 atom0087Coded := by decide +kernel
theorem atom0087Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (82560 : Int) atom0087Coded) := by
  have h := atom0087_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0087Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0088 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0088 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0088 = ((g 1) * (g 3) * (g 10)) := by
  norm_num [atom0088, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0088_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84440 : Int) atom0088) := by
  rw [SparsePolynomial.eval_scale, eval_atom0088]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0088Coded : CoefficientMerge.Poly := [(nat_lit 190, Int.ofNat (nat_lit 1))]
theorem atom0088Coded_decode : atom0088 = SparsePolynomial.decodeCubic 12 atom0088Coded := by decide +kernel
theorem atom0088Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (84440 : Int) atom0088Coded) := by
  have h := atom0088_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0088Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0089 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 3, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0089 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0089 = ((g 1) * (g 3) * (g 11)) := by
  norm_num [atom0089, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0089_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (89344 : Int) atom0089) := by
  rw [SparsePolynomial.eval_scale, eval_atom0089]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0089Coded : CoefficientMerge.Poly := [(nat_lit 191, Int.ofNat (nat_lit 1))]
theorem atom0089Coded_decode : atom0089 = SparsePolynomial.decodeCubic 12 atom0089Coded := by decide +kernel
theorem atom0089Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (89344 : Int) atom0089Coded) := by
  have h := atom0089_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0089Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0090 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0090 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0090 = ((g 1) * (g 4) * (g 4)) := by
  norm_num [atom0090, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0090_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21888 : Int) atom0090) := by
  rw [SparsePolynomial.eval_scale, eval_atom0090]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0090Coded : CoefficientMerge.Poly := [(nat_lit 196, Int.ofNat (nat_lit 1))]
theorem atom0090Coded_decode : atom0090 = SparsePolynomial.decodeCubic 12 atom0090Coded := by decide +kernel
theorem atom0090Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (21888 : Int) atom0090Coded) := by
  have h := atom0090_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0090Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0091 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0091 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0091 = ((g 1) * (g 4) * (g 5)) := by
  norm_num [atom0091, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0091_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39008 : Int) atom0091) := by
  rw [SparsePolynomial.eval_scale, eval_atom0091]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0091Coded : CoefficientMerge.Poly := [(nat_lit 197, Int.ofNat (nat_lit 1))]
theorem atom0091Coded_decode : atom0091 = SparsePolynomial.decodeCubic 12 atom0091Coded := by decide +kernel
theorem atom0091Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (39008 : Int) atom0091Coded) := by
  have h := atom0091_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0091Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0092 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0092 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0092 = ((g 1) * (g 4) * (g 6)) := by
  norm_num [atom0092, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0092_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (109824 : Int) atom0092) := by
  rw [SparsePolynomial.eval_scale, eval_atom0092]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0092Coded : CoefficientMerge.Poly := [(nat_lit 198, Int.ofNat (nat_lit 1))]
theorem atom0092Coded_decode : atom0092 = SparsePolynomial.decodeCubic 12 atom0092Coded := by decide +kernel
theorem atom0092Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (109824 : Int) atom0092Coded) := by
  have h := atom0092_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0092Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0093 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0093 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0093 = ((g 1) * (g 4) * (g 7)) := by
  norm_num [atom0093, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0093_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69952 : Int) atom0093) := by
  rw [SparsePolynomial.eval_scale, eval_atom0093]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0093Coded : CoefficientMerge.Poly := [(nat_lit 199, Int.ofNat (nat_lit 1))]
theorem atom0093Coded_decode : atom0093 = SparsePolynomial.decodeCubic 12 atom0093Coded := by decide +kernel
theorem atom0093Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (69952 : Int) atom0093Coded) := by
  have h := atom0093_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0093Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0094 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0094 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0094 = ((g 1) * (g 4) * (g 8)) := by
  norm_num [atom0094, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0094_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90624 : Int) atom0094) := by
  rw [SparsePolynomial.eval_scale, eval_atom0094]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0094Coded : CoefficientMerge.Poly := [(nat_lit 200, Int.ofNat (nat_lit 1))]
theorem atom0094Coded_decode : atom0094 = SparsePolynomial.decodeCubic 12 atom0094Coded := by decide +kernel
theorem atom0094Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (90624 : Int) atom0094Coded) := by
  have h := atom0094_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0094Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0095 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0095 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0095 = ((g 1) * (g 4) * (g 9)) := by
  norm_num [atom0095, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0095_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (102528 : Int) atom0095) := by
  rw [SparsePolynomial.eval_scale, eval_atom0095]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0095Coded : CoefficientMerge.Poly := [(nat_lit 201, Int.ofNat (nat_lit 1))]
theorem atom0095Coded_decode : atom0095 = SparsePolynomial.decodeCubic 12 atom0095Coded := by decide +kernel
theorem atom0095Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (102528 : Int) atom0095Coded) := by
  have h := atom0095_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0095Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0096 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0096 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0096 = ((g 1) * (g 4) * (g 10)) := by
  norm_num [atom0096, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0096_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (109856 : Int) atom0096) := by
  rw [SparsePolynomial.eval_scale, eval_atom0096]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0096Coded : CoefficientMerge.Poly := [(nat_lit 202, Int.ofNat (nat_lit 1))]
theorem atom0096Coded_decode : atom0096 = SparsePolynomial.decodeCubic 12 atom0096Coded := by decide +kernel
theorem atom0096Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (109856 : Int) atom0096Coded) := by
  have h := atom0096_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0096Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0097 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0097 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0097 = ((g 1) * (g 4) * (g 11)) := by
  norm_num [atom0097, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0097_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (120832 : Int) atom0097) := by
  rw [SparsePolynomial.eval_scale, eval_atom0097]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0097Coded : CoefficientMerge.Poly := [(nat_lit 203, Int.ofNat (nat_lit 1))]
theorem atom0097Coded_decode : atom0097 = SparsePolynomial.decodeCubic 12 atom0097Coded := by decide +kernel
theorem atom0097Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (120832 : Int) atom0097Coded) := by
  have h := atom0097_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0097Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0098 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0098 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0098 = ((g 1) * (g 5) * (g 5)) := by
  norm_num [atom0098, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0098_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33152 : Int) atom0098) := by
  rw [SparsePolynomial.eval_scale, eval_atom0098]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0098Coded : CoefficientMerge.Poly := [(nat_lit 209, Int.ofNat (nat_lit 1))]
theorem atom0098Coded_decode : atom0098 = SparsePolynomial.decodeCubic 12 atom0098Coded := by decide +kernel
theorem atom0098Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (33152 : Int) atom0098Coded) := by
  have h := atom0098_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0098Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0099 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0099 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0099 = ((g 1) * (g 5) * (g 6)) := by
  norm_num [atom0099, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0099_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (113536 : Int) atom0099) := by
  rw [SparsePolynomial.eval_scale, eval_atom0099]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0099Coded : CoefficientMerge.Poly := [(nat_lit 210, Int.ofNat (nat_lit 1))]
theorem atom0099Coded_decode : atom0099 = SparsePolynomial.decodeCubic 12 atom0099Coded := by decide +kernel
theorem atom0099Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (113536 : Int) atom0099Coded) := by
  have h := atom0099_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0099Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0100 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0100 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0100 = ((g 1) * (g 5) * (g 7)) := by
  norm_num [atom0100, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0100_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83712 : Int) atom0100) := by
  rw [SparsePolynomial.eval_scale, eval_atom0100]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0100Coded : CoefficientMerge.Poly := [(nat_lit 211, Int.ofNat (nat_lit 1))]
theorem atom0100Coded_decode : atom0100 = SparsePolynomial.decodeCubic 12 atom0100Coded := by decide +kernel
theorem atom0100Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (83712 : Int) atom0100Coded) := by
  have h := atom0100_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0100Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0101 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0101 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0101 = ((g 1) * (g 5) * (g 8)) := by
  norm_num [atom0101, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0101_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (104320 : Int) atom0101) := by
  rw [SparsePolynomial.eval_scale, eval_atom0101]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0101Coded : CoefficientMerge.Poly := [(nat_lit 212, Int.ofNat (nat_lit 1))]
theorem atom0101Coded_decode : atom0101 = SparsePolynomial.decodeCubic 12 atom0101Coded := by decide +kernel
theorem atom0101Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (104320 : Int) atom0101Coded) := by
  have h := atom0101_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0101Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0102 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0102 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0102 = ((g 1) * (g 5) * (g 9)) := by
  norm_num [atom0102, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0102_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (121728 : Int) atom0102) := by
  rw [SparsePolynomial.eval_scale, eval_atom0102]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0102Coded : CoefficientMerge.Poly := [(nat_lit 213, Int.ofNat (nat_lit 1))]
theorem atom0102Coded_decode : atom0102 = SparsePolynomial.decodeCubic 12 atom0102Coded := by decide +kernel
theorem atom0102Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (121728 : Int) atom0102Coded) := by
  have h := atom0102_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0102Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0103 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0103 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0103 = ((g 1) * (g 5) * (g 10)) := by
  norm_num [atom0103, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0103_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (127200 : Int) atom0103) := by
  rw [SparsePolynomial.eval_scale, eval_atom0103]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0103Coded : CoefficientMerge.Poly := [(nat_lit 214, Int.ofNat (nat_lit 1))]
theorem atom0103Coded_decode : atom0103 = SparsePolynomial.decodeCubic 12 atom0103Coded := by decide +kernel
theorem atom0103Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (127200 : Int) atom0103Coded) := by
  have h := atom0103_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0103Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0104 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0104 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0104 = ((g 1) * (g 5) * (g 11)) := by
  norm_num [atom0104, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0104_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (150016 : Int) atom0104) := by
  rw [SparsePolynomial.eval_scale, eval_atom0104]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0104Coded : CoefficientMerge.Poly := [(nat_lit 215, Int.ofNat (nat_lit 1))]
theorem atom0104Coded_decode : atom0104 = SparsePolynomial.decodeCubic 12 atom0104Coded := by decide +kernel
theorem atom0104Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (150016 : Int) atom0104Coded) := by
  have h := atom0104_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0104Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0105 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0105 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0105 = ((g 1) * (g 6) * (g 6)) := by
  norm_num [atom0105, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0105_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95616 : Int) atom0105) := by
  rw [SparsePolynomial.eval_scale, eval_atom0105]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0105Coded : CoefficientMerge.Poly := [(nat_lit 222, Int.ofNat (nat_lit 1))]
theorem atom0105Coded_decode : atom0105 = SparsePolynomial.decodeCubic 12 atom0105Coded := by decide +kernel
theorem atom0105Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (95616 : Int) atom0105Coded) := by
  have h := atom0105_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0105Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0106 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0106 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0106 = ((g 1) * (g 6) * (g 7)) := by
  norm_num [atom0106, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0106_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (147584 : Int) atom0106) := by
  rw [SparsePolynomial.eval_scale, eval_atom0106]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0106Coded : CoefficientMerge.Poly := [(nat_lit 223, Int.ofNat (nat_lit 1))]
theorem atom0106Coded_decode : atom0106 = SparsePolynomial.decodeCubic 12 atom0106Coded := by decide +kernel
theorem atom0106Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (147584 : Int) atom0106Coded) := by
  have h := atom0106_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0106Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0107 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0107 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0107 = ((g 1) * (g 6) * (g 8)) := by
  norm_num [atom0107, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0107_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (195072 : Int) atom0107) := by
  rw [SparsePolynomial.eval_scale, eval_atom0107]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0107Coded : CoefficientMerge.Poly := [(nat_lit 224, Int.ofNat (nat_lit 1))]
theorem atom0107Coded_decode : atom0107 = SparsePolynomial.decodeCubic 12 atom0107Coded := by decide +kernel
theorem atom0107Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (195072 : Int) atom0107Coded) := by
  have h := atom0107_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0107Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0108 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0108 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0108 = ((g 1) * (g 6) * (g 9)) := by
  norm_num [atom0108, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0108_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (218112 : Int) atom0108) := by
  rw [SparsePolynomial.eval_scale, eval_atom0108]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0108Coded : CoefficientMerge.Poly := [(nat_lit 225, Int.ofNat (nat_lit 1))]
theorem atom0108Coded_decode : atom0108 = SparsePolynomial.decodeCubic 12 atom0108Coded := by decide +kernel
theorem atom0108Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (218112 : Int) atom0108Coded) := by
  have h := atom0108_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0108Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0109 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0109 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0109 = ((g 1) * (g 6) * (g 10)) := by
  norm_num [atom0109, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0109_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (134656 : Int) atom0109) := by
  rw [SparsePolynomial.eval_scale, eval_atom0109]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0109Coded : CoefficientMerge.Poly := [(nat_lit 226, Int.ofNat (nat_lit 1))]
theorem atom0109Coded_decode : atom0109 = SparsePolynomial.decodeCubic 12 atom0109Coded := by decide +kernel
theorem atom0109Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (134656 : Int) atom0109Coded) := by
  have h := atom0109_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0109Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0110 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0110 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0110 = ((g 1) * (g 6) * (g 11)) := by
  norm_num [atom0110, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0110_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (168824 : Int) atom0110) := by
  rw [SparsePolynomial.eval_scale, eval_atom0110]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0110Coded : CoefficientMerge.Poly := [(nat_lit 227, Int.ofNat (nat_lit 1))]
theorem atom0110Coded_decode : atom0110 = SparsePolynomial.decodeCubic 12 atom0110Coded := by decide +kernel
theorem atom0110Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (168824 : Int) atom0110Coded) := by
  have h := atom0110_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0110Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0111 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0111 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0111 = ((g 1) * (g 7) * (g 7)) := by
  norm_num [atom0111, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0111_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60736 : Int) atom0111) := by
  rw [SparsePolynomial.eval_scale, eval_atom0111]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0111Coded : CoefficientMerge.Poly := [(nat_lit 235, Int.ofNat (nat_lit 1))]
theorem atom0111Coded_decode : atom0111 = SparsePolynomial.decodeCubic 12 atom0111Coded := by decide +kernel
theorem atom0111Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (60736 : Int) atom0111Coded) := by
  have h := atom0111_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0111Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0112 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0112 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0112 = ((g 1) * (g 7) * (g 8)) := by
  norm_num [atom0112, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0112_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140864 : Int) atom0112) := by
  rw [SparsePolynomial.eval_scale, eval_atom0112]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0112Coded : CoefficientMerge.Poly := [(nat_lit 236, Int.ofNat (nat_lit 1))]
theorem atom0112Coded_decode : atom0112 = SparsePolynomial.decodeCubic 12 atom0112Coded := by decide +kernel
theorem atom0112Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (140864 : Int) atom0112Coded) := by
  have h := atom0112_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0112Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0113 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0113 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0113 = ((g 1) * (g 7) * (g 9)) := by
  norm_num [atom0113, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0113_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (191712 : Int) atom0113) := by
  rw [SparsePolynomial.eval_scale, eval_atom0113]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0113Coded : CoefficientMerge.Poly := [(nat_lit 237, Int.ofNat (nat_lit 1))]
theorem atom0113Coded_decode : atom0113 = SparsePolynomial.decodeCubic 12 atom0113Coded := by decide +kernel
theorem atom0113Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (191712 : Int) atom0113Coded) := by
  have h := atom0113_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0113Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0114 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0114 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0114 = ((g 1) * (g 7) * (g 10)) := by
  norm_num [atom0114, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0114_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (142048 : Int) atom0114) := by
  rw [SparsePolynomial.eval_scale, eval_atom0114]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0114Coded : CoefficientMerge.Poly := [(nat_lit 238, Int.ofNat (nat_lit 1))]
theorem atom0114Coded_decode : atom0114 = SparsePolynomial.decodeCubic 12 atom0114Coded := by decide +kernel
theorem atom0114Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (142048 : Int) atom0114Coded) := by
  have h := atom0114_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0114Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0115 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0115 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0115 = ((g 1) * (g 7) * (g 11)) := by
  norm_num [atom0115, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0115_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (166552 : Int) atom0115) := by
  rw [SparsePolynomial.eval_scale, eval_atom0115]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0115Coded : CoefficientMerge.Poly := [(nat_lit 239, Int.ofNat (nat_lit 1))]
theorem atom0115Coded_decode : atom0115 = SparsePolynomial.decodeCubic 12 atom0115Coded := by decide +kernel
theorem atom0115Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (166552 : Int) atom0115Coded) := by
  have h := atom0115_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0115Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0116 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0116 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0116 = ((g 1) * (g 8) * (g 8)) := by
  norm_num [atom0116, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0116_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105216 : Int) atom0116) := by
  rw [SparsePolynomial.eval_scale, eval_atom0116]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0116Coded : CoefficientMerge.Poly := [(nat_lit 248, Int.ofNat (nat_lit 1))]
theorem atom0116Coded_decode : atom0116 = SparsePolynomial.decodeCubic 12 atom0116Coded := by decide +kernel
theorem atom0116Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (105216 : Int) atom0116Coded) := by
  have h := atom0116_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0116Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0117 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0117 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0117 = ((g 1) * (g 8) * (g 9)) := by
  norm_num [atom0117, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0117_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193344 : Int) atom0117) := by
  rw [SparsePolynomial.eval_scale, eval_atom0117]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0117Coded : CoefficientMerge.Poly := [(nat_lit 249, Int.ofNat (nat_lit 1))]
theorem atom0117Coded_decode : atom0117 = SparsePolynomial.decodeCubic 12 atom0117Coded := by decide +kernel
theorem atom0117Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (193344 : Int) atom0117Coded) := by
  have h := atom0117_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0117Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0118 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0118 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0118 = ((g 1) * (g 8) * (g 10)) := by
  norm_num [atom0118, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0118_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (145792 : Int) atom0118) := by
  rw [SparsePolynomial.eval_scale, eval_atom0118]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0118Coded : CoefficientMerge.Poly := [(nat_lit 250, Int.ofNat (nat_lit 1))]
theorem atom0118Coded_decode : atom0118 = SparsePolynomial.decodeCubic 12 atom0118Coded := by decide +kernel
theorem atom0118Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (145792 : Int) atom0118Coded) := by
  have h := atom0118_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0118Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0119 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0119 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0119 = ((g 1) * (g 8) * (g 11)) := by
  norm_num [atom0119, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0119_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (177848 : Int) atom0119) := by
  rw [SparsePolynomial.eval_scale, eval_atom0119]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0119Coded : CoefficientMerge.Poly := [(nat_lit 251, Int.ofNat (nat_lit 1))]
theorem atom0119Coded_decode : atom0119 = SparsePolynomial.decodeCubic 12 atom0119Coded := by decide +kernel
theorem atom0119Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (177848 : Int) atom0119Coded) := by
  have h := atom0119_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0119Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0120 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0120 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0120 = ((g 1) * (g 9) * (g 9)) := by
  norm_num [atom0120, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0120_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81504 : Int) atom0120) := by
  rw [SparsePolynomial.eval_scale, eval_atom0120]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0120Coded : CoefficientMerge.Poly := [(nat_lit 261, Int.ofNat (nat_lit 1))]
theorem atom0120Coded_decode : atom0120 = SparsePolynomial.decodeCubic 12 atom0120Coded := by decide +kernel
theorem atom0120Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (81504 : Int) atom0120Coded) := by
  have h := atom0120_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0120Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0121 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0121 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0121 = ((g 1) * (g 9) * (g 10)) := by
  norm_num [atom0121, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0121_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (118752 : Int) atom0121) := by
  rw [SparsePolynomial.eval_scale, eval_atom0121]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0121Coded : CoefficientMerge.Poly := [(nat_lit 262, Int.ofNat (nat_lit 1))]
theorem atom0121Coded_decode : atom0121 = SparsePolynomial.decodeCubic 12 atom0121Coded := by decide +kernel
theorem atom0121Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (118752 : Int) atom0121Coded) := by
  have h := atom0121_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0121Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0122 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0122 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0122 = ((g 1) * (g 9) * (g 11)) := by
  norm_num [atom0122, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0122_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (152720 : Int) atom0122) := by
  rw [SparsePolynomial.eval_scale, eval_atom0122]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0122Coded : CoefficientMerge.Poly := [(nat_lit 263, Int.ofNat (nat_lit 1))]
theorem atom0122Coded_decode : atom0122 = SparsePolynomial.decodeCubic 12 atom0122Coded := by decide +kernel
theorem atom0122Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (152720 : Int) atom0122Coded) := by
  have h := atom0122_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0122Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0123 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0123 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0123 = ((g 1) * (g 10) * (g 10)) := by
  norm_num [atom0123, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0123_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26176 : Int) atom0123) := by
  rw [SparsePolynomial.eval_scale, eval_atom0123]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0123Coded : CoefficientMerge.Poly := [(nat_lit 274, Int.ofNat (nat_lit 1))]
theorem atom0123Coded_decode : atom0123 = SparsePolynomial.decodeCubic 12 atom0123Coded := by decide +kernel
theorem atom0123Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (26176 : Int) atom0123Coded) := by
  have h := atom0123_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0123Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0124 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0124 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0124 = ((g 1) * (g 10) * (g 11)) := by
  norm_num [atom0124, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0124_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (76064 : Int) atom0124) := by
  rw [SparsePolynomial.eval_scale, eval_atom0124]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0124Coded : CoefficientMerge.Poly := [(nat_lit 275, Int.ofNat (nat_lit 1))]
theorem atom0124Coded_decode : atom0124 = SparsePolynomial.decodeCubic 12 atom0124Coded := by decide +kernel
theorem atom0124Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (76064 : Int) atom0124Coded) := by
  have h := atom0124_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0124Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0125 : SparsePolynomial.Poly := [([nat_lit 1, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0125 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0125 = ((g 1) * (g 11) * (g 11)) := by
  norm_num [atom0125, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0125_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34272 : Int) atom0125) := by
  rw [SparsePolynomial.eval_scale, eval_atom0125]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0125Coded : CoefficientMerge.Poly := [(nat_lit 287, Int.ofNat (nat_lit 1))]
theorem atom0125Coded_decode : atom0125 = SparsePolynomial.decodeCubic 12 atom0125Coded := by decide +kernel
theorem atom0125Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (34272 : Int) atom0125Coded) := by
  have h := atom0125_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0125Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0126 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 2], Int.ofNat (nat_lit 1))]
theorem eval_atom0126 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0126 = ((g 2) * (g 2) * (g 2)) := by
  norm_num [atom0126, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0126_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8640 : Int) atom0126) := by
  rw [SparsePolynomial.eval_scale, eval_atom0126]
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 2) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0126Coded : CoefficientMerge.Poly := [(nat_lit 314, Int.ofNat (nat_lit 1))]
theorem atom0126Coded_decode : atom0126 = SparsePolynomial.decodeCubic 12 atom0126Coded := by decide +kernel
theorem atom0126Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (8640 : Int) atom0126Coded) := by
  have h := atom0126_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0126Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0127 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0127 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0127 = ((g 2) * (g 2) * (g 3)) := by
  norm_num [atom0127, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0127_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24768 : Int) atom0127) := by
  rw [SparsePolynomial.eval_scale, eval_atom0127]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0127Coded : CoefficientMerge.Poly := [(nat_lit 315, Int.ofNat (nat_lit 1))]
theorem atom0127Coded_decode : atom0127 = SparsePolynomial.decodeCubic 12 atom0127Coded := by decide +kernel
theorem atom0127Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (24768 : Int) atom0127Coded) := by
  have h := atom0127_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0127Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0128 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0128 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0128 = ((g 2) * (g 2) * (g 4)) := by
  norm_num [atom0128, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0128_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23616 : Int) atom0128) := by
  rw [SparsePolynomial.eval_scale, eval_atom0128]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0128Coded : CoefficientMerge.Poly := [(nat_lit 316, Int.ofNat (nat_lit 1))]
theorem atom0128Coded_decode : atom0128 = SparsePolynomial.decodeCubic 12 atom0128Coded := by decide +kernel
theorem atom0128Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (23616 : Int) atom0128Coded) := by
  have h := atom0128_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0128Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0129 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0129 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0129 = ((g 2) * (g 2) * (g 5)) := by
  norm_num [atom0129, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0129_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22464 : Int) atom0129) := by
  rw [SparsePolynomial.eval_scale, eval_atom0129]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0129Coded : CoefficientMerge.Poly := [(nat_lit 317, Int.ofNat (nat_lit 1))]
theorem atom0129Coded_decode : atom0129 = SparsePolynomial.decodeCubic 12 atom0129Coded := by decide +kernel
theorem atom0129Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (22464 : Int) atom0129Coded) := by
  have h := atom0129_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0129Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0130 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0130 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0130 = ((g 2) * (g 2) * (g 6)) := by
  norm_num [atom0130, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0130_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59328 : Int) atom0130) := by
  rw [SparsePolynomial.eval_scale, eval_atom0130]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0130Coded : CoefficientMerge.Poly := [(nat_lit 318, Int.ofNat (nat_lit 1))]
theorem atom0130Coded_decode : atom0130 = SparsePolynomial.decodeCubic 12 atom0130Coded := by decide +kernel
theorem atom0130Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (59328 : Int) atom0130Coded) := by
  have h := atom0130_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0130Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0131 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0131 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0131 = ((g 2) * (g 2) * (g 7)) := by
  norm_num [atom0131, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0131_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20160 : Int) atom0131) := by
  rw [SparsePolynomial.eval_scale, eval_atom0131]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0131Coded : CoefficientMerge.Poly := [(nat_lit 319, Int.ofNat (nat_lit 1))]
theorem atom0131Coded_decode : atom0131 = SparsePolynomial.decodeCubic 12 atom0131Coded := by decide +kernel
theorem atom0131Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (20160 : Int) atom0131Coded) := by
  have h := atom0131_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0131Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0132 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0132 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0132 = ((g 2) * (g 2) * (g 8)) := by
  norm_num [atom0132, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0132_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30912 : Int) atom0132) := by
  rw [SparsePolynomial.eval_scale, eval_atom0132]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0132Coded : CoefficientMerge.Poly := [(nat_lit 320, Int.ofNat (nat_lit 1))]
theorem atom0132Coded_decode : atom0132 = SparsePolynomial.decodeCubic 12 atom0132Coded := by decide +kernel
theorem atom0132Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (30912 : Int) atom0132Coded) := by
  have h := atom0132_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0132Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0133 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0133 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0133 = ((g 2) * (g 2) * (g 9)) := by
  norm_num [atom0133, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0133_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17856 : Int) atom0133) := by
  rw [SparsePolynomial.eval_scale, eval_atom0133]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0133Coded : CoefficientMerge.Poly := [(nat_lit 321, Int.ofNat (nat_lit 1))]
theorem atom0133Coded_decode : atom0133 = SparsePolynomial.decodeCubic 12 atom0133Coded := by decide +kernel
theorem atom0133Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (17856 : Int) atom0133Coded) := by
  have h := atom0133_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0133Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0134 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 2, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0134 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0134 = ((g 2) * (g 2) * (g 11)) := by
  norm_num [atom0134, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0134_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22080 : Int) atom0134) := by
  rw [SparsePolynomial.eval_scale, eval_atom0134]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0134Coded : CoefficientMerge.Poly := [(nat_lit 323, Int.ofNat (nat_lit 1))]
theorem atom0134Coded_decode : atom0134 = SparsePolynomial.decodeCubic 12 atom0134Coded := by decide +kernel
theorem atom0134Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (22080 : Int) atom0134Coded) := by
  have h := atom0134_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0134Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0135 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 3], Int.ofNat (nat_lit 1))]
theorem eval_atom0135 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0135 = ((g 2) * (g 3) * (g 3)) := by
  norm_num [atom0135, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0135_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24960 : Int) atom0135) := by
  rw [SparsePolynomial.eval_scale, eval_atom0135]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0135Coded : CoefficientMerge.Poly := [(nat_lit 327, Int.ofNat (nat_lit 1))]
theorem atom0135Coded_decode : atom0135 = SparsePolynomial.decodeCubic 12 atom0135Coded := by decide +kernel
theorem atom0135Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (24960 : Int) atom0135Coded) := by
  have h := atom0135_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0135Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0136 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0136 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0136 = ((g 2) * (g 3) * (g 4)) := by
  norm_num [atom0136, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0136_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38208 : Int) atom0136) := by
  rw [SparsePolynomial.eval_scale, eval_atom0136]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0136Coded : CoefficientMerge.Poly := [(nat_lit 328, Int.ofNat (nat_lit 1))]
theorem atom0136Coded_decode : atom0136 = SparsePolynomial.decodeCubic 12 atom0136Coded := by decide +kernel
theorem atom0136Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (38208 : Int) atom0136Coded) := by
  have h := atom0136_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0136Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0137 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0137 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0137 = ((g 2) * (g 3) * (g 5)) := by
  norm_num [atom0137, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0137_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40320 : Int) atom0137) := by
  rw [SparsePolynomial.eval_scale, eval_atom0137]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0137Coded : CoefficientMerge.Poly := [(nat_lit 329, Int.ofNat (nat_lit 1))]
theorem atom0137Coded_decode : atom0137 = SparsePolynomial.decodeCubic 12 atom0137Coded := by decide +kernel
theorem atom0137Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (40320 : Int) atom0137Coded) := by
  have h := atom0137_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0137Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0138 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0138 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0138 = ((g 2) * (g 3) * (g 6)) := by
  norm_num [atom0138, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0138_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (122688 : Int) atom0138) := by
  rw [SparsePolynomial.eval_scale, eval_atom0138]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0138Coded : CoefficientMerge.Poly := [(nat_lit 330, Int.ofNat (nat_lit 1))]
theorem atom0138Coded_decode : atom0138 = SparsePolynomial.decodeCubic 12 atom0138Coded := by decide +kernel
theorem atom0138Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (122688 : Int) atom0138Coded) := by
  have h := atom0138_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0138Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0139 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0139 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0139 = ((g 2) * (g 3) * (g 7)) := by
  norm_num [atom0139, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0139_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52992 : Int) atom0139) := by
  rw [SparsePolynomial.eval_scale, eval_atom0139]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0139Coded : CoefficientMerge.Poly := [(nat_lit 331, Int.ofNat (nat_lit 1))]
theorem atom0139Coded_decode : atom0139 = SparsePolynomial.decodeCubic 12 atom0139Coded := by decide +kernel
theorem atom0139Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (52992 : Int) atom0139Coded) := by
  have h := atom0139_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0139Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0140 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0140 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0140 = ((g 2) * (g 3) * (g 8)) := by
  norm_num [atom0140, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0140_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (83136 : Int) atom0140) := by
  rw [SparsePolynomial.eval_scale, eval_atom0140]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0140Coded : CoefficientMerge.Poly := [(nat_lit 332, Int.ofNat (nat_lit 1))]
theorem atom0140Coded_decode : atom0140 = SparsePolynomial.decodeCubic 12 atom0140Coded := by decide +kernel
theorem atom0140Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (83136 : Int) atom0140Coded) := by
  have h := atom0140_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0140Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0141 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0141 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0141 = ((g 2) * (g 3) * (g 9)) := by
  norm_num [atom0141, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0141_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65664 : Int) atom0141) := by
  rw [SparsePolynomial.eval_scale, eval_atom0141]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0141Coded : CoefficientMerge.Poly := [(nat_lit 333, Int.ofNat (nat_lit 1))]
theorem atom0141Coded_decode : atom0141 = SparsePolynomial.decodeCubic 12 atom0141Coded := by decide +kernel
theorem atom0141Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (65664 : Int) atom0141Coded) := by
  have h := atom0141_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0141Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0142 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0142 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0142 = ((g 2) * (g 3) * (g 10)) := by
  norm_num [atom0142, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0142_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52272 : Int) atom0142) := by
  rw [SparsePolynomial.eval_scale, eval_atom0142]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0142Coded : CoefficientMerge.Poly := [(nat_lit 334, Int.ofNat (nat_lit 1))]
theorem atom0142Coded_decode : atom0142 = SparsePolynomial.decodeCubic 12 atom0142Coded := by decide +kernel
theorem atom0142Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (52272 : Int) atom0142Coded) := by
  have h := atom0142_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0142Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0143 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 3, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0143 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0143 = ((g 2) * (g 3) * (g 11)) := by
  norm_num [atom0143, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0143_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84864 : Int) atom0143) := by
  rw [SparsePolynomial.eval_scale, eval_atom0143]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0143Coded : CoefficientMerge.Poly := [(nat_lit 335, Int.ofNat (nat_lit 1))]
theorem atom0143Coded_decode : atom0143 = SparsePolynomial.decodeCubic 12 atom0143Coded := by decide +kernel
theorem atom0143Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (84864 : Int) atom0143Coded) := by
  have h := atom0143_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0143Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0144 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 4], Int.ofNat (nat_lit 1))]
theorem eval_atom0144 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0144 = ((g 2) * (g 4) * (g 4)) := by
  norm_num [atom0144, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0144_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30336 : Int) atom0144) := by
  rw [SparsePolynomial.eval_scale, eval_atom0144]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0144Coded : CoefficientMerge.Poly := [(nat_lit 340, Int.ofNat (nat_lit 1))]
theorem atom0144Coded_decode : atom0144 = SparsePolynomial.decodeCubic 12 atom0144Coded := by decide +kernel
theorem atom0144Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (30336 : Int) atom0144Coded) := by
  have h := atom0144_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0144Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0145 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0145 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0145 = ((g 2) * (g 4) * (g 5)) := by
  norm_num [atom0145, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0145_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (62016 : Int) atom0145) := by
  rw [SparsePolynomial.eval_scale, eval_atom0145]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0145Coded : CoefficientMerge.Poly := [(nat_lit 341, Int.ofNat (nat_lit 1))]
theorem atom0145Coded_decode : atom0145 = SparsePolynomial.decodeCubic 12 atom0145Coded := by decide +kernel
theorem atom0145Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (62016 : Int) atom0145Coded) := by
  have h := atom0145_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0145Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0146 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0146 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0146 = ((g 2) * (g 4) * (g 6)) := by
  norm_num [atom0146, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0146_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126720 : Int) atom0146) := by
  rw [SparsePolynomial.eval_scale, eval_atom0146]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0146Coded : CoefficientMerge.Poly := [(nat_lit 342, Int.ofNat (nat_lit 1))]
theorem atom0146Coded_decode : atom0146 = SparsePolynomial.decodeCubic 12 atom0146Coded := by decide +kernel
theorem atom0146Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (126720 : Int) atom0146Coded) := by
  have h := atom0146_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0146Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0147 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0147 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0147 = ((g 2) * (g 4) * (g 7)) := by
  norm_num [atom0147, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0147_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (74496 : Int) atom0147) := by
  rw [SparsePolynomial.eval_scale, eval_atom0147]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0147Coded : CoefficientMerge.Poly := [(nat_lit 343, Int.ofNat (nat_lit 1))]
theorem atom0147Coded_decode : atom0147 = SparsePolynomial.decodeCubic 12 atom0147Coded := by decide +kernel
theorem atom0147Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (74496 : Int) atom0147Coded) := by
  have h := atom0147_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0147Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0148 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0148 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0148 = ((g 2) * (g 4) * (g 8)) := by
  norm_num [atom0148, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0148_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (104448 : Int) atom0148) := by
  rw [SparsePolynomial.eval_scale, eval_atom0148]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0148Coded : CoefficientMerge.Poly := [(nat_lit 344, Int.ofNat (nat_lit 1))]
theorem atom0148Coded_decode : atom0148 = SparsePolynomial.decodeCubic 12 atom0148Coded := by decide +kernel
theorem atom0148Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (104448 : Int) atom0148Coded) := by
  have h := atom0148_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0148Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0149 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0149 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0149 = ((g 2) * (g 4) * (g 9)) := by
  norm_num [atom0149, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0149_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (95616 : Int) atom0149) := by
  rw [SparsePolynomial.eval_scale, eval_atom0149]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0149Coded : CoefficientMerge.Poly := [(nat_lit 345, Int.ofNat (nat_lit 1))]
theorem atom0149Coded_decode : atom0149 = SparsePolynomial.decodeCubic 12 atom0149Coded := by decide +kernel
theorem atom0149Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (95616 : Int) atom0149Coded) := by
  have h := atom0149_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0149Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0150 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0150 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0150 = ((g 2) * (g 4) * (g 10)) := by
  norm_num [atom0150, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0150_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (90240 : Int) atom0150) := by
  rw [SparsePolynomial.eval_scale, eval_atom0150]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0150Coded : CoefficientMerge.Poly := [(nat_lit 346, Int.ofNat (nat_lit 1))]
theorem atom0150Coded_decode : atom0150 = SparsePolynomial.decodeCubic 12 atom0150Coded := by decide +kernel
theorem atom0150Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (90240 : Int) atom0150Coded) := by
  have h := atom0150_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0150Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0151 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 4, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0151 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0151 = ((g 2) * (g 4) * (g 11)) := by
  norm_num [atom0151, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0151_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (132096 : Int) atom0151) := by
  rw [SparsePolynomial.eval_scale, eval_atom0151]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0151Coded : CoefficientMerge.Poly := [(nat_lit 347, Int.ofNat (nat_lit 1))]
theorem atom0151Coded_decode : atom0151 = SparsePolynomial.decodeCubic 12 atom0151Coded := by decide +kernel
theorem atom0151Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (132096 : Int) atom0151Coded) := by
  have h := atom0151_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0151Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0152 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom0152 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0152 = ((g 2) * (g 5) * (g 5)) := by
  norm_num [atom0152, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0152_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43200 : Int) atom0152) := by
  rw [SparsePolynomial.eval_scale, eval_atom0152]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0152Coded : CoefficientMerge.Poly := [(nat_lit 353, Int.ofNat (nat_lit 1))]
theorem atom0152Coded_decode : atom0152 = SparsePolynomial.decodeCubic 12 atom0152Coded := by decide +kernel
theorem atom0152Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (43200 : Int) atom0152Coded) := by
  have h := atom0152_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0152Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0153 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0153 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0153 = ((g 2) * (g 5) * (g 6)) := by
  norm_num [atom0153, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0153_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (130752 : Int) atom0153) := by
  rw [SparsePolynomial.eval_scale, eval_atom0153]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0153Coded : CoefficientMerge.Poly := [(nat_lit 354, Int.ofNat (nat_lit 1))]
theorem atom0153Coded_decode : atom0153 = SparsePolynomial.decodeCubic 12 atom0153Coded := by decide +kernel
theorem atom0153Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (130752 : Int) atom0153Coded) := by
  have h := atom0153_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0153Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0154 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom0154 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0154 = ((g 2) * (g 5) * (g 7)) := by
  norm_num [atom0154, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0154_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (96768 : Int) atom0154) := by
  rw [SparsePolynomial.eval_scale, eval_atom0154]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0154Coded : CoefficientMerge.Poly := [(nat_lit 355, Int.ofNat (nat_lit 1))]
theorem atom0154Coded_decode : atom0154 = SparsePolynomial.decodeCubic 12 atom0154Coded := by decide +kernel
theorem atom0154Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (96768 : Int) atom0154Coded) := by
  have h := atom0154_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0154Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0155 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom0155 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0155 = ((g 2) * (g 5) * (g 8)) := by
  norm_num [atom0155, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0155_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (125760 : Int) atom0155) := by
  rw [SparsePolynomial.eval_scale, eval_atom0155]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0155Coded : CoefficientMerge.Poly := [(nat_lit 356, Int.ofNat (nat_lit 1))]
theorem atom0155Coded_decode : atom0155 = SparsePolynomial.decodeCubic 12 atom0155Coded := by decide +kernel
theorem atom0155Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (125760 : Int) atom0155Coded) := by
  have h := atom0155_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0155Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0156 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom0156 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0156 = ((g 2) * (g 5) * (g 9)) := by
  norm_num [atom0156, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0156_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (125568 : Int) atom0156) := by
  rw [SparsePolynomial.eval_scale, eval_atom0156]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0156Coded : CoefficientMerge.Poly := [(nat_lit 357, Int.ofNat (nat_lit 1))]
theorem atom0156Coded_decode : atom0156 = SparsePolynomial.decodeCubic 12 atom0156Coded := by decide +kernel
theorem atom0156Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (125568 : Int) atom0156Coded) := by
  have h := atom0156_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0156Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0157 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom0157 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0157 = ((g 2) * (g 5) * (g 10)) := by
  norm_num [atom0157, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0157_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (114624 : Int) atom0157) := by
  rw [SparsePolynomial.eval_scale, eval_atom0157]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0157Coded : CoefficientMerge.Poly := [(nat_lit 358, Int.ofNat (nat_lit 1))]
theorem atom0157Coded_decode : atom0157 = SparsePolynomial.decodeCubic 12 atom0157Coded := by decide +kernel
theorem atom0157Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (114624 : Int) atom0157Coded) := by
  have h := atom0157_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0157Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0158 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0158 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0158 = ((g 2) * (g 5) * (g 11)) := by
  norm_num [atom0158, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0158_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (179328 : Int) atom0158) := by
  rw [SparsePolynomial.eval_scale, eval_atom0158]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0158Coded : CoefficientMerge.Poly := [(nat_lit 359, Int.ofNat (nat_lit 1))]
theorem atom0158Coded_decode : atom0158 = SparsePolynomial.decodeCubic 12 atom0158Coded := by decide +kernel
theorem atom0158Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (179328 : Int) atom0158Coded) := by
  have h := atom0158_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0158Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0159 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom0159 (g : Fin 12 → ℝ) : SparsePolynomial.eval (gapValues g) atom0159 = ((g 2) * (g 6) * (g 6)) := by
  norm_num [atom0159, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0159_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105408 : Int) atom0159) := by
  rw [SparsePolynomial.eval_scale, eval_atom0159]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0159Coded : CoefficientMerge.Poly := [(nat_lit 366, Int.ofNat (nat_lit 1))]
theorem atom0159Coded_decode : atom0159 = SparsePolynomial.decodeCubic 12 atom0159Coded := by decide +kernel
theorem atom0159Coded_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) (CoefficientMerge.scale (105408 : Int) atom0159Coded) := by
  have h := atom0159_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0159Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block001 : CoefficientMerge.Poly := [(nat_lit 179, Int.ofNat (nat_lit 62752)), (nat_lit 183, Int.ofNat (nat_lit 17568)), (nat_lit 184, Int.ofNat (nat_lit 24768)), (nat_lit 185, Int.ofNat (nat_lit 28928)), (nat_lit 186, Int.ofNat (nat_lit 107136)), (nat_lit 187, Int.ofNat (nat_lit 57088)), (nat_lit 188, Int.ofNat (nat_lit 76416)), (nat_lit 189, Int.ofNat (nat_lit 82560)), (nat_lit 190, Int.ofNat (nat_lit 84440)), (nat_lit 191, Int.ofNat (nat_lit 89344)), (nat_lit 196, Int.ofNat (nat_lit 21888)), (nat_lit 197, Int.ofNat (nat_lit 39008)), (nat_lit 198, Int.ofNat (nat_lit 109824)), (nat_lit 199, Int.ofNat (nat_lit 69952)), (nat_lit 200, Int.ofNat (nat_lit 90624)), (nat_lit 201, Int.ofNat (nat_lit 102528)), (nat_lit 202, Int.ofNat (nat_lit 109856)), (nat_lit 203, Int.ofNat (nat_lit 120832)), (nat_lit 209, Int.ofNat (nat_lit 33152)), (nat_lit 210, Int.ofNat (nat_lit 113536)), (nat_lit 211, Int.ofNat (nat_lit 83712)), (nat_lit 212, Int.ofNat (nat_lit 104320)), (nat_lit 213, Int.ofNat (nat_lit 121728)), (nat_lit 214, Int.ofNat (nat_lit 127200)), (nat_lit 215, Int.ofNat (nat_lit 150016)), (nat_lit 222, Int.ofNat (nat_lit 95616)), (nat_lit 223, Int.ofNat (nat_lit 147584)), (nat_lit 224, Int.ofNat (nat_lit 195072)), (nat_lit 225, Int.ofNat (nat_lit 218112)), (nat_lit 226, Int.ofNat (nat_lit 134656)), (nat_lit 227, Int.ofNat (nat_lit 168824)), (nat_lit 235, Int.ofNat (nat_lit 60736)), (nat_lit 236, Int.ofNat (nat_lit 140864)), (nat_lit 237, Int.ofNat (nat_lit 191712)), (nat_lit 238, Int.ofNat (nat_lit 142048)), (nat_lit 239, Int.ofNat (nat_lit 166552)), (nat_lit 248, Int.ofNat (nat_lit 105216)), (nat_lit 249, Int.ofNat (nat_lit 193344)), (nat_lit 250, Int.ofNat (nat_lit 145792)), (nat_lit 251, Int.ofNat (nat_lit 177848)), (nat_lit 261, Int.ofNat (nat_lit 81504)), (nat_lit 262, Int.ofNat (nat_lit 118752)), (nat_lit 263, Int.ofNat (nat_lit 152720)), (nat_lit 274, Int.ofNat (nat_lit 26176)), (nat_lit 275, Int.ofNat (nat_lit 76064)), (nat_lit 287, Int.ofNat (nat_lit 34272)), (nat_lit 314, Int.ofNat (nat_lit 8640)), (nat_lit 315, Int.ofNat (nat_lit 24768)), (nat_lit 316, Int.ofNat (nat_lit 23616)), (nat_lit 317, Int.ofNat (nat_lit 22464)), (nat_lit 318, Int.ofNat (nat_lit 59328)), (nat_lit 319, Int.ofNat (nat_lit 20160)), (nat_lit 320, Int.ofNat (nat_lit 30912)), (nat_lit 321, Int.ofNat (nat_lit 17856)), (nat_lit 323, Int.ofNat (nat_lit 22080)), (nat_lit 327, Int.ofNat (nat_lit 24960)), (nat_lit 328, Int.ofNat (nat_lit 38208)), (nat_lit 329, Int.ofNat (nat_lit 40320)), (nat_lit 330, Int.ofNat (nat_lit 122688)), (nat_lit 331, Int.ofNat (nat_lit 52992)), (nat_lit 332, Int.ofNat (nat_lit 83136)), (nat_lit 333, Int.ofNat (nat_lit 65664)), (nat_lit 334, Int.ofNat (nat_lit 52272)), (nat_lit 335, Int.ofNat (nat_lit 84864)), (nat_lit 340, Int.ofNat (nat_lit 30336)), (nat_lit 341, Int.ofNat (nat_lit 62016)), (nat_lit 342, Int.ofNat (nat_lit 126720)), (nat_lit 343, Int.ofNat (nat_lit 74496)), (nat_lit 344, Int.ofNat (nat_lit 104448)), (nat_lit 345, Int.ofNat (nat_lit 95616)), (nat_lit 346, Int.ofNat (nat_lit 90240)), (nat_lit 347, Int.ofNat (nat_lit 132096)), (nat_lit 353, Int.ofNat (nat_lit 43200)), (nat_lit 354, Int.ofNat (nat_lit 130752)), (nat_lit 355, Int.ofNat (nat_lit 96768)), (nat_lit 356, Int.ofNat (nat_lit 125760)), (nat_lit 357, Int.ofNat (nat_lit 125568)), (nat_lit 358, Int.ofNat (nat_lit 114624)), (nat_lit 359, Int.ofNat (nat_lit 179328)), (nat_lit 366, Int.ofNat (nat_lit 105408))]
def block001_data_flat000 : CoefficientMerge.Poly := [(nat_lit 179, Int.ofNat (nat_lit 62752))]
theorem block001_data_flat000_step : block001_data_flat000 = (CoefficientMerge.scale (62752 : Int) atom0080Coded) := by decide +kernel
theorem block001_data_flat000_original : block001_data_flat000 = (CoefficientMerge.scale (62752 : Int) atom0080Coded) := by
  rw [block001_data_flat000_step]
def block001_data_flat001 : CoefficientMerge.Poly := [(nat_lit 183, Int.ofNat (nat_lit 17568))]
theorem block001_data_flat001_step : block001_data_flat001 = (CoefficientMerge.scale (17568 : Int) atom0081Coded) := by decide +kernel
theorem block001_data_flat001_original : block001_data_flat001 = (CoefficientMerge.scale (17568 : Int) atom0081Coded) := by
  rw [block001_data_flat001_step]
def block001_data_flat002 : CoefficientMerge.Poly := [(nat_lit 179, Int.ofNat (nat_lit 62752)), (nat_lit 183, Int.ofNat (nat_lit 17568))]
theorem block001_data_flat002_step : block001_data_flat002 = (CoefficientMerge.fastMerge block001_data_flat000 block001_data_flat001) := by decide +kernel
theorem block001_data_flat002_original : block001_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (62752 : Int) atom0080Coded) (CoefficientMerge.scale (17568 : Int) atom0081Coded)) := by
  rw [block001_data_flat002_step, block001_data_flat000_original, block001_data_flat001_original]
def block001_data_flat003 : CoefficientMerge.Poly := [(nat_lit 184, Int.ofNat (nat_lit 24768))]
theorem block001_data_flat003_step : block001_data_flat003 = (CoefficientMerge.scale (24768 : Int) atom0082Coded) := by decide +kernel
theorem block001_data_flat003_original : block001_data_flat003 = (CoefficientMerge.scale (24768 : Int) atom0082Coded) := by
  rw [block001_data_flat003_step]
def block001_data_flat004 : CoefficientMerge.Poly := [(nat_lit 185, Int.ofNat (nat_lit 28928))]
theorem block001_data_flat004_step : block001_data_flat004 = (CoefficientMerge.scale (28928 : Int) atom0083Coded) := by decide +kernel
theorem block001_data_flat004_original : block001_data_flat004 = (CoefficientMerge.scale (28928 : Int) atom0083Coded) := by
  rw [block001_data_flat004_step]
def block001_data_flat005 : CoefficientMerge.Poly := [(nat_lit 186, Int.ofNat (nat_lit 107136))]
theorem block001_data_flat005_step : block001_data_flat005 = (CoefficientMerge.scale (107136 : Int) atom0084Coded) := by decide +kernel
theorem block001_data_flat005_original : block001_data_flat005 = (CoefficientMerge.scale (107136 : Int) atom0084Coded) := by
  rw [block001_data_flat005_step]
def block001_data_flat006 : CoefficientMerge.Poly := [(nat_lit 185, Int.ofNat (nat_lit 28928)), (nat_lit 186, Int.ofNat (nat_lit 107136))]
theorem block001_data_flat006_step : block001_data_flat006 = (CoefficientMerge.fastMerge block001_data_flat004 block001_data_flat005) := by decide +kernel
theorem block001_data_flat006_original : block001_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (28928 : Int) atom0083Coded) (CoefficientMerge.scale (107136 : Int) atom0084Coded)) := by
  rw [block001_data_flat006_step, block001_data_flat004_original, block001_data_flat005_original]
def block001_data_flat007 : CoefficientMerge.Poly := [(nat_lit 184, Int.ofNat (nat_lit 24768)), (nat_lit 185, Int.ofNat (nat_lit 28928)), (nat_lit 186, Int.ofNat (nat_lit 107136))]
theorem block001_data_flat007_step : block001_data_flat007 = (CoefficientMerge.fastMerge block001_data_flat003 block001_data_flat006) := by decide +kernel
theorem block001_data_flat007_original : block001_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24768 : Int) atom0082Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28928 : Int) atom0083Coded) (CoefficientMerge.scale (107136 : Int) atom0084Coded))) := by
  rw [block001_data_flat007_step, block001_data_flat003_original, block001_data_flat006_original]
def block001_data_flat008 : CoefficientMerge.Poly := [(nat_lit 179, Int.ofNat (nat_lit 62752)), (nat_lit 183, Int.ofNat (nat_lit 17568)), (nat_lit 184, Int.ofNat (nat_lit 24768)), (nat_lit 185, Int.ofNat (nat_lit 28928)), (nat_lit 186, Int.ofNat (nat_lit 107136))]
theorem block001_data_flat008_step : block001_data_flat008 = (CoefficientMerge.fastMerge block001_data_flat002 block001_data_flat007) := by decide +kernel
theorem block001_data_flat008_original : block001_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62752 : Int) atom0080Coded) (CoefficientMerge.scale (17568 : Int) atom0081Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24768 : Int) atom0082Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28928 : Int) atom0083Coded) (CoefficientMerge.scale (107136 : Int) atom0084Coded)))) := by
  rw [block001_data_flat008_step, block001_data_flat002_original, block001_data_flat007_original]
def block001_data_flat009 : CoefficientMerge.Poly := [(nat_lit 187, Int.ofNat (nat_lit 57088))]
theorem block001_data_flat009_step : block001_data_flat009 = (CoefficientMerge.scale (57088 : Int) atom0085Coded) := by decide +kernel
theorem block001_data_flat009_original : block001_data_flat009 = (CoefficientMerge.scale (57088 : Int) atom0085Coded) := by
  rw [block001_data_flat009_step]
def block001_data_flat010 : CoefficientMerge.Poly := [(nat_lit 188, Int.ofNat (nat_lit 76416))]
theorem block001_data_flat010_step : block001_data_flat010 = (CoefficientMerge.scale (76416 : Int) atom0086Coded) := by decide +kernel
theorem block001_data_flat010_original : block001_data_flat010 = (CoefficientMerge.scale (76416 : Int) atom0086Coded) := by
  rw [block001_data_flat010_step]
def block001_data_flat011 : CoefficientMerge.Poly := [(nat_lit 187, Int.ofNat (nat_lit 57088)), (nat_lit 188, Int.ofNat (nat_lit 76416))]
theorem block001_data_flat011_step : block001_data_flat011 = (CoefficientMerge.fastMerge block001_data_flat009 block001_data_flat010) := by decide +kernel
theorem block001_data_flat011_original : block001_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (57088 : Int) atom0085Coded) (CoefficientMerge.scale (76416 : Int) atom0086Coded)) := by
  rw [block001_data_flat011_step, block001_data_flat009_original, block001_data_flat010_original]
def block001_data_flat012 : CoefficientMerge.Poly := [(nat_lit 189, Int.ofNat (nat_lit 82560))]
theorem block001_data_flat012_step : block001_data_flat012 = (CoefficientMerge.scale (82560 : Int) atom0087Coded) := by decide +kernel
theorem block001_data_flat012_original : block001_data_flat012 = (CoefficientMerge.scale (82560 : Int) atom0087Coded) := by
  rw [block001_data_flat012_step]
def block001_data_flat013 : CoefficientMerge.Poly := [(nat_lit 190, Int.ofNat (nat_lit 84440))]
theorem block001_data_flat013_step : block001_data_flat013 = (CoefficientMerge.scale (84440 : Int) atom0088Coded) := by decide +kernel
theorem block001_data_flat013_original : block001_data_flat013 = (CoefficientMerge.scale (84440 : Int) atom0088Coded) := by
  rw [block001_data_flat013_step]
def block001_data_flat014 : CoefficientMerge.Poly := [(nat_lit 191, Int.ofNat (nat_lit 89344))]
theorem block001_data_flat014_step : block001_data_flat014 = (CoefficientMerge.scale (89344 : Int) atom0089Coded) := by decide +kernel
theorem block001_data_flat014_original : block001_data_flat014 = (CoefficientMerge.scale (89344 : Int) atom0089Coded) := by
  rw [block001_data_flat014_step]
def block001_data_flat015 : CoefficientMerge.Poly := [(nat_lit 190, Int.ofNat (nat_lit 84440)), (nat_lit 191, Int.ofNat (nat_lit 89344))]
theorem block001_data_flat015_step : block001_data_flat015 = (CoefficientMerge.fastMerge block001_data_flat013 block001_data_flat014) := by decide +kernel
theorem block001_data_flat015_original : block001_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (84440 : Int) atom0088Coded) (CoefficientMerge.scale (89344 : Int) atom0089Coded)) := by
  rw [block001_data_flat015_step, block001_data_flat013_original, block001_data_flat014_original]
def block001_data_flat016 : CoefficientMerge.Poly := [(nat_lit 189, Int.ofNat (nat_lit 82560)), (nat_lit 190, Int.ofNat (nat_lit 84440)), (nat_lit 191, Int.ofNat (nat_lit 89344))]
theorem block001_data_flat016_step : block001_data_flat016 = (CoefficientMerge.fastMerge block001_data_flat012 block001_data_flat015) := by decide +kernel
theorem block001_data_flat016_original : block001_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (82560 : Int) atom0087Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84440 : Int) atom0088Coded) (CoefficientMerge.scale (89344 : Int) atom0089Coded))) := by
  rw [block001_data_flat016_step, block001_data_flat012_original, block001_data_flat015_original]
def block001_data_flat017 : CoefficientMerge.Poly := [(nat_lit 187, Int.ofNat (nat_lit 57088)), (nat_lit 188, Int.ofNat (nat_lit 76416)), (nat_lit 189, Int.ofNat (nat_lit 82560)), (nat_lit 190, Int.ofNat (nat_lit 84440)), (nat_lit 191, Int.ofNat (nat_lit 89344))]
theorem block001_data_flat017_step : block001_data_flat017 = (CoefficientMerge.fastMerge block001_data_flat011 block001_data_flat016) := by decide +kernel
theorem block001_data_flat017_original : block001_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57088 : Int) atom0085Coded) (CoefficientMerge.scale (76416 : Int) atom0086Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82560 : Int) atom0087Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84440 : Int) atom0088Coded) (CoefficientMerge.scale (89344 : Int) atom0089Coded)))) := by
  rw [block001_data_flat017_step, block001_data_flat011_original, block001_data_flat016_original]
def block001_data_flat018 : CoefficientMerge.Poly := [(nat_lit 179, Int.ofNat (nat_lit 62752)), (nat_lit 183, Int.ofNat (nat_lit 17568)), (nat_lit 184, Int.ofNat (nat_lit 24768)), (nat_lit 185, Int.ofNat (nat_lit 28928)), (nat_lit 186, Int.ofNat (nat_lit 107136)), (nat_lit 187, Int.ofNat (nat_lit 57088)), (nat_lit 188, Int.ofNat (nat_lit 76416)), (nat_lit 189, Int.ofNat (nat_lit 82560)), (nat_lit 190, Int.ofNat (nat_lit 84440)), (nat_lit 191, Int.ofNat (nat_lit 89344))]
theorem block001_data_flat018_step : block001_data_flat018 = (CoefficientMerge.fastMerge block001_data_flat008 block001_data_flat017) := by decide +kernel
theorem block001_data_flat018_original : block001_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62752 : Int) atom0080Coded) (CoefficientMerge.scale (17568 : Int) atom0081Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24768 : Int) atom0082Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28928 : Int) atom0083Coded) (CoefficientMerge.scale (107136 : Int) atom0084Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57088 : Int) atom0085Coded) (CoefficientMerge.scale (76416 : Int) atom0086Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82560 : Int) atom0087Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84440 : Int) atom0088Coded) (CoefficientMerge.scale (89344 : Int) atom0089Coded))))) := by
  rw [block001_data_flat018_step, block001_data_flat008_original, block001_data_flat017_original]
def block001_data_flat019 : CoefficientMerge.Poly := [(nat_lit 196, Int.ofNat (nat_lit 21888))]
theorem block001_data_flat019_step : block001_data_flat019 = (CoefficientMerge.scale (21888 : Int) atom0090Coded) := by decide +kernel
theorem block001_data_flat019_original : block001_data_flat019 = (CoefficientMerge.scale (21888 : Int) atom0090Coded) := by
  rw [block001_data_flat019_step]
def block001_data_flat020 : CoefficientMerge.Poly := [(nat_lit 197, Int.ofNat (nat_lit 39008))]
theorem block001_data_flat020_step : block001_data_flat020 = (CoefficientMerge.scale (39008 : Int) atom0091Coded) := by decide +kernel
theorem block001_data_flat020_original : block001_data_flat020 = (CoefficientMerge.scale (39008 : Int) atom0091Coded) := by
  rw [block001_data_flat020_step]
def block001_data_flat021 : CoefficientMerge.Poly := [(nat_lit 196, Int.ofNat (nat_lit 21888)), (nat_lit 197, Int.ofNat (nat_lit 39008))]
theorem block001_data_flat021_step : block001_data_flat021 = (CoefficientMerge.fastMerge block001_data_flat019 block001_data_flat020) := by decide +kernel
theorem block001_data_flat021_original : block001_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21888 : Int) atom0090Coded) (CoefficientMerge.scale (39008 : Int) atom0091Coded)) := by
  rw [block001_data_flat021_step, block001_data_flat019_original, block001_data_flat020_original]
def block001_data_flat022 : CoefficientMerge.Poly := [(nat_lit 198, Int.ofNat (nat_lit 109824))]
theorem block001_data_flat022_step : block001_data_flat022 = (CoefficientMerge.scale (109824 : Int) atom0092Coded) := by decide +kernel
theorem block001_data_flat022_original : block001_data_flat022 = (CoefficientMerge.scale (109824 : Int) atom0092Coded) := by
  rw [block001_data_flat022_step]
def block001_data_flat023 : CoefficientMerge.Poly := [(nat_lit 199, Int.ofNat (nat_lit 69952))]
theorem block001_data_flat023_step : block001_data_flat023 = (CoefficientMerge.scale (69952 : Int) atom0093Coded) := by decide +kernel
theorem block001_data_flat023_original : block001_data_flat023 = (CoefficientMerge.scale (69952 : Int) atom0093Coded) := by
  rw [block001_data_flat023_step]
def block001_data_flat024 : CoefficientMerge.Poly := [(nat_lit 200, Int.ofNat (nat_lit 90624))]
theorem block001_data_flat024_step : block001_data_flat024 = (CoefficientMerge.scale (90624 : Int) atom0094Coded) := by decide +kernel
theorem block001_data_flat024_original : block001_data_flat024 = (CoefficientMerge.scale (90624 : Int) atom0094Coded) := by
  rw [block001_data_flat024_step]
def block001_data_flat025 : CoefficientMerge.Poly := [(nat_lit 199, Int.ofNat (nat_lit 69952)), (nat_lit 200, Int.ofNat (nat_lit 90624))]
theorem block001_data_flat025_step : block001_data_flat025 = (CoefficientMerge.fastMerge block001_data_flat023 block001_data_flat024) := by decide +kernel
theorem block001_data_flat025_original : block001_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (69952 : Int) atom0093Coded) (CoefficientMerge.scale (90624 : Int) atom0094Coded)) := by
  rw [block001_data_flat025_step, block001_data_flat023_original, block001_data_flat024_original]
def block001_data_flat026 : CoefficientMerge.Poly := [(nat_lit 198, Int.ofNat (nat_lit 109824)), (nat_lit 199, Int.ofNat (nat_lit 69952)), (nat_lit 200, Int.ofNat (nat_lit 90624))]
theorem block001_data_flat026_step : block001_data_flat026 = (CoefficientMerge.fastMerge block001_data_flat022 block001_data_flat025) := by decide +kernel
theorem block001_data_flat026_original : block001_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (109824 : Int) atom0092Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69952 : Int) atom0093Coded) (CoefficientMerge.scale (90624 : Int) atom0094Coded))) := by
  rw [block001_data_flat026_step, block001_data_flat022_original, block001_data_flat025_original]
def block001_data_flat027 : CoefficientMerge.Poly := [(nat_lit 196, Int.ofNat (nat_lit 21888)), (nat_lit 197, Int.ofNat (nat_lit 39008)), (nat_lit 198, Int.ofNat (nat_lit 109824)), (nat_lit 199, Int.ofNat (nat_lit 69952)), (nat_lit 200, Int.ofNat (nat_lit 90624))]
theorem block001_data_flat027_step : block001_data_flat027 = (CoefficientMerge.fastMerge block001_data_flat021 block001_data_flat026) := by decide +kernel
theorem block001_data_flat027_original : block001_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21888 : Int) atom0090Coded) (CoefficientMerge.scale (39008 : Int) atom0091Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109824 : Int) atom0092Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69952 : Int) atom0093Coded) (CoefficientMerge.scale (90624 : Int) atom0094Coded)))) := by
  rw [block001_data_flat027_step, block001_data_flat021_original, block001_data_flat026_original]
def block001_data_flat028 : CoefficientMerge.Poly := [(nat_lit 201, Int.ofNat (nat_lit 102528))]
theorem block001_data_flat028_step : block001_data_flat028 = (CoefficientMerge.scale (102528 : Int) atom0095Coded) := by decide +kernel
theorem block001_data_flat028_original : block001_data_flat028 = (CoefficientMerge.scale (102528 : Int) atom0095Coded) := by
  rw [block001_data_flat028_step]
def block001_data_flat029 : CoefficientMerge.Poly := [(nat_lit 202, Int.ofNat (nat_lit 109856))]
theorem block001_data_flat029_step : block001_data_flat029 = (CoefficientMerge.scale (109856 : Int) atom0096Coded) := by decide +kernel
theorem block001_data_flat029_original : block001_data_flat029 = (CoefficientMerge.scale (109856 : Int) atom0096Coded) := by
  rw [block001_data_flat029_step]
def block001_data_flat030 : CoefficientMerge.Poly := [(nat_lit 201, Int.ofNat (nat_lit 102528)), (nat_lit 202, Int.ofNat (nat_lit 109856))]
theorem block001_data_flat030_step : block001_data_flat030 = (CoefficientMerge.fastMerge block001_data_flat028 block001_data_flat029) := by decide +kernel
theorem block001_data_flat030_original : block001_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (102528 : Int) atom0095Coded) (CoefficientMerge.scale (109856 : Int) atom0096Coded)) := by
  rw [block001_data_flat030_step, block001_data_flat028_original, block001_data_flat029_original]
def block001_data_flat031 : CoefficientMerge.Poly := [(nat_lit 203, Int.ofNat (nat_lit 120832))]
theorem block001_data_flat031_step : block001_data_flat031 = (CoefficientMerge.scale (120832 : Int) atom0097Coded) := by decide +kernel
theorem block001_data_flat031_original : block001_data_flat031 = (CoefficientMerge.scale (120832 : Int) atom0097Coded) := by
  rw [block001_data_flat031_step]
def block001_data_flat032 : CoefficientMerge.Poly := [(nat_lit 209, Int.ofNat (nat_lit 33152))]
theorem block001_data_flat032_step : block001_data_flat032 = (CoefficientMerge.scale (33152 : Int) atom0098Coded) := by decide +kernel
theorem block001_data_flat032_original : block001_data_flat032 = (CoefficientMerge.scale (33152 : Int) atom0098Coded) := by
  rw [block001_data_flat032_step]
def block001_data_flat033 : CoefficientMerge.Poly := [(nat_lit 210, Int.ofNat (nat_lit 113536))]
theorem block001_data_flat033_step : block001_data_flat033 = (CoefficientMerge.scale (113536 : Int) atom0099Coded) := by decide +kernel
theorem block001_data_flat033_original : block001_data_flat033 = (CoefficientMerge.scale (113536 : Int) atom0099Coded) := by
  rw [block001_data_flat033_step]
def block001_data_flat034 : CoefficientMerge.Poly := [(nat_lit 209, Int.ofNat (nat_lit 33152)), (nat_lit 210, Int.ofNat (nat_lit 113536))]
theorem block001_data_flat034_step : block001_data_flat034 = (CoefficientMerge.fastMerge block001_data_flat032 block001_data_flat033) := by decide +kernel
theorem block001_data_flat034_original : block001_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (33152 : Int) atom0098Coded) (CoefficientMerge.scale (113536 : Int) atom0099Coded)) := by
  rw [block001_data_flat034_step, block001_data_flat032_original, block001_data_flat033_original]
def block001_data_flat035 : CoefficientMerge.Poly := [(nat_lit 203, Int.ofNat (nat_lit 120832)), (nat_lit 209, Int.ofNat (nat_lit 33152)), (nat_lit 210, Int.ofNat (nat_lit 113536))]
theorem block001_data_flat035_step : block001_data_flat035 = (CoefficientMerge.fastMerge block001_data_flat031 block001_data_flat034) := by decide +kernel
theorem block001_data_flat035_original : block001_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (120832 : Int) atom0097Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33152 : Int) atom0098Coded) (CoefficientMerge.scale (113536 : Int) atom0099Coded))) := by
  rw [block001_data_flat035_step, block001_data_flat031_original, block001_data_flat034_original]
def block001_data_flat036 : CoefficientMerge.Poly := [(nat_lit 201, Int.ofNat (nat_lit 102528)), (nat_lit 202, Int.ofNat (nat_lit 109856)), (nat_lit 203, Int.ofNat (nat_lit 120832)), (nat_lit 209, Int.ofNat (nat_lit 33152)), (nat_lit 210, Int.ofNat (nat_lit 113536))]
theorem block001_data_flat036_step : block001_data_flat036 = (CoefficientMerge.fastMerge block001_data_flat030 block001_data_flat035) := by decide +kernel
theorem block001_data_flat036_original : block001_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (102528 : Int) atom0095Coded) (CoefficientMerge.scale (109856 : Int) atom0096Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120832 : Int) atom0097Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33152 : Int) atom0098Coded) (CoefficientMerge.scale (113536 : Int) atom0099Coded)))) := by
  rw [block001_data_flat036_step, block001_data_flat030_original, block001_data_flat035_original]
def block001_data_flat037 : CoefficientMerge.Poly := [(nat_lit 196, Int.ofNat (nat_lit 21888)), (nat_lit 197, Int.ofNat (nat_lit 39008)), (nat_lit 198, Int.ofNat (nat_lit 109824)), (nat_lit 199, Int.ofNat (nat_lit 69952)), (nat_lit 200, Int.ofNat (nat_lit 90624)), (nat_lit 201, Int.ofNat (nat_lit 102528)), (nat_lit 202, Int.ofNat (nat_lit 109856)), (nat_lit 203, Int.ofNat (nat_lit 120832)), (nat_lit 209, Int.ofNat (nat_lit 33152)), (nat_lit 210, Int.ofNat (nat_lit 113536))]
theorem block001_data_flat037_step : block001_data_flat037 = (CoefficientMerge.fastMerge block001_data_flat027 block001_data_flat036) := by decide +kernel
theorem block001_data_flat037_original : block001_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21888 : Int) atom0090Coded) (CoefficientMerge.scale (39008 : Int) atom0091Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109824 : Int) atom0092Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69952 : Int) atom0093Coded) (CoefficientMerge.scale (90624 : Int) atom0094Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (102528 : Int) atom0095Coded) (CoefficientMerge.scale (109856 : Int) atom0096Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120832 : Int) atom0097Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33152 : Int) atom0098Coded) (CoefficientMerge.scale (113536 : Int) atom0099Coded))))) := by
  rw [block001_data_flat037_step, block001_data_flat027_original, block001_data_flat036_original]
def block001_data_flat038 : CoefficientMerge.Poly := [(nat_lit 179, Int.ofNat (nat_lit 62752)), (nat_lit 183, Int.ofNat (nat_lit 17568)), (nat_lit 184, Int.ofNat (nat_lit 24768)), (nat_lit 185, Int.ofNat (nat_lit 28928)), (nat_lit 186, Int.ofNat (nat_lit 107136)), (nat_lit 187, Int.ofNat (nat_lit 57088)), (nat_lit 188, Int.ofNat (nat_lit 76416)), (nat_lit 189, Int.ofNat (nat_lit 82560)), (nat_lit 190, Int.ofNat (nat_lit 84440)), (nat_lit 191, Int.ofNat (nat_lit 89344)), (nat_lit 196, Int.ofNat (nat_lit 21888)), (nat_lit 197, Int.ofNat (nat_lit 39008)), (nat_lit 198, Int.ofNat (nat_lit 109824)), (nat_lit 199, Int.ofNat (nat_lit 69952)), (nat_lit 200, Int.ofNat (nat_lit 90624)), (nat_lit 201, Int.ofNat (nat_lit 102528)), (nat_lit 202, Int.ofNat (nat_lit 109856)), (nat_lit 203, Int.ofNat (nat_lit 120832)), (nat_lit 209, Int.ofNat (nat_lit 33152)), (nat_lit 210, Int.ofNat (nat_lit 113536))]
theorem block001_data_flat038_step : block001_data_flat038 = (CoefficientMerge.fastMerge block001_data_flat018 block001_data_flat037) := by decide +kernel
theorem block001_data_flat038_original : block001_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62752 : Int) atom0080Coded) (CoefficientMerge.scale (17568 : Int) atom0081Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24768 : Int) atom0082Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28928 : Int) atom0083Coded) (CoefficientMerge.scale (107136 : Int) atom0084Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57088 : Int) atom0085Coded) (CoefficientMerge.scale (76416 : Int) atom0086Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82560 : Int) atom0087Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84440 : Int) atom0088Coded) (CoefficientMerge.scale (89344 : Int) atom0089Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21888 : Int) atom0090Coded) (CoefficientMerge.scale (39008 : Int) atom0091Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109824 : Int) atom0092Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69952 : Int) atom0093Coded) (CoefficientMerge.scale (90624 : Int) atom0094Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (102528 : Int) atom0095Coded) (CoefficientMerge.scale (109856 : Int) atom0096Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120832 : Int) atom0097Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33152 : Int) atom0098Coded) (CoefficientMerge.scale (113536 : Int) atom0099Coded)))))) := by
  rw [block001_data_flat038_step, block001_data_flat018_original, block001_data_flat037_original]
def block001_data_flat039 : CoefficientMerge.Poly := [(nat_lit 211, Int.ofNat (nat_lit 83712))]
theorem block001_data_flat039_step : block001_data_flat039 = (CoefficientMerge.scale (83712 : Int) atom0100Coded) := by decide +kernel
theorem block001_data_flat039_original : block001_data_flat039 = (CoefficientMerge.scale (83712 : Int) atom0100Coded) := by
  rw [block001_data_flat039_step]
def block001_data_flat040 : CoefficientMerge.Poly := [(nat_lit 212, Int.ofNat (nat_lit 104320))]
theorem block001_data_flat040_step : block001_data_flat040 = (CoefficientMerge.scale (104320 : Int) atom0101Coded) := by decide +kernel
theorem block001_data_flat040_original : block001_data_flat040 = (CoefficientMerge.scale (104320 : Int) atom0101Coded) := by
  rw [block001_data_flat040_step]
def block001_data_flat041 : CoefficientMerge.Poly := [(nat_lit 211, Int.ofNat (nat_lit 83712)), (nat_lit 212, Int.ofNat (nat_lit 104320))]
theorem block001_data_flat041_step : block001_data_flat041 = (CoefficientMerge.fastMerge block001_data_flat039 block001_data_flat040) := by decide +kernel
theorem block001_data_flat041_original : block001_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (83712 : Int) atom0100Coded) (CoefficientMerge.scale (104320 : Int) atom0101Coded)) := by
  rw [block001_data_flat041_step, block001_data_flat039_original, block001_data_flat040_original]
def block001_data_flat042 : CoefficientMerge.Poly := [(nat_lit 213, Int.ofNat (nat_lit 121728))]
theorem block001_data_flat042_step : block001_data_flat042 = (CoefficientMerge.scale (121728 : Int) atom0102Coded) := by decide +kernel
theorem block001_data_flat042_original : block001_data_flat042 = (CoefficientMerge.scale (121728 : Int) atom0102Coded) := by
  rw [block001_data_flat042_step]
def block001_data_flat043 : CoefficientMerge.Poly := [(nat_lit 214, Int.ofNat (nat_lit 127200))]
theorem block001_data_flat043_step : block001_data_flat043 = (CoefficientMerge.scale (127200 : Int) atom0103Coded) := by decide +kernel
theorem block001_data_flat043_original : block001_data_flat043 = (CoefficientMerge.scale (127200 : Int) atom0103Coded) := by
  rw [block001_data_flat043_step]
def block001_data_flat044 : CoefficientMerge.Poly := [(nat_lit 215, Int.ofNat (nat_lit 150016))]
theorem block001_data_flat044_step : block001_data_flat044 = (CoefficientMerge.scale (150016 : Int) atom0104Coded) := by decide +kernel
theorem block001_data_flat044_original : block001_data_flat044 = (CoefficientMerge.scale (150016 : Int) atom0104Coded) := by
  rw [block001_data_flat044_step]
def block001_data_flat045 : CoefficientMerge.Poly := [(nat_lit 214, Int.ofNat (nat_lit 127200)), (nat_lit 215, Int.ofNat (nat_lit 150016))]
theorem block001_data_flat045_step : block001_data_flat045 = (CoefficientMerge.fastMerge block001_data_flat043 block001_data_flat044) := by decide +kernel
theorem block001_data_flat045_original : block001_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (127200 : Int) atom0103Coded) (CoefficientMerge.scale (150016 : Int) atom0104Coded)) := by
  rw [block001_data_flat045_step, block001_data_flat043_original, block001_data_flat044_original]
def block001_data_flat046 : CoefficientMerge.Poly := [(nat_lit 213, Int.ofNat (nat_lit 121728)), (nat_lit 214, Int.ofNat (nat_lit 127200)), (nat_lit 215, Int.ofNat (nat_lit 150016))]
theorem block001_data_flat046_step : block001_data_flat046 = (CoefficientMerge.fastMerge block001_data_flat042 block001_data_flat045) := by decide +kernel
theorem block001_data_flat046_original : block001_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (121728 : Int) atom0102Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (127200 : Int) atom0103Coded) (CoefficientMerge.scale (150016 : Int) atom0104Coded))) := by
  rw [block001_data_flat046_step, block001_data_flat042_original, block001_data_flat045_original]
def block001_data_flat047 : CoefficientMerge.Poly := [(nat_lit 211, Int.ofNat (nat_lit 83712)), (nat_lit 212, Int.ofNat (nat_lit 104320)), (nat_lit 213, Int.ofNat (nat_lit 121728)), (nat_lit 214, Int.ofNat (nat_lit 127200)), (nat_lit 215, Int.ofNat (nat_lit 150016))]
theorem block001_data_flat047_step : block001_data_flat047 = (CoefficientMerge.fastMerge block001_data_flat041 block001_data_flat046) := by decide +kernel
theorem block001_data_flat047_original : block001_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (83712 : Int) atom0100Coded) (CoefficientMerge.scale (104320 : Int) atom0101Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121728 : Int) atom0102Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (127200 : Int) atom0103Coded) (CoefficientMerge.scale (150016 : Int) atom0104Coded)))) := by
  rw [block001_data_flat047_step, block001_data_flat041_original, block001_data_flat046_original]
def block001_data_flat048 : CoefficientMerge.Poly := [(nat_lit 222, Int.ofNat (nat_lit 95616))]
theorem block001_data_flat048_step : block001_data_flat048 = (CoefficientMerge.scale (95616 : Int) atom0105Coded) := by decide +kernel
theorem block001_data_flat048_original : block001_data_flat048 = (CoefficientMerge.scale (95616 : Int) atom0105Coded) := by
  rw [block001_data_flat048_step]
def block001_data_flat049 : CoefficientMerge.Poly := [(nat_lit 223, Int.ofNat (nat_lit 147584))]
theorem block001_data_flat049_step : block001_data_flat049 = (CoefficientMerge.scale (147584 : Int) atom0106Coded) := by decide +kernel
theorem block001_data_flat049_original : block001_data_flat049 = (CoefficientMerge.scale (147584 : Int) atom0106Coded) := by
  rw [block001_data_flat049_step]
def block001_data_flat050 : CoefficientMerge.Poly := [(nat_lit 222, Int.ofNat (nat_lit 95616)), (nat_lit 223, Int.ofNat (nat_lit 147584))]
theorem block001_data_flat050_step : block001_data_flat050 = (CoefficientMerge.fastMerge block001_data_flat048 block001_data_flat049) := by decide +kernel
theorem block001_data_flat050_original : block001_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (95616 : Int) atom0105Coded) (CoefficientMerge.scale (147584 : Int) atom0106Coded)) := by
  rw [block001_data_flat050_step, block001_data_flat048_original, block001_data_flat049_original]
def block001_data_flat051 : CoefficientMerge.Poly := [(nat_lit 224, Int.ofNat (nat_lit 195072))]
theorem block001_data_flat051_step : block001_data_flat051 = (CoefficientMerge.scale (195072 : Int) atom0107Coded) := by decide +kernel
theorem block001_data_flat051_original : block001_data_flat051 = (CoefficientMerge.scale (195072 : Int) atom0107Coded) := by
  rw [block001_data_flat051_step]
def block001_data_flat052 : CoefficientMerge.Poly := [(nat_lit 225, Int.ofNat (nat_lit 218112))]
theorem block001_data_flat052_step : block001_data_flat052 = (CoefficientMerge.scale (218112 : Int) atom0108Coded) := by decide +kernel
theorem block001_data_flat052_original : block001_data_flat052 = (CoefficientMerge.scale (218112 : Int) atom0108Coded) := by
  rw [block001_data_flat052_step]
def block001_data_flat053 : CoefficientMerge.Poly := [(nat_lit 226, Int.ofNat (nat_lit 134656))]
theorem block001_data_flat053_step : block001_data_flat053 = (CoefficientMerge.scale (134656 : Int) atom0109Coded) := by decide +kernel
theorem block001_data_flat053_original : block001_data_flat053 = (CoefficientMerge.scale (134656 : Int) atom0109Coded) := by
  rw [block001_data_flat053_step]
def block001_data_flat054 : CoefficientMerge.Poly := [(nat_lit 225, Int.ofNat (nat_lit 218112)), (nat_lit 226, Int.ofNat (nat_lit 134656))]
theorem block001_data_flat054_step : block001_data_flat054 = (CoefficientMerge.fastMerge block001_data_flat052 block001_data_flat053) := by decide +kernel
theorem block001_data_flat054_original : block001_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (218112 : Int) atom0108Coded) (CoefficientMerge.scale (134656 : Int) atom0109Coded)) := by
  rw [block001_data_flat054_step, block001_data_flat052_original, block001_data_flat053_original]
def block001_data_flat055 : CoefficientMerge.Poly := [(nat_lit 224, Int.ofNat (nat_lit 195072)), (nat_lit 225, Int.ofNat (nat_lit 218112)), (nat_lit 226, Int.ofNat (nat_lit 134656))]
theorem block001_data_flat055_step : block001_data_flat055 = (CoefficientMerge.fastMerge block001_data_flat051 block001_data_flat054) := by decide +kernel
theorem block001_data_flat055_original : block001_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (195072 : Int) atom0107Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (218112 : Int) atom0108Coded) (CoefficientMerge.scale (134656 : Int) atom0109Coded))) := by
  rw [block001_data_flat055_step, block001_data_flat051_original, block001_data_flat054_original]
def block001_data_flat056 : CoefficientMerge.Poly := [(nat_lit 222, Int.ofNat (nat_lit 95616)), (nat_lit 223, Int.ofNat (nat_lit 147584)), (nat_lit 224, Int.ofNat (nat_lit 195072)), (nat_lit 225, Int.ofNat (nat_lit 218112)), (nat_lit 226, Int.ofNat (nat_lit 134656))]
theorem block001_data_flat056_step : block001_data_flat056 = (CoefficientMerge.fastMerge block001_data_flat050 block001_data_flat055) := by decide +kernel
theorem block001_data_flat056_original : block001_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (95616 : Int) atom0105Coded) (CoefficientMerge.scale (147584 : Int) atom0106Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195072 : Int) atom0107Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (218112 : Int) atom0108Coded) (CoefficientMerge.scale (134656 : Int) atom0109Coded)))) := by
  rw [block001_data_flat056_step, block001_data_flat050_original, block001_data_flat055_original]
def block001_data_flat057 : CoefficientMerge.Poly := [(nat_lit 211, Int.ofNat (nat_lit 83712)), (nat_lit 212, Int.ofNat (nat_lit 104320)), (nat_lit 213, Int.ofNat (nat_lit 121728)), (nat_lit 214, Int.ofNat (nat_lit 127200)), (nat_lit 215, Int.ofNat (nat_lit 150016)), (nat_lit 222, Int.ofNat (nat_lit 95616)), (nat_lit 223, Int.ofNat (nat_lit 147584)), (nat_lit 224, Int.ofNat (nat_lit 195072)), (nat_lit 225, Int.ofNat (nat_lit 218112)), (nat_lit 226, Int.ofNat (nat_lit 134656))]
theorem block001_data_flat057_step : block001_data_flat057 = (CoefficientMerge.fastMerge block001_data_flat047 block001_data_flat056) := by decide +kernel
theorem block001_data_flat057_original : block001_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (83712 : Int) atom0100Coded) (CoefficientMerge.scale (104320 : Int) atom0101Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121728 : Int) atom0102Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (127200 : Int) atom0103Coded) (CoefficientMerge.scale (150016 : Int) atom0104Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (95616 : Int) atom0105Coded) (CoefficientMerge.scale (147584 : Int) atom0106Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195072 : Int) atom0107Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (218112 : Int) atom0108Coded) (CoefficientMerge.scale (134656 : Int) atom0109Coded))))) := by
  rw [block001_data_flat057_step, block001_data_flat047_original, block001_data_flat056_original]
def block001_data_flat058 : CoefficientMerge.Poly := [(nat_lit 227, Int.ofNat (nat_lit 168824))]
theorem block001_data_flat058_step : block001_data_flat058 = (CoefficientMerge.scale (168824 : Int) atom0110Coded) := by decide +kernel
theorem block001_data_flat058_original : block001_data_flat058 = (CoefficientMerge.scale (168824 : Int) atom0110Coded) := by
  rw [block001_data_flat058_step]
def block001_data_flat059 : CoefficientMerge.Poly := [(nat_lit 235, Int.ofNat (nat_lit 60736))]
theorem block001_data_flat059_step : block001_data_flat059 = (CoefficientMerge.scale (60736 : Int) atom0111Coded) := by decide +kernel
theorem block001_data_flat059_original : block001_data_flat059 = (CoefficientMerge.scale (60736 : Int) atom0111Coded) := by
  rw [block001_data_flat059_step]
def block001_data_flat060 : CoefficientMerge.Poly := [(nat_lit 227, Int.ofNat (nat_lit 168824)), (nat_lit 235, Int.ofNat (nat_lit 60736))]
theorem block001_data_flat060_step : block001_data_flat060 = (CoefficientMerge.fastMerge block001_data_flat058 block001_data_flat059) := by decide +kernel
theorem block001_data_flat060_original : block001_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (168824 : Int) atom0110Coded) (CoefficientMerge.scale (60736 : Int) atom0111Coded)) := by
  rw [block001_data_flat060_step, block001_data_flat058_original, block001_data_flat059_original]
def block001_data_flat061 : CoefficientMerge.Poly := [(nat_lit 236, Int.ofNat (nat_lit 140864))]
theorem block001_data_flat061_step : block001_data_flat061 = (CoefficientMerge.scale (140864 : Int) atom0112Coded) := by decide +kernel
theorem block001_data_flat061_original : block001_data_flat061 = (CoefficientMerge.scale (140864 : Int) atom0112Coded) := by
  rw [block001_data_flat061_step]
def block001_data_flat062 : CoefficientMerge.Poly := [(nat_lit 237, Int.ofNat (nat_lit 191712))]
theorem block001_data_flat062_step : block001_data_flat062 = (CoefficientMerge.scale (191712 : Int) atom0113Coded) := by decide +kernel
theorem block001_data_flat062_original : block001_data_flat062 = (CoefficientMerge.scale (191712 : Int) atom0113Coded) := by
  rw [block001_data_flat062_step]
def block001_data_flat063 : CoefficientMerge.Poly := [(nat_lit 238, Int.ofNat (nat_lit 142048))]
theorem block001_data_flat063_step : block001_data_flat063 = (CoefficientMerge.scale (142048 : Int) atom0114Coded) := by decide +kernel
theorem block001_data_flat063_original : block001_data_flat063 = (CoefficientMerge.scale (142048 : Int) atom0114Coded) := by
  rw [block001_data_flat063_step]
def block001_data_flat064 : CoefficientMerge.Poly := [(nat_lit 237, Int.ofNat (nat_lit 191712)), (nat_lit 238, Int.ofNat (nat_lit 142048))]
theorem block001_data_flat064_step : block001_data_flat064 = (CoefficientMerge.fastMerge block001_data_flat062 block001_data_flat063) := by decide +kernel
theorem block001_data_flat064_original : block001_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (191712 : Int) atom0113Coded) (CoefficientMerge.scale (142048 : Int) atom0114Coded)) := by
  rw [block001_data_flat064_step, block001_data_flat062_original, block001_data_flat063_original]
def block001_data_flat065 : CoefficientMerge.Poly := [(nat_lit 236, Int.ofNat (nat_lit 140864)), (nat_lit 237, Int.ofNat (nat_lit 191712)), (nat_lit 238, Int.ofNat (nat_lit 142048))]
theorem block001_data_flat065_step : block001_data_flat065 = (CoefficientMerge.fastMerge block001_data_flat061 block001_data_flat064) := by decide +kernel
theorem block001_data_flat065_original : block001_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (140864 : Int) atom0112Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191712 : Int) atom0113Coded) (CoefficientMerge.scale (142048 : Int) atom0114Coded))) := by
  rw [block001_data_flat065_step, block001_data_flat061_original, block001_data_flat064_original]
def block001_data_flat066 : CoefficientMerge.Poly := [(nat_lit 227, Int.ofNat (nat_lit 168824)), (nat_lit 235, Int.ofNat (nat_lit 60736)), (nat_lit 236, Int.ofNat (nat_lit 140864)), (nat_lit 237, Int.ofNat (nat_lit 191712)), (nat_lit 238, Int.ofNat (nat_lit 142048))]
theorem block001_data_flat066_step : block001_data_flat066 = (CoefficientMerge.fastMerge block001_data_flat060 block001_data_flat065) := by decide +kernel
theorem block001_data_flat066_original : block001_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (168824 : Int) atom0110Coded) (CoefficientMerge.scale (60736 : Int) atom0111Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140864 : Int) atom0112Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191712 : Int) atom0113Coded) (CoefficientMerge.scale (142048 : Int) atom0114Coded)))) := by
  rw [block001_data_flat066_step, block001_data_flat060_original, block001_data_flat065_original]
def block001_data_flat067 : CoefficientMerge.Poly := [(nat_lit 239, Int.ofNat (nat_lit 166552))]
theorem block001_data_flat067_step : block001_data_flat067 = (CoefficientMerge.scale (166552 : Int) atom0115Coded) := by decide +kernel
theorem block001_data_flat067_original : block001_data_flat067 = (CoefficientMerge.scale (166552 : Int) atom0115Coded) := by
  rw [block001_data_flat067_step]
def block001_data_flat068 : CoefficientMerge.Poly := [(nat_lit 248, Int.ofNat (nat_lit 105216))]
theorem block001_data_flat068_step : block001_data_flat068 = (CoefficientMerge.scale (105216 : Int) atom0116Coded) := by decide +kernel
theorem block001_data_flat068_original : block001_data_flat068 = (CoefficientMerge.scale (105216 : Int) atom0116Coded) := by
  rw [block001_data_flat068_step]
def block001_data_flat069 : CoefficientMerge.Poly := [(nat_lit 239, Int.ofNat (nat_lit 166552)), (nat_lit 248, Int.ofNat (nat_lit 105216))]
theorem block001_data_flat069_step : block001_data_flat069 = (CoefficientMerge.fastMerge block001_data_flat067 block001_data_flat068) := by decide +kernel
theorem block001_data_flat069_original : block001_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (166552 : Int) atom0115Coded) (CoefficientMerge.scale (105216 : Int) atom0116Coded)) := by
  rw [block001_data_flat069_step, block001_data_flat067_original, block001_data_flat068_original]
def block001_data_flat070 : CoefficientMerge.Poly := [(nat_lit 249, Int.ofNat (nat_lit 193344))]
theorem block001_data_flat070_step : block001_data_flat070 = (CoefficientMerge.scale (193344 : Int) atom0117Coded) := by decide +kernel
theorem block001_data_flat070_original : block001_data_flat070 = (CoefficientMerge.scale (193344 : Int) atom0117Coded) := by
  rw [block001_data_flat070_step]
def block001_data_flat071 : CoefficientMerge.Poly := [(nat_lit 250, Int.ofNat (nat_lit 145792))]
theorem block001_data_flat071_step : block001_data_flat071 = (CoefficientMerge.scale (145792 : Int) atom0118Coded) := by decide +kernel
theorem block001_data_flat071_original : block001_data_flat071 = (CoefficientMerge.scale (145792 : Int) atom0118Coded) := by
  rw [block001_data_flat071_step]
def block001_data_flat072 : CoefficientMerge.Poly := [(nat_lit 251, Int.ofNat (nat_lit 177848))]
theorem block001_data_flat072_step : block001_data_flat072 = (CoefficientMerge.scale (177848 : Int) atom0119Coded) := by decide +kernel
theorem block001_data_flat072_original : block001_data_flat072 = (CoefficientMerge.scale (177848 : Int) atom0119Coded) := by
  rw [block001_data_flat072_step]
def block001_data_flat073 : CoefficientMerge.Poly := [(nat_lit 250, Int.ofNat (nat_lit 145792)), (nat_lit 251, Int.ofNat (nat_lit 177848))]
theorem block001_data_flat073_step : block001_data_flat073 = (CoefficientMerge.fastMerge block001_data_flat071 block001_data_flat072) := by decide +kernel
theorem block001_data_flat073_original : block001_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (145792 : Int) atom0118Coded) (CoefficientMerge.scale (177848 : Int) atom0119Coded)) := by
  rw [block001_data_flat073_step, block001_data_flat071_original, block001_data_flat072_original]
def block001_data_flat074 : CoefficientMerge.Poly := [(nat_lit 249, Int.ofNat (nat_lit 193344)), (nat_lit 250, Int.ofNat (nat_lit 145792)), (nat_lit 251, Int.ofNat (nat_lit 177848))]
theorem block001_data_flat074_step : block001_data_flat074 = (CoefficientMerge.fastMerge block001_data_flat070 block001_data_flat073) := by decide +kernel
theorem block001_data_flat074_original : block001_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (193344 : Int) atom0117Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145792 : Int) atom0118Coded) (CoefficientMerge.scale (177848 : Int) atom0119Coded))) := by
  rw [block001_data_flat074_step, block001_data_flat070_original, block001_data_flat073_original]
def block001_data_flat075 : CoefficientMerge.Poly := [(nat_lit 239, Int.ofNat (nat_lit 166552)), (nat_lit 248, Int.ofNat (nat_lit 105216)), (nat_lit 249, Int.ofNat (nat_lit 193344)), (nat_lit 250, Int.ofNat (nat_lit 145792)), (nat_lit 251, Int.ofNat (nat_lit 177848))]
theorem block001_data_flat075_step : block001_data_flat075 = (CoefficientMerge.fastMerge block001_data_flat069 block001_data_flat074) := by decide +kernel
theorem block001_data_flat075_original : block001_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (166552 : Int) atom0115Coded) (CoefficientMerge.scale (105216 : Int) atom0116Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193344 : Int) atom0117Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145792 : Int) atom0118Coded) (CoefficientMerge.scale (177848 : Int) atom0119Coded)))) := by
  rw [block001_data_flat075_step, block001_data_flat069_original, block001_data_flat074_original]
def block001_data_flat076 : CoefficientMerge.Poly := [(nat_lit 227, Int.ofNat (nat_lit 168824)), (nat_lit 235, Int.ofNat (nat_lit 60736)), (nat_lit 236, Int.ofNat (nat_lit 140864)), (nat_lit 237, Int.ofNat (nat_lit 191712)), (nat_lit 238, Int.ofNat (nat_lit 142048)), (nat_lit 239, Int.ofNat (nat_lit 166552)), (nat_lit 248, Int.ofNat (nat_lit 105216)), (nat_lit 249, Int.ofNat (nat_lit 193344)), (nat_lit 250, Int.ofNat (nat_lit 145792)), (nat_lit 251, Int.ofNat (nat_lit 177848))]
theorem block001_data_flat076_step : block001_data_flat076 = (CoefficientMerge.fastMerge block001_data_flat066 block001_data_flat075) := by decide +kernel
theorem block001_data_flat076_original : block001_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (168824 : Int) atom0110Coded) (CoefficientMerge.scale (60736 : Int) atom0111Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140864 : Int) atom0112Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191712 : Int) atom0113Coded) (CoefficientMerge.scale (142048 : Int) atom0114Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (166552 : Int) atom0115Coded) (CoefficientMerge.scale (105216 : Int) atom0116Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193344 : Int) atom0117Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145792 : Int) atom0118Coded) (CoefficientMerge.scale (177848 : Int) atom0119Coded))))) := by
  rw [block001_data_flat076_step, block001_data_flat066_original, block001_data_flat075_original]
def block001_data_flat077 : CoefficientMerge.Poly := [(nat_lit 211, Int.ofNat (nat_lit 83712)), (nat_lit 212, Int.ofNat (nat_lit 104320)), (nat_lit 213, Int.ofNat (nat_lit 121728)), (nat_lit 214, Int.ofNat (nat_lit 127200)), (nat_lit 215, Int.ofNat (nat_lit 150016)), (nat_lit 222, Int.ofNat (nat_lit 95616)), (nat_lit 223, Int.ofNat (nat_lit 147584)), (nat_lit 224, Int.ofNat (nat_lit 195072)), (nat_lit 225, Int.ofNat (nat_lit 218112)), (nat_lit 226, Int.ofNat (nat_lit 134656)), (nat_lit 227, Int.ofNat (nat_lit 168824)), (nat_lit 235, Int.ofNat (nat_lit 60736)), (nat_lit 236, Int.ofNat (nat_lit 140864)), (nat_lit 237, Int.ofNat (nat_lit 191712)), (nat_lit 238, Int.ofNat (nat_lit 142048)), (nat_lit 239, Int.ofNat (nat_lit 166552)), (nat_lit 248, Int.ofNat (nat_lit 105216)), (nat_lit 249, Int.ofNat (nat_lit 193344)), (nat_lit 250, Int.ofNat (nat_lit 145792)), (nat_lit 251, Int.ofNat (nat_lit 177848))]
theorem block001_data_flat077_step : block001_data_flat077 = (CoefficientMerge.fastMerge block001_data_flat057 block001_data_flat076) := by decide +kernel
theorem block001_data_flat077_original : block001_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (83712 : Int) atom0100Coded) (CoefficientMerge.scale (104320 : Int) atom0101Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121728 : Int) atom0102Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (127200 : Int) atom0103Coded) (CoefficientMerge.scale (150016 : Int) atom0104Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (95616 : Int) atom0105Coded) (CoefficientMerge.scale (147584 : Int) atom0106Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195072 : Int) atom0107Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (218112 : Int) atom0108Coded) (CoefficientMerge.scale (134656 : Int) atom0109Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (168824 : Int) atom0110Coded) (CoefficientMerge.scale (60736 : Int) atom0111Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140864 : Int) atom0112Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191712 : Int) atom0113Coded) (CoefficientMerge.scale (142048 : Int) atom0114Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (166552 : Int) atom0115Coded) (CoefficientMerge.scale (105216 : Int) atom0116Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193344 : Int) atom0117Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145792 : Int) atom0118Coded) (CoefficientMerge.scale (177848 : Int) atom0119Coded)))))) := by
  rw [block001_data_flat077_step, block001_data_flat057_original, block001_data_flat076_original]
def block001_data_flat078 : CoefficientMerge.Poly := [(nat_lit 179, Int.ofNat (nat_lit 62752)), (nat_lit 183, Int.ofNat (nat_lit 17568)), (nat_lit 184, Int.ofNat (nat_lit 24768)), (nat_lit 185, Int.ofNat (nat_lit 28928)), (nat_lit 186, Int.ofNat (nat_lit 107136)), (nat_lit 187, Int.ofNat (nat_lit 57088)), (nat_lit 188, Int.ofNat (nat_lit 76416)), (nat_lit 189, Int.ofNat (nat_lit 82560)), (nat_lit 190, Int.ofNat (nat_lit 84440)), (nat_lit 191, Int.ofNat (nat_lit 89344)), (nat_lit 196, Int.ofNat (nat_lit 21888)), (nat_lit 197, Int.ofNat (nat_lit 39008)), (nat_lit 198, Int.ofNat (nat_lit 109824)), (nat_lit 199, Int.ofNat (nat_lit 69952)), (nat_lit 200, Int.ofNat (nat_lit 90624)), (nat_lit 201, Int.ofNat (nat_lit 102528)), (nat_lit 202, Int.ofNat (nat_lit 109856)), (nat_lit 203, Int.ofNat (nat_lit 120832)), (nat_lit 209, Int.ofNat (nat_lit 33152)), (nat_lit 210, Int.ofNat (nat_lit 113536)), (nat_lit 211, Int.ofNat (nat_lit 83712)), (nat_lit 212, Int.ofNat (nat_lit 104320)), (nat_lit 213, Int.ofNat (nat_lit 121728)), (nat_lit 214, Int.ofNat (nat_lit 127200)), (nat_lit 215, Int.ofNat (nat_lit 150016)), (nat_lit 222, Int.ofNat (nat_lit 95616)), (nat_lit 223, Int.ofNat (nat_lit 147584)), (nat_lit 224, Int.ofNat (nat_lit 195072)), (nat_lit 225, Int.ofNat (nat_lit 218112)), (nat_lit 226, Int.ofNat (nat_lit 134656)), (nat_lit 227, Int.ofNat (nat_lit 168824)), (nat_lit 235, Int.ofNat (nat_lit 60736)), (nat_lit 236, Int.ofNat (nat_lit 140864)), (nat_lit 237, Int.ofNat (nat_lit 191712)), (nat_lit 238, Int.ofNat (nat_lit 142048)), (nat_lit 239, Int.ofNat (nat_lit 166552)), (nat_lit 248, Int.ofNat (nat_lit 105216)), (nat_lit 249, Int.ofNat (nat_lit 193344)), (nat_lit 250, Int.ofNat (nat_lit 145792)), (nat_lit 251, Int.ofNat (nat_lit 177848))]
theorem block001_data_flat078_step : block001_data_flat078 = (CoefficientMerge.fastMerge block001_data_flat038 block001_data_flat077) := by decide +kernel
theorem block001_data_flat078_original : block001_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62752 : Int) atom0080Coded) (CoefficientMerge.scale (17568 : Int) atom0081Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24768 : Int) atom0082Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28928 : Int) atom0083Coded) (CoefficientMerge.scale (107136 : Int) atom0084Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57088 : Int) atom0085Coded) (CoefficientMerge.scale (76416 : Int) atom0086Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82560 : Int) atom0087Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84440 : Int) atom0088Coded) (CoefficientMerge.scale (89344 : Int) atom0089Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21888 : Int) atom0090Coded) (CoefficientMerge.scale (39008 : Int) atom0091Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109824 : Int) atom0092Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69952 : Int) atom0093Coded) (CoefficientMerge.scale (90624 : Int) atom0094Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (102528 : Int) atom0095Coded) (CoefficientMerge.scale (109856 : Int) atom0096Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120832 : Int) atom0097Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33152 : Int) atom0098Coded) (CoefficientMerge.scale (113536 : Int) atom0099Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (83712 : Int) atom0100Coded) (CoefficientMerge.scale (104320 : Int) atom0101Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121728 : Int) atom0102Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (127200 : Int) atom0103Coded) (CoefficientMerge.scale (150016 : Int) atom0104Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (95616 : Int) atom0105Coded) (CoefficientMerge.scale (147584 : Int) atom0106Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195072 : Int) atom0107Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (218112 : Int) atom0108Coded) (CoefficientMerge.scale (134656 : Int) atom0109Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (168824 : Int) atom0110Coded) (CoefficientMerge.scale (60736 : Int) atom0111Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140864 : Int) atom0112Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191712 : Int) atom0113Coded) (CoefficientMerge.scale (142048 : Int) atom0114Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (166552 : Int) atom0115Coded) (CoefficientMerge.scale (105216 : Int) atom0116Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193344 : Int) atom0117Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145792 : Int) atom0118Coded) (CoefficientMerge.scale (177848 : Int) atom0119Coded))))))) := by
  rw [block001_data_flat078_step, block001_data_flat038_original, block001_data_flat077_original]
def block001_data_flat079 : CoefficientMerge.Poly := [(nat_lit 261, Int.ofNat (nat_lit 81504))]
theorem block001_data_flat079_step : block001_data_flat079 = (CoefficientMerge.scale (81504 : Int) atom0120Coded) := by decide +kernel
theorem block001_data_flat079_original : block001_data_flat079 = (CoefficientMerge.scale (81504 : Int) atom0120Coded) := by
  rw [block001_data_flat079_step]
def block001_data_flat080 : CoefficientMerge.Poly := [(nat_lit 262, Int.ofNat (nat_lit 118752))]
theorem block001_data_flat080_step : block001_data_flat080 = (CoefficientMerge.scale (118752 : Int) atom0121Coded) := by decide +kernel
theorem block001_data_flat080_original : block001_data_flat080 = (CoefficientMerge.scale (118752 : Int) atom0121Coded) := by
  rw [block001_data_flat080_step]
def block001_data_flat081 : CoefficientMerge.Poly := [(nat_lit 261, Int.ofNat (nat_lit 81504)), (nat_lit 262, Int.ofNat (nat_lit 118752))]
theorem block001_data_flat081_step : block001_data_flat081 = (CoefficientMerge.fastMerge block001_data_flat079 block001_data_flat080) := by decide +kernel
theorem block001_data_flat081_original : block001_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (81504 : Int) atom0120Coded) (CoefficientMerge.scale (118752 : Int) atom0121Coded)) := by
  rw [block001_data_flat081_step, block001_data_flat079_original, block001_data_flat080_original]
def block001_data_flat082 : CoefficientMerge.Poly := [(nat_lit 263, Int.ofNat (nat_lit 152720))]
theorem block001_data_flat082_step : block001_data_flat082 = (CoefficientMerge.scale (152720 : Int) atom0122Coded) := by decide +kernel
theorem block001_data_flat082_original : block001_data_flat082 = (CoefficientMerge.scale (152720 : Int) atom0122Coded) := by
  rw [block001_data_flat082_step]
def block001_data_flat083 : CoefficientMerge.Poly := [(nat_lit 274, Int.ofNat (nat_lit 26176))]
theorem block001_data_flat083_step : block001_data_flat083 = (CoefficientMerge.scale (26176 : Int) atom0123Coded) := by decide +kernel
theorem block001_data_flat083_original : block001_data_flat083 = (CoefficientMerge.scale (26176 : Int) atom0123Coded) := by
  rw [block001_data_flat083_step]
def block001_data_flat084 : CoefficientMerge.Poly := [(nat_lit 275, Int.ofNat (nat_lit 76064))]
theorem block001_data_flat084_step : block001_data_flat084 = (CoefficientMerge.scale (76064 : Int) atom0124Coded) := by decide +kernel
theorem block001_data_flat084_original : block001_data_flat084 = (CoefficientMerge.scale (76064 : Int) atom0124Coded) := by
  rw [block001_data_flat084_step]
def block001_data_flat085 : CoefficientMerge.Poly := [(nat_lit 274, Int.ofNat (nat_lit 26176)), (nat_lit 275, Int.ofNat (nat_lit 76064))]
theorem block001_data_flat085_step : block001_data_flat085 = (CoefficientMerge.fastMerge block001_data_flat083 block001_data_flat084) := by decide +kernel
theorem block001_data_flat085_original : block001_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26176 : Int) atom0123Coded) (CoefficientMerge.scale (76064 : Int) atom0124Coded)) := by
  rw [block001_data_flat085_step, block001_data_flat083_original, block001_data_flat084_original]
def block001_data_flat086 : CoefficientMerge.Poly := [(nat_lit 263, Int.ofNat (nat_lit 152720)), (nat_lit 274, Int.ofNat (nat_lit 26176)), (nat_lit 275, Int.ofNat (nat_lit 76064))]
theorem block001_data_flat086_step : block001_data_flat086 = (CoefficientMerge.fastMerge block001_data_flat082 block001_data_flat085) := by decide +kernel
theorem block001_data_flat086_original : block001_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (152720 : Int) atom0122Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26176 : Int) atom0123Coded) (CoefficientMerge.scale (76064 : Int) atom0124Coded))) := by
  rw [block001_data_flat086_step, block001_data_flat082_original, block001_data_flat085_original]
def block001_data_flat087 : CoefficientMerge.Poly := [(nat_lit 261, Int.ofNat (nat_lit 81504)), (nat_lit 262, Int.ofNat (nat_lit 118752)), (nat_lit 263, Int.ofNat (nat_lit 152720)), (nat_lit 274, Int.ofNat (nat_lit 26176)), (nat_lit 275, Int.ofNat (nat_lit 76064))]
theorem block001_data_flat087_step : block001_data_flat087 = (CoefficientMerge.fastMerge block001_data_flat081 block001_data_flat086) := by decide +kernel
theorem block001_data_flat087_original : block001_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81504 : Int) atom0120Coded) (CoefficientMerge.scale (118752 : Int) atom0121Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152720 : Int) atom0122Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26176 : Int) atom0123Coded) (CoefficientMerge.scale (76064 : Int) atom0124Coded)))) := by
  rw [block001_data_flat087_step, block001_data_flat081_original, block001_data_flat086_original]
def block001_data_flat088 : CoefficientMerge.Poly := [(nat_lit 287, Int.ofNat (nat_lit 34272))]
theorem block001_data_flat088_step : block001_data_flat088 = (CoefficientMerge.scale (34272 : Int) atom0125Coded) := by decide +kernel
theorem block001_data_flat088_original : block001_data_flat088 = (CoefficientMerge.scale (34272 : Int) atom0125Coded) := by
  rw [block001_data_flat088_step]
def block001_data_flat089 : CoefficientMerge.Poly := [(nat_lit 314, Int.ofNat (nat_lit 8640))]
theorem block001_data_flat089_step : block001_data_flat089 = (CoefficientMerge.scale (8640 : Int) atom0126Coded) := by decide +kernel
theorem block001_data_flat089_original : block001_data_flat089 = (CoefficientMerge.scale (8640 : Int) atom0126Coded) := by
  rw [block001_data_flat089_step]
def block001_data_flat090 : CoefficientMerge.Poly := [(nat_lit 287, Int.ofNat (nat_lit 34272)), (nat_lit 314, Int.ofNat (nat_lit 8640))]
theorem block001_data_flat090_step : block001_data_flat090 = (CoefficientMerge.fastMerge block001_data_flat088 block001_data_flat089) := by decide +kernel
theorem block001_data_flat090_original : block001_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (34272 : Int) atom0125Coded) (CoefficientMerge.scale (8640 : Int) atom0126Coded)) := by
  rw [block001_data_flat090_step, block001_data_flat088_original, block001_data_flat089_original]
def block001_data_flat091 : CoefficientMerge.Poly := [(nat_lit 315, Int.ofNat (nat_lit 24768))]
theorem block001_data_flat091_step : block001_data_flat091 = (CoefficientMerge.scale (24768 : Int) atom0127Coded) := by decide +kernel
theorem block001_data_flat091_original : block001_data_flat091 = (CoefficientMerge.scale (24768 : Int) atom0127Coded) := by
  rw [block001_data_flat091_step]
def block001_data_flat092 : CoefficientMerge.Poly := [(nat_lit 316, Int.ofNat (nat_lit 23616))]
theorem block001_data_flat092_step : block001_data_flat092 = (CoefficientMerge.scale (23616 : Int) atom0128Coded) := by decide +kernel
theorem block001_data_flat092_original : block001_data_flat092 = (CoefficientMerge.scale (23616 : Int) atom0128Coded) := by
  rw [block001_data_flat092_step]
def block001_data_flat093 : CoefficientMerge.Poly := [(nat_lit 317, Int.ofNat (nat_lit 22464))]
theorem block001_data_flat093_step : block001_data_flat093 = (CoefficientMerge.scale (22464 : Int) atom0129Coded) := by decide +kernel
theorem block001_data_flat093_original : block001_data_flat093 = (CoefficientMerge.scale (22464 : Int) atom0129Coded) := by
  rw [block001_data_flat093_step]
def block001_data_flat094 : CoefficientMerge.Poly := [(nat_lit 316, Int.ofNat (nat_lit 23616)), (nat_lit 317, Int.ofNat (nat_lit 22464))]
theorem block001_data_flat094_step : block001_data_flat094 = (CoefficientMerge.fastMerge block001_data_flat092 block001_data_flat093) := by decide +kernel
theorem block001_data_flat094_original : block001_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23616 : Int) atom0128Coded) (CoefficientMerge.scale (22464 : Int) atom0129Coded)) := by
  rw [block001_data_flat094_step, block001_data_flat092_original, block001_data_flat093_original]
def block001_data_flat095 : CoefficientMerge.Poly := [(nat_lit 315, Int.ofNat (nat_lit 24768)), (nat_lit 316, Int.ofNat (nat_lit 23616)), (nat_lit 317, Int.ofNat (nat_lit 22464))]
theorem block001_data_flat095_step : block001_data_flat095 = (CoefficientMerge.fastMerge block001_data_flat091 block001_data_flat094) := by decide +kernel
theorem block001_data_flat095_original : block001_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24768 : Int) atom0127Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23616 : Int) atom0128Coded) (CoefficientMerge.scale (22464 : Int) atom0129Coded))) := by
  rw [block001_data_flat095_step, block001_data_flat091_original, block001_data_flat094_original]
def block001_data_flat096 : CoefficientMerge.Poly := [(nat_lit 287, Int.ofNat (nat_lit 34272)), (nat_lit 314, Int.ofNat (nat_lit 8640)), (nat_lit 315, Int.ofNat (nat_lit 24768)), (nat_lit 316, Int.ofNat (nat_lit 23616)), (nat_lit 317, Int.ofNat (nat_lit 22464))]
theorem block001_data_flat096_step : block001_data_flat096 = (CoefficientMerge.fastMerge block001_data_flat090 block001_data_flat095) := by decide +kernel
theorem block001_data_flat096_original : block001_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34272 : Int) atom0125Coded) (CoefficientMerge.scale (8640 : Int) atom0126Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24768 : Int) atom0127Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23616 : Int) atom0128Coded) (CoefficientMerge.scale (22464 : Int) atom0129Coded)))) := by
  rw [block001_data_flat096_step, block001_data_flat090_original, block001_data_flat095_original]
def block001_data_flat097 : CoefficientMerge.Poly := [(nat_lit 261, Int.ofNat (nat_lit 81504)), (nat_lit 262, Int.ofNat (nat_lit 118752)), (nat_lit 263, Int.ofNat (nat_lit 152720)), (nat_lit 274, Int.ofNat (nat_lit 26176)), (nat_lit 275, Int.ofNat (nat_lit 76064)), (nat_lit 287, Int.ofNat (nat_lit 34272)), (nat_lit 314, Int.ofNat (nat_lit 8640)), (nat_lit 315, Int.ofNat (nat_lit 24768)), (nat_lit 316, Int.ofNat (nat_lit 23616)), (nat_lit 317, Int.ofNat (nat_lit 22464))]
theorem block001_data_flat097_step : block001_data_flat097 = (CoefficientMerge.fastMerge block001_data_flat087 block001_data_flat096) := by decide +kernel
theorem block001_data_flat097_original : block001_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81504 : Int) atom0120Coded) (CoefficientMerge.scale (118752 : Int) atom0121Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152720 : Int) atom0122Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26176 : Int) atom0123Coded) (CoefficientMerge.scale (76064 : Int) atom0124Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34272 : Int) atom0125Coded) (CoefficientMerge.scale (8640 : Int) atom0126Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24768 : Int) atom0127Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23616 : Int) atom0128Coded) (CoefficientMerge.scale (22464 : Int) atom0129Coded))))) := by
  rw [block001_data_flat097_step, block001_data_flat087_original, block001_data_flat096_original]
def block001_data_flat098 : CoefficientMerge.Poly := [(nat_lit 318, Int.ofNat (nat_lit 59328))]
theorem block001_data_flat098_step : block001_data_flat098 = (CoefficientMerge.scale (59328 : Int) atom0130Coded) := by decide +kernel
theorem block001_data_flat098_original : block001_data_flat098 = (CoefficientMerge.scale (59328 : Int) atom0130Coded) := by
  rw [block001_data_flat098_step]
def block001_data_flat099 : CoefficientMerge.Poly := [(nat_lit 319, Int.ofNat (nat_lit 20160))]
theorem block001_data_flat099_step : block001_data_flat099 = (CoefficientMerge.scale (20160 : Int) atom0131Coded) := by decide +kernel
theorem block001_data_flat099_original : block001_data_flat099 = (CoefficientMerge.scale (20160 : Int) atom0131Coded) := by
  rw [block001_data_flat099_step]
def block001_data_flat100 : CoefficientMerge.Poly := [(nat_lit 318, Int.ofNat (nat_lit 59328)), (nat_lit 319, Int.ofNat (nat_lit 20160))]
theorem block001_data_flat100_step : block001_data_flat100 = (CoefficientMerge.fastMerge block001_data_flat098 block001_data_flat099) := by decide +kernel
theorem block001_data_flat100_original : block001_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (59328 : Int) atom0130Coded) (CoefficientMerge.scale (20160 : Int) atom0131Coded)) := by
  rw [block001_data_flat100_step, block001_data_flat098_original, block001_data_flat099_original]
def block001_data_flat101 : CoefficientMerge.Poly := [(nat_lit 320, Int.ofNat (nat_lit 30912))]
theorem block001_data_flat101_step : block001_data_flat101 = (CoefficientMerge.scale (30912 : Int) atom0132Coded) := by decide +kernel
theorem block001_data_flat101_original : block001_data_flat101 = (CoefficientMerge.scale (30912 : Int) atom0132Coded) := by
  rw [block001_data_flat101_step]
def block001_data_flat102 : CoefficientMerge.Poly := [(nat_lit 321, Int.ofNat (nat_lit 17856))]
theorem block001_data_flat102_step : block001_data_flat102 = (CoefficientMerge.scale (17856 : Int) atom0133Coded) := by decide +kernel
theorem block001_data_flat102_original : block001_data_flat102 = (CoefficientMerge.scale (17856 : Int) atom0133Coded) := by
  rw [block001_data_flat102_step]
def block001_data_flat103 : CoefficientMerge.Poly := [(nat_lit 323, Int.ofNat (nat_lit 22080))]
theorem block001_data_flat103_step : block001_data_flat103 = (CoefficientMerge.scale (22080 : Int) atom0134Coded) := by decide +kernel
theorem block001_data_flat103_original : block001_data_flat103 = (CoefficientMerge.scale (22080 : Int) atom0134Coded) := by
  rw [block001_data_flat103_step]
def block001_data_flat104 : CoefficientMerge.Poly := [(nat_lit 321, Int.ofNat (nat_lit 17856)), (nat_lit 323, Int.ofNat (nat_lit 22080))]
theorem block001_data_flat104_step : block001_data_flat104 = (CoefficientMerge.fastMerge block001_data_flat102 block001_data_flat103) := by decide +kernel
theorem block001_data_flat104_original : block001_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17856 : Int) atom0133Coded) (CoefficientMerge.scale (22080 : Int) atom0134Coded)) := by
  rw [block001_data_flat104_step, block001_data_flat102_original, block001_data_flat103_original]
def block001_data_flat105 : CoefficientMerge.Poly := [(nat_lit 320, Int.ofNat (nat_lit 30912)), (nat_lit 321, Int.ofNat (nat_lit 17856)), (nat_lit 323, Int.ofNat (nat_lit 22080))]
theorem block001_data_flat105_step : block001_data_flat105 = (CoefficientMerge.fastMerge block001_data_flat101 block001_data_flat104) := by decide +kernel
theorem block001_data_flat105_original : block001_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30912 : Int) atom0132Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17856 : Int) atom0133Coded) (CoefficientMerge.scale (22080 : Int) atom0134Coded))) := by
  rw [block001_data_flat105_step, block001_data_flat101_original, block001_data_flat104_original]
def block001_data_flat106 : CoefficientMerge.Poly := [(nat_lit 318, Int.ofNat (nat_lit 59328)), (nat_lit 319, Int.ofNat (nat_lit 20160)), (nat_lit 320, Int.ofNat (nat_lit 30912)), (nat_lit 321, Int.ofNat (nat_lit 17856)), (nat_lit 323, Int.ofNat (nat_lit 22080))]
theorem block001_data_flat106_step : block001_data_flat106 = (CoefficientMerge.fastMerge block001_data_flat100 block001_data_flat105) := by decide +kernel
theorem block001_data_flat106_original : block001_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (59328 : Int) atom0130Coded) (CoefficientMerge.scale (20160 : Int) atom0131Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30912 : Int) atom0132Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17856 : Int) atom0133Coded) (CoefficientMerge.scale (22080 : Int) atom0134Coded)))) := by
  rw [block001_data_flat106_step, block001_data_flat100_original, block001_data_flat105_original]
def block001_data_flat107 : CoefficientMerge.Poly := [(nat_lit 327, Int.ofNat (nat_lit 24960))]
theorem block001_data_flat107_step : block001_data_flat107 = (CoefficientMerge.scale (24960 : Int) atom0135Coded) := by decide +kernel
theorem block001_data_flat107_original : block001_data_flat107 = (CoefficientMerge.scale (24960 : Int) atom0135Coded) := by
  rw [block001_data_flat107_step]
def block001_data_flat108 : CoefficientMerge.Poly := [(nat_lit 328, Int.ofNat (nat_lit 38208))]
theorem block001_data_flat108_step : block001_data_flat108 = (CoefficientMerge.scale (38208 : Int) atom0136Coded) := by decide +kernel
theorem block001_data_flat108_original : block001_data_flat108 = (CoefficientMerge.scale (38208 : Int) atom0136Coded) := by
  rw [block001_data_flat108_step]
def block001_data_flat109 : CoefficientMerge.Poly := [(nat_lit 327, Int.ofNat (nat_lit 24960)), (nat_lit 328, Int.ofNat (nat_lit 38208))]
theorem block001_data_flat109_step : block001_data_flat109 = (CoefficientMerge.fastMerge block001_data_flat107 block001_data_flat108) := by decide +kernel
theorem block001_data_flat109_original : block001_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960 : Int) atom0135Coded) (CoefficientMerge.scale (38208 : Int) atom0136Coded)) := by
  rw [block001_data_flat109_step, block001_data_flat107_original, block001_data_flat108_original]
def block001_data_flat110 : CoefficientMerge.Poly := [(nat_lit 329, Int.ofNat (nat_lit 40320))]
theorem block001_data_flat110_step : block001_data_flat110 = (CoefficientMerge.scale (40320 : Int) atom0137Coded) := by decide +kernel
theorem block001_data_flat110_original : block001_data_flat110 = (CoefficientMerge.scale (40320 : Int) atom0137Coded) := by
  rw [block001_data_flat110_step]
def block001_data_flat111 : CoefficientMerge.Poly := [(nat_lit 330, Int.ofNat (nat_lit 122688))]
theorem block001_data_flat111_step : block001_data_flat111 = (CoefficientMerge.scale (122688 : Int) atom0138Coded) := by decide +kernel
theorem block001_data_flat111_original : block001_data_flat111 = (CoefficientMerge.scale (122688 : Int) atom0138Coded) := by
  rw [block001_data_flat111_step]
def block001_data_flat112 : CoefficientMerge.Poly := [(nat_lit 331, Int.ofNat (nat_lit 52992))]
theorem block001_data_flat112_step : block001_data_flat112 = (CoefficientMerge.scale (52992 : Int) atom0139Coded) := by decide +kernel
theorem block001_data_flat112_original : block001_data_flat112 = (CoefficientMerge.scale (52992 : Int) atom0139Coded) := by
  rw [block001_data_flat112_step]
def block001_data_flat113 : CoefficientMerge.Poly := [(nat_lit 330, Int.ofNat (nat_lit 122688)), (nat_lit 331, Int.ofNat (nat_lit 52992))]
theorem block001_data_flat113_step : block001_data_flat113 = (CoefficientMerge.fastMerge block001_data_flat111 block001_data_flat112) := by decide +kernel
theorem block001_data_flat113_original : block001_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (122688 : Int) atom0138Coded) (CoefficientMerge.scale (52992 : Int) atom0139Coded)) := by
  rw [block001_data_flat113_step, block001_data_flat111_original, block001_data_flat112_original]
def block001_data_flat114 : CoefficientMerge.Poly := [(nat_lit 329, Int.ofNat (nat_lit 40320)), (nat_lit 330, Int.ofNat (nat_lit 122688)), (nat_lit 331, Int.ofNat (nat_lit 52992))]
theorem block001_data_flat114_step : block001_data_flat114 = (CoefficientMerge.fastMerge block001_data_flat110 block001_data_flat113) := by decide +kernel
theorem block001_data_flat114_original : block001_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40320 : Int) atom0137Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122688 : Int) atom0138Coded) (CoefficientMerge.scale (52992 : Int) atom0139Coded))) := by
  rw [block001_data_flat114_step, block001_data_flat110_original, block001_data_flat113_original]
def block001_data_flat115 : CoefficientMerge.Poly := [(nat_lit 327, Int.ofNat (nat_lit 24960)), (nat_lit 328, Int.ofNat (nat_lit 38208)), (nat_lit 329, Int.ofNat (nat_lit 40320)), (nat_lit 330, Int.ofNat (nat_lit 122688)), (nat_lit 331, Int.ofNat (nat_lit 52992))]
theorem block001_data_flat115_step : block001_data_flat115 = (CoefficientMerge.fastMerge block001_data_flat109 block001_data_flat114) := by decide +kernel
theorem block001_data_flat115_original : block001_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960 : Int) atom0135Coded) (CoefficientMerge.scale (38208 : Int) atom0136Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40320 : Int) atom0137Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122688 : Int) atom0138Coded) (CoefficientMerge.scale (52992 : Int) atom0139Coded)))) := by
  rw [block001_data_flat115_step, block001_data_flat109_original, block001_data_flat114_original]
def block001_data_flat116 : CoefficientMerge.Poly := [(nat_lit 318, Int.ofNat (nat_lit 59328)), (nat_lit 319, Int.ofNat (nat_lit 20160)), (nat_lit 320, Int.ofNat (nat_lit 30912)), (nat_lit 321, Int.ofNat (nat_lit 17856)), (nat_lit 323, Int.ofNat (nat_lit 22080)), (nat_lit 327, Int.ofNat (nat_lit 24960)), (nat_lit 328, Int.ofNat (nat_lit 38208)), (nat_lit 329, Int.ofNat (nat_lit 40320)), (nat_lit 330, Int.ofNat (nat_lit 122688)), (nat_lit 331, Int.ofNat (nat_lit 52992))]
theorem block001_data_flat116_step : block001_data_flat116 = (CoefficientMerge.fastMerge block001_data_flat106 block001_data_flat115) := by decide +kernel
theorem block001_data_flat116_original : block001_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (59328 : Int) atom0130Coded) (CoefficientMerge.scale (20160 : Int) atom0131Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30912 : Int) atom0132Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17856 : Int) atom0133Coded) (CoefficientMerge.scale (22080 : Int) atom0134Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960 : Int) atom0135Coded) (CoefficientMerge.scale (38208 : Int) atom0136Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40320 : Int) atom0137Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122688 : Int) atom0138Coded) (CoefficientMerge.scale (52992 : Int) atom0139Coded))))) := by
  rw [block001_data_flat116_step, block001_data_flat106_original, block001_data_flat115_original]
def block001_data_flat117 : CoefficientMerge.Poly := [(nat_lit 261, Int.ofNat (nat_lit 81504)), (nat_lit 262, Int.ofNat (nat_lit 118752)), (nat_lit 263, Int.ofNat (nat_lit 152720)), (nat_lit 274, Int.ofNat (nat_lit 26176)), (nat_lit 275, Int.ofNat (nat_lit 76064)), (nat_lit 287, Int.ofNat (nat_lit 34272)), (nat_lit 314, Int.ofNat (nat_lit 8640)), (nat_lit 315, Int.ofNat (nat_lit 24768)), (nat_lit 316, Int.ofNat (nat_lit 23616)), (nat_lit 317, Int.ofNat (nat_lit 22464)), (nat_lit 318, Int.ofNat (nat_lit 59328)), (nat_lit 319, Int.ofNat (nat_lit 20160)), (nat_lit 320, Int.ofNat (nat_lit 30912)), (nat_lit 321, Int.ofNat (nat_lit 17856)), (nat_lit 323, Int.ofNat (nat_lit 22080)), (nat_lit 327, Int.ofNat (nat_lit 24960)), (nat_lit 328, Int.ofNat (nat_lit 38208)), (nat_lit 329, Int.ofNat (nat_lit 40320)), (nat_lit 330, Int.ofNat (nat_lit 122688)), (nat_lit 331, Int.ofNat (nat_lit 52992))]
theorem block001_data_flat117_step : block001_data_flat117 = (CoefficientMerge.fastMerge block001_data_flat097 block001_data_flat116) := by decide +kernel
theorem block001_data_flat117_original : block001_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81504 : Int) atom0120Coded) (CoefficientMerge.scale (118752 : Int) atom0121Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152720 : Int) atom0122Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26176 : Int) atom0123Coded) (CoefficientMerge.scale (76064 : Int) atom0124Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34272 : Int) atom0125Coded) (CoefficientMerge.scale (8640 : Int) atom0126Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24768 : Int) atom0127Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23616 : Int) atom0128Coded) (CoefficientMerge.scale (22464 : Int) atom0129Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (59328 : Int) atom0130Coded) (CoefficientMerge.scale (20160 : Int) atom0131Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30912 : Int) atom0132Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17856 : Int) atom0133Coded) (CoefficientMerge.scale (22080 : Int) atom0134Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960 : Int) atom0135Coded) (CoefficientMerge.scale (38208 : Int) atom0136Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40320 : Int) atom0137Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122688 : Int) atom0138Coded) (CoefficientMerge.scale (52992 : Int) atom0139Coded)))))) := by
  rw [block001_data_flat117_step, block001_data_flat097_original, block001_data_flat116_original]
def block001_data_flat118 : CoefficientMerge.Poly := [(nat_lit 332, Int.ofNat (nat_lit 83136))]
theorem block001_data_flat118_step : block001_data_flat118 = (CoefficientMerge.scale (83136 : Int) atom0140Coded) := by decide +kernel
theorem block001_data_flat118_original : block001_data_flat118 = (CoefficientMerge.scale (83136 : Int) atom0140Coded) := by
  rw [block001_data_flat118_step]
def block001_data_flat119 : CoefficientMerge.Poly := [(nat_lit 333, Int.ofNat (nat_lit 65664))]
theorem block001_data_flat119_step : block001_data_flat119 = (CoefficientMerge.scale (65664 : Int) atom0141Coded) := by decide +kernel
theorem block001_data_flat119_original : block001_data_flat119 = (CoefficientMerge.scale (65664 : Int) atom0141Coded) := by
  rw [block001_data_flat119_step]
def block001_data_flat120 : CoefficientMerge.Poly := [(nat_lit 332, Int.ofNat (nat_lit 83136)), (nat_lit 333, Int.ofNat (nat_lit 65664))]
theorem block001_data_flat120_step : block001_data_flat120 = (CoefficientMerge.fastMerge block001_data_flat118 block001_data_flat119) := by decide +kernel
theorem block001_data_flat120_original : block001_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (83136 : Int) atom0140Coded) (CoefficientMerge.scale (65664 : Int) atom0141Coded)) := by
  rw [block001_data_flat120_step, block001_data_flat118_original, block001_data_flat119_original]
def block001_data_flat121 : CoefficientMerge.Poly := [(nat_lit 334, Int.ofNat (nat_lit 52272))]
theorem block001_data_flat121_step : block001_data_flat121 = (CoefficientMerge.scale (52272 : Int) atom0142Coded) := by decide +kernel
theorem block001_data_flat121_original : block001_data_flat121 = (CoefficientMerge.scale (52272 : Int) atom0142Coded) := by
  rw [block001_data_flat121_step]
def block001_data_flat122 : CoefficientMerge.Poly := [(nat_lit 335, Int.ofNat (nat_lit 84864))]
theorem block001_data_flat122_step : block001_data_flat122 = (CoefficientMerge.scale (84864 : Int) atom0143Coded) := by decide +kernel
theorem block001_data_flat122_original : block001_data_flat122 = (CoefficientMerge.scale (84864 : Int) atom0143Coded) := by
  rw [block001_data_flat122_step]
def block001_data_flat123 : CoefficientMerge.Poly := [(nat_lit 340, Int.ofNat (nat_lit 30336))]
theorem block001_data_flat123_step : block001_data_flat123 = (CoefficientMerge.scale (30336 : Int) atom0144Coded) := by decide +kernel
theorem block001_data_flat123_original : block001_data_flat123 = (CoefficientMerge.scale (30336 : Int) atom0144Coded) := by
  rw [block001_data_flat123_step]
def block001_data_flat124 : CoefficientMerge.Poly := [(nat_lit 335, Int.ofNat (nat_lit 84864)), (nat_lit 340, Int.ofNat (nat_lit 30336))]
theorem block001_data_flat124_step : block001_data_flat124 = (CoefficientMerge.fastMerge block001_data_flat122 block001_data_flat123) := by decide +kernel
theorem block001_data_flat124_original : block001_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (84864 : Int) atom0143Coded) (CoefficientMerge.scale (30336 : Int) atom0144Coded)) := by
  rw [block001_data_flat124_step, block001_data_flat122_original, block001_data_flat123_original]
def block001_data_flat125 : CoefficientMerge.Poly := [(nat_lit 334, Int.ofNat (nat_lit 52272)), (nat_lit 335, Int.ofNat (nat_lit 84864)), (nat_lit 340, Int.ofNat (nat_lit 30336))]
theorem block001_data_flat125_step : block001_data_flat125 = (CoefficientMerge.fastMerge block001_data_flat121 block001_data_flat124) := by decide +kernel
theorem block001_data_flat125_original : block001_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (52272 : Int) atom0142Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84864 : Int) atom0143Coded) (CoefficientMerge.scale (30336 : Int) atom0144Coded))) := by
  rw [block001_data_flat125_step, block001_data_flat121_original, block001_data_flat124_original]
def block001_data_flat126 : CoefficientMerge.Poly := [(nat_lit 332, Int.ofNat (nat_lit 83136)), (nat_lit 333, Int.ofNat (nat_lit 65664)), (nat_lit 334, Int.ofNat (nat_lit 52272)), (nat_lit 335, Int.ofNat (nat_lit 84864)), (nat_lit 340, Int.ofNat (nat_lit 30336))]
theorem block001_data_flat126_step : block001_data_flat126 = (CoefficientMerge.fastMerge block001_data_flat120 block001_data_flat125) := by decide +kernel
theorem block001_data_flat126_original : block001_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (83136 : Int) atom0140Coded) (CoefficientMerge.scale (65664 : Int) atom0141Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52272 : Int) atom0142Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84864 : Int) atom0143Coded) (CoefficientMerge.scale (30336 : Int) atom0144Coded)))) := by
  rw [block001_data_flat126_step, block001_data_flat120_original, block001_data_flat125_original]
def block001_data_flat127 : CoefficientMerge.Poly := [(nat_lit 341, Int.ofNat (nat_lit 62016))]
theorem block001_data_flat127_step : block001_data_flat127 = (CoefficientMerge.scale (62016 : Int) atom0145Coded) := by decide +kernel
theorem block001_data_flat127_original : block001_data_flat127 = (CoefficientMerge.scale (62016 : Int) atom0145Coded) := by
  rw [block001_data_flat127_step]
def block001_data_flat128 : CoefficientMerge.Poly := [(nat_lit 342, Int.ofNat (nat_lit 126720))]
theorem block001_data_flat128_step : block001_data_flat128 = (CoefficientMerge.scale (126720 : Int) atom0146Coded) := by decide +kernel
theorem block001_data_flat128_original : block001_data_flat128 = (CoefficientMerge.scale (126720 : Int) atom0146Coded) := by
  rw [block001_data_flat128_step]
def block001_data_flat129 : CoefficientMerge.Poly := [(nat_lit 341, Int.ofNat (nat_lit 62016)), (nat_lit 342, Int.ofNat (nat_lit 126720))]
theorem block001_data_flat129_step : block001_data_flat129 = (CoefficientMerge.fastMerge block001_data_flat127 block001_data_flat128) := by decide +kernel
theorem block001_data_flat129_original : block001_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (62016 : Int) atom0145Coded) (CoefficientMerge.scale (126720 : Int) atom0146Coded)) := by
  rw [block001_data_flat129_step, block001_data_flat127_original, block001_data_flat128_original]
def block001_data_flat130 : CoefficientMerge.Poly := [(nat_lit 343, Int.ofNat (nat_lit 74496))]
theorem block001_data_flat130_step : block001_data_flat130 = (CoefficientMerge.scale (74496 : Int) atom0147Coded) := by decide +kernel
theorem block001_data_flat130_original : block001_data_flat130 = (CoefficientMerge.scale (74496 : Int) atom0147Coded) := by
  rw [block001_data_flat130_step]
def block001_data_flat131 : CoefficientMerge.Poly := [(nat_lit 344, Int.ofNat (nat_lit 104448))]
theorem block001_data_flat131_step : block001_data_flat131 = (CoefficientMerge.scale (104448 : Int) atom0148Coded) := by decide +kernel
theorem block001_data_flat131_original : block001_data_flat131 = (CoefficientMerge.scale (104448 : Int) atom0148Coded) := by
  rw [block001_data_flat131_step]
def block001_data_flat132 : CoefficientMerge.Poly := [(nat_lit 345, Int.ofNat (nat_lit 95616))]
theorem block001_data_flat132_step : block001_data_flat132 = (CoefficientMerge.scale (95616 : Int) atom0149Coded) := by decide +kernel
theorem block001_data_flat132_original : block001_data_flat132 = (CoefficientMerge.scale (95616 : Int) atom0149Coded) := by
  rw [block001_data_flat132_step]
def block001_data_flat133 : CoefficientMerge.Poly := [(nat_lit 344, Int.ofNat (nat_lit 104448)), (nat_lit 345, Int.ofNat (nat_lit 95616))]
theorem block001_data_flat133_step : block001_data_flat133 = (CoefficientMerge.fastMerge block001_data_flat131 block001_data_flat132) := by decide +kernel
theorem block001_data_flat133_original : block001_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (104448 : Int) atom0148Coded) (CoefficientMerge.scale (95616 : Int) atom0149Coded)) := by
  rw [block001_data_flat133_step, block001_data_flat131_original, block001_data_flat132_original]
def block001_data_flat134 : CoefficientMerge.Poly := [(nat_lit 343, Int.ofNat (nat_lit 74496)), (nat_lit 344, Int.ofNat (nat_lit 104448)), (nat_lit 345, Int.ofNat (nat_lit 95616))]
theorem block001_data_flat134_step : block001_data_flat134 = (CoefficientMerge.fastMerge block001_data_flat130 block001_data_flat133) := by decide +kernel
theorem block001_data_flat134_original : block001_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (74496 : Int) atom0147Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104448 : Int) atom0148Coded) (CoefficientMerge.scale (95616 : Int) atom0149Coded))) := by
  rw [block001_data_flat134_step, block001_data_flat130_original, block001_data_flat133_original]
def block001_data_flat135 : CoefficientMerge.Poly := [(nat_lit 341, Int.ofNat (nat_lit 62016)), (nat_lit 342, Int.ofNat (nat_lit 126720)), (nat_lit 343, Int.ofNat (nat_lit 74496)), (nat_lit 344, Int.ofNat (nat_lit 104448)), (nat_lit 345, Int.ofNat (nat_lit 95616))]
theorem block001_data_flat135_step : block001_data_flat135 = (CoefficientMerge.fastMerge block001_data_flat129 block001_data_flat134) := by decide +kernel
theorem block001_data_flat135_original : block001_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62016 : Int) atom0145Coded) (CoefficientMerge.scale (126720 : Int) atom0146Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74496 : Int) atom0147Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104448 : Int) atom0148Coded) (CoefficientMerge.scale (95616 : Int) atom0149Coded)))) := by
  rw [block001_data_flat135_step, block001_data_flat129_original, block001_data_flat134_original]
def block001_data_flat136 : CoefficientMerge.Poly := [(nat_lit 332, Int.ofNat (nat_lit 83136)), (nat_lit 333, Int.ofNat (nat_lit 65664)), (nat_lit 334, Int.ofNat (nat_lit 52272)), (nat_lit 335, Int.ofNat (nat_lit 84864)), (nat_lit 340, Int.ofNat (nat_lit 30336)), (nat_lit 341, Int.ofNat (nat_lit 62016)), (nat_lit 342, Int.ofNat (nat_lit 126720)), (nat_lit 343, Int.ofNat (nat_lit 74496)), (nat_lit 344, Int.ofNat (nat_lit 104448)), (nat_lit 345, Int.ofNat (nat_lit 95616))]
theorem block001_data_flat136_step : block001_data_flat136 = (CoefficientMerge.fastMerge block001_data_flat126 block001_data_flat135) := by decide +kernel
theorem block001_data_flat136_original : block001_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (83136 : Int) atom0140Coded) (CoefficientMerge.scale (65664 : Int) atom0141Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52272 : Int) atom0142Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84864 : Int) atom0143Coded) (CoefficientMerge.scale (30336 : Int) atom0144Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62016 : Int) atom0145Coded) (CoefficientMerge.scale (126720 : Int) atom0146Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74496 : Int) atom0147Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104448 : Int) atom0148Coded) (CoefficientMerge.scale (95616 : Int) atom0149Coded))))) := by
  rw [block001_data_flat136_step, block001_data_flat126_original, block001_data_flat135_original]
def block001_data_flat137 : CoefficientMerge.Poly := [(nat_lit 346, Int.ofNat (nat_lit 90240))]
theorem block001_data_flat137_step : block001_data_flat137 = (CoefficientMerge.scale (90240 : Int) atom0150Coded) := by decide +kernel
theorem block001_data_flat137_original : block001_data_flat137 = (CoefficientMerge.scale (90240 : Int) atom0150Coded) := by
  rw [block001_data_flat137_step]
def block001_data_flat138 : CoefficientMerge.Poly := [(nat_lit 347, Int.ofNat (nat_lit 132096))]
theorem block001_data_flat138_step : block001_data_flat138 = (CoefficientMerge.scale (132096 : Int) atom0151Coded) := by decide +kernel
theorem block001_data_flat138_original : block001_data_flat138 = (CoefficientMerge.scale (132096 : Int) atom0151Coded) := by
  rw [block001_data_flat138_step]
def block001_data_flat139 : CoefficientMerge.Poly := [(nat_lit 346, Int.ofNat (nat_lit 90240)), (nat_lit 347, Int.ofNat (nat_lit 132096))]
theorem block001_data_flat139_step : block001_data_flat139 = (CoefficientMerge.fastMerge block001_data_flat137 block001_data_flat138) := by decide +kernel
theorem block001_data_flat139_original : block001_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (90240 : Int) atom0150Coded) (CoefficientMerge.scale (132096 : Int) atom0151Coded)) := by
  rw [block001_data_flat139_step, block001_data_flat137_original, block001_data_flat138_original]
def block001_data_flat140 : CoefficientMerge.Poly := [(nat_lit 353, Int.ofNat (nat_lit 43200))]
theorem block001_data_flat140_step : block001_data_flat140 = (CoefficientMerge.scale (43200 : Int) atom0152Coded) := by decide +kernel
theorem block001_data_flat140_original : block001_data_flat140 = (CoefficientMerge.scale (43200 : Int) atom0152Coded) := by
  rw [block001_data_flat140_step]
def block001_data_flat141 : CoefficientMerge.Poly := [(nat_lit 354, Int.ofNat (nat_lit 130752))]
theorem block001_data_flat141_step : block001_data_flat141 = (CoefficientMerge.scale (130752 : Int) atom0153Coded) := by decide +kernel
theorem block001_data_flat141_original : block001_data_flat141 = (CoefficientMerge.scale (130752 : Int) atom0153Coded) := by
  rw [block001_data_flat141_step]
def block001_data_flat142 : CoefficientMerge.Poly := [(nat_lit 355, Int.ofNat (nat_lit 96768))]
theorem block001_data_flat142_step : block001_data_flat142 = (CoefficientMerge.scale (96768 : Int) atom0154Coded) := by decide +kernel
theorem block001_data_flat142_original : block001_data_flat142 = (CoefficientMerge.scale (96768 : Int) atom0154Coded) := by
  rw [block001_data_flat142_step]
def block001_data_flat143 : CoefficientMerge.Poly := [(nat_lit 354, Int.ofNat (nat_lit 130752)), (nat_lit 355, Int.ofNat (nat_lit 96768))]
theorem block001_data_flat143_step : block001_data_flat143 = (CoefficientMerge.fastMerge block001_data_flat141 block001_data_flat142) := by decide +kernel
theorem block001_data_flat143_original : block001_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (130752 : Int) atom0153Coded) (CoefficientMerge.scale (96768 : Int) atom0154Coded)) := by
  rw [block001_data_flat143_step, block001_data_flat141_original, block001_data_flat142_original]
def block001_data_flat144 : CoefficientMerge.Poly := [(nat_lit 353, Int.ofNat (nat_lit 43200)), (nat_lit 354, Int.ofNat (nat_lit 130752)), (nat_lit 355, Int.ofNat (nat_lit 96768))]
theorem block001_data_flat144_step : block001_data_flat144 = (CoefficientMerge.fastMerge block001_data_flat140 block001_data_flat143) := by decide +kernel
theorem block001_data_flat144_original : block001_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (43200 : Int) atom0152Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (130752 : Int) atom0153Coded) (CoefficientMerge.scale (96768 : Int) atom0154Coded))) := by
  rw [block001_data_flat144_step, block001_data_flat140_original, block001_data_flat143_original]
def block001_data_flat145 : CoefficientMerge.Poly := [(nat_lit 346, Int.ofNat (nat_lit 90240)), (nat_lit 347, Int.ofNat (nat_lit 132096)), (nat_lit 353, Int.ofNat (nat_lit 43200)), (nat_lit 354, Int.ofNat (nat_lit 130752)), (nat_lit 355, Int.ofNat (nat_lit 96768))]
theorem block001_data_flat145_step : block001_data_flat145 = (CoefficientMerge.fastMerge block001_data_flat139 block001_data_flat144) := by decide +kernel
theorem block001_data_flat145_original : block001_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90240 : Int) atom0150Coded) (CoefficientMerge.scale (132096 : Int) atom0151Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43200 : Int) atom0152Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (130752 : Int) atom0153Coded) (CoefficientMerge.scale (96768 : Int) atom0154Coded)))) := by
  rw [block001_data_flat145_step, block001_data_flat139_original, block001_data_flat144_original]
def block001_data_flat146 : CoefficientMerge.Poly := [(nat_lit 356, Int.ofNat (nat_lit 125760))]
theorem block001_data_flat146_step : block001_data_flat146 = (CoefficientMerge.scale (125760 : Int) atom0155Coded) := by decide +kernel
theorem block001_data_flat146_original : block001_data_flat146 = (CoefficientMerge.scale (125760 : Int) atom0155Coded) := by
  rw [block001_data_flat146_step]
def block001_data_flat147 : CoefficientMerge.Poly := [(nat_lit 357, Int.ofNat (nat_lit 125568))]
theorem block001_data_flat147_step : block001_data_flat147 = (CoefficientMerge.scale (125568 : Int) atom0156Coded) := by decide +kernel
theorem block001_data_flat147_original : block001_data_flat147 = (CoefficientMerge.scale (125568 : Int) atom0156Coded) := by
  rw [block001_data_flat147_step]
def block001_data_flat148 : CoefficientMerge.Poly := [(nat_lit 356, Int.ofNat (nat_lit 125760)), (nat_lit 357, Int.ofNat (nat_lit 125568))]
theorem block001_data_flat148_step : block001_data_flat148 = (CoefficientMerge.fastMerge block001_data_flat146 block001_data_flat147) := by decide +kernel
theorem block001_data_flat148_original : block001_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (125760 : Int) atom0155Coded) (CoefficientMerge.scale (125568 : Int) atom0156Coded)) := by
  rw [block001_data_flat148_step, block001_data_flat146_original, block001_data_flat147_original]
def block001_data_flat149 : CoefficientMerge.Poly := [(nat_lit 358, Int.ofNat (nat_lit 114624))]
theorem block001_data_flat149_step : block001_data_flat149 = (CoefficientMerge.scale (114624 : Int) atom0157Coded) := by decide +kernel
theorem block001_data_flat149_original : block001_data_flat149 = (CoefficientMerge.scale (114624 : Int) atom0157Coded) := by
  rw [block001_data_flat149_step]
def block001_data_flat150 : CoefficientMerge.Poly := [(nat_lit 359, Int.ofNat (nat_lit 179328))]
theorem block001_data_flat150_step : block001_data_flat150 = (CoefficientMerge.scale (179328 : Int) atom0158Coded) := by decide +kernel
theorem block001_data_flat150_original : block001_data_flat150 = (CoefficientMerge.scale (179328 : Int) atom0158Coded) := by
  rw [block001_data_flat150_step]
def block001_data_flat151 : CoefficientMerge.Poly := [(nat_lit 366, Int.ofNat (nat_lit 105408))]
theorem block001_data_flat151_step : block001_data_flat151 = (CoefficientMerge.scale (105408 : Int) atom0159Coded) := by decide +kernel
theorem block001_data_flat151_original : block001_data_flat151 = (CoefficientMerge.scale (105408 : Int) atom0159Coded) := by
  rw [block001_data_flat151_step]
def block001_data_flat152 : CoefficientMerge.Poly := [(nat_lit 359, Int.ofNat (nat_lit 179328)), (nat_lit 366, Int.ofNat (nat_lit 105408))]
theorem block001_data_flat152_step : block001_data_flat152 = (CoefficientMerge.fastMerge block001_data_flat150 block001_data_flat151) := by decide +kernel
theorem block001_data_flat152_original : block001_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (179328 : Int) atom0158Coded) (CoefficientMerge.scale (105408 : Int) atom0159Coded)) := by
  rw [block001_data_flat152_step, block001_data_flat150_original, block001_data_flat151_original]
def block001_data_flat153 : CoefficientMerge.Poly := [(nat_lit 358, Int.ofNat (nat_lit 114624)), (nat_lit 359, Int.ofNat (nat_lit 179328)), (nat_lit 366, Int.ofNat (nat_lit 105408))]
theorem block001_data_flat153_step : block001_data_flat153 = (CoefficientMerge.fastMerge block001_data_flat149 block001_data_flat152) := by decide +kernel
theorem block001_data_flat153_original : block001_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (114624 : Int) atom0157Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179328 : Int) atom0158Coded) (CoefficientMerge.scale (105408 : Int) atom0159Coded))) := by
  rw [block001_data_flat153_step, block001_data_flat149_original, block001_data_flat152_original]
def block001_data_flat154 : CoefficientMerge.Poly := [(nat_lit 356, Int.ofNat (nat_lit 125760)), (nat_lit 357, Int.ofNat (nat_lit 125568)), (nat_lit 358, Int.ofNat (nat_lit 114624)), (nat_lit 359, Int.ofNat (nat_lit 179328)), (nat_lit 366, Int.ofNat (nat_lit 105408))]
theorem block001_data_flat154_step : block001_data_flat154 = (CoefficientMerge.fastMerge block001_data_flat148 block001_data_flat153) := by decide +kernel
theorem block001_data_flat154_original : block001_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (125760 : Int) atom0155Coded) (CoefficientMerge.scale (125568 : Int) atom0156Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114624 : Int) atom0157Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179328 : Int) atom0158Coded) (CoefficientMerge.scale (105408 : Int) atom0159Coded)))) := by
  rw [block001_data_flat154_step, block001_data_flat148_original, block001_data_flat153_original]
def block001_data_flat155 : CoefficientMerge.Poly := [(nat_lit 346, Int.ofNat (nat_lit 90240)), (nat_lit 347, Int.ofNat (nat_lit 132096)), (nat_lit 353, Int.ofNat (nat_lit 43200)), (nat_lit 354, Int.ofNat (nat_lit 130752)), (nat_lit 355, Int.ofNat (nat_lit 96768)), (nat_lit 356, Int.ofNat (nat_lit 125760)), (nat_lit 357, Int.ofNat (nat_lit 125568)), (nat_lit 358, Int.ofNat (nat_lit 114624)), (nat_lit 359, Int.ofNat (nat_lit 179328)), (nat_lit 366, Int.ofNat (nat_lit 105408))]
theorem block001_data_flat155_step : block001_data_flat155 = (CoefficientMerge.fastMerge block001_data_flat145 block001_data_flat154) := by decide +kernel
theorem block001_data_flat155_original : block001_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90240 : Int) atom0150Coded) (CoefficientMerge.scale (132096 : Int) atom0151Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43200 : Int) atom0152Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (130752 : Int) atom0153Coded) (CoefficientMerge.scale (96768 : Int) atom0154Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (125760 : Int) atom0155Coded) (CoefficientMerge.scale (125568 : Int) atom0156Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114624 : Int) atom0157Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179328 : Int) atom0158Coded) (CoefficientMerge.scale (105408 : Int) atom0159Coded))))) := by
  rw [block001_data_flat155_step, block001_data_flat145_original, block001_data_flat154_original]
def block001_data_flat156 : CoefficientMerge.Poly := [(nat_lit 332, Int.ofNat (nat_lit 83136)), (nat_lit 333, Int.ofNat (nat_lit 65664)), (nat_lit 334, Int.ofNat (nat_lit 52272)), (nat_lit 335, Int.ofNat (nat_lit 84864)), (nat_lit 340, Int.ofNat (nat_lit 30336)), (nat_lit 341, Int.ofNat (nat_lit 62016)), (nat_lit 342, Int.ofNat (nat_lit 126720)), (nat_lit 343, Int.ofNat (nat_lit 74496)), (nat_lit 344, Int.ofNat (nat_lit 104448)), (nat_lit 345, Int.ofNat (nat_lit 95616)), (nat_lit 346, Int.ofNat (nat_lit 90240)), (nat_lit 347, Int.ofNat (nat_lit 132096)), (nat_lit 353, Int.ofNat (nat_lit 43200)), (nat_lit 354, Int.ofNat (nat_lit 130752)), (nat_lit 355, Int.ofNat (nat_lit 96768)), (nat_lit 356, Int.ofNat (nat_lit 125760)), (nat_lit 357, Int.ofNat (nat_lit 125568)), (nat_lit 358, Int.ofNat (nat_lit 114624)), (nat_lit 359, Int.ofNat (nat_lit 179328)), (nat_lit 366, Int.ofNat (nat_lit 105408))]
theorem block001_data_flat156_step : block001_data_flat156 = (CoefficientMerge.fastMerge block001_data_flat136 block001_data_flat155) := by decide +kernel
theorem block001_data_flat156_original : block001_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (83136 : Int) atom0140Coded) (CoefficientMerge.scale (65664 : Int) atom0141Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52272 : Int) atom0142Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84864 : Int) atom0143Coded) (CoefficientMerge.scale (30336 : Int) atom0144Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62016 : Int) atom0145Coded) (CoefficientMerge.scale (126720 : Int) atom0146Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74496 : Int) atom0147Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104448 : Int) atom0148Coded) (CoefficientMerge.scale (95616 : Int) atom0149Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90240 : Int) atom0150Coded) (CoefficientMerge.scale (132096 : Int) atom0151Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43200 : Int) atom0152Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (130752 : Int) atom0153Coded) (CoefficientMerge.scale (96768 : Int) atom0154Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (125760 : Int) atom0155Coded) (CoefficientMerge.scale (125568 : Int) atom0156Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114624 : Int) atom0157Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179328 : Int) atom0158Coded) (CoefficientMerge.scale (105408 : Int) atom0159Coded)))))) := by
  rw [block001_data_flat156_step, block001_data_flat136_original, block001_data_flat155_original]
def block001_data_flat157 : CoefficientMerge.Poly := [(nat_lit 261, Int.ofNat (nat_lit 81504)), (nat_lit 262, Int.ofNat (nat_lit 118752)), (nat_lit 263, Int.ofNat (nat_lit 152720)), (nat_lit 274, Int.ofNat (nat_lit 26176)), (nat_lit 275, Int.ofNat (nat_lit 76064)), (nat_lit 287, Int.ofNat (nat_lit 34272)), (nat_lit 314, Int.ofNat (nat_lit 8640)), (nat_lit 315, Int.ofNat (nat_lit 24768)), (nat_lit 316, Int.ofNat (nat_lit 23616)), (nat_lit 317, Int.ofNat (nat_lit 22464)), (nat_lit 318, Int.ofNat (nat_lit 59328)), (nat_lit 319, Int.ofNat (nat_lit 20160)), (nat_lit 320, Int.ofNat (nat_lit 30912)), (nat_lit 321, Int.ofNat (nat_lit 17856)), (nat_lit 323, Int.ofNat (nat_lit 22080)), (nat_lit 327, Int.ofNat (nat_lit 24960)), (nat_lit 328, Int.ofNat (nat_lit 38208)), (nat_lit 329, Int.ofNat (nat_lit 40320)), (nat_lit 330, Int.ofNat (nat_lit 122688)), (nat_lit 331, Int.ofNat (nat_lit 52992)), (nat_lit 332, Int.ofNat (nat_lit 83136)), (nat_lit 333, Int.ofNat (nat_lit 65664)), (nat_lit 334, Int.ofNat (nat_lit 52272)), (nat_lit 335, Int.ofNat (nat_lit 84864)), (nat_lit 340, Int.ofNat (nat_lit 30336)), (nat_lit 341, Int.ofNat (nat_lit 62016)), (nat_lit 342, Int.ofNat (nat_lit 126720)), (nat_lit 343, Int.ofNat (nat_lit 74496)), (nat_lit 344, Int.ofNat (nat_lit 104448)), (nat_lit 345, Int.ofNat (nat_lit 95616)), (nat_lit 346, Int.ofNat (nat_lit 90240)), (nat_lit 347, Int.ofNat (nat_lit 132096)), (nat_lit 353, Int.ofNat (nat_lit 43200)), (nat_lit 354, Int.ofNat (nat_lit 130752)), (nat_lit 355, Int.ofNat (nat_lit 96768)), (nat_lit 356, Int.ofNat (nat_lit 125760)), (nat_lit 357, Int.ofNat (nat_lit 125568)), (nat_lit 358, Int.ofNat (nat_lit 114624)), (nat_lit 359, Int.ofNat (nat_lit 179328)), (nat_lit 366, Int.ofNat (nat_lit 105408))]
theorem block001_data_flat157_step : block001_data_flat157 = (CoefficientMerge.fastMerge block001_data_flat117 block001_data_flat156) := by decide +kernel
theorem block001_data_flat157_original : block001_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81504 : Int) atom0120Coded) (CoefficientMerge.scale (118752 : Int) atom0121Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152720 : Int) atom0122Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26176 : Int) atom0123Coded) (CoefficientMerge.scale (76064 : Int) atom0124Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34272 : Int) atom0125Coded) (CoefficientMerge.scale (8640 : Int) atom0126Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24768 : Int) atom0127Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23616 : Int) atom0128Coded) (CoefficientMerge.scale (22464 : Int) atom0129Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (59328 : Int) atom0130Coded) (CoefficientMerge.scale (20160 : Int) atom0131Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30912 : Int) atom0132Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17856 : Int) atom0133Coded) (CoefficientMerge.scale (22080 : Int) atom0134Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960 : Int) atom0135Coded) (CoefficientMerge.scale (38208 : Int) atom0136Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40320 : Int) atom0137Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122688 : Int) atom0138Coded) (CoefficientMerge.scale (52992 : Int) atom0139Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (83136 : Int) atom0140Coded) (CoefficientMerge.scale (65664 : Int) atom0141Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52272 : Int) atom0142Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84864 : Int) atom0143Coded) (CoefficientMerge.scale (30336 : Int) atom0144Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62016 : Int) atom0145Coded) (CoefficientMerge.scale (126720 : Int) atom0146Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74496 : Int) atom0147Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104448 : Int) atom0148Coded) (CoefficientMerge.scale (95616 : Int) atom0149Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90240 : Int) atom0150Coded) (CoefficientMerge.scale (132096 : Int) atom0151Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43200 : Int) atom0152Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (130752 : Int) atom0153Coded) (CoefficientMerge.scale (96768 : Int) atom0154Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (125760 : Int) atom0155Coded) (CoefficientMerge.scale (125568 : Int) atom0156Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114624 : Int) atom0157Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179328 : Int) atom0158Coded) (CoefficientMerge.scale (105408 : Int) atom0159Coded))))))) := by
  rw [block001_data_flat157_step, block001_data_flat117_original, block001_data_flat156_original]
def block001_data_flat158 : CoefficientMerge.Poly := [(nat_lit 179, Int.ofNat (nat_lit 62752)), (nat_lit 183, Int.ofNat (nat_lit 17568)), (nat_lit 184, Int.ofNat (nat_lit 24768)), (nat_lit 185, Int.ofNat (nat_lit 28928)), (nat_lit 186, Int.ofNat (nat_lit 107136)), (nat_lit 187, Int.ofNat (nat_lit 57088)), (nat_lit 188, Int.ofNat (nat_lit 76416)), (nat_lit 189, Int.ofNat (nat_lit 82560)), (nat_lit 190, Int.ofNat (nat_lit 84440)), (nat_lit 191, Int.ofNat (nat_lit 89344)), (nat_lit 196, Int.ofNat (nat_lit 21888)), (nat_lit 197, Int.ofNat (nat_lit 39008)), (nat_lit 198, Int.ofNat (nat_lit 109824)), (nat_lit 199, Int.ofNat (nat_lit 69952)), (nat_lit 200, Int.ofNat (nat_lit 90624)), (nat_lit 201, Int.ofNat (nat_lit 102528)), (nat_lit 202, Int.ofNat (nat_lit 109856)), (nat_lit 203, Int.ofNat (nat_lit 120832)), (nat_lit 209, Int.ofNat (nat_lit 33152)), (nat_lit 210, Int.ofNat (nat_lit 113536)), (nat_lit 211, Int.ofNat (nat_lit 83712)), (nat_lit 212, Int.ofNat (nat_lit 104320)), (nat_lit 213, Int.ofNat (nat_lit 121728)), (nat_lit 214, Int.ofNat (nat_lit 127200)), (nat_lit 215, Int.ofNat (nat_lit 150016)), (nat_lit 222, Int.ofNat (nat_lit 95616)), (nat_lit 223, Int.ofNat (nat_lit 147584)), (nat_lit 224, Int.ofNat (nat_lit 195072)), (nat_lit 225, Int.ofNat (nat_lit 218112)), (nat_lit 226, Int.ofNat (nat_lit 134656)), (nat_lit 227, Int.ofNat (nat_lit 168824)), (nat_lit 235, Int.ofNat (nat_lit 60736)), (nat_lit 236, Int.ofNat (nat_lit 140864)), (nat_lit 237, Int.ofNat (nat_lit 191712)), (nat_lit 238, Int.ofNat (nat_lit 142048)), (nat_lit 239, Int.ofNat (nat_lit 166552)), (nat_lit 248, Int.ofNat (nat_lit 105216)), (nat_lit 249, Int.ofNat (nat_lit 193344)), (nat_lit 250, Int.ofNat (nat_lit 145792)), (nat_lit 251, Int.ofNat (nat_lit 177848)), (nat_lit 261, Int.ofNat (nat_lit 81504)), (nat_lit 262, Int.ofNat (nat_lit 118752)), (nat_lit 263, Int.ofNat (nat_lit 152720)), (nat_lit 274, Int.ofNat (nat_lit 26176)), (nat_lit 275, Int.ofNat (nat_lit 76064)), (nat_lit 287, Int.ofNat (nat_lit 34272)), (nat_lit 314, Int.ofNat (nat_lit 8640)), (nat_lit 315, Int.ofNat (nat_lit 24768)), (nat_lit 316, Int.ofNat (nat_lit 23616)), (nat_lit 317, Int.ofNat (nat_lit 22464)), (nat_lit 318, Int.ofNat (nat_lit 59328)), (nat_lit 319, Int.ofNat (nat_lit 20160)), (nat_lit 320, Int.ofNat (nat_lit 30912)), (nat_lit 321, Int.ofNat (nat_lit 17856)), (nat_lit 323, Int.ofNat (nat_lit 22080)), (nat_lit 327, Int.ofNat (nat_lit 24960)), (nat_lit 328, Int.ofNat (nat_lit 38208)), (nat_lit 329, Int.ofNat (nat_lit 40320)), (nat_lit 330, Int.ofNat (nat_lit 122688)), (nat_lit 331, Int.ofNat (nat_lit 52992)), (nat_lit 332, Int.ofNat (nat_lit 83136)), (nat_lit 333, Int.ofNat (nat_lit 65664)), (nat_lit 334, Int.ofNat (nat_lit 52272)), (nat_lit 335, Int.ofNat (nat_lit 84864)), (nat_lit 340, Int.ofNat (nat_lit 30336)), (nat_lit 341, Int.ofNat (nat_lit 62016)), (nat_lit 342, Int.ofNat (nat_lit 126720)), (nat_lit 343, Int.ofNat (nat_lit 74496)), (nat_lit 344, Int.ofNat (nat_lit 104448)), (nat_lit 345, Int.ofNat (nat_lit 95616)), (nat_lit 346, Int.ofNat (nat_lit 90240)), (nat_lit 347, Int.ofNat (nat_lit 132096)), (nat_lit 353, Int.ofNat (nat_lit 43200)), (nat_lit 354, Int.ofNat (nat_lit 130752)), (nat_lit 355, Int.ofNat (nat_lit 96768)), (nat_lit 356, Int.ofNat (nat_lit 125760)), (nat_lit 357, Int.ofNat (nat_lit 125568)), (nat_lit 358, Int.ofNat (nat_lit 114624)), (nat_lit 359, Int.ofNat (nat_lit 179328)), (nat_lit 366, Int.ofNat (nat_lit 105408))]
theorem block001_data_flat158_step : block001_data_flat158 = (CoefficientMerge.fastMerge block001_data_flat078 block001_data_flat157) := by decide +kernel
theorem block001_data_flat158_original : block001_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62752 : Int) atom0080Coded) (CoefficientMerge.scale (17568 : Int) atom0081Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24768 : Int) atom0082Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28928 : Int) atom0083Coded) (CoefficientMerge.scale (107136 : Int) atom0084Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57088 : Int) atom0085Coded) (CoefficientMerge.scale (76416 : Int) atom0086Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82560 : Int) atom0087Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84440 : Int) atom0088Coded) (CoefficientMerge.scale (89344 : Int) atom0089Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21888 : Int) atom0090Coded) (CoefficientMerge.scale (39008 : Int) atom0091Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109824 : Int) atom0092Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69952 : Int) atom0093Coded) (CoefficientMerge.scale (90624 : Int) atom0094Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (102528 : Int) atom0095Coded) (CoefficientMerge.scale (109856 : Int) atom0096Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120832 : Int) atom0097Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33152 : Int) atom0098Coded) (CoefficientMerge.scale (113536 : Int) atom0099Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (83712 : Int) atom0100Coded) (CoefficientMerge.scale (104320 : Int) atom0101Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121728 : Int) atom0102Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (127200 : Int) atom0103Coded) (CoefficientMerge.scale (150016 : Int) atom0104Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (95616 : Int) atom0105Coded) (CoefficientMerge.scale (147584 : Int) atom0106Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195072 : Int) atom0107Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (218112 : Int) atom0108Coded) (CoefficientMerge.scale (134656 : Int) atom0109Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (168824 : Int) atom0110Coded) (CoefficientMerge.scale (60736 : Int) atom0111Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140864 : Int) atom0112Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191712 : Int) atom0113Coded) (CoefficientMerge.scale (142048 : Int) atom0114Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (166552 : Int) atom0115Coded) (CoefficientMerge.scale (105216 : Int) atom0116Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193344 : Int) atom0117Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145792 : Int) atom0118Coded) (CoefficientMerge.scale (177848 : Int) atom0119Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81504 : Int) atom0120Coded) (CoefficientMerge.scale (118752 : Int) atom0121Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152720 : Int) atom0122Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26176 : Int) atom0123Coded) (CoefficientMerge.scale (76064 : Int) atom0124Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34272 : Int) atom0125Coded) (CoefficientMerge.scale (8640 : Int) atom0126Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24768 : Int) atom0127Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23616 : Int) atom0128Coded) (CoefficientMerge.scale (22464 : Int) atom0129Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (59328 : Int) atom0130Coded) (CoefficientMerge.scale (20160 : Int) atom0131Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30912 : Int) atom0132Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17856 : Int) atom0133Coded) (CoefficientMerge.scale (22080 : Int) atom0134Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960 : Int) atom0135Coded) (CoefficientMerge.scale (38208 : Int) atom0136Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40320 : Int) atom0137Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122688 : Int) atom0138Coded) (CoefficientMerge.scale (52992 : Int) atom0139Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (83136 : Int) atom0140Coded) (CoefficientMerge.scale (65664 : Int) atom0141Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52272 : Int) atom0142Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84864 : Int) atom0143Coded) (CoefficientMerge.scale (30336 : Int) atom0144Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62016 : Int) atom0145Coded) (CoefficientMerge.scale (126720 : Int) atom0146Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74496 : Int) atom0147Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104448 : Int) atom0148Coded) (CoefficientMerge.scale (95616 : Int) atom0149Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90240 : Int) atom0150Coded) (CoefficientMerge.scale (132096 : Int) atom0151Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43200 : Int) atom0152Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (130752 : Int) atom0153Coded) (CoefficientMerge.scale (96768 : Int) atom0154Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (125760 : Int) atom0155Coded) (CoefficientMerge.scale (125568 : Int) atom0156Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114624 : Int) atom0157Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179328 : Int) atom0158Coded) (CoefficientMerge.scale (105408 : Int) atom0159Coded)))))))) := by
  rw [block001_data_flat158_step, block001_data_flat078_original, block001_data_flat157_original]
def block001_data_flat159 : CoefficientMerge.Poly := [(nat_lit 179, Int.ofNat (nat_lit 62752)), (nat_lit 183, Int.ofNat (nat_lit 17568)), (nat_lit 184, Int.ofNat (nat_lit 24768)), (nat_lit 185, Int.ofNat (nat_lit 28928)), (nat_lit 186, Int.ofNat (nat_lit 107136)), (nat_lit 187, Int.ofNat (nat_lit 57088)), (nat_lit 188, Int.ofNat (nat_lit 76416)), (nat_lit 189, Int.ofNat (nat_lit 82560)), (nat_lit 190, Int.ofNat (nat_lit 84440)), (nat_lit 191, Int.ofNat (nat_lit 89344)), (nat_lit 196, Int.ofNat (nat_lit 21888)), (nat_lit 197, Int.ofNat (nat_lit 39008)), (nat_lit 198, Int.ofNat (nat_lit 109824)), (nat_lit 199, Int.ofNat (nat_lit 69952)), (nat_lit 200, Int.ofNat (nat_lit 90624)), (nat_lit 201, Int.ofNat (nat_lit 102528)), (nat_lit 202, Int.ofNat (nat_lit 109856)), (nat_lit 203, Int.ofNat (nat_lit 120832)), (nat_lit 209, Int.ofNat (nat_lit 33152)), (nat_lit 210, Int.ofNat (nat_lit 113536)), (nat_lit 211, Int.ofNat (nat_lit 83712)), (nat_lit 212, Int.ofNat (nat_lit 104320)), (nat_lit 213, Int.ofNat (nat_lit 121728)), (nat_lit 214, Int.ofNat (nat_lit 127200)), (nat_lit 215, Int.ofNat (nat_lit 150016)), (nat_lit 222, Int.ofNat (nat_lit 95616)), (nat_lit 223, Int.ofNat (nat_lit 147584)), (nat_lit 224, Int.ofNat (nat_lit 195072)), (nat_lit 225, Int.ofNat (nat_lit 218112)), (nat_lit 226, Int.ofNat (nat_lit 134656)), (nat_lit 227, Int.ofNat (nat_lit 168824)), (nat_lit 235, Int.ofNat (nat_lit 60736)), (nat_lit 236, Int.ofNat (nat_lit 140864)), (nat_lit 237, Int.ofNat (nat_lit 191712)), (nat_lit 238, Int.ofNat (nat_lit 142048)), (nat_lit 239, Int.ofNat (nat_lit 166552)), (nat_lit 248, Int.ofNat (nat_lit 105216)), (nat_lit 249, Int.ofNat (nat_lit 193344)), (nat_lit 250, Int.ofNat (nat_lit 145792)), (nat_lit 251, Int.ofNat (nat_lit 177848)), (nat_lit 261, Int.ofNat (nat_lit 81504)), (nat_lit 262, Int.ofNat (nat_lit 118752)), (nat_lit 263, Int.ofNat (nat_lit 152720)), (nat_lit 274, Int.ofNat (nat_lit 26176)), (nat_lit 275, Int.ofNat (nat_lit 76064)), (nat_lit 287, Int.ofNat (nat_lit 34272)), (nat_lit 314, Int.ofNat (nat_lit 8640)), (nat_lit 315, Int.ofNat (nat_lit 24768)), (nat_lit 316, Int.ofNat (nat_lit 23616)), (nat_lit 317, Int.ofNat (nat_lit 22464)), (nat_lit 318, Int.ofNat (nat_lit 59328)), (nat_lit 319, Int.ofNat (nat_lit 20160)), (nat_lit 320, Int.ofNat (nat_lit 30912)), (nat_lit 321, Int.ofNat (nat_lit 17856)), (nat_lit 323, Int.ofNat (nat_lit 22080)), (nat_lit 327, Int.ofNat (nat_lit 24960)), (nat_lit 328, Int.ofNat (nat_lit 38208)), (nat_lit 329, Int.ofNat (nat_lit 40320)), (nat_lit 330, Int.ofNat (nat_lit 122688)), (nat_lit 331, Int.ofNat (nat_lit 52992)), (nat_lit 332, Int.ofNat (nat_lit 83136)), (nat_lit 333, Int.ofNat (nat_lit 65664)), (nat_lit 334, Int.ofNat (nat_lit 52272)), (nat_lit 335, Int.ofNat (nat_lit 84864)), (nat_lit 340, Int.ofNat (nat_lit 30336)), (nat_lit 341, Int.ofNat (nat_lit 62016)), (nat_lit 342, Int.ofNat (nat_lit 126720)), (nat_lit 343, Int.ofNat (nat_lit 74496)), (nat_lit 344, Int.ofNat (nat_lit 104448)), (nat_lit 345, Int.ofNat (nat_lit 95616)), (nat_lit 346, Int.ofNat (nat_lit 90240)), (nat_lit 347, Int.ofNat (nat_lit 132096)), (nat_lit 353, Int.ofNat (nat_lit 43200)), (nat_lit 354, Int.ofNat (nat_lit 130752)), (nat_lit 355, Int.ofNat (nat_lit 96768)), (nat_lit 356, Int.ofNat (nat_lit 125760)), (nat_lit 357, Int.ofNat (nat_lit 125568)), (nat_lit 358, Int.ofNat (nat_lit 114624)), (nat_lit 359, Int.ofNat (nat_lit 179328)), (nat_lit 366, Int.ofNat (nat_lit 105408))]
theorem block001_data_flat159_step : block001_data_flat159 = (CoefficientMerge.trim block001_data_flat158) := by decide +kernel
theorem block001_data_flat159_original : block001_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62752 : Int) atom0080Coded) (CoefficientMerge.scale (17568 : Int) atom0081Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24768 : Int) atom0082Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28928 : Int) atom0083Coded) (CoefficientMerge.scale (107136 : Int) atom0084Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57088 : Int) atom0085Coded) (CoefficientMerge.scale (76416 : Int) atom0086Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82560 : Int) atom0087Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84440 : Int) atom0088Coded) (CoefficientMerge.scale (89344 : Int) atom0089Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21888 : Int) atom0090Coded) (CoefficientMerge.scale (39008 : Int) atom0091Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109824 : Int) atom0092Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69952 : Int) atom0093Coded) (CoefficientMerge.scale (90624 : Int) atom0094Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (102528 : Int) atom0095Coded) (CoefficientMerge.scale (109856 : Int) atom0096Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120832 : Int) atom0097Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33152 : Int) atom0098Coded) (CoefficientMerge.scale (113536 : Int) atom0099Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (83712 : Int) atom0100Coded) (CoefficientMerge.scale (104320 : Int) atom0101Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121728 : Int) atom0102Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (127200 : Int) atom0103Coded) (CoefficientMerge.scale (150016 : Int) atom0104Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (95616 : Int) atom0105Coded) (CoefficientMerge.scale (147584 : Int) atom0106Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195072 : Int) atom0107Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (218112 : Int) atom0108Coded) (CoefficientMerge.scale (134656 : Int) atom0109Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (168824 : Int) atom0110Coded) (CoefficientMerge.scale (60736 : Int) atom0111Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140864 : Int) atom0112Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191712 : Int) atom0113Coded) (CoefficientMerge.scale (142048 : Int) atom0114Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (166552 : Int) atom0115Coded) (CoefficientMerge.scale (105216 : Int) atom0116Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193344 : Int) atom0117Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145792 : Int) atom0118Coded) (CoefficientMerge.scale (177848 : Int) atom0119Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81504 : Int) atom0120Coded) (CoefficientMerge.scale (118752 : Int) atom0121Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152720 : Int) atom0122Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26176 : Int) atom0123Coded) (CoefficientMerge.scale (76064 : Int) atom0124Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34272 : Int) atom0125Coded) (CoefficientMerge.scale (8640 : Int) atom0126Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24768 : Int) atom0127Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23616 : Int) atom0128Coded) (CoefficientMerge.scale (22464 : Int) atom0129Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (59328 : Int) atom0130Coded) (CoefficientMerge.scale (20160 : Int) atom0131Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30912 : Int) atom0132Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17856 : Int) atom0133Coded) (CoefficientMerge.scale (22080 : Int) atom0134Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960 : Int) atom0135Coded) (CoefficientMerge.scale (38208 : Int) atom0136Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40320 : Int) atom0137Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122688 : Int) atom0138Coded) (CoefficientMerge.scale (52992 : Int) atom0139Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (83136 : Int) atom0140Coded) (CoefficientMerge.scale (65664 : Int) atom0141Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52272 : Int) atom0142Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84864 : Int) atom0143Coded) (CoefficientMerge.scale (30336 : Int) atom0144Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62016 : Int) atom0145Coded) (CoefficientMerge.scale (126720 : Int) atom0146Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74496 : Int) atom0147Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104448 : Int) atom0148Coded) (CoefficientMerge.scale (95616 : Int) atom0149Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90240 : Int) atom0150Coded) (CoefficientMerge.scale (132096 : Int) atom0151Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43200 : Int) atom0152Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (130752 : Int) atom0153Coded) (CoefficientMerge.scale (96768 : Int) atom0154Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (125760 : Int) atom0155Coded) (CoefficientMerge.scale (125568 : Int) atom0156Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114624 : Int) atom0157Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179328 : Int) atom0158Coded) (CoefficientMerge.scale (105408 : Int) atom0159Coded))))))))) := by
  rw [block001_data_flat159_step, block001_data_flat158_original]
theorem block001_data : block001 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62752 : Int) atom0080Coded) (CoefficientMerge.scale (17568 : Int) atom0081Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24768 : Int) atom0082Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (28928 : Int) atom0083Coded) (CoefficientMerge.scale (107136 : Int) atom0084Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (57088 : Int) atom0085Coded) (CoefficientMerge.scale (76416 : Int) atom0086Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (82560 : Int) atom0087Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84440 : Int) atom0088Coded) (CoefficientMerge.scale (89344 : Int) atom0089Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (21888 : Int) atom0090Coded) (CoefficientMerge.scale (39008 : Int) atom0091Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (109824 : Int) atom0092Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (69952 : Int) atom0093Coded) (CoefficientMerge.scale (90624 : Int) atom0094Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (102528 : Int) atom0095Coded) (CoefficientMerge.scale (109856 : Int) atom0096Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (120832 : Int) atom0097Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33152 : Int) atom0098Coded) (CoefficientMerge.scale (113536 : Int) atom0099Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (83712 : Int) atom0100Coded) (CoefficientMerge.scale (104320 : Int) atom0101Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (121728 : Int) atom0102Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (127200 : Int) atom0103Coded) (CoefficientMerge.scale (150016 : Int) atom0104Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (95616 : Int) atom0105Coded) (CoefficientMerge.scale (147584 : Int) atom0106Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (195072 : Int) atom0107Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (218112 : Int) atom0108Coded) (CoefficientMerge.scale (134656 : Int) atom0109Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (168824 : Int) atom0110Coded) (CoefficientMerge.scale (60736 : Int) atom0111Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (140864 : Int) atom0112Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191712 : Int) atom0113Coded) (CoefficientMerge.scale (142048 : Int) atom0114Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (166552 : Int) atom0115Coded) (CoefficientMerge.scale (105216 : Int) atom0116Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (193344 : Int) atom0117Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (145792 : Int) atom0118Coded) (CoefficientMerge.scale (177848 : Int) atom0119Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (81504 : Int) atom0120Coded) (CoefficientMerge.scale (118752 : Int) atom0121Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (152720 : Int) atom0122Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26176 : Int) atom0123Coded) (CoefficientMerge.scale (76064 : Int) atom0124Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (34272 : Int) atom0125Coded) (CoefficientMerge.scale (8640 : Int) atom0126Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (24768 : Int) atom0127Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23616 : Int) atom0128Coded) (CoefficientMerge.scale (22464 : Int) atom0129Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (59328 : Int) atom0130Coded) (CoefficientMerge.scale (20160 : Int) atom0131Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30912 : Int) atom0132Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17856 : Int) atom0133Coded) (CoefficientMerge.scale (22080 : Int) atom0134Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24960 : Int) atom0135Coded) (CoefficientMerge.scale (38208 : Int) atom0136Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40320 : Int) atom0137Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (122688 : Int) atom0138Coded) (CoefficientMerge.scale (52992 : Int) atom0139Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (83136 : Int) atom0140Coded) (CoefficientMerge.scale (65664 : Int) atom0141Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52272 : Int) atom0142Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (84864 : Int) atom0143Coded) (CoefficientMerge.scale (30336 : Int) atom0144Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (62016 : Int) atom0145Coded) (CoefficientMerge.scale (126720 : Int) atom0146Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (74496 : Int) atom0147Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (104448 : Int) atom0148Coded) (CoefficientMerge.scale (95616 : Int) atom0149Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (90240 : Int) atom0150Coded) (CoefficientMerge.scale (132096 : Int) atom0151Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (43200 : Int) atom0152Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (130752 : Int) atom0153Coded) (CoefficientMerge.scale (96768 : Int) atom0154Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (125760 : Int) atom0155Coded) (CoefficientMerge.scale (125568 : Int) atom0156Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (114624 : Int) atom0157Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (179328 : Int) atom0158Coded) (CoefficientMerge.scale (105408 : Int) atom0159Coded)))))))) := by
  have h : block001 = block001_data_flat159 := by decide +kernel
  exact h.trans block001_data_flat159_original
theorem block001_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 12) block001 := by
  rw [block001_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0080Coded_nonneg g hg hA hB) (atom0081Coded_nonneg g hg hA hB)) (add_nonneg (atom0082Coded_nonneg g hg hA hB) (add_nonneg (atom0083Coded_nonneg g hg hA hB) (atom0084Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0085Coded_nonneg g hg hA hB) (atom0086Coded_nonneg g hg hA hB)) (add_nonneg (atom0087Coded_nonneg g hg hA hB) (add_nonneg (atom0088Coded_nonneg g hg hA hB) (atom0089Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0090Coded_nonneg g hg hA hB) (atom0091Coded_nonneg g hg hA hB)) (add_nonneg (atom0092Coded_nonneg g hg hA hB) (add_nonneg (atom0093Coded_nonneg g hg hA hB) (atom0094Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0095Coded_nonneg g hg hA hB) (atom0096Coded_nonneg g hg hA hB)) (add_nonneg (atom0097Coded_nonneg g hg hA hB) (add_nonneg (atom0098Coded_nonneg g hg hA hB) (atom0099Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0100Coded_nonneg g hg hA hB) (atom0101Coded_nonneg g hg hA hB)) (add_nonneg (atom0102Coded_nonneg g hg hA hB) (add_nonneg (atom0103Coded_nonneg g hg hA hB) (atom0104Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0105Coded_nonneg g hg hA hB) (atom0106Coded_nonneg g hg hA hB)) (add_nonneg (atom0107Coded_nonneg g hg hA hB) (add_nonneg (atom0108Coded_nonneg g hg hA hB) (atom0109Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0110Coded_nonneg g hg hA hB) (atom0111Coded_nonneg g hg hA hB)) (add_nonneg (atom0112Coded_nonneg g hg hA hB) (add_nonneg (atom0113Coded_nonneg g hg hA hB) (atom0114Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0115Coded_nonneg g hg hA hB) (atom0116Coded_nonneg g hg hA hB)) (add_nonneg (atom0117Coded_nonneg g hg hA hB) (add_nonneg (atom0118Coded_nonneg g hg hA hB) (atom0119Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0120Coded_nonneg g hg hA hB) (atom0121Coded_nonneg g hg hA hB)) (add_nonneg (atom0122Coded_nonneg g hg hA hB) (add_nonneg (atom0123Coded_nonneg g hg hA hB) (atom0124Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0125Coded_nonneg g hg hA hB) (atom0126Coded_nonneg g hg hA hB)) (add_nonneg (atom0127Coded_nonneg g hg hA hB) (add_nonneg (atom0128Coded_nonneg g hg hA hB) (atom0129Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0130Coded_nonneg g hg hA hB) (atom0131Coded_nonneg g hg hA hB)) (add_nonneg (atom0132Coded_nonneg g hg hA hB) (add_nonneg (atom0133Coded_nonneg g hg hA hB) (atom0134Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0135Coded_nonneg g hg hA hB) (atom0136Coded_nonneg g hg hA hB)) (add_nonneg (atom0137Coded_nonneg g hg hA hB) (add_nonneg (atom0138Coded_nonneg g hg hA hB) (atom0139Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0140Coded_nonneg g hg hA hB) (atom0141Coded_nonneg g hg hA hB)) (add_nonneg (atom0142Coded_nonneg g hg hA hB) (add_nonneg (atom0143Coded_nonneg g hg hA hB) (atom0144Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0145Coded_nonneg g hg hA hB) (atom0146Coded_nonneg g hg hA hB)) (add_nonneg (atom0147Coded_nonneg g hg hA hB) (add_nonneg (atom0148Coded_nonneg g hg hA hB) (atom0149Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0150Coded_nonneg g hg hA hB) (atom0151Coded_nonneg g hg hA hB)) (add_nonneg (atom0152Coded_nonneg g hg hA hB) (add_nonneg (atom0153Coded_nonneg g hg hA hB) (atom0154Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0155Coded_nonneg g hg hA hB) (atom0156Coded_nonneg g hg hA hB)) (add_nonneg (atom0157Coded_nonneg g hg hA hB) (add_nonneg (atom0158Coded_nonneg g hg hA hB) (atom0159Coded_nonneg g hg hA hB))))))))

end APPT.Finite12
