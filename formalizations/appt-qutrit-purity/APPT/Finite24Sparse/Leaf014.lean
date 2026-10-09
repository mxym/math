-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom0929 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0929 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0929 = ((g 2) * (g 10) * (g 13)) := by
  norm_num [atom0929, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0929_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (403961087933568 : Int) atom0929) := by
  rw [SparsePolynomial.eval_scale, eval_atom0929]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0929Coded : CoefficientMerge.Poly := [(nat_lit 1405, Int.ofNat (nat_lit 1))]
theorem atom0929Coded_decode : atom0929 = SparsePolynomial.decodeCubic 24 atom0929Coded := by decide +kernel
theorem atom0929Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (403961087933568 : Int) atom0929Coded) := by
  have h := atom0929_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0929Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0930 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0930 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0930 = ((g 2) * (g 10) * (g 14)) := by
  norm_num [atom0930, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0930_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (381526078906368 : Int) atom0930) := by
  rw [SparsePolynomial.eval_scale, eval_atom0930]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0930Coded : CoefficientMerge.Poly := [(nat_lit 1406, Int.ofNat (nat_lit 1))]
theorem atom0930Coded_decode : atom0930 = SparsePolynomial.decodeCubic 24 atom0930Coded := by decide +kernel
theorem atom0930Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (381526078906368 : Int) atom0930Coded) := by
  have h := atom0930_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0930Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0931 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0931 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0931 = ((g 2) * (g 10) * (g 15)) := by
  norm_num [atom0931, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0931_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (373878076474368 : Int) atom0931) := by
  rw [SparsePolynomial.eval_scale, eval_atom0931]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0931Coded : CoefficientMerge.Poly := [(nat_lit 1407, Int.ofNat (nat_lit 1))]
theorem atom0931Coded_decode : atom0931 = SparsePolynomial.decodeCubic 24 atom0931Coded := by decide +kernel
theorem atom0931Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (373878076474368 : Int) atom0931Coded) := by
  have h := atom0931_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0931Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0932 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0932 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0932 = ((g 2) * (g 10) * (g 16)) := by
  norm_num [atom0932, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0932_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (354407563795968 : Int) atom0932) := by
  rw [SparsePolynomial.eval_scale, eval_atom0932]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0932Coded : CoefficientMerge.Poly := [(nat_lit 1408, Int.ofNat (nat_lit 1))]
theorem atom0932Coded_decode : atom0932 = SparsePolynomial.decodeCubic 24 atom0932Coded := by decide +kernel
theorem atom0932Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (354407563795968 : Int) atom0932Coded) := by
  have h := atom0932_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0932Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0933 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0933 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0933 = ((g 2) * (g 10) * (g 17)) := by
  norm_num [atom0933, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0933_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (344869789575168 : Int) atom0933) := by
  rw [SparsePolynomial.eval_scale, eval_atom0933]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0933Coded : CoefficientMerge.Poly := [(nat_lit 1409, Int.ofNat (nat_lit 1))]
theorem atom0933Coded_decode : atom0933 = SparsePolynomial.decodeCubic 24 atom0933Coded := by decide +kernel
theorem atom0933Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (344869789575168 : Int) atom0933Coded) := by
  have h := atom0933_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0933Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0934 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0934 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0934 = ((g 2) * (g 10) * (g 18)) := by
  norm_num [atom0934, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0934_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (379974615939072 : Int) atom0934) := by
  rw [SparsePolynomial.eval_scale, eval_atom0934]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0934Coded : CoefficientMerge.Poly := [(nat_lit 1410, Int.ofNat (nat_lit 1))]
theorem atom0934Coded_decode : atom0934 = SparsePolynomial.decodeCubic 24 atom0934Coded := by decide +kernel
theorem atom0934Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (379974615939072 : Int) atom0934Coded) := by
  have h := atom0934_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0934Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0935 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0935 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0935 = ((g 2) * (g 10) * (g 19)) := by
  norm_num [atom0935, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0935_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (329477914529280 : Int) atom0935) := by
  rw [SparsePolynomial.eval_scale, eval_atom0935]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0935Coded : CoefficientMerge.Poly := [(nat_lit 1411, Int.ofNat (nat_lit 1))]
theorem atom0935Coded_decode : atom0935 = SparsePolynomial.decodeCubic 24 atom0935Coded := by decide +kernel
theorem atom0935Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (329477914529280 : Int) atom0935Coded) := by
  have h := atom0935_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0935Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0936 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0936 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0936 = ((g 2) * (g 10) * (g 20)) := by
  norm_num [atom0936, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0936_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (419823011570688 : Int) atom0936) := by
  rw [SparsePolynomial.eval_scale, eval_atom0936]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0936Coded : CoefficientMerge.Poly := [(nat_lit 1412, Int.ofNat (nat_lit 1))]
theorem atom0936Coded_decode : atom0936 = SparsePolynomial.decodeCubic 24 atom0936Coded := by decide +kernel
theorem atom0936Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (419823011570688 : Int) atom0936Coded) := by
  have h := atom0936_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0936Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0937 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0937 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0937 = ((g 2) * (g 10) * (g 21)) := by
  norm_num [atom0937, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0937_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (399350123656704 : Int) atom0937) := by
  rw [SparsePolynomial.eval_scale, eval_atom0937]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0937Coded : CoefficientMerge.Poly := [(nat_lit 1413, Int.ofNat (nat_lit 1))]
theorem atom0937Coded_decode : atom0937 = SparsePolynomial.decodeCubic 24 atom0937Coded := by decide +kernel
theorem atom0937Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (399350123656704 : Int) atom0937Coded) := by
  have h := atom0937_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0937Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0938 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0938 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0938 = ((g 2) * (g 10) * (g 22)) := by
  norm_num [atom0938, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0938_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (445024402859520 : Int) atom0938) := by
  rw [SparsePolynomial.eval_scale, eval_atom0938]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0938Coded : CoefficientMerge.Poly := [(nat_lit 1414, Int.ofNat (nat_lit 1))]
theorem atom0938Coded_decode : atom0938 = SparsePolynomial.decodeCubic 24 atom0938Coded := by decide +kernel
theorem atom0938Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (445024402859520 : Int) atom0938Coded) := by
  have h := atom0938_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0938Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0939 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 10, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0939 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0939 = ((g 2) * (g 10) * (g 23)) := by
  norm_num [atom0939, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0939_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (523432068039936 : Int) atom0939) := by
  rw [SparsePolynomial.eval_scale, eval_atom0939]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0939Coded : CoefficientMerge.Poly := [(nat_lit 1415, Int.ofNat (nat_lit 1))]
theorem atom0939Coded_decode : atom0939 = SparsePolynomial.decodeCubic 24 atom0939Coded := by decide +kernel
theorem atom0939Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (523432068039936 : Int) atom0939Coded) := by
  have h := atom0939_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0939Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0940 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom0940 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0940 = ((g 2) * (g 11) * (g 11)) := by
  norm_num [atom0940, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0940_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (247082976765504 : Int) atom0940) := by
  rw [SparsePolynomial.eval_scale, eval_atom0940]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0940Coded : CoefficientMerge.Poly := [(nat_lit 1427, Int.ofNat (nat_lit 1))]
theorem atom0940Coded_decode : atom0940 = SparsePolynomial.decodeCubic 24 atom0940Coded := by decide +kernel
theorem atom0940Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (247082976765504 : Int) atom0940Coded) := by
  have h := atom0940_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0940Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0941 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0941 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0941 = ((g 2) * (g 11) * (g 12)) := by
  norm_num [atom0941, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0941_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (484045607060928 : Int) atom0941) := by
  rw [SparsePolynomial.eval_scale, eval_atom0941]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0941Coded : CoefficientMerge.Poly := [(nat_lit 1428, Int.ofNat (nat_lit 1))]
theorem atom0941Coded_decode : atom0941 = SparsePolynomial.decodeCubic 24 atom0941Coded := by decide +kernel
theorem atom0941Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (484045607060928 : Int) atom0941Coded) := by
  have h := atom0941_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0941Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0942 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0942 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0942 = ((g 2) * (g 11) * (g 13)) := by
  norm_num [atom0942, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0942_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (457120118911104 : Int) atom0942) := by
  rw [SparsePolynomial.eval_scale, eval_atom0942]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0942Coded : CoefficientMerge.Poly := [(nat_lit 1429, Int.ofNat (nat_lit 1))]
theorem atom0942Coded_decode : atom0942 = SparsePolynomial.decodeCubic 24 atom0942Coded := by decide +kernel
theorem atom0942Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (457120118911104 : Int) atom0942Coded) := by
  have h := atom0942_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0942Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0943 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0943 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0943 = ((g 2) * (g 11) * (g 14)) := by
  norm_num [atom0943, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0943_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (426520367944704 : Int) atom0943) := by
  rw [SparsePolynomial.eval_scale, eval_atom0943]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0943Coded : CoefficientMerge.Poly := [(nat_lit 1430, Int.ofNat (nat_lit 1))]
theorem atom0943Coded_decode : atom0943 = SparsePolynomial.decodeCubic 24 atom0943Coded := by decide +kernel
theorem atom0943Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (426520367944704 : Int) atom0943Coded) := by
  have h := atom0943_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0943Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0944 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0944 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0944 = ((g 2) * (g 11) * (g 15)) := by
  norm_num [atom0944, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0944_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (410707623573504 : Int) atom0944) := by
  rw [SparsePolynomial.eval_scale, eval_atom0944]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0944Coded : CoefficientMerge.Poly := [(nat_lit 1431, Int.ofNat (nat_lit 1))]
theorem atom0944Coded_decode : atom0944 = SparsePolynomial.decodeCubic 24 atom0944Coded := by decide +kernel
theorem atom0944Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (410707623573504 : Int) atom0944Coded) := by
  have h := atom0944_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0944Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0945 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0945 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0945 = ((g 2) * (g 11) * (g 16)) := by
  norm_num [atom0945, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0945_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (386155409531904 : Int) atom0945) := by
  rw [SparsePolynomial.eval_scale, eval_atom0945]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0945Coded : CoefficientMerge.Poly := [(nat_lit 1432, Int.ofNat (nat_lit 1))]
theorem atom0945Coded_decode : atom0945 = SparsePolynomial.decodeCubic 24 atom0945Coded := by decide +kernel
theorem atom0945Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (386155409531904 : Int) atom0945Coded) := by
  have h := atom0945_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0945Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0946 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0946 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0946 = ((g 2) * (g 11) * (g 17)) := by
  norm_num [atom0946, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0946_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (371535933947904 : Int) atom0946) := by
  rw [SparsePolynomial.eval_scale, eval_atom0946]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0946Coded : CoefficientMerge.Poly := [(nat_lit 1433, Int.ofNat (nat_lit 1))]
theorem atom0946Coded_decode : atom0946 = SparsePolynomial.decodeCubic 24 atom0946Coded := by decide +kernel
theorem atom0946Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (371535933947904 : Int) atom0946Coded) := by
  have h := atom0946_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0946Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0947 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0947 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0947 = ((g 2) * (g 11) * (g 18)) := by
  norm_num [atom0947, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0947_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (413692392979008 : Int) atom0947) := by
  rw [SparsePolynomial.eval_scale, eval_atom0947]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0947Coded : CoefficientMerge.Poly := [(nat_lit 1434, Int.ofNat (nat_lit 1))]
theorem atom0947Coded_decode : atom0947 = SparsePolynomial.decodeCubic 24 atom0947Coded := by decide +kernel
theorem atom0947Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (413692392979008 : Int) atom0947Coded) := by
  have h := atom0947_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0947Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0948 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0948 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0948 = ((g 2) * (g 11) * (g 19)) := by
  norm_num [atom0948, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0948_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (347494413911040 : Int) atom0948) := by
  rw [SparsePolynomial.eval_scale, eval_atom0948]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0948Coded : CoefficientMerge.Poly := [(nat_lit 1435, Int.ofNat (nat_lit 1))]
theorem atom0948Coded_decode : atom0948 = SparsePolynomial.decodeCubic 24 atom0948Coded := by decide +kernel
theorem atom0948Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (347494413911040 : Int) atom0948Coded) := by
  have h := atom0948_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0948Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0949 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0949 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0949 = ((g 2) * (g 11) * (g 20)) := by
  norm_num [atom0949, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0949_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (444055027065408 : Int) atom0949) := by
  rw [SparsePolynomial.eval_scale, eval_atom0949]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0949Coded : CoefficientMerge.Poly := [(nat_lit 1436, Int.ofNat (nat_lit 1))]
theorem atom0949Coded_decode : atom0949 = SparsePolynomial.decodeCubic 24 atom0949Coded := by decide +kernel
theorem atom0949Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (444055027065408 : Int) atom0949Coded) := by
  have h := atom0949_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0949Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0950 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0950 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0950 = ((g 2) * (g 11) * (g 21)) := by
  norm_num [atom0950, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0950_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (410230735782912 : Int) atom0950) := by
  rw [SparsePolynomial.eval_scale, eval_atom0950]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0950Coded : CoefficientMerge.Poly := [(nat_lit 1437, Int.ofNat (nat_lit 1))]
theorem atom0950Coded_decode : atom0950 = SparsePolynomial.decodeCubic 24 atom0950Coded := by decide +kernel
theorem atom0950Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (410230735782912 : Int) atom0950Coded) := by
  have h := atom0950_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0950Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0951 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0951 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0951 = ((g 2) * (g 11) * (g 22)) := by
  norm_num [atom0951, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0951_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (452841657269760 : Int) atom0951) := by
  rw [SparsePolynomial.eval_scale, eval_atom0951]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0951Coded : CoefficientMerge.Poly := [(nat_lit 1438, Int.ofNat (nat_lit 1))]
theorem atom0951Coded_decode : atom0951 = SparsePolynomial.decodeCubic 24 atom0951Coded := by decide +kernel
theorem atom0951Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (452841657269760 : Int) atom0951Coded) := by
  have h := atom0951_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0951Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0952 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 11, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0952 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0952 = ((g 2) * (g 11) * (g 23)) := by
  norm_num [atom0952, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0952_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (528185964734208 : Int) atom0952) := by
  rw [SparsePolynomial.eval_scale, eval_atom0952]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0952Coded : CoefficientMerge.Poly := [(nat_lit 1439, Int.ofNat (nat_lit 1))]
theorem atom0952Coded_decode : atom0952 = SparsePolynomial.decodeCubic 24 atom0952Coded := by decide +kernel
theorem atom0952Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (528185964734208 : Int) atom0952Coded) := by
  have h := atom0952_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0952Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0953 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom0953 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0953 = ((g 2) * (g 12) * (g 12)) := by
  norm_num [atom0953, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0953_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (284228831677824 : Int) atom0953) := by
  rw [SparsePolynomial.eval_scale, eval_atom0953]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0953Coded : CoefficientMerge.Poly := [(nat_lit 1452, Int.ofNat (nat_lit 1))]
theorem atom0953Coded_decode : atom0953 = SparsePolynomial.decodeCubic 24 atom0953Coded := by decide +kernel
theorem atom0953Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (284228831677824 : Int) atom0953Coded) := by
  have h := atom0953_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0953Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0954 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0954 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0954 = ((g 2) * (g 12) * (g 13)) := by
  norm_num [atom0954, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0954_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (526699029124224 : Int) atom0954) := by
  rw [SparsePolynomial.eval_scale, eval_atom0954]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0954Coded : CoefficientMerge.Poly := [(nat_lit 1453, Int.ofNat (nat_lit 1))]
theorem atom0954Coded_decode : atom0954 = SparsePolynomial.decodeCubic 24 atom0954Coded := by decide +kernel
theorem atom0954Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (526699029124224 : Int) atom0954Coded) := by
  have h := atom0954_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0954Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0955 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0955 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0955 = ((g 2) * (g 12) * (g 14)) := by
  norm_num [atom0955, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0955_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (493080024628224 : Int) atom0955) := by
  rw [SparsePolynomial.eval_scale, eval_atom0955]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0955Coded : CoefficientMerge.Poly := [(nat_lit 1454, Int.ofNat (nat_lit 1))]
theorem atom0955Coded_decode : atom0955 = SparsePolynomial.decodeCubic 24 atom0955Coded := by decide +kernel
theorem atom0955Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (493080024628224 : Int) atom0955Coded) := by
  have h := atom0955_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0955Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0956 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0956 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0956 = ((g 2) * (g 12) * (g 15)) := by
  norm_num [atom0956, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0956_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (474248026727424 : Int) atom0956) := by
  rw [SparsePolynomial.eval_scale, eval_atom0956]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0956Coded : CoefficientMerge.Poly := [(nat_lit 1455, Int.ofNat (nat_lit 1))]
theorem atom0956Coded_decode : atom0956 = SparsePolynomial.decodeCubic 24 atom0956Coded := by decide +kernel
theorem atom0956Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (474248026727424 : Int) atom0956Coded) := by
  have h := atom0956_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0956Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0957 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0957 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0957 = ((g 2) * (g 12) * (g 16)) := by
  norm_num [atom0957, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0957_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (443593518580224 : Int) atom0957) := by
  rw [SparsePolynomial.eval_scale, eval_atom0957]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0957Coded : CoefficientMerge.Poly := [(nat_lit 1456, Int.ofNat (nat_lit 1))]
theorem atom0957Coded_decode : atom0957 = SparsePolynomial.decodeCubic 24 atom0957Coded := by decide +kernel
theorem atom0957Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (443593518580224 : Int) atom0957Coded) := by
  have h := atom0957_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0957Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0958 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0958 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0958 = ((g 2) * (g 12) * (g 17)) := by
  norm_num [atom0958, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0958_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (422871748890624 : Int) atom0958) := by
  rw [SparsePolynomial.eval_scale, eval_atom0958]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0958Coded : CoefficientMerge.Poly := [(nat_lit 1457, Int.ofNat (nat_lit 1))]
theorem atom0958Coded_decode : atom0958 = SparsePolynomial.decodeCubic 24 atom0958Coded := by decide +kernel
theorem atom0958Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (422871748890624 : Int) atom0958Coded) := by
  have h := atom0958_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0958Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0959 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0959 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0959 = ((g 2) * (g 12) * (g 18)) := by
  norm_num [atom0959, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0959_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (484590100376448 : Int) atom0959) := by
  rw [SparsePolynomial.eval_scale, eval_atom0959]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0959Coded : CoefficientMerge.Poly := [(nat_lit 1458, Int.ofNat (nat_lit 1))]
theorem atom0959Coded_decode : atom0959 = SparsePolynomial.decodeCubic 24 atom0959Coded := by decide +kernel
theorem atom0959Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (484590100376448 : Int) atom0959Coded) := by
  have h := atom0959_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0959Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0960 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0960 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0960 = ((g 2) * (g 12) * (g 19)) := by
  norm_num [atom0960, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0960_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (377389276323840 : Int) atom0960) := by
  rw [SparsePolynomial.eval_scale, eval_atom0960]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0960Coded : CoefficientMerge.Poly := [(nat_lit 1459, Int.ofNat (nat_lit 1))]
theorem atom0960Coded_decode : atom0960 = SparsePolynomial.decodeCubic 24 atom0960Coded := by decide +kernel
theorem atom0960Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (377389276323840 : Int) atom0960Coded) := by
  have h := atom0960_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0960Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0961 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0961 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0961 = ((g 2) * (g 12) * (g 20)) := by
  norm_num [atom0961, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0961_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (521076290917248 : Int) atom0961) := by
  rw [SparsePolynomial.eval_scale, eval_atom0961]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0961Coded : CoefficientMerge.Poly := [(nat_lit 1460, Int.ofNat (nat_lit 1))]
theorem atom0961Coded_decode : atom0961 = SparsePolynomial.decodeCubic 24 atom0961Coded := by decide +kernel
theorem atom0961Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (521076290917248 : Int) atom0961Coded) := by
  have h := atom0961_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0961Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0962 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0962 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0962 = ((g 2) * (g 12) * (g 21)) := by
  norm_num [atom0962, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0962_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (409448281347072 : Int) atom0962) := by
  rw [SparsePolynomial.eval_scale, eval_atom0962]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0962Coded : CoefficientMerge.Poly := [(nat_lit 1461, Int.ofNat (nat_lit 1))]
theorem atom0962Coded_decode : atom0962 = SparsePolynomial.decodeCubic 24 atom0962Coded := by decide +kernel
theorem atom0962Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (409448281347072 : Int) atom0962Coded) := by
  have h := atom0962_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0962Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0963 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0963 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0963 = ((g 2) * (g 12) * (g 22)) := by
  norm_num [atom0963, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0963_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (433641756303360 : Int) atom0963) := by
  rw [SparsePolynomial.eval_scale, eval_atom0963]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0963Coded : CoefficientMerge.Poly := [(nat_lit 1462, Int.ofNat (nat_lit 1))]
theorem atom0963Coded_decode : atom0963 = SparsePolynomial.decodeCubic 24 atom0963Coded := by decide +kernel
theorem atom0963Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (433641756303360 : Int) atom0963Coded) := by
  have h := atom0963_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0963Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0964 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 12, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0964 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0964 = ((g 2) * (g 12) * (g 23)) := by
  norm_num [atom0964, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0964_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (490568617237248 : Int) atom0964) := by
  rw [SparsePolynomial.eval_scale, eval_atom0964]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0964Coded : CoefficientMerge.Poly := [(nat_lit 1463, Int.ofNat (nat_lit 1))]
theorem atom0964Coded_decode : atom0964 = SparsePolynomial.decodeCubic 24 atom0964Coded := by decide +kernel
theorem atom0964Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (490568617237248 : Int) atom0964Coded) := by
  have h := atom0964_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0964Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0965 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom0965 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0965 = ((g 2) * (g 13) * (g 13)) := by
  norm_num [atom0965, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0965_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (289736398828800 : Int) atom0965) := by
  rw [SparsePolynomial.eval_scale, eval_atom0965]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0965Coded : CoefficientMerge.Poly := [(nat_lit 1477, Int.ofNat (nat_lit 1))]
theorem atom0965Coded_decode : atom0965 = SparsePolynomial.decodeCubic 24 atom0965Coded := by decide +kernel
theorem atom0965Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (289736398828800 : Int) atom0965Coded) := by
  have h := atom0965_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0965Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0966 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0966 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0966 = ((g 2) * (g 13) * (g 14)) := by
  norm_num [atom0966, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0966_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (526404059596800 : Int) atom0966) := by
  rw [SparsePolynomial.eval_scale, eval_atom0966]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0966Coded : CoefficientMerge.Poly := [(nat_lit 1478, Int.ofNat (nat_lit 1))]
theorem atom0966Coded_decode : atom0966 = SparsePolynomial.decodeCubic 24 atom0966Coded := by decide +kernel
theorem atom0966Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (526404059596800 : Int) atom0966Coded) := by
  have h := atom0966_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0966Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0967 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0967 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0967 = ((g 2) * (g 13) * (g 15)) := by
  norm_num [atom0967, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0967_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (497366134272000 : Int) atom0967) := by
  rw [SparsePolynomial.eval_scale, eval_atom0967]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0967Coded : CoefficientMerge.Poly := [(nat_lit 1479, Int.ofNat (nat_lit 1))]
theorem atom0967Coded_decode : atom0967 = SparsePolynomial.decodeCubic 24 atom0967Coded := by decide +kernel
theorem atom0967Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (497366134272000 : Int) atom0967Coded) := by
  have h := atom0967_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0967Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0968 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0968 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0968 = ((g 2) * (g 13) * (g 16)) := by
  norm_num [atom0968, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0968_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (459588739276800 : Int) atom0968) := by
  rw [SparsePolynomial.eval_scale, eval_atom0968]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0968Coded : CoefficientMerge.Poly := [(nat_lit 1480, Int.ofNat (nat_lit 1))]
theorem atom0968Coded_decode : atom0968 = SparsePolynomial.decodeCubic 24 atom0968Coded := by decide +kernel
theorem atom0968Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (459588739276800 : Int) atom0968Coded) := by
  have h := atom0968_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0968Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0969 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0969 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0969 = ((g 2) * (g 13) * (g 17)) := by
  norm_num [atom0969, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0969_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (431744082739200 : Int) atom0969) := by
  rw [SparsePolynomial.eval_scale, eval_atom0969]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0969Coded : CoefficientMerge.Poly := [(nat_lit 1481, Int.ofNat (nat_lit 1))]
theorem atom0969Coded_decode : atom0969 = SparsePolynomial.decodeCubic 24 atom0969Coded := by decide +kernel
theorem atom0969Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (431744082739200 : Int) atom0969Coded) := by
  have h := atom0969_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0969Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0970 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0970 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0970 = ((g 2) * (g 13) * (g 18)) := by
  norm_num [atom0970, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0970_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (482321582265600 : Int) atom0970) := by
  rw [SparsePolynomial.eval_scale, eval_atom0970]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0970Coded : CoefficientMerge.Poly := [(nat_lit 1482, Int.ofNat (nat_lit 1))]
theorem atom0970Coded_decode : atom0970 = SparsePolynomial.decodeCubic 24 atom0970Coded := by decide +kernel
theorem atom0970Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (482321582265600 : Int) atom0970Coded) := by
  have h := atom0970_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0970Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0971 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0971 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0971 = ((g 2) * (g 13) * (g 19)) := by
  norm_num [atom0971, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0971_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (377204281977600 : Int) atom0971) := by
  rw [SparsePolynomial.eval_scale, eval_atom0971]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0971Coded : CoefficientMerge.Poly := [(nat_lit 1483, Int.ofNat (nat_lit 1))]
theorem atom0971Coded_decode : atom0971 = SparsePolynomial.decodeCubic 24 atom0971Coded := by decide +kernel
theorem atom0971Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (377204281977600 : Int) atom0971Coded) := by
  have h := atom0971_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0971Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0972 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0972 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0972 = ((g 2) * (g 13) * (g 20)) := by
  norm_num [atom0972, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0972_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (524931329260800 : Int) atom0972) := by
  rw [SparsePolynomial.eval_scale, eval_atom0972]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0972Coded : CoefficientMerge.Poly := [(nat_lit 1484, Int.ofNat (nat_lit 1))]
theorem atom0972Coded_decode : atom0972 = SparsePolynomial.decodeCubic 24 atom0972Coded := by decide +kernel
theorem atom0972Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (524931329260800 : Int) atom0972Coded) := by
  have h := atom0972_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0972Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0973 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0973 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0973 = ((g 2) * (g 13) * (g 21)) := by
  norm_num [atom0973, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0973_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (405394404307200 : Int) atom0973) := by
  rw [SparsePolynomial.eval_scale, eval_atom0973]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0973Coded : CoefficientMerge.Poly := [(nat_lit 1485, Int.ofNat (nat_lit 1))]
theorem atom0973Coded_decode : atom0973 = SparsePolynomial.decodeCubic 24 atom0973Coded := by decide +kernel
theorem atom0973Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (405394404307200 : Int) atom0973Coded) := by
  have h := atom0973_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0973Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0974 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0974 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0974 = ((g 2) * (g 13) * (g 22)) := by
  norm_num [atom0974, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0974_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (429382919750400 : Int) atom0974) := by
  rw [SparsePolynomial.eval_scale, eval_atom0974]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0974Coded : CoefficientMerge.Poly := [(nat_lit 1486, Int.ofNat (nat_lit 1))]
theorem atom0974Coded_decode : atom0974 = SparsePolynomial.decodeCubic 24 atom0974Coded := by decide +kernel
theorem atom0974Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (429382919750400 : Int) atom0974Coded) := by
  have h := atom0974_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0974Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0975 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 13, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0975 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0975 = ((g 2) * (g 13) * (g 23)) := by
  norm_num [atom0975, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0975_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (486104821171200 : Int) atom0975) := by
  rw [SparsePolynomial.eval_scale, eval_atom0975]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0975Coded : CoefficientMerge.Poly := [(nat_lit 1487, Int.ofNat (nat_lit 1))]
theorem atom0975Coded_decode : atom0975 = SparsePolynomial.decodeCubic 24 atom0975Coded := by decide +kernel
theorem atom0975Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (486104821171200 : Int) atom0975Coded) := by
  have h := atom0975_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0975Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0976 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom0976 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0976 = ((g 2) * (g 14) * (g 14)) := by
  norm_num [atom0976, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0976_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283933862150400 : Int) atom0976) := by
  rw [SparsePolynomial.eval_scale, eval_atom0976]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0976Coded : CoefficientMerge.Poly := [(nat_lit 1502, Int.ofNat (nat_lit 1))]
theorem atom0976Coded_decode : atom0976 = SparsePolynomial.decodeCubic 24 atom0976Coded := by decide +kernel
theorem atom0976Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (283933862150400 : Int) atom0976Coded) := by
  have h := atom0976_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0976Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0977 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0977 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0977 = ((g 2) * (g 14) * (g 15)) := by
  norm_num [atom0977, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0977_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (525551462150400 : Int) atom0977) := by
  rw [SparsePolynomial.eval_scale, eval_atom0977]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0977Coded : CoefficientMerge.Poly := [(nat_lit 1503, Int.ofNat (nat_lit 1))]
theorem atom0977Coded_decode : atom0977 = SparsePolynomial.decodeCubic 24 atom0977Coded := by decide +kernel
theorem atom0977Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (525551462150400 : Int) atom0977Coded) := by
  have h := atom0977_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0977Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0978 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0978 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0978 = ((g 2) * (g 14) * (g 16)) := by
  norm_num [atom0978, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0978_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (479630587564800 : Int) atom0978) := by
  rw [SparsePolynomial.eval_scale, eval_atom0978]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0978Coded : CoefficientMerge.Poly := [(nat_lit 1504, Int.ofNat (nat_lit 1))]
theorem atom0978Coded_decode : atom0978 = SparsePolynomial.decodeCubic 24 atom0978Coded := by decide +kernel
theorem atom0978Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (479630587564800 : Int) atom0978Coded) := by
  have h := atom0978_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0978Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0979 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0979 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0979 = ((g 2) * (g 14) * (g 17)) := by
  norm_num [atom0979, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0979_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (443642451436800 : Int) atom0979) := by
  rw [SparsePolynomial.eval_scale, eval_atom0979]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0979Coded : CoefficientMerge.Poly := [(nat_lit 1505, Int.ofNat (nat_lit 1))]
theorem atom0979Coded_decode : atom0979 = SparsePolynomial.decodeCubic 24 atom0979Coded := by decide +kernel
theorem atom0979Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (443642451436800 : Int) atom0979Coded) := by
  have h := atom0979_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0979Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0980 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0980 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0980 = ((g 2) * (g 14) * (g 18)) := by
  norm_num [atom0980, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0980_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (472704538521600 : Int) atom0980) := by
  rw [SparsePolynomial.eval_scale, eval_atom0980]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0980Coded : CoefficientMerge.Poly := [(nat_lit 1506, Int.ofNat (nat_lit 1))]
theorem atom0980Coded_decode : atom0980 = SparsePolynomial.decodeCubic 24 atom0980Coded := by decide +kernel
theorem atom0980Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (472704538521600 : Int) atom0980Coded) := by
  have h := atom0980_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0980Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0981 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0981 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0981 = ((g 2) * (g 14) * (g 19)) := by
  norm_num [atom0981, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0981_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (375370378336800 : Int) atom0981) := by
  rw [SparsePolynomial.eval_scale, eval_atom0981]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0981Coded : CoefficientMerge.Poly := [(nat_lit 1507, Int.ofNat (nat_lit 1))]
theorem atom0981Coded_decode : atom0981 = SparsePolynomial.decodeCubic 24 atom0981Coded := by decide +kernel
theorem atom0981Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (375370378336800 : Int) atom0981Coded) := by
  have h := atom0981_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0981Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0982 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0982 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0982 = ((g 2) * (g 14) * (g 20)) := by
  norm_num [atom0982, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0982_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (521437841971200 : Int) atom0982) := by
  rw [SparsePolynomial.eval_scale, eval_atom0982]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0982Coded : CoefficientMerge.Poly := [(nat_lit 1508, Int.ofNat (nat_lit 1))]
theorem atom0982Coded_decode : atom0982 = SparsePolynomial.decodeCubic 24 atom0982Coded := by decide +kernel
theorem atom0982Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (521437841971200 : Int) atom0982Coded) := by
  have h := atom0982_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0982Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0983 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0983 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0983 = ((g 2) * (g 14) * (g 21)) := by
  norm_num [atom0983, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0983_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (404962695244800 : Int) atom0983) := by
  rw [SparsePolynomial.eval_scale, eval_atom0983]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0983Coded : CoefficientMerge.Poly := [(nat_lit 1509, Int.ofNat (nat_lit 1))]
theorem atom0983Coded_decode : atom0983 = SparsePolynomial.decodeCubic 24 atom0983Coded := by decide +kernel
theorem atom0983Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (404962695244800 : Int) atom0983Coded) := by
  have h := atom0983_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0983Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0984 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0984 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0984 = ((g 2) * (g 14) * (g 22)) := by
  norm_num [atom0984, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0984_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (411634200146400 : Int) atom0984) := by
  rw [SparsePolynomial.eval_scale, eval_atom0984]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0984Coded : CoefficientMerge.Poly := [(nat_lit 1510, Int.ofNat (nat_lit 1))]
theorem atom0984Coded_decode : atom0984 = SparsePolynomial.decodeCubic 24 atom0984Coded := by decide +kernel
theorem atom0984Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (411634200146400 : Int) atom0984Coded) := by
  have h := atom0984_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0984Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0985 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 14, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0985 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0985 = ((g 2) * (g 14) * (g 23)) := by
  norm_num [atom0985, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0985_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (463618871100000 : Int) atom0985) := by
  rw [SparsePolynomial.eval_scale, eval_atom0985]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0985Coded : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 1))]
theorem atom0985Coded_decode : atom0985 = SparsePolynomial.decodeCubic 24 atom0985Coded := by decide +kernel
theorem atom0985Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (463618871100000 : Int) atom0985Coded) := by
  have h := atom0985_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0985Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0986 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom0986 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0986 = ((g 2) * (g 15) * (g 15)) := by
  norm_num [atom0986, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0986_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (291966841958400 : Int) atom0986) := by
  rw [SparsePolynomial.eval_scale, eval_atom0986]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 2) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0986Coded : CoefficientMerge.Poly := [(nat_lit 1527, Int.ofNat (nat_lit 1))]
theorem atom0986Coded_decode : atom0986 = SparsePolynomial.decodeCubic 24 atom0986Coded := by decide +kernel
theorem atom0986Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (291966841958400 : Int) atom0986Coded) := by
  have h := atom0986_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0986Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0987 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0987 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0987 = ((g 2) * (g 15) * (g 16)) := by
  norm_num [atom0987, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0987_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (515495981952000 : Int) atom0987) := by
  rw [SparsePolynomial.eval_scale, eval_atom0987]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0987Coded : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 1))]
theorem atom0987Coded_decode : atom0987 = SparsePolynomial.decodeCubic 24 atom0987Coded := by decide +kernel
theorem atom0987Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (515495981952000 : Int) atom0987Coded) := by
  have h := atom0987_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0987Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0988 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0988 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0988 = ((g 2) * (g 15) * (g 17)) := by
  norm_num [atom0988, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0988_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (470343773491200 : Int) atom0988) := by
  rw [SparsePolynomial.eval_scale, eval_atom0988]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0988Coded : CoefficientMerge.Poly := [(nat_lit 1529, Int.ofNat (nat_lit 1))]
theorem atom0988Coded_decode : atom0988 = SparsePolynomial.decodeCubic 24 atom0988Coded := by decide +kernel
theorem atom0988Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (470343773491200 : Int) atom0988Coded) := by
  have h := atom0988_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0988Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0989 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0989 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0989 = ((g 2) * (g 15) * (g 18)) := by
  norm_num [atom0989, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0989_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (492661507968000 : Int) atom0989) := by
  rw [SparsePolynomial.eval_scale, eval_atom0989]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0989Coded : CoefficientMerge.Poly := [(nat_lit 1530, Int.ofNat (nat_lit 1))]
theorem atom0989Coded_decode : atom0989 = SparsePolynomial.decodeCubic 24 atom0989Coded := by decide +kernel
theorem atom0989Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (492661507968000 : Int) atom0989Coded) := by
  have h := atom0989_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0989Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0990 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0990 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0990 = ((g 2) * (g 15) * (g 19)) := by
  norm_num [atom0990, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0990_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (379248139468800 : Int) atom0990) := by
  rw [SparsePolynomial.eval_scale, eval_atom0990]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0990Coded : CoefficientMerge.Poly := [(nat_lit 1531, Int.ofNat (nat_lit 1))]
theorem atom0990Coded_decode : atom0990 = SparsePolynomial.decodeCubic 24 atom0990Coded := by decide +kernel
theorem atom0990Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (379248139468800 : Int) atom0990Coded) := by
  have h := atom0990_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0990Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0991 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0991 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0991 = ((g 2) * (g 15) * (g 20)) := by
  norm_num [atom0991, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0991_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (547518367872000 : Int) atom0991) := by
  rw [SparsePolynomial.eval_scale, eval_atom0991]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0991Coded : CoefficientMerge.Poly := [(nat_lit 1532, Int.ofNat (nat_lit 1))]
theorem atom0991Coded_decode : atom0991 = SparsePolynomial.decodeCubic 24 atom0991Coded := by decide +kernel
theorem atom0991Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (547518367872000 : Int) atom0991Coded) := by
  have h := atom0991_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0991Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0992 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom0992 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0992 = ((g 2) * (g 15) * (g 21)) := by
  norm_num [atom0992, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0992_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (434104999372800 : Int) atom0992) := by
  rw [SparsePolynomial.eval_scale, eval_atom0992]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0992Coded : CoefficientMerge.Poly := [(nat_lit 1533, Int.ofNat (nat_lit 1))]
theorem atom0992Coded_decode : atom0992 = SparsePolynomial.decodeCubic 24 atom0992Coded := by decide +kernel
theorem atom0992Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (434104999372800 : Int) atom0992Coded) := by
  have h := atom0992_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0992Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0993 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom0993 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0993 = ((g 2) * (g 15) * (g 22)) := by
  norm_num [atom0993, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0993_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (373035023424000 : Int) atom0993) := by
  rw [SparsePolynomial.eval_scale, eval_atom0993]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0993Coded : CoefficientMerge.Poly := [(nat_lit 1534, Int.ofNat (nat_lit 1))]
theorem atom0993Coded_decode : atom0993 = SparsePolynomial.decodeCubic 24 atom0993Coded := by decide +kernel
theorem atom0993Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (373035023424000 : Int) atom0993Coded) := by
  have h := atom0993_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0993Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0994 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom0994 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0994 = ((g 2) * (g 15) * (g 23)) := by
  norm_num [atom0994, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0994_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (415072942099200 : Int) atom0994) := by
  rw [SparsePolynomial.eval_scale, eval_atom0994]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0994Coded : CoefficientMerge.Poly := [(nat_lit 1535, Int.ofNat (nat_lit 1))]
theorem atom0994Coded_decode : atom0994 = SparsePolynomial.decodeCubic 24 atom0994Coded := by decide +kernel
theorem atom0994Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (415072942099200 : Int) atom0994Coded) := by
  have h := atom0994_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0994Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0995 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom0995 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0995 = ((g 2) * (g 16) * (g 16)) := by
  norm_num [atom0995, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0995_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (276961422528000 : Int) atom0995) := by
  rw [SparsePolynomial.eval_scale, eval_atom0995]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 2) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0995Coded : CoefficientMerge.Poly := [(nat_lit 1552, Int.ofNat (nat_lit 1))]
theorem atom0995Coded_decode : atom0995 = SparsePolynomial.decodeCubic 24 atom0995Coded := by decide +kernel
theorem atom0995Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (276961422528000 : Int) atom0995Coded) := by
  have h := atom0995_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0995Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0996 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom0996 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0996 = ((g 2) * (g 16) * (g 17)) := by
  norm_num [atom0996, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0996_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (495502930944000 : Int) atom0996) := by
  rw [SparsePolynomial.eval_scale, eval_atom0996]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0996Coded : CoefficientMerge.Poly := [(nat_lit 1553, Int.ofNat (nat_lit 1))]
theorem atom0996Coded_decode : atom0996 = SparsePolynomial.decodeCubic 24 atom0996Coded := by decide +kernel
theorem atom0996Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (495502930944000 : Int) atom0996Coded) := by
  have h := atom0996_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0996Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0997 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom0997 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0997 = ((g 2) * (g 16) * (g 18)) := by
  norm_num [atom0997, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0997_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (488973456921600 : Int) atom0997) := by
  rw [SparsePolynomial.eval_scale, eval_atom0997]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0997Coded : CoefficientMerge.Poly := [(nat_lit 1554, Int.ofNat (nat_lit 1))]
theorem atom0997Coded_decode : atom0997 = SparsePolynomial.decodeCubic 24 atom0997Coded := by decide +kernel
theorem atom0997Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (488973456921600 : Int) atom0997Coded) := by
  have h := atom0997_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0997Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0998 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom0998 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0998 = ((g 2) * (g 16) * (g 19)) := by
  norm_num [atom0998, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0998_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (378621866649600 : Int) atom0998) := by
  rw [SparsePolynomial.eval_scale, eval_atom0998]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0998Coded : CoefficientMerge.Poly := [(nat_lit 1555, Int.ofNat (nat_lit 1))]
theorem atom0998Coded_decode : atom0998 = SparsePolynomial.decodeCubic 24 atom0998Coded := by decide +kernel
theorem atom0998Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (378621866649600 : Int) atom0998Coded) := by
  have h := atom0998_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0998Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom0999 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom0999 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom0999 = ((g 2) * (g 16) * (g 20)) := by
  norm_num [atom0999, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom0999_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (549953873280000 : Int) atom0999) := by
  rw [SparsePolynomial.eval_scale, eval_atom0999]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0999Coded : CoefficientMerge.Poly := [(nat_lit 1556, Int.ofNat (nat_lit 1))]
theorem atom0999Coded_decode : atom0999 = SparsePolynomial.decodeCubic 24 atom0999Coded := by decide +kernel
theorem atom0999Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (549953873280000 : Int) atom0999Coded) := by
  have h := atom0999_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom0999Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1000 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1000 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1000 = ((g 2) * (g 16) * (g 21)) := by
  norm_num [atom1000, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1000_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (439602283008000 : Int) atom1000) := by
  rw [SparsePolynomial.eval_scale, eval_atom1000]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1000Coded : CoefficientMerge.Poly := [(nat_lit 1557, Int.ofNat (nat_lit 1))]
theorem atom1000Coded_decode : atom1000 = SparsePolynomial.decodeCubic 24 atom1000Coded := by decide +kernel
theorem atom1000Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (439602283008000 : Int) atom1000Coded) := by
  have h := atom1000_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1000Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1001 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1001 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1001 = ((g 2) * (g 16) * (g 22)) := by
  norm_num [atom1001, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1001_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (323801088307200 : Int) atom1001) := by
  rw [SparsePolynomial.eval_scale, eval_atom1001]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1001Coded : CoefficientMerge.Poly := [(nat_lit 1558, Int.ofNat (nat_lit 1))]
theorem atom1001Coded_decode : atom1001 = SparsePolynomial.decodeCubic 24 atom1001Coded := by decide +kernel
theorem atom1001Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (323801088307200 : Int) atom1001Coded) := by
  have h := atom1001_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1001Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1002 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1002 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1002 = ((g 2) * (g 16) * (g 23)) := by
  norm_num [atom1002, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1002_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (445435576185600 : Int) atom1002) := by
  rw [SparsePolynomial.eval_scale, eval_atom1002]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 2) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1002Coded : CoefficientMerge.Poly := [(nat_lit 1559, Int.ofNat (nat_lit 1))]
theorem atom1002Coded_decode : atom1002 = SparsePolynomial.decodeCubic 24 atom1002Coded := by decide +kernel
theorem atom1002Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (445435576185600 : Int) atom1002Coded) := by
  have h := atom1002_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1002Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1003 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1003 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1003 = ((g 2) * (g 17) * (g 17)) := by
  norm_num [atom1003, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1003_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (267182675020800 : Int) atom1003) := by
  rw [SparsePolynomial.eval_scale, eval_atom1003]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 2) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1003Coded : CoefficientMerge.Poly := [(nat_lit 1577, Int.ofNat (nat_lit 1))]
theorem atom1003Coded_decode : atom1003 = SparsePolynomial.decodeCubic 24 atom1003Coded := by decide +kernel
theorem atom1003Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (267182675020800 : Int) atom1003Coded) := by
  have h := atom1003_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1003Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1004 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1004 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1004 = ((g 2) * (g 17) * (g 18)) := by
  norm_num [atom1004, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1004_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (505150882790400 : Int) atom1004) := by
  rw [SparsePolynomial.eval_scale, eval_atom1004]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 2) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1004Coded : CoefficientMerge.Poly := [(nat_lit 1578, Int.ofNat (nat_lit 1))]
theorem atom1004Coded_decode : atom1004 = SparsePolynomial.decodeCubic 24 atom1004Coded := by decide +kernel
theorem atom1004Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (505150882790400 : Int) atom1004Coded) := by
  have h := atom1004_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1004Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1005 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1005 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1005 = ((g 2) * (g 17) * (g 19)) := by
  norm_num [atom1005, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1005_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (397861070745600 : Int) atom1005) := by
  rw [SparsePolynomial.eval_scale, eval_atom1005]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 2) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1005Coded : CoefficientMerge.Poly := [(nat_lit 1579, Int.ofNat (nat_lit 1))]
theorem atom1005Coded_decode : atom1005 = SparsePolynomial.decodeCubic 24 atom1005Coded := by decide +kernel
theorem atom1005Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (397861070745600 : Int) atom1005Coded) := by
  have h := atom1005_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1005Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1006 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1006 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1006 = ((g 2) * (g 17) * (g 20)) := by
  norm_num [atom1006, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1006_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (572254855603200 : Int) atom1006) := by
  rw [SparsePolynomial.eval_scale, eval_atom1006]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 2) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1006Coded : CoefficientMerge.Poly := [(nat_lit 1580, Int.ofNat (nat_lit 1))]
theorem atom1006Coded_decode : atom1006 = SparsePolynomial.decodeCubic 24 atom1006Coded := by decide +kernel
theorem atom1006Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (572254855603200 : Int) atom1006Coded) := by
  have h := atom1006_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1006Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1007 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1007 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1007 = ((g 2) * (g 17) * (g 21)) := by
  norm_num [atom1007, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1007_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (464965043558400 : Int) atom1007) := by
  rw [SparsePolynomial.eval_scale, eval_atom1007]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 2) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1007Coded : CoefficientMerge.Poly := [(nat_lit 1581, Int.ofNat (nat_lit 1))]
theorem atom1007Coded_decode : atom1007 = SparsePolynomial.decodeCubic 24 atom1007Coded := by decide +kernel
theorem atom1007Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (464965043558400 : Int) atom1007Coded) := by
  have h := atom1007_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1007Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1008 : SparsePolynomial.Poly := [([nat_lit 2, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1008 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1008 = ((g 2) * (g 17) * (g 22)) := by
  norm_num [atom1008, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1008_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (351101944166400 : Int) atom1008) := by
  rw [SparsePolynomial.eval_scale, eval_atom1008]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 2) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1008Coded : CoefficientMerge.Poly := [(nat_lit 1582, Int.ofNat (nat_lit 1))]
theorem atom1008Coded_decode : atom1008 = SparsePolynomial.decodeCubic 24 atom1008Coded := by decide +kernel
theorem atom1008Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (351101944166400 : Int) atom1008Coded) := by
  have h := atom1008_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1008Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block014 : CoefficientMerge.Poly := [(nat_lit 1405, Int.ofNat (nat_lit 403961087933568)), (nat_lit 1406, Int.ofNat (nat_lit 381526078906368)), (nat_lit 1407, Int.ofNat (nat_lit 373878076474368)), (nat_lit 1408, Int.ofNat (nat_lit 354407563795968)), (nat_lit 1409, Int.ofNat (nat_lit 344869789575168)), (nat_lit 1410, Int.ofNat (nat_lit 379974615939072)), (nat_lit 1411, Int.ofNat (nat_lit 329477914529280)), (nat_lit 1412, Int.ofNat (nat_lit 419823011570688)), (nat_lit 1413, Int.ofNat (nat_lit 399350123656704)), (nat_lit 1414, Int.ofNat (nat_lit 445024402859520)), (nat_lit 1415, Int.ofNat (nat_lit 523432068039936)), (nat_lit 1427, Int.ofNat (nat_lit 247082976765504)), (nat_lit 1428, Int.ofNat (nat_lit 484045607060928)), (nat_lit 1429, Int.ofNat (nat_lit 457120118911104)), (nat_lit 1430, Int.ofNat (nat_lit 426520367944704)), (nat_lit 1431, Int.ofNat (nat_lit 410707623573504)), (nat_lit 1432, Int.ofNat (nat_lit 386155409531904)), (nat_lit 1433, Int.ofNat (nat_lit 371535933947904)), (nat_lit 1434, Int.ofNat (nat_lit 413692392979008)), (nat_lit 1435, Int.ofNat (nat_lit 347494413911040)), (nat_lit 1436, Int.ofNat (nat_lit 444055027065408)), (nat_lit 1437, Int.ofNat (nat_lit 410230735782912)), (nat_lit 1438, Int.ofNat (nat_lit 452841657269760)), (nat_lit 1439, Int.ofNat (nat_lit 528185964734208)), (nat_lit 1452, Int.ofNat (nat_lit 284228831677824)), (nat_lit 1453, Int.ofNat (nat_lit 526699029124224)), (nat_lit 1454, Int.ofNat (nat_lit 493080024628224)), (nat_lit 1455, Int.ofNat (nat_lit 474248026727424)), (nat_lit 1456, Int.ofNat (nat_lit 443593518580224)), (nat_lit 1457, Int.ofNat (nat_lit 422871748890624)), (nat_lit 1458, Int.ofNat (nat_lit 484590100376448)), (nat_lit 1459, Int.ofNat (nat_lit 377389276323840)), (nat_lit 1460, Int.ofNat (nat_lit 521076290917248)), (nat_lit 1461, Int.ofNat (nat_lit 409448281347072)), (nat_lit 1462, Int.ofNat (nat_lit 433641756303360)), (nat_lit 1463, Int.ofNat (nat_lit 490568617237248)), (nat_lit 1477, Int.ofNat (nat_lit 289736398828800)), (nat_lit 1478, Int.ofNat (nat_lit 526404059596800)), (nat_lit 1479, Int.ofNat (nat_lit 497366134272000)), (nat_lit 1480, Int.ofNat (nat_lit 459588739276800)), (nat_lit 1481, Int.ofNat (nat_lit 431744082739200)), (nat_lit 1482, Int.ofNat (nat_lit 482321582265600)), (nat_lit 1483, Int.ofNat (nat_lit 377204281977600)), (nat_lit 1484, Int.ofNat (nat_lit 524931329260800)), (nat_lit 1485, Int.ofNat (nat_lit 405394404307200)), (nat_lit 1486, Int.ofNat (nat_lit 429382919750400)), (nat_lit 1487, Int.ofNat (nat_lit 486104821171200)), (nat_lit 1502, Int.ofNat (nat_lit 283933862150400)), (nat_lit 1503, Int.ofNat (nat_lit 525551462150400)), (nat_lit 1504, Int.ofNat (nat_lit 479630587564800)), (nat_lit 1505, Int.ofNat (nat_lit 443642451436800)), (nat_lit 1506, Int.ofNat (nat_lit 472704538521600)), (nat_lit 1507, Int.ofNat (nat_lit 375370378336800)), (nat_lit 1508, Int.ofNat (nat_lit 521437841971200)), (nat_lit 1509, Int.ofNat (nat_lit 404962695244800)), (nat_lit 1510, Int.ofNat (nat_lit 411634200146400)), (nat_lit 1511, Int.ofNat (nat_lit 463618871100000)), (nat_lit 1527, Int.ofNat (nat_lit 291966841958400)), (nat_lit 1528, Int.ofNat (nat_lit 515495981952000)), (nat_lit 1529, Int.ofNat (nat_lit 470343773491200)), (nat_lit 1530, Int.ofNat (nat_lit 492661507968000)), (nat_lit 1531, Int.ofNat (nat_lit 379248139468800)), (nat_lit 1532, Int.ofNat (nat_lit 547518367872000)), (nat_lit 1533, Int.ofNat (nat_lit 434104999372800)), (nat_lit 1534, Int.ofNat (nat_lit 373035023424000)), (nat_lit 1535, Int.ofNat (nat_lit 415072942099200)), (nat_lit 1552, Int.ofNat (nat_lit 276961422528000)), (nat_lit 1553, Int.ofNat (nat_lit 495502930944000)), (nat_lit 1554, Int.ofNat (nat_lit 488973456921600)), (nat_lit 1555, Int.ofNat (nat_lit 378621866649600)), (nat_lit 1556, Int.ofNat (nat_lit 549953873280000)), (nat_lit 1557, Int.ofNat (nat_lit 439602283008000)), (nat_lit 1558, Int.ofNat (nat_lit 323801088307200)), (nat_lit 1559, Int.ofNat (nat_lit 445435576185600)), (nat_lit 1577, Int.ofNat (nat_lit 267182675020800)), (nat_lit 1578, Int.ofNat (nat_lit 505150882790400)), (nat_lit 1579, Int.ofNat (nat_lit 397861070745600)), (nat_lit 1580, Int.ofNat (nat_lit 572254855603200)), (nat_lit 1581, Int.ofNat (nat_lit 464965043558400)), (nat_lit 1582, Int.ofNat (nat_lit 351101944166400))]
def block014_data_flat000 : CoefficientMerge.Poly := [(nat_lit 1405, Int.ofNat (nat_lit 403961087933568))]
theorem block014_data_flat000_step : block014_data_flat000 = (CoefficientMerge.scale (403961087933568 : Int) atom0929Coded) := by decide +kernel
theorem block014_data_flat000_original : block014_data_flat000 = (CoefficientMerge.scale (403961087933568 : Int) atom0929Coded) := by
  rw [block014_data_flat000_step]
def block014_data_flat001 : CoefficientMerge.Poly := [(nat_lit 1406, Int.ofNat (nat_lit 381526078906368))]
theorem block014_data_flat001_step : block014_data_flat001 = (CoefficientMerge.scale (381526078906368 : Int) atom0930Coded) := by decide +kernel
theorem block014_data_flat001_original : block014_data_flat001 = (CoefficientMerge.scale (381526078906368 : Int) atom0930Coded) := by
  rw [block014_data_flat001_step]
def block014_data_flat002 : CoefficientMerge.Poly := [(nat_lit 1405, Int.ofNat (nat_lit 403961087933568)), (nat_lit 1406, Int.ofNat (nat_lit 381526078906368))]
theorem block014_data_flat002_step : block014_data_flat002 = (CoefficientMerge.fastMerge block014_data_flat000 block014_data_flat001) := by decide +kernel
theorem block014_data_flat002_original : block014_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (403961087933568 : Int) atom0929Coded) (CoefficientMerge.scale (381526078906368 : Int) atom0930Coded)) := by
  rw [block014_data_flat002_step, block014_data_flat000_original, block014_data_flat001_original]
def block014_data_flat003 : CoefficientMerge.Poly := [(nat_lit 1407, Int.ofNat (nat_lit 373878076474368))]
theorem block014_data_flat003_step : block014_data_flat003 = (CoefficientMerge.scale (373878076474368 : Int) atom0931Coded) := by decide +kernel
theorem block014_data_flat003_original : block014_data_flat003 = (CoefficientMerge.scale (373878076474368 : Int) atom0931Coded) := by
  rw [block014_data_flat003_step]
def block014_data_flat004 : CoefficientMerge.Poly := [(nat_lit 1408, Int.ofNat (nat_lit 354407563795968))]
theorem block014_data_flat004_step : block014_data_flat004 = (CoefficientMerge.scale (354407563795968 : Int) atom0932Coded) := by decide +kernel
theorem block014_data_flat004_original : block014_data_flat004 = (CoefficientMerge.scale (354407563795968 : Int) atom0932Coded) := by
  rw [block014_data_flat004_step]
def block014_data_flat005 : CoefficientMerge.Poly := [(nat_lit 1409, Int.ofNat (nat_lit 344869789575168))]
theorem block014_data_flat005_step : block014_data_flat005 = (CoefficientMerge.scale (344869789575168 : Int) atom0933Coded) := by decide +kernel
theorem block014_data_flat005_original : block014_data_flat005 = (CoefficientMerge.scale (344869789575168 : Int) atom0933Coded) := by
  rw [block014_data_flat005_step]
def block014_data_flat006 : CoefficientMerge.Poly := [(nat_lit 1408, Int.ofNat (nat_lit 354407563795968)), (nat_lit 1409, Int.ofNat (nat_lit 344869789575168))]
theorem block014_data_flat006_step : block014_data_flat006 = (CoefficientMerge.fastMerge block014_data_flat004 block014_data_flat005) := by decide +kernel
theorem block014_data_flat006_original : block014_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (354407563795968 : Int) atom0932Coded) (CoefficientMerge.scale (344869789575168 : Int) atom0933Coded)) := by
  rw [block014_data_flat006_step, block014_data_flat004_original, block014_data_flat005_original]
def block014_data_flat007 : CoefficientMerge.Poly := [(nat_lit 1407, Int.ofNat (nat_lit 373878076474368)), (nat_lit 1408, Int.ofNat (nat_lit 354407563795968)), (nat_lit 1409, Int.ofNat (nat_lit 344869789575168))]
theorem block014_data_flat007_step : block014_data_flat007 = (CoefficientMerge.fastMerge block014_data_flat003 block014_data_flat006) := by decide +kernel
theorem block014_data_flat007_original : block014_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (373878076474368 : Int) atom0931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (354407563795968 : Int) atom0932Coded) (CoefficientMerge.scale (344869789575168 : Int) atom0933Coded))) := by
  rw [block014_data_flat007_step, block014_data_flat003_original, block014_data_flat006_original]
def block014_data_flat008 : CoefficientMerge.Poly := [(nat_lit 1405, Int.ofNat (nat_lit 403961087933568)), (nat_lit 1406, Int.ofNat (nat_lit 381526078906368)), (nat_lit 1407, Int.ofNat (nat_lit 373878076474368)), (nat_lit 1408, Int.ofNat (nat_lit 354407563795968)), (nat_lit 1409, Int.ofNat (nat_lit 344869789575168))]
theorem block014_data_flat008_step : block014_data_flat008 = (CoefficientMerge.fastMerge block014_data_flat002 block014_data_flat007) := by decide +kernel
theorem block014_data_flat008_original : block014_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (403961087933568 : Int) atom0929Coded) (CoefficientMerge.scale (381526078906368 : Int) atom0930Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (373878076474368 : Int) atom0931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (354407563795968 : Int) atom0932Coded) (CoefficientMerge.scale (344869789575168 : Int) atom0933Coded)))) := by
  rw [block014_data_flat008_step, block014_data_flat002_original, block014_data_flat007_original]
def block014_data_flat009 : CoefficientMerge.Poly := [(nat_lit 1410, Int.ofNat (nat_lit 379974615939072))]
theorem block014_data_flat009_step : block014_data_flat009 = (CoefficientMerge.scale (379974615939072 : Int) atom0934Coded) := by decide +kernel
theorem block014_data_flat009_original : block014_data_flat009 = (CoefficientMerge.scale (379974615939072 : Int) atom0934Coded) := by
  rw [block014_data_flat009_step]
def block014_data_flat010 : CoefficientMerge.Poly := [(nat_lit 1411, Int.ofNat (nat_lit 329477914529280))]
theorem block014_data_flat010_step : block014_data_flat010 = (CoefficientMerge.scale (329477914529280 : Int) atom0935Coded) := by decide +kernel
theorem block014_data_flat010_original : block014_data_flat010 = (CoefficientMerge.scale (329477914529280 : Int) atom0935Coded) := by
  rw [block014_data_flat010_step]
def block014_data_flat011 : CoefficientMerge.Poly := [(nat_lit 1410, Int.ofNat (nat_lit 379974615939072)), (nat_lit 1411, Int.ofNat (nat_lit 329477914529280))]
theorem block014_data_flat011_step : block014_data_flat011 = (CoefficientMerge.fastMerge block014_data_flat009 block014_data_flat010) := by decide +kernel
theorem block014_data_flat011_original : block014_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (379974615939072 : Int) atom0934Coded) (CoefficientMerge.scale (329477914529280 : Int) atom0935Coded)) := by
  rw [block014_data_flat011_step, block014_data_flat009_original, block014_data_flat010_original]
def block014_data_flat012 : CoefficientMerge.Poly := [(nat_lit 1412, Int.ofNat (nat_lit 419823011570688))]
theorem block014_data_flat012_step : block014_data_flat012 = (CoefficientMerge.scale (419823011570688 : Int) atom0936Coded) := by decide +kernel
theorem block014_data_flat012_original : block014_data_flat012 = (CoefficientMerge.scale (419823011570688 : Int) atom0936Coded) := by
  rw [block014_data_flat012_step]
def block014_data_flat013 : CoefficientMerge.Poly := [(nat_lit 1413, Int.ofNat (nat_lit 399350123656704))]
theorem block014_data_flat013_step : block014_data_flat013 = (CoefficientMerge.scale (399350123656704 : Int) atom0937Coded) := by decide +kernel
theorem block014_data_flat013_original : block014_data_flat013 = (CoefficientMerge.scale (399350123656704 : Int) atom0937Coded) := by
  rw [block014_data_flat013_step]
def block014_data_flat014 : CoefficientMerge.Poly := [(nat_lit 1414, Int.ofNat (nat_lit 445024402859520))]
theorem block014_data_flat014_step : block014_data_flat014 = (CoefficientMerge.scale (445024402859520 : Int) atom0938Coded) := by decide +kernel
theorem block014_data_flat014_original : block014_data_flat014 = (CoefficientMerge.scale (445024402859520 : Int) atom0938Coded) := by
  rw [block014_data_flat014_step]
def block014_data_flat015 : CoefficientMerge.Poly := [(nat_lit 1413, Int.ofNat (nat_lit 399350123656704)), (nat_lit 1414, Int.ofNat (nat_lit 445024402859520))]
theorem block014_data_flat015_step : block014_data_flat015 = (CoefficientMerge.fastMerge block014_data_flat013 block014_data_flat014) := by decide +kernel
theorem block014_data_flat015_original : block014_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (399350123656704 : Int) atom0937Coded) (CoefficientMerge.scale (445024402859520 : Int) atom0938Coded)) := by
  rw [block014_data_flat015_step, block014_data_flat013_original, block014_data_flat014_original]
def block014_data_flat016 : CoefficientMerge.Poly := [(nat_lit 1412, Int.ofNat (nat_lit 419823011570688)), (nat_lit 1413, Int.ofNat (nat_lit 399350123656704)), (nat_lit 1414, Int.ofNat (nat_lit 445024402859520))]
theorem block014_data_flat016_step : block014_data_flat016 = (CoefficientMerge.fastMerge block014_data_flat012 block014_data_flat015) := by decide +kernel
theorem block014_data_flat016_original : block014_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (419823011570688 : Int) atom0936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (399350123656704 : Int) atom0937Coded) (CoefficientMerge.scale (445024402859520 : Int) atom0938Coded))) := by
  rw [block014_data_flat016_step, block014_data_flat012_original, block014_data_flat015_original]
def block014_data_flat017 : CoefficientMerge.Poly := [(nat_lit 1410, Int.ofNat (nat_lit 379974615939072)), (nat_lit 1411, Int.ofNat (nat_lit 329477914529280)), (nat_lit 1412, Int.ofNat (nat_lit 419823011570688)), (nat_lit 1413, Int.ofNat (nat_lit 399350123656704)), (nat_lit 1414, Int.ofNat (nat_lit 445024402859520))]
theorem block014_data_flat017_step : block014_data_flat017 = (CoefficientMerge.fastMerge block014_data_flat011 block014_data_flat016) := by decide +kernel
theorem block014_data_flat017_original : block014_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (379974615939072 : Int) atom0934Coded) (CoefficientMerge.scale (329477914529280 : Int) atom0935Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (419823011570688 : Int) atom0936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (399350123656704 : Int) atom0937Coded) (CoefficientMerge.scale (445024402859520 : Int) atom0938Coded)))) := by
  rw [block014_data_flat017_step, block014_data_flat011_original, block014_data_flat016_original]
def block014_data_flat018 : CoefficientMerge.Poly := [(nat_lit 1405, Int.ofNat (nat_lit 403961087933568)), (nat_lit 1406, Int.ofNat (nat_lit 381526078906368)), (nat_lit 1407, Int.ofNat (nat_lit 373878076474368)), (nat_lit 1408, Int.ofNat (nat_lit 354407563795968)), (nat_lit 1409, Int.ofNat (nat_lit 344869789575168)), (nat_lit 1410, Int.ofNat (nat_lit 379974615939072)), (nat_lit 1411, Int.ofNat (nat_lit 329477914529280)), (nat_lit 1412, Int.ofNat (nat_lit 419823011570688)), (nat_lit 1413, Int.ofNat (nat_lit 399350123656704)), (nat_lit 1414, Int.ofNat (nat_lit 445024402859520))]
theorem block014_data_flat018_step : block014_data_flat018 = (CoefficientMerge.fastMerge block014_data_flat008 block014_data_flat017) := by decide +kernel
theorem block014_data_flat018_original : block014_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (403961087933568 : Int) atom0929Coded) (CoefficientMerge.scale (381526078906368 : Int) atom0930Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (373878076474368 : Int) atom0931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (354407563795968 : Int) atom0932Coded) (CoefficientMerge.scale (344869789575168 : Int) atom0933Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (379974615939072 : Int) atom0934Coded) (CoefficientMerge.scale (329477914529280 : Int) atom0935Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (419823011570688 : Int) atom0936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (399350123656704 : Int) atom0937Coded) (CoefficientMerge.scale (445024402859520 : Int) atom0938Coded))))) := by
  rw [block014_data_flat018_step, block014_data_flat008_original, block014_data_flat017_original]
def block014_data_flat019 : CoefficientMerge.Poly := [(nat_lit 1415, Int.ofNat (nat_lit 523432068039936))]
theorem block014_data_flat019_step : block014_data_flat019 = (CoefficientMerge.scale (523432068039936 : Int) atom0939Coded) := by decide +kernel
theorem block014_data_flat019_original : block014_data_flat019 = (CoefficientMerge.scale (523432068039936 : Int) atom0939Coded) := by
  rw [block014_data_flat019_step]
def block014_data_flat020 : CoefficientMerge.Poly := [(nat_lit 1427, Int.ofNat (nat_lit 247082976765504))]
theorem block014_data_flat020_step : block014_data_flat020 = (CoefficientMerge.scale (247082976765504 : Int) atom0940Coded) := by decide +kernel
theorem block014_data_flat020_original : block014_data_flat020 = (CoefficientMerge.scale (247082976765504 : Int) atom0940Coded) := by
  rw [block014_data_flat020_step]
def block014_data_flat021 : CoefficientMerge.Poly := [(nat_lit 1415, Int.ofNat (nat_lit 523432068039936)), (nat_lit 1427, Int.ofNat (nat_lit 247082976765504))]
theorem block014_data_flat021_step : block014_data_flat021 = (CoefficientMerge.fastMerge block014_data_flat019 block014_data_flat020) := by decide +kernel
theorem block014_data_flat021_original : block014_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (523432068039936 : Int) atom0939Coded) (CoefficientMerge.scale (247082976765504 : Int) atom0940Coded)) := by
  rw [block014_data_flat021_step, block014_data_flat019_original, block014_data_flat020_original]
def block014_data_flat022 : CoefficientMerge.Poly := [(nat_lit 1428, Int.ofNat (nat_lit 484045607060928))]
theorem block014_data_flat022_step : block014_data_flat022 = (CoefficientMerge.scale (484045607060928 : Int) atom0941Coded) := by decide +kernel
theorem block014_data_flat022_original : block014_data_flat022 = (CoefficientMerge.scale (484045607060928 : Int) atom0941Coded) := by
  rw [block014_data_flat022_step]
def block014_data_flat023 : CoefficientMerge.Poly := [(nat_lit 1429, Int.ofNat (nat_lit 457120118911104))]
theorem block014_data_flat023_step : block014_data_flat023 = (CoefficientMerge.scale (457120118911104 : Int) atom0942Coded) := by decide +kernel
theorem block014_data_flat023_original : block014_data_flat023 = (CoefficientMerge.scale (457120118911104 : Int) atom0942Coded) := by
  rw [block014_data_flat023_step]
def block014_data_flat024 : CoefficientMerge.Poly := [(nat_lit 1430, Int.ofNat (nat_lit 426520367944704))]
theorem block014_data_flat024_step : block014_data_flat024 = (CoefficientMerge.scale (426520367944704 : Int) atom0943Coded) := by decide +kernel
theorem block014_data_flat024_original : block014_data_flat024 = (CoefficientMerge.scale (426520367944704 : Int) atom0943Coded) := by
  rw [block014_data_flat024_step]
def block014_data_flat025 : CoefficientMerge.Poly := [(nat_lit 1429, Int.ofNat (nat_lit 457120118911104)), (nat_lit 1430, Int.ofNat (nat_lit 426520367944704))]
theorem block014_data_flat025_step : block014_data_flat025 = (CoefficientMerge.fastMerge block014_data_flat023 block014_data_flat024) := by decide +kernel
theorem block014_data_flat025_original : block014_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (457120118911104 : Int) atom0942Coded) (CoefficientMerge.scale (426520367944704 : Int) atom0943Coded)) := by
  rw [block014_data_flat025_step, block014_data_flat023_original, block014_data_flat024_original]
def block014_data_flat026 : CoefficientMerge.Poly := [(nat_lit 1428, Int.ofNat (nat_lit 484045607060928)), (nat_lit 1429, Int.ofNat (nat_lit 457120118911104)), (nat_lit 1430, Int.ofNat (nat_lit 426520367944704))]
theorem block014_data_flat026_step : block014_data_flat026 = (CoefficientMerge.fastMerge block014_data_flat022 block014_data_flat025) := by decide +kernel
theorem block014_data_flat026_original : block014_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (484045607060928 : Int) atom0941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457120118911104 : Int) atom0942Coded) (CoefficientMerge.scale (426520367944704 : Int) atom0943Coded))) := by
  rw [block014_data_flat026_step, block014_data_flat022_original, block014_data_flat025_original]
def block014_data_flat027 : CoefficientMerge.Poly := [(nat_lit 1415, Int.ofNat (nat_lit 523432068039936)), (nat_lit 1427, Int.ofNat (nat_lit 247082976765504)), (nat_lit 1428, Int.ofNat (nat_lit 484045607060928)), (nat_lit 1429, Int.ofNat (nat_lit 457120118911104)), (nat_lit 1430, Int.ofNat (nat_lit 426520367944704))]
theorem block014_data_flat027_step : block014_data_flat027 = (CoefficientMerge.fastMerge block014_data_flat021 block014_data_flat026) := by decide +kernel
theorem block014_data_flat027_original : block014_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (523432068039936 : Int) atom0939Coded) (CoefficientMerge.scale (247082976765504 : Int) atom0940Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (484045607060928 : Int) atom0941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457120118911104 : Int) atom0942Coded) (CoefficientMerge.scale (426520367944704 : Int) atom0943Coded)))) := by
  rw [block014_data_flat027_step, block014_data_flat021_original, block014_data_flat026_original]
def block014_data_flat028 : CoefficientMerge.Poly := [(nat_lit 1431, Int.ofNat (nat_lit 410707623573504))]
theorem block014_data_flat028_step : block014_data_flat028 = (CoefficientMerge.scale (410707623573504 : Int) atom0944Coded) := by decide +kernel
theorem block014_data_flat028_original : block014_data_flat028 = (CoefficientMerge.scale (410707623573504 : Int) atom0944Coded) := by
  rw [block014_data_flat028_step]
def block014_data_flat029 : CoefficientMerge.Poly := [(nat_lit 1432, Int.ofNat (nat_lit 386155409531904))]
theorem block014_data_flat029_step : block014_data_flat029 = (CoefficientMerge.scale (386155409531904 : Int) atom0945Coded) := by decide +kernel
theorem block014_data_flat029_original : block014_data_flat029 = (CoefficientMerge.scale (386155409531904 : Int) atom0945Coded) := by
  rw [block014_data_flat029_step]
def block014_data_flat030 : CoefficientMerge.Poly := [(nat_lit 1431, Int.ofNat (nat_lit 410707623573504)), (nat_lit 1432, Int.ofNat (nat_lit 386155409531904))]
theorem block014_data_flat030_step : block014_data_flat030 = (CoefficientMerge.fastMerge block014_data_flat028 block014_data_flat029) := by decide +kernel
theorem block014_data_flat030_original : block014_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (410707623573504 : Int) atom0944Coded) (CoefficientMerge.scale (386155409531904 : Int) atom0945Coded)) := by
  rw [block014_data_flat030_step, block014_data_flat028_original, block014_data_flat029_original]
def block014_data_flat031 : CoefficientMerge.Poly := [(nat_lit 1433, Int.ofNat (nat_lit 371535933947904))]
theorem block014_data_flat031_step : block014_data_flat031 = (CoefficientMerge.scale (371535933947904 : Int) atom0946Coded) := by decide +kernel
theorem block014_data_flat031_original : block014_data_flat031 = (CoefficientMerge.scale (371535933947904 : Int) atom0946Coded) := by
  rw [block014_data_flat031_step]
def block014_data_flat032 : CoefficientMerge.Poly := [(nat_lit 1434, Int.ofNat (nat_lit 413692392979008))]
theorem block014_data_flat032_step : block014_data_flat032 = (CoefficientMerge.scale (413692392979008 : Int) atom0947Coded) := by decide +kernel
theorem block014_data_flat032_original : block014_data_flat032 = (CoefficientMerge.scale (413692392979008 : Int) atom0947Coded) := by
  rw [block014_data_flat032_step]
def block014_data_flat033 : CoefficientMerge.Poly := [(nat_lit 1435, Int.ofNat (nat_lit 347494413911040))]
theorem block014_data_flat033_step : block014_data_flat033 = (CoefficientMerge.scale (347494413911040 : Int) atom0948Coded) := by decide +kernel
theorem block014_data_flat033_original : block014_data_flat033 = (CoefficientMerge.scale (347494413911040 : Int) atom0948Coded) := by
  rw [block014_data_flat033_step]
def block014_data_flat034 : CoefficientMerge.Poly := [(nat_lit 1434, Int.ofNat (nat_lit 413692392979008)), (nat_lit 1435, Int.ofNat (nat_lit 347494413911040))]
theorem block014_data_flat034_step : block014_data_flat034 = (CoefficientMerge.fastMerge block014_data_flat032 block014_data_flat033) := by decide +kernel
theorem block014_data_flat034_original : block014_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (413692392979008 : Int) atom0947Coded) (CoefficientMerge.scale (347494413911040 : Int) atom0948Coded)) := by
  rw [block014_data_flat034_step, block014_data_flat032_original, block014_data_flat033_original]
def block014_data_flat035 : CoefficientMerge.Poly := [(nat_lit 1433, Int.ofNat (nat_lit 371535933947904)), (nat_lit 1434, Int.ofNat (nat_lit 413692392979008)), (nat_lit 1435, Int.ofNat (nat_lit 347494413911040))]
theorem block014_data_flat035_step : block014_data_flat035 = (CoefficientMerge.fastMerge block014_data_flat031 block014_data_flat034) := by decide +kernel
theorem block014_data_flat035_original : block014_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (371535933947904 : Int) atom0946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413692392979008 : Int) atom0947Coded) (CoefficientMerge.scale (347494413911040 : Int) atom0948Coded))) := by
  rw [block014_data_flat035_step, block014_data_flat031_original, block014_data_flat034_original]
def block014_data_flat036 : CoefficientMerge.Poly := [(nat_lit 1431, Int.ofNat (nat_lit 410707623573504)), (nat_lit 1432, Int.ofNat (nat_lit 386155409531904)), (nat_lit 1433, Int.ofNat (nat_lit 371535933947904)), (nat_lit 1434, Int.ofNat (nat_lit 413692392979008)), (nat_lit 1435, Int.ofNat (nat_lit 347494413911040))]
theorem block014_data_flat036_step : block014_data_flat036 = (CoefficientMerge.fastMerge block014_data_flat030 block014_data_flat035) := by decide +kernel
theorem block014_data_flat036_original : block014_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (410707623573504 : Int) atom0944Coded) (CoefficientMerge.scale (386155409531904 : Int) atom0945Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (371535933947904 : Int) atom0946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413692392979008 : Int) atom0947Coded) (CoefficientMerge.scale (347494413911040 : Int) atom0948Coded)))) := by
  rw [block014_data_flat036_step, block014_data_flat030_original, block014_data_flat035_original]
def block014_data_flat037 : CoefficientMerge.Poly := [(nat_lit 1415, Int.ofNat (nat_lit 523432068039936)), (nat_lit 1427, Int.ofNat (nat_lit 247082976765504)), (nat_lit 1428, Int.ofNat (nat_lit 484045607060928)), (nat_lit 1429, Int.ofNat (nat_lit 457120118911104)), (nat_lit 1430, Int.ofNat (nat_lit 426520367944704)), (nat_lit 1431, Int.ofNat (nat_lit 410707623573504)), (nat_lit 1432, Int.ofNat (nat_lit 386155409531904)), (nat_lit 1433, Int.ofNat (nat_lit 371535933947904)), (nat_lit 1434, Int.ofNat (nat_lit 413692392979008)), (nat_lit 1435, Int.ofNat (nat_lit 347494413911040))]
theorem block014_data_flat037_step : block014_data_flat037 = (CoefficientMerge.fastMerge block014_data_flat027 block014_data_flat036) := by decide +kernel
theorem block014_data_flat037_original : block014_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (523432068039936 : Int) atom0939Coded) (CoefficientMerge.scale (247082976765504 : Int) atom0940Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (484045607060928 : Int) atom0941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457120118911104 : Int) atom0942Coded) (CoefficientMerge.scale (426520367944704 : Int) atom0943Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (410707623573504 : Int) atom0944Coded) (CoefficientMerge.scale (386155409531904 : Int) atom0945Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (371535933947904 : Int) atom0946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413692392979008 : Int) atom0947Coded) (CoefficientMerge.scale (347494413911040 : Int) atom0948Coded))))) := by
  rw [block014_data_flat037_step, block014_data_flat027_original, block014_data_flat036_original]
def block014_data_flat038 : CoefficientMerge.Poly := [(nat_lit 1405, Int.ofNat (nat_lit 403961087933568)), (nat_lit 1406, Int.ofNat (nat_lit 381526078906368)), (nat_lit 1407, Int.ofNat (nat_lit 373878076474368)), (nat_lit 1408, Int.ofNat (nat_lit 354407563795968)), (nat_lit 1409, Int.ofNat (nat_lit 344869789575168)), (nat_lit 1410, Int.ofNat (nat_lit 379974615939072)), (nat_lit 1411, Int.ofNat (nat_lit 329477914529280)), (nat_lit 1412, Int.ofNat (nat_lit 419823011570688)), (nat_lit 1413, Int.ofNat (nat_lit 399350123656704)), (nat_lit 1414, Int.ofNat (nat_lit 445024402859520)), (nat_lit 1415, Int.ofNat (nat_lit 523432068039936)), (nat_lit 1427, Int.ofNat (nat_lit 247082976765504)), (nat_lit 1428, Int.ofNat (nat_lit 484045607060928)), (nat_lit 1429, Int.ofNat (nat_lit 457120118911104)), (nat_lit 1430, Int.ofNat (nat_lit 426520367944704)), (nat_lit 1431, Int.ofNat (nat_lit 410707623573504)), (nat_lit 1432, Int.ofNat (nat_lit 386155409531904)), (nat_lit 1433, Int.ofNat (nat_lit 371535933947904)), (nat_lit 1434, Int.ofNat (nat_lit 413692392979008)), (nat_lit 1435, Int.ofNat (nat_lit 347494413911040))]
theorem block014_data_flat038_step : block014_data_flat038 = (CoefficientMerge.fastMerge block014_data_flat018 block014_data_flat037) := by decide +kernel
theorem block014_data_flat038_original : block014_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (403961087933568 : Int) atom0929Coded) (CoefficientMerge.scale (381526078906368 : Int) atom0930Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (373878076474368 : Int) atom0931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (354407563795968 : Int) atom0932Coded) (CoefficientMerge.scale (344869789575168 : Int) atom0933Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (379974615939072 : Int) atom0934Coded) (CoefficientMerge.scale (329477914529280 : Int) atom0935Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (419823011570688 : Int) atom0936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (399350123656704 : Int) atom0937Coded) (CoefficientMerge.scale (445024402859520 : Int) atom0938Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (523432068039936 : Int) atom0939Coded) (CoefficientMerge.scale (247082976765504 : Int) atom0940Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (484045607060928 : Int) atom0941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457120118911104 : Int) atom0942Coded) (CoefficientMerge.scale (426520367944704 : Int) atom0943Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (410707623573504 : Int) atom0944Coded) (CoefficientMerge.scale (386155409531904 : Int) atom0945Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (371535933947904 : Int) atom0946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413692392979008 : Int) atom0947Coded) (CoefficientMerge.scale (347494413911040 : Int) atom0948Coded)))))) := by
  rw [block014_data_flat038_step, block014_data_flat018_original, block014_data_flat037_original]
def block014_data_flat039 : CoefficientMerge.Poly := [(nat_lit 1436, Int.ofNat (nat_lit 444055027065408))]
theorem block014_data_flat039_step : block014_data_flat039 = (CoefficientMerge.scale (444055027065408 : Int) atom0949Coded) := by decide +kernel
theorem block014_data_flat039_original : block014_data_flat039 = (CoefficientMerge.scale (444055027065408 : Int) atom0949Coded) := by
  rw [block014_data_flat039_step]
def block014_data_flat040 : CoefficientMerge.Poly := [(nat_lit 1437, Int.ofNat (nat_lit 410230735782912))]
theorem block014_data_flat040_step : block014_data_flat040 = (CoefficientMerge.scale (410230735782912 : Int) atom0950Coded) := by decide +kernel
theorem block014_data_flat040_original : block014_data_flat040 = (CoefficientMerge.scale (410230735782912 : Int) atom0950Coded) := by
  rw [block014_data_flat040_step]
def block014_data_flat041 : CoefficientMerge.Poly := [(nat_lit 1436, Int.ofNat (nat_lit 444055027065408)), (nat_lit 1437, Int.ofNat (nat_lit 410230735782912))]
theorem block014_data_flat041_step : block014_data_flat041 = (CoefficientMerge.fastMerge block014_data_flat039 block014_data_flat040) := by decide +kernel
theorem block014_data_flat041_original : block014_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (444055027065408 : Int) atom0949Coded) (CoefficientMerge.scale (410230735782912 : Int) atom0950Coded)) := by
  rw [block014_data_flat041_step, block014_data_flat039_original, block014_data_flat040_original]
def block014_data_flat042 : CoefficientMerge.Poly := [(nat_lit 1438, Int.ofNat (nat_lit 452841657269760))]
theorem block014_data_flat042_step : block014_data_flat042 = (CoefficientMerge.scale (452841657269760 : Int) atom0951Coded) := by decide +kernel
theorem block014_data_flat042_original : block014_data_flat042 = (CoefficientMerge.scale (452841657269760 : Int) atom0951Coded) := by
  rw [block014_data_flat042_step]
def block014_data_flat043 : CoefficientMerge.Poly := [(nat_lit 1439, Int.ofNat (nat_lit 528185964734208))]
theorem block014_data_flat043_step : block014_data_flat043 = (CoefficientMerge.scale (528185964734208 : Int) atom0952Coded) := by decide +kernel
theorem block014_data_flat043_original : block014_data_flat043 = (CoefficientMerge.scale (528185964734208 : Int) atom0952Coded) := by
  rw [block014_data_flat043_step]
def block014_data_flat044 : CoefficientMerge.Poly := [(nat_lit 1452, Int.ofNat (nat_lit 284228831677824))]
theorem block014_data_flat044_step : block014_data_flat044 = (CoefficientMerge.scale (284228831677824 : Int) atom0953Coded) := by decide +kernel
theorem block014_data_flat044_original : block014_data_flat044 = (CoefficientMerge.scale (284228831677824 : Int) atom0953Coded) := by
  rw [block014_data_flat044_step]
def block014_data_flat045 : CoefficientMerge.Poly := [(nat_lit 1439, Int.ofNat (nat_lit 528185964734208)), (nat_lit 1452, Int.ofNat (nat_lit 284228831677824))]
theorem block014_data_flat045_step : block014_data_flat045 = (CoefficientMerge.fastMerge block014_data_flat043 block014_data_flat044) := by decide +kernel
theorem block014_data_flat045_original : block014_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (528185964734208 : Int) atom0952Coded) (CoefficientMerge.scale (284228831677824 : Int) atom0953Coded)) := by
  rw [block014_data_flat045_step, block014_data_flat043_original, block014_data_flat044_original]
def block014_data_flat046 : CoefficientMerge.Poly := [(nat_lit 1438, Int.ofNat (nat_lit 452841657269760)), (nat_lit 1439, Int.ofNat (nat_lit 528185964734208)), (nat_lit 1452, Int.ofNat (nat_lit 284228831677824))]
theorem block014_data_flat046_step : block014_data_flat046 = (CoefficientMerge.fastMerge block014_data_flat042 block014_data_flat045) := by decide +kernel
theorem block014_data_flat046_original : block014_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (452841657269760 : Int) atom0951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (528185964734208 : Int) atom0952Coded) (CoefficientMerge.scale (284228831677824 : Int) atom0953Coded))) := by
  rw [block014_data_flat046_step, block014_data_flat042_original, block014_data_flat045_original]
def block014_data_flat047 : CoefficientMerge.Poly := [(nat_lit 1436, Int.ofNat (nat_lit 444055027065408)), (nat_lit 1437, Int.ofNat (nat_lit 410230735782912)), (nat_lit 1438, Int.ofNat (nat_lit 452841657269760)), (nat_lit 1439, Int.ofNat (nat_lit 528185964734208)), (nat_lit 1452, Int.ofNat (nat_lit 284228831677824))]
theorem block014_data_flat047_step : block014_data_flat047 = (CoefficientMerge.fastMerge block014_data_flat041 block014_data_flat046) := by decide +kernel
theorem block014_data_flat047_original : block014_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (444055027065408 : Int) atom0949Coded) (CoefficientMerge.scale (410230735782912 : Int) atom0950Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (452841657269760 : Int) atom0951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (528185964734208 : Int) atom0952Coded) (CoefficientMerge.scale (284228831677824 : Int) atom0953Coded)))) := by
  rw [block014_data_flat047_step, block014_data_flat041_original, block014_data_flat046_original]
def block014_data_flat048 : CoefficientMerge.Poly := [(nat_lit 1453, Int.ofNat (nat_lit 526699029124224))]
theorem block014_data_flat048_step : block014_data_flat048 = (CoefficientMerge.scale (526699029124224 : Int) atom0954Coded) := by decide +kernel
theorem block014_data_flat048_original : block014_data_flat048 = (CoefficientMerge.scale (526699029124224 : Int) atom0954Coded) := by
  rw [block014_data_flat048_step]
def block014_data_flat049 : CoefficientMerge.Poly := [(nat_lit 1454, Int.ofNat (nat_lit 493080024628224))]
theorem block014_data_flat049_step : block014_data_flat049 = (CoefficientMerge.scale (493080024628224 : Int) atom0955Coded) := by decide +kernel
theorem block014_data_flat049_original : block014_data_flat049 = (CoefficientMerge.scale (493080024628224 : Int) atom0955Coded) := by
  rw [block014_data_flat049_step]
def block014_data_flat050 : CoefficientMerge.Poly := [(nat_lit 1453, Int.ofNat (nat_lit 526699029124224)), (nat_lit 1454, Int.ofNat (nat_lit 493080024628224))]
theorem block014_data_flat050_step : block014_data_flat050 = (CoefficientMerge.fastMerge block014_data_flat048 block014_data_flat049) := by decide +kernel
theorem block014_data_flat050_original : block014_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (526699029124224 : Int) atom0954Coded) (CoefficientMerge.scale (493080024628224 : Int) atom0955Coded)) := by
  rw [block014_data_flat050_step, block014_data_flat048_original, block014_data_flat049_original]
def block014_data_flat051 : CoefficientMerge.Poly := [(nat_lit 1455, Int.ofNat (nat_lit 474248026727424))]
theorem block014_data_flat051_step : block014_data_flat051 = (CoefficientMerge.scale (474248026727424 : Int) atom0956Coded) := by decide +kernel
theorem block014_data_flat051_original : block014_data_flat051 = (CoefficientMerge.scale (474248026727424 : Int) atom0956Coded) := by
  rw [block014_data_flat051_step]
def block014_data_flat052 : CoefficientMerge.Poly := [(nat_lit 1456, Int.ofNat (nat_lit 443593518580224))]
theorem block014_data_flat052_step : block014_data_flat052 = (CoefficientMerge.scale (443593518580224 : Int) atom0957Coded) := by decide +kernel
theorem block014_data_flat052_original : block014_data_flat052 = (CoefficientMerge.scale (443593518580224 : Int) atom0957Coded) := by
  rw [block014_data_flat052_step]
def block014_data_flat053 : CoefficientMerge.Poly := [(nat_lit 1457, Int.ofNat (nat_lit 422871748890624))]
theorem block014_data_flat053_step : block014_data_flat053 = (CoefficientMerge.scale (422871748890624 : Int) atom0958Coded) := by decide +kernel
theorem block014_data_flat053_original : block014_data_flat053 = (CoefficientMerge.scale (422871748890624 : Int) atom0958Coded) := by
  rw [block014_data_flat053_step]
def block014_data_flat054 : CoefficientMerge.Poly := [(nat_lit 1456, Int.ofNat (nat_lit 443593518580224)), (nat_lit 1457, Int.ofNat (nat_lit 422871748890624))]
theorem block014_data_flat054_step : block014_data_flat054 = (CoefficientMerge.fastMerge block014_data_flat052 block014_data_flat053) := by decide +kernel
theorem block014_data_flat054_original : block014_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (443593518580224 : Int) atom0957Coded) (CoefficientMerge.scale (422871748890624 : Int) atom0958Coded)) := by
  rw [block014_data_flat054_step, block014_data_flat052_original, block014_data_flat053_original]
def block014_data_flat055 : CoefficientMerge.Poly := [(nat_lit 1455, Int.ofNat (nat_lit 474248026727424)), (nat_lit 1456, Int.ofNat (nat_lit 443593518580224)), (nat_lit 1457, Int.ofNat (nat_lit 422871748890624))]
theorem block014_data_flat055_step : block014_data_flat055 = (CoefficientMerge.fastMerge block014_data_flat051 block014_data_flat054) := by decide +kernel
theorem block014_data_flat055_original : block014_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (474248026727424 : Int) atom0956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (443593518580224 : Int) atom0957Coded) (CoefficientMerge.scale (422871748890624 : Int) atom0958Coded))) := by
  rw [block014_data_flat055_step, block014_data_flat051_original, block014_data_flat054_original]
def block014_data_flat056 : CoefficientMerge.Poly := [(nat_lit 1453, Int.ofNat (nat_lit 526699029124224)), (nat_lit 1454, Int.ofNat (nat_lit 493080024628224)), (nat_lit 1455, Int.ofNat (nat_lit 474248026727424)), (nat_lit 1456, Int.ofNat (nat_lit 443593518580224)), (nat_lit 1457, Int.ofNat (nat_lit 422871748890624))]
theorem block014_data_flat056_step : block014_data_flat056 = (CoefficientMerge.fastMerge block014_data_flat050 block014_data_flat055) := by decide +kernel
theorem block014_data_flat056_original : block014_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (526699029124224 : Int) atom0954Coded) (CoefficientMerge.scale (493080024628224 : Int) atom0955Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (474248026727424 : Int) atom0956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (443593518580224 : Int) atom0957Coded) (CoefficientMerge.scale (422871748890624 : Int) atom0958Coded)))) := by
  rw [block014_data_flat056_step, block014_data_flat050_original, block014_data_flat055_original]
def block014_data_flat057 : CoefficientMerge.Poly := [(nat_lit 1436, Int.ofNat (nat_lit 444055027065408)), (nat_lit 1437, Int.ofNat (nat_lit 410230735782912)), (nat_lit 1438, Int.ofNat (nat_lit 452841657269760)), (nat_lit 1439, Int.ofNat (nat_lit 528185964734208)), (nat_lit 1452, Int.ofNat (nat_lit 284228831677824)), (nat_lit 1453, Int.ofNat (nat_lit 526699029124224)), (nat_lit 1454, Int.ofNat (nat_lit 493080024628224)), (nat_lit 1455, Int.ofNat (nat_lit 474248026727424)), (nat_lit 1456, Int.ofNat (nat_lit 443593518580224)), (nat_lit 1457, Int.ofNat (nat_lit 422871748890624))]
theorem block014_data_flat057_step : block014_data_flat057 = (CoefficientMerge.fastMerge block014_data_flat047 block014_data_flat056) := by decide +kernel
theorem block014_data_flat057_original : block014_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (444055027065408 : Int) atom0949Coded) (CoefficientMerge.scale (410230735782912 : Int) atom0950Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (452841657269760 : Int) atom0951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (528185964734208 : Int) atom0952Coded) (CoefficientMerge.scale (284228831677824 : Int) atom0953Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (526699029124224 : Int) atom0954Coded) (CoefficientMerge.scale (493080024628224 : Int) atom0955Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (474248026727424 : Int) atom0956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (443593518580224 : Int) atom0957Coded) (CoefficientMerge.scale (422871748890624 : Int) atom0958Coded))))) := by
  rw [block014_data_flat057_step, block014_data_flat047_original, block014_data_flat056_original]
def block014_data_flat058 : CoefficientMerge.Poly := [(nat_lit 1458, Int.ofNat (nat_lit 484590100376448))]
theorem block014_data_flat058_step : block014_data_flat058 = (CoefficientMerge.scale (484590100376448 : Int) atom0959Coded) := by decide +kernel
theorem block014_data_flat058_original : block014_data_flat058 = (CoefficientMerge.scale (484590100376448 : Int) atom0959Coded) := by
  rw [block014_data_flat058_step]
def block014_data_flat059 : CoefficientMerge.Poly := [(nat_lit 1459, Int.ofNat (nat_lit 377389276323840))]
theorem block014_data_flat059_step : block014_data_flat059 = (CoefficientMerge.scale (377389276323840 : Int) atom0960Coded) := by decide +kernel
theorem block014_data_flat059_original : block014_data_flat059 = (CoefficientMerge.scale (377389276323840 : Int) atom0960Coded) := by
  rw [block014_data_flat059_step]
def block014_data_flat060 : CoefficientMerge.Poly := [(nat_lit 1458, Int.ofNat (nat_lit 484590100376448)), (nat_lit 1459, Int.ofNat (nat_lit 377389276323840))]
theorem block014_data_flat060_step : block014_data_flat060 = (CoefficientMerge.fastMerge block014_data_flat058 block014_data_flat059) := by decide +kernel
theorem block014_data_flat060_original : block014_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (484590100376448 : Int) atom0959Coded) (CoefficientMerge.scale (377389276323840 : Int) atom0960Coded)) := by
  rw [block014_data_flat060_step, block014_data_flat058_original, block014_data_flat059_original]
def block014_data_flat061 : CoefficientMerge.Poly := [(nat_lit 1460, Int.ofNat (nat_lit 521076290917248))]
theorem block014_data_flat061_step : block014_data_flat061 = (CoefficientMerge.scale (521076290917248 : Int) atom0961Coded) := by decide +kernel
theorem block014_data_flat061_original : block014_data_flat061 = (CoefficientMerge.scale (521076290917248 : Int) atom0961Coded) := by
  rw [block014_data_flat061_step]
def block014_data_flat062 : CoefficientMerge.Poly := [(nat_lit 1461, Int.ofNat (nat_lit 409448281347072))]
theorem block014_data_flat062_step : block014_data_flat062 = (CoefficientMerge.scale (409448281347072 : Int) atom0962Coded) := by decide +kernel
theorem block014_data_flat062_original : block014_data_flat062 = (CoefficientMerge.scale (409448281347072 : Int) atom0962Coded) := by
  rw [block014_data_flat062_step]
def block014_data_flat063 : CoefficientMerge.Poly := [(nat_lit 1462, Int.ofNat (nat_lit 433641756303360))]
theorem block014_data_flat063_step : block014_data_flat063 = (CoefficientMerge.scale (433641756303360 : Int) atom0963Coded) := by decide +kernel
theorem block014_data_flat063_original : block014_data_flat063 = (CoefficientMerge.scale (433641756303360 : Int) atom0963Coded) := by
  rw [block014_data_flat063_step]
def block014_data_flat064 : CoefficientMerge.Poly := [(nat_lit 1461, Int.ofNat (nat_lit 409448281347072)), (nat_lit 1462, Int.ofNat (nat_lit 433641756303360))]
theorem block014_data_flat064_step : block014_data_flat064 = (CoefficientMerge.fastMerge block014_data_flat062 block014_data_flat063) := by decide +kernel
theorem block014_data_flat064_original : block014_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (409448281347072 : Int) atom0962Coded) (CoefficientMerge.scale (433641756303360 : Int) atom0963Coded)) := by
  rw [block014_data_flat064_step, block014_data_flat062_original, block014_data_flat063_original]
def block014_data_flat065 : CoefficientMerge.Poly := [(nat_lit 1460, Int.ofNat (nat_lit 521076290917248)), (nat_lit 1461, Int.ofNat (nat_lit 409448281347072)), (nat_lit 1462, Int.ofNat (nat_lit 433641756303360))]
theorem block014_data_flat065_step : block014_data_flat065 = (CoefficientMerge.fastMerge block014_data_flat061 block014_data_flat064) := by decide +kernel
theorem block014_data_flat065_original : block014_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (521076290917248 : Int) atom0961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (409448281347072 : Int) atom0962Coded) (CoefficientMerge.scale (433641756303360 : Int) atom0963Coded))) := by
  rw [block014_data_flat065_step, block014_data_flat061_original, block014_data_flat064_original]
def block014_data_flat066 : CoefficientMerge.Poly := [(nat_lit 1458, Int.ofNat (nat_lit 484590100376448)), (nat_lit 1459, Int.ofNat (nat_lit 377389276323840)), (nat_lit 1460, Int.ofNat (nat_lit 521076290917248)), (nat_lit 1461, Int.ofNat (nat_lit 409448281347072)), (nat_lit 1462, Int.ofNat (nat_lit 433641756303360))]
theorem block014_data_flat066_step : block014_data_flat066 = (CoefficientMerge.fastMerge block014_data_flat060 block014_data_flat065) := by decide +kernel
theorem block014_data_flat066_original : block014_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (484590100376448 : Int) atom0959Coded) (CoefficientMerge.scale (377389276323840 : Int) atom0960Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (521076290917248 : Int) atom0961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (409448281347072 : Int) atom0962Coded) (CoefficientMerge.scale (433641756303360 : Int) atom0963Coded)))) := by
  rw [block014_data_flat066_step, block014_data_flat060_original, block014_data_flat065_original]
def block014_data_flat067 : CoefficientMerge.Poly := [(nat_lit 1463, Int.ofNat (nat_lit 490568617237248))]
theorem block014_data_flat067_step : block014_data_flat067 = (CoefficientMerge.scale (490568617237248 : Int) atom0964Coded) := by decide +kernel
theorem block014_data_flat067_original : block014_data_flat067 = (CoefficientMerge.scale (490568617237248 : Int) atom0964Coded) := by
  rw [block014_data_flat067_step]
def block014_data_flat068 : CoefficientMerge.Poly := [(nat_lit 1477, Int.ofNat (nat_lit 289736398828800))]
theorem block014_data_flat068_step : block014_data_flat068 = (CoefficientMerge.scale (289736398828800 : Int) atom0965Coded) := by decide +kernel
theorem block014_data_flat068_original : block014_data_flat068 = (CoefficientMerge.scale (289736398828800 : Int) atom0965Coded) := by
  rw [block014_data_flat068_step]
def block014_data_flat069 : CoefficientMerge.Poly := [(nat_lit 1463, Int.ofNat (nat_lit 490568617237248)), (nat_lit 1477, Int.ofNat (nat_lit 289736398828800))]
theorem block014_data_flat069_step : block014_data_flat069 = (CoefficientMerge.fastMerge block014_data_flat067 block014_data_flat068) := by decide +kernel
theorem block014_data_flat069_original : block014_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (490568617237248 : Int) atom0964Coded) (CoefficientMerge.scale (289736398828800 : Int) atom0965Coded)) := by
  rw [block014_data_flat069_step, block014_data_flat067_original, block014_data_flat068_original]
def block014_data_flat070 : CoefficientMerge.Poly := [(nat_lit 1478, Int.ofNat (nat_lit 526404059596800))]
theorem block014_data_flat070_step : block014_data_flat070 = (CoefficientMerge.scale (526404059596800 : Int) atom0966Coded) := by decide +kernel
theorem block014_data_flat070_original : block014_data_flat070 = (CoefficientMerge.scale (526404059596800 : Int) atom0966Coded) := by
  rw [block014_data_flat070_step]
def block014_data_flat071 : CoefficientMerge.Poly := [(nat_lit 1479, Int.ofNat (nat_lit 497366134272000))]
theorem block014_data_flat071_step : block014_data_flat071 = (CoefficientMerge.scale (497366134272000 : Int) atom0967Coded) := by decide +kernel
theorem block014_data_flat071_original : block014_data_flat071 = (CoefficientMerge.scale (497366134272000 : Int) atom0967Coded) := by
  rw [block014_data_flat071_step]
def block014_data_flat072 : CoefficientMerge.Poly := [(nat_lit 1480, Int.ofNat (nat_lit 459588739276800))]
theorem block014_data_flat072_step : block014_data_flat072 = (CoefficientMerge.scale (459588739276800 : Int) atom0968Coded) := by decide +kernel
theorem block014_data_flat072_original : block014_data_flat072 = (CoefficientMerge.scale (459588739276800 : Int) atom0968Coded) := by
  rw [block014_data_flat072_step]
def block014_data_flat073 : CoefficientMerge.Poly := [(nat_lit 1479, Int.ofNat (nat_lit 497366134272000)), (nat_lit 1480, Int.ofNat (nat_lit 459588739276800))]
theorem block014_data_flat073_step : block014_data_flat073 = (CoefficientMerge.fastMerge block014_data_flat071 block014_data_flat072) := by decide +kernel
theorem block014_data_flat073_original : block014_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (497366134272000 : Int) atom0967Coded) (CoefficientMerge.scale (459588739276800 : Int) atom0968Coded)) := by
  rw [block014_data_flat073_step, block014_data_flat071_original, block014_data_flat072_original]
def block014_data_flat074 : CoefficientMerge.Poly := [(nat_lit 1478, Int.ofNat (nat_lit 526404059596800)), (nat_lit 1479, Int.ofNat (nat_lit 497366134272000)), (nat_lit 1480, Int.ofNat (nat_lit 459588739276800))]
theorem block014_data_flat074_step : block014_data_flat074 = (CoefficientMerge.fastMerge block014_data_flat070 block014_data_flat073) := by decide +kernel
theorem block014_data_flat074_original : block014_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (526404059596800 : Int) atom0966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497366134272000 : Int) atom0967Coded) (CoefficientMerge.scale (459588739276800 : Int) atom0968Coded))) := by
  rw [block014_data_flat074_step, block014_data_flat070_original, block014_data_flat073_original]
def block014_data_flat075 : CoefficientMerge.Poly := [(nat_lit 1463, Int.ofNat (nat_lit 490568617237248)), (nat_lit 1477, Int.ofNat (nat_lit 289736398828800)), (nat_lit 1478, Int.ofNat (nat_lit 526404059596800)), (nat_lit 1479, Int.ofNat (nat_lit 497366134272000)), (nat_lit 1480, Int.ofNat (nat_lit 459588739276800))]
theorem block014_data_flat075_step : block014_data_flat075 = (CoefficientMerge.fastMerge block014_data_flat069 block014_data_flat074) := by decide +kernel
theorem block014_data_flat075_original : block014_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (490568617237248 : Int) atom0964Coded) (CoefficientMerge.scale (289736398828800 : Int) atom0965Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (526404059596800 : Int) atom0966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497366134272000 : Int) atom0967Coded) (CoefficientMerge.scale (459588739276800 : Int) atom0968Coded)))) := by
  rw [block014_data_flat075_step, block014_data_flat069_original, block014_data_flat074_original]
def block014_data_flat076 : CoefficientMerge.Poly := [(nat_lit 1458, Int.ofNat (nat_lit 484590100376448)), (nat_lit 1459, Int.ofNat (nat_lit 377389276323840)), (nat_lit 1460, Int.ofNat (nat_lit 521076290917248)), (nat_lit 1461, Int.ofNat (nat_lit 409448281347072)), (nat_lit 1462, Int.ofNat (nat_lit 433641756303360)), (nat_lit 1463, Int.ofNat (nat_lit 490568617237248)), (nat_lit 1477, Int.ofNat (nat_lit 289736398828800)), (nat_lit 1478, Int.ofNat (nat_lit 526404059596800)), (nat_lit 1479, Int.ofNat (nat_lit 497366134272000)), (nat_lit 1480, Int.ofNat (nat_lit 459588739276800))]
theorem block014_data_flat076_step : block014_data_flat076 = (CoefficientMerge.fastMerge block014_data_flat066 block014_data_flat075) := by decide +kernel
theorem block014_data_flat076_original : block014_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (484590100376448 : Int) atom0959Coded) (CoefficientMerge.scale (377389276323840 : Int) atom0960Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (521076290917248 : Int) atom0961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (409448281347072 : Int) atom0962Coded) (CoefficientMerge.scale (433641756303360 : Int) atom0963Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (490568617237248 : Int) atom0964Coded) (CoefficientMerge.scale (289736398828800 : Int) atom0965Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (526404059596800 : Int) atom0966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497366134272000 : Int) atom0967Coded) (CoefficientMerge.scale (459588739276800 : Int) atom0968Coded))))) := by
  rw [block014_data_flat076_step, block014_data_flat066_original, block014_data_flat075_original]
def block014_data_flat077 : CoefficientMerge.Poly := [(nat_lit 1436, Int.ofNat (nat_lit 444055027065408)), (nat_lit 1437, Int.ofNat (nat_lit 410230735782912)), (nat_lit 1438, Int.ofNat (nat_lit 452841657269760)), (nat_lit 1439, Int.ofNat (nat_lit 528185964734208)), (nat_lit 1452, Int.ofNat (nat_lit 284228831677824)), (nat_lit 1453, Int.ofNat (nat_lit 526699029124224)), (nat_lit 1454, Int.ofNat (nat_lit 493080024628224)), (nat_lit 1455, Int.ofNat (nat_lit 474248026727424)), (nat_lit 1456, Int.ofNat (nat_lit 443593518580224)), (nat_lit 1457, Int.ofNat (nat_lit 422871748890624)), (nat_lit 1458, Int.ofNat (nat_lit 484590100376448)), (nat_lit 1459, Int.ofNat (nat_lit 377389276323840)), (nat_lit 1460, Int.ofNat (nat_lit 521076290917248)), (nat_lit 1461, Int.ofNat (nat_lit 409448281347072)), (nat_lit 1462, Int.ofNat (nat_lit 433641756303360)), (nat_lit 1463, Int.ofNat (nat_lit 490568617237248)), (nat_lit 1477, Int.ofNat (nat_lit 289736398828800)), (nat_lit 1478, Int.ofNat (nat_lit 526404059596800)), (nat_lit 1479, Int.ofNat (nat_lit 497366134272000)), (nat_lit 1480, Int.ofNat (nat_lit 459588739276800))]
theorem block014_data_flat077_step : block014_data_flat077 = (CoefficientMerge.fastMerge block014_data_flat057 block014_data_flat076) := by decide +kernel
theorem block014_data_flat077_original : block014_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (444055027065408 : Int) atom0949Coded) (CoefficientMerge.scale (410230735782912 : Int) atom0950Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (452841657269760 : Int) atom0951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (528185964734208 : Int) atom0952Coded) (CoefficientMerge.scale (284228831677824 : Int) atom0953Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (526699029124224 : Int) atom0954Coded) (CoefficientMerge.scale (493080024628224 : Int) atom0955Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (474248026727424 : Int) atom0956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (443593518580224 : Int) atom0957Coded) (CoefficientMerge.scale (422871748890624 : Int) atom0958Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (484590100376448 : Int) atom0959Coded) (CoefficientMerge.scale (377389276323840 : Int) atom0960Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (521076290917248 : Int) atom0961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (409448281347072 : Int) atom0962Coded) (CoefficientMerge.scale (433641756303360 : Int) atom0963Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (490568617237248 : Int) atom0964Coded) (CoefficientMerge.scale (289736398828800 : Int) atom0965Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (526404059596800 : Int) atom0966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497366134272000 : Int) atom0967Coded) (CoefficientMerge.scale (459588739276800 : Int) atom0968Coded)))))) := by
  rw [block014_data_flat077_step, block014_data_flat057_original, block014_data_flat076_original]
def block014_data_flat078 : CoefficientMerge.Poly := [(nat_lit 1405, Int.ofNat (nat_lit 403961087933568)), (nat_lit 1406, Int.ofNat (nat_lit 381526078906368)), (nat_lit 1407, Int.ofNat (nat_lit 373878076474368)), (nat_lit 1408, Int.ofNat (nat_lit 354407563795968)), (nat_lit 1409, Int.ofNat (nat_lit 344869789575168)), (nat_lit 1410, Int.ofNat (nat_lit 379974615939072)), (nat_lit 1411, Int.ofNat (nat_lit 329477914529280)), (nat_lit 1412, Int.ofNat (nat_lit 419823011570688)), (nat_lit 1413, Int.ofNat (nat_lit 399350123656704)), (nat_lit 1414, Int.ofNat (nat_lit 445024402859520)), (nat_lit 1415, Int.ofNat (nat_lit 523432068039936)), (nat_lit 1427, Int.ofNat (nat_lit 247082976765504)), (nat_lit 1428, Int.ofNat (nat_lit 484045607060928)), (nat_lit 1429, Int.ofNat (nat_lit 457120118911104)), (nat_lit 1430, Int.ofNat (nat_lit 426520367944704)), (nat_lit 1431, Int.ofNat (nat_lit 410707623573504)), (nat_lit 1432, Int.ofNat (nat_lit 386155409531904)), (nat_lit 1433, Int.ofNat (nat_lit 371535933947904)), (nat_lit 1434, Int.ofNat (nat_lit 413692392979008)), (nat_lit 1435, Int.ofNat (nat_lit 347494413911040)), (nat_lit 1436, Int.ofNat (nat_lit 444055027065408)), (nat_lit 1437, Int.ofNat (nat_lit 410230735782912)), (nat_lit 1438, Int.ofNat (nat_lit 452841657269760)), (nat_lit 1439, Int.ofNat (nat_lit 528185964734208)), (nat_lit 1452, Int.ofNat (nat_lit 284228831677824)), (nat_lit 1453, Int.ofNat (nat_lit 526699029124224)), (nat_lit 1454, Int.ofNat (nat_lit 493080024628224)), (nat_lit 1455, Int.ofNat (nat_lit 474248026727424)), (nat_lit 1456, Int.ofNat (nat_lit 443593518580224)), (nat_lit 1457, Int.ofNat (nat_lit 422871748890624)), (nat_lit 1458, Int.ofNat (nat_lit 484590100376448)), (nat_lit 1459, Int.ofNat (nat_lit 377389276323840)), (nat_lit 1460, Int.ofNat (nat_lit 521076290917248)), (nat_lit 1461, Int.ofNat (nat_lit 409448281347072)), (nat_lit 1462, Int.ofNat (nat_lit 433641756303360)), (nat_lit 1463, Int.ofNat (nat_lit 490568617237248)), (nat_lit 1477, Int.ofNat (nat_lit 289736398828800)), (nat_lit 1478, Int.ofNat (nat_lit 526404059596800)), (nat_lit 1479, Int.ofNat (nat_lit 497366134272000)), (nat_lit 1480, Int.ofNat (nat_lit 459588739276800))]
theorem block014_data_flat078_step : block014_data_flat078 = (CoefficientMerge.fastMerge block014_data_flat038 block014_data_flat077) := by decide +kernel
theorem block014_data_flat078_original : block014_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (403961087933568 : Int) atom0929Coded) (CoefficientMerge.scale (381526078906368 : Int) atom0930Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (373878076474368 : Int) atom0931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (354407563795968 : Int) atom0932Coded) (CoefficientMerge.scale (344869789575168 : Int) atom0933Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (379974615939072 : Int) atom0934Coded) (CoefficientMerge.scale (329477914529280 : Int) atom0935Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (419823011570688 : Int) atom0936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (399350123656704 : Int) atom0937Coded) (CoefficientMerge.scale (445024402859520 : Int) atom0938Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (523432068039936 : Int) atom0939Coded) (CoefficientMerge.scale (247082976765504 : Int) atom0940Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (484045607060928 : Int) atom0941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457120118911104 : Int) atom0942Coded) (CoefficientMerge.scale (426520367944704 : Int) atom0943Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (410707623573504 : Int) atom0944Coded) (CoefficientMerge.scale (386155409531904 : Int) atom0945Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (371535933947904 : Int) atom0946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413692392979008 : Int) atom0947Coded) (CoefficientMerge.scale (347494413911040 : Int) atom0948Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (444055027065408 : Int) atom0949Coded) (CoefficientMerge.scale (410230735782912 : Int) atom0950Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (452841657269760 : Int) atom0951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (528185964734208 : Int) atom0952Coded) (CoefficientMerge.scale (284228831677824 : Int) atom0953Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (526699029124224 : Int) atom0954Coded) (CoefficientMerge.scale (493080024628224 : Int) atom0955Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (474248026727424 : Int) atom0956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (443593518580224 : Int) atom0957Coded) (CoefficientMerge.scale (422871748890624 : Int) atom0958Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (484590100376448 : Int) atom0959Coded) (CoefficientMerge.scale (377389276323840 : Int) atom0960Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (521076290917248 : Int) atom0961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (409448281347072 : Int) atom0962Coded) (CoefficientMerge.scale (433641756303360 : Int) atom0963Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (490568617237248 : Int) atom0964Coded) (CoefficientMerge.scale (289736398828800 : Int) atom0965Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (526404059596800 : Int) atom0966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497366134272000 : Int) atom0967Coded) (CoefficientMerge.scale (459588739276800 : Int) atom0968Coded))))))) := by
  rw [block014_data_flat078_step, block014_data_flat038_original, block014_data_flat077_original]
def block014_data_flat079 : CoefficientMerge.Poly := [(nat_lit 1481, Int.ofNat (nat_lit 431744082739200))]
theorem block014_data_flat079_step : block014_data_flat079 = (CoefficientMerge.scale (431744082739200 : Int) atom0969Coded) := by decide +kernel
theorem block014_data_flat079_original : block014_data_flat079 = (CoefficientMerge.scale (431744082739200 : Int) atom0969Coded) := by
  rw [block014_data_flat079_step]
def block014_data_flat080 : CoefficientMerge.Poly := [(nat_lit 1482, Int.ofNat (nat_lit 482321582265600))]
theorem block014_data_flat080_step : block014_data_flat080 = (CoefficientMerge.scale (482321582265600 : Int) atom0970Coded) := by decide +kernel
theorem block014_data_flat080_original : block014_data_flat080 = (CoefficientMerge.scale (482321582265600 : Int) atom0970Coded) := by
  rw [block014_data_flat080_step]
def block014_data_flat081 : CoefficientMerge.Poly := [(nat_lit 1481, Int.ofNat (nat_lit 431744082739200)), (nat_lit 1482, Int.ofNat (nat_lit 482321582265600))]
theorem block014_data_flat081_step : block014_data_flat081 = (CoefficientMerge.fastMerge block014_data_flat079 block014_data_flat080) := by decide +kernel
theorem block014_data_flat081_original : block014_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (431744082739200 : Int) atom0969Coded) (CoefficientMerge.scale (482321582265600 : Int) atom0970Coded)) := by
  rw [block014_data_flat081_step, block014_data_flat079_original, block014_data_flat080_original]
def block014_data_flat082 : CoefficientMerge.Poly := [(nat_lit 1483, Int.ofNat (nat_lit 377204281977600))]
theorem block014_data_flat082_step : block014_data_flat082 = (CoefficientMerge.scale (377204281977600 : Int) atom0971Coded) := by decide +kernel
theorem block014_data_flat082_original : block014_data_flat082 = (CoefficientMerge.scale (377204281977600 : Int) atom0971Coded) := by
  rw [block014_data_flat082_step]
def block014_data_flat083 : CoefficientMerge.Poly := [(nat_lit 1484, Int.ofNat (nat_lit 524931329260800))]
theorem block014_data_flat083_step : block014_data_flat083 = (CoefficientMerge.scale (524931329260800 : Int) atom0972Coded) := by decide +kernel
theorem block014_data_flat083_original : block014_data_flat083 = (CoefficientMerge.scale (524931329260800 : Int) atom0972Coded) := by
  rw [block014_data_flat083_step]
def block014_data_flat084 : CoefficientMerge.Poly := [(nat_lit 1485, Int.ofNat (nat_lit 405394404307200))]
theorem block014_data_flat084_step : block014_data_flat084 = (CoefficientMerge.scale (405394404307200 : Int) atom0973Coded) := by decide +kernel
theorem block014_data_flat084_original : block014_data_flat084 = (CoefficientMerge.scale (405394404307200 : Int) atom0973Coded) := by
  rw [block014_data_flat084_step]
def block014_data_flat085 : CoefficientMerge.Poly := [(nat_lit 1484, Int.ofNat (nat_lit 524931329260800)), (nat_lit 1485, Int.ofNat (nat_lit 405394404307200))]
theorem block014_data_flat085_step : block014_data_flat085 = (CoefficientMerge.fastMerge block014_data_flat083 block014_data_flat084) := by decide +kernel
theorem block014_data_flat085_original : block014_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (524931329260800 : Int) atom0972Coded) (CoefficientMerge.scale (405394404307200 : Int) atom0973Coded)) := by
  rw [block014_data_flat085_step, block014_data_flat083_original, block014_data_flat084_original]
def block014_data_flat086 : CoefficientMerge.Poly := [(nat_lit 1483, Int.ofNat (nat_lit 377204281977600)), (nat_lit 1484, Int.ofNat (nat_lit 524931329260800)), (nat_lit 1485, Int.ofNat (nat_lit 405394404307200))]
theorem block014_data_flat086_step : block014_data_flat086 = (CoefficientMerge.fastMerge block014_data_flat082 block014_data_flat085) := by decide +kernel
theorem block014_data_flat086_original : block014_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (377204281977600 : Int) atom0971Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (524931329260800 : Int) atom0972Coded) (CoefficientMerge.scale (405394404307200 : Int) atom0973Coded))) := by
  rw [block014_data_flat086_step, block014_data_flat082_original, block014_data_flat085_original]
def block014_data_flat087 : CoefficientMerge.Poly := [(nat_lit 1481, Int.ofNat (nat_lit 431744082739200)), (nat_lit 1482, Int.ofNat (nat_lit 482321582265600)), (nat_lit 1483, Int.ofNat (nat_lit 377204281977600)), (nat_lit 1484, Int.ofNat (nat_lit 524931329260800)), (nat_lit 1485, Int.ofNat (nat_lit 405394404307200))]
theorem block014_data_flat087_step : block014_data_flat087 = (CoefficientMerge.fastMerge block014_data_flat081 block014_data_flat086) := by decide +kernel
theorem block014_data_flat087_original : block014_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (431744082739200 : Int) atom0969Coded) (CoefficientMerge.scale (482321582265600 : Int) atom0970Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377204281977600 : Int) atom0971Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (524931329260800 : Int) atom0972Coded) (CoefficientMerge.scale (405394404307200 : Int) atom0973Coded)))) := by
  rw [block014_data_flat087_step, block014_data_flat081_original, block014_data_flat086_original]
def block014_data_flat088 : CoefficientMerge.Poly := [(nat_lit 1486, Int.ofNat (nat_lit 429382919750400))]
theorem block014_data_flat088_step : block014_data_flat088 = (CoefficientMerge.scale (429382919750400 : Int) atom0974Coded) := by decide +kernel
theorem block014_data_flat088_original : block014_data_flat088 = (CoefficientMerge.scale (429382919750400 : Int) atom0974Coded) := by
  rw [block014_data_flat088_step]
def block014_data_flat089 : CoefficientMerge.Poly := [(nat_lit 1487, Int.ofNat (nat_lit 486104821171200))]
theorem block014_data_flat089_step : block014_data_flat089 = (CoefficientMerge.scale (486104821171200 : Int) atom0975Coded) := by decide +kernel
theorem block014_data_flat089_original : block014_data_flat089 = (CoefficientMerge.scale (486104821171200 : Int) atom0975Coded) := by
  rw [block014_data_flat089_step]
def block014_data_flat090 : CoefficientMerge.Poly := [(nat_lit 1486, Int.ofNat (nat_lit 429382919750400)), (nat_lit 1487, Int.ofNat (nat_lit 486104821171200))]
theorem block014_data_flat090_step : block014_data_flat090 = (CoefficientMerge.fastMerge block014_data_flat088 block014_data_flat089) := by decide +kernel
theorem block014_data_flat090_original : block014_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (429382919750400 : Int) atom0974Coded) (CoefficientMerge.scale (486104821171200 : Int) atom0975Coded)) := by
  rw [block014_data_flat090_step, block014_data_flat088_original, block014_data_flat089_original]
def block014_data_flat091 : CoefficientMerge.Poly := [(nat_lit 1502, Int.ofNat (nat_lit 283933862150400))]
theorem block014_data_flat091_step : block014_data_flat091 = (CoefficientMerge.scale (283933862150400 : Int) atom0976Coded) := by decide +kernel
theorem block014_data_flat091_original : block014_data_flat091 = (CoefficientMerge.scale (283933862150400 : Int) atom0976Coded) := by
  rw [block014_data_flat091_step]
def block014_data_flat092 : CoefficientMerge.Poly := [(nat_lit 1503, Int.ofNat (nat_lit 525551462150400))]
theorem block014_data_flat092_step : block014_data_flat092 = (CoefficientMerge.scale (525551462150400 : Int) atom0977Coded) := by decide +kernel
theorem block014_data_flat092_original : block014_data_flat092 = (CoefficientMerge.scale (525551462150400 : Int) atom0977Coded) := by
  rw [block014_data_flat092_step]
def block014_data_flat093 : CoefficientMerge.Poly := [(nat_lit 1504, Int.ofNat (nat_lit 479630587564800))]
theorem block014_data_flat093_step : block014_data_flat093 = (CoefficientMerge.scale (479630587564800 : Int) atom0978Coded) := by decide +kernel
theorem block014_data_flat093_original : block014_data_flat093 = (CoefficientMerge.scale (479630587564800 : Int) atom0978Coded) := by
  rw [block014_data_flat093_step]
def block014_data_flat094 : CoefficientMerge.Poly := [(nat_lit 1503, Int.ofNat (nat_lit 525551462150400)), (nat_lit 1504, Int.ofNat (nat_lit 479630587564800))]
theorem block014_data_flat094_step : block014_data_flat094 = (CoefficientMerge.fastMerge block014_data_flat092 block014_data_flat093) := by decide +kernel
theorem block014_data_flat094_original : block014_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (525551462150400 : Int) atom0977Coded) (CoefficientMerge.scale (479630587564800 : Int) atom0978Coded)) := by
  rw [block014_data_flat094_step, block014_data_flat092_original, block014_data_flat093_original]
def block014_data_flat095 : CoefficientMerge.Poly := [(nat_lit 1502, Int.ofNat (nat_lit 283933862150400)), (nat_lit 1503, Int.ofNat (nat_lit 525551462150400)), (nat_lit 1504, Int.ofNat (nat_lit 479630587564800))]
theorem block014_data_flat095_step : block014_data_flat095 = (CoefficientMerge.fastMerge block014_data_flat091 block014_data_flat094) := by decide +kernel
theorem block014_data_flat095_original : block014_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (283933862150400 : Int) atom0976Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (525551462150400 : Int) atom0977Coded) (CoefficientMerge.scale (479630587564800 : Int) atom0978Coded))) := by
  rw [block014_data_flat095_step, block014_data_flat091_original, block014_data_flat094_original]
def block014_data_flat096 : CoefficientMerge.Poly := [(nat_lit 1486, Int.ofNat (nat_lit 429382919750400)), (nat_lit 1487, Int.ofNat (nat_lit 486104821171200)), (nat_lit 1502, Int.ofNat (nat_lit 283933862150400)), (nat_lit 1503, Int.ofNat (nat_lit 525551462150400)), (nat_lit 1504, Int.ofNat (nat_lit 479630587564800))]
theorem block014_data_flat096_step : block014_data_flat096 = (CoefficientMerge.fastMerge block014_data_flat090 block014_data_flat095) := by decide +kernel
theorem block014_data_flat096_original : block014_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (429382919750400 : Int) atom0974Coded) (CoefficientMerge.scale (486104821171200 : Int) atom0975Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283933862150400 : Int) atom0976Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (525551462150400 : Int) atom0977Coded) (CoefficientMerge.scale (479630587564800 : Int) atom0978Coded)))) := by
  rw [block014_data_flat096_step, block014_data_flat090_original, block014_data_flat095_original]
def block014_data_flat097 : CoefficientMerge.Poly := [(nat_lit 1481, Int.ofNat (nat_lit 431744082739200)), (nat_lit 1482, Int.ofNat (nat_lit 482321582265600)), (nat_lit 1483, Int.ofNat (nat_lit 377204281977600)), (nat_lit 1484, Int.ofNat (nat_lit 524931329260800)), (nat_lit 1485, Int.ofNat (nat_lit 405394404307200)), (nat_lit 1486, Int.ofNat (nat_lit 429382919750400)), (nat_lit 1487, Int.ofNat (nat_lit 486104821171200)), (nat_lit 1502, Int.ofNat (nat_lit 283933862150400)), (nat_lit 1503, Int.ofNat (nat_lit 525551462150400)), (nat_lit 1504, Int.ofNat (nat_lit 479630587564800))]
theorem block014_data_flat097_step : block014_data_flat097 = (CoefficientMerge.fastMerge block014_data_flat087 block014_data_flat096) := by decide +kernel
theorem block014_data_flat097_original : block014_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (431744082739200 : Int) atom0969Coded) (CoefficientMerge.scale (482321582265600 : Int) atom0970Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377204281977600 : Int) atom0971Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (524931329260800 : Int) atom0972Coded) (CoefficientMerge.scale (405394404307200 : Int) atom0973Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (429382919750400 : Int) atom0974Coded) (CoefficientMerge.scale (486104821171200 : Int) atom0975Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283933862150400 : Int) atom0976Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (525551462150400 : Int) atom0977Coded) (CoefficientMerge.scale (479630587564800 : Int) atom0978Coded))))) := by
  rw [block014_data_flat097_step, block014_data_flat087_original, block014_data_flat096_original]
def block014_data_flat098 : CoefficientMerge.Poly := [(nat_lit 1505, Int.ofNat (nat_lit 443642451436800))]
theorem block014_data_flat098_step : block014_data_flat098 = (CoefficientMerge.scale (443642451436800 : Int) atom0979Coded) := by decide +kernel
theorem block014_data_flat098_original : block014_data_flat098 = (CoefficientMerge.scale (443642451436800 : Int) atom0979Coded) := by
  rw [block014_data_flat098_step]
def block014_data_flat099 : CoefficientMerge.Poly := [(nat_lit 1506, Int.ofNat (nat_lit 472704538521600))]
theorem block014_data_flat099_step : block014_data_flat099 = (CoefficientMerge.scale (472704538521600 : Int) atom0980Coded) := by decide +kernel
theorem block014_data_flat099_original : block014_data_flat099 = (CoefficientMerge.scale (472704538521600 : Int) atom0980Coded) := by
  rw [block014_data_flat099_step]
def block014_data_flat100 : CoefficientMerge.Poly := [(nat_lit 1505, Int.ofNat (nat_lit 443642451436800)), (nat_lit 1506, Int.ofNat (nat_lit 472704538521600))]
theorem block014_data_flat100_step : block014_data_flat100 = (CoefficientMerge.fastMerge block014_data_flat098 block014_data_flat099) := by decide +kernel
theorem block014_data_flat100_original : block014_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (443642451436800 : Int) atom0979Coded) (CoefficientMerge.scale (472704538521600 : Int) atom0980Coded)) := by
  rw [block014_data_flat100_step, block014_data_flat098_original, block014_data_flat099_original]
def block014_data_flat101 : CoefficientMerge.Poly := [(nat_lit 1507, Int.ofNat (nat_lit 375370378336800))]
theorem block014_data_flat101_step : block014_data_flat101 = (CoefficientMerge.scale (375370378336800 : Int) atom0981Coded) := by decide +kernel
theorem block014_data_flat101_original : block014_data_flat101 = (CoefficientMerge.scale (375370378336800 : Int) atom0981Coded) := by
  rw [block014_data_flat101_step]
def block014_data_flat102 : CoefficientMerge.Poly := [(nat_lit 1508, Int.ofNat (nat_lit 521437841971200))]
theorem block014_data_flat102_step : block014_data_flat102 = (CoefficientMerge.scale (521437841971200 : Int) atom0982Coded) := by decide +kernel
theorem block014_data_flat102_original : block014_data_flat102 = (CoefficientMerge.scale (521437841971200 : Int) atom0982Coded) := by
  rw [block014_data_flat102_step]
def block014_data_flat103 : CoefficientMerge.Poly := [(nat_lit 1509, Int.ofNat (nat_lit 404962695244800))]
theorem block014_data_flat103_step : block014_data_flat103 = (CoefficientMerge.scale (404962695244800 : Int) atom0983Coded) := by decide +kernel
theorem block014_data_flat103_original : block014_data_flat103 = (CoefficientMerge.scale (404962695244800 : Int) atom0983Coded) := by
  rw [block014_data_flat103_step]
def block014_data_flat104 : CoefficientMerge.Poly := [(nat_lit 1508, Int.ofNat (nat_lit 521437841971200)), (nat_lit 1509, Int.ofNat (nat_lit 404962695244800))]
theorem block014_data_flat104_step : block014_data_flat104 = (CoefficientMerge.fastMerge block014_data_flat102 block014_data_flat103) := by decide +kernel
theorem block014_data_flat104_original : block014_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (521437841971200 : Int) atom0982Coded) (CoefficientMerge.scale (404962695244800 : Int) atom0983Coded)) := by
  rw [block014_data_flat104_step, block014_data_flat102_original, block014_data_flat103_original]
def block014_data_flat105 : CoefficientMerge.Poly := [(nat_lit 1507, Int.ofNat (nat_lit 375370378336800)), (nat_lit 1508, Int.ofNat (nat_lit 521437841971200)), (nat_lit 1509, Int.ofNat (nat_lit 404962695244800))]
theorem block014_data_flat105_step : block014_data_flat105 = (CoefficientMerge.fastMerge block014_data_flat101 block014_data_flat104) := by decide +kernel
theorem block014_data_flat105_original : block014_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (375370378336800 : Int) atom0981Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (521437841971200 : Int) atom0982Coded) (CoefficientMerge.scale (404962695244800 : Int) atom0983Coded))) := by
  rw [block014_data_flat105_step, block014_data_flat101_original, block014_data_flat104_original]
def block014_data_flat106 : CoefficientMerge.Poly := [(nat_lit 1505, Int.ofNat (nat_lit 443642451436800)), (nat_lit 1506, Int.ofNat (nat_lit 472704538521600)), (nat_lit 1507, Int.ofNat (nat_lit 375370378336800)), (nat_lit 1508, Int.ofNat (nat_lit 521437841971200)), (nat_lit 1509, Int.ofNat (nat_lit 404962695244800))]
theorem block014_data_flat106_step : block014_data_flat106 = (CoefficientMerge.fastMerge block014_data_flat100 block014_data_flat105) := by decide +kernel
theorem block014_data_flat106_original : block014_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (443642451436800 : Int) atom0979Coded) (CoefficientMerge.scale (472704538521600 : Int) atom0980Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375370378336800 : Int) atom0981Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (521437841971200 : Int) atom0982Coded) (CoefficientMerge.scale (404962695244800 : Int) atom0983Coded)))) := by
  rw [block014_data_flat106_step, block014_data_flat100_original, block014_data_flat105_original]
def block014_data_flat107 : CoefficientMerge.Poly := [(nat_lit 1510, Int.ofNat (nat_lit 411634200146400))]
theorem block014_data_flat107_step : block014_data_flat107 = (CoefficientMerge.scale (411634200146400 : Int) atom0984Coded) := by decide +kernel
theorem block014_data_flat107_original : block014_data_flat107 = (CoefficientMerge.scale (411634200146400 : Int) atom0984Coded) := by
  rw [block014_data_flat107_step]
def block014_data_flat108 : CoefficientMerge.Poly := [(nat_lit 1511, Int.ofNat (nat_lit 463618871100000))]
theorem block014_data_flat108_step : block014_data_flat108 = (CoefficientMerge.scale (463618871100000 : Int) atom0985Coded) := by decide +kernel
theorem block014_data_flat108_original : block014_data_flat108 = (CoefficientMerge.scale (463618871100000 : Int) atom0985Coded) := by
  rw [block014_data_flat108_step]
def block014_data_flat109 : CoefficientMerge.Poly := [(nat_lit 1510, Int.ofNat (nat_lit 411634200146400)), (nat_lit 1511, Int.ofNat (nat_lit 463618871100000))]
theorem block014_data_flat109_step : block014_data_flat109 = (CoefficientMerge.fastMerge block014_data_flat107 block014_data_flat108) := by decide +kernel
theorem block014_data_flat109_original : block014_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (411634200146400 : Int) atom0984Coded) (CoefficientMerge.scale (463618871100000 : Int) atom0985Coded)) := by
  rw [block014_data_flat109_step, block014_data_flat107_original, block014_data_flat108_original]
def block014_data_flat110 : CoefficientMerge.Poly := [(nat_lit 1527, Int.ofNat (nat_lit 291966841958400))]
theorem block014_data_flat110_step : block014_data_flat110 = (CoefficientMerge.scale (291966841958400 : Int) atom0986Coded) := by decide +kernel
theorem block014_data_flat110_original : block014_data_flat110 = (CoefficientMerge.scale (291966841958400 : Int) atom0986Coded) := by
  rw [block014_data_flat110_step]
def block014_data_flat111 : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 515495981952000))]
theorem block014_data_flat111_step : block014_data_flat111 = (CoefficientMerge.scale (515495981952000 : Int) atom0987Coded) := by decide +kernel
theorem block014_data_flat111_original : block014_data_flat111 = (CoefficientMerge.scale (515495981952000 : Int) atom0987Coded) := by
  rw [block014_data_flat111_step]
def block014_data_flat112 : CoefficientMerge.Poly := [(nat_lit 1529, Int.ofNat (nat_lit 470343773491200))]
theorem block014_data_flat112_step : block014_data_flat112 = (CoefficientMerge.scale (470343773491200 : Int) atom0988Coded) := by decide +kernel
theorem block014_data_flat112_original : block014_data_flat112 = (CoefficientMerge.scale (470343773491200 : Int) atom0988Coded) := by
  rw [block014_data_flat112_step]
def block014_data_flat113 : CoefficientMerge.Poly := [(nat_lit 1528, Int.ofNat (nat_lit 515495981952000)), (nat_lit 1529, Int.ofNat (nat_lit 470343773491200))]
theorem block014_data_flat113_step : block014_data_flat113 = (CoefficientMerge.fastMerge block014_data_flat111 block014_data_flat112) := by decide +kernel
theorem block014_data_flat113_original : block014_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (515495981952000 : Int) atom0987Coded) (CoefficientMerge.scale (470343773491200 : Int) atom0988Coded)) := by
  rw [block014_data_flat113_step, block014_data_flat111_original, block014_data_flat112_original]
def block014_data_flat114 : CoefficientMerge.Poly := [(nat_lit 1527, Int.ofNat (nat_lit 291966841958400)), (nat_lit 1528, Int.ofNat (nat_lit 515495981952000)), (nat_lit 1529, Int.ofNat (nat_lit 470343773491200))]
theorem block014_data_flat114_step : block014_data_flat114 = (CoefficientMerge.fastMerge block014_data_flat110 block014_data_flat113) := by decide +kernel
theorem block014_data_flat114_original : block014_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (291966841958400 : Int) atom0986Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (515495981952000 : Int) atom0987Coded) (CoefficientMerge.scale (470343773491200 : Int) atom0988Coded))) := by
  rw [block014_data_flat114_step, block014_data_flat110_original, block014_data_flat113_original]
def block014_data_flat115 : CoefficientMerge.Poly := [(nat_lit 1510, Int.ofNat (nat_lit 411634200146400)), (nat_lit 1511, Int.ofNat (nat_lit 463618871100000)), (nat_lit 1527, Int.ofNat (nat_lit 291966841958400)), (nat_lit 1528, Int.ofNat (nat_lit 515495981952000)), (nat_lit 1529, Int.ofNat (nat_lit 470343773491200))]
theorem block014_data_flat115_step : block014_data_flat115 = (CoefficientMerge.fastMerge block014_data_flat109 block014_data_flat114) := by decide +kernel
theorem block014_data_flat115_original : block014_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (411634200146400 : Int) atom0984Coded) (CoefficientMerge.scale (463618871100000 : Int) atom0985Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (291966841958400 : Int) atom0986Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (515495981952000 : Int) atom0987Coded) (CoefficientMerge.scale (470343773491200 : Int) atom0988Coded)))) := by
  rw [block014_data_flat115_step, block014_data_flat109_original, block014_data_flat114_original]
def block014_data_flat116 : CoefficientMerge.Poly := [(nat_lit 1505, Int.ofNat (nat_lit 443642451436800)), (nat_lit 1506, Int.ofNat (nat_lit 472704538521600)), (nat_lit 1507, Int.ofNat (nat_lit 375370378336800)), (nat_lit 1508, Int.ofNat (nat_lit 521437841971200)), (nat_lit 1509, Int.ofNat (nat_lit 404962695244800)), (nat_lit 1510, Int.ofNat (nat_lit 411634200146400)), (nat_lit 1511, Int.ofNat (nat_lit 463618871100000)), (nat_lit 1527, Int.ofNat (nat_lit 291966841958400)), (nat_lit 1528, Int.ofNat (nat_lit 515495981952000)), (nat_lit 1529, Int.ofNat (nat_lit 470343773491200))]
theorem block014_data_flat116_step : block014_data_flat116 = (CoefficientMerge.fastMerge block014_data_flat106 block014_data_flat115) := by decide +kernel
theorem block014_data_flat116_original : block014_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (443642451436800 : Int) atom0979Coded) (CoefficientMerge.scale (472704538521600 : Int) atom0980Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375370378336800 : Int) atom0981Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (521437841971200 : Int) atom0982Coded) (CoefficientMerge.scale (404962695244800 : Int) atom0983Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (411634200146400 : Int) atom0984Coded) (CoefficientMerge.scale (463618871100000 : Int) atom0985Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (291966841958400 : Int) atom0986Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (515495981952000 : Int) atom0987Coded) (CoefficientMerge.scale (470343773491200 : Int) atom0988Coded))))) := by
  rw [block014_data_flat116_step, block014_data_flat106_original, block014_data_flat115_original]
def block014_data_flat117 : CoefficientMerge.Poly := [(nat_lit 1481, Int.ofNat (nat_lit 431744082739200)), (nat_lit 1482, Int.ofNat (nat_lit 482321582265600)), (nat_lit 1483, Int.ofNat (nat_lit 377204281977600)), (nat_lit 1484, Int.ofNat (nat_lit 524931329260800)), (nat_lit 1485, Int.ofNat (nat_lit 405394404307200)), (nat_lit 1486, Int.ofNat (nat_lit 429382919750400)), (nat_lit 1487, Int.ofNat (nat_lit 486104821171200)), (nat_lit 1502, Int.ofNat (nat_lit 283933862150400)), (nat_lit 1503, Int.ofNat (nat_lit 525551462150400)), (nat_lit 1504, Int.ofNat (nat_lit 479630587564800)), (nat_lit 1505, Int.ofNat (nat_lit 443642451436800)), (nat_lit 1506, Int.ofNat (nat_lit 472704538521600)), (nat_lit 1507, Int.ofNat (nat_lit 375370378336800)), (nat_lit 1508, Int.ofNat (nat_lit 521437841971200)), (nat_lit 1509, Int.ofNat (nat_lit 404962695244800)), (nat_lit 1510, Int.ofNat (nat_lit 411634200146400)), (nat_lit 1511, Int.ofNat (nat_lit 463618871100000)), (nat_lit 1527, Int.ofNat (nat_lit 291966841958400)), (nat_lit 1528, Int.ofNat (nat_lit 515495981952000)), (nat_lit 1529, Int.ofNat (nat_lit 470343773491200))]
theorem block014_data_flat117_step : block014_data_flat117 = (CoefficientMerge.fastMerge block014_data_flat097 block014_data_flat116) := by decide +kernel
theorem block014_data_flat117_original : block014_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (431744082739200 : Int) atom0969Coded) (CoefficientMerge.scale (482321582265600 : Int) atom0970Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377204281977600 : Int) atom0971Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (524931329260800 : Int) atom0972Coded) (CoefficientMerge.scale (405394404307200 : Int) atom0973Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (429382919750400 : Int) atom0974Coded) (CoefficientMerge.scale (486104821171200 : Int) atom0975Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283933862150400 : Int) atom0976Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (525551462150400 : Int) atom0977Coded) (CoefficientMerge.scale (479630587564800 : Int) atom0978Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (443642451436800 : Int) atom0979Coded) (CoefficientMerge.scale (472704538521600 : Int) atom0980Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375370378336800 : Int) atom0981Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (521437841971200 : Int) atom0982Coded) (CoefficientMerge.scale (404962695244800 : Int) atom0983Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (411634200146400 : Int) atom0984Coded) (CoefficientMerge.scale (463618871100000 : Int) atom0985Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (291966841958400 : Int) atom0986Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (515495981952000 : Int) atom0987Coded) (CoefficientMerge.scale (470343773491200 : Int) atom0988Coded)))))) := by
  rw [block014_data_flat117_step, block014_data_flat097_original, block014_data_flat116_original]
def block014_data_flat118 : CoefficientMerge.Poly := [(nat_lit 1530, Int.ofNat (nat_lit 492661507968000))]
theorem block014_data_flat118_step : block014_data_flat118 = (CoefficientMerge.scale (492661507968000 : Int) atom0989Coded) := by decide +kernel
theorem block014_data_flat118_original : block014_data_flat118 = (CoefficientMerge.scale (492661507968000 : Int) atom0989Coded) := by
  rw [block014_data_flat118_step]
def block014_data_flat119 : CoefficientMerge.Poly := [(nat_lit 1531, Int.ofNat (nat_lit 379248139468800))]
theorem block014_data_flat119_step : block014_data_flat119 = (CoefficientMerge.scale (379248139468800 : Int) atom0990Coded) := by decide +kernel
theorem block014_data_flat119_original : block014_data_flat119 = (CoefficientMerge.scale (379248139468800 : Int) atom0990Coded) := by
  rw [block014_data_flat119_step]
def block014_data_flat120 : CoefficientMerge.Poly := [(nat_lit 1530, Int.ofNat (nat_lit 492661507968000)), (nat_lit 1531, Int.ofNat (nat_lit 379248139468800))]
theorem block014_data_flat120_step : block014_data_flat120 = (CoefficientMerge.fastMerge block014_data_flat118 block014_data_flat119) := by decide +kernel
theorem block014_data_flat120_original : block014_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (492661507968000 : Int) atom0989Coded) (CoefficientMerge.scale (379248139468800 : Int) atom0990Coded)) := by
  rw [block014_data_flat120_step, block014_data_flat118_original, block014_data_flat119_original]
def block014_data_flat121 : CoefficientMerge.Poly := [(nat_lit 1532, Int.ofNat (nat_lit 547518367872000))]
theorem block014_data_flat121_step : block014_data_flat121 = (CoefficientMerge.scale (547518367872000 : Int) atom0991Coded) := by decide +kernel
theorem block014_data_flat121_original : block014_data_flat121 = (CoefficientMerge.scale (547518367872000 : Int) atom0991Coded) := by
  rw [block014_data_flat121_step]
def block014_data_flat122 : CoefficientMerge.Poly := [(nat_lit 1533, Int.ofNat (nat_lit 434104999372800))]
theorem block014_data_flat122_step : block014_data_flat122 = (CoefficientMerge.scale (434104999372800 : Int) atom0992Coded) := by decide +kernel
theorem block014_data_flat122_original : block014_data_flat122 = (CoefficientMerge.scale (434104999372800 : Int) atom0992Coded) := by
  rw [block014_data_flat122_step]
def block014_data_flat123 : CoefficientMerge.Poly := [(nat_lit 1534, Int.ofNat (nat_lit 373035023424000))]
theorem block014_data_flat123_step : block014_data_flat123 = (CoefficientMerge.scale (373035023424000 : Int) atom0993Coded) := by decide +kernel
theorem block014_data_flat123_original : block014_data_flat123 = (CoefficientMerge.scale (373035023424000 : Int) atom0993Coded) := by
  rw [block014_data_flat123_step]
def block014_data_flat124 : CoefficientMerge.Poly := [(nat_lit 1533, Int.ofNat (nat_lit 434104999372800)), (nat_lit 1534, Int.ofNat (nat_lit 373035023424000))]
theorem block014_data_flat124_step : block014_data_flat124 = (CoefficientMerge.fastMerge block014_data_flat122 block014_data_flat123) := by decide +kernel
theorem block014_data_flat124_original : block014_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (434104999372800 : Int) atom0992Coded) (CoefficientMerge.scale (373035023424000 : Int) atom0993Coded)) := by
  rw [block014_data_flat124_step, block014_data_flat122_original, block014_data_flat123_original]
def block014_data_flat125 : CoefficientMerge.Poly := [(nat_lit 1532, Int.ofNat (nat_lit 547518367872000)), (nat_lit 1533, Int.ofNat (nat_lit 434104999372800)), (nat_lit 1534, Int.ofNat (nat_lit 373035023424000))]
theorem block014_data_flat125_step : block014_data_flat125 = (CoefficientMerge.fastMerge block014_data_flat121 block014_data_flat124) := by decide +kernel
theorem block014_data_flat125_original : block014_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (547518367872000 : Int) atom0991Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (434104999372800 : Int) atom0992Coded) (CoefficientMerge.scale (373035023424000 : Int) atom0993Coded))) := by
  rw [block014_data_flat125_step, block014_data_flat121_original, block014_data_flat124_original]
def block014_data_flat126 : CoefficientMerge.Poly := [(nat_lit 1530, Int.ofNat (nat_lit 492661507968000)), (nat_lit 1531, Int.ofNat (nat_lit 379248139468800)), (nat_lit 1532, Int.ofNat (nat_lit 547518367872000)), (nat_lit 1533, Int.ofNat (nat_lit 434104999372800)), (nat_lit 1534, Int.ofNat (nat_lit 373035023424000))]
theorem block014_data_flat126_step : block014_data_flat126 = (CoefficientMerge.fastMerge block014_data_flat120 block014_data_flat125) := by decide +kernel
theorem block014_data_flat126_original : block014_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (492661507968000 : Int) atom0989Coded) (CoefficientMerge.scale (379248139468800 : Int) atom0990Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (547518367872000 : Int) atom0991Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (434104999372800 : Int) atom0992Coded) (CoefficientMerge.scale (373035023424000 : Int) atom0993Coded)))) := by
  rw [block014_data_flat126_step, block014_data_flat120_original, block014_data_flat125_original]
def block014_data_flat127 : CoefficientMerge.Poly := [(nat_lit 1535, Int.ofNat (nat_lit 415072942099200))]
theorem block014_data_flat127_step : block014_data_flat127 = (CoefficientMerge.scale (415072942099200 : Int) atom0994Coded) := by decide +kernel
theorem block014_data_flat127_original : block014_data_flat127 = (CoefficientMerge.scale (415072942099200 : Int) atom0994Coded) := by
  rw [block014_data_flat127_step]
def block014_data_flat128 : CoefficientMerge.Poly := [(nat_lit 1552, Int.ofNat (nat_lit 276961422528000))]
theorem block014_data_flat128_step : block014_data_flat128 = (CoefficientMerge.scale (276961422528000 : Int) atom0995Coded) := by decide +kernel
theorem block014_data_flat128_original : block014_data_flat128 = (CoefficientMerge.scale (276961422528000 : Int) atom0995Coded) := by
  rw [block014_data_flat128_step]
def block014_data_flat129 : CoefficientMerge.Poly := [(nat_lit 1535, Int.ofNat (nat_lit 415072942099200)), (nat_lit 1552, Int.ofNat (nat_lit 276961422528000))]
theorem block014_data_flat129_step : block014_data_flat129 = (CoefficientMerge.fastMerge block014_data_flat127 block014_data_flat128) := by decide +kernel
theorem block014_data_flat129_original : block014_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (415072942099200 : Int) atom0994Coded) (CoefficientMerge.scale (276961422528000 : Int) atom0995Coded)) := by
  rw [block014_data_flat129_step, block014_data_flat127_original, block014_data_flat128_original]
def block014_data_flat130 : CoefficientMerge.Poly := [(nat_lit 1553, Int.ofNat (nat_lit 495502930944000))]
theorem block014_data_flat130_step : block014_data_flat130 = (CoefficientMerge.scale (495502930944000 : Int) atom0996Coded) := by decide +kernel
theorem block014_data_flat130_original : block014_data_flat130 = (CoefficientMerge.scale (495502930944000 : Int) atom0996Coded) := by
  rw [block014_data_flat130_step]
def block014_data_flat131 : CoefficientMerge.Poly := [(nat_lit 1554, Int.ofNat (nat_lit 488973456921600))]
theorem block014_data_flat131_step : block014_data_flat131 = (CoefficientMerge.scale (488973456921600 : Int) atom0997Coded) := by decide +kernel
theorem block014_data_flat131_original : block014_data_flat131 = (CoefficientMerge.scale (488973456921600 : Int) atom0997Coded) := by
  rw [block014_data_flat131_step]
def block014_data_flat132 : CoefficientMerge.Poly := [(nat_lit 1555, Int.ofNat (nat_lit 378621866649600))]
theorem block014_data_flat132_step : block014_data_flat132 = (CoefficientMerge.scale (378621866649600 : Int) atom0998Coded) := by decide +kernel
theorem block014_data_flat132_original : block014_data_flat132 = (CoefficientMerge.scale (378621866649600 : Int) atom0998Coded) := by
  rw [block014_data_flat132_step]
def block014_data_flat133 : CoefficientMerge.Poly := [(nat_lit 1554, Int.ofNat (nat_lit 488973456921600)), (nat_lit 1555, Int.ofNat (nat_lit 378621866649600))]
theorem block014_data_flat133_step : block014_data_flat133 = (CoefficientMerge.fastMerge block014_data_flat131 block014_data_flat132) := by decide +kernel
theorem block014_data_flat133_original : block014_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (488973456921600 : Int) atom0997Coded) (CoefficientMerge.scale (378621866649600 : Int) atom0998Coded)) := by
  rw [block014_data_flat133_step, block014_data_flat131_original, block014_data_flat132_original]
def block014_data_flat134 : CoefficientMerge.Poly := [(nat_lit 1553, Int.ofNat (nat_lit 495502930944000)), (nat_lit 1554, Int.ofNat (nat_lit 488973456921600)), (nat_lit 1555, Int.ofNat (nat_lit 378621866649600))]
theorem block014_data_flat134_step : block014_data_flat134 = (CoefficientMerge.fastMerge block014_data_flat130 block014_data_flat133) := by decide +kernel
theorem block014_data_flat134_original : block014_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (495502930944000 : Int) atom0996Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488973456921600 : Int) atom0997Coded) (CoefficientMerge.scale (378621866649600 : Int) atom0998Coded))) := by
  rw [block014_data_flat134_step, block014_data_flat130_original, block014_data_flat133_original]
def block014_data_flat135 : CoefficientMerge.Poly := [(nat_lit 1535, Int.ofNat (nat_lit 415072942099200)), (nat_lit 1552, Int.ofNat (nat_lit 276961422528000)), (nat_lit 1553, Int.ofNat (nat_lit 495502930944000)), (nat_lit 1554, Int.ofNat (nat_lit 488973456921600)), (nat_lit 1555, Int.ofNat (nat_lit 378621866649600))]
theorem block014_data_flat135_step : block014_data_flat135 = (CoefficientMerge.fastMerge block014_data_flat129 block014_data_flat134) := by decide +kernel
theorem block014_data_flat135_original : block014_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (415072942099200 : Int) atom0994Coded) (CoefficientMerge.scale (276961422528000 : Int) atom0995Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (495502930944000 : Int) atom0996Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488973456921600 : Int) atom0997Coded) (CoefficientMerge.scale (378621866649600 : Int) atom0998Coded)))) := by
  rw [block014_data_flat135_step, block014_data_flat129_original, block014_data_flat134_original]
def block014_data_flat136 : CoefficientMerge.Poly := [(nat_lit 1530, Int.ofNat (nat_lit 492661507968000)), (nat_lit 1531, Int.ofNat (nat_lit 379248139468800)), (nat_lit 1532, Int.ofNat (nat_lit 547518367872000)), (nat_lit 1533, Int.ofNat (nat_lit 434104999372800)), (nat_lit 1534, Int.ofNat (nat_lit 373035023424000)), (nat_lit 1535, Int.ofNat (nat_lit 415072942099200)), (nat_lit 1552, Int.ofNat (nat_lit 276961422528000)), (nat_lit 1553, Int.ofNat (nat_lit 495502930944000)), (nat_lit 1554, Int.ofNat (nat_lit 488973456921600)), (nat_lit 1555, Int.ofNat (nat_lit 378621866649600))]
theorem block014_data_flat136_step : block014_data_flat136 = (CoefficientMerge.fastMerge block014_data_flat126 block014_data_flat135) := by decide +kernel
theorem block014_data_flat136_original : block014_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (492661507968000 : Int) atom0989Coded) (CoefficientMerge.scale (379248139468800 : Int) atom0990Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (547518367872000 : Int) atom0991Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (434104999372800 : Int) atom0992Coded) (CoefficientMerge.scale (373035023424000 : Int) atom0993Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (415072942099200 : Int) atom0994Coded) (CoefficientMerge.scale (276961422528000 : Int) atom0995Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (495502930944000 : Int) atom0996Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488973456921600 : Int) atom0997Coded) (CoefficientMerge.scale (378621866649600 : Int) atom0998Coded))))) := by
  rw [block014_data_flat136_step, block014_data_flat126_original, block014_data_flat135_original]
def block014_data_flat137 : CoefficientMerge.Poly := [(nat_lit 1556, Int.ofNat (nat_lit 549953873280000))]
theorem block014_data_flat137_step : block014_data_flat137 = (CoefficientMerge.scale (549953873280000 : Int) atom0999Coded) := by decide +kernel
theorem block014_data_flat137_original : block014_data_flat137 = (CoefficientMerge.scale (549953873280000 : Int) atom0999Coded) := by
  rw [block014_data_flat137_step]
def block014_data_flat138 : CoefficientMerge.Poly := [(nat_lit 1557, Int.ofNat (nat_lit 439602283008000))]
theorem block014_data_flat138_step : block014_data_flat138 = (CoefficientMerge.scale (439602283008000 : Int) atom1000Coded) := by decide +kernel
theorem block014_data_flat138_original : block014_data_flat138 = (CoefficientMerge.scale (439602283008000 : Int) atom1000Coded) := by
  rw [block014_data_flat138_step]
def block014_data_flat139 : CoefficientMerge.Poly := [(nat_lit 1556, Int.ofNat (nat_lit 549953873280000)), (nat_lit 1557, Int.ofNat (nat_lit 439602283008000))]
theorem block014_data_flat139_step : block014_data_flat139 = (CoefficientMerge.fastMerge block014_data_flat137 block014_data_flat138) := by decide +kernel
theorem block014_data_flat139_original : block014_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (549953873280000 : Int) atom0999Coded) (CoefficientMerge.scale (439602283008000 : Int) atom1000Coded)) := by
  rw [block014_data_flat139_step, block014_data_flat137_original, block014_data_flat138_original]
def block014_data_flat140 : CoefficientMerge.Poly := [(nat_lit 1558, Int.ofNat (nat_lit 323801088307200))]
theorem block014_data_flat140_step : block014_data_flat140 = (CoefficientMerge.scale (323801088307200 : Int) atom1001Coded) := by decide +kernel
theorem block014_data_flat140_original : block014_data_flat140 = (CoefficientMerge.scale (323801088307200 : Int) atom1001Coded) := by
  rw [block014_data_flat140_step]
def block014_data_flat141 : CoefficientMerge.Poly := [(nat_lit 1559, Int.ofNat (nat_lit 445435576185600))]
theorem block014_data_flat141_step : block014_data_flat141 = (CoefficientMerge.scale (445435576185600 : Int) atom1002Coded) := by decide +kernel
theorem block014_data_flat141_original : block014_data_flat141 = (CoefficientMerge.scale (445435576185600 : Int) atom1002Coded) := by
  rw [block014_data_flat141_step]
def block014_data_flat142 : CoefficientMerge.Poly := [(nat_lit 1577, Int.ofNat (nat_lit 267182675020800))]
theorem block014_data_flat142_step : block014_data_flat142 = (CoefficientMerge.scale (267182675020800 : Int) atom1003Coded) := by decide +kernel
theorem block014_data_flat142_original : block014_data_flat142 = (CoefficientMerge.scale (267182675020800 : Int) atom1003Coded) := by
  rw [block014_data_flat142_step]
def block014_data_flat143 : CoefficientMerge.Poly := [(nat_lit 1559, Int.ofNat (nat_lit 445435576185600)), (nat_lit 1577, Int.ofNat (nat_lit 267182675020800))]
theorem block014_data_flat143_step : block014_data_flat143 = (CoefficientMerge.fastMerge block014_data_flat141 block014_data_flat142) := by decide +kernel
theorem block014_data_flat143_original : block014_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (445435576185600 : Int) atom1002Coded) (CoefficientMerge.scale (267182675020800 : Int) atom1003Coded)) := by
  rw [block014_data_flat143_step, block014_data_flat141_original, block014_data_flat142_original]
def block014_data_flat144 : CoefficientMerge.Poly := [(nat_lit 1558, Int.ofNat (nat_lit 323801088307200)), (nat_lit 1559, Int.ofNat (nat_lit 445435576185600)), (nat_lit 1577, Int.ofNat (nat_lit 267182675020800))]
theorem block014_data_flat144_step : block014_data_flat144 = (CoefficientMerge.fastMerge block014_data_flat140 block014_data_flat143) := by decide +kernel
theorem block014_data_flat144_original : block014_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (323801088307200 : Int) atom1001Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (445435576185600 : Int) atom1002Coded) (CoefficientMerge.scale (267182675020800 : Int) atom1003Coded))) := by
  rw [block014_data_flat144_step, block014_data_flat140_original, block014_data_flat143_original]
def block014_data_flat145 : CoefficientMerge.Poly := [(nat_lit 1556, Int.ofNat (nat_lit 549953873280000)), (nat_lit 1557, Int.ofNat (nat_lit 439602283008000)), (nat_lit 1558, Int.ofNat (nat_lit 323801088307200)), (nat_lit 1559, Int.ofNat (nat_lit 445435576185600)), (nat_lit 1577, Int.ofNat (nat_lit 267182675020800))]
theorem block014_data_flat145_step : block014_data_flat145 = (CoefficientMerge.fastMerge block014_data_flat139 block014_data_flat144) := by decide +kernel
theorem block014_data_flat145_original : block014_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (549953873280000 : Int) atom0999Coded) (CoefficientMerge.scale (439602283008000 : Int) atom1000Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (323801088307200 : Int) atom1001Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (445435576185600 : Int) atom1002Coded) (CoefficientMerge.scale (267182675020800 : Int) atom1003Coded)))) := by
  rw [block014_data_flat145_step, block014_data_flat139_original, block014_data_flat144_original]
def block014_data_flat146 : CoefficientMerge.Poly := [(nat_lit 1578, Int.ofNat (nat_lit 505150882790400))]
theorem block014_data_flat146_step : block014_data_flat146 = (CoefficientMerge.scale (505150882790400 : Int) atom1004Coded) := by decide +kernel
theorem block014_data_flat146_original : block014_data_flat146 = (CoefficientMerge.scale (505150882790400 : Int) atom1004Coded) := by
  rw [block014_data_flat146_step]
def block014_data_flat147 : CoefficientMerge.Poly := [(nat_lit 1579, Int.ofNat (nat_lit 397861070745600))]
theorem block014_data_flat147_step : block014_data_flat147 = (CoefficientMerge.scale (397861070745600 : Int) atom1005Coded) := by decide +kernel
theorem block014_data_flat147_original : block014_data_flat147 = (CoefficientMerge.scale (397861070745600 : Int) atom1005Coded) := by
  rw [block014_data_flat147_step]
def block014_data_flat148 : CoefficientMerge.Poly := [(nat_lit 1578, Int.ofNat (nat_lit 505150882790400)), (nat_lit 1579, Int.ofNat (nat_lit 397861070745600))]
theorem block014_data_flat148_step : block014_data_flat148 = (CoefficientMerge.fastMerge block014_data_flat146 block014_data_flat147) := by decide +kernel
theorem block014_data_flat148_original : block014_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (505150882790400 : Int) atom1004Coded) (CoefficientMerge.scale (397861070745600 : Int) atom1005Coded)) := by
  rw [block014_data_flat148_step, block014_data_flat146_original, block014_data_flat147_original]
def block014_data_flat149 : CoefficientMerge.Poly := [(nat_lit 1580, Int.ofNat (nat_lit 572254855603200))]
theorem block014_data_flat149_step : block014_data_flat149 = (CoefficientMerge.scale (572254855603200 : Int) atom1006Coded) := by decide +kernel
theorem block014_data_flat149_original : block014_data_flat149 = (CoefficientMerge.scale (572254855603200 : Int) atom1006Coded) := by
  rw [block014_data_flat149_step]
def block014_data_flat150 : CoefficientMerge.Poly := [(nat_lit 1581, Int.ofNat (nat_lit 464965043558400))]
theorem block014_data_flat150_step : block014_data_flat150 = (CoefficientMerge.scale (464965043558400 : Int) atom1007Coded) := by decide +kernel
theorem block014_data_flat150_original : block014_data_flat150 = (CoefficientMerge.scale (464965043558400 : Int) atom1007Coded) := by
  rw [block014_data_flat150_step]
def block014_data_flat151 : CoefficientMerge.Poly := [(nat_lit 1582, Int.ofNat (nat_lit 351101944166400))]
theorem block014_data_flat151_step : block014_data_flat151 = (CoefficientMerge.scale (351101944166400 : Int) atom1008Coded) := by decide +kernel
theorem block014_data_flat151_original : block014_data_flat151 = (CoefficientMerge.scale (351101944166400 : Int) atom1008Coded) := by
  rw [block014_data_flat151_step]
def block014_data_flat152 : CoefficientMerge.Poly := [(nat_lit 1581, Int.ofNat (nat_lit 464965043558400)), (nat_lit 1582, Int.ofNat (nat_lit 351101944166400))]
theorem block014_data_flat152_step : block014_data_flat152 = (CoefficientMerge.fastMerge block014_data_flat150 block014_data_flat151) := by decide +kernel
theorem block014_data_flat152_original : block014_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (464965043558400 : Int) atom1007Coded) (CoefficientMerge.scale (351101944166400 : Int) atom1008Coded)) := by
  rw [block014_data_flat152_step, block014_data_flat150_original, block014_data_flat151_original]
def block014_data_flat153 : CoefficientMerge.Poly := [(nat_lit 1580, Int.ofNat (nat_lit 572254855603200)), (nat_lit 1581, Int.ofNat (nat_lit 464965043558400)), (nat_lit 1582, Int.ofNat (nat_lit 351101944166400))]
theorem block014_data_flat153_step : block014_data_flat153 = (CoefficientMerge.fastMerge block014_data_flat149 block014_data_flat152) := by decide +kernel
theorem block014_data_flat153_original : block014_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (572254855603200 : Int) atom1006Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (464965043558400 : Int) atom1007Coded) (CoefficientMerge.scale (351101944166400 : Int) atom1008Coded))) := by
  rw [block014_data_flat153_step, block014_data_flat149_original, block014_data_flat152_original]
def block014_data_flat154 : CoefficientMerge.Poly := [(nat_lit 1578, Int.ofNat (nat_lit 505150882790400)), (nat_lit 1579, Int.ofNat (nat_lit 397861070745600)), (nat_lit 1580, Int.ofNat (nat_lit 572254855603200)), (nat_lit 1581, Int.ofNat (nat_lit 464965043558400)), (nat_lit 1582, Int.ofNat (nat_lit 351101944166400))]
theorem block014_data_flat154_step : block014_data_flat154 = (CoefficientMerge.fastMerge block014_data_flat148 block014_data_flat153) := by decide +kernel
theorem block014_data_flat154_original : block014_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (505150882790400 : Int) atom1004Coded) (CoefficientMerge.scale (397861070745600 : Int) atom1005Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (572254855603200 : Int) atom1006Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (464965043558400 : Int) atom1007Coded) (CoefficientMerge.scale (351101944166400 : Int) atom1008Coded)))) := by
  rw [block014_data_flat154_step, block014_data_flat148_original, block014_data_flat153_original]
def block014_data_flat155 : CoefficientMerge.Poly := [(nat_lit 1556, Int.ofNat (nat_lit 549953873280000)), (nat_lit 1557, Int.ofNat (nat_lit 439602283008000)), (nat_lit 1558, Int.ofNat (nat_lit 323801088307200)), (nat_lit 1559, Int.ofNat (nat_lit 445435576185600)), (nat_lit 1577, Int.ofNat (nat_lit 267182675020800)), (nat_lit 1578, Int.ofNat (nat_lit 505150882790400)), (nat_lit 1579, Int.ofNat (nat_lit 397861070745600)), (nat_lit 1580, Int.ofNat (nat_lit 572254855603200)), (nat_lit 1581, Int.ofNat (nat_lit 464965043558400)), (nat_lit 1582, Int.ofNat (nat_lit 351101944166400))]
theorem block014_data_flat155_step : block014_data_flat155 = (CoefficientMerge.fastMerge block014_data_flat145 block014_data_flat154) := by decide +kernel
theorem block014_data_flat155_original : block014_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (549953873280000 : Int) atom0999Coded) (CoefficientMerge.scale (439602283008000 : Int) atom1000Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (323801088307200 : Int) atom1001Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (445435576185600 : Int) atom1002Coded) (CoefficientMerge.scale (267182675020800 : Int) atom1003Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (505150882790400 : Int) atom1004Coded) (CoefficientMerge.scale (397861070745600 : Int) atom1005Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (572254855603200 : Int) atom1006Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (464965043558400 : Int) atom1007Coded) (CoefficientMerge.scale (351101944166400 : Int) atom1008Coded))))) := by
  rw [block014_data_flat155_step, block014_data_flat145_original, block014_data_flat154_original]
def block014_data_flat156 : CoefficientMerge.Poly := [(nat_lit 1530, Int.ofNat (nat_lit 492661507968000)), (nat_lit 1531, Int.ofNat (nat_lit 379248139468800)), (nat_lit 1532, Int.ofNat (nat_lit 547518367872000)), (nat_lit 1533, Int.ofNat (nat_lit 434104999372800)), (nat_lit 1534, Int.ofNat (nat_lit 373035023424000)), (nat_lit 1535, Int.ofNat (nat_lit 415072942099200)), (nat_lit 1552, Int.ofNat (nat_lit 276961422528000)), (nat_lit 1553, Int.ofNat (nat_lit 495502930944000)), (nat_lit 1554, Int.ofNat (nat_lit 488973456921600)), (nat_lit 1555, Int.ofNat (nat_lit 378621866649600)), (nat_lit 1556, Int.ofNat (nat_lit 549953873280000)), (nat_lit 1557, Int.ofNat (nat_lit 439602283008000)), (nat_lit 1558, Int.ofNat (nat_lit 323801088307200)), (nat_lit 1559, Int.ofNat (nat_lit 445435576185600)), (nat_lit 1577, Int.ofNat (nat_lit 267182675020800)), (nat_lit 1578, Int.ofNat (nat_lit 505150882790400)), (nat_lit 1579, Int.ofNat (nat_lit 397861070745600)), (nat_lit 1580, Int.ofNat (nat_lit 572254855603200)), (nat_lit 1581, Int.ofNat (nat_lit 464965043558400)), (nat_lit 1582, Int.ofNat (nat_lit 351101944166400))]
theorem block014_data_flat156_step : block014_data_flat156 = (CoefficientMerge.fastMerge block014_data_flat136 block014_data_flat155) := by decide +kernel
theorem block014_data_flat156_original : block014_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (492661507968000 : Int) atom0989Coded) (CoefficientMerge.scale (379248139468800 : Int) atom0990Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (547518367872000 : Int) atom0991Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (434104999372800 : Int) atom0992Coded) (CoefficientMerge.scale (373035023424000 : Int) atom0993Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (415072942099200 : Int) atom0994Coded) (CoefficientMerge.scale (276961422528000 : Int) atom0995Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (495502930944000 : Int) atom0996Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488973456921600 : Int) atom0997Coded) (CoefficientMerge.scale (378621866649600 : Int) atom0998Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (549953873280000 : Int) atom0999Coded) (CoefficientMerge.scale (439602283008000 : Int) atom1000Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (323801088307200 : Int) atom1001Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (445435576185600 : Int) atom1002Coded) (CoefficientMerge.scale (267182675020800 : Int) atom1003Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (505150882790400 : Int) atom1004Coded) (CoefficientMerge.scale (397861070745600 : Int) atom1005Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (572254855603200 : Int) atom1006Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (464965043558400 : Int) atom1007Coded) (CoefficientMerge.scale (351101944166400 : Int) atom1008Coded)))))) := by
  rw [block014_data_flat156_step, block014_data_flat136_original, block014_data_flat155_original]
def block014_data_flat157 : CoefficientMerge.Poly := [(nat_lit 1481, Int.ofNat (nat_lit 431744082739200)), (nat_lit 1482, Int.ofNat (nat_lit 482321582265600)), (nat_lit 1483, Int.ofNat (nat_lit 377204281977600)), (nat_lit 1484, Int.ofNat (nat_lit 524931329260800)), (nat_lit 1485, Int.ofNat (nat_lit 405394404307200)), (nat_lit 1486, Int.ofNat (nat_lit 429382919750400)), (nat_lit 1487, Int.ofNat (nat_lit 486104821171200)), (nat_lit 1502, Int.ofNat (nat_lit 283933862150400)), (nat_lit 1503, Int.ofNat (nat_lit 525551462150400)), (nat_lit 1504, Int.ofNat (nat_lit 479630587564800)), (nat_lit 1505, Int.ofNat (nat_lit 443642451436800)), (nat_lit 1506, Int.ofNat (nat_lit 472704538521600)), (nat_lit 1507, Int.ofNat (nat_lit 375370378336800)), (nat_lit 1508, Int.ofNat (nat_lit 521437841971200)), (nat_lit 1509, Int.ofNat (nat_lit 404962695244800)), (nat_lit 1510, Int.ofNat (nat_lit 411634200146400)), (nat_lit 1511, Int.ofNat (nat_lit 463618871100000)), (nat_lit 1527, Int.ofNat (nat_lit 291966841958400)), (nat_lit 1528, Int.ofNat (nat_lit 515495981952000)), (nat_lit 1529, Int.ofNat (nat_lit 470343773491200)), (nat_lit 1530, Int.ofNat (nat_lit 492661507968000)), (nat_lit 1531, Int.ofNat (nat_lit 379248139468800)), (nat_lit 1532, Int.ofNat (nat_lit 547518367872000)), (nat_lit 1533, Int.ofNat (nat_lit 434104999372800)), (nat_lit 1534, Int.ofNat (nat_lit 373035023424000)), (nat_lit 1535, Int.ofNat (nat_lit 415072942099200)), (nat_lit 1552, Int.ofNat (nat_lit 276961422528000)), (nat_lit 1553, Int.ofNat (nat_lit 495502930944000)), (nat_lit 1554, Int.ofNat (nat_lit 488973456921600)), (nat_lit 1555, Int.ofNat (nat_lit 378621866649600)), (nat_lit 1556, Int.ofNat (nat_lit 549953873280000)), (nat_lit 1557, Int.ofNat (nat_lit 439602283008000)), (nat_lit 1558, Int.ofNat (nat_lit 323801088307200)), (nat_lit 1559, Int.ofNat (nat_lit 445435576185600)), (nat_lit 1577, Int.ofNat (nat_lit 267182675020800)), (nat_lit 1578, Int.ofNat (nat_lit 505150882790400)), (nat_lit 1579, Int.ofNat (nat_lit 397861070745600)), (nat_lit 1580, Int.ofNat (nat_lit 572254855603200)), (nat_lit 1581, Int.ofNat (nat_lit 464965043558400)), (nat_lit 1582, Int.ofNat (nat_lit 351101944166400))]
theorem block014_data_flat157_step : block014_data_flat157 = (CoefficientMerge.fastMerge block014_data_flat117 block014_data_flat156) := by decide +kernel
theorem block014_data_flat157_original : block014_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (431744082739200 : Int) atom0969Coded) (CoefficientMerge.scale (482321582265600 : Int) atom0970Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377204281977600 : Int) atom0971Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (524931329260800 : Int) atom0972Coded) (CoefficientMerge.scale (405394404307200 : Int) atom0973Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (429382919750400 : Int) atom0974Coded) (CoefficientMerge.scale (486104821171200 : Int) atom0975Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283933862150400 : Int) atom0976Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (525551462150400 : Int) atom0977Coded) (CoefficientMerge.scale (479630587564800 : Int) atom0978Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (443642451436800 : Int) atom0979Coded) (CoefficientMerge.scale (472704538521600 : Int) atom0980Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375370378336800 : Int) atom0981Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (521437841971200 : Int) atom0982Coded) (CoefficientMerge.scale (404962695244800 : Int) atom0983Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (411634200146400 : Int) atom0984Coded) (CoefficientMerge.scale (463618871100000 : Int) atom0985Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (291966841958400 : Int) atom0986Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (515495981952000 : Int) atom0987Coded) (CoefficientMerge.scale (470343773491200 : Int) atom0988Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (492661507968000 : Int) atom0989Coded) (CoefficientMerge.scale (379248139468800 : Int) atom0990Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (547518367872000 : Int) atom0991Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (434104999372800 : Int) atom0992Coded) (CoefficientMerge.scale (373035023424000 : Int) atom0993Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (415072942099200 : Int) atom0994Coded) (CoefficientMerge.scale (276961422528000 : Int) atom0995Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (495502930944000 : Int) atom0996Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488973456921600 : Int) atom0997Coded) (CoefficientMerge.scale (378621866649600 : Int) atom0998Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (549953873280000 : Int) atom0999Coded) (CoefficientMerge.scale (439602283008000 : Int) atom1000Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (323801088307200 : Int) atom1001Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (445435576185600 : Int) atom1002Coded) (CoefficientMerge.scale (267182675020800 : Int) atom1003Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (505150882790400 : Int) atom1004Coded) (CoefficientMerge.scale (397861070745600 : Int) atom1005Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (572254855603200 : Int) atom1006Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (464965043558400 : Int) atom1007Coded) (CoefficientMerge.scale (351101944166400 : Int) atom1008Coded))))))) := by
  rw [block014_data_flat157_step, block014_data_flat117_original, block014_data_flat156_original]
def block014_data_flat158 : CoefficientMerge.Poly := [(nat_lit 1405, Int.ofNat (nat_lit 403961087933568)), (nat_lit 1406, Int.ofNat (nat_lit 381526078906368)), (nat_lit 1407, Int.ofNat (nat_lit 373878076474368)), (nat_lit 1408, Int.ofNat (nat_lit 354407563795968)), (nat_lit 1409, Int.ofNat (nat_lit 344869789575168)), (nat_lit 1410, Int.ofNat (nat_lit 379974615939072)), (nat_lit 1411, Int.ofNat (nat_lit 329477914529280)), (nat_lit 1412, Int.ofNat (nat_lit 419823011570688)), (nat_lit 1413, Int.ofNat (nat_lit 399350123656704)), (nat_lit 1414, Int.ofNat (nat_lit 445024402859520)), (nat_lit 1415, Int.ofNat (nat_lit 523432068039936)), (nat_lit 1427, Int.ofNat (nat_lit 247082976765504)), (nat_lit 1428, Int.ofNat (nat_lit 484045607060928)), (nat_lit 1429, Int.ofNat (nat_lit 457120118911104)), (nat_lit 1430, Int.ofNat (nat_lit 426520367944704)), (nat_lit 1431, Int.ofNat (nat_lit 410707623573504)), (nat_lit 1432, Int.ofNat (nat_lit 386155409531904)), (nat_lit 1433, Int.ofNat (nat_lit 371535933947904)), (nat_lit 1434, Int.ofNat (nat_lit 413692392979008)), (nat_lit 1435, Int.ofNat (nat_lit 347494413911040)), (nat_lit 1436, Int.ofNat (nat_lit 444055027065408)), (nat_lit 1437, Int.ofNat (nat_lit 410230735782912)), (nat_lit 1438, Int.ofNat (nat_lit 452841657269760)), (nat_lit 1439, Int.ofNat (nat_lit 528185964734208)), (nat_lit 1452, Int.ofNat (nat_lit 284228831677824)), (nat_lit 1453, Int.ofNat (nat_lit 526699029124224)), (nat_lit 1454, Int.ofNat (nat_lit 493080024628224)), (nat_lit 1455, Int.ofNat (nat_lit 474248026727424)), (nat_lit 1456, Int.ofNat (nat_lit 443593518580224)), (nat_lit 1457, Int.ofNat (nat_lit 422871748890624)), (nat_lit 1458, Int.ofNat (nat_lit 484590100376448)), (nat_lit 1459, Int.ofNat (nat_lit 377389276323840)), (nat_lit 1460, Int.ofNat (nat_lit 521076290917248)), (nat_lit 1461, Int.ofNat (nat_lit 409448281347072)), (nat_lit 1462, Int.ofNat (nat_lit 433641756303360)), (nat_lit 1463, Int.ofNat (nat_lit 490568617237248)), (nat_lit 1477, Int.ofNat (nat_lit 289736398828800)), (nat_lit 1478, Int.ofNat (nat_lit 526404059596800)), (nat_lit 1479, Int.ofNat (nat_lit 497366134272000)), (nat_lit 1480, Int.ofNat (nat_lit 459588739276800)), (nat_lit 1481, Int.ofNat (nat_lit 431744082739200)), (nat_lit 1482, Int.ofNat (nat_lit 482321582265600)), (nat_lit 1483, Int.ofNat (nat_lit 377204281977600)), (nat_lit 1484, Int.ofNat (nat_lit 524931329260800)), (nat_lit 1485, Int.ofNat (nat_lit 405394404307200)), (nat_lit 1486, Int.ofNat (nat_lit 429382919750400)), (nat_lit 1487, Int.ofNat (nat_lit 486104821171200)), (nat_lit 1502, Int.ofNat (nat_lit 283933862150400)), (nat_lit 1503, Int.ofNat (nat_lit 525551462150400)), (nat_lit 1504, Int.ofNat (nat_lit 479630587564800)), (nat_lit 1505, Int.ofNat (nat_lit 443642451436800)), (nat_lit 1506, Int.ofNat (nat_lit 472704538521600)), (nat_lit 1507, Int.ofNat (nat_lit 375370378336800)), (nat_lit 1508, Int.ofNat (nat_lit 521437841971200)), (nat_lit 1509, Int.ofNat (nat_lit 404962695244800)), (nat_lit 1510, Int.ofNat (nat_lit 411634200146400)), (nat_lit 1511, Int.ofNat (nat_lit 463618871100000)), (nat_lit 1527, Int.ofNat (nat_lit 291966841958400)), (nat_lit 1528, Int.ofNat (nat_lit 515495981952000)), (nat_lit 1529, Int.ofNat (nat_lit 470343773491200)), (nat_lit 1530, Int.ofNat (nat_lit 492661507968000)), (nat_lit 1531, Int.ofNat (nat_lit 379248139468800)), (nat_lit 1532, Int.ofNat (nat_lit 547518367872000)), (nat_lit 1533, Int.ofNat (nat_lit 434104999372800)), (nat_lit 1534, Int.ofNat (nat_lit 373035023424000)), (nat_lit 1535, Int.ofNat (nat_lit 415072942099200)), (nat_lit 1552, Int.ofNat (nat_lit 276961422528000)), (nat_lit 1553, Int.ofNat (nat_lit 495502930944000)), (nat_lit 1554, Int.ofNat (nat_lit 488973456921600)), (nat_lit 1555, Int.ofNat (nat_lit 378621866649600)), (nat_lit 1556, Int.ofNat (nat_lit 549953873280000)), (nat_lit 1557, Int.ofNat (nat_lit 439602283008000)), (nat_lit 1558, Int.ofNat (nat_lit 323801088307200)), (nat_lit 1559, Int.ofNat (nat_lit 445435576185600)), (nat_lit 1577, Int.ofNat (nat_lit 267182675020800)), (nat_lit 1578, Int.ofNat (nat_lit 505150882790400)), (nat_lit 1579, Int.ofNat (nat_lit 397861070745600)), (nat_lit 1580, Int.ofNat (nat_lit 572254855603200)), (nat_lit 1581, Int.ofNat (nat_lit 464965043558400)), (nat_lit 1582, Int.ofNat (nat_lit 351101944166400))]
theorem block014_data_flat158_step : block014_data_flat158 = (CoefficientMerge.fastMerge block014_data_flat078 block014_data_flat157) := by decide +kernel
theorem block014_data_flat158_original : block014_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (403961087933568 : Int) atom0929Coded) (CoefficientMerge.scale (381526078906368 : Int) atom0930Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (373878076474368 : Int) atom0931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (354407563795968 : Int) atom0932Coded) (CoefficientMerge.scale (344869789575168 : Int) atom0933Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (379974615939072 : Int) atom0934Coded) (CoefficientMerge.scale (329477914529280 : Int) atom0935Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (419823011570688 : Int) atom0936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (399350123656704 : Int) atom0937Coded) (CoefficientMerge.scale (445024402859520 : Int) atom0938Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (523432068039936 : Int) atom0939Coded) (CoefficientMerge.scale (247082976765504 : Int) atom0940Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (484045607060928 : Int) atom0941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457120118911104 : Int) atom0942Coded) (CoefficientMerge.scale (426520367944704 : Int) atom0943Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (410707623573504 : Int) atom0944Coded) (CoefficientMerge.scale (386155409531904 : Int) atom0945Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (371535933947904 : Int) atom0946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413692392979008 : Int) atom0947Coded) (CoefficientMerge.scale (347494413911040 : Int) atom0948Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (444055027065408 : Int) atom0949Coded) (CoefficientMerge.scale (410230735782912 : Int) atom0950Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (452841657269760 : Int) atom0951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (528185964734208 : Int) atom0952Coded) (CoefficientMerge.scale (284228831677824 : Int) atom0953Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (526699029124224 : Int) atom0954Coded) (CoefficientMerge.scale (493080024628224 : Int) atom0955Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (474248026727424 : Int) atom0956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (443593518580224 : Int) atom0957Coded) (CoefficientMerge.scale (422871748890624 : Int) atom0958Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (484590100376448 : Int) atom0959Coded) (CoefficientMerge.scale (377389276323840 : Int) atom0960Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (521076290917248 : Int) atom0961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (409448281347072 : Int) atom0962Coded) (CoefficientMerge.scale (433641756303360 : Int) atom0963Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (490568617237248 : Int) atom0964Coded) (CoefficientMerge.scale (289736398828800 : Int) atom0965Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (526404059596800 : Int) atom0966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497366134272000 : Int) atom0967Coded) (CoefficientMerge.scale (459588739276800 : Int) atom0968Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (431744082739200 : Int) atom0969Coded) (CoefficientMerge.scale (482321582265600 : Int) atom0970Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377204281977600 : Int) atom0971Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (524931329260800 : Int) atom0972Coded) (CoefficientMerge.scale (405394404307200 : Int) atom0973Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (429382919750400 : Int) atom0974Coded) (CoefficientMerge.scale (486104821171200 : Int) atom0975Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283933862150400 : Int) atom0976Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (525551462150400 : Int) atom0977Coded) (CoefficientMerge.scale (479630587564800 : Int) atom0978Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (443642451436800 : Int) atom0979Coded) (CoefficientMerge.scale (472704538521600 : Int) atom0980Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375370378336800 : Int) atom0981Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (521437841971200 : Int) atom0982Coded) (CoefficientMerge.scale (404962695244800 : Int) atom0983Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (411634200146400 : Int) atom0984Coded) (CoefficientMerge.scale (463618871100000 : Int) atom0985Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (291966841958400 : Int) atom0986Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (515495981952000 : Int) atom0987Coded) (CoefficientMerge.scale (470343773491200 : Int) atom0988Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (492661507968000 : Int) atom0989Coded) (CoefficientMerge.scale (379248139468800 : Int) atom0990Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (547518367872000 : Int) atom0991Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (434104999372800 : Int) atom0992Coded) (CoefficientMerge.scale (373035023424000 : Int) atom0993Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (415072942099200 : Int) atom0994Coded) (CoefficientMerge.scale (276961422528000 : Int) atom0995Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (495502930944000 : Int) atom0996Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488973456921600 : Int) atom0997Coded) (CoefficientMerge.scale (378621866649600 : Int) atom0998Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (549953873280000 : Int) atom0999Coded) (CoefficientMerge.scale (439602283008000 : Int) atom1000Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (323801088307200 : Int) atom1001Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (445435576185600 : Int) atom1002Coded) (CoefficientMerge.scale (267182675020800 : Int) atom1003Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (505150882790400 : Int) atom1004Coded) (CoefficientMerge.scale (397861070745600 : Int) atom1005Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (572254855603200 : Int) atom1006Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (464965043558400 : Int) atom1007Coded) (CoefficientMerge.scale (351101944166400 : Int) atom1008Coded)))))))) := by
  rw [block014_data_flat158_step, block014_data_flat078_original, block014_data_flat157_original]
def block014_data_flat159 : CoefficientMerge.Poly := [(nat_lit 1405, Int.ofNat (nat_lit 403961087933568)), (nat_lit 1406, Int.ofNat (nat_lit 381526078906368)), (nat_lit 1407, Int.ofNat (nat_lit 373878076474368)), (nat_lit 1408, Int.ofNat (nat_lit 354407563795968)), (nat_lit 1409, Int.ofNat (nat_lit 344869789575168)), (nat_lit 1410, Int.ofNat (nat_lit 379974615939072)), (nat_lit 1411, Int.ofNat (nat_lit 329477914529280)), (nat_lit 1412, Int.ofNat (nat_lit 419823011570688)), (nat_lit 1413, Int.ofNat (nat_lit 399350123656704)), (nat_lit 1414, Int.ofNat (nat_lit 445024402859520)), (nat_lit 1415, Int.ofNat (nat_lit 523432068039936)), (nat_lit 1427, Int.ofNat (nat_lit 247082976765504)), (nat_lit 1428, Int.ofNat (nat_lit 484045607060928)), (nat_lit 1429, Int.ofNat (nat_lit 457120118911104)), (nat_lit 1430, Int.ofNat (nat_lit 426520367944704)), (nat_lit 1431, Int.ofNat (nat_lit 410707623573504)), (nat_lit 1432, Int.ofNat (nat_lit 386155409531904)), (nat_lit 1433, Int.ofNat (nat_lit 371535933947904)), (nat_lit 1434, Int.ofNat (nat_lit 413692392979008)), (nat_lit 1435, Int.ofNat (nat_lit 347494413911040)), (nat_lit 1436, Int.ofNat (nat_lit 444055027065408)), (nat_lit 1437, Int.ofNat (nat_lit 410230735782912)), (nat_lit 1438, Int.ofNat (nat_lit 452841657269760)), (nat_lit 1439, Int.ofNat (nat_lit 528185964734208)), (nat_lit 1452, Int.ofNat (nat_lit 284228831677824)), (nat_lit 1453, Int.ofNat (nat_lit 526699029124224)), (nat_lit 1454, Int.ofNat (nat_lit 493080024628224)), (nat_lit 1455, Int.ofNat (nat_lit 474248026727424)), (nat_lit 1456, Int.ofNat (nat_lit 443593518580224)), (nat_lit 1457, Int.ofNat (nat_lit 422871748890624)), (nat_lit 1458, Int.ofNat (nat_lit 484590100376448)), (nat_lit 1459, Int.ofNat (nat_lit 377389276323840)), (nat_lit 1460, Int.ofNat (nat_lit 521076290917248)), (nat_lit 1461, Int.ofNat (nat_lit 409448281347072)), (nat_lit 1462, Int.ofNat (nat_lit 433641756303360)), (nat_lit 1463, Int.ofNat (nat_lit 490568617237248)), (nat_lit 1477, Int.ofNat (nat_lit 289736398828800)), (nat_lit 1478, Int.ofNat (nat_lit 526404059596800)), (nat_lit 1479, Int.ofNat (nat_lit 497366134272000)), (nat_lit 1480, Int.ofNat (nat_lit 459588739276800)), (nat_lit 1481, Int.ofNat (nat_lit 431744082739200)), (nat_lit 1482, Int.ofNat (nat_lit 482321582265600)), (nat_lit 1483, Int.ofNat (nat_lit 377204281977600)), (nat_lit 1484, Int.ofNat (nat_lit 524931329260800)), (nat_lit 1485, Int.ofNat (nat_lit 405394404307200)), (nat_lit 1486, Int.ofNat (nat_lit 429382919750400)), (nat_lit 1487, Int.ofNat (nat_lit 486104821171200)), (nat_lit 1502, Int.ofNat (nat_lit 283933862150400)), (nat_lit 1503, Int.ofNat (nat_lit 525551462150400)), (nat_lit 1504, Int.ofNat (nat_lit 479630587564800)), (nat_lit 1505, Int.ofNat (nat_lit 443642451436800)), (nat_lit 1506, Int.ofNat (nat_lit 472704538521600)), (nat_lit 1507, Int.ofNat (nat_lit 375370378336800)), (nat_lit 1508, Int.ofNat (nat_lit 521437841971200)), (nat_lit 1509, Int.ofNat (nat_lit 404962695244800)), (nat_lit 1510, Int.ofNat (nat_lit 411634200146400)), (nat_lit 1511, Int.ofNat (nat_lit 463618871100000)), (nat_lit 1527, Int.ofNat (nat_lit 291966841958400)), (nat_lit 1528, Int.ofNat (nat_lit 515495981952000)), (nat_lit 1529, Int.ofNat (nat_lit 470343773491200)), (nat_lit 1530, Int.ofNat (nat_lit 492661507968000)), (nat_lit 1531, Int.ofNat (nat_lit 379248139468800)), (nat_lit 1532, Int.ofNat (nat_lit 547518367872000)), (nat_lit 1533, Int.ofNat (nat_lit 434104999372800)), (nat_lit 1534, Int.ofNat (nat_lit 373035023424000)), (nat_lit 1535, Int.ofNat (nat_lit 415072942099200)), (nat_lit 1552, Int.ofNat (nat_lit 276961422528000)), (nat_lit 1553, Int.ofNat (nat_lit 495502930944000)), (nat_lit 1554, Int.ofNat (nat_lit 488973456921600)), (nat_lit 1555, Int.ofNat (nat_lit 378621866649600)), (nat_lit 1556, Int.ofNat (nat_lit 549953873280000)), (nat_lit 1557, Int.ofNat (nat_lit 439602283008000)), (nat_lit 1558, Int.ofNat (nat_lit 323801088307200)), (nat_lit 1559, Int.ofNat (nat_lit 445435576185600)), (nat_lit 1577, Int.ofNat (nat_lit 267182675020800)), (nat_lit 1578, Int.ofNat (nat_lit 505150882790400)), (nat_lit 1579, Int.ofNat (nat_lit 397861070745600)), (nat_lit 1580, Int.ofNat (nat_lit 572254855603200)), (nat_lit 1581, Int.ofNat (nat_lit 464965043558400)), (nat_lit 1582, Int.ofNat (nat_lit 351101944166400))]
theorem block014_data_flat159_step : block014_data_flat159 = (CoefficientMerge.trim block014_data_flat158) := by decide +kernel
theorem block014_data_flat159_original : block014_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (403961087933568 : Int) atom0929Coded) (CoefficientMerge.scale (381526078906368 : Int) atom0930Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (373878076474368 : Int) atom0931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (354407563795968 : Int) atom0932Coded) (CoefficientMerge.scale (344869789575168 : Int) atom0933Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (379974615939072 : Int) atom0934Coded) (CoefficientMerge.scale (329477914529280 : Int) atom0935Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (419823011570688 : Int) atom0936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (399350123656704 : Int) atom0937Coded) (CoefficientMerge.scale (445024402859520 : Int) atom0938Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (523432068039936 : Int) atom0939Coded) (CoefficientMerge.scale (247082976765504 : Int) atom0940Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (484045607060928 : Int) atom0941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457120118911104 : Int) atom0942Coded) (CoefficientMerge.scale (426520367944704 : Int) atom0943Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (410707623573504 : Int) atom0944Coded) (CoefficientMerge.scale (386155409531904 : Int) atom0945Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (371535933947904 : Int) atom0946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413692392979008 : Int) atom0947Coded) (CoefficientMerge.scale (347494413911040 : Int) atom0948Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (444055027065408 : Int) atom0949Coded) (CoefficientMerge.scale (410230735782912 : Int) atom0950Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (452841657269760 : Int) atom0951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (528185964734208 : Int) atom0952Coded) (CoefficientMerge.scale (284228831677824 : Int) atom0953Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (526699029124224 : Int) atom0954Coded) (CoefficientMerge.scale (493080024628224 : Int) atom0955Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (474248026727424 : Int) atom0956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (443593518580224 : Int) atom0957Coded) (CoefficientMerge.scale (422871748890624 : Int) atom0958Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (484590100376448 : Int) atom0959Coded) (CoefficientMerge.scale (377389276323840 : Int) atom0960Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (521076290917248 : Int) atom0961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (409448281347072 : Int) atom0962Coded) (CoefficientMerge.scale (433641756303360 : Int) atom0963Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (490568617237248 : Int) atom0964Coded) (CoefficientMerge.scale (289736398828800 : Int) atom0965Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (526404059596800 : Int) atom0966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497366134272000 : Int) atom0967Coded) (CoefficientMerge.scale (459588739276800 : Int) atom0968Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (431744082739200 : Int) atom0969Coded) (CoefficientMerge.scale (482321582265600 : Int) atom0970Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377204281977600 : Int) atom0971Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (524931329260800 : Int) atom0972Coded) (CoefficientMerge.scale (405394404307200 : Int) atom0973Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (429382919750400 : Int) atom0974Coded) (CoefficientMerge.scale (486104821171200 : Int) atom0975Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283933862150400 : Int) atom0976Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (525551462150400 : Int) atom0977Coded) (CoefficientMerge.scale (479630587564800 : Int) atom0978Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (443642451436800 : Int) atom0979Coded) (CoefficientMerge.scale (472704538521600 : Int) atom0980Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375370378336800 : Int) atom0981Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (521437841971200 : Int) atom0982Coded) (CoefficientMerge.scale (404962695244800 : Int) atom0983Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (411634200146400 : Int) atom0984Coded) (CoefficientMerge.scale (463618871100000 : Int) atom0985Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (291966841958400 : Int) atom0986Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (515495981952000 : Int) atom0987Coded) (CoefficientMerge.scale (470343773491200 : Int) atom0988Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (492661507968000 : Int) atom0989Coded) (CoefficientMerge.scale (379248139468800 : Int) atom0990Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (547518367872000 : Int) atom0991Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (434104999372800 : Int) atom0992Coded) (CoefficientMerge.scale (373035023424000 : Int) atom0993Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (415072942099200 : Int) atom0994Coded) (CoefficientMerge.scale (276961422528000 : Int) atom0995Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (495502930944000 : Int) atom0996Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488973456921600 : Int) atom0997Coded) (CoefficientMerge.scale (378621866649600 : Int) atom0998Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (549953873280000 : Int) atom0999Coded) (CoefficientMerge.scale (439602283008000 : Int) atom1000Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (323801088307200 : Int) atom1001Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (445435576185600 : Int) atom1002Coded) (CoefficientMerge.scale (267182675020800 : Int) atom1003Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (505150882790400 : Int) atom1004Coded) (CoefficientMerge.scale (397861070745600 : Int) atom1005Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (572254855603200 : Int) atom1006Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (464965043558400 : Int) atom1007Coded) (CoefficientMerge.scale (351101944166400 : Int) atom1008Coded))))))))) := by
  rw [block014_data_flat159_step, block014_data_flat158_original]
theorem block014_data : block014 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (403961087933568 : Int) atom0929Coded) (CoefficientMerge.scale (381526078906368 : Int) atom0930Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (373878076474368 : Int) atom0931Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (354407563795968 : Int) atom0932Coded) (CoefficientMerge.scale (344869789575168 : Int) atom0933Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (379974615939072 : Int) atom0934Coded) (CoefficientMerge.scale (329477914529280 : Int) atom0935Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (419823011570688 : Int) atom0936Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (399350123656704 : Int) atom0937Coded) (CoefficientMerge.scale (445024402859520 : Int) atom0938Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (523432068039936 : Int) atom0939Coded) (CoefficientMerge.scale (247082976765504 : Int) atom0940Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (484045607060928 : Int) atom0941Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (457120118911104 : Int) atom0942Coded) (CoefficientMerge.scale (426520367944704 : Int) atom0943Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (410707623573504 : Int) atom0944Coded) (CoefficientMerge.scale (386155409531904 : Int) atom0945Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (371535933947904 : Int) atom0946Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413692392979008 : Int) atom0947Coded) (CoefficientMerge.scale (347494413911040 : Int) atom0948Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (444055027065408 : Int) atom0949Coded) (CoefficientMerge.scale (410230735782912 : Int) atom0950Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (452841657269760 : Int) atom0951Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (528185964734208 : Int) atom0952Coded) (CoefficientMerge.scale (284228831677824 : Int) atom0953Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (526699029124224 : Int) atom0954Coded) (CoefficientMerge.scale (493080024628224 : Int) atom0955Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (474248026727424 : Int) atom0956Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (443593518580224 : Int) atom0957Coded) (CoefficientMerge.scale (422871748890624 : Int) atom0958Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (484590100376448 : Int) atom0959Coded) (CoefficientMerge.scale (377389276323840 : Int) atom0960Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (521076290917248 : Int) atom0961Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (409448281347072 : Int) atom0962Coded) (CoefficientMerge.scale (433641756303360 : Int) atom0963Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (490568617237248 : Int) atom0964Coded) (CoefficientMerge.scale (289736398828800 : Int) atom0965Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (526404059596800 : Int) atom0966Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (497366134272000 : Int) atom0967Coded) (CoefficientMerge.scale (459588739276800 : Int) atom0968Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (431744082739200 : Int) atom0969Coded) (CoefficientMerge.scale (482321582265600 : Int) atom0970Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377204281977600 : Int) atom0971Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (524931329260800 : Int) atom0972Coded) (CoefficientMerge.scale (405394404307200 : Int) atom0973Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (429382919750400 : Int) atom0974Coded) (CoefficientMerge.scale (486104821171200 : Int) atom0975Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (283933862150400 : Int) atom0976Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (525551462150400 : Int) atom0977Coded) (CoefficientMerge.scale (479630587564800 : Int) atom0978Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (443642451436800 : Int) atom0979Coded) (CoefficientMerge.scale (472704538521600 : Int) atom0980Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (375370378336800 : Int) atom0981Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (521437841971200 : Int) atom0982Coded) (CoefficientMerge.scale (404962695244800 : Int) atom0983Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (411634200146400 : Int) atom0984Coded) (CoefficientMerge.scale (463618871100000 : Int) atom0985Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (291966841958400 : Int) atom0986Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (515495981952000 : Int) atom0987Coded) (CoefficientMerge.scale (470343773491200 : Int) atom0988Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (492661507968000 : Int) atom0989Coded) (CoefficientMerge.scale (379248139468800 : Int) atom0990Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (547518367872000 : Int) atom0991Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (434104999372800 : Int) atom0992Coded) (CoefficientMerge.scale (373035023424000 : Int) atom0993Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (415072942099200 : Int) atom0994Coded) (CoefficientMerge.scale (276961422528000 : Int) atom0995Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (495502930944000 : Int) atom0996Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (488973456921600 : Int) atom0997Coded) (CoefficientMerge.scale (378621866649600 : Int) atom0998Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (549953873280000 : Int) atom0999Coded) (CoefficientMerge.scale (439602283008000 : Int) atom1000Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (323801088307200 : Int) atom1001Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (445435576185600 : Int) atom1002Coded) (CoefficientMerge.scale (267182675020800 : Int) atom1003Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (505150882790400 : Int) atom1004Coded) (CoefficientMerge.scale (397861070745600 : Int) atom1005Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (572254855603200 : Int) atom1006Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (464965043558400 : Int) atom1007Coded) (CoefficientMerge.scale (351101944166400 : Int) atom1008Coded)))))))) := by
  have h : block014 = block014_data_flat159 := by decide +kernel
  exact h.trans block014_data_flat159_original
theorem block014_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block014 := by
  rw [block014_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0929Coded_nonneg g hg hA hB) (atom0930Coded_nonneg g hg hA hB)) (add_nonneg (atom0931Coded_nonneg g hg hA hB) (add_nonneg (atom0932Coded_nonneg g hg hA hB) (atom0933Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0934Coded_nonneg g hg hA hB) (atom0935Coded_nonneg g hg hA hB)) (add_nonneg (atom0936Coded_nonneg g hg hA hB) (add_nonneg (atom0937Coded_nonneg g hg hA hB) (atom0938Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0939Coded_nonneg g hg hA hB) (atom0940Coded_nonneg g hg hA hB)) (add_nonneg (atom0941Coded_nonneg g hg hA hB) (add_nonneg (atom0942Coded_nonneg g hg hA hB) (atom0943Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0944Coded_nonneg g hg hA hB) (atom0945Coded_nonneg g hg hA hB)) (add_nonneg (atom0946Coded_nonneg g hg hA hB) (add_nonneg (atom0947Coded_nonneg g hg hA hB) (atom0948Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0949Coded_nonneg g hg hA hB) (atom0950Coded_nonneg g hg hA hB)) (add_nonneg (atom0951Coded_nonneg g hg hA hB) (add_nonneg (atom0952Coded_nonneg g hg hA hB) (atom0953Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0954Coded_nonneg g hg hA hB) (atom0955Coded_nonneg g hg hA hB)) (add_nonneg (atom0956Coded_nonneg g hg hA hB) (add_nonneg (atom0957Coded_nonneg g hg hA hB) (atom0958Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0959Coded_nonneg g hg hA hB) (atom0960Coded_nonneg g hg hA hB)) (add_nonneg (atom0961Coded_nonneg g hg hA hB) (add_nonneg (atom0962Coded_nonneg g hg hA hB) (atom0963Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0964Coded_nonneg g hg hA hB) (atom0965Coded_nonneg g hg hA hB)) (add_nonneg (atom0966Coded_nonneg g hg hA hB) (add_nonneg (atom0967Coded_nonneg g hg hA hB) (atom0968Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0969Coded_nonneg g hg hA hB) (atom0970Coded_nonneg g hg hA hB)) (add_nonneg (atom0971Coded_nonneg g hg hA hB) (add_nonneg (atom0972Coded_nonneg g hg hA hB) (atom0973Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0974Coded_nonneg g hg hA hB) (atom0975Coded_nonneg g hg hA hB)) (add_nonneg (atom0976Coded_nonneg g hg hA hB) (add_nonneg (atom0977Coded_nonneg g hg hA hB) (atom0978Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0979Coded_nonneg g hg hA hB) (atom0980Coded_nonneg g hg hA hB)) (add_nonneg (atom0981Coded_nonneg g hg hA hB) (add_nonneg (atom0982Coded_nonneg g hg hA hB) (atom0983Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0984Coded_nonneg g hg hA hB) (atom0985Coded_nonneg g hg hA hB)) (add_nonneg (atom0986Coded_nonneg g hg hA hB) (add_nonneg (atom0987Coded_nonneg g hg hA hB) (atom0988Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0989Coded_nonneg g hg hA hB) (atom0990Coded_nonneg g hg hA hB)) (add_nonneg (atom0991Coded_nonneg g hg hA hB) (add_nonneg (atom0992Coded_nonneg g hg hA hB) (atom0993Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0994Coded_nonneg g hg hA hB) (atom0995Coded_nonneg g hg hA hB)) (add_nonneg (atom0996Coded_nonneg g hg hA hB) (add_nonneg (atom0997Coded_nonneg g hg hA hB) (atom0998Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0999Coded_nonneg g hg hA hB) (atom1000Coded_nonneg g hg hA hB)) (add_nonneg (atom1001Coded_nonneg g hg hA hB) (add_nonneg (atom1002Coded_nonneg g hg hA hB) (atom1003Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1004Coded_nonneg g hg hA hB) (atom1005Coded_nonneg g hg hA hB)) (add_nonneg (atom1006Coded_nonneg g hg hA hB) (add_nonneg (atom1007Coded_nonneg g hg hA hB) (atom1008Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
