-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1056 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1056 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1056 = ((g 4) * (g 16) * (g 19)) := by
  norm_num [atom1056, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1056_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40297587372000 : Int) atom1056) := by
  rw [SparsePolynomial.eval_scale, eval_atom1056]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1056Coded : CoefficientMerge.Poly := [(nat_lit 2119, Int.ofNat (nat_lit 1))]
theorem atom1056Coded_decode : atom1056 = SparsePolynomial.decodeCubic 21 atom1056Coded := by decide +kernel
theorem atom1056Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40297587372000 : Int) atom1056Coded) := by
  have h := atom1056_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1056Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1057 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1057 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1057 = ((g 4) * (g 16) * (g 20)) := by
  norm_num [atom1057, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1057_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45912704890500 : Int) atom1057) := by
  rw [SparsePolynomial.eval_scale, eval_atom1057]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1057Coded : CoefficientMerge.Poly := [(nat_lit 2120, Int.ofNat (nat_lit 1))]
theorem atom1057Coded_decode : atom1057 = SparsePolynomial.decodeCubic 21 atom1057Coded := by decide +kernel
theorem atom1057Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (45912704890500 : Int) atom1057Coded) := by
  have h := atom1057_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1057Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1058 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1058 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1058 = ((g 4) * (g 17) * (g 17)) := by
  norm_num [atom1058, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1058_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39243222144000 : Int) atom1058) := by
  rw [SparsePolynomial.eval_scale, eval_atom1058]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1058Coded : CoefficientMerge.Poly := [(nat_lit 2138, Int.ofNat (nat_lit 1))]
theorem atom1058Coded_decode : atom1058 = SparsePolynomial.decodeCubic 21 atom1058Coded := by decide +kernel
theorem atom1058Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39243222144000 : Int) atom1058Coded) := by
  have h := atom1058_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1058Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1059 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1059 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1059 = ((g 4) * (g 17) * (g 18)) := by
  norm_num [atom1059, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1059_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60042692026800 : Int) atom1059) := by
  rw [SparsePolynomial.eval_scale, eval_atom1059]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1059Coded : CoefficientMerge.Poly := [(nat_lit 2139, Int.ofNat (nat_lit 1))]
theorem atom1059Coded_decode : atom1059 = SparsePolynomial.decodeCubic 21 atom1059Coded := by decide +kernel
theorem atom1059Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (60042692026800 : Int) atom1059Coded) := by
  have h := atom1059_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1059Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1060 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1060 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1060 = ((g 4) * (g 17) * (g 19)) := by
  norm_num [atom1060, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1060_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42753122622000 : Int) atom1060) := by
  rw [SparsePolynomial.eval_scale, eval_atom1060]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1060Coded : CoefficientMerge.Poly := [(nat_lit 2140, Int.ofNat (nat_lit 1))]
theorem atom1060Coded_decode : atom1060 = SparsePolynomial.decodeCubic 21 atom1060Coded := by decide +kernel
theorem atom1060Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42753122622000 : Int) atom1060Coded) := by
  have h := atom1060_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1060Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1061 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1061 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1061 = ((g 4) * (g 17) * (g 20)) := by
  norm_num [atom1061, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1061_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53503172881200 : Int) atom1061) := by
  rw [SparsePolynomial.eval_scale, eval_atom1061]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1061Coded : CoefficientMerge.Poly := [(nat_lit 2141, Int.ofNat (nat_lit 1))]
theorem atom1061Coded_decode : atom1061 = SparsePolynomial.decodeCubic 21 atom1061Coded := by decide +kernel
theorem atom1061Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53503172881200 : Int) atom1061Coded) := by
  have h := atom1061_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1061Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1062 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1062 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1062 = ((g 4) * (g 18) * (g 18)) := by
  norm_num [atom1062, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1062_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16441201816200 : Int) atom1062) := by
  rw [SparsePolynomial.eval_scale, eval_atom1062]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1062Coded : CoefficientMerge.Poly := [(nat_lit 2160, Int.ofNat (nat_lit 1))]
theorem atom1062Coded_decode : atom1062 = SparsePolynomial.decodeCubic 21 atom1062Coded := by decide +kernel
theorem atom1062Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16441201816200 : Int) atom1062Coded) := by
  have h := atom1062_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1062Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1063 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1063 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1063 = ((g 4) * (g 18) * (g 19)) := by
  norm_num [atom1063, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1063_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21090286866600 : Int) atom1063) := by
  rw [SparsePolynomial.eval_scale, eval_atom1063]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1063Coded : CoefficientMerge.Poly := [(nat_lit 2161, Int.ofNat (nat_lit 1))]
theorem atom1063Coded_decode : atom1063 = SparsePolynomial.decodeCubic 21 atom1063Coded := by decide +kernel
theorem atom1063Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21090286866600 : Int) atom1063Coded) := by
  have h := atom1063_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1063Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1064 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1064 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1064 = ((g 4) * (g 18) * (g 20)) := by
  norm_num [atom1064, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1064_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31933858238100 : Int) atom1064) := by
  rw [SparsePolynomial.eval_scale, eval_atom1064]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1064Coded : CoefficientMerge.Poly := [(nat_lit 2162, Int.ofNat (nat_lit 1))]
theorem atom1064Coded_decode : atom1064 = SparsePolynomial.decodeCubic 21 atom1064Coded := by decide +kernel
theorem atom1064Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31933858238100 : Int) atom1064Coded) := by
  have h := atom1064_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1064Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1065 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1065 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1065 = ((g 4) * (g 19) * (g 20)) := by
  norm_num [atom1065, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1065_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8021538207900 : Int) atom1065) := by
  rw [SparsePolynomial.eval_scale, eval_atom1065]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1065Coded : CoefficientMerge.Poly := [(nat_lit 2183, Int.ofNat (nat_lit 1))]
theorem atom1065Coded_decode : atom1065 = SparsePolynomial.decodeCubic 21 atom1065Coded := by decide +kernel
theorem atom1065Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8021538207900 : Int) atom1065Coded) := by
  have h := atom1065_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1065Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1066 : SparsePolynomial.Poly := [([nat_lit 4, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1066 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1066 = ((g 4) * (g 20) * (g 20)) := by
  norm_num [atom1066, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1066_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10915331798700 : Int) atom1066) := by
  rw [SparsePolynomial.eval_scale, eval_atom1066]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1066Coded : CoefficientMerge.Poly := [(nat_lit 2204, Int.ofNat (nat_lit 1))]
theorem atom1066Coded_decode : atom1066 = SparsePolynomial.decodeCubic 21 atom1066Coded := by decide +kernel
theorem atom1066Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10915331798700 : Int) atom1066Coded) := by
  have h := atom1066_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1066Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1067 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 5], Int.ofNat (nat_lit 1))]
theorem eval_atom1067 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1067 = ((g 5) * (g 5) * (g 5)) := by
  norm_num [atom1067, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1067_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2384168341248 : Int) atom1067) := by
  rw [SparsePolynomial.eval_scale, eval_atom1067]
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 5) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1067Coded : CoefficientMerge.Poly := [(nat_lit 2315, Int.ofNat (nat_lit 1))]
theorem atom1067Coded_decode : atom1067 = SparsePolynomial.decodeCubic 21 atom1067Coded := by decide +kernel
theorem atom1067Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2384168341248 : Int) atom1067Coded) := by
  have h := atom1067_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1067Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1068 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom1068 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1068 = ((g 5) * (g 5) * (g 6)) := by
  norm_num [atom1068, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1068_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5099671524096 : Int) atom1068) := by
  rw [SparsePolynomial.eval_scale, eval_atom1068]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1068Coded : CoefficientMerge.Poly := [(nat_lit 2316, Int.ofNat (nat_lit 1))]
theorem atom1068Coded_decode : atom1068 = SparsePolynomial.decodeCubic 21 atom1068Coded := by decide +kernel
theorem atom1068Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5099671524096 : Int) atom1068Coded) := by
  have h := atom1068_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1068Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1069 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1069 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1069 = ((g 5) * (g 5) * (g 7)) := by
  norm_num [atom1069, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1069_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (475114087296 : Int) atom1069) := by
  rw [SparsePolynomial.eval_scale, eval_atom1069]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1069Coded : CoefficientMerge.Poly := [(nat_lit 2317, Int.ofNat (nat_lit 1))]
theorem atom1069Coded_decode : atom1069 = SparsePolynomial.decodeCubic 21 atom1069Coded := by decide +kernel
theorem atom1069Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (475114087296 : Int) atom1069Coded) := by
  have h := atom1069_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1069Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1070 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1070 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1070 = ((g 5) * (g 5) * (g 9)) := by
  norm_num [atom1070, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1070_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1116273312000 : Int) atom1070) := by
  rw [SparsePolynomial.eval_scale, eval_atom1070]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1070Coded : CoefficientMerge.Poly := [(nat_lit 2319, Int.ofNat (nat_lit 1))]
theorem atom1070Coded_decode : atom1070 = SparsePolynomial.decodeCubic 21 atom1070Coded := by decide +kernel
theorem atom1070Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1116273312000 : Int) atom1070Coded) := by
  have h := atom1070_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1070Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1071 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1071 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1071 = ((g 5) * (g 5) * (g 10)) := by
  norm_num [atom1071, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1071_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (773176320000 : Int) atom1071) := by
  rw [SparsePolynomial.eval_scale, eval_atom1071]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1071Coded : CoefficientMerge.Poly := [(nat_lit 2320, Int.ofNat (nat_lit 1))]
theorem atom1071Coded_decode : atom1071 = SparsePolynomial.decodeCubic 21 atom1071Coded := by decide +kernel
theorem atom1071Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (773176320000 : Int) atom1071Coded) := by
  have h := atom1071_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1071Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1072 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1072 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1072 = ((g 5) * (g 5) * (g 11)) := by
  norm_num [atom1072, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1072_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (847840896000 : Int) atom1072) := by
  rw [SparsePolynomial.eval_scale, eval_atom1072]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1072Coded : CoefficientMerge.Poly := [(nat_lit 2321, Int.ofNat (nat_lit 1))]
theorem atom1072Coded_decode : atom1072 = SparsePolynomial.decodeCubic 21 atom1072Coded := by decide +kernel
theorem atom1072Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (847840896000 : Int) atom1072Coded) := by
  have h := atom1072_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1072Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1073 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1073 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1073 = ((g 5) * (g 5) * (g 12)) := by
  norm_num [atom1073, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1073_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (261913478400 : Int) atom1073) := by
  rw [SparsePolynomial.eval_scale, eval_atom1073]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1073Coded : CoefficientMerge.Poly := [(nat_lit 2322, Int.ofNat (nat_lit 1))]
theorem atom1073Coded_decode : atom1073 = SparsePolynomial.decodeCubic 21 atom1073Coded := by decide +kernel
theorem atom1073Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (261913478400 : Int) atom1073Coded) := by
  have h := atom1073_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1073Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1074 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 5, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1074 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1074 = ((g 5) * (g 5) * (g 15)) := by
  norm_num [atom1074, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1074_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3749450450688 : Int) atom1074) := by
  rw [SparsePolynomial.eval_scale, eval_atom1074]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1074Coded : CoefficientMerge.Poly := [(nat_lit 2325, Int.ofNat (nat_lit 1))]
theorem atom1074Coded_decode : atom1074 = SparsePolynomial.decodeCubic 21 atom1074Coded := by decide +kernel
theorem atom1074Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3749450450688 : Int) atom1074Coded) := by
  have h := atom1074_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1074Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1075 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom1075 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1075 = ((g 5) * (g 6) * (g 6)) := by
  norm_num [atom1075, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1075_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7321536603648 : Int) atom1075) := by
  rw [SparsePolynomial.eval_scale, eval_atom1075]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1075Coded : CoefficientMerge.Poly := [(nat_lit 2337, Int.ofNat (nat_lit 1))]
theorem atom1075Coded_decode : atom1075 = SparsePolynomial.decodeCubic 21 atom1075Coded := by decide +kernel
theorem atom1075Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7321536603648 : Int) atom1075Coded) := by
  have h := atom1075_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1075Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1076 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1076 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1076 = ((g 5) * (g 6) * (g 7)) := by
  norm_num [atom1076, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1076_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5911986468096 : Int) atom1076) := by
  rw [SparsePolynomial.eval_scale, eval_atom1076]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1076Coded : CoefficientMerge.Poly := [(nat_lit 2338, Int.ofNat (nat_lit 1))]
theorem atom1076Coded_decode : atom1076 = SparsePolynomial.decodeCubic 21 atom1076Coded := by decide +kernel
theorem atom1076Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5911986468096 : Int) atom1076Coded) := by
  have h := atom1076_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1076Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1077 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1077 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1077 = ((g 5) * (g 6) * (g 8)) := by
  norm_num [atom1077, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1077_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1501404912000 : Int) atom1077) := by
  rw [SparsePolynomial.eval_scale, eval_atom1077]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1077Coded : CoefficientMerge.Poly := [(nat_lit 2339, Int.ofNat (nat_lit 1))]
theorem atom1077Coded_decode : atom1077 = SparsePolynomial.decodeCubic 21 atom1077Coded := by decide +kernel
theorem atom1077Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1501404912000 : Int) atom1077Coded) := by
  have h := atom1077_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1077Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1078 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1078 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1078 = ((g 5) * (g 6) * (g 11)) := by
  norm_num [atom1078, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1078_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (158747500800 : Int) atom1078) := by
  rw [SparsePolynomial.eval_scale, eval_atom1078]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1078Coded : CoefficientMerge.Poly := [(nat_lit 2342, Int.ofNat (nat_lit 1))]
theorem atom1078Coded_decode : atom1078 = SparsePolynomial.decodeCubic 21 atom1078Coded := by decide +kernel
theorem atom1078Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (158747500800 : Int) atom1078Coded) := by
  have h := atom1078_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1078Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1079 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1079 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1079 = ((g 5) * (g 6) * (g 13)) := by
  norm_num [atom1079, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1079_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (165266438400 : Int) atom1079) := by
  rw [SparsePolynomial.eval_scale, eval_atom1079]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1079Coded : CoefficientMerge.Poly := [(nat_lit 2344, Int.ofNat (nat_lit 1))]
theorem atom1079Coded_decode : atom1079 = SparsePolynomial.decodeCubic 21 atom1079Coded := by decide +kernel
theorem atom1079Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (165266438400 : Int) atom1079Coded) := by
  have h := atom1079_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1079Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1080 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1080 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1080 = ((g 5) * (g 6) * (g 14)) := by
  norm_num [atom1080, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1080_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (592446355200 : Int) atom1080) := by
  rw [SparsePolynomial.eval_scale, eval_atom1080]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1080Coded : CoefficientMerge.Poly := [(nat_lit 2345, Int.ofNat (nat_lit 1))]
theorem atom1080Coded_decode : atom1080 = SparsePolynomial.decodeCubic 21 atom1080Coded := by decide +kernel
theorem atom1080Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (592446355200 : Int) atom1080Coded) := by
  have h := atom1080_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1080Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1081 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1081 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1081 = ((g 5) * (g 6) * (g 15)) := by
  norm_num [atom1081, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1081_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7715209569408 : Int) atom1081) := by
  rw [SparsePolynomial.eval_scale, eval_atom1081]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1081Coded : CoefficientMerge.Poly := [(nat_lit 2346, Int.ofNat (nat_lit 1))]
theorem atom1081Coded_decode : atom1081 = SparsePolynomial.decodeCubic 21 atom1081Coded := by decide +kernel
theorem atom1081Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7715209569408 : Int) atom1081Coded) := by
  have h := atom1081_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1081Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1082 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1082 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1082 = ((g 5) * (g 6) * (g 17)) := by
  norm_num [atom1082, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1082_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (666940934016 : Int) atom1082) := by
  rw [SparsePolynomial.eval_scale, eval_atom1082]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1082Coded : CoefficientMerge.Poly := [(nat_lit 2348, Int.ofNat (nat_lit 1))]
theorem atom1082Coded_decode : atom1082 = SparsePolynomial.decodeCubic 21 atom1082Coded := by decide +kernel
theorem atom1082Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (666940934016 : Int) atom1082Coded) := by
  have h := atom1082_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1082Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1083 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1083 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1083 = ((g 5) * (g 6) * (g 18)) := by
  norm_num [atom1083, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1083_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5982693393600 : Int) atom1083) := by
  rw [SparsePolynomial.eval_scale, eval_atom1083]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1083Coded : CoefficientMerge.Poly := [(nat_lit 2349, Int.ofNat (nat_lit 1))]
theorem atom1083Coded_decode : atom1083 = SparsePolynomial.decodeCubic 21 atom1083Coded := by decide +kernel
theorem atom1083Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5982693393600 : Int) atom1083Coded) := by
  have h := atom1083_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1083Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1084 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1084 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1084 = ((g 5) * (g 6) * (g 19)) := by
  norm_num [atom1084, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1084_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11433151537920 : Int) atom1084) := by
  rw [SparsePolynomial.eval_scale, eval_atom1084]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1084Coded : CoefficientMerge.Poly := [(nat_lit 2350, Int.ofNat (nat_lit 1))]
theorem atom1084Coded_decode : atom1084 = SparsePolynomial.decodeCubic 21 atom1084Coded := by decide +kernel
theorem atom1084Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11433151537920 : Int) atom1084Coded) := by
  have h := atom1084_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1084Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1085 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 6, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1085 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1085 = ((g 5) * (g 6) * (g 20)) := by
  norm_num [atom1085, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1085_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17685804276000 : Int) atom1085) := by
  rw [SparsePolynomial.eval_scale, eval_atom1085]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1085Coded : CoefficientMerge.Poly := [(nat_lit 2351, Int.ofNat (nat_lit 1))]
theorem atom1085Coded_decode : atom1085 = SparsePolynomial.decodeCubic 21 atom1085Coded := by decide +kernel
theorem atom1085Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17685804276000 : Int) atom1085Coded) := by
  have h := atom1085_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1085Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1086 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1086 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1086 = ((g 5) * (g 7) * (g 7)) := by
  norm_num [atom1086, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1086_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2176055048448 : Int) atom1086) := by
  rw [SparsePolynomial.eval_scale, eval_atom1086]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1086Coded : CoefficientMerge.Poly := [(nat_lit 2359, Int.ofNat (nat_lit 1))]
theorem atom1086Coded_decode : atom1086 = SparsePolynomial.decodeCubic 21 atom1086Coded := by decide +kernel
theorem atom1086Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2176055048448 : Int) atom1086Coded) := by
  have h := atom1086_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1086Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1087 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1087 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1087 = ((g 5) * (g 7) * (g 8)) := by
  norm_num [atom1087, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1087_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (977584809600 : Int) atom1087) := by
  rw [SparsePolynomial.eval_scale, eval_atom1087]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1087Coded : CoefficientMerge.Poly := [(nat_lit 2360, Int.ofNat (nat_lit 1))]
theorem atom1087Coded_decode : atom1087 = SparsePolynomial.decodeCubic 21 atom1087Coded := by decide +kernel
theorem atom1087Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (977584809600 : Int) atom1087Coded) := by
  have h := atom1087_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1087Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1088 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1088 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1088 = ((g 5) * (g 7) * (g 11)) := by
  norm_num [atom1088, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1088_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (676775635200 : Int) atom1088) := by
  rw [SparsePolynomial.eval_scale, eval_atom1088]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1088Coded : CoefficientMerge.Poly := [(nat_lit 2363, Int.ofNat (nat_lit 1))]
theorem atom1088Coded_decode : atom1088 = SparsePolynomial.decodeCubic 21 atom1088Coded := by decide +kernel
theorem atom1088Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (676775635200 : Int) atom1088Coded) := by
  have h := atom1088_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1088Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1089 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1089 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1089 = ((g 5) * (g 7) * (g 12)) := by
  norm_num [atom1089, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1089_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (777042201600 : Int) atom1089) := by
  rw [SparsePolynomial.eval_scale, eval_atom1089]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1089Coded : CoefficientMerge.Poly := [(nat_lit 2364, Int.ofNat (nat_lit 1))]
theorem atom1089Coded_decode : atom1089 = SparsePolynomial.decodeCubic 21 atom1089Coded := by decide +kernel
theorem atom1089Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (777042201600 : Int) atom1089Coded) := by
  have h := atom1089_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1089Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1090 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1090 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1090 = ((g 5) * (g 7) * (g 13)) := by
  norm_num [atom1090, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1090_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1201322707200 : Int) atom1090) := by
  rw [SparsePolynomial.eval_scale, eval_atom1090]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1090Coded : CoefficientMerge.Poly := [(nat_lit 2365, Int.ofNat (nat_lit 1))]
theorem atom1090Coded_decode : atom1090 = SparsePolynomial.decodeCubic 21 atom1090Coded := by decide +kernel
theorem atom1090Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1201322707200 : Int) atom1090Coded) := by
  have h := atom1090_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1090Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1091 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1091 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1091 = ((g 5) * (g 7) * (g 14)) := by
  norm_num [atom1091, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1091_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1887516691200 : Int) atom1091) := by
  rw [SparsePolynomial.eval_scale, eval_atom1091]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1091Coded : CoefficientMerge.Poly := [(nat_lit 2366, Int.ofNat (nat_lit 1))]
theorem atom1091Coded_decode : atom1091 = SparsePolynomial.decodeCubic 21 atom1091Coded := by decide +kernel
theorem atom1091Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1887516691200 : Int) atom1091Coded) := by
  have h := atom1091_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1091Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1092 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1092 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1092 = ((g 5) * (g 7) * (g 15)) := by
  norm_num [atom1092, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1092_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11268696014208 : Int) atom1092) := by
  rw [SparsePolynomial.eval_scale, eval_atom1092]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1092Coded : CoefficientMerge.Poly := [(nat_lit 2367, Int.ofNat (nat_lit 1))]
theorem atom1092Coded_decode : atom1092 = SparsePolynomial.decodeCubic 21 atom1092Coded := by decide +kernel
theorem atom1092Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11268696014208 : Int) atom1092Coded) := by
  have h := atom1092_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1092Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1093 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1093 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1093 = ((g 5) * (g 7) * (g 16)) := by
  norm_num [atom1093, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1093_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7360279591680 : Int) atom1093) := by
  rw [SparsePolynomial.eval_scale, eval_atom1093]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1093Coded : CoefficientMerge.Poly := [(nat_lit 2368, Int.ofNat (nat_lit 1))]
theorem atom1093Coded_decode : atom1093 = SparsePolynomial.decodeCubic 21 atom1093Coded := by decide +kernel
theorem atom1093Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7360279591680 : Int) atom1093Coded) := by
  have h := atom1093_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1093Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1094 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1094 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1094 = ((g 5) * (g 7) * (g 17)) := by
  norm_num [atom1094, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1094_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12136953868416 : Int) atom1094) := by
  rw [SparsePolynomial.eval_scale, eval_atom1094]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1094Coded : CoefficientMerge.Poly := [(nat_lit 2369, Int.ofNat (nat_lit 1))]
theorem atom1094Coded_decode : atom1094 = SparsePolynomial.decodeCubic 21 atom1094Coded := by decide +kernel
theorem atom1094Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12136953868416 : Int) atom1094Coded) := by
  have h := atom1094_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1094Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1095 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1095 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1095 = ((g 5) * (g 7) * (g 18)) := by
  norm_num [atom1095, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1095_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18104289410880 : Int) atom1095) := by
  rw [SparsePolynomial.eval_scale, eval_atom1095]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1095Coded : CoefficientMerge.Poly := [(nat_lit 2370, Int.ofNat (nat_lit 1))]
theorem atom1095Coded_decode : atom1095 = SparsePolynomial.decodeCubic 21 atom1095Coded := by decide +kernel
theorem atom1095Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18104289410880 : Int) atom1095Coded) := by
  have h := atom1095_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1095Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1096 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1096 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1096 = ((g 5) * (g 7) * (g 19)) := by
  norm_num [atom1096, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1096_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25272405692928 : Int) atom1096) := by
  rw [SparsePolynomial.eval_scale, eval_atom1096]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1096Coded : CoefficientMerge.Poly := [(nat_lit 2371, Int.ofNat (nat_lit 1))]
theorem atom1096Coded_decode : atom1096 = SparsePolynomial.decodeCubic 21 atom1096Coded := by decide +kernel
theorem atom1096Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25272405692928 : Int) atom1096Coded) := by
  have h := atom1096_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1096Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1097 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 7, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1097 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1097 = ((g 5) * (g 7) * (g 20)) := by
  norm_num [atom1097, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1097_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32557609173600 : Int) atom1097) := by
  rw [SparsePolynomial.eval_scale, eval_atom1097]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1097Coded : CoefficientMerge.Poly := [(nat_lit 2372, Int.ofNat (nat_lit 1))]
theorem atom1097Coded_decode : atom1097 = SparsePolynomial.decodeCubic 21 atom1097Coded := by decide +kernel
theorem atom1097Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32557609173600 : Int) atom1097Coded) := by
  have h := atom1097_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1097Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1098 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1098 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1098 = ((g 5) * (g 8) * (g 8)) := by
  norm_num [atom1098, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1098_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2814314861952 : Int) atom1098) := by
  rw [SparsePolynomial.eval_scale, eval_atom1098]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1098Coded : CoefficientMerge.Poly := [(nat_lit 2381, Int.ofNat (nat_lit 1))]
theorem atom1098Coded_decode : atom1098 = SparsePolynomial.decodeCubic 21 atom1098Coded := by decide +kernel
theorem atom1098Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2814314861952 : Int) atom1098Coded) := by
  have h := atom1098_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1098Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1099 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1099 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1099 = ((g 5) * (g 8) * (g 9)) := by
  norm_num [atom1099, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1099_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4832741349504 : Int) atom1099) := by
  rw [SparsePolynomial.eval_scale, eval_atom1099]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1099Coded : CoefficientMerge.Poly := [(nat_lit 2382, Int.ofNat (nat_lit 1))]
theorem atom1099Coded_decode : atom1099 = SparsePolynomial.decodeCubic 21 atom1099Coded := by decide +kernel
theorem atom1099Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4832741349504 : Int) atom1099Coded) := by
  have h := atom1099_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1099Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1100 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1100 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1100 = ((g 5) * (g 8) * (g 10)) := by
  norm_num [atom1100, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1100_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4664575499904 : Int) atom1100) := by
  rw [SparsePolynomial.eval_scale, eval_atom1100]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1100Coded : CoefficientMerge.Poly := [(nat_lit 2383, Int.ofNat (nat_lit 1))]
theorem atom1100Coded_decode : atom1100 = SparsePolynomial.decodeCubic 21 atom1100Coded := by decide +kernel
theorem atom1100Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4664575499904 : Int) atom1100Coded) := by
  have h := atom1100_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1100Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1101 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1101 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1101 = ((g 5) * (g 8) * (g 11)) := by
  norm_num [atom1101, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1101_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5173185285504 : Int) atom1101) := by
  rw [SparsePolynomial.eval_scale, eval_atom1101]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1101Coded : CoefficientMerge.Poly := [(nat_lit 2384, Int.ofNat (nat_lit 1))]
theorem atom1101Coded_decode : atom1101 = SparsePolynomial.decodeCubic 21 atom1101Coded := by decide +kernel
theorem atom1101Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5173185285504 : Int) atom1101Coded) := by
  have h := atom1101_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1101Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1102 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1102 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1102 = ((g 5) * (g 8) * (g 12)) := by
  norm_num [atom1102, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1102_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4937120152704 : Int) atom1102) := by
  rw [SparsePolynomial.eval_scale, eval_atom1102]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1102Coded : CoefficientMerge.Poly := [(nat_lit 2385, Int.ofNat (nat_lit 1))]
theorem atom1102Coded_decode : atom1102 = SparsePolynomial.decodeCubic 21 atom1102Coded := by decide +kernel
theorem atom1102Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4937120152704 : Int) atom1102Coded) := by
  have h := atom1102_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1102Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1103 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1103 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1103 = ((g 5) * (g 8) * (g 13)) := by
  norm_num [atom1103, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1103_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5452248875904 : Int) atom1103) := by
  rw [SparsePolynomial.eval_scale, eval_atom1103]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1103Coded : CoefficientMerge.Poly := [(nat_lit 2386, Int.ofNat (nat_lit 1))]
theorem atom1103Coded_decode : atom1103 = SparsePolynomial.decodeCubic 21 atom1103Coded := by decide +kernel
theorem atom1103Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5452248875904 : Int) atom1103Coded) := by
  have h := atom1103_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1103Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1104 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1104 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1104 = ((g 5) * (g 8) * (g 14)) := by
  norm_num [atom1104, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1104_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6229291077504 : Int) atom1104) := by
  rw [SparsePolynomial.eval_scale, eval_atom1104]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1104Coded : CoefficientMerge.Poly := [(nat_lit 2387, Int.ofNat (nat_lit 1))]
theorem atom1104Coded_decode : atom1104 = SparsePolynomial.decodeCubic 21 atom1104Coded := by decide +kernel
theorem atom1104Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6229291077504 : Int) atom1104Coded) := by
  have h := atom1104_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1104Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1105 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1105 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1105 = ((g 5) * (g 8) * (g 15)) := by
  norm_num [atom1105, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1105_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15678311099904 : Int) atom1105) := by
  rw [SparsePolynomial.eval_scale, eval_atom1105]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1105Coded : CoefficientMerge.Poly := [(nat_lit 2388, Int.ofNat (nat_lit 1))]
theorem atom1105Coded_decode : atom1105 = SparsePolynomial.decodeCubic 21 atom1105Coded := by decide +kernel
theorem atom1105Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15678311099904 : Int) atom1105Coded) := by
  have h := atom1105_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1105Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1106 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1106 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1106 = ((g 5) * (g 8) * (g 16)) := by
  norm_num [atom1106, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1106_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13269277891440 : Int) atom1106) := by
  rw [SparsePolynomial.eval_scale, eval_atom1106]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1106Coded : CoefficientMerge.Poly := [(nat_lit 2389, Int.ofNat (nat_lit 1))]
theorem atom1106Coded_decode : atom1106 = SparsePolynomial.decodeCubic 21 atom1106Coded := by decide +kernel
theorem atom1106Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13269277891440 : Int) atom1106Coded) := by
  have h := atom1106_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1106Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1107 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1107 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1107 = ((g 5) * (g 8) * (g 17)) := by
  norm_num [atom1107, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1107_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19501256738304 : Int) atom1107) := by
  rw [SparsePolynomial.eval_scale, eval_atom1107]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1107Coded : CoefficientMerge.Poly := [(nat_lit 2390, Int.ofNat (nat_lit 1))]
theorem atom1107Coded_decode : atom1107 = SparsePolynomial.decodeCubic 21 atom1107Coded := by decide +kernel
theorem atom1107Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19501256738304 : Int) atom1107Coded) := by
  have h := atom1107_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1107Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1108 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1108 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1108 = ((g 5) * (g 8) * (g 18)) := by
  norm_num [atom1108, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1108_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25795167116112 : Int) atom1108) := by
  rw [SparsePolynomial.eval_scale, eval_atom1108]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1108Coded : CoefficientMerge.Poly := [(nat_lit 2391, Int.ofNat (nat_lit 1))]
theorem atom1108Coded_decode : atom1108 = SparsePolynomial.decodeCubic 21 atom1108Coded := by decide +kernel
theorem atom1108Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25795167116112 : Int) atom1108Coded) := by
  have h := atom1108_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1108Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1109 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1109 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1109 = ((g 5) * (g 8) * (g 19)) := by
  norm_num [atom1109, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1109_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33886745865360 : Int) atom1109) := by
  rw [SparsePolynomial.eval_scale, eval_atom1109]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1109Coded : CoefficientMerge.Poly := [(nat_lit 2392, Int.ofNat (nat_lit 1))]
theorem atom1109Coded_decode : atom1109 = SparsePolynomial.decodeCubic 21 atom1109Coded := by decide +kernel
theorem atom1109Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33886745865360 : Int) atom1109Coded) := by
  have h := atom1109_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1109Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1110 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 8, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1110 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1110 = ((g 5) * (g 8) * (g 20)) := by
  norm_num [atom1110, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1110_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41978324614608 : Int) atom1110) := by
  rw [SparsePolynomial.eval_scale, eval_atom1110]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1110Coded : CoefficientMerge.Poly := [(nat_lit 2393, Int.ofNat (nat_lit 1))]
theorem atom1110Coded_decode : atom1110 = SparsePolynomial.decodeCubic 21 atom1110Coded := by decide +kernel
theorem atom1110Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41978324614608 : Int) atom1110Coded) := by
  have h := atom1110_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1110Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1111 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1111 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1111 = ((g 5) * (g 9) * (g 9)) := by
  norm_num [atom1111, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1111_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6031211588352 : Int) atom1111) := by
  rw [SparsePolynomial.eval_scale, eval_atom1111]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1111Coded : CoefficientMerge.Poly := [(nat_lit 2403, Int.ofNat (nat_lit 1))]
theorem atom1111Coded_decode : atom1111 = SparsePolynomial.decodeCubic 21 atom1111Coded := by decide +kernel
theorem atom1111Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6031211588352 : Int) atom1111Coded) := by
  have h := atom1111_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1111Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1112 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1112 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1112 = ((g 5) * (g 9) * (g 10)) := by
  norm_num [atom1112, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1112_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10283151170304 : Int) atom1112) := by
  rw [SparsePolynomial.eval_scale, eval_atom1112]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1112Coded : CoefficientMerge.Poly := [(nat_lit 2404, Int.ofNat (nat_lit 1))]
theorem atom1112Coded_decode : atom1112 = SparsePolynomial.decodeCubic 21 atom1112Coded := by decide +kernel
theorem atom1112Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10283151170304 : Int) atom1112Coded) := by
  have h := atom1112_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1112Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1113 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1113 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1113 = ((g 5) * (g 9) * (g 11)) := by
  norm_num [atom1113, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1113_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10455429256704 : Int) atom1113) := by
  rw [SparsePolynomial.eval_scale, eval_atom1113]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1113Coded : CoefficientMerge.Poly := [(nat_lit 2405, Int.ofNat (nat_lit 1))]
theorem atom1113Coded_decode : atom1113 = SparsePolynomial.decodeCubic 21 atom1113Coded := by decide +kernel
theorem atom1113Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10455429256704 : Int) atom1113Coded) := by
  have h := atom1113_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1113Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1114 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1114 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1114 = ((g 5) * (g 9) * (g 12)) := by
  norm_num [atom1114, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1114_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10569226408704 : Int) atom1114) := by
  rw [SparsePolynomial.eval_scale, eval_atom1114]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1114Coded : CoefficientMerge.Poly := [(nat_lit 2406, Int.ofNat (nat_lit 1))]
theorem atom1114Coded_decode : atom1114 = SparsePolynomial.decodeCubic 21 atom1114Coded := by decide +kernel
theorem atom1114Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10569226408704 : Int) atom1114Coded) := by
  have h := atom1114_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1114Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1115 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1115 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1115 = ((g 5) * (g 9) * (g 13)) := by
  norm_num [atom1115, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1115_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11007037499904 : Int) atom1115) := by
  rw [SparsePolynomial.eval_scale, eval_atom1115]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1115Coded : CoefficientMerge.Poly := [(nat_lit 2407, Int.ofNat (nat_lit 1))]
theorem atom1115Coded_decode : atom1115 = SparsePolynomial.decodeCubic 21 atom1115Coded := by decide +kernel
theorem atom1115Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11007037499904 : Int) atom1115Coded) := by
  have h := atom1115_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1115Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1116 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1116 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1116 = ((g 5) * (g 9) * (g 14)) := by
  norm_num [atom1116, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1116_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11706762069504 : Int) atom1116) := by
  rw [SparsePolynomial.eval_scale, eval_atom1116]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1116Coded : CoefficientMerge.Poly := [(nat_lit 2408, Int.ofNat (nat_lit 1))]
theorem atom1116Coded_decode : atom1116 = SparsePolynomial.decodeCubic 21 atom1116Coded := by decide +kernel
theorem atom1116Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11706762069504 : Int) atom1116Coded) := by
  have h := atom1116_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1116Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1117 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1117 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1117 = ((g 5) * (g 9) * (g 15)) := by
  norm_num [atom1117, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1117_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20771126872704 : Int) atom1117) := by
  rw [SparsePolynomial.eval_scale, eval_atom1117]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1117Coded : CoefficientMerge.Poly := [(nat_lit 2409, Int.ofNat (nat_lit 1))]
theorem atom1117Coded_decode : atom1117 = SparsePolynomial.decodeCubic 21 atom1117Coded := by decide +kernel
theorem atom1117Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20771126872704 : Int) atom1117Coded) := by
  have h := atom1117_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1117Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1118 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1118 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1118 = ((g 5) * (g 9) * (g 16)) := by
  norm_num [atom1118, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1118_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18331227015840 : Int) atom1118) := by
  rw [SparsePolynomial.eval_scale, eval_atom1118]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1118Coded : CoefficientMerge.Poly := [(nat_lit 2410, Int.ofNat (nat_lit 1))]
theorem atom1118Coded_decode : atom1118 = SparsePolynomial.decodeCubic 21 atom1118Coded := by decide +kernel
theorem atom1118Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18331227015840 : Int) atom1118Coded) := by
  have h := atom1118_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1118Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1119 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1119 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1119 = ((g 5) * (g 9) * (g 17)) := by
  norm_num [atom1119, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1119_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25882377554304 : Int) atom1119) := by
  rw [SparsePolynomial.eval_scale, eval_atom1119]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1119Coded : CoefficientMerge.Poly := [(nat_lit 2411, Int.ofNat (nat_lit 1))]
theorem atom1119Coded_decode : atom1119 = SparsePolynomial.decodeCubic 21 atom1119Coded := by decide +kernel
theorem atom1119Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25882377554304 : Int) atom1119Coded) := by
  have h := atom1119_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1119Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1120 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1120 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1120 = ((g 5) * (g 9) * (g 18)) := by
  norm_num [atom1120, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1120_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31092814209312 : Int) atom1120) := by
  rw [SparsePolynomial.eval_scale, eval_atom1120]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1120Coded : CoefficientMerge.Poly := [(nat_lit 2412, Int.ofNat (nat_lit 1))]
theorem atom1120Coded_decode : atom1120 = SparsePolynomial.decodeCubic 21 atom1120Coded := by decide +kernel
theorem atom1120Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31092814209312 : Int) atom1120Coded) := by
  have h := atom1120_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1120Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1121 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1121 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1121 = ((g 5) * (g 9) * (g 19)) := by
  norm_num [atom1121, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1121_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39549718769760 : Int) atom1121) := by
  rw [SparsePolynomial.eval_scale, eval_atom1121]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1121Coded : CoefficientMerge.Poly := [(nat_lit 2413, Int.ofNat (nat_lit 1))]
theorem atom1121Coded_decode : atom1121 = SparsePolynomial.decodeCubic 21 atom1121Coded := by decide +kernel
theorem atom1121Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39549718769760 : Int) atom1121Coded) := by
  have h := atom1121_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1121Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1122 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 9, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1122 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1122 = ((g 5) * (g 9) * (g 20)) := by
  norm_num [atom1122, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1122_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48097833974208 : Int) atom1122) := by
  rw [SparsePolynomial.eval_scale, eval_atom1122]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1122Coded : CoefficientMerge.Poly := [(nat_lit 2414, Int.ofNat (nat_lit 1))]
theorem atom1122Coded_decode : atom1122 = SparsePolynomial.decodeCubic 21 atom1122Coded := by decide +kernel
theorem atom1122Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48097833974208 : Int) atom1122Coded) := by
  have h := atom1122_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1122Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1123 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1123 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1123 = ((g 5) * (g 10) * (g 10)) := by
  norm_num [atom1123, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1123_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8264724682752 : Int) atom1123) := by
  rw [SparsePolynomial.eval_scale, eval_atom1123]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1123Coded : CoefficientMerge.Poly := [(nat_lit 2425, Int.ofNat (nat_lit 1))]
theorem atom1123Coded_decode : atom1123 = SparsePolynomial.decodeCubic 21 atom1123Coded := by decide +kernel
theorem atom1123Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8264724682752 : Int) atom1123Coded) := by
  have h := atom1123_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1123Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1124 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1124 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1124 = ((g 5) * (g 10) * (g 11)) := by
  norm_num [atom1124, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1124_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15692732354304 : Int) atom1124) := by
  rw [SparsePolynomial.eval_scale, eval_atom1124]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1124Coded : CoefficientMerge.Poly := [(nat_lit 2426, Int.ofNat (nat_lit 1))]
theorem atom1124Coded_decode : atom1124 = SparsePolynomial.decodeCubic 21 atom1124Coded := by decide +kernel
theorem atom1124Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15692732354304 : Int) atom1124Coded) := by
  have h := atom1124_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1124Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1125 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1125 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1125 = ((g 5) * (g 10) * (g 12)) := by
  norm_num [atom1125, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1125_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15133866107904 : Int) atom1125) := by
  rw [SparsePolynomial.eval_scale, eval_atom1125]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1125Coded : CoefficientMerge.Poly := [(nat_lit 2427, Int.ofNat (nat_lit 1))]
theorem atom1125Coded_decode : atom1125 = SparsePolynomial.decodeCubic 21 atom1125Coded := by decide +kernel
theorem atom1125Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15133866107904 : Int) atom1125Coded) := by
  have h := atom1125_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1125Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1126 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1126 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1126 = ((g 5) * (g 10) * (g 13)) := by
  norm_num [atom1126, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1126_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15326193717504 : Int) atom1126) := by
  rw [SparsePolynomial.eval_scale, eval_atom1126]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1126Coded : CoefficientMerge.Poly := [(nat_lit 2428, Int.ofNat (nat_lit 1))]
theorem atom1126Coded_decode : atom1126 = SparsePolynomial.decodeCubic 21 atom1126Coded := by decide +kernel
theorem atom1126Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15326193717504 : Int) atom1126Coded) := by
  have h := atom1126_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1126Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1127 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1127 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1127 = ((g 5) * (g 10) * (g 14)) := by
  norm_num [atom1127, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1127_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15780434805504 : Int) atom1127) := by
  rw [SparsePolynomial.eval_scale, eval_atom1127]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1127Coded : CoefficientMerge.Poly := [(nat_lit 2429, Int.ofNat (nat_lit 1))]
theorem atom1127Coded_decode : atom1127 = SparsePolynomial.decodeCubic 21 atom1127Coded := by decide +kernel
theorem atom1127Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15780434805504 : Int) atom1127Coded) := by
  have h := atom1127_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1127Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1128 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1128 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1128 = ((g 5) * (g 10) * (g 15)) := by
  norm_num [atom1128, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1128_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25134257493504 : Int) atom1128) := by
  rw [SparsePolynomial.eval_scale, eval_atom1128]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1128Coded : CoefficientMerge.Poly := [(nat_lit 2430, Int.ofNat (nat_lit 1))]
theorem atom1128Coded_decode : atom1128 = SparsePolynomial.decodeCubic 21 atom1128Coded := by decide +kernel
theorem atom1128Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25134257493504 : Int) atom1128Coded) := by
  have h := atom1128_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1128Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1129 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1129 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1129 = ((g 5) * (g 10) * (g 16)) := by
  norm_num [atom1129, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1129_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22912538329440 : Int) atom1129) := by
  rw [SparsePolynomial.eval_scale, eval_atom1129]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1129Coded : CoefficientMerge.Poly := [(nat_lit 2431, Int.ofNat (nat_lit 1))]
theorem atom1129Coded_decode : atom1129 = SparsePolynomial.decodeCubic 21 atom1129Coded := by decide +kernel
theorem atom1129Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22912538329440 : Int) atom1129Coded) := by
  have h := atom1129_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1129Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1130 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1130 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1130 = ((g 5) * (g 10) * (g 17)) := by
  norm_num [atom1130, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1130_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32993183522304 : Int) atom1130) := by
  rw [SparsePolynomial.eval_scale, eval_atom1130]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1130Coded : CoefficientMerge.Poly := [(nat_lit 2432, Int.ofNat (nat_lit 1))]
theorem atom1130Coded_decode : atom1130 = SparsePolynomial.decodeCubic 21 atom1130Coded := by decide +kernel
theorem atom1130Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32993183522304 : Int) atom1130Coded) := by
  have h := atom1130_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1130Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1131 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1131 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1131 = ((g 5) * (g 10) * (g 18)) := by
  norm_num [atom1131, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1131_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36268263201312 : Int) atom1131) := by
  rw [SparsePolynomial.eval_scale, eval_atom1131]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1131Coded : CoefficientMerge.Poly := [(nat_lit 2433, Int.ofNat (nat_lit 1))]
theorem atom1131Coded_decode : atom1131 = SparsePolynomial.decodeCubic 21 atom1131Coded := by decide +kernel
theorem atom1131Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36268263201312 : Int) atom1131Coded) := by
  have h := atom1131_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1131Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1132 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1132 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1132 = ((g 5) * (g 10) * (g 19)) := by
  norm_num [atom1132, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1132_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45020666086560 : Int) atom1132) := by
  rw [SparsePolynomial.eval_scale, eval_atom1132]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1132Coded : CoefficientMerge.Poly := [(nat_lit 2434, Int.ofNat (nat_lit 1))]
theorem atom1132Coded_decode : atom1132 = SparsePolynomial.decodeCubic 21 atom1132Coded := by decide +kernel
theorem atom1132Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (45020666086560 : Int) atom1132Coded) := by
  have h := atom1132_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1132Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1133 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1133 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1133 = ((g 5) * (g 10) * (g 20)) := by
  norm_num [atom1133, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1133_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53773068971808 : Int) atom1133) := by
  rw [SparsePolynomial.eval_scale, eval_atom1133]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1133Coded : CoefficientMerge.Poly := [(nat_lit 2435, Int.ofNat (nat_lit 1))]
theorem atom1133Coded_decode : atom1133 = SparsePolynomial.decodeCubic 21 atom1133Coded := by decide +kernel
theorem atom1133Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53773068971808 : Int) atom1133Coded) := by
  have h := atom1133_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1133Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1134 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1134 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1134 = ((g 5) * (g 11) * (g 11)) := by
  norm_num [atom1134, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1134_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11440792772352 : Int) atom1134) := by
  rw [SparsePolynomial.eval_scale, eval_atom1134]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1134Coded : CoefficientMerge.Poly := [(nat_lit 2447, Int.ofNat (nat_lit 1))]
theorem atom1134Coded_decode : atom1134 = SparsePolynomial.decodeCubic 21 atom1134Coded := by decide +kernel
theorem atom1134Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11440792772352 : Int) atom1134Coded) := by
  have h := atom1134_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1134Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1135 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1135 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1135 = ((g 5) * (g 11) * (g 12)) := by
  norm_num [atom1135, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1135_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20459364367104 : Int) atom1135) := by
  rw [SparsePolynomial.eval_scale, eval_atom1135]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1135Coded : CoefficientMerge.Poly := [(nat_lit 2448, Int.ofNat (nat_lit 1))]
theorem atom1135Coded_decode : atom1135 = SparsePolynomial.decodeCubic 21 atom1135Coded := by decide +kernel
theorem atom1135Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20459364367104 : Int) atom1135Coded) := by
  have h := atom1135_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1135Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block015 : CoefficientMerge.Poly := [(nat_lit 2119, Int.ofNat (nat_lit 40297587372000)), (nat_lit 2120, Int.ofNat (nat_lit 45912704890500)), (nat_lit 2138, Int.ofNat (nat_lit 39243222144000)), (nat_lit 2139, Int.ofNat (nat_lit 60042692026800)), (nat_lit 2140, Int.ofNat (nat_lit 42753122622000)), (nat_lit 2141, Int.ofNat (nat_lit 53503172881200)), (nat_lit 2160, Int.ofNat (nat_lit 16441201816200)), (nat_lit 2161, Int.ofNat (nat_lit 21090286866600)), (nat_lit 2162, Int.ofNat (nat_lit 31933858238100)), (nat_lit 2183, Int.ofNat (nat_lit 8021538207900)), (nat_lit 2204, Int.ofNat (nat_lit 10915331798700)), (nat_lit 2315, Int.ofNat (nat_lit 2384168341248)), (nat_lit 2316, Int.ofNat (nat_lit 5099671524096)), (nat_lit 2317, Int.ofNat (nat_lit 475114087296)), (nat_lit 2319, Int.ofNat (nat_lit 1116273312000)), (nat_lit 2320, Int.ofNat (nat_lit 773176320000)), (nat_lit 2321, Int.ofNat (nat_lit 847840896000)), (nat_lit 2322, Int.ofNat (nat_lit 261913478400)), (nat_lit 2325, Int.ofNat (nat_lit 3749450450688)), (nat_lit 2337, Int.ofNat (nat_lit 7321536603648)), (nat_lit 2338, Int.ofNat (nat_lit 5911986468096)), (nat_lit 2339, Int.ofNat (nat_lit 1501404912000)), (nat_lit 2342, Int.ofNat (nat_lit 158747500800)), (nat_lit 2344, Int.ofNat (nat_lit 165266438400)), (nat_lit 2345, Int.ofNat (nat_lit 592446355200)), (nat_lit 2346, Int.ofNat (nat_lit 7715209569408)), (nat_lit 2348, Int.ofNat (nat_lit 666940934016)), (nat_lit 2349, Int.ofNat (nat_lit 5982693393600)), (nat_lit 2350, Int.ofNat (nat_lit 11433151537920)), (nat_lit 2351, Int.ofNat (nat_lit 17685804276000)), (nat_lit 2359, Int.ofNat (nat_lit 2176055048448)), (nat_lit 2360, Int.ofNat (nat_lit 977584809600)), (nat_lit 2363, Int.ofNat (nat_lit 676775635200)), (nat_lit 2364, Int.ofNat (nat_lit 777042201600)), (nat_lit 2365, Int.ofNat (nat_lit 1201322707200)), (nat_lit 2366, Int.ofNat (nat_lit 1887516691200)), (nat_lit 2367, Int.ofNat (nat_lit 11268696014208)), (nat_lit 2368, Int.ofNat (nat_lit 7360279591680)), (nat_lit 2369, Int.ofNat (nat_lit 12136953868416)), (nat_lit 2370, Int.ofNat (nat_lit 18104289410880)), (nat_lit 2371, Int.ofNat (nat_lit 25272405692928)), (nat_lit 2372, Int.ofNat (nat_lit 32557609173600)), (nat_lit 2381, Int.ofNat (nat_lit 2814314861952)), (nat_lit 2382, Int.ofNat (nat_lit 4832741349504)), (nat_lit 2383, Int.ofNat (nat_lit 4664575499904)), (nat_lit 2384, Int.ofNat (nat_lit 5173185285504)), (nat_lit 2385, Int.ofNat (nat_lit 4937120152704)), (nat_lit 2386, Int.ofNat (nat_lit 5452248875904)), (nat_lit 2387, Int.ofNat (nat_lit 6229291077504)), (nat_lit 2388, Int.ofNat (nat_lit 15678311099904)), (nat_lit 2389, Int.ofNat (nat_lit 13269277891440)), (nat_lit 2390, Int.ofNat (nat_lit 19501256738304)), (nat_lit 2391, Int.ofNat (nat_lit 25795167116112)), (nat_lit 2392, Int.ofNat (nat_lit 33886745865360)), (nat_lit 2393, Int.ofNat (nat_lit 41978324614608)), (nat_lit 2403, Int.ofNat (nat_lit 6031211588352)), (nat_lit 2404, Int.ofNat (nat_lit 10283151170304)), (nat_lit 2405, Int.ofNat (nat_lit 10455429256704)), (nat_lit 2406, Int.ofNat (nat_lit 10569226408704)), (nat_lit 2407, Int.ofNat (nat_lit 11007037499904)), (nat_lit 2408, Int.ofNat (nat_lit 11706762069504)), (nat_lit 2409, Int.ofNat (nat_lit 20771126872704)), (nat_lit 2410, Int.ofNat (nat_lit 18331227015840)), (nat_lit 2411, Int.ofNat (nat_lit 25882377554304)), (nat_lit 2412, Int.ofNat (nat_lit 31092814209312)), (nat_lit 2413, Int.ofNat (nat_lit 39549718769760)), (nat_lit 2414, Int.ofNat (nat_lit 48097833974208)), (nat_lit 2425, Int.ofNat (nat_lit 8264724682752)), (nat_lit 2426, Int.ofNat (nat_lit 15692732354304)), (nat_lit 2427, Int.ofNat (nat_lit 15133866107904)), (nat_lit 2428, Int.ofNat (nat_lit 15326193717504)), (nat_lit 2429, Int.ofNat (nat_lit 15780434805504)), (nat_lit 2430, Int.ofNat (nat_lit 25134257493504)), (nat_lit 2431, Int.ofNat (nat_lit 22912538329440)), (nat_lit 2432, Int.ofNat (nat_lit 32993183522304)), (nat_lit 2433, Int.ofNat (nat_lit 36268263201312)), (nat_lit 2434, Int.ofNat (nat_lit 45020666086560)), (nat_lit 2435, Int.ofNat (nat_lit 53773068971808)), (nat_lit 2447, Int.ofNat (nat_lit 11440792772352)), (nat_lit 2448, Int.ofNat (nat_lit 20459364367104))]
def block015_data_flat000 : CoefficientMerge.Poly := [(nat_lit 2119, Int.ofNat (nat_lit 40297587372000))]
theorem block015_data_flat000_step : block015_data_flat000 = (CoefficientMerge.scale (40297587372000 : Int) atom1056Coded) := by decide +kernel
theorem block015_data_flat000_original : block015_data_flat000 = (CoefficientMerge.scale (40297587372000 : Int) atom1056Coded) := by
  rw [block015_data_flat000_step]
def block015_data_flat001 : CoefficientMerge.Poly := [(nat_lit 2120, Int.ofNat (nat_lit 45912704890500))]
theorem block015_data_flat001_step : block015_data_flat001 = (CoefficientMerge.scale (45912704890500 : Int) atom1057Coded) := by decide +kernel
theorem block015_data_flat001_original : block015_data_flat001 = (CoefficientMerge.scale (45912704890500 : Int) atom1057Coded) := by
  rw [block015_data_flat001_step]
def block015_data_flat002 : CoefficientMerge.Poly := [(nat_lit 2119, Int.ofNat (nat_lit 40297587372000)), (nat_lit 2120, Int.ofNat (nat_lit 45912704890500))]
theorem block015_data_flat002_step : block015_data_flat002 = (CoefficientMerge.fastMerge block015_data_flat000 block015_data_flat001) := by decide +kernel
theorem block015_data_flat002_original : block015_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40297587372000 : Int) atom1056Coded) (CoefficientMerge.scale (45912704890500 : Int) atom1057Coded)) := by
  rw [block015_data_flat002_step, block015_data_flat000_original, block015_data_flat001_original]
def block015_data_flat003 : CoefficientMerge.Poly := [(nat_lit 2138, Int.ofNat (nat_lit 39243222144000))]
theorem block015_data_flat003_step : block015_data_flat003 = (CoefficientMerge.scale (39243222144000 : Int) atom1058Coded) := by decide +kernel
theorem block015_data_flat003_original : block015_data_flat003 = (CoefficientMerge.scale (39243222144000 : Int) atom1058Coded) := by
  rw [block015_data_flat003_step]
def block015_data_flat004 : CoefficientMerge.Poly := [(nat_lit 2139, Int.ofNat (nat_lit 60042692026800))]
theorem block015_data_flat004_step : block015_data_flat004 = (CoefficientMerge.scale (60042692026800 : Int) atom1059Coded) := by decide +kernel
theorem block015_data_flat004_original : block015_data_flat004 = (CoefficientMerge.scale (60042692026800 : Int) atom1059Coded) := by
  rw [block015_data_flat004_step]
def block015_data_flat005 : CoefficientMerge.Poly := [(nat_lit 2140, Int.ofNat (nat_lit 42753122622000))]
theorem block015_data_flat005_step : block015_data_flat005 = (CoefficientMerge.scale (42753122622000 : Int) atom1060Coded) := by decide +kernel
theorem block015_data_flat005_original : block015_data_flat005 = (CoefficientMerge.scale (42753122622000 : Int) atom1060Coded) := by
  rw [block015_data_flat005_step]
def block015_data_flat006 : CoefficientMerge.Poly := [(nat_lit 2139, Int.ofNat (nat_lit 60042692026800)), (nat_lit 2140, Int.ofNat (nat_lit 42753122622000))]
theorem block015_data_flat006_step : block015_data_flat006 = (CoefficientMerge.fastMerge block015_data_flat004 block015_data_flat005) := by decide +kernel
theorem block015_data_flat006_original : block015_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (60042692026800 : Int) atom1059Coded) (CoefficientMerge.scale (42753122622000 : Int) atom1060Coded)) := by
  rw [block015_data_flat006_step, block015_data_flat004_original, block015_data_flat005_original]
def block015_data_flat007 : CoefficientMerge.Poly := [(nat_lit 2138, Int.ofNat (nat_lit 39243222144000)), (nat_lit 2139, Int.ofNat (nat_lit 60042692026800)), (nat_lit 2140, Int.ofNat (nat_lit 42753122622000))]
theorem block015_data_flat007_step : block015_data_flat007 = (CoefficientMerge.fastMerge block015_data_flat003 block015_data_flat006) := by decide +kernel
theorem block015_data_flat007_original : block015_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (39243222144000 : Int) atom1058Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60042692026800 : Int) atom1059Coded) (CoefficientMerge.scale (42753122622000 : Int) atom1060Coded))) := by
  rw [block015_data_flat007_step, block015_data_flat003_original, block015_data_flat006_original]
def block015_data_flat008 : CoefficientMerge.Poly := [(nat_lit 2119, Int.ofNat (nat_lit 40297587372000)), (nat_lit 2120, Int.ofNat (nat_lit 45912704890500)), (nat_lit 2138, Int.ofNat (nat_lit 39243222144000)), (nat_lit 2139, Int.ofNat (nat_lit 60042692026800)), (nat_lit 2140, Int.ofNat (nat_lit 42753122622000))]
theorem block015_data_flat008_step : block015_data_flat008 = (CoefficientMerge.fastMerge block015_data_flat002 block015_data_flat007) := by decide +kernel
theorem block015_data_flat008_original : block015_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40297587372000 : Int) atom1056Coded) (CoefficientMerge.scale (45912704890500 : Int) atom1057Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39243222144000 : Int) atom1058Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60042692026800 : Int) atom1059Coded) (CoefficientMerge.scale (42753122622000 : Int) atom1060Coded)))) := by
  rw [block015_data_flat008_step, block015_data_flat002_original, block015_data_flat007_original]
def block015_data_flat009 : CoefficientMerge.Poly := [(nat_lit 2141, Int.ofNat (nat_lit 53503172881200))]
theorem block015_data_flat009_step : block015_data_flat009 = (CoefficientMerge.scale (53503172881200 : Int) atom1061Coded) := by decide +kernel
theorem block015_data_flat009_original : block015_data_flat009 = (CoefficientMerge.scale (53503172881200 : Int) atom1061Coded) := by
  rw [block015_data_flat009_step]
def block015_data_flat010 : CoefficientMerge.Poly := [(nat_lit 2160, Int.ofNat (nat_lit 16441201816200))]
theorem block015_data_flat010_step : block015_data_flat010 = (CoefficientMerge.scale (16441201816200 : Int) atom1062Coded) := by decide +kernel
theorem block015_data_flat010_original : block015_data_flat010 = (CoefficientMerge.scale (16441201816200 : Int) atom1062Coded) := by
  rw [block015_data_flat010_step]
def block015_data_flat011 : CoefficientMerge.Poly := [(nat_lit 2141, Int.ofNat (nat_lit 53503172881200)), (nat_lit 2160, Int.ofNat (nat_lit 16441201816200))]
theorem block015_data_flat011_step : block015_data_flat011 = (CoefficientMerge.fastMerge block015_data_flat009 block015_data_flat010) := by decide +kernel
theorem block015_data_flat011_original : block015_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (53503172881200 : Int) atom1061Coded) (CoefficientMerge.scale (16441201816200 : Int) atom1062Coded)) := by
  rw [block015_data_flat011_step, block015_data_flat009_original, block015_data_flat010_original]
def block015_data_flat012 : CoefficientMerge.Poly := [(nat_lit 2161, Int.ofNat (nat_lit 21090286866600))]
theorem block015_data_flat012_step : block015_data_flat012 = (CoefficientMerge.scale (21090286866600 : Int) atom1063Coded) := by decide +kernel
theorem block015_data_flat012_original : block015_data_flat012 = (CoefficientMerge.scale (21090286866600 : Int) atom1063Coded) := by
  rw [block015_data_flat012_step]
def block015_data_flat013 : CoefficientMerge.Poly := [(nat_lit 2162, Int.ofNat (nat_lit 31933858238100))]
theorem block015_data_flat013_step : block015_data_flat013 = (CoefficientMerge.scale (31933858238100 : Int) atom1064Coded) := by decide +kernel
theorem block015_data_flat013_original : block015_data_flat013 = (CoefficientMerge.scale (31933858238100 : Int) atom1064Coded) := by
  rw [block015_data_flat013_step]
def block015_data_flat014 : CoefficientMerge.Poly := [(nat_lit 2183, Int.ofNat (nat_lit 8021538207900))]
theorem block015_data_flat014_step : block015_data_flat014 = (CoefficientMerge.scale (8021538207900 : Int) atom1065Coded) := by decide +kernel
theorem block015_data_flat014_original : block015_data_flat014 = (CoefficientMerge.scale (8021538207900 : Int) atom1065Coded) := by
  rw [block015_data_flat014_step]
def block015_data_flat015 : CoefficientMerge.Poly := [(nat_lit 2162, Int.ofNat (nat_lit 31933858238100)), (nat_lit 2183, Int.ofNat (nat_lit 8021538207900))]
theorem block015_data_flat015_step : block015_data_flat015 = (CoefficientMerge.fastMerge block015_data_flat013 block015_data_flat014) := by decide +kernel
theorem block015_data_flat015_original : block015_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31933858238100 : Int) atom1064Coded) (CoefficientMerge.scale (8021538207900 : Int) atom1065Coded)) := by
  rw [block015_data_flat015_step, block015_data_flat013_original, block015_data_flat014_original]
def block015_data_flat016 : CoefficientMerge.Poly := [(nat_lit 2161, Int.ofNat (nat_lit 21090286866600)), (nat_lit 2162, Int.ofNat (nat_lit 31933858238100)), (nat_lit 2183, Int.ofNat (nat_lit 8021538207900))]
theorem block015_data_flat016_step : block015_data_flat016 = (CoefficientMerge.fastMerge block015_data_flat012 block015_data_flat015) := by decide +kernel
theorem block015_data_flat016_original : block015_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21090286866600 : Int) atom1063Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31933858238100 : Int) atom1064Coded) (CoefficientMerge.scale (8021538207900 : Int) atom1065Coded))) := by
  rw [block015_data_flat016_step, block015_data_flat012_original, block015_data_flat015_original]
def block015_data_flat017 : CoefficientMerge.Poly := [(nat_lit 2141, Int.ofNat (nat_lit 53503172881200)), (nat_lit 2160, Int.ofNat (nat_lit 16441201816200)), (nat_lit 2161, Int.ofNat (nat_lit 21090286866600)), (nat_lit 2162, Int.ofNat (nat_lit 31933858238100)), (nat_lit 2183, Int.ofNat (nat_lit 8021538207900))]
theorem block015_data_flat017_step : block015_data_flat017 = (CoefficientMerge.fastMerge block015_data_flat011 block015_data_flat016) := by decide +kernel
theorem block015_data_flat017_original : block015_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53503172881200 : Int) atom1061Coded) (CoefficientMerge.scale (16441201816200 : Int) atom1062Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21090286866600 : Int) atom1063Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31933858238100 : Int) atom1064Coded) (CoefficientMerge.scale (8021538207900 : Int) atom1065Coded)))) := by
  rw [block015_data_flat017_step, block015_data_flat011_original, block015_data_flat016_original]
def block015_data_flat018 : CoefficientMerge.Poly := [(nat_lit 2119, Int.ofNat (nat_lit 40297587372000)), (nat_lit 2120, Int.ofNat (nat_lit 45912704890500)), (nat_lit 2138, Int.ofNat (nat_lit 39243222144000)), (nat_lit 2139, Int.ofNat (nat_lit 60042692026800)), (nat_lit 2140, Int.ofNat (nat_lit 42753122622000)), (nat_lit 2141, Int.ofNat (nat_lit 53503172881200)), (nat_lit 2160, Int.ofNat (nat_lit 16441201816200)), (nat_lit 2161, Int.ofNat (nat_lit 21090286866600)), (nat_lit 2162, Int.ofNat (nat_lit 31933858238100)), (nat_lit 2183, Int.ofNat (nat_lit 8021538207900))]
theorem block015_data_flat018_step : block015_data_flat018 = (CoefficientMerge.fastMerge block015_data_flat008 block015_data_flat017) := by decide +kernel
theorem block015_data_flat018_original : block015_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40297587372000 : Int) atom1056Coded) (CoefficientMerge.scale (45912704890500 : Int) atom1057Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39243222144000 : Int) atom1058Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60042692026800 : Int) atom1059Coded) (CoefficientMerge.scale (42753122622000 : Int) atom1060Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53503172881200 : Int) atom1061Coded) (CoefficientMerge.scale (16441201816200 : Int) atom1062Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21090286866600 : Int) atom1063Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31933858238100 : Int) atom1064Coded) (CoefficientMerge.scale (8021538207900 : Int) atom1065Coded))))) := by
  rw [block015_data_flat018_step, block015_data_flat008_original, block015_data_flat017_original]
def block015_data_flat019 : CoefficientMerge.Poly := [(nat_lit 2204, Int.ofNat (nat_lit 10915331798700))]
theorem block015_data_flat019_step : block015_data_flat019 = (CoefficientMerge.scale (10915331798700 : Int) atom1066Coded) := by decide +kernel
theorem block015_data_flat019_original : block015_data_flat019 = (CoefficientMerge.scale (10915331798700 : Int) atom1066Coded) := by
  rw [block015_data_flat019_step]
def block015_data_flat020 : CoefficientMerge.Poly := [(nat_lit 2315, Int.ofNat (nat_lit 2384168341248))]
theorem block015_data_flat020_step : block015_data_flat020 = (CoefficientMerge.scale (2384168341248 : Int) atom1067Coded) := by decide +kernel
theorem block015_data_flat020_original : block015_data_flat020 = (CoefficientMerge.scale (2384168341248 : Int) atom1067Coded) := by
  rw [block015_data_flat020_step]
def block015_data_flat021 : CoefficientMerge.Poly := [(nat_lit 2204, Int.ofNat (nat_lit 10915331798700)), (nat_lit 2315, Int.ofNat (nat_lit 2384168341248))]
theorem block015_data_flat021_step : block015_data_flat021 = (CoefficientMerge.fastMerge block015_data_flat019 block015_data_flat020) := by decide +kernel
theorem block015_data_flat021_original : block015_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10915331798700 : Int) atom1066Coded) (CoefficientMerge.scale (2384168341248 : Int) atom1067Coded)) := by
  rw [block015_data_flat021_step, block015_data_flat019_original, block015_data_flat020_original]
def block015_data_flat022 : CoefficientMerge.Poly := [(nat_lit 2316, Int.ofNat (nat_lit 5099671524096))]
theorem block015_data_flat022_step : block015_data_flat022 = (CoefficientMerge.scale (5099671524096 : Int) atom1068Coded) := by decide +kernel
theorem block015_data_flat022_original : block015_data_flat022 = (CoefficientMerge.scale (5099671524096 : Int) atom1068Coded) := by
  rw [block015_data_flat022_step]
def block015_data_flat023 : CoefficientMerge.Poly := [(nat_lit 2317, Int.ofNat (nat_lit 475114087296))]
theorem block015_data_flat023_step : block015_data_flat023 = (CoefficientMerge.scale (475114087296 : Int) atom1069Coded) := by decide +kernel
theorem block015_data_flat023_original : block015_data_flat023 = (CoefficientMerge.scale (475114087296 : Int) atom1069Coded) := by
  rw [block015_data_flat023_step]
def block015_data_flat024 : CoefficientMerge.Poly := [(nat_lit 2319, Int.ofNat (nat_lit 1116273312000))]
theorem block015_data_flat024_step : block015_data_flat024 = (CoefficientMerge.scale (1116273312000 : Int) atom1070Coded) := by decide +kernel
theorem block015_data_flat024_original : block015_data_flat024 = (CoefficientMerge.scale (1116273312000 : Int) atom1070Coded) := by
  rw [block015_data_flat024_step]
def block015_data_flat025 : CoefficientMerge.Poly := [(nat_lit 2317, Int.ofNat (nat_lit 475114087296)), (nat_lit 2319, Int.ofNat (nat_lit 1116273312000))]
theorem block015_data_flat025_step : block015_data_flat025 = (CoefficientMerge.fastMerge block015_data_flat023 block015_data_flat024) := by decide +kernel
theorem block015_data_flat025_original : block015_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (475114087296 : Int) atom1069Coded) (CoefficientMerge.scale (1116273312000 : Int) atom1070Coded)) := by
  rw [block015_data_flat025_step, block015_data_flat023_original, block015_data_flat024_original]
def block015_data_flat026 : CoefficientMerge.Poly := [(nat_lit 2316, Int.ofNat (nat_lit 5099671524096)), (nat_lit 2317, Int.ofNat (nat_lit 475114087296)), (nat_lit 2319, Int.ofNat (nat_lit 1116273312000))]
theorem block015_data_flat026_step : block015_data_flat026 = (CoefficientMerge.fastMerge block015_data_flat022 block015_data_flat025) := by decide +kernel
theorem block015_data_flat026_original : block015_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5099671524096 : Int) atom1068Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475114087296 : Int) atom1069Coded) (CoefficientMerge.scale (1116273312000 : Int) atom1070Coded))) := by
  rw [block015_data_flat026_step, block015_data_flat022_original, block015_data_flat025_original]
def block015_data_flat027 : CoefficientMerge.Poly := [(nat_lit 2204, Int.ofNat (nat_lit 10915331798700)), (nat_lit 2315, Int.ofNat (nat_lit 2384168341248)), (nat_lit 2316, Int.ofNat (nat_lit 5099671524096)), (nat_lit 2317, Int.ofNat (nat_lit 475114087296)), (nat_lit 2319, Int.ofNat (nat_lit 1116273312000))]
theorem block015_data_flat027_step : block015_data_flat027 = (CoefficientMerge.fastMerge block015_data_flat021 block015_data_flat026) := by decide +kernel
theorem block015_data_flat027_original : block015_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10915331798700 : Int) atom1066Coded) (CoefficientMerge.scale (2384168341248 : Int) atom1067Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5099671524096 : Int) atom1068Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475114087296 : Int) atom1069Coded) (CoefficientMerge.scale (1116273312000 : Int) atom1070Coded)))) := by
  rw [block015_data_flat027_step, block015_data_flat021_original, block015_data_flat026_original]
def block015_data_flat028 : CoefficientMerge.Poly := [(nat_lit 2320, Int.ofNat (nat_lit 773176320000))]
theorem block015_data_flat028_step : block015_data_flat028 = (CoefficientMerge.scale (773176320000 : Int) atom1071Coded) := by decide +kernel
theorem block015_data_flat028_original : block015_data_flat028 = (CoefficientMerge.scale (773176320000 : Int) atom1071Coded) := by
  rw [block015_data_flat028_step]
def block015_data_flat029 : CoefficientMerge.Poly := [(nat_lit 2321, Int.ofNat (nat_lit 847840896000))]
theorem block015_data_flat029_step : block015_data_flat029 = (CoefficientMerge.scale (847840896000 : Int) atom1072Coded) := by decide +kernel
theorem block015_data_flat029_original : block015_data_flat029 = (CoefficientMerge.scale (847840896000 : Int) atom1072Coded) := by
  rw [block015_data_flat029_step]
def block015_data_flat030 : CoefficientMerge.Poly := [(nat_lit 2320, Int.ofNat (nat_lit 773176320000)), (nat_lit 2321, Int.ofNat (nat_lit 847840896000))]
theorem block015_data_flat030_step : block015_data_flat030 = (CoefficientMerge.fastMerge block015_data_flat028 block015_data_flat029) := by decide +kernel
theorem block015_data_flat030_original : block015_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (773176320000 : Int) atom1071Coded) (CoefficientMerge.scale (847840896000 : Int) atom1072Coded)) := by
  rw [block015_data_flat030_step, block015_data_flat028_original, block015_data_flat029_original]
def block015_data_flat031 : CoefficientMerge.Poly := [(nat_lit 2322, Int.ofNat (nat_lit 261913478400))]
theorem block015_data_flat031_step : block015_data_flat031 = (CoefficientMerge.scale (261913478400 : Int) atom1073Coded) := by decide +kernel
theorem block015_data_flat031_original : block015_data_flat031 = (CoefficientMerge.scale (261913478400 : Int) atom1073Coded) := by
  rw [block015_data_flat031_step]
def block015_data_flat032 : CoefficientMerge.Poly := [(nat_lit 2325, Int.ofNat (nat_lit 3749450450688))]
theorem block015_data_flat032_step : block015_data_flat032 = (CoefficientMerge.scale (3749450450688 : Int) atom1074Coded) := by decide +kernel
theorem block015_data_flat032_original : block015_data_flat032 = (CoefficientMerge.scale (3749450450688 : Int) atom1074Coded) := by
  rw [block015_data_flat032_step]
def block015_data_flat033 : CoefficientMerge.Poly := [(nat_lit 2337, Int.ofNat (nat_lit 7321536603648))]
theorem block015_data_flat033_step : block015_data_flat033 = (CoefficientMerge.scale (7321536603648 : Int) atom1075Coded) := by decide +kernel
theorem block015_data_flat033_original : block015_data_flat033 = (CoefficientMerge.scale (7321536603648 : Int) atom1075Coded) := by
  rw [block015_data_flat033_step]
def block015_data_flat034 : CoefficientMerge.Poly := [(nat_lit 2325, Int.ofNat (nat_lit 3749450450688)), (nat_lit 2337, Int.ofNat (nat_lit 7321536603648))]
theorem block015_data_flat034_step : block015_data_flat034 = (CoefficientMerge.fastMerge block015_data_flat032 block015_data_flat033) := by decide +kernel
theorem block015_data_flat034_original : block015_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3749450450688 : Int) atom1074Coded) (CoefficientMerge.scale (7321536603648 : Int) atom1075Coded)) := by
  rw [block015_data_flat034_step, block015_data_flat032_original, block015_data_flat033_original]
def block015_data_flat035 : CoefficientMerge.Poly := [(nat_lit 2322, Int.ofNat (nat_lit 261913478400)), (nat_lit 2325, Int.ofNat (nat_lit 3749450450688)), (nat_lit 2337, Int.ofNat (nat_lit 7321536603648))]
theorem block015_data_flat035_step : block015_data_flat035 = (CoefficientMerge.fastMerge block015_data_flat031 block015_data_flat034) := by decide +kernel
theorem block015_data_flat035_original : block015_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (261913478400 : Int) atom1073Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3749450450688 : Int) atom1074Coded) (CoefficientMerge.scale (7321536603648 : Int) atom1075Coded))) := by
  rw [block015_data_flat035_step, block015_data_flat031_original, block015_data_flat034_original]
def block015_data_flat036 : CoefficientMerge.Poly := [(nat_lit 2320, Int.ofNat (nat_lit 773176320000)), (nat_lit 2321, Int.ofNat (nat_lit 847840896000)), (nat_lit 2322, Int.ofNat (nat_lit 261913478400)), (nat_lit 2325, Int.ofNat (nat_lit 3749450450688)), (nat_lit 2337, Int.ofNat (nat_lit 7321536603648))]
theorem block015_data_flat036_step : block015_data_flat036 = (CoefficientMerge.fastMerge block015_data_flat030 block015_data_flat035) := by decide +kernel
theorem block015_data_flat036_original : block015_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (773176320000 : Int) atom1071Coded) (CoefficientMerge.scale (847840896000 : Int) atom1072Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (261913478400 : Int) atom1073Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3749450450688 : Int) atom1074Coded) (CoefficientMerge.scale (7321536603648 : Int) atom1075Coded)))) := by
  rw [block015_data_flat036_step, block015_data_flat030_original, block015_data_flat035_original]
def block015_data_flat037 : CoefficientMerge.Poly := [(nat_lit 2204, Int.ofNat (nat_lit 10915331798700)), (nat_lit 2315, Int.ofNat (nat_lit 2384168341248)), (nat_lit 2316, Int.ofNat (nat_lit 5099671524096)), (nat_lit 2317, Int.ofNat (nat_lit 475114087296)), (nat_lit 2319, Int.ofNat (nat_lit 1116273312000)), (nat_lit 2320, Int.ofNat (nat_lit 773176320000)), (nat_lit 2321, Int.ofNat (nat_lit 847840896000)), (nat_lit 2322, Int.ofNat (nat_lit 261913478400)), (nat_lit 2325, Int.ofNat (nat_lit 3749450450688)), (nat_lit 2337, Int.ofNat (nat_lit 7321536603648))]
theorem block015_data_flat037_step : block015_data_flat037 = (CoefficientMerge.fastMerge block015_data_flat027 block015_data_flat036) := by decide +kernel
theorem block015_data_flat037_original : block015_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10915331798700 : Int) atom1066Coded) (CoefficientMerge.scale (2384168341248 : Int) atom1067Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5099671524096 : Int) atom1068Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475114087296 : Int) atom1069Coded) (CoefficientMerge.scale (1116273312000 : Int) atom1070Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (773176320000 : Int) atom1071Coded) (CoefficientMerge.scale (847840896000 : Int) atom1072Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (261913478400 : Int) atom1073Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3749450450688 : Int) atom1074Coded) (CoefficientMerge.scale (7321536603648 : Int) atom1075Coded))))) := by
  rw [block015_data_flat037_step, block015_data_flat027_original, block015_data_flat036_original]
def block015_data_flat038 : CoefficientMerge.Poly := [(nat_lit 2119, Int.ofNat (nat_lit 40297587372000)), (nat_lit 2120, Int.ofNat (nat_lit 45912704890500)), (nat_lit 2138, Int.ofNat (nat_lit 39243222144000)), (nat_lit 2139, Int.ofNat (nat_lit 60042692026800)), (nat_lit 2140, Int.ofNat (nat_lit 42753122622000)), (nat_lit 2141, Int.ofNat (nat_lit 53503172881200)), (nat_lit 2160, Int.ofNat (nat_lit 16441201816200)), (nat_lit 2161, Int.ofNat (nat_lit 21090286866600)), (nat_lit 2162, Int.ofNat (nat_lit 31933858238100)), (nat_lit 2183, Int.ofNat (nat_lit 8021538207900)), (nat_lit 2204, Int.ofNat (nat_lit 10915331798700)), (nat_lit 2315, Int.ofNat (nat_lit 2384168341248)), (nat_lit 2316, Int.ofNat (nat_lit 5099671524096)), (nat_lit 2317, Int.ofNat (nat_lit 475114087296)), (nat_lit 2319, Int.ofNat (nat_lit 1116273312000)), (nat_lit 2320, Int.ofNat (nat_lit 773176320000)), (nat_lit 2321, Int.ofNat (nat_lit 847840896000)), (nat_lit 2322, Int.ofNat (nat_lit 261913478400)), (nat_lit 2325, Int.ofNat (nat_lit 3749450450688)), (nat_lit 2337, Int.ofNat (nat_lit 7321536603648))]
theorem block015_data_flat038_step : block015_data_flat038 = (CoefficientMerge.fastMerge block015_data_flat018 block015_data_flat037) := by decide +kernel
theorem block015_data_flat038_original : block015_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40297587372000 : Int) atom1056Coded) (CoefficientMerge.scale (45912704890500 : Int) atom1057Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39243222144000 : Int) atom1058Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60042692026800 : Int) atom1059Coded) (CoefficientMerge.scale (42753122622000 : Int) atom1060Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53503172881200 : Int) atom1061Coded) (CoefficientMerge.scale (16441201816200 : Int) atom1062Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21090286866600 : Int) atom1063Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31933858238100 : Int) atom1064Coded) (CoefficientMerge.scale (8021538207900 : Int) atom1065Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10915331798700 : Int) atom1066Coded) (CoefficientMerge.scale (2384168341248 : Int) atom1067Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5099671524096 : Int) atom1068Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475114087296 : Int) atom1069Coded) (CoefficientMerge.scale (1116273312000 : Int) atom1070Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (773176320000 : Int) atom1071Coded) (CoefficientMerge.scale (847840896000 : Int) atom1072Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (261913478400 : Int) atom1073Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3749450450688 : Int) atom1074Coded) (CoefficientMerge.scale (7321536603648 : Int) atom1075Coded)))))) := by
  rw [block015_data_flat038_step, block015_data_flat018_original, block015_data_flat037_original]
def block015_data_flat039 : CoefficientMerge.Poly := [(nat_lit 2338, Int.ofNat (nat_lit 5911986468096))]
theorem block015_data_flat039_step : block015_data_flat039 = (CoefficientMerge.scale (5911986468096 : Int) atom1076Coded) := by decide +kernel
theorem block015_data_flat039_original : block015_data_flat039 = (CoefficientMerge.scale (5911986468096 : Int) atom1076Coded) := by
  rw [block015_data_flat039_step]
def block015_data_flat040 : CoefficientMerge.Poly := [(nat_lit 2339, Int.ofNat (nat_lit 1501404912000))]
theorem block015_data_flat040_step : block015_data_flat040 = (CoefficientMerge.scale (1501404912000 : Int) atom1077Coded) := by decide +kernel
theorem block015_data_flat040_original : block015_data_flat040 = (CoefficientMerge.scale (1501404912000 : Int) atom1077Coded) := by
  rw [block015_data_flat040_step]
def block015_data_flat041 : CoefficientMerge.Poly := [(nat_lit 2338, Int.ofNat (nat_lit 5911986468096)), (nat_lit 2339, Int.ofNat (nat_lit 1501404912000))]
theorem block015_data_flat041_step : block015_data_flat041 = (CoefficientMerge.fastMerge block015_data_flat039 block015_data_flat040) := by decide +kernel
theorem block015_data_flat041_original : block015_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5911986468096 : Int) atom1076Coded) (CoefficientMerge.scale (1501404912000 : Int) atom1077Coded)) := by
  rw [block015_data_flat041_step, block015_data_flat039_original, block015_data_flat040_original]
def block015_data_flat042 : CoefficientMerge.Poly := [(nat_lit 2342, Int.ofNat (nat_lit 158747500800))]
theorem block015_data_flat042_step : block015_data_flat042 = (CoefficientMerge.scale (158747500800 : Int) atom1078Coded) := by decide +kernel
theorem block015_data_flat042_original : block015_data_flat042 = (CoefficientMerge.scale (158747500800 : Int) atom1078Coded) := by
  rw [block015_data_flat042_step]
def block015_data_flat043 : CoefficientMerge.Poly := [(nat_lit 2344, Int.ofNat (nat_lit 165266438400))]
theorem block015_data_flat043_step : block015_data_flat043 = (CoefficientMerge.scale (165266438400 : Int) atom1079Coded) := by decide +kernel
theorem block015_data_flat043_original : block015_data_flat043 = (CoefficientMerge.scale (165266438400 : Int) atom1079Coded) := by
  rw [block015_data_flat043_step]
def block015_data_flat044 : CoefficientMerge.Poly := [(nat_lit 2345, Int.ofNat (nat_lit 592446355200))]
theorem block015_data_flat044_step : block015_data_flat044 = (CoefficientMerge.scale (592446355200 : Int) atom1080Coded) := by decide +kernel
theorem block015_data_flat044_original : block015_data_flat044 = (CoefficientMerge.scale (592446355200 : Int) atom1080Coded) := by
  rw [block015_data_flat044_step]
def block015_data_flat045 : CoefficientMerge.Poly := [(nat_lit 2344, Int.ofNat (nat_lit 165266438400)), (nat_lit 2345, Int.ofNat (nat_lit 592446355200))]
theorem block015_data_flat045_step : block015_data_flat045 = (CoefficientMerge.fastMerge block015_data_flat043 block015_data_flat044) := by decide +kernel
theorem block015_data_flat045_original : block015_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (165266438400 : Int) atom1079Coded) (CoefficientMerge.scale (592446355200 : Int) atom1080Coded)) := by
  rw [block015_data_flat045_step, block015_data_flat043_original, block015_data_flat044_original]
def block015_data_flat046 : CoefficientMerge.Poly := [(nat_lit 2342, Int.ofNat (nat_lit 158747500800)), (nat_lit 2344, Int.ofNat (nat_lit 165266438400)), (nat_lit 2345, Int.ofNat (nat_lit 592446355200))]
theorem block015_data_flat046_step : block015_data_flat046 = (CoefficientMerge.fastMerge block015_data_flat042 block015_data_flat045) := by decide +kernel
theorem block015_data_flat046_original : block015_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (158747500800 : Int) atom1078Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (165266438400 : Int) atom1079Coded) (CoefficientMerge.scale (592446355200 : Int) atom1080Coded))) := by
  rw [block015_data_flat046_step, block015_data_flat042_original, block015_data_flat045_original]
def block015_data_flat047 : CoefficientMerge.Poly := [(nat_lit 2338, Int.ofNat (nat_lit 5911986468096)), (nat_lit 2339, Int.ofNat (nat_lit 1501404912000)), (nat_lit 2342, Int.ofNat (nat_lit 158747500800)), (nat_lit 2344, Int.ofNat (nat_lit 165266438400)), (nat_lit 2345, Int.ofNat (nat_lit 592446355200))]
theorem block015_data_flat047_step : block015_data_flat047 = (CoefficientMerge.fastMerge block015_data_flat041 block015_data_flat046) := by decide +kernel
theorem block015_data_flat047_original : block015_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5911986468096 : Int) atom1076Coded) (CoefficientMerge.scale (1501404912000 : Int) atom1077Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158747500800 : Int) atom1078Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (165266438400 : Int) atom1079Coded) (CoefficientMerge.scale (592446355200 : Int) atom1080Coded)))) := by
  rw [block015_data_flat047_step, block015_data_flat041_original, block015_data_flat046_original]
def block015_data_flat048 : CoefficientMerge.Poly := [(nat_lit 2346, Int.ofNat (nat_lit 7715209569408))]
theorem block015_data_flat048_step : block015_data_flat048 = (CoefficientMerge.scale (7715209569408 : Int) atom1081Coded) := by decide +kernel
theorem block015_data_flat048_original : block015_data_flat048 = (CoefficientMerge.scale (7715209569408 : Int) atom1081Coded) := by
  rw [block015_data_flat048_step]
def block015_data_flat049 : CoefficientMerge.Poly := [(nat_lit 2348, Int.ofNat (nat_lit 666940934016))]
theorem block015_data_flat049_step : block015_data_flat049 = (CoefficientMerge.scale (666940934016 : Int) atom1082Coded) := by decide +kernel
theorem block015_data_flat049_original : block015_data_flat049 = (CoefficientMerge.scale (666940934016 : Int) atom1082Coded) := by
  rw [block015_data_flat049_step]
def block015_data_flat050 : CoefficientMerge.Poly := [(nat_lit 2346, Int.ofNat (nat_lit 7715209569408)), (nat_lit 2348, Int.ofNat (nat_lit 666940934016))]
theorem block015_data_flat050_step : block015_data_flat050 = (CoefficientMerge.fastMerge block015_data_flat048 block015_data_flat049) := by decide +kernel
theorem block015_data_flat050_original : block015_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715209569408 : Int) atom1081Coded) (CoefficientMerge.scale (666940934016 : Int) atom1082Coded)) := by
  rw [block015_data_flat050_step, block015_data_flat048_original, block015_data_flat049_original]
def block015_data_flat051 : CoefficientMerge.Poly := [(nat_lit 2349, Int.ofNat (nat_lit 5982693393600))]
theorem block015_data_flat051_step : block015_data_flat051 = (CoefficientMerge.scale (5982693393600 : Int) atom1083Coded) := by decide +kernel
theorem block015_data_flat051_original : block015_data_flat051 = (CoefficientMerge.scale (5982693393600 : Int) atom1083Coded) := by
  rw [block015_data_flat051_step]
def block015_data_flat052 : CoefficientMerge.Poly := [(nat_lit 2350, Int.ofNat (nat_lit 11433151537920))]
theorem block015_data_flat052_step : block015_data_flat052 = (CoefficientMerge.scale (11433151537920 : Int) atom1084Coded) := by decide +kernel
theorem block015_data_flat052_original : block015_data_flat052 = (CoefficientMerge.scale (11433151537920 : Int) atom1084Coded) := by
  rw [block015_data_flat052_step]
def block015_data_flat053 : CoefficientMerge.Poly := [(nat_lit 2351, Int.ofNat (nat_lit 17685804276000))]
theorem block015_data_flat053_step : block015_data_flat053 = (CoefficientMerge.scale (17685804276000 : Int) atom1085Coded) := by decide +kernel
theorem block015_data_flat053_original : block015_data_flat053 = (CoefficientMerge.scale (17685804276000 : Int) atom1085Coded) := by
  rw [block015_data_flat053_step]
def block015_data_flat054 : CoefficientMerge.Poly := [(nat_lit 2350, Int.ofNat (nat_lit 11433151537920)), (nat_lit 2351, Int.ofNat (nat_lit 17685804276000))]
theorem block015_data_flat054_step : block015_data_flat054 = (CoefficientMerge.fastMerge block015_data_flat052 block015_data_flat053) := by decide +kernel
theorem block015_data_flat054_original : block015_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11433151537920 : Int) atom1084Coded) (CoefficientMerge.scale (17685804276000 : Int) atom1085Coded)) := by
  rw [block015_data_flat054_step, block015_data_flat052_original, block015_data_flat053_original]
def block015_data_flat055 : CoefficientMerge.Poly := [(nat_lit 2349, Int.ofNat (nat_lit 5982693393600)), (nat_lit 2350, Int.ofNat (nat_lit 11433151537920)), (nat_lit 2351, Int.ofNat (nat_lit 17685804276000))]
theorem block015_data_flat055_step : block015_data_flat055 = (CoefficientMerge.fastMerge block015_data_flat051 block015_data_flat054) := by decide +kernel
theorem block015_data_flat055_original : block015_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5982693393600 : Int) atom1083Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11433151537920 : Int) atom1084Coded) (CoefficientMerge.scale (17685804276000 : Int) atom1085Coded))) := by
  rw [block015_data_flat055_step, block015_data_flat051_original, block015_data_flat054_original]
def block015_data_flat056 : CoefficientMerge.Poly := [(nat_lit 2346, Int.ofNat (nat_lit 7715209569408)), (nat_lit 2348, Int.ofNat (nat_lit 666940934016)), (nat_lit 2349, Int.ofNat (nat_lit 5982693393600)), (nat_lit 2350, Int.ofNat (nat_lit 11433151537920)), (nat_lit 2351, Int.ofNat (nat_lit 17685804276000))]
theorem block015_data_flat056_step : block015_data_flat056 = (CoefficientMerge.fastMerge block015_data_flat050 block015_data_flat055) := by decide +kernel
theorem block015_data_flat056_original : block015_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715209569408 : Int) atom1081Coded) (CoefficientMerge.scale (666940934016 : Int) atom1082Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5982693393600 : Int) atom1083Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11433151537920 : Int) atom1084Coded) (CoefficientMerge.scale (17685804276000 : Int) atom1085Coded)))) := by
  rw [block015_data_flat056_step, block015_data_flat050_original, block015_data_flat055_original]
def block015_data_flat057 : CoefficientMerge.Poly := [(nat_lit 2338, Int.ofNat (nat_lit 5911986468096)), (nat_lit 2339, Int.ofNat (nat_lit 1501404912000)), (nat_lit 2342, Int.ofNat (nat_lit 158747500800)), (nat_lit 2344, Int.ofNat (nat_lit 165266438400)), (nat_lit 2345, Int.ofNat (nat_lit 592446355200)), (nat_lit 2346, Int.ofNat (nat_lit 7715209569408)), (nat_lit 2348, Int.ofNat (nat_lit 666940934016)), (nat_lit 2349, Int.ofNat (nat_lit 5982693393600)), (nat_lit 2350, Int.ofNat (nat_lit 11433151537920)), (nat_lit 2351, Int.ofNat (nat_lit 17685804276000))]
theorem block015_data_flat057_step : block015_data_flat057 = (CoefficientMerge.fastMerge block015_data_flat047 block015_data_flat056) := by decide +kernel
theorem block015_data_flat057_original : block015_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5911986468096 : Int) atom1076Coded) (CoefficientMerge.scale (1501404912000 : Int) atom1077Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158747500800 : Int) atom1078Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (165266438400 : Int) atom1079Coded) (CoefficientMerge.scale (592446355200 : Int) atom1080Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715209569408 : Int) atom1081Coded) (CoefficientMerge.scale (666940934016 : Int) atom1082Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5982693393600 : Int) atom1083Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11433151537920 : Int) atom1084Coded) (CoefficientMerge.scale (17685804276000 : Int) atom1085Coded))))) := by
  rw [block015_data_flat057_step, block015_data_flat047_original, block015_data_flat056_original]
def block015_data_flat058 : CoefficientMerge.Poly := [(nat_lit 2359, Int.ofNat (nat_lit 2176055048448))]
theorem block015_data_flat058_step : block015_data_flat058 = (CoefficientMerge.scale (2176055048448 : Int) atom1086Coded) := by decide +kernel
theorem block015_data_flat058_original : block015_data_flat058 = (CoefficientMerge.scale (2176055048448 : Int) atom1086Coded) := by
  rw [block015_data_flat058_step]
def block015_data_flat059 : CoefficientMerge.Poly := [(nat_lit 2360, Int.ofNat (nat_lit 977584809600))]
theorem block015_data_flat059_step : block015_data_flat059 = (CoefficientMerge.scale (977584809600 : Int) atom1087Coded) := by decide +kernel
theorem block015_data_flat059_original : block015_data_flat059 = (CoefficientMerge.scale (977584809600 : Int) atom1087Coded) := by
  rw [block015_data_flat059_step]
def block015_data_flat060 : CoefficientMerge.Poly := [(nat_lit 2359, Int.ofNat (nat_lit 2176055048448)), (nat_lit 2360, Int.ofNat (nat_lit 977584809600))]
theorem block015_data_flat060_step : block015_data_flat060 = (CoefficientMerge.fastMerge block015_data_flat058 block015_data_flat059) := by decide +kernel
theorem block015_data_flat060_original : block015_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2176055048448 : Int) atom1086Coded) (CoefficientMerge.scale (977584809600 : Int) atom1087Coded)) := by
  rw [block015_data_flat060_step, block015_data_flat058_original, block015_data_flat059_original]
def block015_data_flat061 : CoefficientMerge.Poly := [(nat_lit 2363, Int.ofNat (nat_lit 676775635200))]
theorem block015_data_flat061_step : block015_data_flat061 = (CoefficientMerge.scale (676775635200 : Int) atom1088Coded) := by decide +kernel
theorem block015_data_flat061_original : block015_data_flat061 = (CoefficientMerge.scale (676775635200 : Int) atom1088Coded) := by
  rw [block015_data_flat061_step]
def block015_data_flat062 : CoefficientMerge.Poly := [(nat_lit 2364, Int.ofNat (nat_lit 777042201600))]
theorem block015_data_flat062_step : block015_data_flat062 = (CoefficientMerge.scale (777042201600 : Int) atom1089Coded) := by decide +kernel
theorem block015_data_flat062_original : block015_data_flat062 = (CoefficientMerge.scale (777042201600 : Int) atom1089Coded) := by
  rw [block015_data_flat062_step]
def block015_data_flat063 : CoefficientMerge.Poly := [(nat_lit 2365, Int.ofNat (nat_lit 1201322707200))]
theorem block015_data_flat063_step : block015_data_flat063 = (CoefficientMerge.scale (1201322707200 : Int) atom1090Coded) := by decide +kernel
theorem block015_data_flat063_original : block015_data_flat063 = (CoefficientMerge.scale (1201322707200 : Int) atom1090Coded) := by
  rw [block015_data_flat063_step]
def block015_data_flat064 : CoefficientMerge.Poly := [(nat_lit 2364, Int.ofNat (nat_lit 777042201600)), (nat_lit 2365, Int.ofNat (nat_lit 1201322707200))]
theorem block015_data_flat064_step : block015_data_flat064 = (CoefficientMerge.fastMerge block015_data_flat062 block015_data_flat063) := by decide +kernel
theorem block015_data_flat064_original : block015_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (777042201600 : Int) atom1089Coded) (CoefficientMerge.scale (1201322707200 : Int) atom1090Coded)) := by
  rw [block015_data_flat064_step, block015_data_flat062_original, block015_data_flat063_original]
def block015_data_flat065 : CoefficientMerge.Poly := [(nat_lit 2363, Int.ofNat (nat_lit 676775635200)), (nat_lit 2364, Int.ofNat (nat_lit 777042201600)), (nat_lit 2365, Int.ofNat (nat_lit 1201322707200))]
theorem block015_data_flat065_step : block015_data_flat065 = (CoefficientMerge.fastMerge block015_data_flat061 block015_data_flat064) := by decide +kernel
theorem block015_data_flat065_original : block015_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (676775635200 : Int) atom1088Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (777042201600 : Int) atom1089Coded) (CoefficientMerge.scale (1201322707200 : Int) atom1090Coded))) := by
  rw [block015_data_flat065_step, block015_data_flat061_original, block015_data_flat064_original]
def block015_data_flat066 : CoefficientMerge.Poly := [(nat_lit 2359, Int.ofNat (nat_lit 2176055048448)), (nat_lit 2360, Int.ofNat (nat_lit 977584809600)), (nat_lit 2363, Int.ofNat (nat_lit 676775635200)), (nat_lit 2364, Int.ofNat (nat_lit 777042201600)), (nat_lit 2365, Int.ofNat (nat_lit 1201322707200))]
theorem block015_data_flat066_step : block015_data_flat066 = (CoefficientMerge.fastMerge block015_data_flat060 block015_data_flat065) := by decide +kernel
theorem block015_data_flat066_original : block015_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2176055048448 : Int) atom1086Coded) (CoefficientMerge.scale (977584809600 : Int) atom1087Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (676775635200 : Int) atom1088Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (777042201600 : Int) atom1089Coded) (CoefficientMerge.scale (1201322707200 : Int) atom1090Coded)))) := by
  rw [block015_data_flat066_step, block015_data_flat060_original, block015_data_flat065_original]
def block015_data_flat067 : CoefficientMerge.Poly := [(nat_lit 2366, Int.ofNat (nat_lit 1887516691200))]
theorem block015_data_flat067_step : block015_data_flat067 = (CoefficientMerge.scale (1887516691200 : Int) atom1091Coded) := by decide +kernel
theorem block015_data_flat067_original : block015_data_flat067 = (CoefficientMerge.scale (1887516691200 : Int) atom1091Coded) := by
  rw [block015_data_flat067_step]
def block015_data_flat068 : CoefficientMerge.Poly := [(nat_lit 2367, Int.ofNat (nat_lit 11268696014208))]
theorem block015_data_flat068_step : block015_data_flat068 = (CoefficientMerge.scale (11268696014208 : Int) atom1092Coded) := by decide +kernel
theorem block015_data_flat068_original : block015_data_flat068 = (CoefficientMerge.scale (11268696014208 : Int) atom1092Coded) := by
  rw [block015_data_flat068_step]
def block015_data_flat069 : CoefficientMerge.Poly := [(nat_lit 2366, Int.ofNat (nat_lit 1887516691200)), (nat_lit 2367, Int.ofNat (nat_lit 11268696014208))]
theorem block015_data_flat069_step : block015_data_flat069 = (CoefficientMerge.fastMerge block015_data_flat067 block015_data_flat068) := by decide +kernel
theorem block015_data_flat069_original : block015_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (1887516691200 : Int) atom1091Coded) (CoefficientMerge.scale (11268696014208 : Int) atom1092Coded)) := by
  rw [block015_data_flat069_step, block015_data_flat067_original, block015_data_flat068_original]
def block015_data_flat070 : CoefficientMerge.Poly := [(nat_lit 2368, Int.ofNat (nat_lit 7360279591680))]
theorem block015_data_flat070_step : block015_data_flat070 = (CoefficientMerge.scale (7360279591680 : Int) atom1093Coded) := by decide +kernel
theorem block015_data_flat070_original : block015_data_flat070 = (CoefficientMerge.scale (7360279591680 : Int) atom1093Coded) := by
  rw [block015_data_flat070_step]
def block015_data_flat071 : CoefficientMerge.Poly := [(nat_lit 2369, Int.ofNat (nat_lit 12136953868416))]
theorem block015_data_flat071_step : block015_data_flat071 = (CoefficientMerge.scale (12136953868416 : Int) atom1094Coded) := by decide +kernel
theorem block015_data_flat071_original : block015_data_flat071 = (CoefficientMerge.scale (12136953868416 : Int) atom1094Coded) := by
  rw [block015_data_flat071_step]
def block015_data_flat072 : CoefficientMerge.Poly := [(nat_lit 2370, Int.ofNat (nat_lit 18104289410880))]
theorem block015_data_flat072_step : block015_data_flat072 = (CoefficientMerge.scale (18104289410880 : Int) atom1095Coded) := by decide +kernel
theorem block015_data_flat072_original : block015_data_flat072 = (CoefficientMerge.scale (18104289410880 : Int) atom1095Coded) := by
  rw [block015_data_flat072_step]
def block015_data_flat073 : CoefficientMerge.Poly := [(nat_lit 2369, Int.ofNat (nat_lit 12136953868416)), (nat_lit 2370, Int.ofNat (nat_lit 18104289410880))]
theorem block015_data_flat073_step : block015_data_flat073 = (CoefficientMerge.fastMerge block015_data_flat071 block015_data_flat072) := by decide +kernel
theorem block015_data_flat073_original : block015_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12136953868416 : Int) atom1094Coded) (CoefficientMerge.scale (18104289410880 : Int) atom1095Coded)) := by
  rw [block015_data_flat073_step, block015_data_flat071_original, block015_data_flat072_original]
def block015_data_flat074 : CoefficientMerge.Poly := [(nat_lit 2368, Int.ofNat (nat_lit 7360279591680)), (nat_lit 2369, Int.ofNat (nat_lit 12136953868416)), (nat_lit 2370, Int.ofNat (nat_lit 18104289410880))]
theorem block015_data_flat074_step : block015_data_flat074 = (CoefficientMerge.fastMerge block015_data_flat070 block015_data_flat073) := by decide +kernel
theorem block015_data_flat074_original : block015_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7360279591680 : Int) atom1093Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12136953868416 : Int) atom1094Coded) (CoefficientMerge.scale (18104289410880 : Int) atom1095Coded))) := by
  rw [block015_data_flat074_step, block015_data_flat070_original, block015_data_flat073_original]
def block015_data_flat075 : CoefficientMerge.Poly := [(nat_lit 2366, Int.ofNat (nat_lit 1887516691200)), (nat_lit 2367, Int.ofNat (nat_lit 11268696014208)), (nat_lit 2368, Int.ofNat (nat_lit 7360279591680)), (nat_lit 2369, Int.ofNat (nat_lit 12136953868416)), (nat_lit 2370, Int.ofNat (nat_lit 18104289410880))]
theorem block015_data_flat075_step : block015_data_flat075 = (CoefficientMerge.fastMerge block015_data_flat069 block015_data_flat074) := by decide +kernel
theorem block015_data_flat075_original : block015_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1887516691200 : Int) atom1091Coded) (CoefficientMerge.scale (11268696014208 : Int) atom1092Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7360279591680 : Int) atom1093Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12136953868416 : Int) atom1094Coded) (CoefficientMerge.scale (18104289410880 : Int) atom1095Coded)))) := by
  rw [block015_data_flat075_step, block015_data_flat069_original, block015_data_flat074_original]
def block015_data_flat076 : CoefficientMerge.Poly := [(nat_lit 2359, Int.ofNat (nat_lit 2176055048448)), (nat_lit 2360, Int.ofNat (nat_lit 977584809600)), (nat_lit 2363, Int.ofNat (nat_lit 676775635200)), (nat_lit 2364, Int.ofNat (nat_lit 777042201600)), (nat_lit 2365, Int.ofNat (nat_lit 1201322707200)), (nat_lit 2366, Int.ofNat (nat_lit 1887516691200)), (nat_lit 2367, Int.ofNat (nat_lit 11268696014208)), (nat_lit 2368, Int.ofNat (nat_lit 7360279591680)), (nat_lit 2369, Int.ofNat (nat_lit 12136953868416)), (nat_lit 2370, Int.ofNat (nat_lit 18104289410880))]
theorem block015_data_flat076_step : block015_data_flat076 = (CoefficientMerge.fastMerge block015_data_flat066 block015_data_flat075) := by decide +kernel
theorem block015_data_flat076_original : block015_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2176055048448 : Int) atom1086Coded) (CoefficientMerge.scale (977584809600 : Int) atom1087Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (676775635200 : Int) atom1088Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (777042201600 : Int) atom1089Coded) (CoefficientMerge.scale (1201322707200 : Int) atom1090Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1887516691200 : Int) atom1091Coded) (CoefficientMerge.scale (11268696014208 : Int) atom1092Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7360279591680 : Int) atom1093Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12136953868416 : Int) atom1094Coded) (CoefficientMerge.scale (18104289410880 : Int) atom1095Coded))))) := by
  rw [block015_data_flat076_step, block015_data_flat066_original, block015_data_flat075_original]
def block015_data_flat077 : CoefficientMerge.Poly := [(nat_lit 2338, Int.ofNat (nat_lit 5911986468096)), (nat_lit 2339, Int.ofNat (nat_lit 1501404912000)), (nat_lit 2342, Int.ofNat (nat_lit 158747500800)), (nat_lit 2344, Int.ofNat (nat_lit 165266438400)), (nat_lit 2345, Int.ofNat (nat_lit 592446355200)), (nat_lit 2346, Int.ofNat (nat_lit 7715209569408)), (nat_lit 2348, Int.ofNat (nat_lit 666940934016)), (nat_lit 2349, Int.ofNat (nat_lit 5982693393600)), (nat_lit 2350, Int.ofNat (nat_lit 11433151537920)), (nat_lit 2351, Int.ofNat (nat_lit 17685804276000)), (nat_lit 2359, Int.ofNat (nat_lit 2176055048448)), (nat_lit 2360, Int.ofNat (nat_lit 977584809600)), (nat_lit 2363, Int.ofNat (nat_lit 676775635200)), (nat_lit 2364, Int.ofNat (nat_lit 777042201600)), (nat_lit 2365, Int.ofNat (nat_lit 1201322707200)), (nat_lit 2366, Int.ofNat (nat_lit 1887516691200)), (nat_lit 2367, Int.ofNat (nat_lit 11268696014208)), (nat_lit 2368, Int.ofNat (nat_lit 7360279591680)), (nat_lit 2369, Int.ofNat (nat_lit 12136953868416)), (nat_lit 2370, Int.ofNat (nat_lit 18104289410880))]
theorem block015_data_flat077_step : block015_data_flat077 = (CoefficientMerge.fastMerge block015_data_flat057 block015_data_flat076) := by decide +kernel
theorem block015_data_flat077_original : block015_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5911986468096 : Int) atom1076Coded) (CoefficientMerge.scale (1501404912000 : Int) atom1077Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158747500800 : Int) atom1078Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (165266438400 : Int) atom1079Coded) (CoefficientMerge.scale (592446355200 : Int) atom1080Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715209569408 : Int) atom1081Coded) (CoefficientMerge.scale (666940934016 : Int) atom1082Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5982693393600 : Int) atom1083Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11433151537920 : Int) atom1084Coded) (CoefficientMerge.scale (17685804276000 : Int) atom1085Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2176055048448 : Int) atom1086Coded) (CoefficientMerge.scale (977584809600 : Int) atom1087Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (676775635200 : Int) atom1088Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (777042201600 : Int) atom1089Coded) (CoefficientMerge.scale (1201322707200 : Int) atom1090Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1887516691200 : Int) atom1091Coded) (CoefficientMerge.scale (11268696014208 : Int) atom1092Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7360279591680 : Int) atom1093Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12136953868416 : Int) atom1094Coded) (CoefficientMerge.scale (18104289410880 : Int) atom1095Coded)))))) := by
  rw [block015_data_flat077_step, block015_data_flat057_original, block015_data_flat076_original]
def block015_data_flat078 : CoefficientMerge.Poly := [(nat_lit 2119, Int.ofNat (nat_lit 40297587372000)), (nat_lit 2120, Int.ofNat (nat_lit 45912704890500)), (nat_lit 2138, Int.ofNat (nat_lit 39243222144000)), (nat_lit 2139, Int.ofNat (nat_lit 60042692026800)), (nat_lit 2140, Int.ofNat (nat_lit 42753122622000)), (nat_lit 2141, Int.ofNat (nat_lit 53503172881200)), (nat_lit 2160, Int.ofNat (nat_lit 16441201816200)), (nat_lit 2161, Int.ofNat (nat_lit 21090286866600)), (nat_lit 2162, Int.ofNat (nat_lit 31933858238100)), (nat_lit 2183, Int.ofNat (nat_lit 8021538207900)), (nat_lit 2204, Int.ofNat (nat_lit 10915331798700)), (nat_lit 2315, Int.ofNat (nat_lit 2384168341248)), (nat_lit 2316, Int.ofNat (nat_lit 5099671524096)), (nat_lit 2317, Int.ofNat (nat_lit 475114087296)), (nat_lit 2319, Int.ofNat (nat_lit 1116273312000)), (nat_lit 2320, Int.ofNat (nat_lit 773176320000)), (nat_lit 2321, Int.ofNat (nat_lit 847840896000)), (nat_lit 2322, Int.ofNat (nat_lit 261913478400)), (nat_lit 2325, Int.ofNat (nat_lit 3749450450688)), (nat_lit 2337, Int.ofNat (nat_lit 7321536603648)), (nat_lit 2338, Int.ofNat (nat_lit 5911986468096)), (nat_lit 2339, Int.ofNat (nat_lit 1501404912000)), (nat_lit 2342, Int.ofNat (nat_lit 158747500800)), (nat_lit 2344, Int.ofNat (nat_lit 165266438400)), (nat_lit 2345, Int.ofNat (nat_lit 592446355200)), (nat_lit 2346, Int.ofNat (nat_lit 7715209569408)), (nat_lit 2348, Int.ofNat (nat_lit 666940934016)), (nat_lit 2349, Int.ofNat (nat_lit 5982693393600)), (nat_lit 2350, Int.ofNat (nat_lit 11433151537920)), (nat_lit 2351, Int.ofNat (nat_lit 17685804276000)), (nat_lit 2359, Int.ofNat (nat_lit 2176055048448)), (nat_lit 2360, Int.ofNat (nat_lit 977584809600)), (nat_lit 2363, Int.ofNat (nat_lit 676775635200)), (nat_lit 2364, Int.ofNat (nat_lit 777042201600)), (nat_lit 2365, Int.ofNat (nat_lit 1201322707200)), (nat_lit 2366, Int.ofNat (nat_lit 1887516691200)), (nat_lit 2367, Int.ofNat (nat_lit 11268696014208)), (nat_lit 2368, Int.ofNat (nat_lit 7360279591680)), (nat_lit 2369, Int.ofNat (nat_lit 12136953868416)), (nat_lit 2370, Int.ofNat (nat_lit 18104289410880))]
theorem block015_data_flat078_step : block015_data_flat078 = (CoefficientMerge.fastMerge block015_data_flat038 block015_data_flat077) := by decide +kernel
theorem block015_data_flat078_original : block015_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40297587372000 : Int) atom1056Coded) (CoefficientMerge.scale (45912704890500 : Int) atom1057Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39243222144000 : Int) atom1058Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60042692026800 : Int) atom1059Coded) (CoefficientMerge.scale (42753122622000 : Int) atom1060Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53503172881200 : Int) atom1061Coded) (CoefficientMerge.scale (16441201816200 : Int) atom1062Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21090286866600 : Int) atom1063Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31933858238100 : Int) atom1064Coded) (CoefficientMerge.scale (8021538207900 : Int) atom1065Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10915331798700 : Int) atom1066Coded) (CoefficientMerge.scale (2384168341248 : Int) atom1067Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5099671524096 : Int) atom1068Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475114087296 : Int) atom1069Coded) (CoefficientMerge.scale (1116273312000 : Int) atom1070Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (773176320000 : Int) atom1071Coded) (CoefficientMerge.scale (847840896000 : Int) atom1072Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (261913478400 : Int) atom1073Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3749450450688 : Int) atom1074Coded) (CoefficientMerge.scale (7321536603648 : Int) atom1075Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5911986468096 : Int) atom1076Coded) (CoefficientMerge.scale (1501404912000 : Int) atom1077Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158747500800 : Int) atom1078Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (165266438400 : Int) atom1079Coded) (CoefficientMerge.scale (592446355200 : Int) atom1080Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715209569408 : Int) atom1081Coded) (CoefficientMerge.scale (666940934016 : Int) atom1082Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5982693393600 : Int) atom1083Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11433151537920 : Int) atom1084Coded) (CoefficientMerge.scale (17685804276000 : Int) atom1085Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2176055048448 : Int) atom1086Coded) (CoefficientMerge.scale (977584809600 : Int) atom1087Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (676775635200 : Int) atom1088Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (777042201600 : Int) atom1089Coded) (CoefficientMerge.scale (1201322707200 : Int) atom1090Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1887516691200 : Int) atom1091Coded) (CoefficientMerge.scale (11268696014208 : Int) atom1092Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7360279591680 : Int) atom1093Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12136953868416 : Int) atom1094Coded) (CoefficientMerge.scale (18104289410880 : Int) atom1095Coded))))))) := by
  rw [block015_data_flat078_step, block015_data_flat038_original, block015_data_flat077_original]
def block015_data_flat079 : CoefficientMerge.Poly := [(nat_lit 2371, Int.ofNat (nat_lit 25272405692928))]
theorem block015_data_flat079_step : block015_data_flat079 = (CoefficientMerge.scale (25272405692928 : Int) atom1096Coded) := by decide +kernel
theorem block015_data_flat079_original : block015_data_flat079 = (CoefficientMerge.scale (25272405692928 : Int) atom1096Coded) := by
  rw [block015_data_flat079_step]
def block015_data_flat080 : CoefficientMerge.Poly := [(nat_lit 2372, Int.ofNat (nat_lit 32557609173600))]
theorem block015_data_flat080_step : block015_data_flat080 = (CoefficientMerge.scale (32557609173600 : Int) atom1097Coded) := by decide +kernel
theorem block015_data_flat080_original : block015_data_flat080 = (CoefficientMerge.scale (32557609173600 : Int) atom1097Coded) := by
  rw [block015_data_flat080_step]
def block015_data_flat081 : CoefficientMerge.Poly := [(nat_lit 2371, Int.ofNat (nat_lit 25272405692928)), (nat_lit 2372, Int.ofNat (nat_lit 32557609173600))]
theorem block015_data_flat081_step : block015_data_flat081 = (CoefficientMerge.fastMerge block015_data_flat079 block015_data_flat080) := by decide +kernel
theorem block015_data_flat081_original : block015_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25272405692928 : Int) atom1096Coded) (CoefficientMerge.scale (32557609173600 : Int) atom1097Coded)) := by
  rw [block015_data_flat081_step, block015_data_flat079_original, block015_data_flat080_original]
def block015_data_flat082 : CoefficientMerge.Poly := [(nat_lit 2381, Int.ofNat (nat_lit 2814314861952))]
theorem block015_data_flat082_step : block015_data_flat082 = (CoefficientMerge.scale (2814314861952 : Int) atom1098Coded) := by decide +kernel
theorem block015_data_flat082_original : block015_data_flat082 = (CoefficientMerge.scale (2814314861952 : Int) atom1098Coded) := by
  rw [block015_data_flat082_step]
def block015_data_flat083 : CoefficientMerge.Poly := [(nat_lit 2382, Int.ofNat (nat_lit 4832741349504))]
theorem block015_data_flat083_step : block015_data_flat083 = (CoefficientMerge.scale (4832741349504 : Int) atom1099Coded) := by decide +kernel
theorem block015_data_flat083_original : block015_data_flat083 = (CoefficientMerge.scale (4832741349504 : Int) atom1099Coded) := by
  rw [block015_data_flat083_step]
def block015_data_flat084 : CoefficientMerge.Poly := [(nat_lit 2383, Int.ofNat (nat_lit 4664575499904))]
theorem block015_data_flat084_step : block015_data_flat084 = (CoefficientMerge.scale (4664575499904 : Int) atom1100Coded) := by decide +kernel
theorem block015_data_flat084_original : block015_data_flat084 = (CoefficientMerge.scale (4664575499904 : Int) atom1100Coded) := by
  rw [block015_data_flat084_step]
def block015_data_flat085 : CoefficientMerge.Poly := [(nat_lit 2382, Int.ofNat (nat_lit 4832741349504)), (nat_lit 2383, Int.ofNat (nat_lit 4664575499904))]
theorem block015_data_flat085_step : block015_data_flat085 = (CoefficientMerge.fastMerge block015_data_flat083 block015_data_flat084) := by decide +kernel
theorem block015_data_flat085_original : block015_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (4832741349504 : Int) atom1099Coded) (CoefficientMerge.scale (4664575499904 : Int) atom1100Coded)) := by
  rw [block015_data_flat085_step, block015_data_flat083_original, block015_data_flat084_original]
def block015_data_flat086 : CoefficientMerge.Poly := [(nat_lit 2381, Int.ofNat (nat_lit 2814314861952)), (nat_lit 2382, Int.ofNat (nat_lit 4832741349504)), (nat_lit 2383, Int.ofNat (nat_lit 4664575499904))]
theorem block015_data_flat086_step : block015_data_flat086 = (CoefficientMerge.fastMerge block015_data_flat082 block015_data_flat085) := by decide +kernel
theorem block015_data_flat086_original : block015_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2814314861952 : Int) atom1098Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4832741349504 : Int) atom1099Coded) (CoefficientMerge.scale (4664575499904 : Int) atom1100Coded))) := by
  rw [block015_data_flat086_step, block015_data_flat082_original, block015_data_flat085_original]
def block015_data_flat087 : CoefficientMerge.Poly := [(nat_lit 2371, Int.ofNat (nat_lit 25272405692928)), (nat_lit 2372, Int.ofNat (nat_lit 32557609173600)), (nat_lit 2381, Int.ofNat (nat_lit 2814314861952)), (nat_lit 2382, Int.ofNat (nat_lit 4832741349504)), (nat_lit 2383, Int.ofNat (nat_lit 4664575499904))]
theorem block015_data_flat087_step : block015_data_flat087 = (CoefficientMerge.fastMerge block015_data_flat081 block015_data_flat086) := by decide +kernel
theorem block015_data_flat087_original : block015_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25272405692928 : Int) atom1096Coded) (CoefficientMerge.scale (32557609173600 : Int) atom1097Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2814314861952 : Int) atom1098Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4832741349504 : Int) atom1099Coded) (CoefficientMerge.scale (4664575499904 : Int) atom1100Coded)))) := by
  rw [block015_data_flat087_step, block015_data_flat081_original, block015_data_flat086_original]
def block015_data_flat088 : CoefficientMerge.Poly := [(nat_lit 2384, Int.ofNat (nat_lit 5173185285504))]
theorem block015_data_flat088_step : block015_data_flat088 = (CoefficientMerge.scale (5173185285504 : Int) atom1101Coded) := by decide +kernel
theorem block015_data_flat088_original : block015_data_flat088 = (CoefficientMerge.scale (5173185285504 : Int) atom1101Coded) := by
  rw [block015_data_flat088_step]
def block015_data_flat089 : CoefficientMerge.Poly := [(nat_lit 2385, Int.ofNat (nat_lit 4937120152704))]
theorem block015_data_flat089_step : block015_data_flat089 = (CoefficientMerge.scale (4937120152704 : Int) atom1102Coded) := by decide +kernel
theorem block015_data_flat089_original : block015_data_flat089 = (CoefficientMerge.scale (4937120152704 : Int) atom1102Coded) := by
  rw [block015_data_flat089_step]
def block015_data_flat090 : CoefficientMerge.Poly := [(nat_lit 2384, Int.ofNat (nat_lit 5173185285504)), (nat_lit 2385, Int.ofNat (nat_lit 4937120152704))]
theorem block015_data_flat090_step : block015_data_flat090 = (CoefficientMerge.fastMerge block015_data_flat088 block015_data_flat089) := by decide +kernel
theorem block015_data_flat090_original : block015_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5173185285504 : Int) atom1101Coded) (CoefficientMerge.scale (4937120152704 : Int) atom1102Coded)) := by
  rw [block015_data_flat090_step, block015_data_flat088_original, block015_data_flat089_original]
def block015_data_flat091 : CoefficientMerge.Poly := [(nat_lit 2386, Int.ofNat (nat_lit 5452248875904))]
theorem block015_data_flat091_step : block015_data_flat091 = (CoefficientMerge.scale (5452248875904 : Int) atom1103Coded) := by decide +kernel
theorem block015_data_flat091_original : block015_data_flat091 = (CoefficientMerge.scale (5452248875904 : Int) atom1103Coded) := by
  rw [block015_data_flat091_step]
def block015_data_flat092 : CoefficientMerge.Poly := [(nat_lit 2387, Int.ofNat (nat_lit 6229291077504))]
theorem block015_data_flat092_step : block015_data_flat092 = (CoefficientMerge.scale (6229291077504 : Int) atom1104Coded) := by decide +kernel
theorem block015_data_flat092_original : block015_data_flat092 = (CoefficientMerge.scale (6229291077504 : Int) atom1104Coded) := by
  rw [block015_data_flat092_step]
def block015_data_flat093 : CoefficientMerge.Poly := [(nat_lit 2388, Int.ofNat (nat_lit 15678311099904))]
theorem block015_data_flat093_step : block015_data_flat093 = (CoefficientMerge.scale (15678311099904 : Int) atom1105Coded) := by decide +kernel
theorem block015_data_flat093_original : block015_data_flat093 = (CoefficientMerge.scale (15678311099904 : Int) atom1105Coded) := by
  rw [block015_data_flat093_step]
def block015_data_flat094 : CoefficientMerge.Poly := [(nat_lit 2387, Int.ofNat (nat_lit 6229291077504)), (nat_lit 2388, Int.ofNat (nat_lit 15678311099904))]
theorem block015_data_flat094_step : block015_data_flat094 = (CoefficientMerge.fastMerge block015_data_flat092 block015_data_flat093) := by decide +kernel
theorem block015_data_flat094_original : block015_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6229291077504 : Int) atom1104Coded) (CoefficientMerge.scale (15678311099904 : Int) atom1105Coded)) := by
  rw [block015_data_flat094_step, block015_data_flat092_original, block015_data_flat093_original]
def block015_data_flat095 : CoefficientMerge.Poly := [(nat_lit 2386, Int.ofNat (nat_lit 5452248875904)), (nat_lit 2387, Int.ofNat (nat_lit 6229291077504)), (nat_lit 2388, Int.ofNat (nat_lit 15678311099904))]
theorem block015_data_flat095_step : block015_data_flat095 = (CoefficientMerge.fastMerge block015_data_flat091 block015_data_flat094) := by decide +kernel
theorem block015_data_flat095_original : block015_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5452248875904 : Int) atom1103Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6229291077504 : Int) atom1104Coded) (CoefficientMerge.scale (15678311099904 : Int) atom1105Coded))) := by
  rw [block015_data_flat095_step, block015_data_flat091_original, block015_data_flat094_original]
def block015_data_flat096 : CoefficientMerge.Poly := [(nat_lit 2384, Int.ofNat (nat_lit 5173185285504)), (nat_lit 2385, Int.ofNat (nat_lit 4937120152704)), (nat_lit 2386, Int.ofNat (nat_lit 5452248875904)), (nat_lit 2387, Int.ofNat (nat_lit 6229291077504)), (nat_lit 2388, Int.ofNat (nat_lit 15678311099904))]
theorem block015_data_flat096_step : block015_data_flat096 = (CoefficientMerge.fastMerge block015_data_flat090 block015_data_flat095) := by decide +kernel
theorem block015_data_flat096_original : block015_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5173185285504 : Int) atom1101Coded) (CoefficientMerge.scale (4937120152704 : Int) atom1102Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5452248875904 : Int) atom1103Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6229291077504 : Int) atom1104Coded) (CoefficientMerge.scale (15678311099904 : Int) atom1105Coded)))) := by
  rw [block015_data_flat096_step, block015_data_flat090_original, block015_data_flat095_original]
def block015_data_flat097 : CoefficientMerge.Poly := [(nat_lit 2371, Int.ofNat (nat_lit 25272405692928)), (nat_lit 2372, Int.ofNat (nat_lit 32557609173600)), (nat_lit 2381, Int.ofNat (nat_lit 2814314861952)), (nat_lit 2382, Int.ofNat (nat_lit 4832741349504)), (nat_lit 2383, Int.ofNat (nat_lit 4664575499904)), (nat_lit 2384, Int.ofNat (nat_lit 5173185285504)), (nat_lit 2385, Int.ofNat (nat_lit 4937120152704)), (nat_lit 2386, Int.ofNat (nat_lit 5452248875904)), (nat_lit 2387, Int.ofNat (nat_lit 6229291077504)), (nat_lit 2388, Int.ofNat (nat_lit 15678311099904))]
theorem block015_data_flat097_step : block015_data_flat097 = (CoefficientMerge.fastMerge block015_data_flat087 block015_data_flat096) := by decide +kernel
theorem block015_data_flat097_original : block015_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25272405692928 : Int) atom1096Coded) (CoefficientMerge.scale (32557609173600 : Int) atom1097Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2814314861952 : Int) atom1098Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4832741349504 : Int) atom1099Coded) (CoefficientMerge.scale (4664575499904 : Int) atom1100Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5173185285504 : Int) atom1101Coded) (CoefficientMerge.scale (4937120152704 : Int) atom1102Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5452248875904 : Int) atom1103Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6229291077504 : Int) atom1104Coded) (CoefficientMerge.scale (15678311099904 : Int) atom1105Coded))))) := by
  rw [block015_data_flat097_step, block015_data_flat087_original, block015_data_flat096_original]
def block015_data_flat098 : CoefficientMerge.Poly := [(nat_lit 2389, Int.ofNat (nat_lit 13269277891440))]
theorem block015_data_flat098_step : block015_data_flat098 = (CoefficientMerge.scale (13269277891440 : Int) atom1106Coded) := by decide +kernel
theorem block015_data_flat098_original : block015_data_flat098 = (CoefficientMerge.scale (13269277891440 : Int) atom1106Coded) := by
  rw [block015_data_flat098_step]
def block015_data_flat099 : CoefficientMerge.Poly := [(nat_lit 2390, Int.ofNat (nat_lit 19501256738304))]
theorem block015_data_flat099_step : block015_data_flat099 = (CoefficientMerge.scale (19501256738304 : Int) atom1107Coded) := by decide +kernel
theorem block015_data_flat099_original : block015_data_flat099 = (CoefficientMerge.scale (19501256738304 : Int) atom1107Coded) := by
  rw [block015_data_flat099_step]
def block015_data_flat100 : CoefficientMerge.Poly := [(nat_lit 2389, Int.ofNat (nat_lit 13269277891440)), (nat_lit 2390, Int.ofNat (nat_lit 19501256738304))]
theorem block015_data_flat100_step : block015_data_flat100 = (CoefficientMerge.fastMerge block015_data_flat098 block015_data_flat099) := by decide +kernel
theorem block015_data_flat100_original : block015_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269277891440 : Int) atom1106Coded) (CoefficientMerge.scale (19501256738304 : Int) atom1107Coded)) := by
  rw [block015_data_flat100_step, block015_data_flat098_original, block015_data_flat099_original]
def block015_data_flat101 : CoefficientMerge.Poly := [(nat_lit 2391, Int.ofNat (nat_lit 25795167116112))]
theorem block015_data_flat101_step : block015_data_flat101 = (CoefficientMerge.scale (25795167116112 : Int) atom1108Coded) := by decide +kernel
theorem block015_data_flat101_original : block015_data_flat101 = (CoefficientMerge.scale (25795167116112 : Int) atom1108Coded) := by
  rw [block015_data_flat101_step]
def block015_data_flat102 : CoefficientMerge.Poly := [(nat_lit 2392, Int.ofNat (nat_lit 33886745865360))]
theorem block015_data_flat102_step : block015_data_flat102 = (CoefficientMerge.scale (33886745865360 : Int) atom1109Coded) := by decide +kernel
theorem block015_data_flat102_original : block015_data_flat102 = (CoefficientMerge.scale (33886745865360 : Int) atom1109Coded) := by
  rw [block015_data_flat102_step]
def block015_data_flat103 : CoefficientMerge.Poly := [(nat_lit 2393, Int.ofNat (nat_lit 41978324614608))]
theorem block015_data_flat103_step : block015_data_flat103 = (CoefficientMerge.scale (41978324614608 : Int) atom1110Coded) := by decide +kernel
theorem block015_data_flat103_original : block015_data_flat103 = (CoefficientMerge.scale (41978324614608 : Int) atom1110Coded) := by
  rw [block015_data_flat103_step]
def block015_data_flat104 : CoefficientMerge.Poly := [(nat_lit 2392, Int.ofNat (nat_lit 33886745865360)), (nat_lit 2393, Int.ofNat (nat_lit 41978324614608))]
theorem block015_data_flat104_step : block015_data_flat104 = (CoefficientMerge.fastMerge block015_data_flat102 block015_data_flat103) := by decide +kernel
theorem block015_data_flat104_original : block015_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (33886745865360 : Int) atom1109Coded) (CoefficientMerge.scale (41978324614608 : Int) atom1110Coded)) := by
  rw [block015_data_flat104_step, block015_data_flat102_original, block015_data_flat103_original]
def block015_data_flat105 : CoefficientMerge.Poly := [(nat_lit 2391, Int.ofNat (nat_lit 25795167116112)), (nat_lit 2392, Int.ofNat (nat_lit 33886745865360)), (nat_lit 2393, Int.ofNat (nat_lit 41978324614608))]
theorem block015_data_flat105_step : block015_data_flat105 = (CoefficientMerge.fastMerge block015_data_flat101 block015_data_flat104) := by decide +kernel
theorem block015_data_flat105_original : block015_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25795167116112 : Int) atom1108Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33886745865360 : Int) atom1109Coded) (CoefficientMerge.scale (41978324614608 : Int) atom1110Coded))) := by
  rw [block015_data_flat105_step, block015_data_flat101_original, block015_data_flat104_original]
def block015_data_flat106 : CoefficientMerge.Poly := [(nat_lit 2389, Int.ofNat (nat_lit 13269277891440)), (nat_lit 2390, Int.ofNat (nat_lit 19501256738304)), (nat_lit 2391, Int.ofNat (nat_lit 25795167116112)), (nat_lit 2392, Int.ofNat (nat_lit 33886745865360)), (nat_lit 2393, Int.ofNat (nat_lit 41978324614608))]
theorem block015_data_flat106_step : block015_data_flat106 = (CoefficientMerge.fastMerge block015_data_flat100 block015_data_flat105) := by decide +kernel
theorem block015_data_flat106_original : block015_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269277891440 : Int) atom1106Coded) (CoefficientMerge.scale (19501256738304 : Int) atom1107Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25795167116112 : Int) atom1108Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33886745865360 : Int) atom1109Coded) (CoefficientMerge.scale (41978324614608 : Int) atom1110Coded)))) := by
  rw [block015_data_flat106_step, block015_data_flat100_original, block015_data_flat105_original]
def block015_data_flat107 : CoefficientMerge.Poly := [(nat_lit 2403, Int.ofNat (nat_lit 6031211588352))]
theorem block015_data_flat107_step : block015_data_flat107 = (CoefficientMerge.scale (6031211588352 : Int) atom1111Coded) := by decide +kernel
theorem block015_data_flat107_original : block015_data_flat107 = (CoefficientMerge.scale (6031211588352 : Int) atom1111Coded) := by
  rw [block015_data_flat107_step]
def block015_data_flat108 : CoefficientMerge.Poly := [(nat_lit 2404, Int.ofNat (nat_lit 10283151170304))]
theorem block015_data_flat108_step : block015_data_flat108 = (CoefficientMerge.scale (10283151170304 : Int) atom1112Coded) := by decide +kernel
theorem block015_data_flat108_original : block015_data_flat108 = (CoefficientMerge.scale (10283151170304 : Int) atom1112Coded) := by
  rw [block015_data_flat108_step]
def block015_data_flat109 : CoefficientMerge.Poly := [(nat_lit 2403, Int.ofNat (nat_lit 6031211588352)), (nat_lit 2404, Int.ofNat (nat_lit 10283151170304))]
theorem block015_data_flat109_step : block015_data_flat109 = (CoefficientMerge.fastMerge block015_data_flat107 block015_data_flat108) := by decide +kernel
theorem block015_data_flat109_original : block015_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031211588352 : Int) atom1111Coded) (CoefficientMerge.scale (10283151170304 : Int) atom1112Coded)) := by
  rw [block015_data_flat109_step, block015_data_flat107_original, block015_data_flat108_original]
def block015_data_flat110 : CoefficientMerge.Poly := [(nat_lit 2405, Int.ofNat (nat_lit 10455429256704))]
theorem block015_data_flat110_step : block015_data_flat110 = (CoefficientMerge.scale (10455429256704 : Int) atom1113Coded) := by decide +kernel
theorem block015_data_flat110_original : block015_data_flat110 = (CoefficientMerge.scale (10455429256704 : Int) atom1113Coded) := by
  rw [block015_data_flat110_step]
def block015_data_flat111 : CoefficientMerge.Poly := [(nat_lit 2406, Int.ofNat (nat_lit 10569226408704))]
theorem block015_data_flat111_step : block015_data_flat111 = (CoefficientMerge.scale (10569226408704 : Int) atom1114Coded) := by decide +kernel
theorem block015_data_flat111_original : block015_data_flat111 = (CoefficientMerge.scale (10569226408704 : Int) atom1114Coded) := by
  rw [block015_data_flat111_step]
def block015_data_flat112 : CoefficientMerge.Poly := [(nat_lit 2407, Int.ofNat (nat_lit 11007037499904))]
theorem block015_data_flat112_step : block015_data_flat112 = (CoefficientMerge.scale (11007037499904 : Int) atom1115Coded) := by decide +kernel
theorem block015_data_flat112_original : block015_data_flat112 = (CoefficientMerge.scale (11007037499904 : Int) atom1115Coded) := by
  rw [block015_data_flat112_step]
def block015_data_flat113 : CoefficientMerge.Poly := [(nat_lit 2406, Int.ofNat (nat_lit 10569226408704)), (nat_lit 2407, Int.ofNat (nat_lit 11007037499904))]
theorem block015_data_flat113_step : block015_data_flat113 = (CoefficientMerge.fastMerge block015_data_flat111 block015_data_flat112) := by decide +kernel
theorem block015_data_flat113_original : block015_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10569226408704 : Int) atom1114Coded) (CoefficientMerge.scale (11007037499904 : Int) atom1115Coded)) := by
  rw [block015_data_flat113_step, block015_data_flat111_original, block015_data_flat112_original]
def block015_data_flat114 : CoefficientMerge.Poly := [(nat_lit 2405, Int.ofNat (nat_lit 10455429256704)), (nat_lit 2406, Int.ofNat (nat_lit 10569226408704)), (nat_lit 2407, Int.ofNat (nat_lit 11007037499904))]
theorem block015_data_flat114_step : block015_data_flat114 = (CoefficientMerge.fastMerge block015_data_flat110 block015_data_flat113) := by decide +kernel
theorem block015_data_flat114_original : block015_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10455429256704 : Int) atom1113Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10569226408704 : Int) atom1114Coded) (CoefficientMerge.scale (11007037499904 : Int) atom1115Coded))) := by
  rw [block015_data_flat114_step, block015_data_flat110_original, block015_data_flat113_original]
def block015_data_flat115 : CoefficientMerge.Poly := [(nat_lit 2403, Int.ofNat (nat_lit 6031211588352)), (nat_lit 2404, Int.ofNat (nat_lit 10283151170304)), (nat_lit 2405, Int.ofNat (nat_lit 10455429256704)), (nat_lit 2406, Int.ofNat (nat_lit 10569226408704)), (nat_lit 2407, Int.ofNat (nat_lit 11007037499904))]
theorem block015_data_flat115_step : block015_data_flat115 = (CoefficientMerge.fastMerge block015_data_flat109 block015_data_flat114) := by decide +kernel
theorem block015_data_flat115_original : block015_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031211588352 : Int) atom1111Coded) (CoefficientMerge.scale (10283151170304 : Int) atom1112Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10455429256704 : Int) atom1113Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10569226408704 : Int) atom1114Coded) (CoefficientMerge.scale (11007037499904 : Int) atom1115Coded)))) := by
  rw [block015_data_flat115_step, block015_data_flat109_original, block015_data_flat114_original]
def block015_data_flat116 : CoefficientMerge.Poly := [(nat_lit 2389, Int.ofNat (nat_lit 13269277891440)), (nat_lit 2390, Int.ofNat (nat_lit 19501256738304)), (nat_lit 2391, Int.ofNat (nat_lit 25795167116112)), (nat_lit 2392, Int.ofNat (nat_lit 33886745865360)), (nat_lit 2393, Int.ofNat (nat_lit 41978324614608)), (nat_lit 2403, Int.ofNat (nat_lit 6031211588352)), (nat_lit 2404, Int.ofNat (nat_lit 10283151170304)), (nat_lit 2405, Int.ofNat (nat_lit 10455429256704)), (nat_lit 2406, Int.ofNat (nat_lit 10569226408704)), (nat_lit 2407, Int.ofNat (nat_lit 11007037499904))]
theorem block015_data_flat116_step : block015_data_flat116 = (CoefficientMerge.fastMerge block015_data_flat106 block015_data_flat115) := by decide +kernel
theorem block015_data_flat116_original : block015_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269277891440 : Int) atom1106Coded) (CoefficientMerge.scale (19501256738304 : Int) atom1107Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25795167116112 : Int) atom1108Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33886745865360 : Int) atom1109Coded) (CoefficientMerge.scale (41978324614608 : Int) atom1110Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031211588352 : Int) atom1111Coded) (CoefficientMerge.scale (10283151170304 : Int) atom1112Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10455429256704 : Int) atom1113Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10569226408704 : Int) atom1114Coded) (CoefficientMerge.scale (11007037499904 : Int) atom1115Coded))))) := by
  rw [block015_data_flat116_step, block015_data_flat106_original, block015_data_flat115_original]
def block015_data_flat117 : CoefficientMerge.Poly := [(nat_lit 2371, Int.ofNat (nat_lit 25272405692928)), (nat_lit 2372, Int.ofNat (nat_lit 32557609173600)), (nat_lit 2381, Int.ofNat (nat_lit 2814314861952)), (nat_lit 2382, Int.ofNat (nat_lit 4832741349504)), (nat_lit 2383, Int.ofNat (nat_lit 4664575499904)), (nat_lit 2384, Int.ofNat (nat_lit 5173185285504)), (nat_lit 2385, Int.ofNat (nat_lit 4937120152704)), (nat_lit 2386, Int.ofNat (nat_lit 5452248875904)), (nat_lit 2387, Int.ofNat (nat_lit 6229291077504)), (nat_lit 2388, Int.ofNat (nat_lit 15678311099904)), (nat_lit 2389, Int.ofNat (nat_lit 13269277891440)), (nat_lit 2390, Int.ofNat (nat_lit 19501256738304)), (nat_lit 2391, Int.ofNat (nat_lit 25795167116112)), (nat_lit 2392, Int.ofNat (nat_lit 33886745865360)), (nat_lit 2393, Int.ofNat (nat_lit 41978324614608)), (nat_lit 2403, Int.ofNat (nat_lit 6031211588352)), (nat_lit 2404, Int.ofNat (nat_lit 10283151170304)), (nat_lit 2405, Int.ofNat (nat_lit 10455429256704)), (nat_lit 2406, Int.ofNat (nat_lit 10569226408704)), (nat_lit 2407, Int.ofNat (nat_lit 11007037499904))]
theorem block015_data_flat117_step : block015_data_flat117 = (CoefficientMerge.fastMerge block015_data_flat097 block015_data_flat116) := by decide +kernel
theorem block015_data_flat117_original : block015_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25272405692928 : Int) atom1096Coded) (CoefficientMerge.scale (32557609173600 : Int) atom1097Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2814314861952 : Int) atom1098Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4832741349504 : Int) atom1099Coded) (CoefficientMerge.scale (4664575499904 : Int) atom1100Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5173185285504 : Int) atom1101Coded) (CoefficientMerge.scale (4937120152704 : Int) atom1102Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5452248875904 : Int) atom1103Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6229291077504 : Int) atom1104Coded) (CoefficientMerge.scale (15678311099904 : Int) atom1105Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269277891440 : Int) atom1106Coded) (CoefficientMerge.scale (19501256738304 : Int) atom1107Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25795167116112 : Int) atom1108Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33886745865360 : Int) atom1109Coded) (CoefficientMerge.scale (41978324614608 : Int) atom1110Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031211588352 : Int) atom1111Coded) (CoefficientMerge.scale (10283151170304 : Int) atom1112Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10455429256704 : Int) atom1113Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10569226408704 : Int) atom1114Coded) (CoefficientMerge.scale (11007037499904 : Int) atom1115Coded)))))) := by
  rw [block015_data_flat117_step, block015_data_flat097_original, block015_data_flat116_original]
def block015_data_flat118 : CoefficientMerge.Poly := [(nat_lit 2408, Int.ofNat (nat_lit 11706762069504))]
theorem block015_data_flat118_step : block015_data_flat118 = (CoefficientMerge.scale (11706762069504 : Int) atom1116Coded) := by decide +kernel
theorem block015_data_flat118_original : block015_data_flat118 = (CoefficientMerge.scale (11706762069504 : Int) atom1116Coded) := by
  rw [block015_data_flat118_step]
def block015_data_flat119 : CoefficientMerge.Poly := [(nat_lit 2409, Int.ofNat (nat_lit 20771126872704))]
theorem block015_data_flat119_step : block015_data_flat119 = (CoefficientMerge.scale (20771126872704 : Int) atom1117Coded) := by decide +kernel
theorem block015_data_flat119_original : block015_data_flat119 = (CoefficientMerge.scale (20771126872704 : Int) atom1117Coded) := by
  rw [block015_data_flat119_step]
def block015_data_flat120 : CoefficientMerge.Poly := [(nat_lit 2408, Int.ofNat (nat_lit 11706762069504)), (nat_lit 2409, Int.ofNat (nat_lit 20771126872704))]
theorem block015_data_flat120_step : block015_data_flat120 = (CoefficientMerge.fastMerge block015_data_flat118 block015_data_flat119) := by decide +kernel
theorem block015_data_flat120_original : block015_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11706762069504 : Int) atom1116Coded) (CoefficientMerge.scale (20771126872704 : Int) atom1117Coded)) := by
  rw [block015_data_flat120_step, block015_data_flat118_original, block015_data_flat119_original]
def block015_data_flat121 : CoefficientMerge.Poly := [(nat_lit 2410, Int.ofNat (nat_lit 18331227015840))]
theorem block015_data_flat121_step : block015_data_flat121 = (CoefficientMerge.scale (18331227015840 : Int) atom1118Coded) := by decide +kernel
theorem block015_data_flat121_original : block015_data_flat121 = (CoefficientMerge.scale (18331227015840 : Int) atom1118Coded) := by
  rw [block015_data_flat121_step]
def block015_data_flat122 : CoefficientMerge.Poly := [(nat_lit 2411, Int.ofNat (nat_lit 25882377554304))]
theorem block015_data_flat122_step : block015_data_flat122 = (CoefficientMerge.scale (25882377554304 : Int) atom1119Coded) := by decide +kernel
theorem block015_data_flat122_original : block015_data_flat122 = (CoefficientMerge.scale (25882377554304 : Int) atom1119Coded) := by
  rw [block015_data_flat122_step]
def block015_data_flat123 : CoefficientMerge.Poly := [(nat_lit 2412, Int.ofNat (nat_lit 31092814209312))]
theorem block015_data_flat123_step : block015_data_flat123 = (CoefficientMerge.scale (31092814209312 : Int) atom1120Coded) := by decide +kernel
theorem block015_data_flat123_original : block015_data_flat123 = (CoefficientMerge.scale (31092814209312 : Int) atom1120Coded) := by
  rw [block015_data_flat123_step]
def block015_data_flat124 : CoefficientMerge.Poly := [(nat_lit 2411, Int.ofNat (nat_lit 25882377554304)), (nat_lit 2412, Int.ofNat (nat_lit 31092814209312))]
theorem block015_data_flat124_step : block015_data_flat124 = (CoefficientMerge.fastMerge block015_data_flat122 block015_data_flat123) := by decide +kernel
theorem block015_data_flat124_original : block015_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25882377554304 : Int) atom1119Coded) (CoefficientMerge.scale (31092814209312 : Int) atom1120Coded)) := by
  rw [block015_data_flat124_step, block015_data_flat122_original, block015_data_flat123_original]
def block015_data_flat125 : CoefficientMerge.Poly := [(nat_lit 2410, Int.ofNat (nat_lit 18331227015840)), (nat_lit 2411, Int.ofNat (nat_lit 25882377554304)), (nat_lit 2412, Int.ofNat (nat_lit 31092814209312))]
theorem block015_data_flat125_step : block015_data_flat125 = (CoefficientMerge.fastMerge block015_data_flat121 block015_data_flat124) := by decide +kernel
theorem block015_data_flat125_original : block015_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18331227015840 : Int) atom1118Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25882377554304 : Int) atom1119Coded) (CoefficientMerge.scale (31092814209312 : Int) atom1120Coded))) := by
  rw [block015_data_flat125_step, block015_data_flat121_original, block015_data_flat124_original]
def block015_data_flat126 : CoefficientMerge.Poly := [(nat_lit 2408, Int.ofNat (nat_lit 11706762069504)), (nat_lit 2409, Int.ofNat (nat_lit 20771126872704)), (nat_lit 2410, Int.ofNat (nat_lit 18331227015840)), (nat_lit 2411, Int.ofNat (nat_lit 25882377554304)), (nat_lit 2412, Int.ofNat (nat_lit 31092814209312))]
theorem block015_data_flat126_step : block015_data_flat126 = (CoefficientMerge.fastMerge block015_data_flat120 block015_data_flat125) := by decide +kernel
theorem block015_data_flat126_original : block015_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11706762069504 : Int) atom1116Coded) (CoefficientMerge.scale (20771126872704 : Int) atom1117Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18331227015840 : Int) atom1118Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25882377554304 : Int) atom1119Coded) (CoefficientMerge.scale (31092814209312 : Int) atom1120Coded)))) := by
  rw [block015_data_flat126_step, block015_data_flat120_original, block015_data_flat125_original]
def block015_data_flat127 : CoefficientMerge.Poly := [(nat_lit 2413, Int.ofNat (nat_lit 39549718769760))]
theorem block015_data_flat127_step : block015_data_flat127 = (CoefficientMerge.scale (39549718769760 : Int) atom1121Coded) := by decide +kernel
theorem block015_data_flat127_original : block015_data_flat127 = (CoefficientMerge.scale (39549718769760 : Int) atom1121Coded) := by
  rw [block015_data_flat127_step]
def block015_data_flat128 : CoefficientMerge.Poly := [(nat_lit 2414, Int.ofNat (nat_lit 48097833974208))]
theorem block015_data_flat128_step : block015_data_flat128 = (CoefficientMerge.scale (48097833974208 : Int) atom1122Coded) := by decide +kernel
theorem block015_data_flat128_original : block015_data_flat128 = (CoefficientMerge.scale (48097833974208 : Int) atom1122Coded) := by
  rw [block015_data_flat128_step]
def block015_data_flat129 : CoefficientMerge.Poly := [(nat_lit 2413, Int.ofNat (nat_lit 39549718769760)), (nat_lit 2414, Int.ofNat (nat_lit 48097833974208))]
theorem block015_data_flat129_step : block015_data_flat129 = (CoefficientMerge.fastMerge block015_data_flat127 block015_data_flat128) := by decide +kernel
theorem block015_data_flat129_original : block015_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (39549718769760 : Int) atom1121Coded) (CoefficientMerge.scale (48097833974208 : Int) atom1122Coded)) := by
  rw [block015_data_flat129_step, block015_data_flat127_original, block015_data_flat128_original]
def block015_data_flat130 : CoefficientMerge.Poly := [(nat_lit 2425, Int.ofNat (nat_lit 8264724682752))]
theorem block015_data_flat130_step : block015_data_flat130 = (CoefficientMerge.scale (8264724682752 : Int) atom1123Coded) := by decide +kernel
theorem block015_data_flat130_original : block015_data_flat130 = (CoefficientMerge.scale (8264724682752 : Int) atom1123Coded) := by
  rw [block015_data_flat130_step]
def block015_data_flat131 : CoefficientMerge.Poly := [(nat_lit 2426, Int.ofNat (nat_lit 15692732354304))]
theorem block015_data_flat131_step : block015_data_flat131 = (CoefficientMerge.scale (15692732354304 : Int) atom1124Coded) := by decide +kernel
theorem block015_data_flat131_original : block015_data_flat131 = (CoefficientMerge.scale (15692732354304 : Int) atom1124Coded) := by
  rw [block015_data_flat131_step]
def block015_data_flat132 : CoefficientMerge.Poly := [(nat_lit 2427, Int.ofNat (nat_lit 15133866107904))]
theorem block015_data_flat132_step : block015_data_flat132 = (CoefficientMerge.scale (15133866107904 : Int) atom1125Coded) := by decide +kernel
theorem block015_data_flat132_original : block015_data_flat132 = (CoefficientMerge.scale (15133866107904 : Int) atom1125Coded) := by
  rw [block015_data_flat132_step]
def block015_data_flat133 : CoefficientMerge.Poly := [(nat_lit 2426, Int.ofNat (nat_lit 15692732354304)), (nat_lit 2427, Int.ofNat (nat_lit 15133866107904))]
theorem block015_data_flat133_step : block015_data_flat133 = (CoefficientMerge.fastMerge block015_data_flat131 block015_data_flat132) := by decide +kernel
theorem block015_data_flat133_original : block015_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15692732354304 : Int) atom1124Coded) (CoefficientMerge.scale (15133866107904 : Int) atom1125Coded)) := by
  rw [block015_data_flat133_step, block015_data_flat131_original, block015_data_flat132_original]
def block015_data_flat134 : CoefficientMerge.Poly := [(nat_lit 2425, Int.ofNat (nat_lit 8264724682752)), (nat_lit 2426, Int.ofNat (nat_lit 15692732354304)), (nat_lit 2427, Int.ofNat (nat_lit 15133866107904))]
theorem block015_data_flat134_step : block015_data_flat134 = (CoefficientMerge.fastMerge block015_data_flat130 block015_data_flat133) := by decide +kernel
theorem block015_data_flat134_original : block015_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8264724682752 : Int) atom1123Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15692732354304 : Int) atom1124Coded) (CoefficientMerge.scale (15133866107904 : Int) atom1125Coded))) := by
  rw [block015_data_flat134_step, block015_data_flat130_original, block015_data_flat133_original]
def block015_data_flat135 : CoefficientMerge.Poly := [(nat_lit 2413, Int.ofNat (nat_lit 39549718769760)), (nat_lit 2414, Int.ofNat (nat_lit 48097833974208)), (nat_lit 2425, Int.ofNat (nat_lit 8264724682752)), (nat_lit 2426, Int.ofNat (nat_lit 15692732354304)), (nat_lit 2427, Int.ofNat (nat_lit 15133866107904))]
theorem block015_data_flat135_step : block015_data_flat135 = (CoefficientMerge.fastMerge block015_data_flat129 block015_data_flat134) := by decide +kernel
theorem block015_data_flat135_original : block015_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39549718769760 : Int) atom1121Coded) (CoefficientMerge.scale (48097833974208 : Int) atom1122Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8264724682752 : Int) atom1123Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15692732354304 : Int) atom1124Coded) (CoefficientMerge.scale (15133866107904 : Int) atom1125Coded)))) := by
  rw [block015_data_flat135_step, block015_data_flat129_original, block015_data_flat134_original]
def block015_data_flat136 : CoefficientMerge.Poly := [(nat_lit 2408, Int.ofNat (nat_lit 11706762069504)), (nat_lit 2409, Int.ofNat (nat_lit 20771126872704)), (nat_lit 2410, Int.ofNat (nat_lit 18331227015840)), (nat_lit 2411, Int.ofNat (nat_lit 25882377554304)), (nat_lit 2412, Int.ofNat (nat_lit 31092814209312)), (nat_lit 2413, Int.ofNat (nat_lit 39549718769760)), (nat_lit 2414, Int.ofNat (nat_lit 48097833974208)), (nat_lit 2425, Int.ofNat (nat_lit 8264724682752)), (nat_lit 2426, Int.ofNat (nat_lit 15692732354304)), (nat_lit 2427, Int.ofNat (nat_lit 15133866107904))]
theorem block015_data_flat136_step : block015_data_flat136 = (CoefficientMerge.fastMerge block015_data_flat126 block015_data_flat135) := by decide +kernel
theorem block015_data_flat136_original : block015_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11706762069504 : Int) atom1116Coded) (CoefficientMerge.scale (20771126872704 : Int) atom1117Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18331227015840 : Int) atom1118Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25882377554304 : Int) atom1119Coded) (CoefficientMerge.scale (31092814209312 : Int) atom1120Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39549718769760 : Int) atom1121Coded) (CoefficientMerge.scale (48097833974208 : Int) atom1122Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8264724682752 : Int) atom1123Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15692732354304 : Int) atom1124Coded) (CoefficientMerge.scale (15133866107904 : Int) atom1125Coded))))) := by
  rw [block015_data_flat136_step, block015_data_flat126_original, block015_data_flat135_original]
def block015_data_flat137 : CoefficientMerge.Poly := [(nat_lit 2428, Int.ofNat (nat_lit 15326193717504))]
theorem block015_data_flat137_step : block015_data_flat137 = (CoefficientMerge.scale (15326193717504 : Int) atom1126Coded) := by decide +kernel
theorem block015_data_flat137_original : block015_data_flat137 = (CoefficientMerge.scale (15326193717504 : Int) atom1126Coded) := by
  rw [block015_data_flat137_step]
def block015_data_flat138 : CoefficientMerge.Poly := [(nat_lit 2429, Int.ofNat (nat_lit 15780434805504))]
theorem block015_data_flat138_step : block015_data_flat138 = (CoefficientMerge.scale (15780434805504 : Int) atom1127Coded) := by decide +kernel
theorem block015_data_flat138_original : block015_data_flat138 = (CoefficientMerge.scale (15780434805504 : Int) atom1127Coded) := by
  rw [block015_data_flat138_step]
def block015_data_flat139 : CoefficientMerge.Poly := [(nat_lit 2428, Int.ofNat (nat_lit 15326193717504)), (nat_lit 2429, Int.ofNat (nat_lit 15780434805504))]
theorem block015_data_flat139_step : block015_data_flat139 = (CoefficientMerge.fastMerge block015_data_flat137 block015_data_flat138) := by decide +kernel
theorem block015_data_flat139_original : block015_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (15326193717504 : Int) atom1126Coded) (CoefficientMerge.scale (15780434805504 : Int) atom1127Coded)) := by
  rw [block015_data_flat139_step, block015_data_flat137_original, block015_data_flat138_original]
def block015_data_flat140 : CoefficientMerge.Poly := [(nat_lit 2430, Int.ofNat (nat_lit 25134257493504))]
theorem block015_data_flat140_step : block015_data_flat140 = (CoefficientMerge.scale (25134257493504 : Int) atom1128Coded) := by decide +kernel
theorem block015_data_flat140_original : block015_data_flat140 = (CoefficientMerge.scale (25134257493504 : Int) atom1128Coded) := by
  rw [block015_data_flat140_step]
def block015_data_flat141 : CoefficientMerge.Poly := [(nat_lit 2431, Int.ofNat (nat_lit 22912538329440))]
theorem block015_data_flat141_step : block015_data_flat141 = (CoefficientMerge.scale (22912538329440 : Int) atom1129Coded) := by decide +kernel
theorem block015_data_flat141_original : block015_data_flat141 = (CoefficientMerge.scale (22912538329440 : Int) atom1129Coded) := by
  rw [block015_data_flat141_step]
def block015_data_flat142 : CoefficientMerge.Poly := [(nat_lit 2432, Int.ofNat (nat_lit 32993183522304))]
theorem block015_data_flat142_step : block015_data_flat142 = (CoefficientMerge.scale (32993183522304 : Int) atom1130Coded) := by decide +kernel
theorem block015_data_flat142_original : block015_data_flat142 = (CoefficientMerge.scale (32993183522304 : Int) atom1130Coded) := by
  rw [block015_data_flat142_step]
def block015_data_flat143 : CoefficientMerge.Poly := [(nat_lit 2431, Int.ofNat (nat_lit 22912538329440)), (nat_lit 2432, Int.ofNat (nat_lit 32993183522304))]
theorem block015_data_flat143_step : block015_data_flat143 = (CoefficientMerge.fastMerge block015_data_flat141 block015_data_flat142) := by decide +kernel
theorem block015_data_flat143_original : block015_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22912538329440 : Int) atom1129Coded) (CoefficientMerge.scale (32993183522304 : Int) atom1130Coded)) := by
  rw [block015_data_flat143_step, block015_data_flat141_original, block015_data_flat142_original]
def block015_data_flat144 : CoefficientMerge.Poly := [(nat_lit 2430, Int.ofNat (nat_lit 25134257493504)), (nat_lit 2431, Int.ofNat (nat_lit 22912538329440)), (nat_lit 2432, Int.ofNat (nat_lit 32993183522304))]
theorem block015_data_flat144_step : block015_data_flat144 = (CoefficientMerge.fastMerge block015_data_flat140 block015_data_flat143) := by decide +kernel
theorem block015_data_flat144_original : block015_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25134257493504 : Int) atom1128Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22912538329440 : Int) atom1129Coded) (CoefficientMerge.scale (32993183522304 : Int) atom1130Coded))) := by
  rw [block015_data_flat144_step, block015_data_flat140_original, block015_data_flat143_original]
def block015_data_flat145 : CoefficientMerge.Poly := [(nat_lit 2428, Int.ofNat (nat_lit 15326193717504)), (nat_lit 2429, Int.ofNat (nat_lit 15780434805504)), (nat_lit 2430, Int.ofNat (nat_lit 25134257493504)), (nat_lit 2431, Int.ofNat (nat_lit 22912538329440)), (nat_lit 2432, Int.ofNat (nat_lit 32993183522304))]
theorem block015_data_flat145_step : block015_data_flat145 = (CoefficientMerge.fastMerge block015_data_flat139 block015_data_flat144) := by decide +kernel
theorem block015_data_flat145_original : block015_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15326193717504 : Int) atom1126Coded) (CoefficientMerge.scale (15780434805504 : Int) atom1127Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25134257493504 : Int) atom1128Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22912538329440 : Int) atom1129Coded) (CoefficientMerge.scale (32993183522304 : Int) atom1130Coded)))) := by
  rw [block015_data_flat145_step, block015_data_flat139_original, block015_data_flat144_original]
def block015_data_flat146 : CoefficientMerge.Poly := [(nat_lit 2433, Int.ofNat (nat_lit 36268263201312))]
theorem block015_data_flat146_step : block015_data_flat146 = (CoefficientMerge.scale (36268263201312 : Int) atom1131Coded) := by decide +kernel
theorem block015_data_flat146_original : block015_data_flat146 = (CoefficientMerge.scale (36268263201312 : Int) atom1131Coded) := by
  rw [block015_data_flat146_step]
def block015_data_flat147 : CoefficientMerge.Poly := [(nat_lit 2434, Int.ofNat (nat_lit 45020666086560))]
theorem block015_data_flat147_step : block015_data_flat147 = (CoefficientMerge.scale (45020666086560 : Int) atom1132Coded) := by decide +kernel
theorem block015_data_flat147_original : block015_data_flat147 = (CoefficientMerge.scale (45020666086560 : Int) atom1132Coded) := by
  rw [block015_data_flat147_step]
def block015_data_flat148 : CoefficientMerge.Poly := [(nat_lit 2433, Int.ofNat (nat_lit 36268263201312)), (nat_lit 2434, Int.ofNat (nat_lit 45020666086560))]
theorem block015_data_flat148_step : block015_data_flat148 = (CoefficientMerge.fastMerge block015_data_flat146 block015_data_flat147) := by decide +kernel
theorem block015_data_flat148_original : block015_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (36268263201312 : Int) atom1131Coded) (CoefficientMerge.scale (45020666086560 : Int) atom1132Coded)) := by
  rw [block015_data_flat148_step, block015_data_flat146_original, block015_data_flat147_original]
def block015_data_flat149 : CoefficientMerge.Poly := [(nat_lit 2435, Int.ofNat (nat_lit 53773068971808))]
theorem block015_data_flat149_step : block015_data_flat149 = (CoefficientMerge.scale (53773068971808 : Int) atom1133Coded) := by decide +kernel
theorem block015_data_flat149_original : block015_data_flat149 = (CoefficientMerge.scale (53773068971808 : Int) atom1133Coded) := by
  rw [block015_data_flat149_step]
def block015_data_flat150 : CoefficientMerge.Poly := [(nat_lit 2447, Int.ofNat (nat_lit 11440792772352))]
theorem block015_data_flat150_step : block015_data_flat150 = (CoefficientMerge.scale (11440792772352 : Int) atom1134Coded) := by decide +kernel
theorem block015_data_flat150_original : block015_data_flat150 = (CoefficientMerge.scale (11440792772352 : Int) atom1134Coded) := by
  rw [block015_data_flat150_step]
def block015_data_flat151 : CoefficientMerge.Poly := [(nat_lit 2448, Int.ofNat (nat_lit 20459364367104))]
theorem block015_data_flat151_step : block015_data_flat151 = (CoefficientMerge.scale (20459364367104 : Int) atom1135Coded) := by decide +kernel
theorem block015_data_flat151_original : block015_data_flat151 = (CoefficientMerge.scale (20459364367104 : Int) atom1135Coded) := by
  rw [block015_data_flat151_step]
def block015_data_flat152 : CoefficientMerge.Poly := [(nat_lit 2447, Int.ofNat (nat_lit 11440792772352)), (nat_lit 2448, Int.ofNat (nat_lit 20459364367104))]
theorem block015_data_flat152_step : block015_data_flat152 = (CoefficientMerge.fastMerge block015_data_flat150 block015_data_flat151) := by decide +kernel
theorem block015_data_flat152_original : block015_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11440792772352 : Int) atom1134Coded) (CoefficientMerge.scale (20459364367104 : Int) atom1135Coded)) := by
  rw [block015_data_flat152_step, block015_data_flat150_original, block015_data_flat151_original]
def block015_data_flat153 : CoefficientMerge.Poly := [(nat_lit 2435, Int.ofNat (nat_lit 53773068971808)), (nat_lit 2447, Int.ofNat (nat_lit 11440792772352)), (nat_lit 2448, Int.ofNat (nat_lit 20459364367104))]
theorem block015_data_flat153_step : block015_data_flat153 = (CoefficientMerge.fastMerge block015_data_flat149 block015_data_flat152) := by decide +kernel
theorem block015_data_flat153_original : block015_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (53773068971808 : Int) atom1133Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11440792772352 : Int) atom1134Coded) (CoefficientMerge.scale (20459364367104 : Int) atom1135Coded))) := by
  rw [block015_data_flat153_step, block015_data_flat149_original, block015_data_flat152_original]
def block015_data_flat154 : CoefficientMerge.Poly := [(nat_lit 2433, Int.ofNat (nat_lit 36268263201312)), (nat_lit 2434, Int.ofNat (nat_lit 45020666086560)), (nat_lit 2435, Int.ofNat (nat_lit 53773068971808)), (nat_lit 2447, Int.ofNat (nat_lit 11440792772352)), (nat_lit 2448, Int.ofNat (nat_lit 20459364367104))]
theorem block015_data_flat154_step : block015_data_flat154 = (CoefficientMerge.fastMerge block015_data_flat148 block015_data_flat153) := by decide +kernel
theorem block015_data_flat154_original : block015_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36268263201312 : Int) atom1131Coded) (CoefficientMerge.scale (45020666086560 : Int) atom1132Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53773068971808 : Int) atom1133Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11440792772352 : Int) atom1134Coded) (CoefficientMerge.scale (20459364367104 : Int) atom1135Coded)))) := by
  rw [block015_data_flat154_step, block015_data_flat148_original, block015_data_flat153_original]
def block015_data_flat155 : CoefficientMerge.Poly := [(nat_lit 2428, Int.ofNat (nat_lit 15326193717504)), (nat_lit 2429, Int.ofNat (nat_lit 15780434805504)), (nat_lit 2430, Int.ofNat (nat_lit 25134257493504)), (nat_lit 2431, Int.ofNat (nat_lit 22912538329440)), (nat_lit 2432, Int.ofNat (nat_lit 32993183522304)), (nat_lit 2433, Int.ofNat (nat_lit 36268263201312)), (nat_lit 2434, Int.ofNat (nat_lit 45020666086560)), (nat_lit 2435, Int.ofNat (nat_lit 53773068971808)), (nat_lit 2447, Int.ofNat (nat_lit 11440792772352)), (nat_lit 2448, Int.ofNat (nat_lit 20459364367104))]
theorem block015_data_flat155_step : block015_data_flat155 = (CoefficientMerge.fastMerge block015_data_flat145 block015_data_flat154) := by decide +kernel
theorem block015_data_flat155_original : block015_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15326193717504 : Int) atom1126Coded) (CoefficientMerge.scale (15780434805504 : Int) atom1127Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25134257493504 : Int) atom1128Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22912538329440 : Int) atom1129Coded) (CoefficientMerge.scale (32993183522304 : Int) atom1130Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36268263201312 : Int) atom1131Coded) (CoefficientMerge.scale (45020666086560 : Int) atom1132Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53773068971808 : Int) atom1133Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11440792772352 : Int) atom1134Coded) (CoefficientMerge.scale (20459364367104 : Int) atom1135Coded))))) := by
  rw [block015_data_flat155_step, block015_data_flat145_original, block015_data_flat154_original]
def block015_data_flat156 : CoefficientMerge.Poly := [(nat_lit 2408, Int.ofNat (nat_lit 11706762069504)), (nat_lit 2409, Int.ofNat (nat_lit 20771126872704)), (nat_lit 2410, Int.ofNat (nat_lit 18331227015840)), (nat_lit 2411, Int.ofNat (nat_lit 25882377554304)), (nat_lit 2412, Int.ofNat (nat_lit 31092814209312)), (nat_lit 2413, Int.ofNat (nat_lit 39549718769760)), (nat_lit 2414, Int.ofNat (nat_lit 48097833974208)), (nat_lit 2425, Int.ofNat (nat_lit 8264724682752)), (nat_lit 2426, Int.ofNat (nat_lit 15692732354304)), (nat_lit 2427, Int.ofNat (nat_lit 15133866107904)), (nat_lit 2428, Int.ofNat (nat_lit 15326193717504)), (nat_lit 2429, Int.ofNat (nat_lit 15780434805504)), (nat_lit 2430, Int.ofNat (nat_lit 25134257493504)), (nat_lit 2431, Int.ofNat (nat_lit 22912538329440)), (nat_lit 2432, Int.ofNat (nat_lit 32993183522304)), (nat_lit 2433, Int.ofNat (nat_lit 36268263201312)), (nat_lit 2434, Int.ofNat (nat_lit 45020666086560)), (nat_lit 2435, Int.ofNat (nat_lit 53773068971808)), (nat_lit 2447, Int.ofNat (nat_lit 11440792772352)), (nat_lit 2448, Int.ofNat (nat_lit 20459364367104))]
theorem block015_data_flat156_step : block015_data_flat156 = (CoefficientMerge.fastMerge block015_data_flat136 block015_data_flat155) := by decide +kernel
theorem block015_data_flat156_original : block015_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11706762069504 : Int) atom1116Coded) (CoefficientMerge.scale (20771126872704 : Int) atom1117Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18331227015840 : Int) atom1118Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25882377554304 : Int) atom1119Coded) (CoefficientMerge.scale (31092814209312 : Int) atom1120Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39549718769760 : Int) atom1121Coded) (CoefficientMerge.scale (48097833974208 : Int) atom1122Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8264724682752 : Int) atom1123Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15692732354304 : Int) atom1124Coded) (CoefficientMerge.scale (15133866107904 : Int) atom1125Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15326193717504 : Int) atom1126Coded) (CoefficientMerge.scale (15780434805504 : Int) atom1127Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25134257493504 : Int) atom1128Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22912538329440 : Int) atom1129Coded) (CoefficientMerge.scale (32993183522304 : Int) atom1130Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36268263201312 : Int) atom1131Coded) (CoefficientMerge.scale (45020666086560 : Int) atom1132Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53773068971808 : Int) atom1133Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11440792772352 : Int) atom1134Coded) (CoefficientMerge.scale (20459364367104 : Int) atom1135Coded)))))) := by
  rw [block015_data_flat156_step, block015_data_flat136_original, block015_data_flat155_original]
def block015_data_flat157 : CoefficientMerge.Poly := [(nat_lit 2371, Int.ofNat (nat_lit 25272405692928)), (nat_lit 2372, Int.ofNat (nat_lit 32557609173600)), (nat_lit 2381, Int.ofNat (nat_lit 2814314861952)), (nat_lit 2382, Int.ofNat (nat_lit 4832741349504)), (nat_lit 2383, Int.ofNat (nat_lit 4664575499904)), (nat_lit 2384, Int.ofNat (nat_lit 5173185285504)), (nat_lit 2385, Int.ofNat (nat_lit 4937120152704)), (nat_lit 2386, Int.ofNat (nat_lit 5452248875904)), (nat_lit 2387, Int.ofNat (nat_lit 6229291077504)), (nat_lit 2388, Int.ofNat (nat_lit 15678311099904)), (nat_lit 2389, Int.ofNat (nat_lit 13269277891440)), (nat_lit 2390, Int.ofNat (nat_lit 19501256738304)), (nat_lit 2391, Int.ofNat (nat_lit 25795167116112)), (nat_lit 2392, Int.ofNat (nat_lit 33886745865360)), (nat_lit 2393, Int.ofNat (nat_lit 41978324614608)), (nat_lit 2403, Int.ofNat (nat_lit 6031211588352)), (nat_lit 2404, Int.ofNat (nat_lit 10283151170304)), (nat_lit 2405, Int.ofNat (nat_lit 10455429256704)), (nat_lit 2406, Int.ofNat (nat_lit 10569226408704)), (nat_lit 2407, Int.ofNat (nat_lit 11007037499904)), (nat_lit 2408, Int.ofNat (nat_lit 11706762069504)), (nat_lit 2409, Int.ofNat (nat_lit 20771126872704)), (nat_lit 2410, Int.ofNat (nat_lit 18331227015840)), (nat_lit 2411, Int.ofNat (nat_lit 25882377554304)), (nat_lit 2412, Int.ofNat (nat_lit 31092814209312)), (nat_lit 2413, Int.ofNat (nat_lit 39549718769760)), (nat_lit 2414, Int.ofNat (nat_lit 48097833974208)), (nat_lit 2425, Int.ofNat (nat_lit 8264724682752)), (nat_lit 2426, Int.ofNat (nat_lit 15692732354304)), (nat_lit 2427, Int.ofNat (nat_lit 15133866107904)), (nat_lit 2428, Int.ofNat (nat_lit 15326193717504)), (nat_lit 2429, Int.ofNat (nat_lit 15780434805504)), (nat_lit 2430, Int.ofNat (nat_lit 25134257493504)), (nat_lit 2431, Int.ofNat (nat_lit 22912538329440)), (nat_lit 2432, Int.ofNat (nat_lit 32993183522304)), (nat_lit 2433, Int.ofNat (nat_lit 36268263201312)), (nat_lit 2434, Int.ofNat (nat_lit 45020666086560)), (nat_lit 2435, Int.ofNat (nat_lit 53773068971808)), (nat_lit 2447, Int.ofNat (nat_lit 11440792772352)), (nat_lit 2448, Int.ofNat (nat_lit 20459364367104))]
theorem block015_data_flat157_step : block015_data_flat157 = (CoefficientMerge.fastMerge block015_data_flat117 block015_data_flat156) := by decide +kernel
theorem block015_data_flat157_original : block015_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25272405692928 : Int) atom1096Coded) (CoefficientMerge.scale (32557609173600 : Int) atom1097Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2814314861952 : Int) atom1098Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4832741349504 : Int) atom1099Coded) (CoefficientMerge.scale (4664575499904 : Int) atom1100Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5173185285504 : Int) atom1101Coded) (CoefficientMerge.scale (4937120152704 : Int) atom1102Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5452248875904 : Int) atom1103Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6229291077504 : Int) atom1104Coded) (CoefficientMerge.scale (15678311099904 : Int) atom1105Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269277891440 : Int) atom1106Coded) (CoefficientMerge.scale (19501256738304 : Int) atom1107Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25795167116112 : Int) atom1108Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33886745865360 : Int) atom1109Coded) (CoefficientMerge.scale (41978324614608 : Int) atom1110Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031211588352 : Int) atom1111Coded) (CoefficientMerge.scale (10283151170304 : Int) atom1112Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10455429256704 : Int) atom1113Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10569226408704 : Int) atom1114Coded) (CoefficientMerge.scale (11007037499904 : Int) atom1115Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11706762069504 : Int) atom1116Coded) (CoefficientMerge.scale (20771126872704 : Int) atom1117Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18331227015840 : Int) atom1118Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25882377554304 : Int) atom1119Coded) (CoefficientMerge.scale (31092814209312 : Int) atom1120Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39549718769760 : Int) atom1121Coded) (CoefficientMerge.scale (48097833974208 : Int) atom1122Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8264724682752 : Int) atom1123Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15692732354304 : Int) atom1124Coded) (CoefficientMerge.scale (15133866107904 : Int) atom1125Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15326193717504 : Int) atom1126Coded) (CoefficientMerge.scale (15780434805504 : Int) atom1127Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25134257493504 : Int) atom1128Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22912538329440 : Int) atom1129Coded) (CoefficientMerge.scale (32993183522304 : Int) atom1130Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36268263201312 : Int) atom1131Coded) (CoefficientMerge.scale (45020666086560 : Int) atom1132Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53773068971808 : Int) atom1133Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11440792772352 : Int) atom1134Coded) (CoefficientMerge.scale (20459364367104 : Int) atom1135Coded))))))) := by
  rw [block015_data_flat157_step, block015_data_flat117_original, block015_data_flat156_original]
def block015_data_flat158 : CoefficientMerge.Poly := [(nat_lit 2119, Int.ofNat (nat_lit 40297587372000)), (nat_lit 2120, Int.ofNat (nat_lit 45912704890500)), (nat_lit 2138, Int.ofNat (nat_lit 39243222144000)), (nat_lit 2139, Int.ofNat (nat_lit 60042692026800)), (nat_lit 2140, Int.ofNat (nat_lit 42753122622000)), (nat_lit 2141, Int.ofNat (nat_lit 53503172881200)), (nat_lit 2160, Int.ofNat (nat_lit 16441201816200)), (nat_lit 2161, Int.ofNat (nat_lit 21090286866600)), (nat_lit 2162, Int.ofNat (nat_lit 31933858238100)), (nat_lit 2183, Int.ofNat (nat_lit 8021538207900)), (nat_lit 2204, Int.ofNat (nat_lit 10915331798700)), (nat_lit 2315, Int.ofNat (nat_lit 2384168341248)), (nat_lit 2316, Int.ofNat (nat_lit 5099671524096)), (nat_lit 2317, Int.ofNat (nat_lit 475114087296)), (nat_lit 2319, Int.ofNat (nat_lit 1116273312000)), (nat_lit 2320, Int.ofNat (nat_lit 773176320000)), (nat_lit 2321, Int.ofNat (nat_lit 847840896000)), (nat_lit 2322, Int.ofNat (nat_lit 261913478400)), (nat_lit 2325, Int.ofNat (nat_lit 3749450450688)), (nat_lit 2337, Int.ofNat (nat_lit 7321536603648)), (nat_lit 2338, Int.ofNat (nat_lit 5911986468096)), (nat_lit 2339, Int.ofNat (nat_lit 1501404912000)), (nat_lit 2342, Int.ofNat (nat_lit 158747500800)), (nat_lit 2344, Int.ofNat (nat_lit 165266438400)), (nat_lit 2345, Int.ofNat (nat_lit 592446355200)), (nat_lit 2346, Int.ofNat (nat_lit 7715209569408)), (nat_lit 2348, Int.ofNat (nat_lit 666940934016)), (nat_lit 2349, Int.ofNat (nat_lit 5982693393600)), (nat_lit 2350, Int.ofNat (nat_lit 11433151537920)), (nat_lit 2351, Int.ofNat (nat_lit 17685804276000)), (nat_lit 2359, Int.ofNat (nat_lit 2176055048448)), (nat_lit 2360, Int.ofNat (nat_lit 977584809600)), (nat_lit 2363, Int.ofNat (nat_lit 676775635200)), (nat_lit 2364, Int.ofNat (nat_lit 777042201600)), (nat_lit 2365, Int.ofNat (nat_lit 1201322707200)), (nat_lit 2366, Int.ofNat (nat_lit 1887516691200)), (nat_lit 2367, Int.ofNat (nat_lit 11268696014208)), (nat_lit 2368, Int.ofNat (nat_lit 7360279591680)), (nat_lit 2369, Int.ofNat (nat_lit 12136953868416)), (nat_lit 2370, Int.ofNat (nat_lit 18104289410880)), (nat_lit 2371, Int.ofNat (nat_lit 25272405692928)), (nat_lit 2372, Int.ofNat (nat_lit 32557609173600)), (nat_lit 2381, Int.ofNat (nat_lit 2814314861952)), (nat_lit 2382, Int.ofNat (nat_lit 4832741349504)), (nat_lit 2383, Int.ofNat (nat_lit 4664575499904)), (nat_lit 2384, Int.ofNat (nat_lit 5173185285504)), (nat_lit 2385, Int.ofNat (nat_lit 4937120152704)), (nat_lit 2386, Int.ofNat (nat_lit 5452248875904)), (nat_lit 2387, Int.ofNat (nat_lit 6229291077504)), (nat_lit 2388, Int.ofNat (nat_lit 15678311099904)), (nat_lit 2389, Int.ofNat (nat_lit 13269277891440)), (nat_lit 2390, Int.ofNat (nat_lit 19501256738304)), (nat_lit 2391, Int.ofNat (nat_lit 25795167116112)), (nat_lit 2392, Int.ofNat (nat_lit 33886745865360)), (nat_lit 2393, Int.ofNat (nat_lit 41978324614608)), (nat_lit 2403, Int.ofNat (nat_lit 6031211588352)), (nat_lit 2404, Int.ofNat (nat_lit 10283151170304)), (nat_lit 2405, Int.ofNat (nat_lit 10455429256704)), (nat_lit 2406, Int.ofNat (nat_lit 10569226408704)), (nat_lit 2407, Int.ofNat (nat_lit 11007037499904)), (nat_lit 2408, Int.ofNat (nat_lit 11706762069504)), (nat_lit 2409, Int.ofNat (nat_lit 20771126872704)), (nat_lit 2410, Int.ofNat (nat_lit 18331227015840)), (nat_lit 2411, Int.ofNat (nat_lit 25882377554304)), (nat_lit 2412, Int.ofNat (nat_lit 31092814209312)), (nat_lit 2413, Int.ofNat (nat_lit 39549718769760)), (nat_lit 2414, Int.ofNat (nat_lit 48097833974208)), (nat_lit 2425, Int.ofNat (nat_lit 8264724682752)), (nat_lit 2426, Int.ofNat (nat_lit 15692732354304)), (nat_lit 2427, Int.ofNat (nat_lit 15133866107904)), (nat_lit 2428, Int.ofNat (nat_lit 15326193717504)), (nat_lit 2429, Int.ofNat (nat_lit 15780434805504)), (nat_lit 2430, Int.ofNat (nat_lit 25134257493504)), (nat_lit 2431, Int.ofNat (nat_lit 22912538329440)), (nat_lit 2432, Int.ofNat (nat_lit 32993183522304)), (nat_lit 2433, Int.ofNat (nat_lit 36268263201312)), (nat_lit 2434, Int.ofNat (nat_lit 45020666086560)), (nat_lit 2435, Int.ofNat (nat_lit 53773068971808)), (nat_lit 2447, Int.ofNat (nat_lit 11440792772352)), (nat_lit 2448, Int.ofNat (nat_lit 20459364367104))]
theorem block015_data_flat158_step : block015_data_flat158 = (CoefficientMerge.fastMerge block015_data_flat078 block015_data_flat157) := by decide +kernel
theorem block015_data_flat158_original : block015_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40297587372000 : Int) atom1056Coded) (CoefficientMerge.scale (45912704890500 : Int) atom1057Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39243222144000 : Int) atom1058Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60042692026800 : Int) atom1059Coded) (CoefficientMerge.scale (42753122622000 : Int) atom1060Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53503172881200 : Int) atom1061Coded) (CoefficientMerge.scale (16441201816200 : Int) atom1062Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21090286866600 : Int) atom1063Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31933858238100 : Int) atom1064Coded) (CoefficientMerge.scale (8021538207900 : Int) atom1065Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10915331798700 : Int) atom1066Coded) (CoefficientMerge.scale (2384168341248 : Int) atom1067Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5099671524096 : Int) atom1068Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475114087296 : Int) atom1069Coded) (CoefficientMerge.scale (1116273312000 : Int) atom1070Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (773176320000 : Int) atom1071Coded) (CoefficientMerge.scale (847840896000 : Int) atom1072Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (261913478400 : Int) atom1073Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3749450450688 : Int) atom1074Coded) (CoefficientMerge.scale (7321536603648 : Int) atom1075Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5911986468096 : Int) atom1076Coded) (CoefficientMerge.scale (1501404912000 : Int) atom1077Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158747500800 : Int) atom1078Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (165266438400 : Int) atom1079Coded) (CoefficientMerge.scale (592446355200 : Int) atom1080Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715209569408 : Int) atom1081Coded) (CoefficientMerge.scale (666940934016 : Int) atom1082Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5982693393600 : Int) atom1083Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11433151537920 : Int) atom1084Coded) (CoefficientMerge.scale (17685804276000 : Int) atom1085Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2176055048448 : Int) atom1086Coded) (CoefficientMerge.scale (977584809600 : Int) atom1087Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (676775635200 : Int) atom1088Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (777042201600 : Int) atom1089Coded) (CoefficientMerge.scale (1201322707200 : Int) atom1090Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1887516691200 : Int) atom1091Coded) (CoefficientMerge.scale (11268696014208 : Int) atom1092Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7360279591680 : Int) atom1093Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12136953868416 : Int) atom1094Coded) (CoefficientMerge.scale (18104289410880 : Int) atom1095Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25272405692928 : Int) atom1096Coded) (CoefficientMerge.scale (32557609173600 : Int) atom1097Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2814314861952 : Int) atom1098Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4832741349504 : Int) atom1099Coded) (CoefficientMerge.scale (4664575499904 : Int) atom1100Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5173185285504 : Int) atom1101Coded) (CoefficientMerge.scale (4937120152704 : Int) atom1102Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5452248875904 : Int) atom1103Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6229291077504 : Int) atom1104Coded) (CoefficientMerge.scale (15678311099904 : Int) atom1105Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269277891440 : Int) atom1106Coded) (CoefficientMerge.scale (19501256738304 : Int) atom1107Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25795167116112 : Int) atom1108Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33886745865360 : Int) atom1109Coded) (CoefficientMerge.scale (41978324614608 : Int) atom1110Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031211588352 : Int) atom1111Coded) (CoefficientMerge.scale (10283151170304 : Int) atom1112Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10455429256704 : Int) atom1113Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10569226408704 : Int) atom1114Coded) (CoefficientMerge.scale (11007037499904 : Int) atom1115Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11706762069504 : Int) atom1116Coded) (CoefficientMerge.scale (20771126872704 : Int) atom1117Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18331227015840 : Int) atom1118Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25882377554304 : Int) atom1119Coded) (CoefficientMerge.scale (31092814209312 : Int) atom1120Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39549718769760 : Int) atom1121Coded) (CoefficientMerge.scale (48097833974208 : Int) atom1122Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8264724682752 : Int) atom1123Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15692732354304 : Int) atom1124Coded) (CoefficientMerge.scale (15133866107904 : Int) atom1125Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15326193717504 : Int) atom1126Coded) (CoefficientMerge.scale (15780434805504 : Int) atom1127Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25134257493504 : Int) atom1128Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22912538329440 : Int) atom1129Coded) (CoefficientMerge.scale (32993183522304 : Int) atom1130Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36268263201312 : Int) atom1131Coded) (CoefficientMerge.scale (45020666086560 : Int) atom1132Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53773068971808 : Int) atom1133Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11440792772352 : Int) atom1134Coded) (CoefficientMerge.scale (20459364367104 : Int) atom1135Coded)))))))) := by
  rw [block015_data_flat158_step, block015_data_flat078_original, block015_data_flat157_original]
def block015_data_flat159 : CoefficientMerge.Poly := [(nat_lit 2119, Int.ofNat (nat_lit 40297587372000)), (nat_lit 2120, Int.ofNat (nat_lit 45912704890500)), (nat_lit 2138, Int.ofNat (nat_lit 39243222144000)), (nat_lit 2139, Int.ofNat (nat_lit 60042692026800)), (nat_lit 2140, Int.ofNat (nat_lit 42753122622000)), (nat_lit 2141, Int.ofNat (nat_lit 53503172881200)), (nat_lit 2160, Int.ofNat (nat_lit 16441201816200)), (nat_lit 2161, Int.ofNat (nat_lit 21090286866600)), (nat_lit 2162, Int.ofNat (nat_lit 31933858238100)), (nat_lit 2183, Int.ofNat (nat_lit 8021538207900)), (nat_lit 2204, Int.ofNat (nat_lit 10915331798700)), (nat_lit 2315, Int.ofNat (nat_lit 2384168341248)), (nat_lit 2316, Int.ofNat (nat_lit 5099671524096)), (nat_lit 2317, Int.ofNat (nat_lit 475114087296)), (nat_lit 2319, Int.ofNat (nat_lit 1116273312000)), (nat_lit 2320, Int.ofNat (nat_lit 773176320000)), (nat_lit 2321, Int.ofNat (nat_lit 847840896000)), (nat_lit 2322, Int.ofNat (nat_lit 261913478400)), (nat_lit 2325, Int.ofNat (nat_lit 3749450450688)), (nat_lit 2337, Int.ofNat (nat_lit 7321536603648)), (nat_lit 2338, Int.ofNat (nat_lit 5911986468096)), (nat_lit 2339, Int.ofNat (nat_lit 1501404912000)), (nat_lit 2342, Int.ofNat (nat_lit 158747500800)), (nat_lit 2344, Int.ofNat (nat_lit 165266438400)), (nat_lit 2345, Int.ofNat (nat_lit 592446355200)), (nat_lit 2346, Int.ofNat (nat_lit 7715209569408)), (nat_lit 2348, Int.ofNat (nat_lit 666940934016)), (nat_lit 2349, Int.ofNat (nat_lit 5982693393600)), (nat_lit 2350, Int.ofNat (nat_lit 11433151537920)), (nat_lit 2351, Int.ofNat (nat_lit 17685804276000)), (nat_lit 2359, Int.ofNat (nat_lit 2176055048448)), (nat_lit 2360, Int.ofNat (nat_lit 977584809600)), (nat_lit 2363, Int.ofNat (nat_lit 676775635200)), (nat_lit 2364, Int.ofNat (nat_lit 777042201600)), (nat_lit 2365, Int.ofNat (nat_lit 1201322707200)), (nat_lit 2366, Int.ofNat (nat_lit 1887516691200)), (nat_lit 2367, Int.ofNat (nat_lit 11268696014208)), (nat_lit 2368, Int.ofNat (nat_lit 7360279591680)), (nat_lit 2369, Int.ofNat (nat_lit 12136953868416)), (nat_lit 2370, Int.ofNat (nat_lit 18104289410880)), (nat_lit 2371, Int.ofNat (nat_lit 25272405692928)), (nat_lit 2372, Int.ofNat (nat_lit 32557609173600)), (nat_lit 2381, Int.ofNat (nat_lit 2814314861952)), (nat_lit 2382, Int.ofNat (nat_lit 4832741349504)), (nat_lit 2383, Int.ofNat (nat_lit 4664575499904)), (nat_lit 2384, Int.ofNat (nat_lit 5173185285504)), (nat_lit 2385, Int.ofNat (nat_lit 4937120152704)), (nat_lit 2386, Int.ofNat (nat_lit 5452248875904)), (nat_lit 2387, Int.ofNat (nat_lit 6229291077504)), (nat_lit 2388, Int.ofNat (nat_lit 15678311099904)), (nat_lit 2389, Int.ofNat (nat_lit 13269277891440)), (nat_lit 2390, Int.ofNat (nat_lit 19501256738304)), (nat_lit 2391, Int.ofNat (nat_lit 25795167116112)), (nat_lit 2392, Int.ofNat (nat_lit 33886745865360)), (nat_lit 2393, Int.ofNat (nat_lit 41978324614608)), (nat_lit 2403, Int.ofNat (nat_lit 6031211588352)), (nat_lit 2404, Int.ofNat (nat_lit 10283151170304)), (nat_lit 2405, Int.ofNat (nat_lit 10455429256704)), (nat_lit 2406, Int.ofNat (nat_lit 10569226408704)), (nat_lit 2407, Int.ofNat (nat_lit 11007037499904)), (nat_lit 2408, Int.ofNat (nat_lit 11706762069504)), (nat_lit 2409, Int.ofNat (nat_lit 20771126872704)), (nat_lit 2410, Int.ofNat (nat_lit 18331227015840)), (nat_lit 2411, Int.ofNat (nat_lit 25882377554304)), (nat_lit 2412, Int.ofNat (nat_lit 31092814209312)), (nat_lit 2413, Int.ofNat (nat_lit 39549718769760)), (nat_lit 2414, Int.ofNat (nat_lit 48097833974208)), (nat_lit 2425, Int.ofNat (nat_lit 8264724682752)), (nat_lit 2426, Int.ofNat (nat_lit 15692732354304)), (nat_lit 2427, Int.ofNat (nat_lit 15133866107904)), (nat_lit 2428, Int.ofNat (nat_lit 15326193717504)), (nat_lit 2429, Int.ofNat (nat_lit 15780434805504)), (nat_lit 2430, Int.ofNat (nat_lit 25134257493504)), (nat_lit 2431, Int.ofNat (nat_lit 22912538329440)), (nat_lit 2432, Int.ofNat (nat_lit 32993183522304)), (nat_lit 2433, Int.ofNat (nat_lit 36268263201312)), (nat_lit 2434, Int.ofNat (nat_lit 45020666086560)), (nat_lit 2435, Int.ofNat (nat_lit 53773068971808)), (nat_lit 2447, Int.ofNat (nat_lit 11440792772352)), (nat_lit 2448, Int.ofNat (nat_lit 20459364367104))]
theorem block015_data_flat159_step : block015_data_flat159 = (CoefficientMerge.trim block015_data_flat158) := by decide +kernel
theorem block015_data_flat159_original : block015_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40297587372000 : Int) atom1056Coded) (CoefficientMerge.scale (45912704890500 : Int) atom1057Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39243222144000 : Int) atom1058Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60042692026800 : Int) atom1059Coded) (CoefficientMerge.scale (42753122622000 : Int) atom1060Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53503172881200 : Int) atom1061Coded) (CoefficientMerge.scale (16441201816200 : Int) atom1062Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21090286866600 : Int) atom1063Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31933858238100 : Int) atom1064Coded) (CoefficientMerge.scale (8021538207900 : Int) atom1065Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10915331798700 : Int) atom1066Coded) (CoefficientMerge.scale (2384168341248 : Int) atom1067Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5099671524096 : Int) atom1068Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475114087296 : Int) atom1069Coded) (CoefficientMerge.scale (1116273312000 : Int) atom1070Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (773176320000 : Int) atom1071Coded) (CoefficientMerge.scale (847840896000 : Int) atom1072Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (261913478400 : Int) atom1073Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3749450450688 : Int) atom1074Coded) (CoefficientMerge.scale (7321536603648 : Int) atom1075Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5911986468096 : Int) atom1076Coded) (CoefficientMerge.scale (1501404912000 : Int) atom1077Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158747500800 : Int) atom1078Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (165266438400 : Int) atom1079Coded) (CoefficientMerge.scale (592446355200 : Int) atom1080Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715209569408 : Int) atom1081Coded) (CoefficientMerge.scale (666940934016 : Int) atom1082Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5982693393600 : Int) atom1083Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11433151537920 : Int) atom1084Coded) (CoefficientMerge.scale (17685804276000 : Int) atom1085Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2176055048448 : Int) atom1086Coded) (CoefficientMerge.scale (977584809600 : Int) atom1087Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (676775635200 : Int) atom1088Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (777042201600 : Int) atom1089Coded) (CoefficientMerge.scale (1201322707200 : Int) atom1090Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1887516691200 : Int) atom1091Coded) (CoefficientMerge.scale (11268696014208 : Int) atom1092Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7360279591680 : Int) atom1093Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12136953868416 : Int) atom1094Coded) (CoefficientMerge.scale (18104289410880 : Int) atom1095Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25272405692928 : Int) atom1096Coded) (CoefficientMerge.scale (32557609173600 : Int) atom1097Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2814314861952 : Int) atom1098Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4832741349504 : Int) atom1099Coded) (CoefficientMerge.scale (4664575499904 : Int) atom1100Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5173185285504 : Int) atom1101Coded) (CoefficientMerge.scale (4937120152704 : Int) atom1102Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5452248875904 : Int) atom1103Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6229291077504 : Int) atom1104Coded) (CoefficientMerge.scale (15678311099904 : Int) atom1105Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269277891440 : Int) atom1106Coded) (CoefficientMerge.scale (19501256738304 : Int) atom1107Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25795167116112 : Int) atom1108Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33886745865360 : Int) atom1109Coded) (CoefficientMerge.scale (41978324614608 : Int) atom1110Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031211588352 : Int) atom1111Coded) (CoefficientMerge.scale (10283151170304 : Int) atom1112Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10455429256704 : Int) atom1113Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10569226408704 : Int) atom1114Coded) (CoefficientMerge.scale (11007037499904 : Int) atom1115Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11706762069504 : Int) atom1116Coded) (CoefficientMerge.scale (20771126872704 : Int) atom1117Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18331227015840 : Int) atom1118Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25882377554304 : Int) atom1119Coded) (CoefficientMerge.scale (31092814209312 : Int) atom1120Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39549718769760 : Int) atom1121Coded) (CoefficientMerge.scale (48097833974208 : Int) atom1122Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8264724682752 : Int) atom1123Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15692732354304 : Int) atom1124Coded) (CoefficientMerge.scale (15133866107904 : Int) atom1125Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15326193717504 : Int) atom1126Coded) (CoefficientMerge.scale (15780434805504 : Int) atom1127Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25134257493504 : Int) atom1128Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22912538329440 : Int) atom1129Coded) (CoefficientMerge.scale (32993183522304 : Int) atom1130Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36268263201312 : Int) atom1131Coded) (CoefficientMerge.scale (45020666086560 : Int) atom1132Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53773068971808 : Int) atom1133Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11440792772352 : Int) atom1134Coded) (CoefficientMerge.scale (20459364367104 : Int) atom1135Coded))))))))) := by
  rw [block015_data_flat159_step, block015_data_flat158_original]
theorem block015_data : block015 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (40297587372000 : Int) atom1056Coded) (CoefficientMerge.scale (45912704890500 : Int) atom1057Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (39243222144000 : Int) atom1058Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (60042692026800 : Int) atom1059Coded) (CoefficientMerge.scale (42753122622000 : Int) atom1060Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (53503172881200 : Int) atom1061Coded) (CoefficientMerge.scale (16441201816200 : Int) atom1062Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21090286866600 : Int) atom1063Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31933858238100 : Int) atom1064Coded) (CoefficientMerge.scale (8021538207900 : Int) atom1065Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10915331798700 : Int) atom1066Coded) (CoefficientMerge.scale (2384168341248 : Int) atom1067Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5099671524096 : Int) atom1068Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (475114087296 : Int) atom1069Coded) (CoefficientMerge.scale (1116273312000 : Int) atom1070Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (773176320000 : Int) atom1071Coded) (CoefficientMerge.scale (847840896000 : Int) atom1072Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (261913478400 : Int) atom1073Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3749450450688 : Int) atom1074Coded) (CoefficientMerge.scale (7321536603648 : Int) atom1075Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5911986468096 : Int) atom1076Coded) (CoefficientMerge.scale (1501404912000 : Int) atom1077Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (158747500800 : Int) atom1078Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (165266438400 : Int) atom1079Coded) (CoefficientMerge.scale (592446355200 : Int) atom1080Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715209569408 : Int) atom1081Coded) (CoefficientMerge.scale (666940934016 : Int) atom1082Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5982693393600 : Int) atom1083Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11433151537920 : Int) atom1084Coded) (CoefficientMerge.scale (17685804276000 : Int) atom1085Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2176055048448 : Int) atom1086Coded) (CoefficientMerge.scale (977584809600 : Int) atom1087Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (676775635200 : Int) atom1088Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (777042201600 : Int) atom1089Coded) (CoefficientMerge.scale (1201322707200 : Int) atom1090Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (1887516691200 : Int) atom1091Coded) (CoefficientMerge.scale (11268696014208 : Int) atom1092Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7360279591680 : Int) atom1093Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12136953868416 : Int) atom1094Coded) (CoefficientMerge.scale (18104289410880 : Int) atom1095Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25272405692928 : Int) atom1096Coded) (CoefficientMerge.scale (32557609173600 : Int) atom1097Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (2814314861952 : Int) atom1098Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (4832741349504 : Int) atom1099Coded) (CoefficientMerge.scale (4664575499904 : Int) atom1100Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5173185285504 : Int) atom1101Coded) (CoefficientMerge.scale (4937120152704 : Int) atom1102Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5452248875904 : Int) atom1103Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6229291077504 : Int) atom1104Coded) (CoefficientMerge.scale (15678311099904 : Int) atom1105Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (13269277891440 : Int) atom1106Coded) (CoefficientMerge.scale (19501256738304 : Int) atom1107Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25795167116112 : Int) atom1108Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (33886745865360 : Int) atom1109Coded) (CoefficientMerge.scale (41978324614608 : Int) atom1110Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (6031211588352 : Int) atom1111Coded) (CoefficientMerge.scale (10283151170304 : Int) atom1112Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10455429256704 : Int) atom1113Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (10569226408704 : Int) atom1114Coded) (CoefficientMerge.scale (11007037499904 : Int) atom1115Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (11706762069504 : Int) atom1116Coded) (CoefficientMerge.scale (20771126872704 : Int) atom1117Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18331227015840 : Int) atom1118Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25882377554304 : Int) atom1119Coded) (CoefficientMerge.scale (31092814209312 : Int) atom1120Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39549718769760 : Int) atom1121Coded) (CoefficientMerge.scale (48097833974208 : Int) atom1122Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8264724682752 : Int) atom1123Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (15692732354304 : Int) atom1124Coded) (CoefficientMerge.scale (15133866107904 : Int) atom1125Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (15326193717504 : Int) atom1126Coded) (CoefficientMerge.scale (15780434805504 : Int) atom1127Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (25134257493504 : Int) atom1128Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22912538329440 : Int) atom1129Coded) (CoefficientMerge.scale (32993183522304 : Int) atom1130Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (36268263201312 : Int) atom1131Coded) (CoefficientMerge.scale (45020666086560 : Int) atom1132Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53773068971808 : Int) atom1133Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11440792772352 : Int) atom1134Coded) (CoefficientMerge.scale (20459364367104 : Int) atom1135Coded)))))))) := by
  have h : block015 = block015_data_flat159 := by decide +kernel
  exact h.trans block015_data_flat159_original
theorem block015_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block015 := by
  rw [block015_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1056Coded_nonneg g hg hA hB) (atom1057Coded_nonneg g hg hA hB)) (add_nonneg (atom1058Coded_nonneg g hg hA hB) (add_nonneg (atom1059Coded_nonneg g hg hA hB) (atom1060Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1061Coded_nonneg g hg hA hB) (atom1062Coded_nonneg g hg hA hB)) (add_nonneg (atom1063Coded_nonneg g hg hA hB) (add_nonneg (atom1064Coded_nonneg g hg hA hB) (atom1065Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1066Coded_nonneg g hg hA hB) (atom1067Coded_nonneg g hg hA hB)) (add_nonneg (atom1068Coded_nonneg g hg hA hB) (add_nonneg (atom1069Coded_nonneg g hg hA hB) (atom1070Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1071Coded_nonneg g hg hA hB) (atom1072Coded_nonneg g hg hA hB)) (add_nonneg (atom1073Coded_nonneg g hg hA hB) (add_nonneg (atom1074Coded_nonneg g hg hA hB) (atom1075Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1076Coded_nonneg g hg hA hB) (atom1077Coded_nonneg g hg hA hB)) (add_nonneg (atom1078Coded_nonneg g hg hA hB) (add_nonneg (atom1079Coded_nonneg g hg hA hB) (atom1080Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1081Coded_nonneg g hg hA hB) (atom1082Coded_nonneg g hg hA hB)) (add_nonneg (atom1083Coded_nonneg g hg hA hB) (add_nonneg (atom1084Coded_nonneg g hg hA hB) (atom1085Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1086Coded_nonneg g hg hA hB) (atom1087Coded_nonneg g hg hA hB)) (add_nonneg (atom1088Coded_nonneg g hg hA hB) (add_nonneg (atom1089Coded_nonneg g hg hA hB) (atom1090Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1091Coded_nonneg g hg hA hB) (atom1092Coded_nonneg g hg hA hB)) (add_nonneg (atom1093Coded_nonneg g hg hA hB) (add_nonneg (atom1094Coded_nonneg g hg hA hB) (atom1095Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1096Coded_nonneg g hg hA hB) (atom1097Coded_nonneg g hg hA hB)) (add_nonneg (atom1098Coded_nonneg g hg hA hB) (add_nonneg (atom1099Coded_nonneg g hg hA hB) (atom1100Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1101Coded_nonneg g hg hA hB) (atom1102Coded_nonneg g hg hA hB)) (add_nonneg (atom1103Coded_nonneg g hg hA hB) (add_nonneg (atom1104Coded_nonneg g hg hA hB) (atom1105Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1106Coded_nonneg g hg hA hB) (atom1107Coded_nonneg g hg hA hB)) (add_nonneg (atom1108Coded_nonneg g hg hA hB) (add_nonneg (atom1109Coded_nonneg g hg hA hB) (atom1110Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1111Coded_nonneg g hg hA hB) (atom1112Coded_nonneg g hg hA hB)) (add_nonneg (atom1113Coded_nonneg g hg hA hB) (add_nonneg (atom1114Coded_nonneg g hg hA hB) (atom1115Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1116Coded_nonneg g hg hA hB) (atom1117Coded_nonneg g hg hA hB)) (add_nonneg (atom1118Coded_nonneg g hg hA hB) (add_nonneg (atom1119Coded_nonneg g hg hA hB) (atom1120Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1121Coded_nonneg g hg hA hB) (atom1122Coded_nonneg g hg hA hB)) (add_nonneg (atom1123Coded_nonneg g hg hA hB) (add_nonneg (atom1124Coded_nonneg g hg hA hB) (atom1125Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1126Coded_nonneg g hg hA hB) (atom1127Coded_nonneg g hg hA hB)) (add_nonneg (atom1128Coded_nonneg g hg hA hB) (add_nonneg (atom1129Coded_nonneg g hg hA hB) (atom1130Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1131Coded_nonneg g hg hA hB) (atom1132Coded_nonneg g hg hA hB)) (add_nonneg (atom1133Coded_nonneg g hg hA hB) (add_nonneg (atom1134Coded_nonneg g hg hA hB) (atom1135Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
