-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1089 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1089 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1089 = ((g 3) * (g 6) * (g 8)) := by
  norm_num [atom1089, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1089_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101846650752000 : Int) atom1089) := by
  rw [SparsePolynomial.eval_scale, eval_atom1089]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1089Coded : CoefficientMerge.Poly := [(nat_lit 1880, Int.ofNat (nat_lit 1))]
theorem atom1089Coded_decode : atom1089 = SparsePolynomial.decodeCubic 24 atom1089Coded := by decide +kernel
theorem atom1089Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (101846650752000 : Int) atom1089Coded) := by
  have h := atom1089_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1089Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1090 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1090 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1090 = ((g 3) * (g 6) * (g 9)) := by
  norm_num [atom1090, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1090_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (105562098127728 : Int) atom1090) := by
  rw [SparsePolynomial.eval_scale, eval_atom1090]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1090Coded : CoefficientMerge.Poly := [(nat_lit 1881, Int.ofNat (nat_lit 1))]
theorem atom1090Coded_decode : atom1090 = SparsePolynomial.decodeCubic 24 atom1090Coded := by decide +kernel
theorem atom1090Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (105562098127728 : Int) atom1090Coded) := by
  have h := atom1090_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1090Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1091 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1091 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1091 = ((g 3) * (g 6) * (g 10)) := by
  norm_num [atom1091, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1091_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (125826931427472 : Int) atom1091) := by
  rw [SparsePolynomial.eval_scale, eval_atom1091]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1091Coded : CoefficientMerge.Poly := [(nat_lit 1882, Int.ofNat (nat_lit 1))]
theorem atom1091Coded_decode : atom1091 = SparsePolynomial.decodeCubic 24 atom1091Coded := by decide +kernel
theorem atom1091Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (125826931427472 : Int) atom1091Coded) := by
  have h := atom1091_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1091Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1092 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1092 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1092 = ((g 3) * (g 6) * (g 11)) := by
  norm_num [atom1092, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1092_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (136085099683104 : Int) atom1092) := by
  rw [SparsePolynomial.eval_scale, eval_atom1092]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1092Coded : CoefficientMerge.Poly := [(nat_lit 1883, Int.ofNat (nat_lit 1))]
theorem atom1092Coded_decode : atom1092 = SparsePolynomial.decodeCubic 24 atom1092Coded := by decide +kernel
theorem atom1092Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (136085099683104 : Int) atom1092Coded) := by
  have h := atom1092_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1092Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1093 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1093 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1093 = ((g 3) * (g 6) * (g 12)) := by
  norm_num [atom1093, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1093_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (161923371724224 : Int) atom1093) := by
  rw [SparsePolynomial.eval_scale, eval_atom1093]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1093Coded : CoefficientMerge.Poly := [(nat_lit 1884, Int.ofNat (nat_lit 1))]
theorem atom1093Coded_decode : atom1093 = SparsePolynomial.decodeCubic 24 atom1093Coded := by decide +kernel
theorem atom1093Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (161923371724224 : Int) atom1093Coded) := by
  have h := atom1093_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1093Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1094 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1094 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1094 = ((g 3) * (g 6) * (g 13)) := by
  norm_num [atom1094, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1094_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153240978844800 : Int) atom1094) := by
  rw [SparsePolynomial.eval_scale, eval_atom1094]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1094Coded : CoefficientMerge.Poly := [(nat_lit 1885, Int.ofNat (nat_lit 1))]
theorem atom1094Coded_decode : atom1094 = SparsePolynomial.decodeCubic 24 atom1094Coded := by decide +kernel
theorem atom1094Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (153240978844800 : Int) atom1094Coded) := by
  have h := atom1094_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1094Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1095 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1095 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1095 = ((g 3) * (g 6) * (g 14)) := by
  norm_num [atom1095, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1095_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (140884323148800 : Int) atom1095) := by
  rw [SparsePolynomial.eval_scale, eval_atom1095]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1095Coded : CoefficientMerge.Poly := [(nat_lit 1886, Int.ofNat (nat_lit 1))]
theorem atom1095Coded_decode : atom1095 = SparsePolynomial.decodeCubic 24 atom1095Coded := by decide +kernel
theorem atom1095Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (140884323148800 : Int) atom1095Coded) := by
  have h := atom1095_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1095Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1096 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1096 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1096 = ((g 3) * (g 6) * (g 15)) := by
  norm_num [atom1096, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1096_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (143314674048000 : Int) atom1096) := by
  rw [SparsePolynomial.eval_scale, eval_atom1096]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1096Coded : CoefficientMerge.Poly := [(nat_lit 1887, Int.ofNat (nat_lit 1))]
theorem atom1096Coded_decode : atom1096 = SparsePolynomial.decodeCubic 24 atom1096Coded := by decide +kernel
theorem atom1096Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (143314674048000 : Int) atom1096Coded) := by
  have h := atom1096_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1096Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1097 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1097 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1097 = ((g 3) * (g 6) * (g 16)) := by
  norm_num [atom1097, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1097_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (133922514700800 : Int) atom1097) := by
  rw [SparsePolynomial.eval_scale, eval_atom1097]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1097Coded : CoefficientMerge.Poly := [(nat_lit 1888, Int.ofNat (nat_lit 1))]
theorem atom1097Coded_decode : atom1097 = SparsePolynomial.decodeCubic 24 atom1097Coded := by decide +kernel
theorem atom1097Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (133922514700800 : Int) atom1097Coded) := by
  have h := atom1097_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1097Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1098 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1098 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1098 = ((g 3) * (g 6) * (g 17)) := by
  norm_num [atom1098, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1098_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (134463093811200 : Int) atom1098) := by
  rw [SparsePolynomial.eval_scale, eval_atom1098]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1098Coded : CoefficientMerge.Poly := [(nat_lit 1889, Int.ofNat (nat_lit 1))]
theorem atom1098Coded_decode : atom1098 = SparsePolynomial.decodeCubic 24 atom1098Coded := by decide +kernel
theorem atom1098Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (134463093811200 : Int) atom1098Coded) := by
  have h := atom1098_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1098Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1099 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1099 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1099 = ((g 3) * (g 6) * (g 18)) := by
  norm_num [atom1099, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1099_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (172926682790400 : Int) atom1099) := by
  rw [SparsePolynomial.eval_scale, eval_atom1099]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1099Coded : CoefficientMerge.Poly := [(nat_lit 1890, Int.ofNat (nat_lit 1))]
theorem atom1099Coded_decode : atom1099 = SparsePolynomial.decodeCubic 24 atom1099Coded := by decide +kernel
theorem atom1099Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (172926682790400 : Int) atom1099Coded) := by
  have h := atom1099_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1099Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1100 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1100 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1100 = ((g 3) * (g 6) * (g 19)) := by
  norm_num [atom1100, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1100_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (146965354905600 : Int) atom1100) := by
  rw [SparsePolynomial.eval_scale, eval_atom1100]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1100Coded : CoefficientMerge.Poly := [(nat_lit 1891, Int.ofNat (nat_lit 1))]
theorem atom1100Coded_decode : atom1100 = SparsePolynomial.decodeCubic 24 atom1100Coded := by decide +kernel
theorem atom1100Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (146965354905600 : Int) atom1100Coded) := by
  have h := atom1100_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1100Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1101 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1101 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1101 = ((g 3) * (g 6) * (g 20)) := by
  norm_num [atom1101, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1101_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (206053422220800 : Int) atom1101) := by
  rw [SparsePolynomial.eval_scale, eval_atom1101]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1101Coded : CoefficientMerge.Poly := [(nat_lit 1892, Int.ofNat (nat_lit 1))]
theorem atom1101Coded_decode : atom1101 = SparsePolynomial.decodeCubic 24 atom1101Coded := by decide +kernel
theorem atom1101Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (206053422220800 : Int) atom1101Coded) := by
  have h := atom1101_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1101Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1102 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1102 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1102 = ((g 3) * (g 6) * (g 21)) := by
  norm_num [atom1102, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1102_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (209093938099200 : Int) atom1102) := by
  rw [SparsePolynomial.eval_scale, eval_atom1102]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 6) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1102Coded : CoefficientMerge.Poly := [(nat_lit 1893, Int.ofNat (nat_lit 1))]
theorem atom1102Coded_decode : atom1102 = SparsePolynomial.decodeCubic 24 atom1102Coded := by decide +kernel
theorem atom1102Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (209093938099200 : Int) atom1102Coded) := by
  have h := atom1102_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1102Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1103 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1103 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1103 = ((g 3) * (g 6) * (g 22)) := by
  norm_num [atom1103, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1103_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (248450545728000 : Int) atom1103) := by
  rw [SparsePolynomial.eval_scale, eval_atom1103]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 6) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1103Coded : CoefficientMerge.Poly := [(nat_lit 1894, Int.ofNat (nat_lit 1))]
theorem atom1103Coded_decode : atom1103 = SparsePolynomial.decodeCubic 24 atom1103Coded := by decide +kernel
theorem atom1103Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (248450545728000 : Int) atom1103Coded) := by
  have h := atom1103_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1103Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1104 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 6, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1104 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1104 = ((g 3) * (g 6) * (g 23)) := by
  norm_num [atom1104, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1104_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (287807153356800 : Int) atom1104) := by
  rw [SparsePolynomial.eval_scale, eval_atom1104]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 6) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1104Coded : CoefficientMerge.Poly := [(nat_lit 1895, Int.ofNat (nat_lit 1))]
theorem atom1104Coded_decode : atom1104 = SparsePolynomial.decodeCubic 24 atom1104Coded := by decide +kernel
theorem atom1104Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (287807153356800 : Int) atom1104Coded) := by
  have h := atom1104_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1104Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1105 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1105 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1105 = ((g 3) * (g 7) * (g 7)) := by
  norm_num [atom1105, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1105_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (81912017510400 : Int) atom1105) := by
  rw [SparsePolynomial.eval_scale, eval_atom1105]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1105Coded : CoefficientMerge.Poly := [(nat_lit 1903, Int.ofNat (nat_lit 1))]
theorem atom1105Coded_decode : atom1105 = SparsePolynomial.decodeCubic 24 atom1105Coded := by decide +kernel
theorem atom1105Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (81912017510400 : Int) atom1105Coded) := by
  have h := atom1105_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1105Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1106 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1106 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1106 = ((g 3) * (g 7) * (g 8)) := by
  norm_num [atom1106, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1106_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (148101709324800 : Int) atom1106) := by
  rw [SparsePolynomial.eval_scale, eval_atom1106]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1106Coded : CoefficientMerge.Poly := [(nat_lit 1904, Int.ofNat (nat_lit 1))]
theorem atom1106Coded_decode : atom1106 = SparsePolynomial.decodeCubic 24 atom1106Coded := by decide +kernel
theorem atom1106Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (148101709324800 : Int) atom1106Coded) := by
  have h := atom1106_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1106Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1107 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1107 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1107 = ((g 3) * (g 7) * (g 9)) := by
  norm_num [atom1107, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1107_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (135383723561328 : Int) atom1107) := by
  rw [SparsePolynomial.eval_scale, eval_atom1107]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1107Coded : CoefficientMerge.Poly := [(nat_lit 1905, Int.ofNat (nat_lit 1))]
theorem atom1107Coded_decode : atom1107 = SparsePolynomial.decodeCubic 24 atom1107Coded := by decide +kernel
theorem atom1107Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (135383723561328 : Int) atom1107Coded) := by
  have h := atom1107_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1107Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1108 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1108 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1108 = ((g 3) * (g 7) * (g 10)) := by
  norm_num [atom1108, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1108_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (153607371376272 : Int) atom1108) := by
  rw [SparsePolynomial.eval_scale, eval_atom1108]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1108Coded : CoefficientMerge.Poly := [(nat_lit 1906, Int.ofNat (nat_lit 1))]
theorem atom1108Coded_decode : atom1108 = SparsePolynomial.decodeCubic 24 atom1108Coded := by decide +kernel
theorem atom1108Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (153607371376272 : Int) atom1108Coded) := by
  have h := atom1108_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1108Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1109 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1109 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1109 = ((g 3) * (g 7) * (g 11)) := by
  norm_num [atom1109, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1109_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (165949249814304 : Int) atom1109) := by
  rw [SparsePolynomial.eval_scale, eval_atom1109]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1109Coded : CoefficientMerge.Poly := [(nat_lit 1907, Int.ofNat (nat_lit 1))]
theorem atom1109Coded_decode : atom1109 = SparsePolynomial.decodeCubic 24 atom1109Coded := by decide +kernel
theorem atom1109Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (165949249814304 : Int) atom1109Coded) := by
  have h := atom1109_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1109Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1110 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1110 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1110 = ((g 3) * (g 7) * (g 12)) := by
  norm_num [atom1110, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1110_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (193871232037824 : Int) atom1110) := by
  rw [SparsePolynomial.eval_scale, eval_atom1110]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1110Coded : CoefficientMerge.Poly := [(nat_lit 1908, Int.ofNat (nat_lit 1))]
theorem atom1110Coded_decode : atom1110 = SparsePolynomial.decodeCubic 24 atom1110Coded := by decide +kernel
theorem atom1110Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (193871232037824 : Int) atom1110Coded) := by
  have h := atom1110_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1110Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1111 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1111 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1111 = ((g 3) * (g 7) * (g 13)) := by
  norm_num [atom1111, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1111_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (185210101507200 : Int) atom1111) := by
  rw [SparsePolynomial.eval_scale, eval_atom1111]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1111Coded : CoefficientMerge.Poly := [(nat_lit 1909, Int.ofNat (nat_lit 1))]
theorem atom1111Coded_decode : atom1111 = SparsePolynomial.decodeCubic 24 atom1111Coded := by decide +kernel
theorem atom1111Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (185210101507200 : Int) atom1111Coded) := by
  have h := atom1111_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1111Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1112 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1112 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1112 = ((g 3) * (g 7) * (g 14)) := by
  norm_num [atom1112, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1112_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (172874708160000 : Int) atom1112) := by
  rw [SparsePolynomial.eval_scale, eval_atom1112]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1112Coded : CoefficientMerge.Poly := [(nat_lit 1910, Int.ofNat (nat_lit 1))]
theorem atom1112Coded_decode : atom1112 = SparsePolynomial.decodeCubic 24 atom1112Coded := by decide +kernel
theorem atom1112Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (172874708160000 : Int) atom1112Coded) := by
  have h := atom1112_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1112Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1113 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1113 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1113 = ((g 3) * (g 7) * (g 15)) := by
  norm_num [atom1113, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1113_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175326321408000 : Int) atom1113) := by
  rw [SparsePolynomial.eval_scale, eval_atom1113]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1113Coded : CoefficientMerge.Poly := [(nat_lit 1911, Int.ofNat (nat_lit 1))]
theorem atom1113Coded_decode : atom1113 = SparsePolynomial.decodeCubic 24 atom1113Coded := by decide +kernel
theorem atom1113Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (175326321408000 : Int) atom1113Coded) := by
  have h := atom1113_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1113Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1114 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1114 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1114 = ((g 3) * (g 7) * (g 16)) := by
  norm_num [atom1114, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1114_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (165955424409600 : Int) atom1114) := by
  rw [SparsePolynomial.eval_scale, eval_atom1114]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1114Coded : CoefficientMerge.Poly := [(nat_lit 1912, Int.ofNat (nat_lit 1))]
theorem atom1114Coded_decode : atom1114 = SparsePolynomial.decodeCubic 24 atom1114Coded := by decide +kernel
theorem atom1114Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (165955424409600 : Int) atom1114Coded) := by
  have h := atom1114_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1114Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1115 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1115 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1115 = ((g 3) * (g 7) * (g 17)) := by
  norm_num [atom1115, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1115_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (166517265868800 : Int) atom1115) := by
  rw [SparsePolynomial.eval_scale, eval_atom1115]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1115Coded : CoefficientMerge.Poly := [(nat_lit 1913, Int.ofNat (nat_lit 1))]
theorem atom1115Coded_decode : atom1115 = SparsePolynomial.decodeCubic 24 atom1115Coded := by decide +kernel
theorem atom1115Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (166517265868800 : Int) atom1115Coded) := by
  have h := atom1115_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1115Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1116 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1116 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1116 = ((g 3) * (g 7) * (g 18)) := by
  norm_num [atom1116, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1116_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (207331525632000 : Int) atom1116) := by
  rw [SparsePolynomial.eval_scale, eval_atom1116]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1116Coded : CoefficientMerge.Poly := [(nat_lit 1914, Int.ofNat (nat_lit 1))]
theorem atom1116Coded_decode : atom1116 = SparsePolynomial.decodeCubic 24 atom1116Coded := by decide +kernel
theorem atom1116Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (207331525632000 : Int) atom1116Coded) := by
  have h := atom1116_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1116Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1117 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1117 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1117 = ((g 3) * (g 7) * (g 19)) := by
  norm_num [atom1117, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1117_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (186050276966400 : Int) atom1117) := by
  rw [SparsePolynomial.eval_scale, eval_atom1117]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1117Coded : CoefficientMerge.Poly := [(nat_lit 1915, Int.ofNat (nat_lit 1))]
theorem atom1117Coded_decode : atom1117 = SparsePolynomial.decodeCubic 24 atom1117Coded := by decide +kernel
theorem atom1117Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (186050276966400 : Int) atom1117Coded) := by
  have h := atom1117_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1117Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1118 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1118 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1118 = ((g 3) * (g 7) * (g 20)) := by
  norm_num [atom1118, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1118_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (249818423500800 : Int) atom1118) := by
  rw [SparsePolynomial.eval_scale, eval_atom1118]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1118Coded : CoefficientMerge.Poly := [(nat_lit 1916, Int.ofNat (nat_lit 1))]
theorem atom1118Coded_decode : atom1118 = SparsePolynomial.decodeCubic 24 atom1118Coded := by decide +kernel
theorem atom1118Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (249818423500800 : Int) atom1118Coded) := by
  have h := atom1118_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1118Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1119 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1119 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1119 = ((g 3) * (g 7) * (g 21)) := by
  norm_num [atom1119, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1119_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (262197835468800 : Int) atom1119) := by
  rw [SparsePolynomial.eval_scale, eval_atom1119]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 7) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1119Coded : CoefficientMerge.Poly := [(nat_lit 1917, Int.ofNat (nat_lit 1))]
theorem atom1119Coded_decode : atom1119 = SparsePolynomial.decodeCubic 24 atom1119Coded := by decide +kernel
theorem atom1119Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (262197835468800 : Int) atom1119Coded) := by
  have h := atom1119_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1119Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1120 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1120 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1120 = ((g 3) * (g 7) * (g 22)) := by
  norm_num [atom1120, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1120_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (310893339187200 : Int) atom1120) := by
  rw [SparsePolynomial.eval_scale, eval_atom1120]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 7) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1120Coded : CoefficientMerge.Poly := [(nat_lit 1918, Int.ofNat (nat_lit 1))]
theorem atom1120Coded_decode : atom1120 = SparsePolynomial.decodeCubic 24 atom1120Coded := by decide +kernel
theorem atom1120Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (310893339187200 : Int) atom1120Coded) := by
  have h := atom1120_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1120Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1121 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 7, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1121 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1121 = ((g 3) * (g 7) * (g 23)) := by
  norm_num [atom1121, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1121_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (359588842905600 : Int) atom1121) := by
  rw [SparsePolynomial.eval_scale, eval_atom1121]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 7) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1121Coded : CoefficientMerge.Poly := [(nat_lit 1919, Int.ofNat (nat_lit 1))]
theorem atom1121Coded_decode : atom1121 = SparsePolynomial.decodeCubic 24 atom1121Coded := by decide +kernel
theorem atom1121Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (359588842905600 : Int) atom1121Coded) := by
  have h := atom1121_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1121Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1122 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1122 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1122 = ((g 3) * (g 8) * (g 8)) := by
  norm_num [atom1122, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1122_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (101123730892800 : Int) atom1122) := by
  rw [SparsePolynomial.eval_scale, eval_atom1122]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1122Coded : CoefficientMerge.Poly := [(nat_lit 1928, Int.ofNat (nat_lit 1))]
theorem atom1122Coded_decode : atom1122 = SparsePolynomial.decodeCubic 24 atom1122Coded := by decide +kernel
theorem atom1122Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (101123730892800 : Int) atom1122Coded) := by
  have h := atom1122_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1122Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1123 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1123 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1123 = ((g 3) * (g 8) * (g 9)) := by
  norm_num [atom1123, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1123_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (189544167714528 : Int) atom1123) := by
  rw [SparsePolynomial.eval_scale, eval_atom1123]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1123Coded : CoefficientMerge.Poly := [(nat_lit 1929, Int.ofNat (nat_lit 1))]
theorem atom1123Coded_decode : atom1123 = SparsePolynomial.decodeCubic 24 atom1123Coded := by decide +kernel
theorem atom1123Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (189544167714528 : Int) atom1123Coded) := by
  have h := atom1123_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1123Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1124 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1124 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1124 = ((g 3) * (g 8) * (g 10)) := by
  norm_num [atom1124, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1124_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (178502897027664 : Int) atom1124) := by
  rw [SparsePolynomial.eval_scale, eval_atom1124]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1124Coded : CoefficientMerge.Poly := [(nat_lit 1930, Int.ofNat (nat_lit 1))]
theorem atom1124Coded_decode : atom1124 = SparsePolynomial.decodeCubic 24 atom1124Coded := by decide +kernel
theorem atom1124Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (178502897027664 : Int) atom1124Coded) := by
  have h := atom1124_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1124Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1125 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1125 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1125 = ((g 3) * (g 8) * (g 11)) := by
  norm_num [atom1125, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1125_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (194088787209504 : Int) atom1125) := by
  rw [SparsePolynomial.eval_scale, eval_atom1125]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1125Coded : CoefficientMerge.Poly := [(nat_lit 1931, Int.ofNat (nat_lit 1))]
theorem atom1125Coded_decode : atom1125 = SparsePolynomial.decodeCubic 24 atom1125Coded := by decide +kernel
theorem atom1125Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (194088787209504 : Int) atom1125Coded) := by
  have h := atom1125_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1125Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1126 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1126 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1126 = ((g 3) * (g 8) * (g 12)) := by
  norm_num [atom1126, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1126_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (217928398463424 : Int) atom1126) := by
  rw [SparsePolynomial.eval_scale, eval_atom1126]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1126Coded : CoefficientMerge.Poly := [(nat_lit 1932, Int.ofNat (nat_lit 1))]
theorem atom1126Coded_decode : atom1126 = SparsePolynomial.decodeCubic 24 atom1126Coded := by decide +kernel
theorem atom1126Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (217928398463424 : Int) atom1126Coded) := by
  have h := atom1126_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1126Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1127 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1127 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1127 = ((g 3) * (g 8) * (g 13)) := by
  norm_num [atom1127, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1127_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (208267937539200 : Int) atom1127) := by
  rw [SparsePolynomial.eval_scale, eval_atom1127]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1127Coded : CoefficientMerge.Poly := [(nat_lit 1933, Int.ofNat (nat_lit 1))]
theorem atom1127Coded_decode : atom1127 = SparsePolynomial.decodeCubic 24 atom1127Coded := by decide +kernel
theorem atom1127Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (208267937539200 : Int) atom1127Coded) := by
  have h := atom1127_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1127Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1128 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1128 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1128 = ((g 3) * (g 8) * (g 14)) := by
  norm_num [atom1128, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1128_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (194933213798400 : Int) atom1128) := by
  rw [SparsePolynomial.eval_scale, eval_atom1128]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1128Coded : CoefficientMerge.Poly := [(nat_lit 1934, Int.ofNat (nat_lit 1))]
theorem atom1128Coded_decode : atom1128 = SparsePolynomial.decodeCubic 24 atom1128Coded := by decide +kernel
theorem atom1128Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (194933213798400 : Int) atom1128Coded) := by
  have h := atom1128_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1128Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1129 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1129 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1129 = ((g 3) * (g 8) * (g 15)) := by
  norm_num [atom1129, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1129_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (196385496652800 : Int) atom1129) := by
  rw [SparsePolynomial.eval_scale, eval_atom1129]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1129Coded : CoefficientMerge.Poly := [(nat_lit 1935, Int.ofNat (nat_lit 1))]
theorem atom1129Coded_decode : atom1129 = SparsePolynomial.decodeCubic 24 atom1129Coded := by decide +kernel
theorem atom1129Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (196385496652800 : Int) atom1129Coded) := by
  have h := atom1129_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1129Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1130 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1130 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1130 = ((g 3) * (g 8) * (g 16)) := by
  norm_num [atom1130, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1130_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (186015269260800 : Int) atom1130) := by
  rw [SparsePolynomial.eval_scale, eval_atom1130]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1130Coded : CoefficientMerge.Poly := [(nat_lit 1936, Int.ofNat (nat_lit 1))]
theorem atom1130Coded_decode : atom1130 = SparsePolynomial.decodeCubic 24 atom1130Coded := by decide +kernel
theorem atom1130Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (186015269260800 : Int) atom1130Coded) := by
  have h := atom1130_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1130Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1131 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1131 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1131 = ((g 3) * (g 8) * (g 17)) := by
  norm_num [atom1131, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1131_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (185577780326400 : Int) atom1131) := by
  rw [SparsePolynomial.eval_scale, eval_atom1131]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1131Coded : CoefficientMerge.Poly := [(nat_lit 1937, Int.ofNat (nat_lit 1))]
theorem atom1131Coded_decode : atom1131 = SparsePolynomial.decodeCubic 24 atom1131Coded := by decide +kernel
theorem atom1131Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (185577780326400 : Int) atom1131Coded) := by
  have h := atom1131_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1131Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1132 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1132 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1132 = ((g 3) * (g 8) * (g 18)) := by
  norm_num [atom1132, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1132_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (228846660134400 : Int) atom1132) := by
  rw [SparsePolynomial.eval_scale, eval_atom1132]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1132Coded : CoefficientMerge.Poly := [(nat_lit 1938, Int.ofNat (nat_lit 1))]
theorem atom1132Coded_decode : atom1132 = SparsePolynomial.decodeCubic 24 atom1132Coded := by decide +kernel
theorem atom1132Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (228846660134400 : Int) atom1132Coded) := by
  have h := atom1132_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1132Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1133 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1133 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1133 = ((g 3) * (g 8) * (g 19)) := by
  norm_num [atom1133, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1133_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (213473981952000 : Int) atom1133) := by
  rw [SparsePolynomial.eval_scale, eval_atom1133]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1133Coded : CoefficientMerge.Poly := [(nat_lit 1939, Int.ofNat (nat_lit 1))]
theorem atom1133Coded_decode : atom1133 = SparsePolynomial.decodeCubic 24 atom1133Coded := by decide +kernel
theorem atom1133Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (213473981952000 : Int) atom1133Coded) := by
  have h := atom1133_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1133Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1134 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1134 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1134 = ((g 3) * (g 8) * (g 20)) := by
  norm_num [atom1134, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1134_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (283150698969600 : Int) atom1134) := by
  rw [SparsePolynomial.eval_scale, eval_atom1134]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1134Coded : CoefficientMerge.Poly := [(nat_lit 1940, Int.ofNat (nat_lit 1))]
theorem atom1134Coded_decode : atom1134 = SparsePolynomial.decodeCubic 24 atom1134Coded := by decide +kernel
theorem atom1134Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (283150698969600 : Int) atom1134Coded) := by
  have h := atom1134_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1134Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1135 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1135 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1135 = ((g 3) * (g 8) * (g 21)) := by
  norm_num [atom1135, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1135_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (308346582297600 : Int) atom1135) := by
  rw [SparsePolynomial.eval_scale, eval_atom1135]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 8) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1135Coded : CoefficientMerge.Poly := [(nat_lit 1941, Int.ofNat (nat_lit 1))]
theorem atom1135Coded_decode : atom1135 = SparsePolynomial.decodeCubic 24 atom1135Coded := by decide +kernel
theorem atom1135Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (308346582297600 : Int) atom1135Coded) := by
  have h := atom1135_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1135Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1136 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1136 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1136 = ((g 3) * (g 8) * (g 22)) := by
  norm_num [atom1136, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1136_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (369858557376000 : Int) atom1136) := by
  rw [SparsePolynomial.eval_scale, eval_atom1136]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 8) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1136Coded : CoefficientMerge.Poly := [(nat_lit 1942, Int.ofNat (nat_lit 1))]
theorem atom1136Coded_decode : atom1136 = SparsePolynomial.decodeCubic 24 atom1136Coded := by decide +kernel
theorem atom1136Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (369858557376000 : Int) atom1136Coded) := by
  have h := atom1136_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1136Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1137 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 8, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1137 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1137 = ((g 3) * (g 8) * (g 23)) := by
  norm_num [atom1137, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1137_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (431370532454400 : Int) atom1137) := by
  rw [SparsePolynomial.eval_scale, eval_atom1137]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 8) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1137Coded : CoefficientMerge.Poly := [(nat_lit 1943, Int.ofNat (nat_lit 1))]
theorem atom1137Coded_decode : atom1137 = SparsePolynomial.decodeCubic 24 atom1137Coded := by decide +kernel
theorem atom1137Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (431370532454400 : Int) atom1137Coded) := by
  have h := atom1137_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1137Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1138 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1138 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1138 = ((g 3) * (g 9) * (g 9)) := by
  norm_num [atom1138, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1138_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (126437516476128 : Int) atom1138) := by
  rw [SparsePolynomial.eval_scale, eval_atom1138]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1138Coded : CoefficientMerge.Poly := [(nat_lit 1953, Int.ofNat (nat_lit 1))]
theorem atom1138Coded_decode : atom1138 = SparsePolynomial.decodeCubic 24 atom1138Coded := by decide +kernel
theorem atom1138Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (126437516476128 : Int) atom1138Coded) := by
  have h := atom1138_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1138Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1139 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1139 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1139 = ((g 3) * (g 9) * (g 10)) := by
  norm_num [atom1139, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1139_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (239751911272896 : Int) atom1139) := by
  rw [SparsePolynomial.eval_scale, eval_atom1139]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1139Coded : CoefficientMerge.Poly := [(nat_lit 1954, Int.ofNat (nat_lit 1))]
theorem atom1139Coded_decode : atom1139 = SparsePolynomial.decodeCubic 24 atom1139Coded := by decide +kernel
theorem atom1139Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (239751911272896 : Int) atom1139Coded) := by
  have h := atom1139_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1139Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1140 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1140 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1140 = ((g 3) * (g 9) * (g 11)) := by
  norm_num [atom1140, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1140_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (231275379769632 : Int) atom1140) := by
  rw [SparsePolynomial.eval_scale, eval_atom1140]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1140Coded : CoefficientMerge.Poly := [(nat_lit 1955, Int.ofNat (nat_lit 1))]
theorem atom1140Coded_decode : atom1140 = SparsePolynomial.decodeCubic 24 atom1140Coded := by decide +kernel
theorem atom1140Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (231275379769632 : Int) atom1140Coded) := by
  have h := atom1140_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1140Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1141 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1141 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1141 = ((g 3) * (g 9) * (g 12)) := by
  norm_num [atom1141, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1141_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (256178108463552 : Int) atom1141) := by
  rw [SparsePolynomial.eval_scale, eval_atom1141]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1141Coded : CoefficientMerge.Poly := [(nat_lit 1956, Int.ofNat (nat_lit 1))]
theorem atom1141Coded_decode : atom1141 = SparsePolynomial.decodeCubic 24 atom1141Coded := by decide +kernel
theorem atom1141Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (256178108463552 : Int) atom1141Coded) := by
  have h := atom1141_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1141Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1142 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1142 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1142 = ((g 3) * (g 9) * (g 13)) := by
  norm_num [atom1142, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1142_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (241414683827328 : Int) atom1142) := by
  rw [SparsePolynomial.eval_scale, eval_atom1142]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1142Coded : CoefficientMerge.Poly := [(nat_lit 1957, Int.ofNat (nat_lit 1))]
theorem atom1142Coded_decode : atom1142 = SparsePolynomial.decodeCubic 24 atom1142Coded := by decide +kernel
theorem atom1142Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (241414683827328 : Int) atom1142Coded) := by
  have h := atom1142_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1142Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1143 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1143 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1143 = ((g 3) * (g 9) * (g 14)) := by
  norm_num [atom1143, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1143_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (226060036950528 : Int) atom1143) := by
  rw [SparsePolynomial.eval_scale, eval_atom1143]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1143Coded : CoefficientMerge.Poly := [(nat_lit 1958, Int.ofNat (nat_lit 1))]
theorem atom1143Coded_decode : atom1143 = SparsePolynomial.decodeCubic 24 atom1143Coded := by decide +kernel
theorem atom1143Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (226060036950528 : Int) atom1143Coded) := by
  have h := atom1143_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1143Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1144 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1144 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1144 = ((g 3) * (g 9) * (g 15)) := by
  norm_num [atom1144, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1144_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (225492396668928 : Int) atom1144) := by
  rw [SparsePolynomial.eval_scale, eval_atom1144]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1144Coded : CoefficientMerge.Poly := [(nat_lit 1959, Int.ofNat (nat_lit 1))]
theorem atom1144Coded_decode : atom1144 = SparsePolynomial.decodeCubic 24 atom1144Coded := by decide +kernel
theorem atom1144Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (225492396668928 : Int) atom1144Coded) := by
  have h := atom1144_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1144Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1145 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1145 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1145 = ((g 3) * (g 9) * (g 16)) := by
  norm_num [atom1145, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1145_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (213102246140928 : Int) atom1145) := by
  rw [SparsePolynomial.eval_scale, eval_atom1145]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1145Coded : CoefficientMerge.Poly := [(nat_lit 1960, Int.ofNat (nat_lit 1))]
theorem atom1145Coded_decode : atom1145 = SparsePolynomial.decodeCubic 24 atom1145Coded := by decide +kernel
theorem atom1145Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (213102246140928 : Int) atom1145Coded) := by
  have h := atom1145_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1145Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1146 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1146 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1146 = ((g 3) * (g 9) * (g 17)) := by
  norm_num [atom1146, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1146_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (210644834070528 : Int) atom1146) := by
  rw [SparsePolynomial.eval_scale, eval_atom1146]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1146Coded : CoefficientMerge.Poly := [(nat_lit 1961, Int.ofNat (nat_lit 1))]
theorem atom1146Coded_decode : atom1146 = SparsePolynomial.decodeCubic 24 atom1146Coded := by decide +kernel
theorem atom1146Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (210644834070528 : Int) atom1146Coded) := by
  have h := atom1146_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1146Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1147 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1147 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1147 = ((g 3) * (g 9) * (g 18)) := by
  norm_num [atom1147, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1147_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (254097258573312 : Int) atom1147) := by
  rw [SparsePolynomial.eval_scale, eval_atom1147]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1147Coded : CoefficientMerge.Poly := [(nat_lit 1962, Int.ofNat (nat_lit 1))]
theorem atom1147Coded_decode : atom1147 = SparsePolynomial.decodeCubic 24 atom1147Coded := by decide +kernel
theorem atom1147Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (254097258573312 : Int) atom1147Coded) := by
  have h := atom1147_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1147Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1148 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1148 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1148 = ((g 3) * (g 9) * (g 19)) := by
  norm_num [atom1148, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1148_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (241111592916480 : Int) atom1148) := by
  rw [SparsePolynomial.eval_scale, eval_atom1148]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1148Coded : CoefficientMerge.Poly := [(nat_lit 1963, Int.ofNat (nat_lit 1))]
theorem atom1148Coded_decode : atom1148 = SparsePolynomial.decodeCubic 24 atom1148Coded := by decide +kernel
theorem atom1148Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (241111592916480 : Int) atom1148Coded) := by
  have h := atom1148_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1148Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1149 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1149 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1149 = ((g 3) * (g 9) * (g 20)) := by
  norm_num [atom1149, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1149_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (313175322459648 : Int) atom1149) := by
  rw [SparsePolynomial.eval_scale, eval_atom1149]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1149Coded : CoefficientMerge.Poly := [(nat_lit 1964, Int.ofNat (nat_lit 1))]
theorem atom1149Coded_decode : atom1149 = SparsePolynomial.decodeCubic 24 atom1149Coded := by decide +kernel
theorem atom1149Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (313175322459648 : Int) atom1149Coded) := by
  have h := atom1149_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1149Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1150 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1150 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1150 = ((g 3) * (g 9) * (g 21)) := by
  norm_num [atom1150, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1150_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (345165153974784 : Int) atom1150) := by
  rw [SparsePolynomial.eval_scale, eval_atom1150]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1150Coded : CoefficientMerge.Poly := [(nat_lit 1965, Int.ofNat (nat_lit 1))]
theorem atom1150Coded_decode : atom1150 = SparsePolynomial.decodeCubic 24 atom1150Coded := by decide +kernel
theorem atom1150Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (345165153974784 : Int) atom1150Coded) := by
  have h := atom1150_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1150Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1151 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1151 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1151 = ((g 3) * (g 9) * (g 22)) := by
  norm_num [atom1151, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1151_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (413471077240320 : Int) atom1151) := by
  rw [SparsePolynomial.eval_scale, eval_atom1151]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1151Coded : CoefficientMerge.Poly := [(nat_lit 1966, Int.ofNat (nat_lit 1))]
theorem atom1151Coded_decode : atom1151 = SparsePolynomial.decodeCubic 24 atom1151Coded := by decide +kernel
theorem atom1151Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (413471077240320 : Int) atom1151Coded) := by
  have h := atom1151_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1151Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1152 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 9, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1152 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1152 = ((g 3) * (g 9) * (g 23)) := by
  norm_num [atom1152, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1152_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (481777000505856 : Int) atom1152) := by
  rw [SparsePolynomial.eval_scale, eval_atom1152]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1152Coded : CoefficientMerge.Poly := [(nat_lit 1967, Int.ofNat (nat_lit 1))]
theorem atom1152Coded_decode : atom1152 = SparsePolynomial.decodeCubic 24 atom1152Coded := by decide +kernel
theorem atom1152Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (481777000505856 : Int) atom1152Coded) := by
  have h := atom1152_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1152Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1153 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1153 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1153 = ((g 3) * (g 10) * (g 10)) := by
  norm_num [atom1153, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1153_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (151331474451168 : Int) atom1153) := by
  rw [SparsePolynomial.eval_scale, eval_atom1153]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1153Coded : CoefficientMerge.Poly := [(nat_lit 1978, Int.ofNat (nat_lit 1))]
theorem atom1153Coded_decode : atom1153 = SparsePolynomial.decodeCubic 24 atom1153Coded := by decide +kernel
theorem atom1153Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (151331474451168 : Int) atom1153Coded) := by
  have h := atom1153_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1153Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1154 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1154 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1154 = ((g 3) * (g 10) * (g 11)) := by
  norm_num [atom1154, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1154_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (298353837763872 : Int) atom1154) := by
  rw [SparsePolynomial.eval_scale, eval_atom1154]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1154Coded : CoefficientMerge.Poly := [(nat_lit 1979, Int.ofNat (nat_lit 1))]
theorem atom1154Coded_decode : atom1154 = SparsePolynomial.decodeCubic 24 atom1154Coded := by decide +kernel
theorem atom1154Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (298353837763872 : Int) atom1154Coded) := by
  have h := atom1154_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1154Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1155 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1155 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1155 = ((g 3) * (g 10) * (g 12)) := by
  norm_num [atom1155, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1155_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (317133010003392 : Int) atom1155) := by
  rw [SparsePolynomial.eval_scale, eval_atom1155]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1155Coded : CoefficientMerge.Poly := [(nat_lit 1980, Int.ofNat (nat_lit 1))]
theorem atom1155Coded_decode : atom1155 = SparsePolynomial.decodeCubic 24 atom1155Coded := by decide +kernel
theorem atom1155Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (317133010003392 : Int) atom1155Coded) := by
  have h := atom1155_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1155Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1156 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1156 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1156 = ((g 3) * (g 10) * (g 13)) := by
  norm_num [atom1156, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1156_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (302412110064768 : Int) atom1156) := by
  rw [SparsePolynomial.eval_scale, eval_atom1156]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1156Coded : CoefficientMerge.Poly := [(nat_lit 1981, Int.ofNat (nat_lit 1))]
theorem atom1156Coded_decode : atom1156 = SparsePolynomial.decodeCubic 24 atom1156Coded := by decide +kernel
theorem atom1156Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (302412110064768 : Int) atom1156Coded) := by
  have h := atom1156_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1156Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1157 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1157 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1157 = ((g 3) * (g 10) * (g 14)) := by
  norm_num [atom1157, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1157_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (284016947309568 : Int) atom1157) := by
  rw [SparsePolynomial.eval_scale, eval_atom1157]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1157Coded : CoefficientMerge.Poly := [(nat_lit 1982, Int.ofNat (nat_lit 1))]
theorem atom1157Coded_decode : atom1157 = SparsePolynomial.decodeCubic 24 atom1157Coded := by decide +kernel
theorem atom1157Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (284016947309568 : Int) atom1157Coded) := by
  have h := atom1157_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1157Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1158 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1158 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1158 = ((g 3) * (g 10) * (g 15)) := by
  norm_num [atom1158, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1158_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (280408791149568 : Int) atom1158) := by
  rw [SparsePolynomial.eval_scale, eval_atom1158]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1158Coded : CoefficientMerge.Poly := [(nat_lit 1983, Int.ofNat (nat_lit 1))]
theorem atom1158Coded_decode : atom1158 = SparsePolynomial.decodeCubic 24 atom1158Coded := by decide +kernel
theorem atom1158Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (280408791149568 : Int) atom1158Coded) := by
  have h := atom1158_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1158Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1159 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1159 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1159 = ((g 3) * (g 10) * (g 16)) := by
  norm_num [atom1159, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1159_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (264978124743168 : Int) atom1159) := by
  rw [SparsePolynomial.eval_scale, eval_atom1159]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1159Coded : CoefficientMerge.Poly := [(nat_lit 1984, Int.ofNat (nat_lit 1))]
theorem atom1159Coded_decode : atom1159 = SparsePolynomial.decodeCubic 24 atom1159Coded := by decide +kernel
theorem atom1159Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (264978124743168 : Int) atom1159Coded) := by
  have h := atom1159_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1159Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1160 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1160 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1160 = ((g 3) * (g 10) * (g 17)) := by
  norm_num [atom1160, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1160_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (259480196794368 : Int) atom1160) := by
  rw [SparsePolynomial.eval_scale, eval_atom1160]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1160Coded : CoefficientMerge.Poly := [(nat_lit 1985, Int.ofNat (nat_lit 1))]
theorem atom1160Coded_decode : atom1160 = SparsePolynomial.decodeCubic 24 atom1160Coded := by decide +kernel
theorem atom1160Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (259480196794368 : Int) atom1160Coded) := by
  have h := atom1160_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1160Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1161 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1161 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1161 = ((g 3) * (g 10) * (g 18)) := by
  norm_num [atom1161, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1161_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (298624869430272 : Int) atom1161) := by
  rw [SparsePolynomial.eval_scale, eval_atom1161]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1161Coded : CoefficientMerge.Poly := [(nat_lit 1986, Int.ofNat (nat_lit 1))]
theorem atom1161Coded_decode : atom1161 = SparsePolynomial.decodeCubic 24 atom1161Coded := by decide +kernel
theorem atom1161Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (298624869430272 : Int) atom1161Coded) := by
  have h := atom1161_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1161Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1162 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1162 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1162 = ((g 3) * (g 10) * (g 19)) := by
  norm_num [atom1162, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1162_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (280064215918080 : Int) atom1162) := by
  rw [SparsePolynomial.eval_scale, eval_atom1162]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1162Coded : CoefficientMerge.Poly := [(nat_lit 1987, Int.ofNat (nat_lit 1))]
theorem atom1162Coded_decode : atom1162 = SparsePolynomial.decodeCubic 24 atom1162Coded := by decide +kernel
theorem atom1162Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (280064215918080 : Int) atom1162Coded) := by
  have h := atom1162_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1162Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1163 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1163 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1163 = ((g 3) * (g 10) * (g 20)) := by
  norm_num [atom1163, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1163_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (346552957605888 : Int) atom1163) := by
  rw [SparsePolynomial.eval_scale, eval_atom1163]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1163Coded : CoefficientMerge.Poly := [(nat_lit 1988, Int.ofNat (nat_lit 1))]
theorem atom1163Coded_decode : atom1163 = SparsePolynomial.decodeCubic 24 atom1163Coded := by decide +kernel
theorem atom1163Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (346552957605888 : Int) atom1163Coded) := by
  have h := atom1163_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1163Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1164 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1164 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1164 = ((g 3) * (g 10) * (g 21)) := by
  norm_num [atom1164, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1164_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (370433329288704 : Int) atom1164) := by
  rw [SparsePolynomial.eval_scale, eval_atom1164]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1164Coded : CoefficientMerge.Poly := [(nat_lit 1989, Int.ofNat (nat_lit 1))]
theorem atom1164Coded_decode : atom1164 = SparsePolynomial.decodeCubic 24 atom1164Coded := by decide +kernel
theorem atom1164Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (370433329288704 : Int) atom1164Coded) := by
  have h := atom1164_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1164Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1165 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1165 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1165 = ((g 3) * (g 10) * (g 22)) := by
  norm_num [atom1165, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1165_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (430629792721920 : Int) atom1165) := by
  rw [SparsePolynomial.eval_scale, eval_atom1165]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1165Coded : CoefficientMerge.Poly := [(nat_lit 1990, Int.ofNat (nat_lit 1))]
theorem atom1165Coded_decode : atom1165 = SparsePolynomial.decodeCubic 24 atom1165Coded := by decide +kernel
theorem atom1165Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (430629792721920 : Int) atom1165Coded) := by
  have h := atom1165_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1165Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1166 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 10, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1166 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1166 = ((g 3) * (g 10) * (g 23)) := by
  norm_num [atom1166, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1166_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (490826256155136 : Int) atom1166) := by
  rw [SparsePolynomial.eval_scale, eval_atom1166]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1166Coded : CoefficientMerge.Poly := [(nat_lit 1991, Int.ofNat (nat_lit 1))]
theorem atom1166Coded_decode : atom1166 = SparsePolynomial.decodeCubic 24 atom1166Coded := by decide +kernel
theorem atom1166Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (490826256155136 : Int) atom1166Coded) := by
  have h := atom1166_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1166Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1167 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1167 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1167 = ((g 3) * (g 11) * (g 11)) := by
  norm_num [atom1167, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1167_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (191205524119104 : Int) atom1167) := by
  rw [SparsePolynomial.eval_scale, eval_atom1167]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1167Coded : CoefficientMerge.Poly := [(nat_lit 2003, Int.ofNat (nat_lit 1))]
theorem atom1167Coded_decode : atom1167 = SparsePolynomial.decodeCubic 24 atom1167Coded := by decide +kernel
theorem atom1167Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (191205524119104 : Int) atom1167Coded) := by
  have h := atom1167_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1167Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1168 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1168 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1168 = ((g 3) * (g 11) * (g 12)) := by
  norm_num [atom1168, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1168_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (377351140782528 : Int) atom1168) := by
  rw [SparsePolynomial.eval_scale, eval_atom1168]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1168Coded : CoefficientMerge.Poly := [(nat_lit 2004, Int.ofNat (nat_lit 1))]
theorem atom1168Coded_decode : atom1168 = SparsePolynomial.decodeCubic 24 atom1168Coded := by decide +kernel
theorem atom1168Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (377351140782528 : Int) atom1168Coded) := by
  have h := atom1168_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1168Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block016 : CoefficientMerge.Poly := [(nat_lit 1880, Int.ofNat (nat_lit 101846650752000)), (nat_lit 1881, Int.ofNat (nat_lit 105562098127728)), (nat_lit 1882, Int.ofNat (nat_lit 125826931427472)), (nat_lit 1883, Int.ofNat (nat_lit 136085099683104)), (nat_lit 1884, Int.ofNat (nat_lit 161923371724224)), (nat_lit 1885, Int.ofNat (nat_lit 153240978844800)), (nat_lit 1886, Int.ofNat (nat_lit 140884323148800)), (nat_lit 1887, Int.ofNat (nat_lit 143314674048000)), (nat_lit 1888, Int.ofNat (nat_lit 133922514700800)), (nat_lit 1889, Int.ofNat (nat_lit 134463093811200)), (nat_lit 1890, Int.ofNat (nat_lit 172926682790400)), (nat_lit 1891, Int.ofNat (nat_lit 146965354905600)), (nat_lit 1892, Int.ofNat (nat_lit 206053422220800)), (nat_lit 1893, Int.ofNat (nat_lit 209093938099200)), (nat_lit 1894, Int.ofNat (nat_lit 248450545728000)), (nat_lit 1895, Int.ofNat (nat_lit 287807153356800)), (nat_lit 1903, Int.ofNat (nat_lit 81912017510400)), (nat_lit 1904, Int.ofNat (nat_lit 148101709324800)), (nat_lit 1905, Int.ofNat (nat_lit 135383723561328)), (nat_lit 1906, Int.ofNat (nat_lit 153607371376272)), (nat_lit 1907, Int.ofNat (nat_lit 165949249814304)), (nat_lit 1908, Int.ofNat (nat_lit 193871232037824)), (nat_lit 1909, Int.ofNat (nat_lit 185210101507200)), (nat_lit 1910, Int.ofNat (nat_lit 172874708160000)), (nat_lit 1911, Int.ofNat (nat_lit 175326321408000)), (nat_lit 1912, Int.ofNat (nat_lit 165955424409600)), (nat_lit 1913, Int.ofNat (nat_lit 166517265868800)), (nat_lit 1914, Int.ofNat (nat_lit 207331525632000)), (nat_lit 1915, Int.ofNat (nat_lit 186050276966400)), (nat_lit 1916, Int.ofNat (nat_lit 249818423500800)), (nat_lit 1917, Int.ofNat (nat_lit 262197835468800)), (nat_lit 1918, Int.ofNat (nat_lit 310893339187200)), (nat_lit 1919, Int.ofNat (nat_lit 359588842905600)), (nat_lit 1928, Int.ofNat (nat_lit 101123730892800)), (nat_lit 1929, Int.ofNat (nat_lit 189544167714528)), (nat_lit 1930, Int.ofNat (nat_lit 178502897027664)), (nat_lit 1931, Int.ofNat (nat_lit 194088787209504)), (nat_lit 1932, Int.ofNat (nat_lit 217928398463424)), (nat_lit 1933, Int.ofNat (nat_lit 208267937539200)), (nat_lit 1934, Int.ofNat (nat_lit 194933213798400)), (nat_lit 1935, Int.ofNat (nat_lit 196385496652800)), (nat_lit 1936, Int.ofNat (nat_lit 186015269260800)), (nat_lit 1937, Int.ofNat (nat_lit 185577780326400)), (nat_lit 1938, Int.ofNat (nat_lit 228846660134400)), (nat_lit 1939, Int.ofNat (nat_lit 213473981952000)), (nat_lit 1940, Int.ofNat (nat_lit 283150698969600)), (nat_lit 1941, Int.ofNat (nat_lit 308346582297600)), (nat_lit 1942, Int.ofNat (nat_lit 369858557376000)), (nat_lit 1943, Int.ofNat (nat_lit 431370532454400)), (nat_lit 1953, Int.ofNat (nat_lit 126437516476128)), (nat_lit 1954, Int.ofNat (nat_lit 239751911272896)), (nat_lit 1955, Int.ofNat (nat_lit 231275379769632)), (nat_lit 1956, Int.ofNat (nat_lit 256178108463552)), (nat_lit 1957, Int.ofNat (nat_lit 241414683827328)), (nat_lit 1958, Int.ofNat (nat_lit 226060036950528)), (nat_lit 1959, Int.ofNat (nat_lit 225492396668928)), (nat_lit 1960, Int.ofNat (nat_lit 213102246140928)), (nat_lit 1961, Int.ofNat (nat_lit 210644834070528)), (nat_lit 1962, Int.ofNat (nat_lit 254097258573312)), (nat_lit 1963, Int.ofNat (nat_lit 241111592916480)), (nat_lit 1964, Int.ofNat (nat_lit 313175322459648)), (nat_lit 1965, Int.ofNat (nat_lit 345165153974784)), (nat_lit 1966, Int.ofNat (nat_lit 413471077240320)), (nat_lit 1967, Int.ofNat (nat_lit 481777000505856)), (nat_lit 1978, Int.ofNat (nat_lit 151331474451168)), (nat_lit 1979, Int.ofNat (nat_lit 298353837763872)), (nat_lit 1980, Int.ofNat (nat_lit 317133010003392)), (nat_lit 1981, Int.ofNat (nat_lit 302412110064768)), (nat_lit 1982, Int.ofNat (nat_lit 284016947309568)), (nat_lit 1983, Int.ofNat (nat_lit 280408791149568)), (nat_lit 1984, Int.ofNat (nat_lit 264978124743168)), (nat_lit 1985, Int.ofNat (nat_lit 259480196794368)), (nat_lit 1986, Int.ofNat (nat_lit 298624869430272)), (nat_lit 1987, Int.ofNat (nat_lit 280064215918080)), (nat_lit 1988, Int.ofNat (nat_lit 346552957605888)), (nat_lit 1989, Int.ofNat (nat_lit 370433329288704)), (nat_lit 1990, Int.ofNat (nat_lit 430629792721920)), (nat_lit 1991, Int.ofNat (nat_lit 490826256155136)), (nat_lit 2003, Int.ofNat (nat_lit 191205524119104)), (nat_lit 2004, Int.ofNat (nat_lit 377351140782528))]
def block016_data_flat000 : CoefficientMerge.Poly := [(nat_lit 1880, Int.ofNat (nat_lit 101846650752000))]
theorem block016_data_flat000_step : block016_data_flat000 = (CoefficientMerge.scale (101846650752000 : Int) atom1089Coded) := by decide +kernel
theorem block016_data_flat000_original : block016_data_flat000 = (CoefficientMerge.scale (101846650752000 : Int) atom1089Coded) := by
  rw [block016_data_flat000_step]
def block016_data_flat001 : CoefficientMerge.Poly := [(nat_lit 1881, Int.ofNat (nat_lit 105562098127728))]
theorem block016_data_flat001_step : block016_data_flat001 = (CoefficientMerge.scale (105562098127728 : Int) atom1090Coded) := by decide +kernel
theorem block016_data_flat001_original : block016_data_flat001 = (CoefficientMerge.scale (105562098127728 : Int) atom1090Coded) := by
  rw [block016_data_flat001_step]
def block016_data_flat002 : CoefficientMerge.Poly := [(nat_lit 1880, Int.ofNat (nat_lit 101846650752000)), (nat_lit 1881, Int.ofNat (nat_lit 105562098127728))]
theorem block016_data_flat002_step : block016_data_flat002 = (CoefficientMerge.fastMerge block016_data_flat000 block016_data_flat001) := by decide +kernel
theorem block016_data_flat002_original : block016_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (101846650752000 : Int) atom1089Coded) (CoefficientMerge.scale (105562098127728 : Int) atom1090Coded)) := by
  rw [block016_data_flat002_step, block016_data_flat000_original, block016_data_flat001_original]
def block016_data_flat003 : CoefficientMerge.Poly := [(nat_lit 1882, Int.ofNat (nat_lit 125826931427472))]
theorem block016_data_flat003_step : block016_data_flat003 = (CoefficientMerge.scale (125826931427472 : Int) atom1091Coded) := by decide +kernel
theorem block016_data_flat003_original : block016_data_flat003 = (CoefficientMerge.scale (125826931427472 : Int) atom1091Coded) := by
  rw [block016_data_flat003_step]
def block016_data_flat004 : CoefficientMerge.Poly := [(nat_lit 1883, Int.ofNat (nat_lit 136085099683104))]
theorem block016_data_flat004_step : block016_data_flat004 = (CoefficientMerge.scale (136085099683104 : Int) atom1092Coded) := by decide +kernel
theorem block016_data_flat004_original : block016_data_flat004 = (CoefficientMerge.scale (136085099683104 : Int) atom1092Coded) := by
  rw [block016_data_flat004_step]
def block016_data_flat005 : CoefficientMerge.Poly := [(nat_lit 1884, Int.ofNat (nat_lit 161923371724224))]
theorem block016_data_flat005_step : block016_data_flat005 = (CoefficientMerge.scale (161923371724224 : Int) atom1093Coded) := by decide +kernel
theorem block016_data_flat005_original : block016_data_flat005 = (CoefficientMerge.scale (161923371724224 : Int) atom1093Coded) := by
  rw [block016_data_flat005_step]
def block016_data_flat006 : CoefficientMerge.Poly := [(nat_lit 1883, Int.ofNat (nat_lit 136085099683104)), (nat_lit 1884, Int.ofNat (nat_lit 161923371724224))]
theorem block016_data_flat006_step : block016_data_flat006 = (CoefficientMerge.fastMerge block016_data_flat004 block016_data_flat005) := by decide +kernel
theorem block016_data_flat006_original : block016_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (136085099683104 : Int) atom1092Coded) (CoefficientMerge.scale (161923371724224 : Int) atom1093Coded)) := by
  rw [block016_data_flat006_step, block016_data_flat004_original, block016_data_flat005_original]
def block016_data_flat007 : CoefficientMerge.Poly := [(nat_lit 1882, Int.ofNat (nat_lit 125826931427472)), (nat_lit 1883, Int.ofNat (nat_lit 136085099683104)), (nat_lit 1884, Int.ofNat (nat_lit 161923371724224))]
theorem block016_data_flat007_step : block016_data_flat007 = (CoefficientMerge.fastMerge block016_data_flat003 block016_data_flat006) := by decide +kernel
theorem block016_data_flat007_original : block016_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (125826931427472 : Int) atom1091Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136085099683104 : Int) atom1092Coded) (CoefficientMerge.scale (161923371724224 : Int) atom1093Coded))) := by
  rw [block016_data_flat007_step, block016_data_flat003_original, block016_data_flat006_original]
def block016_data_flat008 : CoefficientMerge.Poly := [(nat_lit 1880, Int.ofNat (nat_lit 101846650752000)), (nat_lit 1881, Int.ofNat (nat_lit 105562098127728)), (nat_lit 1882, Int.ofNat (nat_lit 125826931427472)), (nat_lit 1883, Int.ofNat (nat_lit 136085099683104)), (nat_lit 1884, Int.ofNat (nat_lit 161923371724224))]
theorem block016_data_flat008_step : block016_data_flat008 = (CoefficientMerge.fastMerge block016_data_flat002 block016_data_flat007) := by decide +kernel
theorem block016_data_flat008_original : block016_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (101846650752000 : Int) atom1089Coded) (CoefficientMerge.scale (105562098127728 : Int) atom1090Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125826931427472 : Int) atom1091Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136085099683104 : Int) atom1092Coded) (CoefficientMerge.scale (161923371724224 : Int) atom1093Coded)))) := by
  rw [block016_data_flat008_step, block016_data_flat002_original, block016_data_flat007_original]
def block016_data_flat009 : CoefficientMerge.Poly := [(nat_lit 1885, Int.ofNat (nat_lit 153240978844800))]
theorem block016_data_flat009_step : block016_data_flat009 = (CoefficientMerge.scale (153240978844800 : Int) atom1094Coded) := by decide +kernel
theorem block016_data_flat009_original : block016_data_flat009 = (CoefficientMerge.scale (153240978844800 : Int) atom1094Coded) := by
  rw [block016_data_flat009_step]
def block016_data_flat010 : CoefficientMerge.Poly := [(nat_lit 1886, Int.ofNat (nat_lit 140884323148800))]
theorem block016_data_flat010_step : block016_data_flat010 = (CoefficientMerge.scale (140884323148800 : Int) atom1095Coded) := by decide +kernel
theorem block016_data_flat010_original : block016_data_flat010 = (CoefficientMerge.scale (140884323148800 : Int) atom1095Coded) := by
  rw [block016_data_flat010_step]
def block016_data_flat011 : CoefficientMerge.Poly := [(nat_lit 1885, Int.ofNat (nat_lit 153240978844800)), (nat_lit 1886, Int.ofNat (nat_lit 140884323148800))]
theorem block016_data_flat011_step : block016_data_flat011 = (CoefficientMerge.fastMerge block016_data_flat009 block016_data_flat010) := by decide +kernel
theorem block016_data_flat011_original : block016_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (153240978844800 : Int) atom1094Coded) (CoefficientMerge.scale (140884323148800 : Int) atom1095Coded)) := by
  rw [block016_data_flat011_step, block016_data_flat009_original, block016_data_flat010_original]
def block016_data_flat012 : CoefficientMerge.Poly := [(nat_lit 1887, Int.ofNat (nat_lit 143314674048000))]
theorem block016_data_flat012_step : block016_data_flat012 = (CoefficientMerge.scale (143314674048000 : Int) atom1096Coded) := by decide +kernel
theorem block016_data_flat012_original : block016_data_flat012 = (CoefficientMerge.scale (143314674048000 : Int) atom1096Coded) := by
  rw [block016_data_flat012_step]
def block016_data_flat013 : CoefficientMerge.Poly := [(nat_lit 1888, Int.ofNat (nat_lit 133922514700800))]
theorem block016_data_flat013_step : block016_data_flat013 = (CoefficientMerge.scale (133922514700800 : Int) atom1097Coded) := by decide +kernel
theorem block016_data_flat013_original : block016_data_flat013 = (CoefficientMerge.scale (133922514700800 : Int) atom1097Coded) := by
  rw [block016_data_flat013_step]
def block016_data_flat014 : CoefficientMerge.Poly := [(nat_lit 1889, Int.ofNat (nat_lit 134463093811200))]
theorem block016_data_flat014_step : block016_data_flat014 = (CoefficientMerge.scale (134463093811200 : Int) atom1098Coded) := by decide +kernel
theorem block016_data_flat014_original : block016_data_flat014 = (CoefficientMerge.scale (134463093811200 : Int) atom1098Coded) := by
  rw [block016_data_flat014_step]
def block016_data_flat015 : CoefficientMerge.Poly := [(nat_lit 1888, Int.ofNat (nat_lit 133922514700800)), (nat_lit 1889, Int.ofNat (nat_lit 134463093811200))]
theorem block016_data_flat015_step : block016_data_flat015 = (CoefficientMerge.fastMerge block016_data_flat013 block016_data_flat014) := by decide +kernel
theorem block016_data_flat015_original : block016_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (133922514700800 : Int) atom1097Coded) (CoefficientMerge.scale (134463093811200 : Int) atom1098Coded)) := by
  rw [block016_data_flat015_step, block016_data_flat013_original, block016_data_flat014_original]
def block016_data_flat016 : CoefficientMerge.Poly := [(nat_lit 1887, Int.ofNat (nat_lit 143314674048000)), (nat_lit 1888, Int.ofNat (nat_lit 133922514700800)), (nat_lit 1889, Int.ofNat (nat_lit 134463093811200))]
theorem block016_data_flat016_step : block016_data_flat016 = (CoefficientMerge.fastMerge block016_data_flat012 block016_data_flat015) := by decide +kernel
theorem block016_data_flat016_original : block016_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (143314674048000 : Int) atom1096Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (133922514700800 : Int) atom1097Coded) (CoefficientMerge.scale (134463093811200 : Int) atom1098Coded))) := by
  rw [block016_data_flat016_step, block016_data_flat012_original, block016_data_flat015_original]
def block016_data_flat017 : CoefficientMerge.Poly := [(nat_lit 1885, Int.ofNat (nat_lit 153240978844800)), (nat_lit 1886, Int.ofNat (nat_lit 140884323148800)), (nat_lit 1887, Int.ofNat (nat_lit 143314674048000)), (nat_lit 1888, Int.ofNat (nat_lit 133922514700800)), (nat_lit 1889, Int.ofNat (nat_lit 134463093811200))]
theorem block016_data_flat017_step : block016_data_flat017 = (CoefficientMerge.fastMerge block016_data_flat011 block016_data_flat016) := by decide +kernel
theorem block016_data_flat017_original : block016_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153240978844800 : Int) atom1094Coded) (CoefficientMerge.scale (140884323148800 : Int) atom1095Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (143314674048000 : Int) atom1096Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (133922514700800 : Int) atom1097Coded) (CoefficientMerge.scale (134463093811200 : Int) atom1098Coded)))) := by
  rw [block016_data_flat017_step, block016_data_flat011_original, block016_data_flat016_original]
def block016_data_flat018 : CoefficientMerge.Poly := [(nat_lit 1880, Int.ofNat (nat_lit 101846650752000)), (nat_lit 1881, Int.ofNat (nat_lit 105562098127728)), (nat_lit 1882, Int.ofNat (nat_lit 125826931427472)), (nat_lit 1883, Int.ofNat (nat_lit 136085099683104)), (nat_lit 1884, Int.ofNat (nat_lit 161923371724224)), (nat_lit 1885, Int.ofNat (nat_lit 153240978844800)), (nat_lit 1886, Int.ofNat (nat_lit 140884323148800)), (nat_lit 1887, Int.ofNat (nat_lit 143314674048000)), (nat_lit 1888, Int.ofNat (nat_lit 133922514700800)), (nat_lit 1889, Int.ofNat (nat_lit 134463093811200))]
theorem block016_data_flat018_step : block016_data_flat018 = (CoefficientMerge.fastMerge block016_data_flat008 block016_data_flat017) := by decide +kernel
theorem block016_data_flat018_original : block016_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (101846650752000 : Int) atom1089Coded) (CoefficientMerge.scale (105562098127728 : Int) atom1090Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125826931427472 : Int) atom1091Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136085099683104 : Int) atom1092Coded) (CoefficientMerge.scale (161923371724224 : Int) atom1093Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153240978844800 : Int) atom1094Coded) (CoefficientMerge.scale (140884323148800 : Int) atom1095Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (143314674048000 : Int) atom1096Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (133922514700800 : Int) atom1097Coded) (CoefficientMerge.scale (134463093811200 : Int) atom1098Coded))))) := by
  rw [block016_data_flat018_step, block016_data_flat008_original, block016_data_flat017_original]
def block016_data_flat019 : CoefficientMerge.Poly := [(nat_lit 1890, Int.ofNat (nat_lit 172926682790400))]
theorem block016_data_flat019_step : block016_data_flat019 = (CoefficientMerge.scale (172926682790400 : Int) atom1099Coded) := by decide +kernel
theorem block016_data_flat019_original : block016_data_flat019 = (CoefficientMerge.scale (172926682790400 : Int) atom1099Coded) := by
  rw [block016_data_flat019_step]
def block016_data_flat020 : CoefficientMerge.Poly := [(nat_lit 1891, Int.ofNat (nat_lit 146965354905600))]
theorem block016_data_flat020_step : block016_data_flat020 = (CoefficientMerge.scale (146965354905600 : Int) atom1100Coded) := by decide +kernel
theorem block016_data_flat020_original : block016_data_flat020 = (CoefficientMerge.scale (146965354905600 : Int) atom1100Coded) := by
  rw [block016_data_flat020_step]
def block016_data_flat021 : CoefficientMerge.Poly := [(nat_lit 1890, Int.ofNat (nat_lit 172926682790400)), (nat_lit 1891, Int.ofNat (nat_lit 146965354905600))]
theorem block016_data_flat021_step : block016_data_flat021 = (CoefficientMerge.fastMerge block016_data_flat019 block016_data_flat020) := by decide +kernel
theorem block016_data_flat021_original : block016_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (172926682790400 : Int) atom1099Coded) (CoefficientMerge.scale (146965354905600 : Int) atom1100Coded)) := by
  rw [block016_data_flat021_step, block016_data_flat019_original, block016_data_flat020_original]
def block016_data_flat022 : CoefficientMerge.Poly := [(nat_lit 1892, Int.ofNat (nat_lit 206053422220800))]
theorem block016_data_flat022_step : block016_data_flat022 = (CoefficientMerge.scale (206053422220800 : Int) atom1101Coded) := by decide +kernel
theorem block016_data_flat022_original : block016_data_flat022 = (CoefficientMerge.scale (206053422220800 : Int) atom1101Coded) := by
  rw [block016_data_flat022_step]
def block016_data_flat023 : CoefficientMerge.Poly := [(nat_lit 1893, Int.ofNat (nat_lit 209093938099200))]
theorem block016_data_flat023_step : block016_data_flat023 = (CoefficientMerge.scale (209093938099200 : Int) atom1102Coded) := by decide +kernel
theorem block016_data_flat023_original : block016_data_flat023 = (CoefficientMerge.scale (209093938099200 : Int) atom1102Coded) := by
  rw [block016_data_flat023_step]
def block016_data_flat024 : CoefficientMerge.Poly := [(nat_lit 1894, Int.ofNat (nat_lit 248450545728000))]
theorem block016_data_flat024_step : block016_data_flat024 = (CoefficientMerge.scale (248450545728000 : Int) atom1103Coded) := by decide +kernel
theorem block016_data_flat024_original : block016_data_flat024 = (CoefficientMerge.scale (248450545728000 : Int) atom1103Coded) := by
  rw [block016_data_flat024_step]
def block016_data_flat025 : CoefficientMerge.Poly := [(nat_lit 1893, Int.ofNat (nat_lit 209093938099200)), (nat_lit 1894, Int.ofNat (nat_lit 248450545728000))]
theorem block016_data_flat025_step : block016_data_flat025 = (CoefficientMerge.fastMerge block016_data_flat023 block016_data_flat024) := by decide +kernel
theorem block016_data_flat025_original : block016_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (209093938099200 : Int) atom1102Coded) (CoefficientMerge.scale (248450545728000 : Int) atom1103Coded)) := by
  rw [block016_data_flat025_step, block016_data_flat023_original, block016_data_flat024_original]
def block016_data_flat026 : CoefficientMerge.Poly := [(nat_lit 1892, Int.ofNat (nat_lit 206053422220800)), (nat_lit 1893, Int.ofNat (nat_lit 209093938099200)), (nat_lit 1894, Int.ofNat (nat_lit 248450545728000))]
theorem block016_data_flat026_step : block016_data_flat026 = (CoefficientMerge.fastMerge block016_data_flat022 block016_data_flat025) := by decide +kernel
theorem block016_data_flat026_original : block016_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (206053422220800 : Int) atom1101Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (209093938099200 : Int) atom1102Coded) (CoefficientMerge.scale (248450545728000 : Int) atom1103Coded))) := by
  rw [block016_data_flat026_step, block016_data_flat022_original, block016_data_flat025_original]
def block016_data_flat027 : CoefficientMerge.Poly := [(nat_lit 1890, Int.ofNat (nat_lit 172926682790400)), (nat_lit 1891, Int.ofNat (nat_lit 146965354905600)), (nat_lit 1892, Int.ofNat (nat_lit 206053422220800)), (nat_lit 1893, Int.ofNat (nat_lit 209093938099200)), (nat_lit 1894, Int.ofNat (nat_lit 248450545728000))]
theorem block016_data_flat027_step : block016_data_flat027 = (CoefficientMerge.fastMerge block016_data_flat021 block016_data_flat026) := by decide +kernel
theorem block016_data_flat027_original : block016_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (172926682790400 : Int) atom1099Coded) (CoefficientMerge.scale (146965354905600 : Int) atom1100Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (206053422220800 : Int) atom1101Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (209093938099200 : Int) atom1102Coded) (CoefficientMerge.scale (248450545728000 : Int) atom1103Coded)))) := by
  rw [block016_data_flat027_step, block016_data_flat021_original, block016_data_flat026_original]
def block016_data_flat028 : CoefficientMerge.Poly := [(nat_lit 1895, Int.ofNat (nat_lit 287807153356800))]
theorem block016_data_flat028_step : block016_data_flat028 = (CoefficientMerge.scale (287807153356800 : Int) atom1104Coded) := by decide +kernel
theorem block016_data_flat028_original : block016_data_flat028 = (CoefficientMerge.scale (287807153356800 : Int) atom1104Coded) := by
  rw [block016_data_flat028_step]
def block016_data_flat029 : CoefficientMerge.Poly := [(nat_lit 1903, Int.ofNat (nat_lit 81912017510400))]
theorem block016_data_flat029_step : block016_data_flat029 = (CoefficientMerge.scale (81912017510400 : Int) atom1105Coded) := by decide +kernel
theorem block016_data_flat029_original : block016_data_flat029 = (CoefficientMerge.scale (81912017510400 : Int) atom1105Coded) := by
  rw [block016_data_flat029_step]
def block016_data_flat030 : CoefficientMerge.Poly := [(nat_lit 1895, Int.ofNat (nat_lit 287807153356800)), (nat_lit 1903, Int.ofNat (nat_lit 81912017510400))]
theorem block016_data_flat030_step : block016_data_flat030 = (CoefficientMerge.fastMerge block016_data_flat028 block016_data_flat029) := by decide +kernel
theorem block016_data_flat030_original : block016_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (287807153356800 : Int) atom1104Coded) (CoefficientMerge.scale (81912017510400 : Int) atom1105Coded)) := by
  rw [block016_data_flat030_step, block016_data_flat028_original, block016_data_flat029_original]
def block016_data_flat031 : CoefficientMerge.Poly := [(nat_lit 1904, Int.ofNat (nat_lit 148101709324800))]
theorem block016_data_flat031_step : block016_data_flat031 = (CoefficientMerge.scale (148101709324800 : Int) atom1106Coded) := by decide +kernel
theorem block016_data_flat031_original : block016_data_flat031 = (CoefficientMerge.scale (148101709324800 : Int) atom1106Coded) := by
  rw [block016_data_flat031_step]
def block016_data_flat032 : CoefficientMerge.Poly := [(nat_lit 1905, Int.ofNat (nat_lit 135383723561328))]
theorem block016_data_flat032_step : block016_data_flat032 = (CoefficientMerge.scale (135383723561328 : Int) atom1107Coded) := by decide +kernel
theorem block016_data_flat032_original : block016_data_flat032 = (CoefficientMerge.scale (135383723561328 : Int) atom1107Coded) := by
  rw [block016_data_flat032_step]
def block016_data_flat033 : CoefficientMerge.Poly := [(nat_lit 1906, Int.ofNat (nat_lit 153607371376272))]
theorem block016_data_flat033_step : block016_data_flat033 = (CoefficientMerge.scale (153607371376272 : Int) atom1108Coded) := by decide +kernel
theorem block016_data_flat033_original : block016_data_flat033 = (CoefficientMerge.scale (153607371376272 : Int) atom1108Coded) := by
  rw [block016_data_flat033_step]
def block016_data_flat034 : CoefficientMerge.Poly := [(nat_lit 1905, Int.ofNat (nat_lit 135383723561328)), (nat_lit 1906, Int.ofNat (nat_lit 153607371376272))]
theorem block016_data_flat034_step : block016_data_flat034 = (CoefficientMerge.fastMerge block016_data_flat032 block016_data_flat033) := by decide +kernel
theorem block016_data_flat034_original : block016_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (135383723561328 : Int) atom1107Coded) (CoefficientMerge.scale (153607371376272 : Int) atom1108Coded)) := by
  rw [block016_data_flat034_step, block016_data_flat032_original, block016_data_flat033_original]
def block016_data_flat035 : CoefficientMerge.Poly := [(nat_lit 1904, Int.ofNat (nat_lit 148101709324800)), (nat_lit 1905, Int.ofNat (nat_lit 135383723561328)), (nat_lit 1906, Int.ofNat (nat_lit 153607371376272))]
theorem block016_data_flat035_step : block016_data_flat035 = (CoefficientMerge.fastMerge block016_data_flat031 block016_data_flat034) := by decide +kernel
theorem block016_data_flat035_original : block016_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (148101709324800 : Int) atom1106Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135383723561328 : Int) atom1107Coded) (CoefficientMerge.scale (153607371376272 : Int) atom1108Coded))) := by
  rw [block016_data_flat035_step, block016_data_flat031_original, block016_data_flat034_original]
def block016_data_flat036 : CoefficientMerge.Poly := [(nat_lit 1895, Int.ofNat (nat_lit 287807153356800)), (nat_lit 1903, Int.ofNat (nat_lit 81912017510400)), (nat_lit 1904, Int.ofNat (nat_lit 148101709324800)), (nat_lit 1905, Int.ofNat (nat_lit 135383723561328)), (nat_lit 1906, Int.ofNat (nat_lit 153607371376272))]
theorem block016_data_flat036_step : block016_data_flat036 = (CoefficientMerge.fastMerge block016_data_flat030 block016_data_flat035) := by decide +kernel
theorem block016_data_flat036_original : block016_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (287807153356800 : Int) atom1104Coded) (CoefficientMerge.scale (81912017510400 : Int) atom1105Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (148101709324800 : Int) atom1106Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135383723561328 : Int) atom1107Coded) (CoefficientMerge.scale (153607371376272 : Int) atom1108Coded)))) := by
  rw [block016_data_flat036_step, block016_data_flat030_original, block016_data_flat035_original]
def block016_data_flat037 : CoefficientMerge.Poly := [(nat_lit 1890, Int.ofNat (nat_lit 172926682790400)), (nat_lit 1891, Int.ofNat (nat_lit 146965354905600)), (nat_lit 1892, Int.ofNat (nat_lit 206053422220800)), (nat_lit 1893, Int.ofNat (nat_lit 209093938099200)), (nat_lit 1894, Int.ofNat (nat_lit 248450545728000)), (nat_lit 1895, Int.ofNat (nat_lit 287807153356800)), (nat_lit 1903, Int.ofNat (nat_lit 81912017510400)), (nat_lit 1904, Int.ofNat (nat_lit 148101709324800)), (nat_lit 1905, Int.ofNat (nat_lit 135383723561328)), (nat_lit 1906, Int.ofNat (nat_lit 153607371376272))]
theorem block016_data_flat037_step : block016_data_flat037 = (CoefficientMerge.fastMerge block016_data_flat027 block016_data_flat036) := by decide +kernel
theorem block016_data_flat037_original : block016_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (172926682790400 : Int) atom1099Coded) (CoefficientMerge.scale (146965354905600 : Int) atom1100Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (206053422220800 : Int) atom1101Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (209093938099200 : Int) atom1102Coded) (CoefficientMerge.scale (248450545728000 : Int) atom1103Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (287807153356800 : Int) atom1104Coded) (CoefficientMerge.scale (81912017510400 : Int) atom1105Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (148101709324800 : Int) atom1106Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135383723561328 : Int) atom1107Coded) (CoefficientMerge.scale (153607371376272 : Int) atom1108Coded))))) := by
  rw [block016_data_flat037_step, block016_data_flat027_original, block016_data_flat036_original]
def block016_data_flat038 : CoefficientMerge.Poly := [(nat_lit 1880, Int.ofNat (nat_lit 101846650752000)), (nat_lit 1881, Int.ofNat (nat_lit 105562098127728)), (nat_lit 1882, Int.ofNat (nat_lit 125826931427472)), (nat_lit 1883, Int.ofNat (nat_lit 136085099683104)), (nat_lit 1884, Int.ofNat (nat_lit 161923371724224)), (nat_lit 1885, Int.ofNat (nat_lit 153240978844800)), (nat_lit 1886, Int.ofNat (nat_lit 140884323148800)), (nat_lit 1887, Int.ofNat (nat_lit 143314674048000)), (nat_lit 1888, Int.ofNat (nat_lit 133922514700800)), (nat_lit 1889, Int.ofNat (nat_lit 134463093811200)), (nat_lit 1890, Int.ofNat (nat_lit 172926682790400)), (nat_lit 1891, Int.ofNat (nat_lit 146965354905600)), (nat_lit 1892, Int.ofNat (nat_lit 206053422220800)), (nat_lit 1893, Int.ofNat (nat_lit 209093938099200)), (nat_lit 1894, Int.ofNat (nat_lit 248450545728000)), (nat_lit 1895, Int.ofNat (nat_lit 287807153356800)), (nat_lit 1903, Int.ofNat (nat_lit 81912017510400)), (nat_lit 1904, Int.ofNat (nat_lit 148101709324800)), (nat_lit 1905, Int.ofNat (nat_lit 135383723561328)), (nat_lit 1906, Int.ofNat (nat_lit 153607371376272))]
theorem block016_data_flat038_step : block016_data_flat038 = (CoefficientMerge.fastMerge block016_data_flat018 block016_data_flat037) := by decide +kernel
theorem block016_data_flat038_original : block016_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (101846650752000 : Int) atom1089Coded) (CoefficientMerge.scale (105562098127728 : Int) atom1090Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125826931427472 : Int) atom1091Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136085099683104 : Int) atom1092Coded) (CoefficientMerge.scale (161923371724224 : Int) atom1093Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153240978844800 : Int) atom1094Coded) (CoefficientMerge.scale (140884323148800 : Int) atom1095Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (143314674048000 : Int) atom1096Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (133922514700800 : Int) atom1097Coded) (CoefficientMerge.scale (134463093811200 : Int) atom1098Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (172926682790400 : Int) atom1099Coded) (CoefficientMerge.scale (146965354905600 : Int) atom1100Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (206053422220800 : Int) atom1101Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (209093938099200 : Int) atom1102Coded) (CoefficientMerge.scale (248450545728000 : Int) atom1103Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (287807153356800 : Int) atom1104Coded) (CoefficientMerge.scale (81912017510400 : Int) atom1105Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (148101709324800 : Int) atom1106Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135383723561328 : Int) atom1107Coded) (CoefficientMerge.scale (153607371376272 : Int) atom1108Coded)))))) := by
  rw [block016_data_flat038_step, block016_data_flat018_original, block016_data_flat037_original]
def block016_data_flat039 : CoefficientMerge.Poly := [(nat_lit 1907, Int.ofNat (nat_lit 165949249814304))]
theorem block016_data_flat039_step : block016_data_flat039 = (CoefficientMerge.scale (165949249814304 : Int) atom1109Coded) := by decide +kernel
theorem block016_data_flat039_original : block016_data_flat039 = (CoefficientMerge.scale (165949249814304 : Int) atom1109Coded) := by
  rw [block016_data_flat039_step]
def block016_data_flat040 : CoefficientMerge.Poly := [(nat_lit 1908, Int.ofNat (nat_lit 193871232037824))]
theorem block016_data_flat040_step : block016_data_flat040 = (CoefficientMerge.scale (193871232037824 : Int) atom1110Coded) := by decide +kernel
theorem block016_data_flat040_original : block016_data_flat040 = (CoefficientMerge.scale (193871232037824 : Int) atom1110Coded) := by
  rw [block016_data_flat040_step]
def block016_data_flat041 : CoefficientMerge.Poly := [(nat_lit 1907, Int.ofNat (nat_lit 165949249814304)), (nat_lit 1908, Int.ofNat (nat_lit 193871232037824))]
theorem block016_data_flat041_step : block016_data_flat041 = (CoefficientMerge.fastMerge block016_data_flat039 block016_data_flat040) := by decide +kernel
theorem block016_data_flat041_original : block016_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (165949249814304 : Int) atom1109Coded) (CoefficientMerge.scale (193871232037824 : Int) atom1110Coded)) := by
  rw [block016_data_flat041_step, block016_data_flat039_original, block016_data_flat040_original]
def block016_data_flat042 : CoefficientMerge.Poly := [(nat_lit 1909, Int.ofNat (nat_lit 185210101507200))]
theorem block016_data_flat042_step : block016_data_flat042 = (CoefficientMerge.scale (185210101507200 : Int) atom1111Coded) := by decide +kernel
theorem block016_data_flat042_original : block016_data_flat042 = (CoefficientMerge.scale (185210101507200 : Int) atom1111Coded) := by
  rw [block016_data_flat042_step]
def block016_data_flat043 : CoefficientMerge.Poly := [(nat_lit 1910, Int.ofNat (nat_lit 172874708160000))]
theorem block016_data_flat043_step : block016_data_flat043 = (CoefficientMerge.scale (172874708160000 : Int) atom1112Coded) := by decide +kernel
theorem block016_data_flat043_original : block016_data_flat043 = (CoefficientMerge.scale (172874708160000 : Int) atom1112Coded) := by
  rw [block016_data_flat043_step]
def block016_data_flat044 : CoefficientMerge.Poly := [(nat_lit 1911, Int.ofNat (nat_lit 175326321408000))]
theorem block016_data_flat044_step : block016_data_flat044 = (CoefficientMerge.scale (175326321408000 : Int) atom1113Coded) := by decide +kernel
theorem block016_data_flat044_original : block016_data_flat044 = (CoefficientMerge.scale (175326321408000 : Int) atom1113Coded) := by
  rw [block016_data_flat044_step]
def block016_data_flat045 : CoefficientMerge.Poly := [(nat_lit 1910, Int.ofNat (nat_lit 172874708160000)), (nat_lit 1911, Int.ofNat (nat_lit 175326321408000))]
theorem block016_data_flat045_step : block016_data_flat045 = (CoefficientMerge.fastMerge block016_data_flat043 block016_data_flat044) := by decide +kernel
theorem block016_data_flat045_original : block016_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (172874708160000 : Int) atom1112Coded) (CoefficientMerge.scale (175326321408000 : Int) atom1113Coded)) := by
  rw [block016_data_flat045_step, block016_data_flat043_original, block016_data_flat044_original]
def block016_data_flat046 : CoefficientMerge.Poly := [(nat_lit 1909, Int.ofNat (nat_lit 185210101507200)), (nat_lit 1910, Int.ofNat (nat_lit 172874708160000)), (nat_lit 1911, Int.ofNat (nat_lit 175326321408000))]
theorem block016_data_flat046_step : block016_data_flat046 = (CoefficientMerge.fastMerge block016_data_flat042 block016_data_flat045) := by decide +kernel
theorem block016_data_flat046_original : block016_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (185210101507200 : Int) atom1111Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172874708160000 : Int) atom1112Coded) (CoefficientMerge.scale (175326321408000 : Int) atom1113Coded))) := by
  rw [block016_data_flat046_step, block016_data_flat042_original, block016_data_flat045_original]
def block016_data_flat047 : CoefficientMerge.Poly := [(nat_lit 1907, Int.ofNat (nat_lit 165949249814304)), (nat_lit 1908, Int.ofNat (nat_lit 193871232037824)), (nat_lit 1909, Int.ofNat (nat_lit 185210101507200)), (nat_lit 1910, Int.ofNat (nat_lit 172874708160000)), (nat_lit 1911, Int.ofNat (nat_lit 175326321408000))]
theorem block016_data_flat047_step : block016_data_flat047 = (CoefficientMerge.fastMerge block016_data_flat041 block016_data_flat046) := by decide +kernel
theorem block016_data_flat047_original : block016_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (165949249814304 : Int) atom1109Coded) (CoefficientMerge.scale (193871232037824 : Int) atom1110Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (185210101507200 : Int) atom1111Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172874708160000 : Int) atom1112Coded) (CoefficientMerge.scale (175326321408000 : Int) atom1113Coded)))) := by
  rw [block016_data_flat047_step, block016_data_flat041_original, block016_data_flat046_original]
def block016_data_flat048 : CoefficientMerge.Poly := [(nat_lit 1912, Int.ofNat (nat_lit 165955424409600))]
theorem block016_data_flat048_step : block016_data_flat048 = (CoefficientMerge.scale (165955424409600 : Int) atom1114Coded) := by decide +kernel
theorem block016_data_flat048_original : block016_data_flat048 = (CoefficientMerge.scale (165955424409600 : Int) atom1114Coded) := by
  rw [block016_data_flat048_step]
def block016_data_flat049 : CoefficientMerge.Poly := [(nat_lit 1913, Int.ofNat (nat_lit 166517265868800))]
theorem block016_data_flat049_step : block016_data_flat049 = (CoefficientMerge.scale (166517265868800 : Int) atom1115Coded) := by decide +kernel
theorem block016_data_flat049_original : block016_data_flat049 = (CoefficientMerge.scale (166517265868800 : Int) atom1115Coded) := by
  rw [block016_data_flat049_step]
def block016_data_flat050 : CoefficientMerge.Poly := [(nat_lit 1912, Int.ofNat (nat_lit 165955424409600)), (nat_lit 1913, Int.ofNat (nat_lit 166517265868800))]
theorem block016_data_flat050_step : block016_data_flat050 = (CoefficientMerge.fastMerge block016_data_flat048 block016_data_flat049) := by decide +kernel
theorem block016_data_flat050_original : block016_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (165955424409600 : Int) atom1114Coded) (CoefficientMerge.scale (166517265868800 : Int) atom1115Coded)) := by
  rw [block016_data_flat050_step, block016_data_flat048_original, block016_data_flat049_original]
def block016_data_flat051 : CoefficientMerge.Poly := [(nat_lit 1914, Int.ofNat (nat_lit 207331525632000))]
theorem block016_data_flat051_step : block016_data_flat051 = (CoefficientMerge.scale (207331525632000 : Int) atom1116Coded) := by decide +kernel
theorem block016_data_flat051_original : block016_data_flat051 = (CoefficientMerge.scale (207331525632000 : Int) atom1116Coded) := by
  rw [block016_data_flat051_step]
def block016_data_flat052 : CoefficientMerge.Poly := [(nat_lit 1915, Int.ofNat (nat_lit 186050276966400))]
theorem block016_data_flat052_step : block016_data_flat052 = (CoefficientMerge.scale (186050276966400 : Int) atom1117Coded) := by decide +kernel
theorem block016_data_flat052_original : block016_data_flat052 = (CoefficientMerge.scale (186050276966400 : Int) atom1117Coded) := by
  rw [block016_data_flat052_step]
def block016_data_flat053 : CoefficientMerge.Poly := [(nat_lit 1916, Int.ofNat (nat_lit 249818423500800))]
theorem block016_data_flat053_step : block016_data_flat053 = (CoefficientMerge.scale (249818423500800 : Int) atom1118Coded) := by decide +kernel
theorem block016_data_flat053_original : block016_data_flat053 = (CoefficientMerge.scale (249818423500800 : Int) atom1118Coded) := by
  rw [block016_data_flat053_step]
def block016_data_flat054 : CoefficientMerge.Poly := [(nat_lit 1915, Int.ofNat (nat_lit 186050276966400)), (nat_lit 1916, Int.ofNat (nat_lit 249818423500800))]
theorem block016_data_flat054_step : block016_data_flat054 = (CoefficientMerge.fastMerge block016_data_flat052 block016_data_flat053) := by decide +kernel
theorem block016_data_flat054_original : block016_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (186050276966400 : Int) atom1117Coded) (CoefficientMerge.scale (249818423500800 : Int) atom1118Coded)) := by
  rw [block016_data_flat054_step, block016_data_flat052_original, block016_data_flat053_original]
def block016_data_flat055 : CoefficientMerge.Poly := [(nat_lit 1914, Int.ofNat (nat_lit 207331525632000)), (nat_lit 1915, Int.ofNat (nat_lit 186050276966400)), (nat_lit 1916, Int.ofNat (nat_lit 249818423500800))]
theorem block016_data_flat055_step : block016_data_flat055 = (CoefficientMerge.fastMerge block016_data_flat051 block016_data_flat054) := by decide +kernel
theorem block016_data_flat055_original : block016_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (207331525632000 : Int) atom1116Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (186050276966400 : Int) atom1117Coded) (CoefficientMerge.scale (249818423500800 : Int) atom1118Coded))) := by
  rw [block016_data_flat055_step, block016_data_flat051_original, block016_data_flat054_original]
def block016_data_flat056 : CoefficientMerge.Poly := [(nat_lit 1912, Int.ofNat (nat_lit 165955424409600)), (nat_lit 1913, Int.ofNat (nat_lit 166517265868800)), (nat_lit 1914, Int.ofNat (nat_lit 207331525632000)), (nat_lit 1915, Int.ofNat (nat_lit 186050276966400)), (nat_lit 1916, Int.ofNat (nat_lit 249818423500800))]
theorem block016_data_flat056_step : block016_data_flat056 = (CoefficientMerge.fastMerge block016_data_flat050 block016_data_flat055) := by decide +kernel
theorem block016_data_flat056_original : block016_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (165955424409600 : Int) atom1114Coded) (CoefficientMerge.scale (166517265868800 : Int) atom1115Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207331525632000 : Int) atom1116Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (186050276966400 : Int) atom1117Coded) (CoefficientMerge.scale (249818423500800 : Int) atom1118Coded)))) := by
  rw [block016_data_flat056_step, block016_data_flat050_original, block016_data_flat055_original]
def block016_data_flat057 : CoefficientMerge.Poly := [(nat_lit 1907, Int.ofNat (nat_lit 165949249814304)), (nat_lit 1908, Int.ofNat (nat_lit 193871232037824)), (nat_lit 1909, Int.ofNat (nat_lit 185210101507200)), (nat_lit 1910, Int.ofNat (nat_lit 172874708160000)), (nat_lit 1911, Int.ofNat (nat_lit 175326321408000)), (nat_lit 1912, Int.ofNat (nat_lit 165955424409600)), (nat_lit 1913, Int.ofNat (nat_lit 166517265868800)), (nat_lit 1914, Int.ofNat (nat_lit 207331525632000)), (nat_lit 1915, Int.ofNat (nat_lit 186050276966400)), (nat_lit 1916, Int.ofNat (nat_lit 249818423500800))]
theorem block016_data_flat057_step : block016_data_flat057 = (CoefficientMerge.fastMerge block016_data_flat047 block016_data_flat056) := by decide +kernel
theorem block016_data_flat057_original : block016_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (165949249814304 : Int) atom1109Coded) (CoefficientMerge.scale (193871232037824 : Int) atom1110Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (185210101507200 : Int) atom1111Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172874708160000 : Int) atom1112Coded) (CoefficientMerge.scale (175326321408000 : Int) atom1113Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (165955424409600 : Int) atom1114Coded) (CoefficientMerge.scale (166517265868800 : Int) atom1115Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207331525632000 : Int) atom1116Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (186050276966400 : Int) atom1117Coded) (CoefficientMerge.scale (249818423500800 : Int) atom1118Coded))))) := by
  rw [block016_data_flat057_step, block016_data_flat047_original, block016_data_flat056_original]
def block016_data_flat058 : CoefficientMerge.Poly := [(nat_lit 1917, Int.ofNat (nat_lit 262197835468800))]
theorem block016_data_flat058_step : block016_data_flat058 = (CoefficientMerge.scale (262197835468800 : Int) atom1119Coded) := by decide +kernel
theorem block016_data_flat058_original : block016_data_flat058 = (CoefficientMerge.scale (262197835468800 : Int) atom1119Coded) := by
  rw [block016_data_flat058_step]
def block016_data_flat059 : CoefficientMerge.Poly := [(nat_lit 1918, Int.ofNat (nat_lit 310893339187200))]
theorem block016_data_flat059_step : block016_data_flat059 = (CoefficientMerge.scale (310893339187200 : Int) atom1120Coded) := by decide +kernel
theorem block016_data_flat059_original : block016_data_flat059 = (CoefficientMerge.scale (310893339187200 : Int) atom1120Coded) := by
  rw [block016_data_flat059_step]
def block016_data_flat060 : CoefficientMerge.Poly := [(nat_lit 1917, Int.ofNat (nat_lit 262197835468800)), (nat_lit 1918, Int.ofNat (nat_lit 310893339187200))]
theorem block016_data_flat060_step : block016_data_flat060 = (CoefficientMerge.fastMerge block016_data_flat058 block016_data_flat059) := by decide +kernel
theorem block016_data_flat060_original : block016_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (262197835468800 : Int) atom1119Coded) (CoefficientMerge.scale (310893339187200 : Int) atom1120Coded)) := by
  rw [block016_data_flat060_step, block016_data_flat058_original, block016_data_flat059_original]
def block016_data_flat061 : CoefficientMerge.Poly := [(nat_lit 1919, Int.ofNat (nat_lit 359588842905600))]
theorem block016_data_flat061_step : block016_data_flat061 = (CoefficientMerge.scale (359588842905600 : Int) atom1121Coded) := by decide +kernel
theorem block016_data_flat061_original : block016_data_flat061 = (CoefficientMerge.scale (359588842905600 : Int) atom1121Coded) := by
  rw [block016_data_flat061_step]
def block016_data_flat062 : CoefficientMerge.Poly := [(nat_lit 1928, Int.ofNat (nat_lit 101123730892800))]
theorem block016_data_flat062_step : block016_data_flat062 = (CoefficientMerge.scale (101123730892800 : Int) atom1122Coded) := by decide +kernel
theorem block016_data_flat062_original : block016_data_flat062 = (CoefficientMerge.scale (101123730892800 : Int) atom1122Coded) := by
  rw [block016_data_flat062_step]
def block016_data_flat063 : CoefficientMerge.Poly := [(nat_lit 1929, Int.ofNat (nat_lit 189544167714528))]
theorem block016_data_flat063_step : block016_data_flat063 = (CoefficientMerge.scale (189544167714528 : Int) atom1123Coded) := by decide +kernel
theorem block016_data_flat063_original : block016_data_flat063 = (CoefficientMerge.scale (189544167714528 : Int) atom1123Coded) := by
  rw [block016_data_flat063_step]
def block016_data_flat064 : CoefficientMerge.Poly := [(nat_lit 1928, Int.ofNat (nat_lit 101123730892800)), (nat_lit 1929, Int.ofNat (nat_lit 189544167714528))]
theorem block016_data_flat064_step : block016_data_flat064 = (CoefficientMerge.fastMerge block016_data_flat062 block016_data_flat063) := by decide +kernel
theorem block016_data_flat064_original : block016_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (101123730892800 : Int) atom1122Coded) (CoefficientMerge.scale (189544167714528 : Int) atom1123Coded)) := by
  rw [block016_data_flat064_step, block016_data_flat062_original, block016_data_flat063_original]
def block016_data_flat065 : CoefficientMerge.Poly := [(nat_lit 1919, Int.ofNat (nat_lit 359588842905600)), (nat_lit 1928, Int.ofNat (nat_lit 101123730892800)), (nat_lit 1929, Int.ofNat (nat_lit 189544167714528))]
theorem block016_data_flat065_step : block016_data_flat065 = (CoefficientMerge.fastMerge block016_data_flat061 block016_data_flat064) := by decide +kernel
theorem block016_data_flat065_original : block016_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (359588842905600 : Int) atom1121Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101123730892800 : Int) atom1122Coded) (CoefficientMerge.scale (189544167714528 : Int) atom1123Coded))) := by
  rw [block016_data_flat065_step, block016_data_flat061_original, block016_data_flat064_original]
def block016_data_flat066 : CoefficientMerge.Poly := [(nat_lit 1917, Int.ofNat (nat_lit 262197835468800)), (nat_lit 1918, Int.ofNat (nat_lit 310893339187200)), (nat_lit 1919, Int.ofNat (nat_lit 359588842905600)), (nat_lit 1928, Int.ofNat (nat_lit 101123730892800)), (nat_lit 1929, Int.ofNat (nat_lit 189544167714528))]
theorem block016_data_flat066_step : block016_data_flat066 = (CoefficientMerge.fastMerge block016_data_flat060 block016_data_flat065) := by decide +kernel
theorem block016_data_flat066_original : block016_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (262197835468800 : Int) atom1119Coded) (CoefficientMerge.scale (310893339187200 : Int) atom1120Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (359588842905600 : Int) atom1121Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101123730892800 : Int) atom1122Coded) (CoefficientMerge.scale (189544167714528 : Int) atom1123Coded)))) := by
  rw [block016_data_flat066_step, block016_data_flat060_original, block016_data_flat065_original]
def block016_data_flat067 : CoefficientMerge.Poly := [(nat_lit 1930, Int.ofNat (nat_lit 178502897027664))]
theorem block016_data_flat067_step : block016_data_flat067 = (CoefficientMerge.scale (178502897027664 : Int) atom1124Coded) := by decide +kernel
theorem block016_data_flat067_original : block016_data_flat067 = (CoefficientMerge.scale (178502897027664 : Int) atom1124Coded) := by
  rw [block016_data_flat067_step]
def block016_data_flat068 : CoefficientMerge.Poly := [(nat_lit 1931, Int.ofNat (nat_lit 194088787209504))]
theorem block016_data_flat068_step : block016_data_flat068 = (CoefficientMerge.scale (194088787209504 : Int) atom1125Coded) := by decide +kernel
theorem block016_data_flat068_original : block016_data_flat068 = (CoefficientMerge.scale (194088787209504 : Int) atom1125Coded) := by
  rw [block016_data_flat068_step]
def block016_data_flat069 : CoefficientMerge.Poly := [(nat_lit 1930, Int.ofNat (nat_lit 178502897027664)), (nat_lit 1931, Int.ofNat (nat_lit 194088787209504))]
theorem block016_data_flat069_step : block016_data_flat069 = (CoefficientMerge.fastMerge block016_data_flat067 block016_data_flat068) := by decide +kernel
theorem block016_data_flat069_original : block016_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (178502897027664 : Int) atom1124Coded) (CoefficientMerge.scale (194088787209504 : Int) atom1125Coded)) := by
  rw [block016_data_flat069_step, block016_data_flat067_original, block016_data_flat068_original]
def block016_data_flat070 : CoefficientMerge.Poly := [(nat_lit 1932, Int.ofNat (nat_lit 217928398463424))]
theorem block016_data_flat070_step : block016_data_flat070 = (CoefficientMerge.scale (217928398463424 : Int) atom1126Coded) := by decide +kernel
theorem block016_data_flat070_original : block016_data_flat070 = (CoefficientMerge.scale (217928398463424 : Int) atom1126Coded) := by
  rw [block016_data_flat070_step]
def block016_data_flat071 : CoefficientMerge.Poly := [(nat_lit 1933, Int.ofNat (nat_lit 208267937539200))]
theorem block016_data_flat071_step : block016_data_flat071 = (CoefficientMerge.scale (208267937539200 : Int) atom1127Coded) := by decide +kernel
theorem block016_data_flat071_original : block016_data_flat071 = (CoefficientMerge.scale (208267937539200 : Int) atom1127Coded) := by
  rw [block016_data_flat071_step]
def block016_data_flat072 : CoefficientMerge.Poly := [(nat_lit 1934, Int.ofNat (nat_lit 194933213798400))]
theorem block016_data_flat072_step : block016_data_flat072 = (CoefficientMerge.scale (194933213798400 : Int) atom1128Coded) := by decide +kernel
theorem block016_data_flat072_original : block016_data_flat072 = (CoefficientMerge.scale (194933213798400 : Int) atom1128Coded) := by
  rw [block016_data_flat072_step]
def block016_data_flat073 : CoefficientMerge.Poly := [(nat_lit 1933, Int.ofNat (nat_lit 208267937539200)), (nat_lit 1934, Int.ofNat (nat_lit 194933213798400))]
theorem block016_data_flat073_step : block016_data_flat073 = (CoefficientMerge.fastMerge block016_data_flat071 block016_data_flat072) := by decide +kernel
theorem block016_data_flat073_original : block016_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (208267937539200 : Int) atom1127Coded) (CoefficientMerge.scale (194933213798400 : Int) atom1128Coded)) := by
  rw [block016_data_flat073_step, block016_data_flat071_original, block016_data_flat072_original]
def block016_data_flat074 : CoefficientMerge.Poly := [(nat_lit 1932, Int.ofNat (nat_lit 217928398463424)), (nat_lit 1933, Int.ofNat (nat_lit 208267937539200)), (nat_lit 1934, Int.ofNat (nat_lit 194933213798400))]
theorem block016_data_flat074_step : block016_data_flat074 = (CoefficientMerge.fastMerge block016_data_flat070 block016_data_flat073) := by decide +kernel
theorem block016_data_flat074_original : block016_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (217928398463424 : Int) atom1126Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (208267937539200 : Int) atom1127Coded) (CoefficientMerge.scale (194933213798400 : Int) atom1128Coded))) := by
  rw [block016_data_flat074_step, block016_data_flat070_original, block016_data_flat073_original]
def block016_data_flat075 : CoefficientMerge.Poly := [(nat_lit 1930, Int.ofNat (nat_lit 178502897027664)), (nat_lit 1931, Int.ofNat (nat_lit 194088787209504)), (nat_lit 1932, Int.ofNat (nat_lit 217928398463424)), (nat_lit 1933, Int.ofNat (nat_lit 208267937539200)), (nat_lit 1934, Int.ofNat (nat_lit 194933213798400))]
theorem block016_data_flat075_step : block016_data_flat075 = (CoefficientMerge.fastMerge block016_data_flat069 block016_data_flat074) := by decide +kernel
theorem block016_data_flat075_original : block016_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (178502897027664 : Int) atom1124Coded) (CoefficientMerge.scale (194088787209504 : Int) atom1125Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (217928398463424 : Int) atom1126Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (208267937539200 : Int) atom1127Coded) (CoefficientMerge.scale (194933213798400 : Int) atom1128Coded)))) := by
  rw [block016_data_flat075_step, block016_data_flat069_original, block016_data_flat074_original]
def block016_data_flat076 : CoefficientMerge.Poly := [(nat_lit 1917, Int.ofNat (nat_lit 262197835468800)), (nat_lit 1918, Int.ofNat (nat_lit 310893339187200)), (nat_lit 1919, Int.ofNat (nat_lit 359588842905600)), (nat_lit 1928, Int.ofNat (nat_lit 101123730892800)), (nat_lit 1929, Int.ofNat (nat_lit 189544167714528)), (nat_lit 1930, Int.ofNat (nat_lit 178502897027664)), (nat_lit 1931, Int.ofNat (nat_lit 194088787209504)), (nat_lit 1932, Int.ofNat (nat_lit 217928398463424)), (nat_lit 1933, Int.ofNat (nat_lit 208267937539200)), (nat_lit 1934, Int.ofNat (nat_lit 194933213798400))]
theorem block016_data_flat076_step : block016_data_flat076 = (CoefficientMerge.fastMerge block016_data_flat066 block016_data_flat075) := by decide +kernel
theorem block016_data_flat076_original : block016_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (262197835468800 : Int) atom1119Coded) (CoefficientMerge.scale (310893339187200 : Int) atom1120Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (359588842905600 : Int) atom1121Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101123730892800 : Int) atom1122Coded) (CoefficientMerge.scale (189544167714528 : Int) atom1123Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (178502897027664 : Int) atom1124Coded) (CoefficientMerge.scale (194088787209504 : Int) atom1125Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (217928398463424 : Int) atom1126Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (208267937539200 : Int) atom1127Coded) (CoefficientMerge.scale (194933213798400 : Int) atom1128Coded))))) := by
  rw [block016_data_flat076_step, block016_data_flat066_original, block016_data_flat075_original]
def block016_data_flat077 : CoefficientMerge.Poly := [(nat_lit 1907, Int.ofNat (nat_lit 165949249814304)), (nat_lit 1908, Int.ofNat (nat_lit 193871232037824)), (nat_lit 1909, Int.ofNat (nat_lit 185210101507200)), (nat_lit 1910, Int.ofNat (nat_lit 172874708160000)), (nat_lit 1911, Int.ofNat (nat_lit 175326321408000)), (nat_lit 1912, Int.ofNat (nat_lit 165955424409600)), (nat_lit 1913, Int.ofNat (nat_lit 166517265868800)), (nat_lit 1914, Int.ofNat (nat_lit 207331525632000)), (nat_lit 1915, Int.ofNat (nat_lit 186050276966400)), (nat_lit 1916, Int.ofNat (nat_lit 249818423500800)), (nat_lit 1917, Int.ofNat (nat_lit 262197835468800)), (nat_lit 1918, Int.ofNat (nat_lit 310893339187200)), (nat_lit 1919, Int.ofNat (nat_lit 359588842905600)), (nat_lit 1928, Int.ofNat (nat_lit 101123730892800)), (nat_lit 1929, Int.ofNat (nat_lit 189544167714528)), (nat_lit 1930, Int.ofNat (nat_lit 178502897027664)), (nat_lit 1931, Int.ofNat (nat_lit 194088787209504)), (nat_lit 1932, Int.ofNat (nat_lit 217928398463424)), (nat_lit 1933, Int.ofNat (nat_lit 208267937539200)), (nat_lit 1934, Int.ofNat (nat_lit 194933213798400))]
theorem block016_data_flat077_step : block016_data_flat077 = (CoefficientMerge.fastMerge block016_data_flat057 block016_data_flat076) := by decide +kernel
theorem block016_data_flat077_original : block016_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (165949249814304 : Int) atom1109Coded) (CoefficientMerge.scale (193871232037824 : Int) atom1110Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (185210101507200 : Int) atom1111Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172874708160000 : Int) atom1112Coded) (CoefficientMerge.scale (175326321408000 : Int) atom1113Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (165955424409600 : Int) atom1114Coded) (CoefficientMerge.scale (166517265868800 : Int) atom1115Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207331525632000 : Int) atom1116Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (186050276966400 : Int) atom1117Coded) (CoefficientMerge.scale (249818423500800 : Int) atom1118Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (262197835468800 : Int) atom1119Coded) (CoefficientMerge.scale (310893339187200 : Int) atom1120Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (359588842905600 : Int) atom1121Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101123730892800 : Int) atom1122Coded) (CoefficientMerge.scale (189544167714528 : Int) atom1123Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (178502897027664 : Int) atom1124Coded) (CoefficientMerge.scale (194088787209504 : Int) atom1125Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (217928398463424 : Int) atom1126Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (208267937539200 : Int) atom1127Coded) (CoefficientMerge.scale (194933213798400 : Int) atom1128Coded)))))) := by
  rw [block016_data_flat077_step, block016_data_flat057_original, block016_data_flat076_original]
def block016_data_flat078 : CoefficientMerge.Poly := [(nat_lit 1880, Int.ofNat (nat_lit 101846650752000)), (nat_lit 1881, Int.ofNat (nat_lit 105562098127728)), (nat_lit 1882, Int.ofNat (nat_lit 125826931427472)), (nat_lit 1883, Int.ofNat (nat_lit 136085099683104)), (nat_lit 1884, Int.ofNat (nat_lit 161923371724224)), (nat_lit 1885, Int.ofNat (nat_lit 153240978844800)), (nat_lit 1886, Int.ofNat (nat_lit 140884323148800)), (nat_lit 1887, Int.ofNat (nat_lit 143314674048000)), (nat_lit 1888, Int.ofNat (nat_lit 133922514700800)), (nat_lit 1889, Int.ofNat (nat_lit 134463093811200)), (nat_lit 1890, Int.ofNat (nat_lit 172926682790400)), (nat_lit 1891, Int.ofNat (nat_lit 146965354905600)), (nat_lit 1892, Int.ofNat (nat_lit 206053422220800)), (nat_lit 1893, Int.ofNat (nat_lit 209093938099200)), (nat_lit 1894, Int.ofNat (nat_lit 248450545728000)), (nat_lit 1895, Int.ofNat (nat_lit 287807153356800)), (nat_lit 1903, Int.ofNat (nat_lit 81912017510400)), (nat_lit 1904, Int.ofNat (nat_lit 148101709324800)), (nat_lit 1905, Int.ofNat (nat_lit 135383723561328)), (nat_lit 1906, Int.ofNat (nat_lit 153607371376272)), (nat_lit 1907, Int.ofNat (nat_lit 165949249814304)), (nat_lit 1908, Int.ofNat (nat_lit 193871232037824)), (nat_lit 1909, Int.ofNat (nat_lit 185210101507200)), (nat_lit 1910, Int.ofNat (nat_lit 172874708160000)), (nat_lit 1911, Int.ofNat (nat_lit 175326321408000)), (nat_lit 1912, Int.ofNat (nat_lit 165955424409600)), (nat_lit 1913, Int.ofNat (nat_lit 166517265868800)), (nat_lit 1914, Int.ofNat (nat_lit 207331525632000)), (nat_lit 1915, Int.ofNat (nat_lit 186050276966400)), (nat_lit 1916, Int.ofNat (nat_lit 249818423500800)), (nat_lit 1917, Int.ofNat (nat_lit 262197835468800)), (nat_lit 1918, Int.ofNat (nat_lit 310893339187200)), (nat_lit 1919, Int.ofNat (nat_lit 359588842905600)), (nat_lit 1928, Int.ofNat (nat_lit 101123730892800)), (nat_lit 1929, Int.ofNat (nat_lit 189544167714528)), (nat_lit 1930, Int.ofNat (nat_lit 178502897027664)), (nat_lit 1931, Int.ofNat (nat_lit 194088787209504)), (nat_lit 1932, Int.ofNat (nat_lit 217928398463424)), (nat_lit 1933, Int.ofNat (nat_lit 208267937539200)), (nat_lit 1934, Int.ofNat (nat_lit 194933213798400))]
theorem block016_data_flat078_step : block016_data_flat078 = (CoefficientMerge.fastMerge block016_data_flat038 block016_data_flat077) := by decide +kernel
theorem block016_data_flat078_original : block016_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (101846650752000 : Int) atom1089Coded) (CoefficientMerge.scale (105562098127728 : Int) atom1090Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125826931427472 : Int) atom1091Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136085099683104 : Int) atom1092Coded) (CoefficientMerge.scale (161923371724224 : Int) atom1093Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153240978844800 : Int) atom1094Coded) (CoefficientMerge.scale (140884323148800 : Int) atom1095Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (143314674048000 : Int) atom1096Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (133922514700800 : Int) atom1097Coded) (CoefficientMerge.scale (134463093811200 : Int) atom1098Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (172926682790400 : Int) atom1099Coded) (CoefficientMerge.scale (146965354905600 : Int) atom1100Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (206053422220800 : Int) atom1101Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (209093938099200 : Int) atom1102Coded) (CoefficientMerge.scale (248450545728000 : Int) atom1103Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (287807153356800 : Int) atom1104Coded) (CoefficientMerge.scale (81912017510400 : Int) atom1105Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (148101709324800 : Int) atom1106Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135383723561328 : Int) atom1107Coded) (CoefficientMerge.scale (153607371376272 : Int) atom1108Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (165949249814304 : Int) atom1109Coded) (CoefficientMerge.scale (193871232037824 : Int) atom1110Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (185210101507200 : Int) atom1111Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172874708160000 : Int) atom1112Coded) (CoefficientMerge.scale (175326321408000 : Int) atom1113Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (165955424409600 : Int) atom1114Coded) (CoefficientMerge.scale (166517265868800 : Int) atom1115Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207331525632000 : Int) atom1116Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (186050276966400 : Int) atom1117Coded) (CoefficientMerge.scale (249818423500800 : Int) atom1118Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (262197835468800 : Int) atom1119Coded) (CoefficientMerge.scale (310893339187200 : Int) atom1120Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (359588842905600 : Int) atom1121Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101123730892800 : Int) atom1122Coded) (CoefficientMerge.scale (189544167714528 : Int) atom1123Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (178502897027664 : Int) atom1124Coded) (CoefficientMerge.scale (194088787209504 : Int) atom1125Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (217928398463424 : Int) atom1126Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (208267937539200 : Int) atom1127Coded) (CoefficientMerge.scale (194933213798400 : Int) atom1128Coded))))))) := by
  rw [block016_data_flat078_step, block016_data_flat038_original, block016_data_flat077_original]
def block016_data_flat079 : CoefficientMerge.Poly := [(nat_lit 1935, Int.ofNat (nat_lit 196385496652800))]
theorem block016_data_flat079_step : block016_data_flat079 = (CoefficientMerge.scale (196385496652800 : Int) atom1129Coded) := by decide +kernel
theorem block016_data_flat079_original : block016_data_flat079 = (CoefficientMerge.scale (196385496652800 : Int) atom1129Coded) := by
  rw [block016_data_flat079_step]
def block016_data_flat080 : CoefficientMerge.Poly := [(nat_lit 1936, Int.ofNat (nat_lit 186015269260800))]
theorem block016_data_flat080_step : block016_data_flat080 = (CoefficientMerge.scale (186015269260800 : Int) atom1130Coded) := by decide +kernel
theorem block016_data_flat080_original : block016_data_flat080 = (CoefficientMerge.scale (186015269260800 : Int) atom1130Coded) := by
  rw [block016_data_flat080_step]
def block016_data_flat081 : CoefficientMerge.Poly := [(nat_lit 1935, Int.ofNat (nat_lit 196385496652800)), (nat_lit 1936, Int.ofNat (nat_lit 186015269260800))]
theorem block016_data_flat081_step : block016_data_flat081 = (CoefficientMerge.fastMerge block016_data_flat079 block016_data_flat080) := by decide +kernel
theorem block016_data_flat081_original : block016_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (196385496652800 : Int) atom1129Coded) (CoefficientMerge.scale (186015269260800 : Int) atom1130Coded)) := by
  rw [block016_data_flat081_step, block016_data_flat079_original, block016_data_flat080_original]
def block016_data_flat082 : CoefficientMerge.Poly := [(nat_lit 1937, Int.ofNat (nat_lit 185577780326400))]
theorem block016_data_flat082_step : block016_data_flat082 = (CoefficientMerge.scale (185577780326400 : Int) atom1131Coded) := by decide +kernel
theorem block016_data_flat082_original : block016_data_flat082 = (CoefficientMerge.scale (185577780326400 : Int) atom1131Coded) := by
  rw [block016_data_flat082_step]
def block016_data_flat083 : CoefficientMerge.Poly := [(nat_lit 1938, Int.ofNat (nat_lit 228846660134400))]
theorem block016_data_flat083_step : block016_data_flat083 = (CoefficientMerge.scale (228846660134400 : Int) atom1132Coded) := by decide +kernel
theorem block016_data_flat083_original : block016_data_flat083 = (CoefficientMerge.scale (228846660134400 : Int) atom1132Coded) := by
  rw [block016_data_flat083_step]
def block016_data_flat084 : CoefficientMerge.Poly := [(nat_lit 1939, Int.ofNat (nat_lit 213473981952000))]
theorem block016_data_flat084_step : block016_data_flat084 = (CoefficientMerge.scale (213473981952000 : Int) atom1133Coded) := by decide +kernel
theorem block016_data_flat084_original : block016_data_flat084 = (CoefficientMerge.scale (213473981952000 : Int) atom1133Coded) := by
  rw [block016_data_flat084_step]
def block016_data_flat085 : CoefficientMerge.Poly := [(nat_lit 1938, Int.ofNat (nat_lit 228846660134400)), (nat_lit 1939, Int.ofNat (nat_lit 213473981952000))]
theorem block016_data_flat085_step : block016_data_flat085 = (CoefficientMerge.fastMerge block016_data_flat083 block016_data_flat084) := by decide +kernel
theorem block016_data_flat085_original : block016_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (228846660134400 : Int) atom1132Coded) (CoefficientMerge.scale (213473981952000 : Int) atom1133Coded)) := by
  rw [block016_data_flat085_step, block016_data_flat083_original, block016_data_flat084_original]
def block016_data_flat086 : CoefficientMerge.Poly := [(nat_lit 1937, Int.ofNat (nat_lit 185577780326400)), (nat_lit 1938, Int.ofNat (nat_lit 228846660134400)), (nat_lit 1939, Int.ofNat (nat_lit 213473981952000))]
theorem block016_data_flat086_step : block016_data_flat086 = (CoefficientMerge.fastMerge block016_data_flat082 block016_data_flat085) := by decide +kernel
theorem block016_data_flat086_original : block016_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (185577780326400 : Int) atom1131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (228846660134400 : Int) atom1132Coded) (CoefficientMerge.scale (213473981952000 : Int) atom1133Coded))) := by
  rw [block016_data_flat086_step, block016_data_flat082_original, block016_data_flat085_original]
def block016_data_flat087 : CoefficientMerge.Poly := [(nat_lit 1935, Int.ofNat (nat_lit 196385496652800)), (nat_lit 1936, Int.ofNat (nat_lit 186015269260800)), (nat_lit 1937, Int.ofNat (nat_lit 185577780326400)), (nat_lit 1938, Int.ofNat (nat_lit 228846660134400)), (nat_lit 1939, Int.ofNat (nat_lit 213473981952000))]
theorem block016_data_flat087_step : block016_data_flat087 = (CoefficientMerge.fastMerge block016_data_flat081 block016_data_flat086) := by decide +kernel
theorem block016_data_flat087_original : block016_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (196385496652800 : Int) atom1129Coded) (CoefficientMerge.scale (186015269260800 : Int) atom1130Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (185577780326400 : Int) atom1131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (228846660134400 : Int) atom1132Coded) (CoefficientMerge.scale (213473981952000 : Int) atom1133Coded)))) := by
  rw [block016_data_flat087_step, block016_data_flat081_original, block016_data_flat086_original]
def block016_data_flat088 : CoefficientMerge.Poly := [(nat_lit 1940, Int.ofNat (nat_lit 283150698969600))]
theorem block016_data_flat088_step : block016_data_flat088 = (CoefficientMerge.scale (283150698969600 : Int) atom1134Coded) := by decide +kernel
theorem block016_data_flat088_original : block016_data_flat088 = (CoefficientMerge.scale (283150698969600 : Int) atom1134Coded) := by
  rw [block016_data_flat088_step]
def block016_data_flat089 : CoefficientMerge.Poly := [(nat_lit 1941, Int.ofNat (nat_lit 308346582297600))]
theorem block016_data_flat089_step : block016_data_flat089 = (CoefficientMerge.scale (308346582297600 : Int) atom1135Coded) := by decide +kernel
theorem block016_data_flat089_original : block016_data_flat089 = (CoefficientMerge.scale (308346582297600 : Int) atom1135Coded) := by
  rw [block016_data_flat089_step]
def block016_data_flat090 : CoefficientMerge.Poly := [(nat_lit 1940, Int.ofNat (nat_lit 283150698969600)), (nat_lit 1941, Int.ofNat (nat_lit 308346582297600))]
theorem block016_data_flat090_step : block016_data_flat090 = (CoefficientMerge.fastMerge block016_data_flat088 block016_data_flat089) := by decide +kernel
theorem block016_data_flat090_original : block016_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (283150698969600 : Int) atom1134Coded) (CoefficientMerge.scale (308346582297600 : Int) atom1135Coded)) := by
  rw [block016_data_flat090_step, block016_data_flat088_original, block016_data_flat089_original]
def block016_data_flat091 : CoefficientMerge.Poly := [(nat_lit 1942, Int.ofNat (nat_lit 369858557376000))]
theorem block016_data_flat091_step : block016_data_flat091 = (CoefficientMerge.scale (369858557376000 : Int) atom1136Coded) := by decide +kernel
theorem block016_data_flat091_original : block016_data_flat091 = (CoefficientMerge.scale (369858557376000 : Int) atom1136Coded) := by
  rw [block016_data_flat091_step]
def block016_data_flat092 : CoefficientMerge.Poly := [(nat_lit 1943, Int.ofNat (nat_lit 431370532454400))]
theorem block016_data_flat092_step : block016_data_flat092 = (CoefficientMerge.scale (431370532454400 : Int) atom1137Coded) := by decide +kernel
theorem block016_data_flat092_original : block016_data_flat092 = (CoefficientMerge.scale (431370532454400 : Int) atom1137Coded) := by
  rw [block016_data_flat092_step]
def block016_data_flat093 : CoefficientMerge.Poly := [(nat_lit 1953, Int.ofNat (nat_lit 126437516476128))]
theorem block016_data_flat093_step : block016_data_flat093 = (CoefficientMerge.scale (126437516476128 : Int) atom1138Coded) := by decide +kernel
theorem block016_data_flat093_original : block016_data_flat093 = (CoefficientMerge.scale (126437516476128 : Int) atom1138Coded) := by
  rw [block016_data_flat093_step]
def block016_data_flat094 : CoefficientMerge.Poly := [(nat_lit 1943, Int.ofNat (nat_lit 431370532454400)), (nat_lit 1953, Int.ofNat (nat_lit 126437516476128))]
theorem block016_data_flat094_step : block016_data_flat094 = (CoefficientMerge.fastMerge block016_data_flat092 block016_data_flat093) := by decide +kernel
theorem block016_data_flat094_original : block016_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (431370532454400 : Int) atom1137Coded) (CoefficientMerge.scale (126437516476128 : Int) atom1138Coded)) := by
  rw [block016_data_flat094_step, block016_data_flat092_original, block016_data_flat093_original]
def block016_data_flat095 : CoefficientMerge.Poly := [(nat_lit 1942, Int.ofNat (nat_lit 369858557376000)), (nat_lit 1943, Int.ofNat (nat_lit 431370532454400)), (nat_lit 1953, Int.ofNat (nat_lit 126437516476128))]
theorem block016_data_flat095_step : block016_data_flat095 = (CoefficientMerge.fastMerge block016_data_flat091 block016_data_flat094) := by decide +kernel
theorem block016_data_flat095_original : block016_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (369858557376000 : Int) atom1136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (431370532454400 : Int) atom1137Coded) (CoefficientMerge.scale (126437516476128 : Int) atom1138Coded))) := by
  rw [block016_data_flat095_step, block016_data_flat091_original, block016_data_flat094_original]
def block016_data_flat096 : CoefficientMerge.Poly := [(nat_lit 1940, Int.ofNat (nat_lit 283150698969600)), (nat_lit 1941, Int.ofNat (nat_lit 308346582297600)), (nat_lit 1942, Int.ofNat (nat_lit 369858557376000)), (nat_lit 1943, Int.ofNat (nat_lit 431370532454400)), (nat_lit 1953, Int.ofNat (nat_lit 126437516476128))]
theorem block016_data_flat096_step : block016_data_flat096 = (CoefficientMerge.fastMerge block016_data_flat090 block016_data_flat095) := by decide +kernel
theorem block016_data_flat096_original : block016_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (283150698969600 : Int) atom1134Coded) (CoefficientMerge.scale (308346582297600 : Int) atom1135Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (369858557376000 : Int) atom1136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (431370532454400 : Int) atom1137Coded) (CoefficientMerge.scale (126437516476128 : Int) atom1138Coded)))) := by
  rw [block016_data_flat096_step, block016_data_flat090_original, block016_data_flat095_original]
def block016_data_flat097 : CoefficientMerge.Poly := [(nat_lit 1935, Int.ofNat (nat_lit 196385496652800)), (nat_lit 1936, Int.ofNat (nat_lit 186015269260800)), (nat_lit 1937, Int.ofNat (nat_lit 185577780326400)), (nat_lit 1938, Int.ofNat (nat_lit 228846660134400)), (nat_lit 1939, Int.ofNat (nat_lit 213473981952000)), (nat_lit 1940, Int.ofNat (nat_lit 283150698969600)), (nat_lit 1941, Int.ofNat (nat_lit 308346582297600)), (nat_lit 1942, Int.ofNat (nat_lit 369858557376000)), (nat_lit 1943, Int.ofNat (nat_lit 431370532454400)), (nat_lit 1953, Int.ofNat (nat_lit 126437516476128))]
theorem block016_data_flat097_step : block016_data_flat097 = (CoefficientMerge.fastMerge block016_data_flat087 block016_data_flat096) := by decide +kernel
theorem block016_data_flat097_original : block016_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (196385496652800 : Int) atom1129Coded) (CoefficientMerge.scale (186015269260800 : Int) atom1130Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (185577780326400 : Int) atom1131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (228846660134400 : Int) atom1132Coded) (CoefficientMerge.scale (213473981952000 : Int) atom1133Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (283150698969600 : Int) atom1134Coded) (CoefficientMerge.scale (308346582297600 : Int) atom1135Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (369858557376000 : Int) atom1136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (431370532454400 : Int) atom1137Coded) (CoefficientMerge.scale (126437516476128 : Int) atom1138Coded))))) := by
  rw [block016_data_flat097_step, block016_data_flat087_original, block016_data_flat096_original]
def block016_data_flat098 : CoefficientMerge.Poly := [(nat_lit 1954, Int.ofNat (nat_lit 239751911272896))]
theorem block016_data_flat098_step : block016_data_flat098 = (CoefficientMerge.scale (239751911272896 : Int) atom1139Coded) := by decide +kernel
theorem block016_data_flat098_original : block016_data_flat098 = (CoefficientMerge.scale (239751911272896 : Int) atom1139Coded) := by
  rw [block016_data_flat098_step]
def block016_data_flat099 : CoefficientMerge.Poly := [(nat_lit 1955, Int.ofNat (nat_lit 231275379769632))]
theorem block016_data_flat099_step : block016_data_flat099 = (CoefficientMerge.scale (231275379769632 : Int) atom1140Coded) := by decide +kernel
theorem block016_data_flat099_original : block016_data_flat099 = (CoefficientMerge.scale (231275379769632 : Int) atom1140Coded) := by
  rw [block016_data_flat099_step]
def block016_data_flat100 : CoefficientMerge.Poly := [(nat_lit 1954, Int.ofNat (nat_lit 239751911272896)), (nat_lit 1955, Int.ofNat (nat_lit 231275379769632))]
theorem block016_data_flat100_step : block016_data_flat100 = (CoefficientMerge.fastMerge block016_data_flat098 block016_data_flat099) := by decide +kernel
theorem block016_data_flat100_original : block016_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (239751911272896 : Int) atom1139Coded) (CoefficientMerge.scale (231275379769632 : Int) atom1140Coded)) := by
  rw [block016_data_flat100_step, block016_data_flat098_original, block016_data_flat099_original]
def block016_data_flat101 : CoefficientMerge.Poly := [(nat_lit 1956, Int.ofNat (nat_lit 256178108463552))]
theorem block016_data_flat101_step : block016_data_flat101 = (CoefficientMerge.scale (256178108463552 : Int) atom1141Coded) := by decide +kernel
theorem block016_data_flat101_original : block016_data_flat101 = (CoefficientMerge.scale (256178108463552 : Int) atom1141Coded) := by
  rw [block016_data_flat101_step]
def block016_data_flat102 : CoefficientMerge.Poly := [(nat_lit 1957, Int.ofNat (nat_lit 241414683827328))]
theorem block016_data_flat102_step : block016_data_flat102 = (CoefficientMerge.scale (241414683827328 : Int) atom1142Coded) := by decide +kernel
theorem block016_data_flat102_original : block016_data_flat102 = (CoefficientMerge.scale (241414683827328 : Int) atom1142Coded) := by
  rw [block016_data_flat102_step]
def block016_data_flat103 : CoefficientMerge.Poly := [(nat_lit 1958, Int.ofNat (nat_lit 226060036950528))]
theorem block016_data_flat103_step : block016_data_flat103 = (CoefficientMerge.scale (226060036950528 : Int) atom1143Coded) := by decide +kernel
theorem block016_data_flat103_original : block016_data_flat103 = (CoefficientMerge.scale (226060036950528 : Int) atom1143Coded) := by
  rw [block016_data_flat103_step]
def block016_data_flat104 : CoefficientMerge.Poly := [(nat_lit 1957, Int.ofNat (nat_lit 241414683827328)), (nat_lit 1958, Int.ofNat (nat_lit 226060036950528))]
theorem block016_data_flat104_step : block016_data_flat104 = (CoefficientMerge.fastMerge block016_data_flat102 block016_data_flat103) := by decide +kernel
theorem block016_data_flat104_original : block016_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (241414683827328 : Int) atom1142Coded) (CoefficientMerge.scale (226060036950528 : Int) atom1143Coded)) := by
  rw [block016_data_flat104_step, block016_data_flat102_original, block016_data_flat103_original]
def block016_data_flat105 : CoefficientMerge.Poly := [(nat_lit 1956, Int.ofNat (nat_lit 256178108463552)), (nat_lit 1957, Int.ofNat (nat_lit 241414683827328)), (nat_lit 1958, Int.ofNat (nat_lit 226060036950528))]
theorem block016_data_flat105_step : block016_data_flat105 = (CoefficientMerge.fastMerge block016_data_flat101 block016_data_flat104) := by decide +kernel
theorem block016_data_flat105_original : block016_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (256178108463552 : Int) atom1141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241414683827328 : Int) atom1142Coded) (CoefficientMerge.scale (226060036950528 : Int) atom1143Coded))) := by
  rw [block016_data_flat105_step, block016_data_flat101_original, block016_data_flat104_original]
def block016_data_flat106 : CoefficientMerge.Poly := [(nat_lit 1954, Int.ofNat (nat_lit 239751911272896)), (nat_lit 1955, Int.ofNat (nat_lit 231275379769632)), (nat_lit 1956, Int.ofNat (nat_lit 256178108463552)), (nat_lit 1957, Int.ofNat (nat_lit 241414683827328)), (nat_lit 1958, Int.ofNat (nat_lit 226060036950528))]
theorem block016_data_flat106_step : block016_data_flat106 = (CoefficientMerge.fastMerge block016_data_flat100 block016_data_flat105) := by decide +kernel
theorem block016_data_flat106_original : block016_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (239751911272896 : Int) atom1139Coded) (CoefficientMerge.scale (231275379769632 : Int) atom1140Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256178108463552 : Int) atom1141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241414683827328 : Int) atom1142Coded) (CoefficientMerge.scale (226060036950528 : Int) atom1143Coded)))) := by
  rw [block016_data_flat106_step, block016_data_flat100_original, block016_data_flat105_original]
def block016_data_flat107 : CoefficientMerge.Poly := [(nat_lit 1959, Int.ofNat (nat_lit 225492396668928))]
theorem block016_data_flat107_step : block016_data_flat107 = (CoefficientMerge.scale (225492396668928 : Int) atom1144Coded) := by decide +kernel
theorem block016_data_flat107_original : block016_data_flat107 = (CoefficientMerge.scale (225492396668928 : Int) atom1144Coded) := by
  rw [block016_data_flat107_step]
def block016_data_flat108 : CoefficientMerge.Poly := [(nat_lit 1960, Int.ofNat (nat_lit 213102246140928))]
theorem block016_data_flat108_step : block016_data_flat108 = (CoefficientMerge.scale (213102246140928 : Int) atom1145Coded) := by decide +kernel
theorem block016_data_flat108_original : block016_data_flat108 = (CoefficientMerge.scale (213102246140928 : Int) atom1145Coded) := by
  rw [block016_data_flat108_step]
def block016_data_flat109 : CoefficientMerge.Poly := [(nat_lit 1959, Int.ofNat (nat_lit 225492396668928)), (nat_lit 1960, Int.ofNat (nat_lit 213102246140928))]
theorem block016_data_flat109_step : block016_data_flat109 = (CoefficientMerge.fastMerge block016_data_flat107 block016_data_flat108) := by decide +kernel
theorem block016_data_flat109_original : block016_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (225492396668928 : Int) atom1144Coded) (CoefficientMerge.scale (213102246140928 : Int) atom1145Coded)) := by
  rw [block016_data_flat109_step, block016_data_flat107_original, block016_data_flat108_original]
def block016_data_flat110 : CoefficientMerge.Poly := [(nat_lit 1961, Int.ofNat (nat_lit 210644834070528))]
theorem block016_data_flat110_step : block016_data_flat110 = (CoefficientMerge.scale (210644834070528 : Int) atom1146Coded) := by decide +kernel
theorem block016_data_flat110_original : block016_data_flat110 = (CoefficientMerge.scale (210644834070528 : Int) atom1146Coded) := by
  rw [block016_data_flat110_step]
def block016_data_flat111 : CoefficientMerge.Poly := [(nat_lit 1962, Int.ofNat (nat_lit 254097258573312))]
theorem block016_data_flat111_step : block016_data_flat111 = (CoefficientMerge.scale (254097258573312 : Int) atom1147Coded) := by decide +kernel
theorem block016_data_flat111_original : block016_data_flat111 = (CoefficientMerge.scale (254097258573312 : Int) atom1147Coded) := by
  rw [block016_data_flat111_step]
def block016_data_flat112 : CoefficientMerge.Poly := [(nat_lit 1963, Int.ofNat (nat_lit 241111592916480))]
theorem block016_data_flat112_step : block016_data_flat112 = (CoefficientMerge.scale (241111592916480 : Int) atom1148Coded) := by decide +kernel
theorem block016_data_flat112_original : block016_data_flat112 = (CoefficientMerge.scale (241111592916480 : Int) atom1148Coded) := by
  rw [block016_data_flat112_step]
def block016_data_flat113 : CoefficientMerge.Poly := [(nat_lit 1962, Int.ofNat (nat_lit 254097258573312)), (nat_lit 1963, Int.ofNat (nat_lit 241111592916480))]
theorem block016_data_flat113_step : block016_data_flat113 = (CoefficientMerge.fastMerge block016_data_flat111 block016_data_flat112) := by decide +kernel
theorem block016_data_flat113_original : block016_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (254097258573312 : Int) atom1147Coded) (CoefficientMerge.scale (241111592916480 : Int) atom1148Coded)) := by
  rw [block016_data_flat113_step, block016_data_flat111_original, block016_data_flat112_original]
def block016_data_flat114 : CoefficientMerge.Poly := [(nat_lit 1961, Int.ofNat (nat_lit 210644834070528)), (nat_lit 1962, Int.ofNat (nat_lit 254097258573312)), (nat_lit 1963, Int.ofNat (nat_lit 241111592916480))]
theorem block016_data_flat114_step : block016_data_flat114 = (CoefficientMerge.fastMerge block016_data_flat110 block016_data_flat113) := by decide +kernel
theorem block016_data_flat114_original : block016_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (210644834070528 : Int) atom1146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254097258573312 : Int) atom1147Coded) (CoefficientMerge.scale (241111592916480 : Int) atom1148Coded))) := by
  rw [block016_data_flat114_step, block016_data_flat110_original, block016_data_flat113_original]
def block016_data_flat115 : CoefficientMerge.Poly := [(nat_lit 1959, Int.ofNat (nat_lit 225492396668928)), (nat_lit 1960, Int.ofNat (nat_lit 213102246140928)), (nat_lit 1961, Int.ofNat (nat_lit 210644834070528)), (nat_lit 1962, Int.ofNat (nat_lit 254097258573312)), (nat_lit 1963, Int.ofNat (nat_lit 241111592916480))]
theorem block016_data_flat115_step : block016_data_flat115 = (CoefficientMerge.fastMerge block016_data_flat109 block016_data_flat114) := by decide +kernel
theorem block016_data_flat115_original : block016_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (225492396668928 : Int) atom1144Coded) (CoefficientMerge.scale (213102246140928 : Int) atom1145Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210644834070528 : Int) atom1146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254097258573312 : Int) atom1147Coded) (CoefficientMerge.scale (241111592916480 : Int) atom1148Coded)))) := by
  rw [block016_data_flat115_step, block016_data_flat109_original, block016_data_flat114_original]
def block016_data_flat116 : CoefficientMerge.Poly := [(nat_lit 1954, Int.ofNat (nat_lit 239751911272896)), (nat_lit 1955, Int.ofNat (nat_lit 231275379769632)), (nat_lit 1956, Int.ofNat (nat_lit 256178108463552)), (nat_lit 1957, Int.ofNat (nat_lit 241414683827328)), (nat_lit 1958, Int.ofNat (nat_lit 226060036950528)), (nat_lit 1959, Int.ofNat (nat_lit 225492396668928)), (nat_lit 1960, Int.ofNat (nat_lit 213102246140928)), (nat_lit 1961, Int.ofNat (nat_lit 210644834070528)), (nat_lit 1962, Int.ofNat (nat_lit 254097258573312)), (nat_lit 1963, Int.ofNat (nat_lit 241111592916480))]
theorem block016_data_flat116_step : block016_data_flat116 = (CoefficientMerge.fastMerge block016_data_flat106 block016_data_flat115) := by decide +kernel
theorem block016_data_flat116_original : block016_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (239751911272896 : Int) atom1139Coded) (CoefficientMerge.scale (231275379769632 : Int) atom1140Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256178108463552 : Int) atom1141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241414683827328 : Int) atom1142Coded) (CoefficientMerge.scale (226060036950528 : Int) atom1143Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (225492396668928 : Int) atom1144Coded) (CoefficientMerge.scale (213102246140928 : Int) atom1145Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210644834070528 : Int) atom1146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254097258573312 : Int) atom1147Coded) (CoefficientMerge.scale (241111592916480 : Int) atom1148Coded))))) := by
  rw [block016_data_flat116_step, block016_data_flat106_original, block016_data_flat115_original]
def block016_data_flat117 : CoefficientMerge.Poly := [(nat_lit 1935, Int.ofNat (nat_lit 196385496652800)), (nat_lit 1936, Int.ofNat (nat_lit 186015269260800)), (nat_lit 1937, Int.ofNat (nat_lit 185577780326400)), (nat_lit 1938, Int.ofNat (nat_lit 228846660134400)), (nat_lit 1939, Int.ofNat (nat_lit 213473981952000)), (nat_lit 1940, Int.ofNat (nat_lit 283150698969600)), (nat_lit 1941, Int.ofNat (nat_lit 308346582297600)), (nat_lit 1942, Int.ofNat (nat_lit 369858557376000)), (nat_lit 1943, Int.ofNat (nat_lit 431370532454400)), (nat_lit 1953, Int.ofNat (nat_lit 126437516476128)), (nat_lit 1954, Int.ofNat (nat_lit 239751911272896)), (nat_lit 1955, Int.ofNat (nat_lit 231275379769632)), (nat_lit 1956, Int.ofNat (nat_lit 256178108463552)), (nat_lit 1957, Int.ofNat (nat_lit 241414683827328)), (nat_lit 1958, Int.ofNat (nat_lit 226060036950528)), (nat_lit 1959, Int.ofNat (nat_lit 225492396668928)), (nat_lit 1960, Int.ofNat (nat_lit 213102246140928)), (nat_lit 1961, Int.ofNat (nat_lit 210644834070528)), (nat_lit 1962, Int.ofNat (nat_lit 254097258573312)), (nat_lit 1963, Int.ofNat (nat_lit 241111592916480))]
theorem block016_data_flat117_step : block016_data_flat117 = (CoefficientMerge.fastMerge block016_data_flat097 block016_data_flat116) := by decide +kernel
theorem block016_data_flat117_original : block016_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (196385496652800 : Int) atom1129Coded) (CoefficientMerge.scale (186015269260800 : Int) atom1130Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (185577780326400 : Int) atom1131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (228846660134400 : Int) atom1132Coded) (CoefficientMerge.scale (213473981952000 : Int) atom1133Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (283150698969600 : Int) atom1134Coded) (CoefficientMerge.scale (308346582297600 : Int) atom1135Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (369858557376000 : Int) atom1136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (431370532454400 : Int) atom1137Coded) (CoefficientMerge.scale (126437516476128 : Int) atom1138Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (239751911272896 : Int) atom1139Coded) (CoefficientMerge.scale (231275379769632 : Int) atom1140Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256178108463552 : Int) atom1141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241414683827328 : Int) atom1142Coded) (CoefficientMerge.scale (226060036950528 : Int) atom1143Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (225492396668928 : Int) atom1144Coded) (CoefficientMerge.scale (213102246140928 : Int) atom1145Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210644834070528 : Int) atom1146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254097258573312 : Int) atom1147Coded) (CoefficientMerge.scale (241111592916480 : Int) atom1148Coded)))))) := by
  rw [block016_data_flat117_step, block016_data_flat097_original, block016_data_flat116_original]
def block016_data_flat118 : CoefficientMerge.Poly := [(nat_lit 1964, Int.ofNat (nat_lit 313175322459648))]
theorem block016_data_flat118_step : block016_data_flat118 = (CoefficientMerge.scale (313175322459648 : Int) atom1149Coded) := by decide +kernel
theorem block016_data_flat118_original : block016_data_flat118 = (CoefficientMerge.scale (313175322459648 : Int) atom1149Coded) := by
  rw [block016_data_flat118_step]
def block016_data_flat119 : CoefficientMerge.Poly := [(nat_lit 1965, Int.ofNat (nat_lit 345165153974784))]
theorem block016_data_flat119_step : block016_data_flat119 = (CoefficientMerge.scale (345165153974784 : Int) atom1150Coded) := by decide +kernel
theorem block016_data_flat119_original : block016_data_flat119 = (CoefficientMerge.scale (345165153974784 : Int) atom1150Coded) := by
  rw [block016_data_flat119_step]
def block016_data_flat120 : CoefficientMerge.Poly := [(nat_lit 1964, Int.ofNat (nat_lit 313175322459648)), (nat_lit 1965, Int.ofNat (nat_lit 345165153974784))]
theorem block016_data_flat120_step : block016_data_flat120 = (CoefficientMerge.fastMerge block016_data_flat118 block016_data_flat119) := by decide +kernel
theorem block016_data_flat120_original : block016_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (313175322459648 : Int) atom1149Coded) (CoefficientMerge.scale (345165153974784 : Int) atom1150Coded)) := by
  rw [block016_data_flat120_step, block016_data_flat118_original, block016_data_flat119_original]
def block016_data_flat121 : CoefficientMerge.Poly := [(nat_lit 1966, Int.ofNat (nat_lit 413471077240320))]
theorem block016_data_flat121_step : block016_data_flat121 = (CoefficientMerge.scale (413471077240320 : Int) atom1151Coded) := by decide +kernel
theorem block016_data_flat121_original : block016_data_flat121 = (CoefficientMerge.scale (413471077240320 : Int) atom1151Coded) := by
  rw [block016_data_flat121_step]
def block016_data_flat122 : CoefficientMerge.Poly := [(nat_lit 1967, Int.ofNat (nat_lit 481777000505856))]
theorem block016_data_flat122_step : block016_data_flat122 = (CoefficientMerge.scale (481777000505856 : Int) atom1152Coded) := by decide +kernel
theorem block016_data_flat122_original : block016_data_flat122 = (CoefficientMerge.scale (481777000505856 : Int) atom1152Coded) := by
  rw [block016_data_flat122_step]
def block016_data_flat123 : CoefficientMerge.Poly := [(nat_lit 1978, Int.ofNat (nat_lit 151331474451168))]
theorem block016_data_flat123_step : block016_data_flat123 = (CoefficientMerge.scale (151331474451168 : Int) atom1153Coded) := by decide +kernel
theorem block016_data_flat123_original : block016_data_flat123 = (CoefficientMerge.scale (151331474451168 : Int) atom1153Coded) := by
  rw [block016_data_flat123_step]
def block016_data_flat124 : CoefficientMerge.Poly := [(nat_lit 1967, Int.ofNat (nat_lit 481777000505856)), (nat_lit 1978, Int.ofNat (nat_lit 151331474451168))]
theorem block016_data_flat124_step : block016_data_flat124 = (CoefficientMerge.fastMerge block016_data_flat122 block016_data_flat123) := by decide +kernel
theorem block016_data_flat124_original : block016_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (481777000505856 : Int) atom1152Coded) (CoefficientMerge.scale (151331474451168 : Int) atom1153Coded)) := by
  rw [block016_data_flat124_step, block016_data_flat122_original, block016_data_flat123_original]
def block016_data_flat125 : CoefficientMerge.Poly := [(nat_lit 1966, Int.ofNat (nat_lit 413471077240320)), (nat_lit 1967, Int.ofNat (nat_lit 481777000505856)), (nat_lit 1978, Int.ofNat (nat_lit 151331474451168))]
theorem block016_data_flat125_step : block016_data_flat125 = (CoefficientMerge.fastMerge block016_data_flat121 block016_data_flat124) := by decide +kernel
theorem block016_data_flat125_original : block016_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (413471077240320 : Int) atom1151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (481777000505856 : Int) atom1152Coded) (CoefficientMerge.scale (151331474451168 : Int) atom1153Coded))) := by
  rw [block016_data_flat125_step, block016_data_flat121_original, block016_data_flat124_original]
def block016_data_flat126 : CoefficientMerge.Poly := [(nat_lit 1964, Int.ofNat (nat_lit 313175322459648)), (nat_lit 1965, Int.ofNat (nat_lit 345165153974784)), (nat_lit 1966, Int.ofNat (nat_lit 413471077240320)), (nat_lit 1967, Int.ofNat (nat_lit 481777000505856)), (nat_lit 1978, Int.ofNat (nat_lit 151331474451168))]
theorem block016_data_flat126_step : block016_data_flat126 = (CoefficientMerge.fastMerge block016_data_flat120 block016_data_flat125) := by decide +kernel
theorem block016_data_flat126_original : block016_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (313175322459648 : Int) atom1149Coded) (CoefficientMerge.scale (345165153974784 : Int) atom1150Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413471077240320 : Int) atom1151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (481777000505856 : Int) atom1152Coded) (CoefficientMerge.scale (151331474451168 : Int) atom1153Coded)))) := by
  rw [block016_data_flat126_step, block016_data_flat120_original, block016_data_flat125_original]
def block016_data_flat127 : CoefficientMerge.Poly := [(nat_lit 1979, Int.ofNat (nat_lit 298353837763872))]
theorem block016_data_flat127_step : block016_data_flat127 = (CoefficientMerge.scale (298353837763872 : Int) atom1154Coded) := by decide +kernel
theorem block016_data_flat127_original : block016_data_flat127 = (CoefficientMerge.scale (298353837763872 : Int) atom1154Coded) := by
  rw [block016_data_flat127_step]
def block016_data_flat128 : CoefficientMerge.Poly := [(nat_lit 1980, Int.ofNat (nat_lit 317133010003392))]
theorem block016_data_flat128_step : block016_data_flat128 = (CoefficientMerge.scale (317133010003392 : Int) atom1155Coded) := by decide +kernel
theorem block016_data_flat128_original : block016_data_flat128 = (CoefficientMerge.scale (317133010003392 : Int) atom1155Coded) := by
  rw [block016_data_flat128_step]
def block016_data_flat129 : CoefficientMerge.Poly := [(nat_lit 1979, Int.ofNat (nat_lit 298353837763872)), (nat_lit 1980, Int.ofNat (nat_lit 317133010003392))]
theorem block016_data_flat129_step : block016_data_flat129 = (CoefficientMerge.fastMerge block016_data_flat127 block016_data_flat128) := by decide +kernel
theorem block016_data_flat129_original : block016_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (298353837763872 : Int) atom1154Coded) (CoefficientMerge.scale (317133010003392 : Int) atom1155Coded)) := by
  rw [block016_data_flat129_step, block016_data_flat127_original, block016_data_flat128_original]
def block016_data_flat130 : CoefficientMerge.Poly := [(nat_lit 1981, Int.ofNat (nat_lit 302412110064768))]
theorem block016_data_flat130_step : block016_data_flat130 = (CoefficientMerge.scale (302412110064768 : Int) atom1156Coded) := by decide +kernel
theorem block016_data_flat130_original : block016_data_flat130 = (CoefficientMerge.scale (302412110064768 : Int) atom1156Coded) := by
  rw [block016_data_flat130_step]
def block016_data_flat131 : CoefficientMerge.Poly := [(nat_lit 1982, Int.ofNat (nat_lit 284016947309568))]
theorem block016_data_flat131_step : block016_data_flat131 = (CoefficientMerge.scale (284016947309568 : Int) atom1157Coded) := by decide +kernel
theorem block016_data_flat131_original : block016_data_flat131 = (CoefficientMerge.scale (284016947309568 : Int) atom1157Coded) := by
  rw [block016_data_flat131_step]
def block016_data_flat132 : CoefficientMerge.Poly := [(nat_lit 1983, Int.ofNat (nat_lit 280408791149568))]
theorem block016_data_flat132_step : block016_data_flat132 = (CoefficientMerge.scale (280408791149568 : Int) atom1158Coded) := by decide +kernel
theorem block016_data_flat132_original : block016_data_flat132 = (CoefficientMerge.scale (280408791149568 : Int) atom1158Coded) := by
  rw [block016_data_flat132_step]
def block016_data_flat133 : CoefficientMerge.Poly := [(nat_lit 1982, Int.ofNat (nat_lit 284016947309568)), (nat_lit 1983, Int.ofNat (nat_lit 280408791149568))]
theorem block016_data_flat133_step : block016_data_flat133 = (CoefficientMerge.fastMerge block016_data_flat131 block016_data_flat132) := by decide +kernel
theorem block016_data_flat133_original : block016_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (284016947309568 : Int) atom1157Coded) (CoefficientMerge.scale (280408791149568 : Int) atom1158Coded)) := by
  rw [block016_data_flat133_step, block016_data_flat131_original, block016_data_flat132_original]
def block016_data_flat134 : CoefficientMerge.Poly := [(nat_lit 1981, Int.ofNat (nat_lit 302412110064768)), (nat_lit 1982, Int.ofNat (nat_lit 284016947309568)), (nat_lit 1983, Int.ofNat (nat_lit 280408791149568))]
theorem block016_data_flat134_step : block016_data_flat134 = (CoefficientMerge.fastMerge block016_data_flat130 block016_data_flat133) := by decide +kernel
theorem block016_data_flat134_original : block016_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (302412110064768 : Int) atom1156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284016947309568 : Int) atom1157Coded) (CoefficientMerge.scale (280408791149568 : Int) atom1158Coded))) := by
  rw [block016_data_flat134_step, block016_data_flat130_original, block016_data_flat133_original]
def block016_data_flat135 : CoefficientMerge.Poly := [(nat_lit 1979, Int.ofNat (nat_lit 298353837763872)), (nat_lit 1980, Int.ofNat (nat_lit 317133010003392)), (nat_lit 1981, Int.ofNat (nat_lit 302412110064768)), (nat_lit 1982, Int.ofNat (nat_lit 284016947309568)), (nat_lit 1983, Int.ofNat (nat_lit 280408791149568))]
theorem block016_data_flat135_step : block016_data_flat135 = (CoefficientMerge.fastMerge block016_data_flat129 block016_data_flat134) := by decide +kernel
theorem block016_data_flat135_original : block016_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (298353837763872 : Int) atom1154Coded) (CoefficientMerge.scale (317133010003392 : Int) atom1155Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (302412110064768 : Int) atom1156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284016947309568 : Int) atom1157Coded) (CoefficientMerge.scale (280408791149568 : Int) atom1158Coded)))) := by
  rw [block016_data_flat135_step, block016_data_flat129_original, block016_data_flat134_original]
def block016_data_flat136 : CoefficientMerge.Poly := [(nat_lit 1964, Int.ofNat (nat_lit 313175322459648)), (nat_lit 1965, Int.ofNat (nat_lit 345165153974784)), (nat_lit 1966, Int.ofNat (nat_lit 413471077240320)), (nat_lit 1967, Int.ofNat (nat_lit 481777000505856)), (nat_lit 1978, Int.ofNat (nat_lit 151331474451168)), (nat_lit 1979, Int.ofNat (nat_lit 298353837763872)), (nat_lit 1980, Int.ofNat (nat_lit 317133010003392)), (nat_lit 1981, Int.ofNat (nat_lit 302412110064768)), (nat_lit 1982, Int.ofNat (nat_lit 284016947309568)), (nat_lit 1983, Int.ofNat (nat_lit 280408791149568))]
theorem block016_data_flat136_step : block016_data_flat136 = (CoefficientMerge.fastMerge block016_data_flat126 block016_data_flat135) := by decide +kernel
theorem block016_data_flat136_original : block016_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (313175322459648 : Int) atom1149Coded) (CoefficientMerge.scale (345165153974784 : Int) atom1150Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413471077240320 : Int) atom1151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (481777000505856 : Int) atom1152Coded) (CoefficientMerge.scale (151331474451168 : Int) atom1153Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (298353837763872 : Int) atom1154Coded) (CoefficientMerge.scale (317133010003392 : Int) atom1155Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (302412110064768 : Int) atom1156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284016947309568 : Int) atom1157Coded) (CoefficientMerge.scale (280408791149568 : Int) atom1158Coded))))) := by
  rw [block016_data_flat136_step, block016_data_flat126_original, block016_data_flat135_original]
def block016_data_flat137 : CoefficientMerge.Poly := [(nat_lit 1984, Int.ofNat (nat_lit 264978124743168))]
theorem block016_data_flat137_step : block016_data_flat137 = (CoefficientMerge.scale (264978124743168 : Int) atom1159Coded) := by decide +kernel
theorem block016_data_flat137_original : block016_data_flat137 = (CoefficientMerge.scale (264978124743168 : Int) atom1159Coded) := by
  rw [block016_data_flat137_step]
def block016_data_flat138 : CoefficientMerge.Poly := [(nat_lit 1985, Int.ofNat (nat_lit 259480196794368))]
theorem block016_data_flat138_step : block016_data_flat138 = (CoefficientMerge.scale (259480196794368 : Int) atom1160Coded) := by decide +kernel
theorem block016_data_flat138_original : block016_data_flat138 = (CoefficientMerge.scale (259480196794368 : Int) atom1160Coded) := by
  rw [block016_data_flat138_step]
def block016_data_flat139 : CoefficientMerge.Poly := [(nat_lit 1984, Int.ofNat (nat_lit 264978124743168)), (nat_lit 1985, Int.ofNat (nat_lit 259480196794368))]
theorem block016_data_flat139_step : block016_data_flat139 = (CoefficientMerge.fastMerge block016_data_flat137 block016_data_flat138) := by decide +kernel
theorem block016_data_flat139_original : block016_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (264978124743168 : Int) atom1159Coded) (CoefficientMerge.scale (259480196794368 : Int) atom1160Coded)) := by
  rw [block016_data_flat139_step, block016_data_flat137_original, block016_data_flat138_original]
def block016_data_flat140 : CoefficientMerge.Poly := [(nat_lit 1986, Int.ofNat (nat_lit 298624869430272))]
theorem block016_data_flat140_step : block016_data_flat140 = (CoefficientMerge.scale (298624869430272 : Int) atom1161Coded) := by decide +kernel
theorem block016_data_flat140_original : block016_data_flat140 = (CoefficientMerge.scale (298624869430272 : Int) atom1161Coded) := by
  rw [block016_data_flat140_step]
def block016_data_flat141 : CoefficientMerge.Poly := [(nat_lit 1987, Int.ofNat (nat_lit 280064215918080))]
theorem block016_data_flat141_step : block016_data_flat141 = (CoefficientMerge.scale (280064215918080 : Int) atom1162Coded) := by decide +kernel
theorem block016_data_flat141_original : block016_data_flat141 = (CoefficientMerge.scale (280064215918080 : Int) atom1162Coded) := by
  rw [block016_data_flat141_step]
def block016_data_flat142 : CoefficientMerge.Poly := [(nat_lit 1988, Int.ofNat (nat_lit 346552957605888))]
theorem block016_data_flat142_step : block016_data_flat142 = (CoefficientMerge.scale (346552957605888 : Int) atom1163Coded) := by decide +kernel
theorem block016_data_flat142_original : block016_data_flat142 = (CoefficientMerge.scale (346552957605888 : Int) atom1163Coded) := by
  rw [block016_data_flat142_step]
def block016_data_flat143 : CoefficientMerge.Poly := [(nat_lit 1987, Int.ofNat (nat_lit 280064215918080)), (nat_lit 1988, Int.ofNat (nat_lit 346552957605888))]
theorem block016_data_flat143_step : block016_data_flat143 = (CoefficientMerge.fastMerge block016_data_flat141 block016_data_flat142) := by decide +kernel
theorem block016_data_flat143_original : block016_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (280064215918080 : Int) atom1162Coded) (CoefficientMerge.scale (346552957605888 : Int) atom1163Coded)) := by
  rw [block016_data_flat143_step, block016_data_flat141_original, block016_data_flat142_original]
def block016_data_flat144 : CoefficientMerge.Poly := [(nat_lit 1986, Int.ofNat (nat_lit 298624869430272)), (nat_lit 1987, Int.ofNat (nat_lit 280064215918080)), (nat_lit 1988, Int.ofNat (nat_lit 346552957605888))]
theorem block016_data_flat144_step : block016_data_flat144 = (CoefficientMerge.fastMerge block016_data_flat140 block016_data_flat143) := by decide +kernel
theorem block016_data_flat144_original : block016_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (298624869430272 : Int) atom1161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (280064215918080 : Int) atom1162Coded) (CoefficientMerge.scale (346552957605888 : Int) atom1163Coded))) := by
  rw [block016_data_flat144_step, block016_data_flat140_original, block016_data_flat143_original]
def block016_data_flat145 : CoefficientMerge.Poly := [(nat_lit 1984, Int.ofNat (nat_lit 264978124743168)), (nat_lit 1985, Int.ofNat (nat_lit 259480196794368)), (nat_lit 1986, Int.ofNat (nat_lit 298624869430272)), (nat_lit 1987, Int.ofNat (nat_lit 280064215918080)), (nat_lit 1988, Int.ofNat (nat_lit 346552957605888))]
theorem block016_data_flat145_step : block016_data_flat145 = (CoefficientMerge.fastMerge block016_data_flat139 block016_data_flat144) := by decide +kernel
theorem block016_data_flat145_original : block016_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (264978124743168 : Int) atom1159Coded) (CoefficientMerge.scale (259480196794368 : Int) atom1160Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298624869430272 : Int) atom1161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (280064215918080 : Int) atom1162Coded) (CoefficientMerge.scale (346552957605888 : Int) atom1163Coded)))) := by
  rw [block016_data_flat145_step, block016_data_flat139_original, block016_data_flat144_original]
def block016_data_flat146 : CoefficientMerge.Poly := [(nat_lit 1989, Int.ofNat (nat_lit 370433329288704))]
theorem block016_data_flat146_step : block016_data_flat146 = (CoefficientMerge.scale (370433329288704 : Int) atom1164Coded) := by decide +kernel
theorem block016_data_flat146_original : block016_data_flat146 = (CoefficientMerge.scale (370433329288704 : Int) atom1164Coded) := by
  rw [block016_data_flat146_step]
def block016_data_flat147 : CoefficientMerge.Poly := [(nat_lit 1990, Int.ofNat (nat_lit 430629792721920))]
theorem block016_data_flat147_step : block016_data_flat147 = (CoefficientMerge.scale (430629792721920 : Int) atom1165Coded) := by decide +kernel
theorem block016_data_flat147_original : block016_data_flat147 = (CoefficientMerge.scale (430629792721920 : Int) atom1165Coded) := by
  rw [block016_data_flat147_step]
def block016_data_flat148 : CoefficientMerge.Poly := [(nat_lit 1989, Int.ofNat (nat_lit 370433329288704)), (nat_lit 1990, Int.ofNat (nat_lit 430629792721920))]
theorem block016_data_flat148_step : block016_data_flat148 = (CoefficientMerge.fastMerge block016_data_flat146 block016_data_flat147) := by decide +kernel
theorem block016_data_flat148_original : block016_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (370433329288704 : Int) atom1164Coded) (CoefficientMerge.scale (430629792721920 : Int) atom1165Coded)) := by
  rw [block016_data_flat148_step, block016_data_flat146_original, block016_data_flat147_original]
def block016_data_flat149 : CoefficientMerge.Poly := [(nat_lit 1991, Int.ofNat (nat_lit 490826256155136))]
theorem block016_data_flat149_step : block016_data_flat149 = (CoefficientMerge.scale (490826256155136 : Int) atom1166Coded) := by decide +kernel
theorem block016_data_flat149_original : block016_data_flat149 = (CoefficientMerge.scale (490826256155136 : Int) atom1166Coded) := by
  rw [block016_data_flat149_step]
def block016_data_flat150 : CoefficientMerge.Poly := [(nat_lit 2003, Int.ofNat (nat_lit 191205524119104))]
theorem block016_data_flat150_step : block016_data_flat150 = (CoefficientMerge.scale (191205524119104 : Int) atom1167Coded) := by decide +kernel
theorem block016_data_flat150_original : block016_data_flat150 = (CoefficientMerge.scale (191205524119104 : Int) atom1167Coded) := by
  rw [block016_data_flat150_step]
def block016_data_flat151 : CoefficientMerge.Poly := [(nat_lit 2004, Int.ofNat (nat_lit 377351140782528))]
theorem block016_data_flat151_step : block016_data_flat151 = (CoefficientMerge.scale (377351140782528 : Int) atom1168Coded) := by decide +kernel
theorem block016_data_flat151_original : block016_data_flat151 = (CoefficientMerge.scale (377351140782528 : Int) atom1168Coded) := by
  rw [block016_data_flat151_step]
def block016_data_flat152 : CoefficientMerge.Poly := [(nat_lit 2003, Int.ofNat (nat_lit 191205524119104)), (nat_lit 2004, Int.ofNat (nat_lit 377351140782528))]
theorem block016_data_flat152_step : block016_data_flat152 = (CoefficientMerge.fastMerge block016_data_flat150 block016_data_flat151) := by decide +kernel
theorem block016_data_flat152_original : block016_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (191205524119104 : Int) atom1167Coded) (CoefficientMerge.scale (377351140782528 : Int) atom1168Coded)) := by
  rw [block016_data_flat152_step, block016_data_flat150_original, block016_data_flat151_original]
def block016_data_flat153 : CoefficientMerge.Poly := [(nat_lit 1991, Int.ofNat (nat_lit 490826256155136)), (nat_lit 2003, Int.ofNat (nat_lit 191205524119104)), (nat_lit 2004, Int.ofNat (nat_lit 377351140782528))]
theorem block016_data_flat153_step : block016_data_flat153 = (CoefficientMerge.fastMerge block016_data_flat149 block016_data_flat152) := by decide +kernel
theorem block016_data_flat153_original : block016_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (490826256155136 : Int) atom1166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191205524119104 : Int) atom1167Coded) (CoefficientMerge.scale (377351140782528 : Int) atom1168Coded))) := by
  rw [block016_data_flat153_step, block016_data_flat149_original, block016_data_flat152_original]
def block016_data_flat154 : CoefficientMerge.Poly := [(nat_lit 1989, Int.ofNat (nat_lit 370433329288704)), (nat_lit 1990, Int.ofNat (nat_lit 430629792721920)), (nat_lit 1991, Int.ofNat (nat_lit 490826256155136)), (nat_lit 2003, Int.ofNat (nat_lit 191205524119104)), (nat_lit 2004, Int.ofNat (nat_lit 377351140782528))]
theorem block016_data_flat154_step : block016_data_flat154 = (CoefficientMerge.fastMerge block016_data_flat148 block016_data_flat153) := by decide +kernel
theorem block016_data_flat154_original : block016_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (370433329288704 : Int) atom1164Coded) (CoefficientMerge.scale (430629792721920 : Int) atom1165Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (490826256155136 : Int) atom1166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191205524119104 : Int) atom1167Coded) (CoefficientMerge.scale (377351140782528 : Int) atom1168Coded)))) := by
  rw [block016_data_flat154_step, block016_data_flat148_original, block016_data_flat153_original]
def block016_data_flat155 : CoefficientMerge.Poly := [(nat_lit 1984, Int.ofNat (nat_lit 264978124743168)), (nat_lit 1985, Int.ofNat (nat_lit 259480196794368)), (nat_lit 1986, Int.ofNat (nat_lit 298624869430272)), (nat_lit 1987, Int.ofNat (nat_lit 280064215918080)), (nat_lit 1988, Int.ofNat (nat_lit 346552957605888)), (nat_lit 1989, Int.ofNat (nat_lit 370433329288704)), (nat_lit 1990, Int.ofNat (nat_lit 430629792721920)), (nat_lit 1991, Int.ofNat (nat_lit 490826256155136)), (nat_lit 2003, Int.ofNat (nat_lit 191205524119104)), (nat_lit 2004, Int.ofNat (nat_lit 377351140782528))]
theorem block016_data_flat155_step : block016_data_flat155 = (CoefficientMerge.fastMerge block016_data_flat145 block016_data_flat154) := by decide +kernel
theorem block016_data_flat155_original : block016_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (264978124743168 : Int) atom1159Coded) (CoefficientMerge.scale (259480196794368 : Int) atom1160Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298624869430272 : Int) atom1161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (280064215918080 : Int) atom1162Coded) (CoefficientMerge.scale (346552957605888 : Int) atom1163Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (370433329288704 : Int) atom1164Coded) (CoefficientMerge.scale (430629792721920 : Int) atom1165Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (490826256155136 : Int) atom1166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191205524119104 : Int) atom1167Coded) (CoefficientMerge.scale (377351140782528 : Int) atom1168Coded))))) := by
  rw [block016_data_flat155_step, block016_data_flat145_original, block016_data_flat154_original]
def block016_data_flat156 : CoefficientMerge.Poly := [(nat_lit 1964, Int.ofNat (nat_lit 313175322459648)), (nat_lit 1965, Int.ofNat (nat_lit 345165153974784)), (nat_lit 1966, Int.ofNat (nat_lit 413471077240320)), (nat_lit 1967, Int.ofNat (nat_lit 481777000505856)), (nat_lit 1978, Int.ofNat (nat_lit 151331474451168)), (nat_lit 1979, Int.ofNat (nat_lit 298353837763872)), (nat_lit 1980, Int.ofNat (nat_lit 317133010003392)), (nat_lit 1981, Int.ofNat (nat_lit 302412110064768)), (nat_lit 1982, Int.ofNat (nat_lit 284016947309568)), (nat_lit 1983, Int.ofNat (nat_lit 280408791149568)), (nat_lit 1984, Int.ofNat (nat_lit 264978124743168)), (nat_lit 1985, Int.ofNat (nat_lit 259480196794368)), (nat_lit 1986, Int.ofNat (nat_lit 298624869430272)), (nat_lit 1987, Int.ofNat (nat_lit 280064215918080)), (nat_lit 1988, Int.ofNat (nat_lit 346552957605888)), (nat_lit 1989, Int.ofNat (nat_lit 370433329288704)), (nat_lit 1990, Int.ofNat (nat_lit 430629792721920)), (nat_lit 1991, Int.ofNat (nat_lit 490826256155136)), (nat_lit 2003, Int.ofNat (nat_lit 191205524119104)), (nat_lit 2004, Int.ofNat (nat_lit 377351140782528))]
theorem block016_data_flat156_step : block016_data_flat156 = (CoefficientMerge.fastMerge block016_data_flat136 block016_data_flat155) := by decide +kernel
theorem block016_data_flat156_original : block016_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (313175322459648 : Int) atom1149Coded) (CoefficientMerge.scale (345165153974784 : Int) atom1150Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413471077240320 : Int) atom1151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (481777000505856 : Int) atom1152Coded) (CoefficientMerge.scale (151331474451168 : Int) atom1153Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (298353837763872 : Int) atom1154Coded) (CoefficientMerge.scale (317133010003392 : Int) atom1155Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (302412110064768 : Int) atom1156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284016947309568 : Int) atom1157Coded) (CoefficientMerge.scale (280408791149568 : Int) atom1158Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (264978124743168 : Int) atom1159Coded) (CoefficientMerge.scale (259480196794368 : Int) atom1160Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298624869430272 : Int) atom1161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (280064215918080 : Int) atom1162Coded) (CoefficientMerge.scale (346552957605888 : Int) atom1163Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (370433329288704 : Int) atom1164Coded) (CoefficientMerge.scale (430629792721920 : Int) atom1165Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (490826256155136 : Int) atom1166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191205524119104 : Int) atom1167Coded) (CoefficientMerge.scale (377351140782528 : Int) atom1168Coded)))))) := by
  rw [block016_data_flat156_step, block016_data_flat136_original, block016_data_flat155_original]
def block016_data_flat157 : CoefficientMerge.Poly := [(nat_lit 1935, Int.ofNat (nat_lit 196385496652800)), (nat_lit 1936, Int.ofNat (nat_lit 186015269260800)), (nat_lit 1937, Int.ofNat (nat_lit 185577780326400)), (nat_lit 1938, Int.ofNat (nat_lit 228846660134400)), (nat_lit 1939, Int.ofNat (nat_lit 213473981952000)), (nat_lit 1940, Int.ofNat (nat_lit 283150698969600)), (nat_lit 1941, Int.ofNat (nat_lit 308346582297600)), (nat_lit 1942, Int.ofNat (nat_lit 369858557376000)), (nat_lit 1943, Int.ofNat (nat_lit 431370532454400)), (nat_lit 1953, Int.ofNat (nat_lit 126437516476128)), (nat_lit 1954, Int.ofNat (nat_lit 239751911272896)), (nat_lit 1955, Int.ofNat (nat_lit 231275379769632)), (nat_lit 1956, Int.ofNat (nat_lit 256178108463552)), (nat_lit 1957, Int.ofNat (nat_lit 241414683827328)), (nat_lit 1958, Int.ofNat (nat_lit 226060036950528)), (nat_lit 1959, Int.ofNat (nat_lit 225492396668928)), (nat_lit 1960, Int.ofNat (nat_lit 213102246140928)), (nat_lit 1961, Int.ofNat (nat_lit 210644834070528)), (nat_lit 1962, Int.ofNat (nat_lit 254097258573312)), (nat_lit 1963, Int.ofNat (nat_lit 241111592916480)), (nat_lit 1964, Int.ofNat (nat_lit 313175322459648)), (nat_lit 1965, Int.ofNat (nat_lit 345165153974784)), (nat_lit 1966, Int.ofNat (nat_lit 413471077240320)), (nat_lit 1967, Int.ofNat (nat_lit 481777000505856)), (nat_lit 1978, Int.ofNat (nat_lit 151331474451168)), (nat_lit 1979, Int.ofNat (nat_lit 298353837763872)), (nat_lit 1980, Int.ofNat (nat_lit 317133010003392)), (nat_lit 1981, Int.ofNat (nat_lit 302412110064768)), (nat_lit 1982, Int.ofNat (nat_lit 284016947309568)), (nat_lit 1983, Int.ofNat (nat_lit 280408791149568)), (nat_lit 1984, Int.ofNat (nat_lit 264978124743168)), (nat_lit 1985, Int.ofNat (nat_lit 259480196794368)), (nat_lit 1986, Int.ofNat (nat_lit 298624869430272)), (nat_lit 1987, Int.ofNat (nat_lit 280064215918080)), (nat_lit 1988, Int.ofNat (nat_lit 346552957605888)), (nat_lit 1989, Int.ofNat (nat_lit 370433329288704)), (nat_lit 1990, Int.ofNat (nat_lit 430629792721920)), (nat_lit 1991, Int.ofNat (nat_lit 490826256155136)), (nat_lit 2003, Int.ofNat (nat_lit 191205524119104)), (nat_lit 2004, Int.ofNat (nat_lit 377351140782528))]
theorem block016_data_flat157_step : block016_data_flat157 = (CoefficientMerge.fastMerge block016_data_flat117 block016_data_flat156) := by decide +kernel
theorem block016_data_flat157_original : block016_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (196385496652800 : Int) atom1129Coded) (CoefficientMerge.scale (186015269260800 : Int) atom1130Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (185577780326400 : Int) atom1131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (228846660134400 : Int) atom1132Coded) (CoefficientMerge.scale (213473981952000 : Int) atom1133Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (283150698969600 : Int) atom1134Coded) (CoefficientMerge.scale (308346582297600 : Int) atom1135Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (369858557376000 : Int) atom1136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (431370532454400 : Int) atom1137Coded) (CoefficientMerge.scale (126437516476128 : Int) atom1138Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (239751911272896 : Int) atom1139Coded) (CoefficientMerge.scale (231275379769632 : Int) atom1140Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256178108463552 : Int) atom1141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241414683827328 : Int) atom1142Coded) (CoefficientMerge.scale (226060036950528 : Int) atom1143Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (225492396668928 : Int) atom1144Coded) (CoefficientMerge.scale (213102246140928 : Int) atom1145Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210644834070528 : Int) atom1146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254097258573312 : Int) atom1147Coded) (CoefficientMerge.scale (241111592916480 : Int) atom1148Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (313175322459648 : Int) atom1149Coded) (CoefficientMerge.scale (345165153974784 : Int) atom1150Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413471077240320 : Int) atom1151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (481777000505856 : Int) atom1152Coded) (CoefficientMerge.scale (151331474451168 : Int) atom1153Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (298353837763872 : Int) atom1154Coded) (CoefficientMerge.scale (317133010003392 : Int) atom1155Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (302412110064768 : Int) atom1156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284016947309568 : Int) atom1157Coded) (CoefficientMerge.scale (280408791149568 : Int) atom1158Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (264978124743168 : Int) atom1159Coded) (CoefficientMerge.scale (259480196794368 : Int) atom1160Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298624869430272 : Int) atom1161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (280064215918080 : Int) atom1162Coded) (CoefficientMerge.scale (346552957605888 : Int) atom1163Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (370433329288704 : Int) atom1164Coded) (CoefficientMerge.scale (430629792721920 : Int) atom1165Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (490826256155136 : Int) atom1166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191205524119104 : Int) atom1167Coded) (CoefficientMerge.scale (377351140782528 : Int) atom1168Coded))))))) := by
  rw [block016_data_flat157_step, block016_data_flat117_original, block016_data_flat156_original]
def block016_data_flat158 : CoefficientMerge.Poly := [(nat_lit 1880, Int.ofNat (nat_lit 101846650752000)), (nat_lit 1881, Int.ofNat (nat_lit 105562098127728)), (nat_lit 1882, Int.ofNat (nat_lit 125826931427472)), (nat_lit 1883, Int.ofNat (nat_lit 136085099683104)), (nat_lit 1884, Int.ofNat (nat_lit 161923371724224)), (nat_lit 1885, Int.ofNat (nat_lit 153240978844800)), (nat_lit 1886, Int.ofNat (nat_lit 140884323148800)), (nat_lit 1887, Int.ofNat (nat_lit 143314674048000)), (nat_lit 1888, Int.ofNat (nat_lit 133922514700800)), (nat_lit 1889, Int.ofNat (nat_lit 134463093811200)), (nat_lit 1890, Int.ofNat (nat_lit 172926682790400)), (nat_lit 1891, Int.ofNat (nat_lit 146965354905600)), (nat_lit 1892, Int.ofNat (nat_lit 206053422220800)), (nat_lit 1893, Int.ofNat (nat_lit 209093938099200)), (nat_lit 1894, Int.ofNat (nat_lit 248450545728000)), (nat_lit 1895, Int.ofNat (nat_lit 287807153356800)), (nat_lit 1903, Int.ofNat (nat_lit 81912017510400)), (nat_lit 1904, Int.ofNat (nat_lit 148101709324800)), (nat_lit 1905, Int.ofNat (nat_lit 135383723561328)), (nat_lit 1906, Int.ofNat (nat_lit 153607371376272)), (nat_lit 1907, Int.ofNat (nat_lit 165949249814304)), (nat_lit 1908, Int.ofNat (nat_lit 193871232037824)), (nat_lit 1909, Int.ofNat (nat_lit 185210101507200)), (nat_lit 1910, Int.ofNat (nat_lit 172874708160000)), (nat_lit 1911, Int.ofNat (nat_lit 175326321408000)), (nat_lit 1912, Int.ofNat (nat_lit 165955424409600)), (nat_lit 1913, Int.ofNat (nat_lit 166517265868800)), (nat_lit 1914, Int.ofNat (nat_lit 207331525632000)), (nat_lit 1915, Int.ofNat (nat_lit 186050276966400)), (nat_lit 1916, Int.ofNat (nat_lit 249818423500800)), (nat_lit 1917, Int.ofNat (nat_lit 262197835468800)), (nat_lit 1918, Int.ofNat (nat_lit 310893339187200)), (nat_lit 1919, Int.ofNat (nat_lit 359588842905600)), (nat_lit 1928, Int.ofNat (nat_lit 101123730892800)), (nat_lit 1929, Int.ofNat (nat_lit 189544167714528)), (nat_lit 1930, Int.ofNat (nat_lit 178502897027664)), (nat_lit 1931, Int.ofNat (nat_lit 194088787209504)), (nat_lit 1932, Int.ofNat (nat_lit 217928398463424)), (nat_lit 1933, Int.ofNat (nat_lit 208267937539200)), (nat_lit 1934, Int.ofNat (nat_lit 194933213798400)), (nat_lit 1935, Int.ofNat (nat_lit 196385496652800)), (nat_lit 1936, Int.ofNat (nat_lit 186015269260800)), (nat_lit 1937, Int.ofNat (nat_lit 185577780326400)), (nat_lit 1938, Int.ofNat (nat_lit 228846660134400)), (nat_lit 1939, Int.ofNat (nat_lit 213473981952000)), (nat_lit 1940, Int.ofNat (nat_lit 283150698969600)), (nat_lit 1941, Int.ofNat (nat_lit 308346582297600)), (nat_lit 1942, Int.ofNat (nat_lit 369858557376000)), (nat_lit 1943, Int.ofNat (nat_lit 431370532454400)), (nat_lit 1953, Int.ofNat (nat_lit 126437516476128)), (nat_lit 1954, Int.ofNat (nat_lit 239751911272896)), (nat_lit 1955, Int.ofNat (nat_lit 231275379769632)), (nat_lit 1956, Int.ofNat (nat_lit 256178108463552)), (nat_lit 1957, Int.ofNat (nat_lit 241414683827328)), (nat_lit 1958, Int.ofNat (nat_lit 226060036950528)), (nat_lit 1959, Int.ofNat (nat_lit 225492396668928)), (nat_lit 1960, Int.ofNat (nat_lit 213102246140928)), (nat_lit 1961, Int.ofNat (nat_lit 210644834070528)), (nat_lit 1962, Int.ofNat (nat_lit 254097258573312)), (nat_lit 1963, Int.ofNat (nat_lit 241111592916480)), (nat_lit 1964, Int.ofNat (nat_lit 313175322459648)), (nat_lit 1965, Int.ofNat (nat_lit 345165153974784)), (nat_lit 1966, Int.ofNat (nat_lit 413471077240320)), (nat_lit 1967, Int.ofNat (nat_lit 481777000505856)), (nat_lit 1978, Int.ofNat (nat_lit 151331474451168)), (nat_lit 1979, Int.ofNat (nat_lit 298353837763872)), (nat_lit 1980, Int.ofNat (nat_lit 317133010003392)), (nat_lit 1981, Int.ofNat (nat_lit 302412110064768)), (nat_lit 1982, Int.ofNat (nat_lit 284016947309568)), (nat_lit 1983, Int.ofNat (nat_lit 280408791149568)), (nat_lit 1984, Int.ofNat (nat_lit 264978124743168)), (nat_lit 1985, Int.ofNat (nat_lit 259480196794368)), (nat_lit 1986, Int.ofNat (nat_lit 298624869430272)), (nat_lit 1987, Int.ofNat (nat_lit 280064215918080)), (nat_lit 1988, Int.ofNat (nat_lit 346552957605888)), (nat_lit 1989, Int.ofNat (nat_lit 370433329288704)), (nat_lit 1990, Int.ofNat (nat_lit 430629792721920)), (nat_lit 1991, Int.ofNat (nat_lit 490826256155136)), (nat_lit 2003, Int.ofNat (nat_lit 191205524119104)), (nat_lit 2004, Int.ofNat (nat_lit 377351140782528))]
theorem block016_data_flat158_step : block016_data_flat158 = (CoefficientMerge.fastMerge block016_data_flat078 block016_data_flat157) := by decide +kernel
theorem block016_data_flat158_original : block016_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (101846650752000 : Int) atom1089Coded) (CoefficientMerge.scale (105562098127728 : Int) atom1090Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125826931427472 : Int) atom1091Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136085099683104 : Int) atom1092Coded) (CoefficientMerge.scale (161923371724224 : Int) atom1093Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153240978844800 : Int) atom1094Coded) (CoefficientMerge.scale (140884323148800 : Int) atom1095Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (143314674048000 : Int) atom1096Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (133922514700800 : Int) atom1097Coded) (CoefficientMerge.scale (134463093811200 : Int) atom1098Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (172926682790400 : Int) atom1099Coded) (CoefficientMerge.scale (146965354905600 : Int) atom1100Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (206053422220800 : Int) atom1101Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (209093938099200 : Int) atom1102Coded) (CoefficientMerge.scale (248450545728000 : Int) atom1103Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (287807153356800 : Int) atom1104Coded) (CoefficientMerge.scale (81912017510400 : Int) atom1105Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (148101709324800 : Int) atom1106Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135383723561328 : Int) atom1107Coded) (CoefficientMerge.scale (153607371376272 : Int) atom1108Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (165949249814304 : Int) atom1109Coded) (CoefficientMerge.scale (193871232037824 : Int) atom1110Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (185210101507200 : Int) atom1111Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172874708160000 : Int) atom1112Coded) (CoefficientMerge.scale (175326321408000 : Int) atom1113Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (165955424409600 : Int) atom1114Coded) (CoefficientMerge.scale (166517265868800 : Int) atom1115Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207331525632000 : Int) atom1116Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (186050276966400 : Int) atom1117Coded) (CoefficientMerge.scale (249818423500800 : Int) atom1118Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (262197835468800 : Int) atom1119Coded) (CoefficientMerge.scale (310893339187200 : Int) atom1120Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (359588842905600 : Int) atom1121Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101123730892800 : Int) atom1122Coded) (CoefficientMerge.scale (189544167714528 : Int) atom1123Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (178502897027664 : Int) atom1124Coded) (CoefficientMerge.scale (194088787209504 : Int) atom1125Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (217928398463424 : Int) atom1126Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (208267937539200 : Int) atom1127Coded) (CoefficientMerge.scale (194933213798400 : Int) atom1128Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (196385496652800 : Int) atom1129Coded) (CoefficientMerge.scale (186015269260800 : Int) atom1130Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (185577780326400 : Int) atom1131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (228846660134400 : Int) atom1132Coded) (CoefficientMerge.scale (213473981952000 : Int) atom1133Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (283150698969600 : Int) atom1134Coded) (CoefficientMerge.scale (308346582297600 : Int) atom1135Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (369858557376000 : Int) atom1136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (431370532454400 : Int) atom1137Coded) (CoefficientMerge.scale (126437516476128 : Int) atom1138Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (239751911272896 : Int) atom1139Coded) (CoefficientMerge.scale (231275379769632 : Int) atom1140Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256178108463552 : Int) atom1141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241414683827328 : Int) atom1142Coded) (CoefficientMerge.scale (226060036950528 : Int) atom1143Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (225492396668928 : Int) atom1144Coded) (CoefficientMerge.scale (213102246140928 : Int) atom1145Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210644834070528 : Int) atom1146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254097258573312 : Int) atom1147Coded) (CoefficientMerge.scale (241111592916480 : Int) atom1148Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (313175322459648 : Int) atom1149Coded) (CoefficientMerge.scale (345165153974784 : Int) atom1150Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413471077240320 : Int) atom1151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (481777000505856 : Int) atom1152Coded) (CoefficientMerge.scale (151331474451168 : Int) atom1153Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (298353837763872 : Int) atom1154Coded) (CoefficientMerge.scale (317133010003392 : Int) atom1155Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (302412110064768 : Int) atom1156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284016947309568 : Int) atom1157Coded) (CoefficientMerge.scale (280408791149568 : Int) atom1158Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (264978124743168 : Int) atom1159Coded) (CoefficientMerge.scale (259480196794368 : Int) atom1160Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298624869430272 : Int) atom1161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (280064215918080 : Int) atom1162Coded) (CoefficientMerge.scale (346552957605888 : Int) atom1163Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (370433329288704 : Int) atom1164Coded) (CoefficientMerge.scale (430629792721920 : Int) atom1165Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (490826256155136 : Int) atom1166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191205524119104 : Int) atom1167Coded) (CoefficientMerge.scale (377351140782528 : Int) atom1168Coded)))))))) := by
  rw [block016_data_flat158_step, block016_data_flat078_original, block016_data_flat157_original]
def block016_data_flat159 : CoefficientMerge.Poly := [(nat_lit 1880, Int.ofNat (nat_lit 101846650752000)), (nat_lit 1881, Int.ofNat (nat_lit 105562098127728)), (nat_lit 1882, Int.ofNat (nat_lit 125826931427472)), (nat_lit 1883, Int.ofNat (nat_lit 136085099683104)), (nat_lit 1884, Int.ofNat (nat_lit 161923371724224)), (nat_lit 1885, Int.ofNat (nat_lit 153240978844800)), (nat_lit 1886, Int.ofNat (nat_lit 140884323148800)), (nat_lit 1887, Int.ofNat (nat_lit 143314674048000)), (nat_lit 1888, Int.ofNat (nat_lit 133922514700800)), (nat_lit 1889, Int.ofNat (nat_lit 134463093811200)), (nat_lit 1890, Int.ofNat (nat_lit 172926682790400)), (nat_lit 1891, Int.ofNat (nat_lit 146965354905600)), (nat_lit 1892, Int.ofNat (nat_lit 206053422220800)), (nat_lit 1893, Int.ofNat (nat_lit 209093938099200)), (nat_lit 1894, Int.ofNat (nat_lit 248450545728000)), (nat_lit 1895, Int.ofNat (nat_lit 287807153356800)), (nat_lit 1903, Int.ofNat (nat_lit 81912017510400)), (nat_lit 1904, Int.ofNat (nat_lit 148101709324800)), (nat_lit 1905, Int.ofNat (nat_lit 135383723561328)), (nat_lit 1906, Int.ofNat (nat_lit 153607371376272)), (nat_lit 1907, Int.ofNat (nat_lit 165949249814304)), (nat_lit 1908, Int.ofNat (nat_lit 193871232037824)), (nat_lit 1909, Int.ofNat (nat_lit 185210101507200)), (nat_lit 1910, Int.ofNat (nat_lit 172874708160000)), (nat_lit 1911, Int.ofNat (nat_lit 175326321408000)), (nat_lit 1912, Int.ofNat (nat_lit 165955424409600)), (nat_lit 1913, Int.ofNat (nat_lit 166517265868800)), (nat_lit 1914, Int.ofNat (nat_lit 207331525632000)), (nat_lit 1915, Int.ofNat (nat_lit 186050276966400)), (nat_lit 1916, Int.ofNat (nat_lit 249818423500800)), (nat_lit 1917, Int.ofNat (nat_lit 262197835468800)), (nat_lit 1918, Int.ofNat (nat_lit 310893339187200)), (nat_lit 1919, Int.ofNat (nat_lit 359588842905600)), (nat_lit 1928, Int.ofNat (nat_lit 101123730892800)), (nat_lit 1929, Int.ofNat (nat_lit 189544167714528)), (nat_lit 1930, Int.ofNat (nat_lit 178502897027664)), (nat_lit 1931, Int.ofNat (nat_lit 194088787209504)), (nat_lit 1932, Int.ofNat (nat_lit 217928398463424)), (nat_lit 1933, Int.ofNat (nat_lit 208267937539200)), (nat_lit 1934, Int.ofNat (nat_lit 194933213798400)), (nat_lit 1935, Int.ofNat (nat_lit 196385496652800)), (nat_lit 1936, Int.ofNat (nat_lit 186015269260800)), (nat_lit 1937, Int.ofNat (nat_lit 185577780326400)), (nat_lit 1938, Int.ofNat (nat_lit 228846660134400)), (nat_lit 1939, Int.ofNat (nat_lit 213473981952000)), (nat_lit 1940, Int.ofNat (nat_lit 283150698969600)), (nat_lit 1941, Int.ofNat (nat_lit 308346582297600)), (nat_lit 1942, Int.ofNat (nat_lit 369858557376000)), (nat_lit 1943, Int.ofNat (nat_lit 431370532454400)), (nat_lit 1953, Int.ofNat (nat_lit 126437516476128)), (nat_lit 1954, Int.ofNat (nat_lit 239751911272896)), (nat_lit 1955, Int.ofNat (nat_lit 231275379769632)), (nat_lit 1956, Int.ofNat (nat_lit 256178108463552)), (nat_lit 1957, Int.ofNat (nat_lit 241414683827328)), (nat_lit 1958, Int.ofNat (nat_lit 226060036950528)), (nat_lit 1959, Int.ofNat (nat_lit 225492396668928)), (nat_lit 1960, Int.ofNat (nat_lit 213102246140928)), (nat_lit 1961, Int.ofNat (nat_lit 210644834070528)), (nat_lit 1962, Int.ofNat (nat_lit 254097258573312)), (nat_lit 1963, Int.ofNat (nat_lit 241111592916480)), (nat_lit 1964, Int.ofNat (nat_lit 313175322459648)), (nat_lit 1965, Int.ofNat (nat_lit 345165153974784)), (nat_lit 1966, Int.ofNat (nat_lit 413471077240320)), (nat_lit 1967, Int.ofNat (nat_lit 481777000505856)), (nat_lit 1978, Int.ofNat (nat_lit 151331474451168)), (nat_lit 1979, Int.ofNat (nat_lit 298353837763872)), (nat_lit 1980, Int.ofNat (nat_lit 317133010003392)), (nat_lit 1981, Int.ofNat (nat_lit 302412110064768)), (nat_lit 1982, Int.ofNat (nat_lit 284016947309568)), (nat_lit 1983, Int.ofNat (nat_lit 280408791149568)), (nat_lit 1984, Int.ofNat (nat_lit 264978124743168)), (nat_lit 1985, Int.ofNat (nat_lit 259480196794368)), (nat_lit 1986, Int.ofNat (nat_lit 298624869430272)), (nat_lit 1987, Int.ofNat (nat_lit 280064215918080)), (nat_lit 1988, Int.ofNat (nat_lit 346552957605888)), (nat_lit 1989, Int.ofNat (nat_lit 370433329288704)), (nat_lit 1990, Int.ofNat (nat_lit 430629792721920)), (nat_lit 1991, Int.ofNat (nat_lit 490826256155136)), (nat_lit 2003, Int.ofNat (nat_lit 191205524119104)), (nat_lit 2004, Int.ofNat (nat_lit 377351140782528))]
theorem block016_data_flat159_step : block016_data_flat159 = (CoefficientMerge.trim block016_data_flat158) := by decide +kernel
theorem block016_data_flat159_original : block016_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (101846650752000 : Int) atom1089Coded) (CoefficientMerge.scale (105562098127728 : Int) atom1090Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125826931427472 : Int) atom1091Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136085099683104 : Int) atom1092Coded) (CoefficientMerge.scale (161923371724224 : Int) atom1093Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153240978844800 : Int) atom1094Coded) (CoefficientMerge.scale (140884323148800 : Int) atom1095Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (143314674048000 : Int) atom1096Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (133922514700800 : Int) atom1097Coded) (CoefficientMerge.scale (134463093811200 : Int) atom1098Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (172926682790400 : Int) atom1099Coded) (CoefficientMerge.scale (146965354905600 : Int) atom1100Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (206053422220800 : Int) atom1101Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (209093938099200 : Int) atom1102Coded) (CoefficientMerge.scale (248450545728000 : Int) atom1103Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (287807153356800 : Int) atom1104Coded) (CoefficientMerge.scale (81912017510400 : Int) atom1105Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (148101709324800 : Int) atom1106Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135383723561328 : Int) atom1107Coded) (CoefficientMerge.scale (153607371376272 : Int) atom1108Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (165949249814304 : Int) atom1109Coded) (CoefficientMerge.scale (193871232037824 : Int) atom1110Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (185210101507200 : Int) atom1111Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172874708160000 : Int) atom1112Coded) (CoefficientMerge.scale (175326321408000 : Int) atom1113Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (165955424409600 : Int) atom1114Coded) (CoefficientMerge.scale (166517265868800 : Int) atom1115Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207331525632000 : Int) atom1116Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (186050276966400 : Int) atom1117Coded) (CoefficientMerge.scale (249818423500800 : Int) atom1118Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (262197835468800 : Int) atom1119Coded) (CoefficientMerge.scale (310893339187200 : Int) atom1120Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (359588842905600 : Int) atom1121Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101123730892800 : Int) atom1122Coded) (CoefficientMerge.scale (189544167714528 : Int) atom1123Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (178502897027664 : Int) atom1124Coded) (CoefficientMerge.scale (194088787209504 : Int) atom1125Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (217928398463424 : Int) atom1126Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (208267937539200 : Int) atom1127Coded) (CoefficientMerge.scale (194933213798400 : Int) atom1128Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (196385496652800 : Int) atom1129Coded) (CoefficientMerge.scale (186015269260800 : Int) atom1130Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (185577780326400 : Int) atom1131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (228846660134400 : Int) atom1132Coded) (CoefficientMerge.scale (213473981952000 : Int) atom1133Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (283150698969600 : Int) atom1134Coded) (CoefficientMerge.scale (308346582297600 : Int) atom1135Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (369858557376000 : Int) atom1136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (431370532454400 : Int) atom1137Coded) (CoefficientMerge.scale (126437516476128 : Int) atom1138Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (239751911272896 : Int) atom1139Coded) (CoefficientMerge.scale (231275379769632 : Int) atom1140Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256178108463552 : Int) atom1141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241414683827328 : Int) atom1142Coded) (CoefficientMerge.scale (226060036950528 : Int) atom1143Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (225492396668928 : Int) atom1144Coded) (CoefficientMerge.scale (213102246140928 : Int) atom1145Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210644834070528 : Int) atom1146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254097258573312 : Int) atom1147Coded) (CoefficientMerge.scale (241111592916480 : Int) atom1148Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (313175322459648 : Int) atom1149Coded) (CoefficientMerge.scale (345165153974784 : Int) atom1150Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413471077240320 : Int) atom1151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (481777000505856 : Int) atom1152Coded) (CoefficientMerge.scale (151331474451168 : Int) atom1153Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (298353837763872 : Int) atom1154Coded) (CoefficientMerge.scale (317133010003392 : Int) atom1155Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (302412110064768 : Int) atom1156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284016947309568 : Int) atom1157Coded) (CoefficientMerge.scale (280408791149568 : Int) atom1158Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (264978124743168 : Int) atom1159Coded) (CoefficientMerge.scale (259480196794368 : Int) atom1160Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298624869430272 : Int) atom1161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (280064215918080 : Int) atom1162Coded) (CoefficientMerge.scale (346552957605888 : Int) atom1163Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (370433329288704 : Int) atom1164Coded) (CoefficientMerge.scale (430629792721920 : Int) atom1165Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (490826256155136 : Int) atom1166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191205524119104 : Int) atom1167Coded) (CoefficientMerge.scale (377351140782528 : Int) atom1168Coded))))))))) := by
  rw [block016_data_flat159_step, block016_data_flat158_original]
theorem block016_data : block016 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (101846650752000 : Int) atom1089Coded) (CoefficientMerge.scale (105562098127728 : Int) atom1090Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (125826931427472 : Int) atom1091Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (136085099683104 : Int) atom1092Coded) (CoefficientMerge.scale (161923371724224 : Int) atom1093Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (153240978844800 : Int) atom1094Coded) (CoefficientMerge.scale (140884323148800 : Int) atom1095Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (143314674048000 : Int) atom1096Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (133922514700800 : Int) atom1097Coded) (CoefficientMerge.scale (134463093811200 : Int) atom1098Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (172926682790400 : Int) atom1099Coded) (CoefficientMerge.scale (146965354905600 : Int) atom1100Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (206053422220800 : Int) atom1101Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (209093938099200 : Int) atom1102Coded) (CoefficientMerge.scale (248450545728000 : Int) atom1103Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (287807153356800 : Int) atom1104Coded) (CoefficientMerge.scale (81912017510400 : Int) atom1105Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (148101709324800 : Int) atom1106Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (135383723561328 : Int) atom1107Coded) (CoefficientMerge.scale (153607371376272 : Int) atom1108Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (165949249814304 : Int) atom1109Coded) (CoefficientMerge.scale (193871232037824 : Int) atom1110Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (185210101507200 : Int) atom1111Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (172874708160000 : Int) atom1112Coded) (CoefficientMerge.scale (175326321408000 : Int) atom1113Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (165955424409600 : Int) atom1114Coded) (CoefficientMerge.scale (166517265868800 : Int) atom1115Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (207331525632000 : Int) atom1116Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (186050276966400 : Int) atom1117Coded) (CoefficientMerge.scale (249818423500800 : Int) atom1118Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (262197835468800 : Int) atom1119Coded) (CoefficientMerge.scale (310893339187200 : Int) atom1120Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (359588842905600 : Int) atom1121Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (101123730892800 : Int) atom1122Coded) (CoefficientMerge.scale (189544167714528 : Int) atom1123Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (178502897027664 : Int) atom1124Coded) (CoefficientMerge.scale (194088787209504 : Int) atom1125Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (217928398463424 : Int) atom1126Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (208267937539200 : Int) atom1127Coded) (CoefficientMerge.scale (194933213798400 : Int) atom1128Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (196385496652800 : Int) atom1129Coded) (CoefficientMerge.scale (186015269260800 : Int) atom1130Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (185577780326400 : Int) atom1131Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (228846660134400 : Int) atom1132Coded) (CoefficientMerge.scale (213473981952000 : Int) atom1133Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (283150698969600 : Int) atom1134Coded) (CoefficientMerge.scale (308346582297600 : Int) atom1135Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (369858557376000 : Int) atom1136Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (431370532454400 : Int) atom1137Coded) (CoefficientMerge.scale (126437516476128 : Int) atom1138Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (239751911272896 : Int) atom1139Coded) (CoefficientMerge.scale (231275379769632 : Int) atom1140Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (256178108463552 : Int) atom1141Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241414683827328 : Int) atom1142Coded) (CoefficientMerge.scale (226060036950528 : Int) atom1143Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (225492396668928 : Int) atom1144Coded) (CoefficientMerge.scale (213102246140928 : Int) atom1145Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (210644834070528 : Int) atom1146Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (254097258573312 : Int) atom1147Coded) (CoefficientMerge.scale (241111592916480 : Int) atom1148Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (313175322459648 : Int) atom1149Coded) (CoefficientMerge.scale (345165153974784 : Int) atom1150Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413471077240320 : Int) atom1151Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (481777000505856 : Int) atom1152Coded) (CoefficientMerge.scale (151331474451168 : Int) atom1153Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (298353837763872 : Int) atom1154Coded) (CoefficientMerge.scale (317133010003392 : Int) atom1155Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (302412110064768 : Int) atom1156Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (284016947309568 : Int) atom1157Coded) (CoefficientMerge.scale (280408791149568 : Int) atom1158Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (264978124743168 : Int) atom1159Coded) (CoefficientMerge.scale (259480196794368 : Int) atom1160Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (298624869430272 : Int) atom1161Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (280064215918080 : Int) atom1162Coded) (CoefficientMerge.scale (346552957605888 : Int) atom1163Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (370433329288704 : Int) atom1164Coded) (CoefficientMerge.scale (430629792721920 : Int) atom1165Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (490826256155136 : Int) atom1166Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (191205524119104 : Int) atom1167Coded) (CoefficientMerge.scale (377351140782528 : Int) atom1168Coded)))))))) := by
  have h : block016 = block016_data_flat159 := by decide +kernel
  exact h.trans block016_data_flat159_original
theorem block016_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block016 := by
  rw [block016_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1089Coded_nonneg g hg hA hB) (atom1090Coded_nonneg g hg hA hB)) (add_nonneg (atom1091Coded_nonneg g hg hA hB) (add_nonneg (atom1092Coded_nonneg g hg hA hB) (atom1093Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1094Coded_nonneg g hg hA hB) (atom1095Coded_nonneg g hg hA hB)) (add_nonneg (atom1096Coded_nonneg g hg hA hB) (add_nonneg (atom1097Coded_nonneg g hg hA hB) (atom1098Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1099Coded_nonneg g hg hA hB) (atom1100Coded_nonneg g hg hA hB)) (add_nonneg (atom1101Coded_nonneg g hg hA hB) (add_nonneg (atom1102Coded_nonneg g hg hA hB) (atom1103Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1104Coded_nonneg g hg hA hB) (atom1105Coded_nonneg g hg hA hB)) (add_nonneg (atom1106Coded_nonneg g hg hA hB) (add_nonneg (atom1107Coded_nonneg g hg hA hB) (atom1108Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1109Coded_nonneg g hg hA hB) (atom1110Coded_nonneg g hg hA hB)) (add_nonneg (atom1111Coded_nonneg g hg hA hB) (add_nonneg (atom1112Coded_nonneg g hg hA hB) (atom1113Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1114Coded_nonneg g hg hA hB) (atom1115Coded_nonneg g hg hA hB)) (add_nonneg (atom1116Coded_nonneg g hg hA hB) (add_nonneg (atom1117Coded_nonneg g hg hA hB) (atom1118Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1119Coded_nonneg g hg hA hB) (atom1120Coded_nonneg g hg hA hB)) (add_nonneg (atom1121Coded_nonneg g hg hA hB) (add_nonneg (atom1122Coded_nonneg g hg hA hB) (atom1123Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1124Coded_nonneg g hg hA hB) (atom1125Coded_nonneg g hg hA hB)) (add_nonneg (atom1126Coded_nonneg g hg hA hB) (add_nonneg (atom1127Coded_nonneg g hg hA hB) (atom1128Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1129Coded_nonneg g hg hA hB) (atom1130Coded_nonneg g hg hA hB)) (add_nonneg (atom1131Coded_nonneg g hg hA hB) (add_nonneg (atom1132Coded_nonneg g hg hA hB) (atom1133Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1134Coded_nonneg g hg hA hB) (atom1135Coded_nonneg g hg hA hB)) (add_nonneg (atom1136Coded_nonneg g hg hA hB) (add_nonneg (atom1137Coded_nonneg g hg hA hB) (atom1138Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1139Coded_nonneg g hg hA hB) (atom1140Coded_nonneg g hg hA hB)) (add_nonneg (atom1141Coded_nonneg g hg hA hB) (add_nonneg (atom1142Coded_nonneg g hg hA hB) (atom1143Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1144Coded_nonneg g hg hA hB) (atom1145Coded_nonneg g hg hA hB)) (add_nonneg (atom1146Coded_nonneg g hg hA hB) (add_nonneg (atom1147Coded_nonneg g hg hA hB) (atom1148Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1149Coded_nonneg g hg hA hB) (atom1150Coded_nonneg g hg hA hB)) (add_nonneg (atom1151Coded_nonneg g hg hA hB) (add_nonneg (atom1152Coded_nonneg g hg hA hB) (atom1153Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1154Coded_nonneg g hg hA hB) (atom1155Coded_nonneg g hg hA hB)) (add_nonneg (atom1156Coded_nonneg g hg hA hB) (add_nonneg (atom1157Coded_nonneg g hg hA hB) (atom1158Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1159Coded_nonneg g hg hA hB) (atom1160Coded_nonneg g hg hA hB)) (add_nonneg (atom1161Coded_nonneg g hg hA hB) (add_nonneg (atom1162Coded_nonneg g hg hA hB) (atom1163Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1164Coded_nonneg g hg hA hB) (atom1165Coded_nonneg g hg hA hB)) (add_nonneg (atom1166Coded_nonneg g hg hA hB) (add_nonneg (atom1167Coded_nonneg g hg hA hB) (atom1168Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
