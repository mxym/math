-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1216 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1216 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1216 = ((g 6) * (g 9) * (g 13)) := by
  norm_num [atom1216, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1216_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2066320569600 : Int) atom1216) := by
  rw [SparsePolynomial.eval_scale, eval_atom1216]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1216Coded : CoefficientMerge.Poly := [(nat_lit 2848, Int.ofNat (nat_lit 1))]
theorem atom1216Coded_decode : atom1216 = SparsePolynomial.decodeCubic 21 atom1216Coded := by decide +kernel
theorem atom1216Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2066320569600 : Int) atom1216Coded) := by
  have h := atom1216_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1216Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1217 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1217 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1217 = ((g 6) * (g 9) * (g 14)) := by
  norm_num [atom1217, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1217_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2843362771200 : Int) atom1217) := by
  rw [SparsePolynomial.eval_scale, eval_atom1217]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1217Coded : CoefficientMerge.Poly := [(nat_lit 2849, Int.ofNat (nat_lit 1))]
theorem atom1217Coded_decode : atom1217 = SparsePolynomial.decodeCubic 21 atom1217Coded := by decide +kernel
theorem atom1217Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2843362771200 : Int) atom1217Coded) := by
  have h := atom1217_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1217Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1218 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1218 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1218 = ((g 6) * (g 9) * (g 15)) := by
  norm_num [atom1218, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1218_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12526751865600 : Int) atom1218) := by
  rw [SparsePolynomial.eval_scale, eval_atom1218]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1218Coded : CoefficientMerge.Poly := [(nat_lit 2850, Int.ofNat (nat_lit 1))]
theorem atom1218Coded_decode : atom1218 = SparsePolynomial.decodeCubic 21 atom1218Coded := by decide +kernel
theorem atom1218Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (12526751865600 : Int) atom1218Coded) := by
  have h := atom1218_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1218Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1219 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1219 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1219 = ((g 6) * (g 9) * (g 16)) := by
  norm_num [atom1219, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1219_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9755314884000 : Int) atom1219) := by
  rw [SparsePolynomial.eval_scale, eval_atom1219]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1219Coded : CoefficientMerge.Poly := [(nat_lit 2851, Int.ofNat (nat_lit 1))]
theorem atom1219Coded_decode : atom1219 = SparsePolynomial.decodeCubic 21 atom1219Coded := by decide +kernel
theorem atom1219Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9755314884000 : Int) atom1219Coded) := by
  have h := atom1219_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1219Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1220 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1220 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1220 = ((g 6) * (g 9) * (g 17)) := by
  norm_num [atom1220, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1220_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17449540819200 : Int) atom1220) := by
  rw [SparsePolynomial.eval_scale, eval_atom1220]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1220Coded : CoefficientMerge.Poly := [(nat_lit 2852, Int.ofNat (nat_lit 1))]
theorem atom1220Coded_decode : atom1220 = SparsePolynomial.decodeCubic 21 atom1220Coded := by decide +kernel
theorem atom1220Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17449540819200 : Int) atom1220Coded) := by
  have h := atom1220_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1220Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1221 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1221 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1221 = ((g 6) * (g 9) * (g 18)) := by
  norm_num [atom1221, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1221_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24820650338400 : Int) atom1221) := by
  rw [SparsePolynomial.eval_scale, eval_atom1221]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1221Coded : CoefficientMerge.Poly := [(nat_lit 2853, Int.ofNat (nat_lit 1))]
theorem atom1221Coded_decode : atom1221 = SparsePolynomial.decodeCubic 21 atom1221Coded := by decide +kernel
theorem atom1221Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24820650338400 : Int) atom1221Coded) := by
  have h := atom1221_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1221Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1222 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1222 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1222 = ((g 6) * (g 9) * (g 19)) := by
  norm_num [atom1222, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1222_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35164296367200 : Int) atom1222) := by
  rw [SparsePolynomial.eval_scale, eval_atom1222]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1222Coded : CoefficientMerge.Poly := [(nat_lit 2854, Int.ofNat (nat_lit 1))]
theorem atom1222Coded_decode : atom1222 = SparsePolynomial.decodeCubic 21 atom1222Coded := by decide +kernel
theorem atom1222Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35164296367200 : Int) atom1222Coded) := by
  have h := atom1222_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1222Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1223 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1223 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1223 = ((g 6) * (g 9) * (g 20)) := by
  norm_num [atom1223, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1223_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45787493959200 : Int) atom1223) := by
  rw [SparsePolynomial.eval_scale, eval_atom1223]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1223Coded : CoefficientMerge.Poly := [(nat_lit 2855, Int.ofNat (nat_lit 1))]
theorem atom1223Coded_decode : atom1223 = SparsePolynomial.decodeCubic 21 atom1223Coded := by decide +kernel
theorem atom1223Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (45787493959200 : Int) atom1223Coded) := by
  have h := atom1223_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1223Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1224 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1224 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1224 = ((g 6) * (g 10) * (g 10)) := by
  norm_num [atom1224, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1224_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3204336038400 : Int) atom1224) := by
  rw [SparsePolynomial.eval_scale, eval_atom1224]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1224Coded : CoefficientMerge.Poly := [(nat_lit 2866, Int.ofNat (nat_lit 1))]
theorem atom1224Coded_decode : atom1224 = SparsePolynomial.decodeCubic 21 atom1224Coded := by decide +kernel
theorem atom1224Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3204336038400 : Int) atom1224Coded) := by
  have h := atom1224_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1224Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1225 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1225 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1225 = ((g 6) * (g 10) * (g 11)) := by
  norm_num [atom1225, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1225_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5399676979200 : Int) atom1225) := by
  rw [SparsePolynomial.eval_scale, eval_atom1225]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1225Coded : CoefficientMerge.Poly := [(nat_lit 2867, Int.ofNat (nat_lit 1))]
theorem atom1225Coded_decode : atom1225 = SparsePolynomial.decodeCubic 21 atom1225Coded := by decide +kernel
theorem atom1225Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5399676979200 : Int) atom1225Coded) := by
  have h := atom1225_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1225Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1226 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1226 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1226 = ((g 6) * (g 10) * (g 12)) := by
  norm_num [atom1226, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1226_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5672221632000 : Int) atom1226) := by
  rw [SparsePolynomial.eval_scale, eval_atom1226]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1226Coded : CoefficientMerge.Poly := [(nat_lit 2868, Int.ofNat (nat_lit 1))]
theorem atom1226Coded_decode : atom1226 = SparsePolynomial.decodeCubic 21 atom1226Coded := by decide +kernel
theorem atom1226Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5672221632000 : Int) atom1226Coded) := by
  have h := atom1226_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1226Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1227 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1227 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1227 = ((g 6) * (g 10) * (g 13)) := by
  norm_num [atom1227, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1227_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6371946201600 : Int) atom1227) := by
  rw [SparsePolynomial.eval_scale, eval_atom1227]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1227Coded : CoefficientMerge.Poly := [(nat_lit 2869, Int.ofNat (nat_lit 1))]
theorem atom1227Coded_decode : atom1227 = SparsePolynomial.decodeCubic 21 atom1227Coded := by decide +kernel
theorem atom1227Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6371946201600 : Int) atom1227Coded) := by
  have h := atom1227_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1227Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1228 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1228 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1228 = ((g 6) * (g 10) * (g 14)) := by
  norm_num [atom1228, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1228_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7071670771200 : Int) atom1228) := by
  rw [SparsePolynomial.eval_scale, eval_atom1228]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1228Coded : CoefficientMerge.Poly := [(nat_lit 2870, Int.ofNat (nat_lit 1))]
theorem atom1228Coded_decode : atom1228 = SparsePolynomial.decodeCubic 21 atom1228Coded := by decide +kernel
theorem atom1228Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7071670771200 : Int) atom1228Coded) := by
  have h := atom1228_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1228Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1229 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1229 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1229 = ((g 6) * (g 10) * (g 15)) := by
  norm_num [atom1229, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1229_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17374084156800 : Int) atom1229) := by
  rw [SparsePolynomial.eval_scale, eval_atom1229]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1229Coded : CoefficientMerge.Poly := [(nat_lit 2871, Int.ofNat (nat_lit 1))]
theorem atom1229Coded_decode : atom1229 = SparsePolynomial.decodeCubic 21 atom1229Coded := by decide +kernel
theorem atom1229Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17374084156800 : Int) atom1229Coded) := by
  have h := atom1229_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1229Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1230 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1230 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1230 = ((g 6) * (g 10) * (g 16)) := by
  norm_num [atom1230, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1230_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15150394274400 : Int) atom1230) := by
  rw [SparsePolynomial.eval_scale, eval_atom1230]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1230Coded : CoefficientMerge.Poly := [(nat_lit 2872, Int.ofNat (nat_lit 1))]
theorem atom1230Coded_decode : atom1230 = SparsePolynomial.decodeCubic 21 atom1230Coded := by decide +kernel
theorem atom1230Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15150394274400 : Int) atom1230Coded) := by
  have h := atom1230_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1230Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1231 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1231 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1231 = ((g 6) * (g 10) * (g 17)) := by
  norm_num [atom1231, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1231_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25703681270400 : Int) atom1231) := by
  rw [SparsePolynomial.eval_scale, eval_atom1231]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1231Coded : CoefficientMerge.Poly := [(nat_lit 2873, Int.ofNat (nat_lit 1))]
theorem atom1231Coded_decode : atom1231 = SparsePolynomial.decodeCubic 21 atom1231Coded := by decide +kernel
theorem atom1231Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25703681270400 : Int) atom1231Coded) := by
  have h := atom1231_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1231Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1232 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1232 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1232 = ((g 6) * (g 10) * (g 18)) := by
  norm_num [atom1232, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1232_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31388299941600 : Int) atom1232) := by
  rw [SparsePolynomial.eval_scale, eval_atom1232]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1232Coded : CoefficientMerge.Poly := [(nat_lit 2874, Int.ofNat (nat_lit 1))]
theorem atom1232Coded_decode : atom1232 = SparsePolynomial.decodeCubic 21 atom1232Coded := by decide +kernel
theorem atom1232Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31388299941600 : Int) atom1232Coded) := by
  have h := atom1232_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1232Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1233 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1233 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1233 = ((g 6) * (g 10) * (g 19)) := by
  norm_num [atom1233, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1233_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42276310423200 : Int) atom1233) := by
  rw [SparsePolynomial.eval_scale, eval_atom1233]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1233Coded : CoefficientMerge.Poly := [(nat_lit 2875, Int.ofNat (nat_lit 1))]
theorem atom1233Coded_decode : atom1233 = SparsePolynomial.decodeCubic 21 atom1233Coded := by decide +kernel
theorem atom1233Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42276310423200 : Int) atom1233Coded) := by
  have h := atom1233_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1233Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1234 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 10, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1234 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1234 = ((g 6) * (g 10) * (g 20)) := by
  norm_num [atom1234, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1234_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53312311684800 : Int) atom1234) := by
  rw [SparsePolynomial.eval_scale, eval_atom1234]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1234Coded : CoefficientMerge.Poly := [(nat_lit 2876, Int.ofNat (nat_lit 1))]
theorem atom1234Coded_decode : atom1234 = SparsePolynomial.decodeCubic 21 atom1234Coded := by decide +kernel
theorem atom1234Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53312311684800 : Int) atom1234Coded) := by
  have h := atom1234_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1234Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1235 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1235 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1235 = ((g 6) * (g 11) * (g 11)) := by
  norm_num [atom1235, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1235_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5780946124800 : Int) atom1235) := by
  rw [SparsePolynomial.eval_scale, eval_atom1235]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1235Coded : CoefficientMerge.Poly := [(nat_lit 2888, Int.ofNat (nat_lit 1))]
theorem atom1235Coded_decode : atom1235 = SparsePolynomial.decodeCubic 21 atom1235Coded := by decide +kernel
theorem atom1235Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5780946124800 : Int) atom1235Coded) := by
  have h := atom1235_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1235Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1236 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1236 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1236 = ((g 6) * (g 11) * (g 12)) := by
  norm_num [atom1236, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1236_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10139247820800 : Int) atom1236) := by
  rw [SparsePolynomial.eval_scale, eval_atom1236]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1236Coded : CoefficientMerge.Poly := [(nat_lit 2889, Int.ofNat (nat_lit 1))]
theorem atom1236Coded_decode : atom1236 = SparsePolynomial.decodeCubic 21 atom1236Coded := by decide +kernel
theorem atom1236Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10139247820800 : Int) atom1236Coded) := by
  have h := atom1236_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1236Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1237 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1237 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1237 = ((g 6) * (g 11) * (g 13)) := by
  norm_num [atom1237, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1237_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10593488908800 : Int) atom1237) := by
  rw [SparsePolynomial.eval_scale, eval_atom1237]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1237Coded : CoefficientMerge.Poly := [(nat_lit 2890, Int.ofNat (nat_lit 1))]
theorem atom1237Coded_decode : atom1237 = SparsePolynomial.decodeCubic 21 atom1237Coded := by decide +kernel
theorem atom1237Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10593488908800 : Int) atom1237Coded) := by
  have h := atom1237_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1237Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1238 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1238 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1238 = ((g 6) * (g 11) * (g 14)) := by
  norm_num [atom1238, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1238_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11047729996800 : Int) atom1238) := by
  rw [SparsePolynomial.eval_scale, eval_atom1238]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1238Coded : CoefficientMerge.Poly := [(nat_lit 2891, Int.ofNat (nat_lit 1))]
theorem atom1238Coded_decode : atom1238 = SparsePolynomial.decodeCubic 21 atom1238Coded := by decide +kernel
theorem atom1238Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11047729996800 : Int) atom1238Coded) := by
  have h := atom1238_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1238Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1239 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1239 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1239 = ((g 6) * (g 11) * (g 15)) := by
  norm_num [atom1239, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1239_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21624024038400 : Int) atom1239) := by
  rw [SparsePolynomial.eval_scale, eval_atom1239]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1239Coded : CoefficientMerge.Poly := [(nat_lit 2892, Int.ofNat (nat_lit 1))]
theorem atom1239Coded_decode : atom1239 = SparsePolynomial.decodeCubic 21 atom1239Coded := by decide +kernel
theorem atom1239Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21624024038400 : Int) atom1239Coded) := by
  have h := atom1239_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1239Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1240 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1240 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1240 = ((g 6) * (g 11) * (g 16)) := by
  norm_num [atom1240, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1240_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19839379392000 : Int) atom1240) := by
  rw [SparsePolynomial.eval_scale, eval_atom1240]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1240Coded : CoefficientMerge.Poly := [(nat_lit 2893, Int.ofNat (nat_lit 1))]
theorem atom1240Coded_decode : atom1240 = SparsePolynomial.decodeCubic 21 atom1240Coded := by decide +kernel
theorem atom1240Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (19839379392000 : Int) atom1240Coded) := by
  have h := atom1240_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1240Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1241 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1241 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1241 = ((g 6) * (g 11) * (g 17)) := by
  norm_num [atom1241, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1241_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33307519795200 : Int) atom1241) := by
  rw [SparsePolynomial.eval_scale, eval_atom1241]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1241Coded : CoefficientMerge.Poly := [(nat_lit 2894, Int.ofNat (nat_lit 1))]
theorem atom1241Coded_decode : atom1241 = SparsePolynomial.decodeCubic 21 atom1241Coded := by decide +kernel
theorem atom1241Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (33307519795200 : Int) atom1241Coded) := by
  have h := atom1241_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1241Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1242 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1242 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1242 = ((g 6) * (g 11) * (g 18)) := by
  norm_num [atom1242, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1242_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36744632870400 : Int) atom1242) := by
  rw [SparsePolynomial.eval_scale, eval_atom1242]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1242Coded : CoefficientMerge.Poly := [(nat_lit 2895, Int.ofNat (nat_lit 1))]
theorem atom1242Coded_decode : atom1242 = SparsePolynomial.decodeCubic 21 atom1242Coded := by decide +kernel
theorem atom1242Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (36744632870400 : Int) atom1242Coded) := by
  have h := atom1242_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1242Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1243 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1243 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1243 = ((g 6) * (g 11) * (g 19)) := by
  norm_num [atom1243, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1243_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47909475532800 : Int) atom1243) := by
  rw [SparsePolynomial.eval_scale, eval_atom1243]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1243Coded : CoefficientMerge.Poly := [(nat_lit 2896, Int.ofNat (nat_lit 1))]
theorem atom1243Coded_decode : atom1243 = SparsePolynomial.decodeCubic 21 atom1243Coded := by decide +kernel
theorem atom1243Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47909475532800 : Int) atom1243Coded) := by
  have h := atom1243_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1243Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1244 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1244 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1244 = ((g 6) * (g 11) * (g 20)) := by
  norm_num [atom1244, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1244_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59097361881600 : Int) atom1244) := by
  rw [SparsePolynomial.eval_scale, eval_atom1244]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1244Coded : CoefficientMerge.Poly := [(nat_lit 2897, Int.ofNat (nat_lit 1))]
theorem atom1244Coded_decode : atom1244 = SparsePolynomial.decodeCubic 21 atom1244Coded := by decide +kernel
theorem atom1244Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (59097361881600 : Int) atom1244Coded) := by
  have h := atom1244_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1244Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1245 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1245 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1245 = ((g 6) * (g 12) * (g 12)) := by
  norm_num [atom1245, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1245_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8371086796800 : Int) atom1245) := by
  rw [SparsePolynomial.eval_scale, eval_atom1245]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1245Coded : CoefficientMerge.Poly := [(nat_lit 2910, Int.ofNat (nat_lit 1))]
theorem atom1245Coded_decode : atom1245 = SparsePolynomial.decodeCubic 21 atom1245Coded := by decide +kernel
theorem atom1245Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8371086796800 : Int) atom1245Coded) := by
  have h := atom1245_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1245Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1246 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1246 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1246 = ((g 6) * (g 12) * (g 13)) := by
  norm_num [atom1246, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1246_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16355585433600 : Int) atom1246) := by
  rw [SparsePolynomial.eval_scale, eval_atom1246]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1246Coded : CoefficientMerge.Poly := [(nat_lit 2911, Int.ofNat (nat_lit 1))]
theorem atom1246Coded_decode : atom1246 = SparsePolynomial.decodeCubic 21 atom1246Coded := by decide +kernel
theorem atom1246Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16355585433600 : Int) atom1246Coded) := by
  have h := atom1246_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1246Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1247 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1247 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1247 = ((g 6) * (g 12) * (g 14)) := by
  norm_num [atom1247, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1247_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16396177190400 : Int) atom1247) := by
  rw [SparsePolynomial.eval_scale, eval_atom1247]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1247Coded : CoefficientMerge.Poly := [(nat_lit 2912, Int.ofNat (nat_lit 1))]
theorem atom1247Coded_decode : atom1247 = SparsePolynomial.decodeCubic 21 atom1247Coded := by decide +kernel
theorem atom1247Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16396177190400 : Int) atom1247Coded) := by
  have h := atom1247_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1247Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1248 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1248 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1248 = ((g 6) * (g 12) * (g 15)) := by
  norm_num [atom1248, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1248_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22971182707200 : Int) atom1248) := by
  rw [SparsePolynomial.eval_scale, eval_atom1248]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1248Coded : CoefficientMerge.Poly := [(nat_lit 2913, Int.ofNat (nat_lit 1))]
theorem atom1248Coded_decode : atom1248 = SparsePolynomial.decodeCubic 21 atom1248Coded := by decide +kernel
theorem atom1248Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (22971182707200 : Int) atom1248Coded) := by
  have h := atom1248_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1248Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1249 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1249 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1249 = ((g 6) * (g 12) * (g 16)) := by
  norm_num [atom1249, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1249_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23375330316800 : Int) atom1249) := by
  rw [SparsePolynomial.eval_scale, eval_atom1249]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1249Coded : CoefficientMerge.Poly := [(nat_lit 2914, Int.ofNat (nat_lit 1))]
theorem atom1249Coded_decode : atom1249 = SparsePolynomial.decodeCubic 21 atom1249Coded := by decide +kernel
theorem atom1249Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23375330316800 : Int) atom1249Coded) := by
  have h := atom1249_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1249Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1250 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1250 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1250 = ((g 6) * (g 12) * (g 17)) := by
  norm_num [atom1250, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1250_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35615926976000 : Int) atom1250) := by
  rw [SparsePolynomial.eval_scale, eval_atom1250]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1250Coded : CoefficientMerge.Poly := [(nat_lit 2915, Int.ofNat (nat_lit 1))]
theorem atom1250Coded_decode : atom1250 = SparsePolynomial.decodeCubic 21 atom1250Coded := by decide +kernel
theorem atom1250Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35615926976000 : Int) atom1250Coded) := by
  have h := atom1250_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1250Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1251 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1251 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1251 = ((g 6) * (g 12) * (g 18)) := by
  norm_num [atom1251, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1251_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39881932652800 : Int) atom1251) := by
  rw [SparsePolynomial.eval_scale, eval_atom1251]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1251Coded : CoefficientMerge.Poly := [(nat_lit 2916, Int.ofNat (nat_lit 1))]
theorem atom1251Coded_decode : atom1251 = SparsePolynomial.decodeCubic 21 atom1251Coded := by decide +kernel
theorem atom1251Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39881932652800 : Int) atom1251Coded) := by
  have h := atom1251_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1251Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1252 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1252 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1252 = ((g 6) * (g 12) * (g 19)) := by
  norm_num [atom1252, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1252_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50170991001600 : Int) atom1252) := by
  rw [SparsePolynomial.eval_scale, eval_atom1252]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1252Coded : CoefficientMerge.Poly := [(nat_lit 2917, Int.ofNat (nat_lit 1))]
theorem atom1252Coded_decode : atom1252 = SparsePolynomial.decodeCubic 21 atom1252Coded := by decide +kernel
theorem atom1252Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50170991001600 : Int) atom1252Coded) := by
  have h := atom1252_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1252Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1253 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1253 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1253 = ((g 6) * (g 12) * (g 20)) := by
  norm_num [atom1253, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1253_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (61314928214400 : Int) atom1253) := by
  rw [SparsePolynomial.eval_scale, eval_atom1253]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1253Coded : CoefficientMerge.Poly := [(nat_lit 2918, Int.ofNat (nat_lit 1))]
theorem atom1253Coded_decode : atom1253 = SparsePolynomial.decodeCubic 21 atom1253Coded := by decide +kernel
theorem atom1253Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (61314928214400 : Int) atom1253Coded) := by
  have h := atom1253_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1253Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1254 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1254 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1254 = ((g 6) * (g 13) * (g 13)) := by
  norm_num [atom1254, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1254_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11705777856000 : Int) atom1254) := by
  rw [SparsePolynomial.eval_scale, eval_atom1254]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1254Coded : CoefficientMerge.Poly := [(nat_lit 2932, Int.ofNat (nat_lit 1))]
theorem atom1254Coded_decode : atom1254 = SparsePolynomial.decodeCubic 21 atom1254Coded := by decide +kernel
theorem atom1254Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (11705777856000 : Int) atom1254Coded) := by
  have h := atom1254_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1254Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1255 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1255 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1255 = ((g 6) * (g 13) * (g 14)) := by
  norm_num [atom1255, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1255_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21699798566400 : Int) atom1255) := by
  rw [SparsePolynomial.eval_scale, eval_atom1255]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1255Coded : CoefficientMerge.Poly := [(nat_lit 2933, Int.ofNat (nat_lit 1))]
theorem atom1255Coded_decode : atom1255 = SparsePolynomial.decodeCubic 21 atom1255Coded := by decide +kernel
theorem atom1255Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (21699798566400 : Int) atom1255Coded) := by
  have h := atom1255_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1255Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1256 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1256 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1256 = ((g 6) * (g 13) * (g 15)) := by
  norm_num [atom1256, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1256_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27731989051200 : Int) atom1256) := by
  rw [SparsePolynomial.eval_scale, eval_atom1256]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1256Coded : CoefficientMerge.Poly := [(nat_lit 2934, Int.ofNat (nat_lit 1))]
theorem atom1256Coded_decode : atom1256 = SparsePolynomial.decodeCubic 21 atom1256Coded := by decide +kernel
theorem atom1256Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27731989051200 : Int) atom1256Coded) := by
  have h := atom1256_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1256Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1257 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1257 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1257 = ((g 6) * (g 13) * (g 16)) := by
  norm_num [atom1257, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1257_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27457319044800 : Int) atom1257) := by
  rw [SparsePolynomial.eval_scale, eval_atom1257]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1257Coded : CoefficientMerge.Poly := [(nat_lit 2935, Int.ofNat (nat_lit 1))]
theorem atom1257Coded_decode : atom1257 = SparsePolynomial.decodeCubic 21 atom1257Coded := by decide +kernel
theorem atom1257Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (27457319044800 : Int) atom1257Coded) := by
  have h := atom1257_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1257Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1258 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1258 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1258 = ((g 6) * (g 13) * (g 17)) := by
  norm_num [atom1258, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1258_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42282031276800 : Int) atom1258) := by
  rw [SparsePolynomial.eval_scale, eval_atom1258]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1258Coded : CoefficientMerge.Poly := [(nat_lit 2936, Int.ofNat (nat_lit 1))]
theorem atom1258Coded_decode : atom1258 = SparsePolynomial.decodeCubic 21 atom1258Coded := by decide +kernel
theorem atom1258Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (42282031276800 : Int) atom1258Coded) := by
  have h := atom1258_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1258Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1259 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1259 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1259 = ((g 6) * (g 13) * (g 18)) := by
  norm_num [atom1259, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1259_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47812699267200 : Int) atom1259) := by
  rw [SparsePolynomial.eval_scale, eval_atom1259]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1259Coded : CoefficientMerge.Poly := [(nat_lit 2937, Int.ofNat (nat_lit 1))]
theorem atom1259Coded_decode : atom1259 = SparsePolynomial.decodeCubic 21 atom1259Coded := by decide +kernel
theorem atom1259Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47812699267200 : Int) atom1259Coded) := by
  have h := atom1259_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1259Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1260 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1260 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1260 = ((g 6) * (g 13) * (g 19)) := by
  norm_num [atom1260, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1260_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51497513812800 : Int) atom1260) := by
  rw [SparsePolynomial.eval_scale, eval_atom1260]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1260Coded : CoefficientMerge.Poly := [(nat_lit 2938, Int.ofNat (nat_lit 1))]
theorem atom1260Coded_decode : atom1260 = SparsePolynomial.decodeCubic 21 atom1260Coded := by decide +kernel
theorem atom1260Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (51497513812800 : Int) atom1260Coded) := by
  have h := atom1260_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1260Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1261 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1261 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1261 = ((g 6) * (g 13) * (g 20)) := by
  norm_num [atom1261, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1261_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68517790488000 : Int) atom1261) := by
  rw [SparsePolynomial.eval_scale, eval_atom1261]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1261Coded : CoefficientMerge.Poly := [(nat_lit 2939, Int.ofNat (nat_lit 1))]
theorem atom1261Coded_decode : atom1261 = SparsePolynomial.decodeCubic 21 atom1261Coded := by decide +kernel
theorem atom1261Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (68517790488000 : Int) atom1261Coded) := by
  have h := atom1261_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1261Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1262 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1262 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1262 = ((g 6) * (g 14) * (g 14)) := by
  norm_num [atom1262, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1262_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15983651980800 : Int) atom1262) := by
  rw [SparsePolynomial.eval_scale, eval_atom1262]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1262Coded : CoefficientMerge.Poly := [(nat_lit 2954, Int.ofNat (nat_lit 1))]
theorem atom1262Coded_decode : atom1262 = SparsePolynomial.decodeCubic 21 atom1262Coded := by decide +kernel
theorem atom1262Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (15983651980800 : Int) atom1262Coded) := by
  have h := atom1262_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1262Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1263 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1263 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1263 = ((g 6) * (g 14) * (g 15)) := by
  norm_num [atom1263, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1263_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32380953292800 : Int) atom1263) := by
  rw [SparsePolynomial.eval_scale, eval_atom1263]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1263Coded : CoefficientMerge.Poly := [(nat_lit 2955, Int.ofNat (nat_lit 1))]
theorem atom1263Coded_decode : atom1263 = SparsePolynomial.decodeCubic 21 atom1263Coded := by decide +kernel
theorem atom1263Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32380953292800 : Int) atom1263Coded) := by
  have h := atom1263_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1263Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1264 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1264 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1264 = ((g 6) * (g 14) * (g 16)) := by
  norm_num [atom1264, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1264_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31420158336000 : Int) atom1264) := by
  rw [SparsePolynomial.eval_scale, eval_atom1264]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1264Coded : CoefficientMerge.Poly := [(nat_lit 2956, Int.ofNat (nat_lit 1))]
theorem atom1264Coded_decode : atom1264 = SparsePolynomial.decodeCubic 21 atom1264Coded := by decide +kernel
theorem atom1264Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (31420158336000 : Int) atom1264Coded) := by
  have h := atom1264_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1264Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1265 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1265 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1265 = ((g 6) * (g 14) * (g 17)) := by
  norm_num [atom1265, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1265_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51141665433600 : Int) atom1265) := by
  rw [SparsePolynomial.eval_scale, eval_atom1265]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1265Coded : CoefficientMerge.Poly := [(nat_lit 2957, Int.ofNat (nat_lit 1))]
theorem atom1265Coded_decode : atom1265 = SparsePolynomial.decodeCubic 21 atom1265Coded := by decide +kernel
theorem atom1265Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (51141665433600 : Int) atom1265Coded) := by
  have h := atom1265_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1265Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1266 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1266 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1266 = ((g 6) * (g 14) * (g 18)) := by
  norm_num [atom1266, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1266_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58156348723200 : Int) atom1266) := by
  rw [SparsePolynomial.eval_scale, eval_atom1266]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1266Coded : CoefficientMerge.Poly := [(nat_lit 2958, Int.ofNat (nat_lit 1))]
theorem atom1266Coded_decode : atom1266 = SparsePolynomial.decodeCubic 21 atom1266Coded := by decide +kernel
theorem atom1266Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (58156348723200 : Int) atom1266Coded) := by
  have h := atom1266_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1266Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1267 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1267 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1267 = ((g 6) * (g 14) * (g 19)) := by
  norm_num [atom1267, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1267_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57274763212800 : Int) atom1267) := by
  rw [SparsePolynomial.eval_scale, eval_atom1267]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1267Coded : CoefficientMerge.Poly := [(nat_lit 2959, Int.ofNat (nat_lit 1))]
theorem atom1267Coded_decode : atom1267 = SparsePolynomial.decodeCubic 21 atom1267Coded := by decide +kernel
theorem atom1267Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (57274763212800 : Int) atom1267Coded) := by
  have h := atom1267_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1267Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1268 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1268 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1268 = ((g 6) * (g 14) * (g 20)) := by
  norm_num [atom1268, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1268_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (80303655398400 : Int) atom1268) := by
  rw [SparsePolynomial.eval_scale, eval_atom1268]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1268Coded : CoefficientMerge.Poly := [(nat_lit 2960, Int.ofNat (nat_lit 1))]
theorem atom1268Coded_decode : atom1268 = SparsePolynomial.decodeCubic 21 atom1268Coded := by decide +kernel
theorem atom1268Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (80303655398400 : Int) atom1268Coded) := by
  have h := atom1268_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1268Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1269 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1269 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1269 = ((g 6) * (g 15) * (g 15)) := by
  norm_num [atom1269, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1269_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23458334054400 : Int) atom1269) := by
  rw [SparsePolynomial.eval_scale, eval_atom1269]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1269Coded : CoefficientMerge.Poly := [(nat_lit 2976, Int.ofNat (nat_lit 1))]
theorem atom1269Coded_decode : atom1269 = SparsePolynomial.decodeCubic 21 atom1269Coded := by decide +kernel
theorem atom1269Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23458334054400 : Int) atom1269Coded) := by
  have h := atom1269_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1269Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1270 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1270 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1270 = ((g 6) * (g 15) * (g 16)) := by
  norm_num [atom1270, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1270_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44424079257600 : Int) atom1270) := by
  rw [SparsePolynomial.eval_scale, eval_atom1270]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1270Coded : CoefficientMerge.Poly := [(nat_lit 2977, Int.ofNat (nat_lit 1))]
theorem atom1270Coded_decode : atom1270 = SparsePolynomial.decodeCubic 21 atom1270Coded := by decide +kernel
theorem atom1270Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44424079257600 : Int) atom1270Coded) := by
  have h := atom1270_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1270Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1271 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1271 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1271 = ((g 6) * (g 15) * (g 17)) := by
  norm_num [atom1271, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1271_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68201800934400 : Int) atom1271) := by
  rw [SparsePolynomial.eval_scale, eval_atom1271]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1271Coded : CoefficientMerge.Poly := [(nat_lit 2978, Int.ofNat (nat_lit 1))]
theorem atom1271Coded_decode : atom1271 = SparsePolynomial.decodeCubic 21 atom1271Coded := by decide +kernel
theorem atom1271Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (68201800934400 : Int) atom1271Coded) := by
  have h := atom1271_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1271Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1272 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1272 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1272 = ((g 6) * (g 15) * (g 18)) := by
  norm_num [atom1272, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1272_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (70646230771200 : Int) atom1272) := by
  rw [SparsePolynomial.eval_scale, eval_atom1272]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1272Coded : CoefficientMerge.Poly := [(nat_lit 2979, Int.ofNat (nat_lit 1))]
theorem atom1272Coded_decode : atom1272 = SparsePolynomial.decodeCubic 21 atom1272Coded := by decide +kernel
theorem atom1272Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (70646230771200 : Int) atom1272Coded) := by
  have h := atom1272_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1272Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1273 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1273 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1273 = ((g 6) * (g 15) * (g 19)) := by
  norm_num [atom1273, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1273_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52545926361600 : Int) atom1273) := by
  rw [SparsePolynomial.eval_scale, eval_atom1273]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1273Coded : CoefficientMerge.Poly := [(nat_lit 2980, Int.ofNat (nat_lit 1))]
theorem atom1273Coded_decode : atom1273 = SparsePolynomial.decodeCubic 21 atom1273Coded := by decide +kernel
theorem atom1273Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52545926361600 : Int) atom1273Coded) := by
  have h := atom1273_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1273Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1274 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1274 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1274 = ((g 6) * (g 15) * (g 20)) := by
  norm_num [atom1274, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1274_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (79011669542400 : Int) atom1274) := by
  rw [SparsePolynomial.eval_scale, eval_atom1274]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1274Coded : CoefficientMerge.Poly := [(nat_lit 2981, Int.ofNat (nat_lit 1))]
theorem atom1274Coded_decode : atom1274 = SparsePolynomial.decodeCubic 21 atom1274Coded := by decide +kernel
theorem atom1274Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (79011669542400 : Int) atom1274Coded) := by
  have h := atom1274_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1274Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1275 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1275 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1275 = ((g 6) * (g 16) * (g 16)) := by
  norm_num [atom1275, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1275_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17545854735360 : Int) atom1275) := by
  rw [SparsePolynomial.eval_scale, eval_atom1275]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1275Coded : CoefficientMerge.Poly := [(nat_lit 2998, Int.ofNat (nat_lit 1))]
theorem atom1275Coded_decode : atom1275 = SparsePolynomial.decodeCubic 21 atom1275Coded := by decide +kernel
theorem atom1275Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (17545854735360 : Int) atom1275Coded) := by
  have h := atom1275_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1275Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1276 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1276 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1276 = ((g 6) * (g 16) * (g 17)) := by
  norm_num [atom1276, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1276_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55664911411200 : Int) atom1276) := by
  rw [SparsePolynomial.eval_scale, eval_atom1276]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1276Coded : CoefficientMerge.Poly := [(nat_lit 2999, Int.ofNat (nat_lit 1))]
theorem atom1276Coded_decode : atom1276 = SparsePolynomial.decodeCubic 21 atom1276Coded := by decide +kernel
theorem atom1276Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (55664911411200 : Int) atom1276Coded) := by
  have h := atom1276_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1276Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1277 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1277 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1277 = ((g 6) * (g 16) * (g 18)) := by
  norm_num [atom1277, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1277_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60106665427200 : Int) atom1277) := by
  rw [SparsePolynomial.eval_scale, eval_atom1277]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1277Coded : CoefficientMerge.Poly := [(nat_lit 3000, Int.ofNat (nat_lit 1))]
theorem atom1277Coded_decode : atom1277 = SparsePolynomial.decodeCubic 21 atom1277Coded := by decide +kernel
theorem atom1277Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (60106665427200 : Int) atom1277Coded) := by
  have h := atom1277_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1277Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1278 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1278 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1278 = ((g 6) * (g 16) * (g 19)) := by
  norm_num [atom1278, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1278_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46866713241600 : Int) atom1278) := by
  rw [SparsePolynomial.eval_scale, eval_atom1278]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1278Coded : CoefficientMerge.Poly := [(nat_lit 3001, Int.ofNat (nat_lit 1))]
theorem atom1278Coded_decode : atom1278 = SparsePolynomial.decodeCubic 21 atom1278Coded := by decide +kernel
theorem atom1278Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46866713241600 : Int) atom1278Coded) := by
  have h := atom1278_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1278Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1279 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1279 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1279 = ((g 6) * (g 16) * (g 20)) := by
  norm_num [atom1279, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1279_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57384114883200 : Int) atom1279) := by
  rw [SparsePolynomial.eval_scale, eval_atom1279]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1279Coded : CoefficientMerge.Poly := [(nat_lit 3002, Int.ofNat (nat_lit 1))]
theorem atom1279Coded_decode : atom1279 = SparsePolynomial.decodeCubic 21 atom1279Coded := by decide +kernel
theorem atom1279Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (57384114883200 : Int) atom1279Coded) := by
  have h := atom1279_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1279Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1280 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1280 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1280 = ((g 6) * (g 17) * (g 17)) := by
  norm_num [atom1280, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1280_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40457273472000 : Int) atom1280) := by
  rw [SparsePolynomial.eval_scale, eval_atom1280]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1280Coded : CoefficientMerge.Poly := [(nat_lit 3020, Int.ofNat (nat_lit 1))]
theorem atom1280Coded_decode : atom1280 = SparsePolynomial.decodeCubic 21 atom1280Coded := by decide +kernel
theorem atom1280Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40457273472000 : Int) atom1280Coded) := by
  have h := atom1280_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1280Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1281 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1281 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1281 = ((g 6) * (g 17) * (g 18)) := by
  norm_num [atom1281, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1281_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (65177036467200 : Int) atom1281) := by
  rw [SparsePolynomial.eval_scale, eval_atom1281]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1281Coded : CoefficientMerge.Poly := [(nat_lit 3021, Int.ofNat (nat_lit 1))]
theorem atom1281Coded_decode : atom1281 = SparsePolynomial.decodeCubic 21 atom1281Coded := by decide +kernel
theorem atom1281Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (65177036467200 : Int) atom1281Coded) := by
  have h := atom1281_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1281Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1282 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1282 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1282 = ((g 6) * (g 17) * (g 19)) := by
  norm_num [atom1282, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1282_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (46861654694400 : Int) atom1282) := by
  rw [SparsePolynomial.eval_scale, eval_atom1282]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1282Coded : CoefficientMerge.Poly := [(nat_lit 3022, Int.ofNat (nat_lit 1))]
theorem atom1282Coded_decode : atom1282 = SparsePolynomial.decodeCubic 21 atom1282Coded := by decide +kernel
theorem atom1282Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (46861654694400 : Int) atom1282Coded) := by
  have h := atom1282_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1282Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1283 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1283 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1283 = ((g 6) * (g 17) * (g 20)) := by
  norm_num [atom1283, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1283_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53756858937600 : Int) atom1283) := by
  rw [SparsePolynomial.eval_scale, eval_atom1283]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1283Coded : CoefficientMerge.Poly := [(nat_lit 3023, Int.ofNat (nat_lit 1))]
theorem atom1283Coded_decode : atom1283 = SparsePolynomial.decodeCubic 21 atom1283Coded := by decide +kernel
theorem atom1283Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53756858937600 : Int) atom1283Coded) := by
  have h := atom1283_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1283Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1284 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1284 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1284 = ((g 6) * (g 18) * (g 18)) := by
  norm_num [atom1284, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1284_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18855796377600 : Int) atom1284) := by
  rw [SparsePolynomial.eval_scale, eval_atom1284]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1284Coded : CoefficientMerge.Poly := [(nat_lit 3042, Int.ofNat (nat_lit 1))]
theorem atom1284Coded_decode : atom1284 = SparsePolynomial.decodeCubic 21 atom1284Coded := by decide +kernel
theorem atom1284Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18855796377600 : Int) atom1284Coded) := by
  have h := atom1284_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1284Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1285 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1285 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1285 = ((g 6) * (g 18) * (g 19)) := by
  norm_num [atom1285, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1285_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24005993760000 : Int) atom1285) := by
  rw [SparsePolynomial.eval_scale, eval_atom1285]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1285Coded : CoefficientMerge.Poly := [(nat_lit 3043, Int.ofNat (nat_lit 1))]
theorem atom1285Coded_decode : atom1285 = SparsePolynomial.decodeCubic 21 atom1285Coded := by decide +kernel
theorem atom1285Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (24005993760000 : Int) atom1285Coded) := by
  have h := atom1285_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1285Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1286 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1286 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1286 = ((g 6) * (g 18) * (g 20)) := by
  norm_num [atom1286, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1286_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30962904739200 : Int) atom1286) := by
  rw [SparsePolynomial.eval_scale, eval_atom1286]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1286Coded : CoefficientMerge.Poly := [(nat_lit 3044, Int.ofNat (nat_lit 1))]
theorem atom1286Coded_decode : atom1286 = SparsePolynomial.decodeCubic 21 atom1286Coded := by decide +kernel
theorem atom1286Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30962904739200 : Int) atom1286Coded) := by
  have h := atom1286_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1286Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1287 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1287 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1287 = ((g 7) * (g 7) * (g 7)) := by
  norm_num [atom1287, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1287_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2264279068800 : Int) atom1287) := by
  rw [SparsePolynomial.eval_scale, eval_atom1287]
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 7) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1287Coded : CoefficientMerge.Poly := [(nat_lit 3241, Int.ofNat (nat_lit 1))]
theorem atom1287Coded_decode : atom1287 = SparsePolynomial.decodeCubic 21 atom1287Coded := by decide +kernel
theorem atom1287Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2264279068800 : Int) atom1287Coded) := by
  have h := atom1287_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1287Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1288 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1288 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1288 = ((g 7) * (g 7) * (g 8)) := by
  norm_num [atom1288, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1288_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3207232022400 : Int) atom1288) := by
  rw [SparsePolynomial.eval_scale, eval_atom1288]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1288Coded : CoefficientMerge.Poly := [(nat_lit 3242, Int.ofNat (nat_lit 1))]
theorem atom1288Coded_decode : atom1288 = SparsePolynomial.decodeCubic 21 atom1288Coded := by decide +kernel
theorem atom1288Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3207232022400 : Int) atom1288Coded) := by
  have h := atom1288_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1288Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1289 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 7, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1289 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1289 = ((g 7) * (g 7) * (g 9)) := by
  norm_num [atom1289, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1289_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1289) := by
  rw [SparsePolynomial.eval_scale, eval_atom1289]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1289Coded : CoefficientMerge.Poly := [(nat_lit 3243, Int.ofNat (nat_lit 1))]
theorem atom1289Coded_decode : atom1289 = SparsePolynomial.decodeCubic 21 atom1289Coded := by decide +kernel
theorem atom1289Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1289Coded) := by
  have h := atom1289_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1289Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1290 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 7, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1290 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1290 = ((g 7) * (g 7) * (g 10)) := by
  norm_num [atom1290, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1290_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84082924800 : Int) atom1290) := by
  rw [SparsePolynomial.eval_scale, eval_atom1290]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1290Coded : CoefficientMerge.Poly := [(nat_lit 3244, Int.ofNat (nat_lit 1))]
theorem atom1290Coded_decode : atom1290 = SparsePolynomial.decodeCubic 21 atom1290Coded := by decide +kernel
theorem atom1290Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (84082924800 : Int) atom1290Coded) := by
  have h := atom1290_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1290Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1291 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1291 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1291 = ((g 7) * (g 7) * (g 15)) := by
  norm_num [atom1291, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1291_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3734859508992 : Int) atom1291) := by
  rw [SparsePolynomial.eval_scale, eval_atom1291]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1291Coded : CoefficientMerge.Poly := [(nat_lit 3249, Int.ofNat (nat_lit 1))]
theorem atom1291Coded_decode : atom1291 = SparsePolynomial.decodeCubic 21 atom1291Coded := by decide +kernel
theorem atom1291Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3734859508992 : Int) atom1291Coded) := by
  have h := atom1291_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1291Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1292 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1292 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1292 = ((g 7) * (g 8) * (g 8)) := by
  norm_num [atom1292, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1292_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2780052105600 : Int) atom1292) := by
  rw [SparsePolynomial.eval_scale, eval_atom1292]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1292Coded : CoefficientMerge.Poly := [(nat_lit 3263, Int.ofNat (nat_lit 1))]
theorem atom1292Coded_decode : atom1292 = SparsePolynomial.decodeCubic 21 atom1292Coded := by decide +kernel
theorem atom1292Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2780052105600 : Int) atom1292Coded) := by
  have h := atom1292_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1292Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1293 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1293 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1293 = ((g 7) * (g 8) * (g 9)) := by
  norm_num [atom1293, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1293_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (518028134400 : Int) atom1293) := by
  rw [SparsePolynomial.eval_scale, eval_atom1293]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1293Coded : CoefficientMerge.Poly := [(nat_lit 3264, Int.ofNat (nat_lit 1))]
theorem atom1293Coded_decode : atom1293 = SparsePolynomial.decodeCubic 21 atom1293Coded := by decide +kernel
theorem atom1293Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (518028134400 : Int) atom1293Coded) := by
  have h := atom1293_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1293Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1294 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1294 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1294 = ((g 7) * (g 8) * (g 13)) := by
  norm_num [atom1294, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1294_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1294) := by
  rw [SparsePolynomial.eval_scale, eval_atom1294]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1294Coded : CoefficientMerge.Poly := [(nat_lit 3268, Int.ofNat (nat_lit 1))]
theorem atom1294Coded_decode : atom1294 = SparsePolynomial.decodeCubic 21 atom1294Coded := by decide +kernel
theorem atom1294Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1294Coded) := by
  have h := atom1294_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1294Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1295 : SparsePolynomial.Poly := [([nat_lit 7, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1295 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1295 = ((g 7) * (g 8) * (g 14)) := by
  norm_num [atom1295, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1295_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (854359833600 : Int) atom1295) := by
  rw [SparsePolynomial.eval_scale, eval_atom1295]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1295Coded : CoefficientMerge.Poly := [(nat_lit 3269, Int.ofNat (nat_lit 1))]
theorem atom1295Coded_decode : atom1295 = SparsePolynomial.decodeCubic 21 atom1295Coded := by decide +kernel
theorem atom1295Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (854359833600 : Int) atom1295Coded) := by
  have h := atom1295_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1295Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block017 : CoefficientMerge.Poly := [(nat_lit 2848, Int.ofNat (nat_lit 2066320569600)), (nat_lit 2849, Int.ofNat (nat_lit 2843362771200)), (nat_lit 2850, Int.ofNat (nat_lit 12526751865600)), (nat_lit 2851, Int.ofNat (nat_lit 9755314884000)), (nat_lit 2852, Int.ofNat (nat_lit 17449540819200)), (nat_lit 2853, Int.ofNat (nat_lit 24820650338400)), (nat_lit 2854, Int.ofNat (nat_lit 35164296367200)), (nat_lit 2855, Int.ofNat (nat_lit 45787493959200)), (nat_lit 2866, Int.ofNat (nat_lit 3204336038400)), (nat_lit 2867, Int.ofNat (nat_lit 5399676979200)), (nat_lit 2868, Int.ofNat (nat_lit 5672221632000)), (nat_lit 2869, Int.ofNat (nat_lit 6371946201600)), (nat_lit 2870, Int.ofNat (nat_lit 7071670771200)), (nat_lit 2871, Int.ofNat (nat_lit 17374084156800)), (nat_lit 2872, Int.ofNat (nat_lit 15150394274400)), (nat_lit 2873, Int.ofNat (nat_lit 25703681270400)), (nat_lit 2874, Int.ofNat (nat_lit 31388299941600)), (nat_lit 2875, Int.ofNat (nat_lit 42276310423200)), (nat_lit 2876, Int.ofNat (nat_lit 53312311684800)), (nat_lit 2888, Int.ofNat (nat_lit 5780946124800)), (nat_lit 2889, Int.ofNat (nat_lit 10139247820800)), (nat_lit 2890, Int.ofNat (nat_lit 10593488908800)), (nat_lit 2891, Int.ofNat (nat_lit 11047729996800)), (nat_lit 2892, Int.ofNat (nat_lit 21624024038400)), (nat_lit 2893, Int.ofNat (nat_lit 19839379392000)), (nat_lit 2894, Int.ofNat (nat_lit 33307519795200)), (nat_lit 2895, Int.ofNat (nat_lit 36744632870400)), (nat_lit 2896, Int.ofNat (nat_lit 47909475532800)), (nat_lit 2897, Int.ofNat (nat_lit 59097361881600)), (nat_lit 2910, Int.ofNat (nat_lit 8371086796800)), (nat_lit 2911, Int.ofNat (nat_lit 16355585433600)), (nat_lit 2912, Int.ofNat (nat_lit 16396177190400)), (nat_lit 2913, Int.ofNat (nat_lit 22971182707200)), (nat_lit 2914, Int.ofNat (nat_lit 23375330316800)), (nat_lit 2915, Int.ofNat (nat_lit 35615926976000)), (nat_lit 2916, Int.ofNat (nat_lit 39881932652800)), (nat_lit 2917, Int.ofNat (nat_lit 50170991001600)), (nat_lit 2918, Int.ofNat (nat_lit 61314928214400)), (nat_lit 2932, Int.ofNat (nat_lit 11705777856000)), (nat_lit 2933, Int.ofNat (nat_lit 21699798566400)), (nat_lit 2934, Int.ofNat (nat_lit 27731989051200)), (nat_lit 2935, Int.ofNat (nat_lit 27457319044800)), (nat_lit 2936, Int.ofNat (nat_lit 42282031276800)), (nat_lit 2937, Int.ofNat (nat_lit 47812699267200)), (nat_lit 2938, Int.ofNat (nat_lit 51497513812800)), (nat_lit 2939, Int.ofNat (nat_lit 68517790488000)), (nat_lit 2954, Int.ofNat (nat_lit 15983651980800)), (nat_lit 2955, Int.ofNat (nat_lit 32380953292800)), (nat_lit 2956, Int.ofNat (nat_lit 31420158336000)), (nat_lit 2957, Int.ofNat (nat_lit 51141665433600)), (nat_lit 2958, Int.ofNat (nat_lit 58156348723200)), (nat_lit 2959, Int.ofNat (nat_lit 57274763212800)), (nat_lit 2960, Int.ofNat (nat_lit 80303655398400)), (nat_lit 2976, Int.ofNat (nat_lit 23458334054400)), (nat_lit 2977, Int.ofNat (nat_lit 44424079257600)), (nat_lit 2978, Int.ofNat (nat_lit 68201800934400)), (nat_lit 2979, Int.ofNat (nat_lit 70646230771200)), (nat_lit 2980, Int.ofNat (nat_lit 52545926361600)), (nat_lit 2981, Int.ofNat (nat_lit 79011669542400)), (nat_lit 2998, Int.ofNat (nat_lit 17545854735360)), (nat_lit 2999, Int.ofNat (nat_lit 55664911411200)), (nat_lit 3000, Int.ofNat (nat_lit 60106665427200)), (nat_lit 3001, Int.ofNat (nat_lit 46866713241600)), (nat_lit 3002, Int.ofNat (nat_lit 57384114883200)), (nat_lit 3020, Int.ofNat (nat_lit 40457273472000)), (nat_lit 3021, Int.ofNat (nat_lit 65177036467200)), (nat_lit 3022, Int.ofNat (nat_lit 46861654694400)), (nat_lit 3023, Int.ofNat (nat_lit 53756858937600)), (nat_lit 3042, Int.ofNat (nat_lit 18855796377600)), (nat_lit 3043, Int.ofNat (nat_lit 24005993760000)), (nat_lit 3044, Int.ofNat (nat_lit 30962904739200)), (nat_lit 3241, Int.ofNat (nat_lit 2264279068800)), (nat_lit 3242, Int.ofNat (nat_lit 3207232022400)), (nat_lit 3243, Int.ofNat (nat_lit 427179916800)), (nat_lit 3244, Int.ofNat (nat_lit 84082924800)), (nat_lit 3249, Int.ofNat (nat_lit 3734859508992)), (nat_lit 3263, Int.ofNat (nat_lit 2780052105600)), (nat_lit 3264, Int.ofNat (nat_lit 518028134400)), (nat_lit 3268, Int.ofNat (nat_lit 427179916800)), (nat_lit 3269, Int.ofNat (nat_lit 854359833600))]
def block017_data_flat000 : CoefficientMerge.Poly := [(nat_lit 2848, Int.ofNat (nat_lit 2066320569600))]
theorem block017_data_flat000_step : block017_data_flat000 = (CoefficientMerge.scale (2066320569600 : Int) atom1216Coded) := by decide +kernel
theorem block017_data_flat000_original : block017_data_flat000 = (CoefficientMerge.scale (2066320569600 : Int) atom1216Coded) := by
  rw [block017_data_flat000_step]
def block017_data_flat001 : CoefficientMerge.Poly := [(nat_lit 2849, Int.ofNat (nat_lit 2843362771200))]
theorem block017_data_flat001_step : block017_data_flat001 = (CoefficientMerge.scale (2843362771200 : Int) atom1217Coded) := by decide +kernel
theorem block017_data_flat001_original : block017_data_flat001 = (CoefficientMerge.scale (2843362771200 : Int) atom1217Coded) := by
  rw [block017_data_flat001_step]
def block017_data_flat002 : CoefficientMerge.Poly := [(nat_lit 2848, Int.ofNat (nat_lit 2066320569600)), (nat_lit 2849, Int.ofNat (nat_lit 2843362771200))]
theorem block017_data_flat002_step : block017_data_flat002 = (CoefficientMerge.fastMerge block017_data_flat000 block017_data_flat001) := by decide +kernel
theorem block017_data_flat002_original : block017_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (2066320569600 : Int) atom1216Coded) (CoefficientMerge.scale (2843362771200 : Int) atom1217Coded)) := by
  rw [block017_data_flat002_step, block017_data_flat000_original, block017_data_flat001_original]
def block017_data_flat003 : CoefficientMerge.Poly := [(nat_lit 2850, Int.ofNat (nat_lit 12526751865600))]
theorem block017_data_flat003_step : block017_data_flat003 = (CoefficientMerge.scale (12526751865600 : Int) atom1218Coded) := by decide +kernel
theorem block017_data_flat003_original : block017_data_flat003 = (CoefficientMerge.scale (12526751865600 : Int) atom1218Coded) := by
  rw [block017_data_flat003_step]
def block017_data_flat004 : CoefficientMerge.Poly := [(nat_lit 2851, Int.ofNat (nat_lit 9755314884000))]
theorem block017_data_flat004_step : block017_data_flat004 = (CoefficientMerge.scale (9755314884000 : Int) atom1219Coded) := by decide +kernel
theorem block017_data_flat004_original : block017_data_flat004 = (CoefficientMerge.scale (9755314884000 : Int) atom1219Coded) := by
  rw [block017_data_flat004_step]
def block017_data_flat005 : CoefficientMerge.Poly := [(nat_lit 2852, Int.ofNat (nat_lit 17449540819200))]
theorem block017_data_flat005_step : block017_data_flat005 = (CoefficientMerge.scale (17449540819200 : Int) atom1220Coded) := by decide +kernel
theorem block017_data_flat005_original : block017_data_flat005 = (CoefficientMerge.scale (17449540819200 : Int) atom1220Coded) := by
  rw [block017_data_flat005_step]
def block017_data_flat006 : CoefficientMerge.Poly := [(nat_lit 2851, Int.ofNat (nat_lit 9755314884000)), (nat_lit 2852, Int.ofNat (nat_lit 17449540819200))]
theorem block017_data_flat006_step : block017_data_flat006 = (CoefficientMerge.fastMerge block017_data_flat004 block017_data_flat005) := by decide +kernel
theorem block017_data_flat006_original : block017_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9755314884000 : Int) atom1219Coded) (CoefficientMerge.scale (17449540819200 : Int) atom1220Coded)) := by
  rw [block017_data_flat006_step, block017_data_flat004_original, block017_data_flat005_original]
def block017_data_flat007 : CoefficientMerge.Poly := [(nat_lit 2850, Int.ofNat (nat_lit 12526751865600)), (nat_lit 2851, Int.ofNat (nat_lit 9755314884000)), (nat_lit 2852, Int.ofNat (nat_lit 17449540819200))]
theorem block017_data_flat007_step : block017_data_flat007 = (CoefficientMerge.fastMerge block017_data_flat003 block017_data_flat006) := by decide +kernel
theorem block017_data_flat007_original : block017_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (12526751865600 : Int) atom1218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9755314884000 : Int) atom1219Coded) (CoefficientMerge.scale (17449540819200 : Int) atom1220Coded))) := by
  rw [block017_data_flat007_step, block017_data_flat003_original, block017_data_flat006_original]
def block017_data_flat008 : CoefficientMerge.Poly := [(nat_lit 2848, Int.ofNat (nat_lit 2066320569600)), (nat_lit 2849, Int.ofNat (nat_lit 2843362771200)), (nat_lit 2850, Int.ofNat (nat_lit 12526751865600)), (nat_lit 2851, Int.ofNat (nat_lit 9755314884000)), (nat_lit 2852, Int.ofNat (nat_lit 17449540819200))]
theorem block017_data_flat008_step : block017_data_flat008 = (CoefficientMerge.fastMerge block017_data_flat002 block017_data_flat007) := by decide +kernel
theorem block017_data_flat008_original : block017_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2066320569600 : Int) atom1216Coded) (CoefficientMerge.scale (2843362771200 : Int) atom1217Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12526751865600 : Int) atom1218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9755314884000 : Int) atom1219Coded) (CoefficientMerge.scale (17449540819200 : Int) atom1220Coded)))) := by
  rw [block017_data_flat008_step, block017_data_flat002_original, block017_data_flat007_original]
def block017_data_flat009 : CoefficientMerge.Poly := [(nat_lit 2853, Int.ofNat (nat_lit 24820650338400))]
theorem block017_data_flat009_step : block017_data_flat009 = (CoefficientMerge.scale (24820650338400 : Int) atom1221Coded) := by decide +kernel
theorem block017_data_flat009_original : block017_data_flat009 = (CoefficientMerge.scale (24820650338400 : Int) atom1221Coded) := by
  rw [block017_data_flat009_step]
def block017_data_flat010 : CoefficientMerge.Poly := [(nat_lit 2854, Int.ofNat (nat_lit 35164296367200))]
theorem block017_data_flat010_step : block017_data_flat010 = (CoefficientMerge.scale (35164296367200 : Int) atom1222Coded) := by decide +kernel
theorem block017_data_flat010_original : block017_data_flat010 = (CoefficientMerge.scale (35164296367200 : Int) atom1222Coded) := by
  rw [block017_data_flat010_step]
def block017_data_flat011 : CoefficientMerge.Poly := [(nat_lit 2853, Int.ofNat (nat_lit 24820650338400)), (nat_lit 2854, Int.ofNat (nat_lit 35164296367200))]
theorem block017_data_flat011_step : block017_data_flat011 = (CoefficientMerge.fastMerge block017_data_flat009 block017_data_flat010) := by decide +kernel
theorem block017_data_flat011_original : block017_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (24820650338400 : Int) atom1221Coded) (CoefficientMerge.scale (35164296367200 : Int) atom1222Coded)) := by
  rw [block017_data_flat011_step, block017_data_flat009_original, block017_data_flat010_original]
def block017_data_flat012 : CoefficientMerge.Poly := [(nat_lit 2855, Int.ofNat (nat_lit 45787493959200))]
theorem block017_data_flat012_step : block017_data_flat012 = (CoefficientMerge.scale (45787493959200 : Int) atom1223Coded) := by decide +kernel
theorem block017_data_flat012_original : block017_data_flat012 = (CoefficientMerge.scale (45787493959200 : Int) atom1223Coded) := by
  rw [block017_data_flat012_step]
def block017_data_flat013 : CoefficientMerge.Poly := [(nat_lit 2866, Int.ofNat (nat_lit 3204336038400))]
theorem block017_data_flat013_step : block017_data_flat013 = (CoefficientMerge.scale (3204336038400 : Int) atom1224Coded) := by decide +kernel
theorem block017_data_flat013_original : block017_data_flat013 = (CoefficientMerge.scale (3204336038400 : Int) atom1224Coded) := by
  rw [block017_data_flat013_step]
def block017_data_flat014 : CoefficientMerge.Poly := [(nat_lit 2867, Int.ofNat (nat_lit 5399676979200))]
theorem block017_data_flat014_step : block017_data_flat014 = (CoefficientMerge.scale (5399676979200 : Int) atom1225Coded) := by decide +kernel
theorem block017_data_flat014_original : block017_data_flat014 = (CoefficientMerge.scale (5399676979200 : Int) atom1225Coded) := by
  rw [block017_data_flat014_step]
def block017_data_flat015 : CoefficientMerge.Poly := [(nat_lit 2866, Int.ofNat (nat_lit 3204336038400)), (nat_lit 2867, Int.ofNat (nat_lit 5399676979200))]
theorem block017_data_flat015_step : block017_data_flat015 = (CoefficientMerge.fastMerge block017_data_flat013 block017_data_flat014) := by decide +kernel
theorem block017_data_flat015_original : block017_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3204336038400 : Int) atom1224Coded) (CoefficientMerge.scale (5399676979200 : Int) atom1225Coded)) := by
  rw [block017_data_flat015_step, block017_data_flat013_original, block017_data_flat014_original]
def block017_data_flat016 : CoefficientMerge.Poly := [(nat_lit 2855, Int.ofNat (nat_lit 45787493959200)), (nat_lit 2866, Int.ofNat (nat_lit 3204336038400)), (nat_lit 2867, Int.ofNat (nat_lit 5399676979200))]
theorem block017_data_flat016_step : block017_data_flat016 = (CoefficientMerge.fastMerge block017_data_flat012 block017_data_flat015) := by decide +kernel
theorem block017_data_flat016_original : block017_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (45787493959200 : Int) atom1223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3204336038400 : Int) atom1224Coded) (CoefficientMerge.scale (5399676979200 : Int) atom1225Coded))) := by
  rw [block017_data_flat016_step, block017_data_flat012_original, block017_data_flat015_original]
def block017_data_flat017 : CoefficientMerge.Poly := [(nat_lit 2853, Int.ofNat (nat_lit 24820650338400)), (nat_lit 2854, Int.ofNat (nat_lit 35164296367200)), (nat_lit 2855, Int.ofNat (nat_lit 45787493959200)), (nat_lit 2866, Int.ofNat (nat_lit 3204336038400)), (nat_lit 2867, Int.ofNat (nat_lit 5399676979200))]
theorem block017_data_flat017_step : block017_data_flat017 = (CoefficientMerge.fastMerge block017_data_flat011 block017_data_flat016) := by decide +kernel
theorem block017_data_flat017_original : block017_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24820650338400 : Int) atom1221Coded) (CoefficientMerge.scale (35164296367200 : Int) atom1222Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45787493959200 : Int) atom1223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3204336038400 : Int) atom1224Coded) (CoefficientMerge.scale (5399676979200 : Int) atom1225Coded)))) := by
  rw [block017_data_flat017_step, block017_data_flat011_original, block017_data_flat016_original]
def block017_data_flat018 : CoefficientMerge.Poly := [(nat_lit 2848, Int.ofNat (nat_lit 2066320569600)), (nat_lit 2849, Int.ofNat (nat_lit 2843362771200)), (nat_lit 2850, Int.ofNat (nat_lit 12526751865600)), (nat_lit 2851, Int.ofNat (nat_lit 9755314884000)), (nat_lit 2852, Int.ofNat (nat_lit 17449540819200)), (nat_lit 2853, Int.ofNat (nat_lit 24820650338400)), (nat_lit 2854, Int.ofNat (nat_lit 35164296367200)), (nat_lit 2855, Int.ofNat (nat_lit 45787493959200)), (nat_lit 2866, Int.ofNat (nat_lit 3204336038400)), (nat_lit 2867, Int.ofNat (nat_lit 5399676979200))]
theorem block017_data_flat018_step : block017_data_flat018 = (CoefficientMerge.fastMerge block017_data_flat008 block017_data_flat017) := by decide +kernel
theorem block017_data_flat018_original : block017_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2066320569600 : Int) atom1216Coded) (CoefficientMerge.scale (2843362771200 : Int) atom1217Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12526751865600 : Int) atom1218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9755314884000 : Int) atom1219Coded) (CoefficientMerge.scale (17449540819200 : Int) atom1220Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24820650338400 : Int) atom1221Coded) (CoefficientMerge.scale (35164296367200 : Int) atom1222Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45787493959200 : Int) atom1223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3204336038400 : Int) atom1224Coded) (CoefficientMerge.scale (5399676979200 : Int) atom1225Coded))))) := by
  rw [block017_data_flat018_step, block017_data_flat008_original, block017_data_flat017_original]
def block017_data_flat019 : CoefficientMerge.Poly := [(nat_lit 2868, Int.ofNat (nat_lit 5672221632000))]
theorem block017_data_flat019_step : block017_data_flat019 = (CoefficientMerge.scale (5672221632000 : Int) atom1226Coded) := by decide +kernel
theorem block017_data_flat019_original : block017_data_flat019 = (CoefficientMerge.scale (5672221632000 : Int) atom1226Coded) := by
  rw [block017_data_flat019_step]
def block017_data_flat020 : CoefficientMerge.Poly := [(nat_lit 2869, Int.ofNat (nat_lit 6371946201600))]
theorem block017_data_flat020_step : block017_data_flat020 = (CoefficientMerge.scale (6371946201600 : Int) atom1227Coded) := by decide +kernel
theorem block017_data_flat020_original : block017_data_flat020 = (CoefficientMerge.scale (6371946201600 : Int) atom1227Coded) := by
  rw [block017_data_flat020_step]
def block017_data_flat021 : CoefficientMerge.Poly := [(nat_lit 2868, Int.ofNat (nat_lit 5672221632000)), (nat_lit 2869, Int.ofNat (nat_lit 6371946201600))]
theorem block017_data_flat021_step : block017_data_flat021 = (CoefficientMerge.fastMerge block017_data_flat019 block017_data_flat020) := by decide +kernel
theorem block017_data_flat021_original : block017_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5672221632000 : Int) atom1226Coded) (CoefficientMerge.scale (6371946201600 : Int) atom1227Coded)) := by
  rw [block017_data_flat021_step, block017_data_flat019_original, block017_data_flat020_original]
def block017_data_flat022 : CoefficientMerge.Poly := [(nat_lit 2870, Int.ofNat (nat_lit 7071670771200))]
theorem block017_data_flat022_step : block017_data_flat022 = (CoefficientMerge.scale (7071670771200 : Int) atom1228Coded) := by decide +kernel
theorem block017_data_flat022_original : block017_data_flat022 = (CoefficientMerge.scale (7071670771200 : Int) atom1228Coded) := by
  rw [block017_data_flat022_step]
def block017_data_flat023 : CoefficientMerge.Poly := [(nat_lit 2871, Int.ofNat (nat_lit 17374084156800))]
theorem block017_data_flat023_step : block017_data_flat023 = (CoefficientMerge.scale (17374084156800 : Int) atom1229Coded) := by decide +kernel
theorem block017_data_flat023_original : block017_data_flat023 = (CoefficientMerge.scale (17374084156800 : Int) atom1229Coded) := by
  rw [block017_data_flat023_step]
def block017_data_flat024 : CoefficientMerge.Poly := [(nat_lit 2872, Int.ofNat (nat_lit 15150394274400))]
theorem block017_data_flat024_step : block017_data_flat024 = (CoefficientMerge.scale (15150394274400 : Int) atom1230Coded) := by decide +kernel
theorem block017_data_flat024_original : block017_data_flat024 = (CoefficientMerge.scale (15150394274400 : Int) atom1230Coded) := by
  rw [block017_data_flat024_step]
def block017_data_flat025 : CoefficientMerge.Poly := [(nat_lit 2871, Int.ofNat (nat_lit 17374084156800)), (nat_lit 2872, Int.ofNat (nat_lit 15150394274400))]
theorem block017_data_flat025_step : block017_data_flat025 = (CoefficientMerge.fastMerge block017_data_flat023 block017_data_flat024) := by decide +kernel
theorem block017_data_flat025_original : block017_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (17374084156800 : Int) atom1229Coded) (CoefficientMerge.scale (15150394274400 : Int) atom1230Coded)) := by
  rw [block017_data_flat025_step, block017_data_flat023_original, block017_data_flat024_original]
def block017_data_flat026 : CoefficientMerge.Poly := [(nat_lit 2870, Int.ofNat (nat_lit 7071670771200)), (nat_lit 2871, Int.ofNat (nat_lit 17374084156800)), (nat_lit 2872, Int.ofNat (nat_lit 15150394274400))]
theorem block017_data_flat026_step : block017_data_flat026 = (CoefficientMerge.fastMerge block017_data_flat022 block017_data_flat025) := by decide +kernel
theorem block017_data_flat026_original : block017_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7071670771200 : Int) atom1228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17374084156800 : Int) atom1229Coded) (CoefficientMerge.scale (15150394274400 : Int) atom1230Coded))) := by
  rw [block017_data_flat026_step, block017_data_flat022_original, block017_data_flat025_original]
def block017_data_flat027 : CoefficientMerge.Poly := [(nat_lit 2868, Int.ofNat (nat_lit 5672221632000)), (nat_lit 2869, Int.ofNat (nat_lit 6371946201600)), (nat_lit 2870, Int.ofNat (nat_lit 7071670771200)), (nat_lit 2871, Int.ofNat (nat_lit 17374084156800)), (nat_lit 2872, Int.ofNat (nat_lit 15150394274400))]
theorem block017_data_flat027_step : block017_data_flat027 = (CoefficientMerge.fastMerge block017_data_flat021 block017_data_flat026) := by decide +kernel
theorem block017_data_flat027_original : block017_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5672221632000 : Int) atom1226Coded) (CoefficientMerge.scale (6371946201600 : Int) atom1227Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7071670771200 : Int) atom1228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17374084156800 : Int) atom1229Coded) (CoefficientMerge.scale (15150394274400 : Int) atom1230Coded)))) := by
  rw [block017_data_flat027_step, block017_data_flat021_original, block017_data_flat026_original]
def block017_data_flat028 : CoefficientMerge.Poly := [(nat_lit 2873, Int.ofNat (nat_lit 25703681270400))]
theorem block017_data_flat028_step : block017_data_flat028 = (CoefficientMerge.scale (25703681270400 : Int) atom1231Coded) := by decide +kernel
theorem block017_data_flat028_original : block017_data_flat028 = (CoefficientMerge.scale (25703681270400 : Int) atom1231Coded) := by
  rw [block017_data_flat028_step]
def block017_data_flat029 : CoefficientMerge.Poly := [(nat_lit 2874, Int.ofNat (nat_lit 31388299941600))]
theorem block017_data_flat029_step : block017_data_flat029 = (CoefficientMerge.scale (31388299941600 : Int) atom1232Coded) := by decide +kernel
theorem block017_data_flat029_original : block017_data_flat029 = (CoefficientMerge.scale (31388299941600 : Int) atom1232Coded) := by
  rw [block017_data_flat029_step]
def block017_data_flat030 : CoefficientMerge.Poly := [(nat_lit 2873, Int.ofNat (nat_lit 25703681270400)), (nat_lit 2874, Int.ofNat (nat_lit 31388299941600))]
theorem block017_data_flat030_step : block017_data_flat030 = (CoefficientMerge.fastMerge block017_data_flat028 block017_data_flat029) := by decide +kernel
theorem block017_data_flat030_original : block017_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25703681270400 : Int) atom1231Coded) (CoefficientMerge.scale (31388299941600 : Int) atom1232Coded)) := by
  rw [block017_data_flat030_step, block017_data_flat028_original, block017_data_flat029_original]
def block017_data_flat031 : CoefficientMerge.Poly := [(nat_lit 2875, Int.ofNat (nat_lit 42276310423200))]
theorem block017_data_flat031_step : block017_data_flat031 = (CoefficientMerge.scale (42276310423200 : Int) atom1233Coded) := by decide +kernel
theorem block017_data_flat031_original : block017_data_flat031 = (CoefficientMerge.scale (42276310423200 : Int) atom1233Coded) := by
  rw [block017_data_flat031_step]
def block017_data_flat032 : CoefficientMerge.Poly := [(nat_lit 2876, Int.ofNat (nat_lit 53312311684800))]
theorem block017_data_flat032_step : block017_data_flat032 = (CoefficientMerge.scale (53312311684800 : Int) atom1234Coded) := by decide +kernel
theorem block017_data_flat032_original : block017_data_flat032 = (CoefficientMerge.scale (53312311684800 : Int) atom1234Coded) := by
  rw [block017_data_flat032_step]
def block017_data_flat033 : CoefficientMerge.Poly := [(nat_lit 2888, Int.ofNat (nat_lit 5780946124800))]
theorem block017_data_flat033_step : block017_data_flat033 = (CoefficientMerge.scale (5780946124800 : Int) atom1235Coded) := by decide +kernel
theorem block017_data_flat033_original : block017_data_flat033 = (CoefficientMerge.scale (5780946124800 : Int) atom1235Coded) := by
  rw [block017_data_flat033_step]
def block017_data_flat034 : CoefficientMerge.Poly := [(nat_lit 2876, Int.ofNat (nat_lit 53312311684800)), (nat_lit 2888, Int.ofNat (nat_lit 5780946124800))]
theorem block017_data_flat034_step : block017_data_flat034 = (CoefficientMerge.fastMerge block017_data_flat032 block017_data_flat033) := by decide +kernel
theorem block017_data_flat034_original : block017_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (53312311684800 : Int) atom1234Coded) (CoefficientMerge.scale (5780946124800 : Int) atom1235Coded)) := by
  rw [block017_data_flat034_step, block017_data_flat032_original, block017_data_flat033_original]
def block017_data_flat035 : CoefficientMerge.Poly := [(nat_lit 2875, Int.ofNat (nat_lit 42276310423200)), (nat_lit 2876, Int.ofNat (nat_lit 53312311684800)), (nat_lit 2888, Int.ofNat (nat_lit 5780946124800))]
theorem block017_data_flat035_step : block017_data_flat035 = (CoefficientMerge.fastMerge block017_data_flat031 block017_data_flat034) := by decide +kernel
theorem block017_data_flat035_original : block017_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (42276310423200 : Int) atom1233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53312311684800 : Int) atom1234Coded) (CoefficientMerge.scale (5780946124800 : Int) atom1235Coded))) := by
  rw [block017_data_flat035_step, block017_data_flat031_original, block017_data_flat034_original]
def block017_data_flat036 : CoefficientMerge.Poly := [(nat_lit 2873, Int.ofNat (nat_lit 25703681270400)), (nat_lit 2874, Int.ofNat (nat_lit 31388299941600)), (nat_lit 2875, Int.ofNat (nat_lit 42276310423200)), (nat_lit 2876, Int.ofNat (nat_lit 53312311684800)), (nat_lit 2888, Int.ofNat (nat_lit 5780946124800))]
theorem block017_data_flat036_step : block017_data_flat036 = (CoefficientMerge.fastMerge block017_data_flat030 block017_data_flat035) := by decide +kernel
theorem block017_data_flat036_original : block017_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25703681270400 : Int) atom1231Coded) (CoefficientMerge.scale (31388299941600 : Int) atom1232Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42276310423200 : Int) atom1233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53312311684800 : Int) atom1234Coded) (CoefficientMerge.scale (5780946124800 : Int) atom1235Coded)))) := by
  rw [block017_data_flat036_step, block017_data_flat030_original, block017_data_flat035_original]
def block017_data_flat037 : CoefficientMerge.Poly := [(nat_lit 2868, Int.ofNat (nat_lit 5672221632000)), (nat_lit 2869, Int.ofNat (nat_lit 6371946201600)), (nat_lit 2870, Int.ofNat (nat_lit 7071670771200)), (nat_lit 2871, Int.ofNat (nat_lit 17374084156800)), (nat_lit 2872, Int.ofNat (nat_lit 15150394274400)), (nat_lit 2873, Int.ofNat (nat_lit 25703681270400)), (nat_lit 2874, Int.ofNat (nat_lit 31388299941600)), (nat_lit 2875, Int.ofNat (nat_lit 42276310423200)), (nat_lit 2876, Int.ofNat (nat_lit 53312311684800)), (nat_lit 2888, Int.ofNat (nat_lit 5780946124800))]
theorem block017_data_flat037_step : block017_data_flat037 = (CoefficientMerge.fastMerge block017_data_flat027 block017_data_flat036) := by decide +kernel
theorem block017_data_flat037_original : block017_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5672221632000 : Int) atom1226Coded) (CoefficientMerge.scale (6371946201600 : Int) atom1227Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7071670771200 : Int) atom1228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17374084156800 : Int) atom1229Coded) (CoefficientMerge.scale (15150394274400 : Int) atom1230Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25703681270400 : Int) atom1231Coded) (CoefficientMerge.scale (31388299941600 : Int) atom1232Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42276310423200 : Int) atom1233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53312311684800 : Int) atom1234Coded) (CoefficientMerge.scale (5780946124800 : Int) atom1235Coded))))) := by
  rw [block017_data_flat037_step, block017_data_flat027_original, block017_data_flat036_original]
def block017_data_flat038 : CoefficientMerge.Poly := [(nat_lit 2848, Int.ofNat (nat_lit 2066320569600)), (nat_lit 2849, Int.ofNat (nat_lit 2843362771200)), (nat_lit 2850, Int.ofNat (nat_lit 12526751865600)), (nat_lit 2851, Int.ofNat (nat_lit 9755314884000)), (nat_lit 2852, Int.ofNat (nat_lit 17449540819200)), (nat_lit 2853, Int.ofNat (nat_lit 24820650338400)), (nat_lit 2854, Int.ofNat (nat_lit 35164296367200)), (nat_lit 2855, Int.ofNat (nat_lit 45787493959200)), (nat_lit 2866, Int.ofNat (nat_lit 3204336038400)), (nat_lit 2867, Int.ofNat (nat_lit 5399676979200)), (nat_lit 2868, Int.ofNat (nat_lit 5672221632000)), (nat_lit 2869, Int.ofNat (nat_lit 6371946201600)), (nat_lit 2870, Int.ofNat (nat_lit 7071670771200)), (nat_lit 2871, Int.ofNat (nat_lit 17374084156800)), (nat_lit 2872, Int.ofNat (nat_lit 15150394274400)), (nat_lit 2873, Int.ofNat (nat_lit 25703681270400)), (nat_lit 2874, Int.ofNat (nat_lit 31388299941600)), (nat_lit 2875, Int.ofNat (nat_lit 42276310423200)), (nat_lit 2876, Int.ofNat (nat_lit 53312311684800)), (nat_lit 2888, Int.ofNat (nat_lit 5780946124800))]
theorem block017_data_flat038_step : block017_data_flat038 = (CoefficientMerge.fastMerge block017_data_flat018 block017_data_flat037) := by decide +kernel
theorem block017_data_flat038_original : block017_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2066320569600 : Int) atom1216Coded) (CoefficientMerge.scale (2843362771200 : Int) atom1217Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12526751865600 : Int) atom1218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9755314884000 : Int) atom1219Coded) (CoefficientMerge.scale (17449540819200 : Int) atom1220Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24820650338400 : Int) atom1221Coded) (CoefficientMerge.scale (35164296367200 : Int) atom1222Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45787493959200 : Int) atom1223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3204336038400 : Int) atom1224Coded) (CoefficientMerge.scale (5399676979200 : Int) atom1225Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5672221632000 : Int) atom1226Coded) (CoefficientMerge.scale (6371946201600 : Int) atom1227Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7071670771200 : Int) atom1228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17374084156800 : Int) atom1229Coded) (CoefficientMerge.scale (15150394274400 : Int) atom1230Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25703681270400 : Int) atom1231Coded) (CoefficientMerge.scale (31388299941600 : Int) atom1232Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42276310423200 : Int) atom1233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53312311684800 : Int) atom1234Coded) (CoefficientMerge.scale (5780946124800 : Int) atom1235Coded)))))) := by
  rw [block017_data_flat038_step, block017_data_flat018_original, block017_data_flat037_original]
def block017_data_flat039 : CoefficientMerge.Poly := [(nat_lit 2889, Int.ofNat (nat_lit 10139247820800))]
theorem block017_data_flat039_step : block017_data_flat039 = (CoefficientMerge.scale (10139247820800 : Int) atom1236Coded) := by decide +kernel
theorem block017_data_flat039_original : block017_data_flat039 = (CoefficientMerge.scale (10139247820800 : Int) atom1236Coded) := by
  rw [block017_data_flat039_step]
def block017_data_flat040 : CoefficientMerge.Poly := [(nat_lit 2890, Int.ofNat (nat_lit 10593488908800))]
theorem block017_data_flat040_step : block017_data_flat040 = (CoefficientMerge.scale (10593488908800 : Int) atom1237Coded) := by decide +kernel
theorem block017_data_flat040_original : block017_data_flat040 = (CoefficientMerge.scale (10593488908800 : Int) atom1237Coded) := by
  rw [block017_data_flat040_step]
def block017_data_flat041 : CoefficientMerge.Poly := [(nat_lit 2889, Int.ofNat (nat_lit 10139247820800)), (nat_lit 2890, Int.ofNat (nat_lit 10593488908800))]
theorem block017_data_flat041_step : block017_data_flat041 = (CoefficientMerge.fastMerge block017_data_flat039 block017_data_flat040) := by decide +kernel
theorem block017_data_flat041_original : block017_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (10139247820800 : Int) atom1236Coded) (CoefficientMerge.scale (10593488908800 : Int) atom1237Coded)) := by
  rw [block017_data_flat041_step, block017_data_flat039_original, block017_data_flat040_original]
def block017_data_flat042 : CoefficientMerge.Poly := [(nat_lit 2891, Int.ofNat (nat_lit 11047729996800))]
theorem block017_data_flat042_step : block017_data_flat042 = (CoefficientMerge.scale (11047729996800 : Int) atom1238Coded) := by decide +kernel
theorem block017_data_flat042_original : block017_data_flat042 = (CoefficientMerge.scale (11047729996800 : Int) atom1238Coded) := by
  rw [block017_data_flat042_step]
def block017_data_flat043 : CoefficientMerge.Poly := [(nat_lit 2892, Int.ofNat (nat_lit 21624024038400))]
theorem block017_data_flat043_step : block017_data_flat043 = (CoefficientMerge.scale (21624024038400 : Int) atom1239Coded) := by decide +kernel
theorem block017_data_flat043_original : block017_data_flat043 = (CoefficientMerge.scale (21624024038400 : Int) atom1239Coded) := by
  rw [block017_data_flat043_step]
def block017_data_flat044 : CoefficientMerge.Poly := [(nat_lit 2893, Int.ofNat (nat_lit 19839379392000))]
theorem block017_data_flat044_step : block017_data_flat044 = (CoefficientMerge.scale (19839379392000 : Int) atom1240Coded) := by decide +kernel
theorem block017_data_flat044_original : block017_data_flat044 = (CoefficientMerge.scale (19839379392000 : Int) atom1240Coded) := by
  rw [block017_data_flat044_step]
def block017_data_flat045 : CoefficientMerge.Poly := [(nat_lit 2892, Int.ofNat (nat_lit 21624024038400)), (nat_lit 2893, Int.ofNat (nat_lit 19839379392000))]
theorem block017_data_flat045_step : block017_data_flat045 = (CoefficientMerge.fastMerge block017_data_flat043 block017_data_flat044) := by decide +kernel
theorem block017_data_flat045_original : block017_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (21624024038400 : Int) atom1239Coded) (CoefficientMerge.scale (19839379392000 : Int) atom1240Coded)) := by
  rw [block017_data_flat045_step, block017_data_flat043_original, block017_data_flat044_original]
def block017_data_flat046 : CoefficientMerge.Poly := [(nat_lit 2891, Int.ofNat (nat_lit 11047729996800)), (nat_lit 2892, Int.ofNat (nat_lit 21624024038400)), (nat_lit 2893, Int.ofNat (nat_lit 19839379392000))]
theorem block017_data_flat046_step : block017_data_flat046 = (CoefficientMerge.fastMerge block017_data_flat042 block017_data_flat045) := by decide +kernel
theorem block017_data_flat046_original : block017_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11047729996800 : Int) atom1238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21624024038400 : Int) atom1239Coded) (CoefficientMerge.scale (19839379392000 : Int) atom1240Coded))) := by
  rw [block017_data_flat046_step, block017_data_flat042_original, block017_data_flat045_original]
def block017_data_flat047 : CoefficientMerge.Poly := [(nat_lit 2889, Int.ofNat (nat_lit 10139247820800)), (nat_lit 2890, Int.ofNat (nat_lit 10593488908800)), (nat_lit 2891, Int.ofNat (nat_lit 11047729996800)), (nat_lit 2892, Int.ofNat (nat_lit 21624024038400)), (nat_lit 2893, Int.ofNat (nat_lit 19839379392000))]
theorem block017_data_flat047_step : block017_data_flat047 = (CoefficientMerge.fastMerge block017_data_flat041 block017_data_flat046) := by decide +kernel
theorem block017_data_flat047_original : block017_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10139247820800 : Int) atom1236Coded) (CoefficientMerge.scale (10593488908800 : Int) atom1237Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11047729996800 : Int) atom1238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21624024038400 : Int) atom1239Coded) (CoefficientMerge.scale (19839379392000 : Int) atom1240Coded)))) := by
  rw [block017_data_flat047_step, block017_data_flat041_original, block017_data_flat046_original]
def block017_data_flat048 : CoefficientMerge.Poly := [(nat_lit 2894, Int.ofNat (nat_lit 33307519795200))]
theorem block017_data_flat048_step : block017_data_flat048 = (CoefficientMerge.scale (33307519795200 : Int) atom1241Coded) := by decide +kernel
theorem block017_data_flat048_original : block017_data_flat048 = (CoefficientMerge.scale (33307519795200 : Int) atom1241Coded) := by
  rw [block017_data_flat048_step]
def block017_data_flat049 : CoefficientMerge.Poly := [(nat_lit 2895, Int.ofNat (nat_lit 36744632870400))]
theorem block017_data_flat049_step : block017_data_flat049 = (CoefficientMerge.scale (36744632870400 : Int) atom1242Coded) := by decide +kernel
theorem block017_data_flat049_original : block017_data_flat049 = (CoefficientMerge.scale (36744632870400 : Int) atom1242Coded) := by
  rw [block017_data_flat049_step]
def block017_data_flat050 : CoefficientMerge.Poly := [(nat_lit 2894, Int.ofNat (nat_lit 33307519795200)), (nat_lit 2895, Int.ofNat (nat_lit 36744632870400))]
theorem block017_data_flat050_step : block017_data_flat050 = (CoefficientMerge.fastMerge block017_data_flat048 block017_data_flat049) := by decide +kernel
theorem block017_data_flat050_original : block017_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (33307519795200 : Int) atom1241Coded) (CoefficientMerge.scale (36744632870400 : Int) atom1242Coded)) := by
  rw [block017_data_flat050_step, block017_data_flat048_original, block017_data_flat049_original]
def block017_data_flat051 : CoefficientMerge.Poly := [(nat_lit 2896, Int.ofNat (nat_lit 47909475532800))]
theorem block017_data_flat051_step : block017_data_flat051 = (CoefficientMerge.scale (47909475532800 : Int) atom1243Coded) := by decide +kernel
theorem block017_data_flat051_original : block017_data_flat051 = (CoefficientMerge.scale (47909475532800 : Int) atom1243Coded) := by
  rw [block017_data_flat051_step]
def block017_data_flat052 : CoefficientMerge.Poly := [(nat_lit 2897, Int.ofNat (nat_lit 59097361881600))]
theorem block017_data_flat052_step : block017_data_flat052 = (CoefficientMerge.scale (59097361881600 : Int) atom1244Coded) := by decide +kernel
theorem block017_data_flat052_original : block017_data_flat052 = (CoefficientMerge.scale (59097361881600 : Int) atom1244Coded) := by
  rw [block017_data_flat052_step]
def block017_data_flat053 : CoefficientMerge.Poly := [(nat_lit 2910, Int.ofNat (nat_lit 8371086796800))]
theorem block017_data_flat053_step : block017_data_flat053 = (CoefficientMerge.scale (8371086796800 : Int) atom1245Coded) := by decide +kernel
theorem block017_data_flat053_original : block017_data_flat053 = (CoefficientMerge.scale (8371086796800 : Int) atom1245Coded) := by
  rw [block017_data_flat053_step]
def block017_data_flat054 : CoefficientMerge.Poly := [(nat_lit 2897, Int.ofNat (nat_lit 59097361881600)), (nat_lit 2910, Int.ofNat (nat_lit 8371086796800))]
theorem block017_data_flat054_step : block017_data_flat054 = (CoefficientMerge.fastMerge block017_data_flat052 block017_data_flat053) := by decide +kernel
theorem block017_data_flat054_original : block017_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (59097361881600 : Int) atom1244Coded) (CoefficientMerge.scale (8371086796800 : Int) atom1245Coded)) := by
  rw [block017_data_flat054_step, block017_data_flat052_original, block017_data_flat053_original]
def block017_data_flat055 : CoefficientMerge.Poly := [(nat_lit 2896, Int.ofNat (nat_lit 47909475532800)), (nat_lit 2897, Int.ofNat (nat_lit 59097361881600)), (nat_lit 2910, Int.ofNat (nat_lit 8371086796800))]
theorem block017_data_flat055_step : block017_data_flat055 = (CoefficientMerge.fastMerge block017_data_flat051 block017_data_flat054) := by decide +kernel
theorem block017_data_flat055_original : block017_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (47909475532800 : Int) atom1243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59097361881600 : Int) atom1244Coded) (CoefficientMerge.scale (8371086796800 : Int) atom1245Coded))) := by
  rw [block017_data_flat055_step, block017_data_flat051_original, block017_data_flat054_original]
def block017_data_flat056 : CoefficientMerge.Poly := [(nat_lit 2894, Int.ofNat (nat_lit 33307519795200)), (nat_lit 2895, Int.ofNat (nat_lit 36744632870400)), (nat_lit 2896, Int.ofNat (nat_lit 47909475532800)), (nat_lit 2897, Int.ofNat (nat_lit 59097361881600)), (nat_lit 2910, Int.ofNat (nat_lit 8371086796800))]
theorem block017_data_flat056_step : block017_data_flat056 = (CoefficientMerge.fastMerge block017_data_flat050 block017_data_flat055) := by decide +kernel
theorem block017_data_flat056_original : block017_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33307519795200 : Int) atom1241Coded) (CoefficientMerge.scale (36744632870400 : Int) atom1242Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47909475532800 : Int) atom1243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59097361881600 : Int) atom1244Coded) (CoefficientMerge.scale (8371086796800 : Int) atom1245Coded)))) := by
  rw [block017_data_flat056_step, block017_data_flat050_original, block017_data_flat055_original]
def block017_data_flat057 : CoefficientMerge.Poly := [(nat_lit 2889, Int.ofNat (nat_lit 10139247820800)), (nat_lit 2890, Int.ofNat (nat_lit 10593488908800)), (nat_lit 2891, Int.ofNat (nat_lit 11047729996800)), (nat_lit 2892, Int.ofNat (nat_lit 21624024038400)), (nat_lit 2893, Int.ofNat (nat_lit 19839379392000)), (nat_lit 2894, Int.ofNat (nat_lit 33307519795200)), (nat_lit 2895, Int.ofNat (nat_lit 36744632870400)), (nat_lit 2896, Int.ofNat (nat_lit 47909475532800)), (nat_lit 2897, Int.ofNat (nat_lit 59097361881600)), (nat_lit 2910, Int.ofNat (nat_lit 8371086796800))]
theorem block017_data_flat057_step : block017_data_flat057 = (CoefficientMerge.fastMerge block017_data_flat047 block017_data_flat056) := by decide +kernel
theorem block017_data_flat057_original : block017_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10139247820800 : Int) atom1236Coded) (CoefficientMerge.scale (10593488908800 : Int) atom1237Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11047729996800 : Int) atom1238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21624024038400 : Int) atom1239Coded) (CoefficientMerge.scale (19839379392000 : Int) atom1240Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33307519795200 : Int) atom1241Coded) (CoefficientMerge.scale (36744632870400 : Int) atom1242Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47909475532800 : Int) atom1243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59097361881600 : Int) atom1244Coded) (CoefficientMerge.scale (8371086796800 : Int) atom1245Coded))))) := by
  rw [block017_data_flat057_step, block017_data_flat047_original, block017_data_flat056_original]
def block017_data_flat058 : CoefficientMerge.Poly := [(nat_lit 2911, Int.ofNat (nat_lit 16355585433600))]
theorem block017_data_flat058_step : block017_data_flat058 = (CoefficientMerge.scale (16355585433600 : Int) atom1246Coded) := by decide +kernel
theorem block017_data_flat058_original : block017_data_flat058 = (CoefficientMerge.scale (16355585433600 : Int) atom1246Coded) := by
  rw [block017_data_flat058_step]
def block017_data_flat059 : CoefficientMerge.Poly := [(nat_lit 2912, Int.ofNat (nat_lit 16396177190400))]
theorem block017_data_flat059_step : block017_data_flat059 = (CoefficientMerge.scale (16396177190400 : Int) atom1247Coded) := by decide +kernel
theorem block017_data_flat059_original : block017_data_flat059 = (CoefficientMerge.scale (16396177190400 : Int) atom1247Coded) := by
  rw [block017_data_flat059_step]
def block017_data_flat060 : CoefficientMerge.Poly := [(nat_lit 2911, Int.ofNat (nat_lit 16355585433600)), (nat_lit 2912, Int.ofNat (nat_lit 16396177190400))]
theorem block017_data_flat060_step : block017_data_flat060 = (CoefficientMerge.fastMerge block017_data_flat058 block017_data_flat059) := by decide +kernel
theorem block017_data_flat060_original : block017_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16355585433600 : Int) atom1246Coded) (CoefficientMerge.scale (16396177190400 : Int) atom1247Coded)) := by
  rw [block017_data_flat060_step, block017_data_flat058_original, block017_data_flat059_original]
def block017_data_flat061 : CoefficientMerge.Poly := [(nat_lit 2913, Int.ofNat (nat_lit 22971182707200))]
theorem block017_data_flat061_step : block017_data_flat061 = (CoefficientMerge.scale (22971182707200 : Int) atom1248Coded) := by decide +kernel
theorem block017_data_flat061_original : block017_data_flat061 = (CoefficientMerge.scale (22971182707200 : Int) atom1248Coded) := by
  rw [block017_data_flat061_step]
def block017_data_flat062 : CoefficientMerge.Poly := [(nat_lit 2914, Int.ofNat (nat_lit 23375330316800))]
theorem block017_data_flat062_step : block017_data_flat062 = (CoefficientMerge.scale (23375330316800 : Int) atom1249Coded) := by decide +kernel
theorem block017_data_flat062_original : block017_data_flat062 = (CoefficientMerge.scale (23375330316800 : Int) atom1249Coded) := by
  rw [block017_data_flat062_step]
def block017_data_flat063 : CoefficientMerge.Poly := [(nat_lit 2915, Int.ofNat (nat_lit 35615926976000))]
theorem block017_data_flat063_step : block017_data_flat063 = (CoefficientMerge.scale (35615926976000 : Int) atom1250Coded) := by decide +kernel
theorem block017_data_flat063_original : block017_data_flat063 = (CoefficientMerge.scale (35615926976000 : Int) atom1250Coded) := by
  rw [block017_data_flat063_step]
def block017_data_flat064 : CoefficientMerge.Poly := [(nat_lit 2914, Int.ofNat (nat_lit 23375330316800)), (nat_lit 2915, Int.ofNat (nat_lit 35615926976000))]
theorem block017_data_flat064_step : block017_data_flat064 = (CoefficientMerge.fastMerge block017_data_flat062 block017_data_flat063) := by decide +kernel
theorem block017_data_flat064_original : block017_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23375330316800 : Int) atom1249Coded) (CoefficientMerge.scale (35615926976000 : Int) atom1250Coded)) := by
  rw [block017_data_flat064_step, block017_data_flat062_original, block017_data_flat063_original]
def block017_data_flat065 : CoefficientMerge.Poly := [(nat_lit 2913, Int.ofNat (nat_lit 22971182707200)), (nat_lit 2914, Int.ofNat (nat_lit 23375330316800)), (nat_lit 2915, Int.ofNat (nat_lit 35615926976000))]
theorem block017_data_flat065_step : block017_data_flat065 = (CoefficientMerge.fastMerge block017_data_flat061 block017_data_flat064) := by decide +kernel
theorem block017_data_flat065_original : block017_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (22971182707200 : Int) atom1248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23375330316800 : Int) atom1249Coded) (CoefficientMerge.scale (35615926976000 : Int) atom1250Coded))) := by
  rw [block017_data_flat065_step, block017_data_flat061_original, block017_data_flat064_original]
def block017_data_flat066 : CoefficientMerge.Poly := [(nat_lit 2911, Int.ofNat (nat_lit 16355585433600)), (nat_lit 2912, Int.ofNat (nat_lit 16396177190400)), (nat_lit 2913, Int.ofNat (nat_lit 22971182707200)), (nat_lit 2914, Int.ofNat (nat_lit 23375330316800)), (nat_lit 2915, Int.ofNat (nat_lit 35615926976000))]
theorem block017_data_flat066_step : block017_data_flat066 = (CoefficientMerge.fastMerge block017_data_flat060 block017_data_flat065) := by decide +kernel
theorem block017_data_flat066_original : block017_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16355585433600 : Int) atom1246Coded) (CoefficientMerge.scale (16396177190400 : Int) atom1247Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22971182707200 : Int) atom1248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23375330316800 : Int) atom1249Coded) (CoefficientMerge.scale (35615926976000 : Int) atom1250Coded)))) := by
  rw [block017_data_flat066_step, block017_data_flat060_original, block017_data_flat065_original]
def block017_data_flat067 : CoefficientMerge.Poly := [(nat_lit 2916, Int.ofNat (nat_lit 39881932652800))]
theorem block017_data_flat067_step : block017_data_flat067 = (CoefficientMerge.scale (39881932652800 : Int) atom1251Coded) := by decide +kernel
theorem block017_data_flat067_original : block017_data_flat067 = (CoefficientMerge.scale (39881932652800 : Int) atom1251Coded) := by
  rw [block017_data_flat067_step]
def block017_data_flat068 : CoefficientMerge.Poly := [(nat_lit 2917, Int.ofNat (nat_lit 50170991001600))]
theorem block017_data_flat068_step : block017_data_flat068 = (CoefficientMerge.scale (50170991001600 : Int) atom1252Coded) := by decide +kernel
theorem block017_data_flat068_original : block017_data_flat068 = (CoefficientMerge.scale (50170991001600 : Int) atom1252Coded) := by
  rw [block017_data_flat068_step]
def block017_data_flat069 : CoefficientMerge.Poly := [(nat_lit 2916, Int.ofNat (nat_lit 39881932652800)), (nat_lit 2917, Int.ofNat (nat_lit 50170991001600))]
theorem block017_data_flat069_step : block017_data_flat069 = (CoefficientMerge.fastMerge block017_data_flat067 block017_data_flat068) := by decide +kernel
theorem block017_data_flat069_original : block017_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (39881932652800 : Int) atom1251Coded) (CoefficientMerge.scale (50170991001600 : Int) atom1252Coded)) := by
  rw [block017_data_flat069_step, block017_data_flat067_original, block017_data_flat068_original]
def block017_data_flat070 : CoefficientMerge.Poly := [(nat_lit 2918, Int.ofNat (nat_lit 61314928214400))]
theorem block017_data_flat070_step : block017_data_flat070 = (CoefficientMerge.scale (61314928214400 : Int) atom1253Coded) := by decide +kernel
theorem block017_data_flat070_original : block017_data_flat070 = (CoefficientMerge.scale (61314928214400 : Int) atom1253Coded) := by
  rw [block017_data_flat070_step]
def block017_data_flat071 : CoefficientMerge.Poly := [(nat_lit 2932, Int.ofNat (nat_lit 11705777856000))]
theorem block017_data_flat071_step : block017_data_flat071 = (CoefficientMerge.scale (11705777856000 : Int) atom1254Coded) := by decide +kernel
theorem block017_data_flat071_original : block017_data_flat071 = (CoefficientMerge.scale (11705777856000 : Int) atom1254Coded) := by
  rw [block017_data_flat071_step]
def block017_data_flat072 : CoefficientMerge.Poly := [(nat_lit 2933, Int.ofNat (nat_lit 21699798566400))]
theorem block017_data_flat072_step : block017_data_flat072 = (CoefficientMerge.scale (21699798566400 : Int) atom1255Coded) := by decide +kernel
theorem block017_data_flat072_original : block017_data_flat072 = (CoefficientMerge.scale (21699798566400 : Int) atom1255Coded) := by
  rw [block017_data_flat072_step]
def block017_data_flat073 : CoefficientMerge.Poly := [(nat_lit 2932, Int.ofNat (nat_lit 11705777856000)), (nat_lit 2933, Int.ofNat (nat_lit 21699798566400))]
theorem block017_data_flat073_step : block017_data_flat073 = (CoefficientMerge.fastMerge block017_data_flat071 block017_data_flat072) := by decide +kernel
theorem block017_data_flat073_original : block017_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (11705777856000 : Int) atom1254Coded) (CoefficientMerge.scale (21699798566400 : Int) atom1255Coded)) := by
  rw [block017_data_flat073_step, block017_data_flat071_original, block017_data_flat072_original]
def block017_data_flat074 : CoefficientMerge.Poly := [(nat_lit 2918, Int.ofNat (nat_lit 61314928214400)), (nat_lit 2932, Int.ofNat (nat_lit 11705777856000)), (nat_lit 2933, Int.ofNat (nat_lit 21699798566400))]
theorem block017_data_flat074_step : block017_data_flat074 = (CoefficientMerge.fastMerge block017_data_flat070 block017_data_flat073) := by decide +kernel
theorem block017_data_flat074_original : block017_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (61314928214400 : Int) atom1253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11705777856000 : Int) atom1254Coded) (CoefficientMerge.scale (21699798566400 : Int) atom1255Coded))) := by
  rw [block017_data_flat074_step, block017_data_flat070_original, block017_data_flat073_original]
def block017_data_flat075 : CoefficientMerge.Poly := [(nat_lit 2916, Int.ofNat (nat_lit 39881932652800)), (nat_lit 2917, Int.ofNat (nat_lit 50170991001600)), (nat_lit 2918, Int.ofNat (nat_lit 61314928214400)), (nat_lit 2932, Int.ofNat (nat_lit 11705777856000)), (nat_lit 2933, Int.ofNat (nat_lit 21699798566400))]
theorem block017_data_flat075_step : block017_data_flat075 = (CoefficientMerge.fastMerge block017_data_flat069 block017_data_flat074) := by decide +kernel
theorem block017_data_flat075_original : block017_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39881932652800 : Int) atom1251Coded) (CoefficientMerge.scale (50170991001600 : Int) atom1252Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61314928214400 : Int) atom1253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11705777856000 : Int) atom1254Coded) (CoefficientMerge.scale (21699798566400 : Int) atom1255Coded)))) := by
  rw [block017_data_flat075_step, block017_data_flat069_original, block017_data_flat074_original]
def block017_data_flat076 : CoefficientMerge.Poly := [(nat_lit 2911, Int.ofNat (nat_lit 16355585433600)), (nat_lit 2912, Int.ofNat (nat_lit 16396177190400)), (nat_lit 2913, Int.ofNat (nat_lit 22971182707200)), (nat_lit 2914, Int.ofNat (nat_lit 23375330316800)), (nat_lit 2915, Int.ofNat (nat_lit 35615926976000)), (nat_lit 2916, Int.ofNat (nat_lit 39881932652800)), (nat_lit 2917, Int.ofNat (nat_lit 50170991001600)), (nat_lit 2918, Int.ofNat (nat_lit 61314928214400)), (nat_lit 2932, Int.ofNat (nat_lit 11705777856000)), (nat_lit 2933, Int.ofNat (nat_lit 21699798566400))]
theorem block017_data_flat076_step : block017_data_flat076 = (CoefficientMerge.fastMerge block017_data_flat066 block017_data_flat075) := by decide +kernel
theorem block017_data_flat076_original : block017_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16355585433600 : Int) atom1246Coded) (CoefficientMerge.scale (16396177190400 : Int) atom1247Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22971182707200 : Int) atom1248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23375330316800 : Int) atom1249Coded) (CoefficientMerge.scale (35615926976000 : Int) atom1250Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39881932652800 : Int) atom1251Coded) (CoefficientMerge.scale (50170991001600 : Int) atom1252Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61314928214400 : Int) atom1253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11705777856000 : Int) atom1254Coded) (CoefficientMerge.scale (21699798566400 : Int) atom1255Coded))))) := by
  rw [block017_data_flat076_step, block017_data_flat066_original, block017_data_flat075_original]
def block017_data_flat077 : CoefficientMerge.Poly := [(nat_lit 2889, Int.ofNat (nat_lit 10139247820800)), (nat_lit 2890, Int.ofNat (nat_lit 10593488908800)), (nat_lit 2891, Int.ofNat (nat_lit 11047729996800)), (nat_lit 2892, Int.ofNat (nat_lit 21624024038400)), (nat_lit 2893, Int.ofNat (nat_lit 19839379392000)), (nat_lit 2894, Int.ofNat (nat_lit 33307519795200)), (nat_lit 2895, Int.ofNat (nat_lit 36744632870400)), (nat_lit 2896, Int.ofNat (nat_lit 47909475532800)), (nat_lit 2897, Int.ofNat (nat_lit 59097361881600)), (nat_lit 2910, Int.ofNat (nat_lit 8371086796800)), (nat_lit 2911, Int.ofNat (nat_lit 16355585433600)), (nat_lit 2912, Int.ofNat (nat_lit 16396177190400)), (nat_lit 2913, Int.ofNat (nat_lit 22971182707200)), (nat_lit 2914, Int.ofNat (nat_lit 23375330316800)), (nat_lit 2915, Int.ofNat (nat_lit 35615926976000)), (nat_lit 2916, Int.ofNat (nat_lit 39881932652800)), (nat_lit 2917, Int.ofNat (nat_lit 50170991001600)), (nat_lit 2918, Int.ofNat (nat_lit 61314928214400)), (nat_lit 2932, Int.ofNat (nat_lit 11705777856000)), (nat_lit 2933, Int.ofNat (nat_lit 21699798566400))]
theorem block017_data_flat077_step : block017_data_flat077 = (CoefficientMerge.fastMerge block017_data_flat057 block017_data_flat076) := by decide +kernel
theorem block017_data_flat077_original : block017_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10139247820800 : Int) atom1236Coded) (CoefficientMerge.scale (10593488908800 : Int) atom1237Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11047729996800 : Int) atom1238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21624024038400 : Int) atom1239Coded) (CoefficientMerge.scale (19839379392000 : Int) atom1240Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33307519795200 : Int) atom1241Coded) (CoefficientMerge.scale (36744632870400 : Int) atom1242Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47909475532800 : Int) atom1243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59097361881600 : Int) atom1244Coded) (CoefficientMerge.scale (8371086796800 : Int) atom1245Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16355585433600 : Int) atom1246Coded) (CoefficientMerge.scale (16396177190400 : Int) atom1247Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22971182707200 : Int) atom1248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23375330316800 : Int) atom1249Coded) (CoefficientMerge.scale (35615926976000 : Int) atom1250Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39881932652800 : Int) atom1251Coded) (CoefficientMerge.scale (50170991001600 : Int) atom1252Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61314928214400 : Int) atom1253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11705777856000 : Int) atom1254Coded) (CoefficientMerge.scale (21699798566400 : Int) atom1255Coded)))))) := by
  rw [block017_data_flat077_step, block017_data_flat057_original, block017_data_flat076_original]
def block017_data_flat078 : CoefficientMerge.Poly := [(nat_lit 2848, Int.ofNat (nat_lit 2066320569600)), (nat_lit 2849, Int.ofNat (nat_lit 2843362771200)), (nat_lit 2850, Int.ofNat (nat_lit 12526751865600)), (nat_lit 2851, Int.ofNat (nat_lit 9755314884000)), (nat_lit 2852, Int.ofNat (nat_lit 17449540819200)), (nat_lit 2853, Int.ofNat (nat_lit 24820650338400)), (nat_lit 2854, Int.ofNat (nat_lit 35164296367200)), (nat_lit 2855, Int.ofNat (nat_lit 45787493959200)), (nat_lit 2866, Int.ofNat (nat_lit 3204336038400)), (nat_lit 2867, Int.ofNat (nat_lit 5399676979200)), (nat_lit 2868, Int.ofNat (nat_lit 5672221632000)), (nat_lit 2869, Int.ofNat (nat_lit 6371946201600)), (nat_lit 2870, Int.ofNat (nat_lit 7071670771200)), (nat_lit 2871, Int.ofNat (nat_lit 17374084156800)), (nat_lit 2872, Int.ofNat (nat_lit 15150394274400)), (nat_lit 2873, Int.ofNat (nat_lit 25703681270400)), (nat_lit 2874, Int.ofNat (nat_lit 31388299941600)), (nat_lit 2875, Int.ofNat (nat_lit 42276310423200)), (nat_lit 2876, Int.ofNat (nat_lit 53312311684800)), (nat_lit 2888, Int.ofNat (nat_lit 5780946124800)), (nat_lit 2889, Int.ofNat (nat_lit 10139247820800)), (nat_lit 2890, Int.ofNat (nat_lit 10593488908800)), (nat_lit 2891, Int.ofNat (nat_lit 11047729996800)), (nat_lit 2892, Int.ofNat (nat_lit 21624024038400)), (nat_lit 2893, Int.ofNat (nat_lit 19839379392000)), (nat_lit 2894, Int.ofNat (nat_lit 33307519795200)), (nat_lit 2895, Int.ofNat (nat_lit 36744632870400)), (nat_lit 2896, Int.ofNat (nat_lit 47909475532800)), (nat_lit 2897, Int.ofNat (nat_lit 59097361881600)), (nat_lit 2910, Int.ofNat (nat_lit 8371086796800)), (nat_lit 2911, Int.ofNat (nat_lit 16355585433600)), (nat_lit 2912, Int.ofNat (nat_lit 16396177190400)), (nat_lit 2913, Int.ofNat (nat_lit 22971182707200)), (nat_lit 2914, Int.ofNat (nat_lit 23375330316800)), (nat_lit 2915, Int.ofNat (nat_lit 35615926976000)), (nat_lit 2916, Int.ofNat (nat_lit 39881932652800)), (nat_lit 2917, Int.ofNat (nat_lit 50170991001600)), (nat_lit 2918, Int.ofNat (nat_lit 61314928214400)), (nat_lit 2932, Int.ofNat (nat_lit 11705777856000)), (nat_lit 2933, Int.ofNat (nat_lit 21699798566400))]
theorem block017_data_flat078_step : block017_data_flat078 = (CoefficientMerge.fastMerge block017_data_flat038 block017_data_flat077) := by decide +kernel
theorem block017_data_flat078_original : block017_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2066320569600 : Int) atom1216Coded) (CoefficientMerge.scale (2843362771200 : Int) atom1217Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12526751865600 : Int) atom1218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9755314884000 : Int) atom1219Coded) (CoefficientMerge.scale (17449540819200 : Int) atom1220Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24820650338400 : Int) atom1221Coded) (CoefficientMerge.scale (35164296367200 : Int) atom1222Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45787493959200 : Int) atom1223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3204336038400 : Int) atom1224Coded) (CoefficientMerge.scale (5399676979200 : Int) atom1225Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5672221632000 : Int) atom1226Coded) (CoefficientMerge.scale (6371946201600 : Int) atom1227Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7071670771200 : Int) atom1228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17374084156800 : Int) atom1229Coded) (CoefficientMerge.scale (15150394274400 : Int) atom1230Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25703681270400 : Int) atom1231Coded) (CoefficientMerge.scale (31388299941600 : Int) atom1232Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42276310423200 : Int) atom1233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53312311684800 : Int) atom1234Coded) (CoefficientMerge.scale (5780946124800 : Int) atom1235Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10139247820800 : Int) atom1236Coded) (CoefficientMerge.scale (10593488908800 : Int) atom1237Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11047729996800 : Int) atom1238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21624024038400 : Int) atom1239Coded) (CoefficientMerge.scale (19839379392000 : Int) atom1240Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33307519795200 : Int) atom1241Coded) (CoefficientMerge.scale (36744632870400 : Int) atom1242Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47909475532800 : Int) atom1243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59097361881600 : Int) atom1244Coded) (CoefficientMerge.scale (8371086796800 : Int) atom1245Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16355585433600 : Int) atom1246Coded) (CoefficientMerge.scale (16396177190400 : Int) atom1247Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22971182707200 : Int) atom1248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23375330316800 : Int) atom1249Coded) (CoefficientMerge.scale (35615926976000 : Int) atom1250Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39881932652800 : Int) atom1251Coded) (CoefficientMerge.scale (50170991001600 : Int) atom1252Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61314928214400 : Int) atom1253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11705777856000 : Int) atom1254Coded) (CoefficientMerge.scale (21699798566400 : Int) atom1255Coded))))))) := by
  rw [block017_data_flat078_step, block017_data_flat038_original, block017_data_flat077_original]
def block017_data_flat079 : CoefficientMerge.Poly := [(nat_lit 2934, Int.ofNat (nat_lit 27731989051200))]
theorem block017_data_flat079_step : block017_data_flat079 = (CoefficientMerge.scale (27731989051200 : Int) atom1256Coded) := by decide +kernel
theorem block017_data_flat079_original : block017_data_flat079 = (CoefficientMerge.scale (27731989051200 : Int) atom1256Coded) := by
  rw [block017_data_flat079_step]
def block017_data_flat080 : CoefficientMerge.Poly := [(nat_lit 2935, Int.ofNat (nat_lit 27457319044800))]
theorem block017_data_flat080_step : block017_data_flat080 = (CoefficientMerge.scale (27457319044800 : Int) atom1257Coded) := by decide +kernel
theorem block017_data_flat080_original : block017_data_flat080 = (CoefficientMerge.scale (27457319044800 : Int) atom1257Coded) := by
  rw [block017_data_flat080_step]
def block017_data_flat081 : CoefficientMerge.Poly := [(nat_lit 2934, Int.ofNat (nat_lit 27731989051200)), (nat_lit 2935, Int.ofNat (nat_lit 27457319044800))]
theorem block017_data_flat081_step : block017_data_flat081 = (CoefficientMerge.fastMerge block017_data_flat079 block017_data_flat080) := by decide +kernel
theorem block017_data_flat081_original : block017_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (27731989051200 : Int) atom1256Coded) (CoefficientMerge.scale (27457319044800 : Int) atom1257Coded)) := by
  rw [block017_data_flat081_step, block017_data_flat079_original, block017_data_flat080_original]
def block017_data_flat082 : CoefficientMerge.Poly := [(nat_lit 2936, Int.ofNat (nat_lit 42282031276800))]
theorem block017_data_flat082_step : block017_data_flat082 = (CoefficientMerge.scale (42282031276800 : Int) atom1258Coded) := by decide +kernel
theorem block017_data_flat082_original : block017_data_flat082 = (CoefficientMerge.scale (42282031276800 : Int) atom1258Coded) := by
  rw [block017_data_flat082_step]
def block017_data_flat083 : CoefficientMerge.Poly := [(nat_lit 2937, Int.ofNat (nat_lit 47812699267200))]
theorem block017_data_flat083_step : block017_data_flat083 = (CoefficientMerge.scale (47812699267200 : Int) atom1259Coded) := by decide +kernel
theorem block017_data_flat083_original : block017_data_flat083 = (CoefficientMerge.scale (47812699267200 : Int) atom1259Coded) := by
  rw [block017_data_flat083_step]
def block017_data_flat084 : CoefficientMerge.Poly := [(nat_lit 2938, Int.ofNat (nat_lit 51497513812800))]
theorem block017_data_flat084_step : block017_data_flat084 = (CoefficientMerge.scale (51497513812800 : Int) atom1260Coded) := by decide +kernel
theorem block017_data_flat084_original : block017_data_flat084 = (CoefficientMerge.scale (51497513812800 : Int) atom1260Coded) := by
  rw [block017_data_flat084_step]
def block017_data_flat085 : CoefficientMerge.Poly := [(nat_lit 2937, Int.ofNat (nat_lit 47812699267200)), (nat_lit 2938, Int.ofNat (nat_lit 51497513812800))]
theorem block017_data_flat085_step : block017_data_flat085 = (CoefficientMerge.fastMerge block017_data_flat083 block017_data_flat084) := by decide +kernel
theorem block017_data_flat085_original : block017_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (47812699267200 : Int) atom1259Coded) (CoefficientMerge.scale (51497513812800 : Int) atom1260Coded)) := by
  rw [block017_data_flat085_step, block017_data_flat083_original, block017_data_flat084_original]
def block017_data_flat086 : CoefficientMerge.Poly := [(nat_lit 2936, Int.ofNat (nat_lit 42282031276800)), (nat_lit 2937, Int.ofNat (nat_lit 47812699267200)), (nat_lit 2938, Int.ofNat (nat_lit 51497513812800))]
theorem block017_data_flat086_step : block017_data_flat086 = (CoefficientMerge.fastMerge block017_data_flat082 block017_data_flat085) := by decide +kernel
theorem block017_data_flat086_original : block017_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (42282031276800 : Int) atom1258Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47812699267200 : Int) atom1259Coded) (CoefficientMerge.scale (51497513812800 : Int) atom1260Coded))) := by
  rw [block017_data_flat086_step, block017_data_flat082_original, block017_data_flat085_original]
def block017_data_flat087 : CoefficientMerge.Poly := [(nat_lit 2934, Int.ofNat (nat_lit 27731989051200)), (nat_lit 2935, Int.ofNat (nat_lit 27457319044800)), (nat_lit 2936, Int.ofNat (nat_lit 42282031276800)), (nat_lit 2937, Int.ofNat (nat_lit 47812699267200)), (nat_lit 2938, Int.ofNat (nat_lit 51497513812800))]
theorem block017_data_flat087_step : block017_data_flat087 = (CoefficientMerge.fastMerge block017_data_flat081 block017_data_flat086) := by decide +kernel
theorem block017_data_flat087_original : block017_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27731989051200 : Int) atom1256Coded) (CoefficientMerge.scale (27457319044800 : Int) atom1257Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42282031276800 : Int) atom1258Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47812699267200 : Int) atom1259Coded) (CoefficientMerge.scale (51497513812800 : Int) atom1260Coded)))) := by
  rw [block017_data_flat087_step, block017_data_flat081_original, block017_data_flat086_original]
def block017_data_flat088 : CoefficientMerge.Poly := [(nat_lit 2939, Int.ofNat (nat_lit 68517790488000))]
theorem block017_data_flat088_step : block017_data_flat088 = (CoefficientMerge.scale (68517790488000 : Int) atom1261Coded) := by decide +kernel
theorem block017_data_flat088_original : block017_data_flat088 = (CoefficientMerge.scale (68517790488000 : Int) atom1261Coded) := by
  rw [block017_data_flat088_step]
def block017_data_flat089 : CoefficientMerge.Poly := [(nat_lit 2954, Int.ofNat (nat_lit 15983651980800))]
theorem block017_data_flat089_step : block017_data_flat089 = (CoefficientMerge.scale (15983651980800 : Int) atom1262Coded) := by decide +kernel
theorem block017_data_flat089_original : block017_data_flat089 = (CoefficientMerge.scale (15983651980800 : Int) atom1262Coded) := by
  rw [block017_data_flat089_step]
def block017_data_flat090 : CoefficientMerge.Poly := [(nat_lit 2939, Int.ofNat (nat_lit 68517790488000)), (nat_lit 2954, Int.ofNat (nat_lit 15983651980800))]
theorem block017_data_flat090_step : block017_data_flat090 = (CoefficientMerge.fastMerge block017_data_flat088 block017_data_flat089) := by decide +kernel
theorem block017_data_flat090_original : block017_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517790488000 : Int) atom1261Coded) (CoefficientMerge.scale (15983651980800 : Int) atom1262Coded)) := by
  rw [block017_data_flat090_step, block017_data_flat088_original, block017_data_flat089_original]
def block017_data_flat091 : CoefficientMerge.Poly := [(nat_lit 2955, Int.ofNat (nat_lit 32380953292800))]
theorem block017_data_flat091_step : block017_data_flat091 = (CoefficientMerge.scale (32380953292800 : Int) atom1263Coded) := by decide +kernel
theorem block017_data_flat091_original : block017_data_flat091 = (CoefficientMerge.scale (32380953292800 : Int) atom1263Coded) := by
  rw [block017_data_flat091_step]
def block017_data_flat092 : CoefficientMerge.Poly := [(nat_lit 2956, Int.ofNat (nat_lit 31420158336000))]
theorem block017_data_flat092_step : block017_data_flat092 = (CoefficientMerge.scale (31420158336000 : Int) atom1264Coded) := by decide +kernel
theorem block017_data_flat092_original : block017_data_flat092 = (CoefficientMerge.scale (31420158336000 : Int) atom1264Coded) := by
  rw [block017_data_flat092_step]
def block017_data_flat093 : CoefficientMerge.Poly := [(nat_lit 2957, Int.ofNat (nat_lit 51141665433600))]
theorem block017_data_flat093_step : block017_data_flat093 = (CoefficientMerge.scale (51141665433600 : Int) atom1265Coded) := by decide +kernel
theorem block017_data_flat093_original : block017_data_flat093 = (CoefficientMerge.scale (51141665433600 : Int) atom1265Coded) := by
  rw [block017_data_flat093_step]
def block017_data_flat094 : CoefficientMerge.Poly := [(nat_lit 2956, Int.ofNat (nat_lit 31420158336000)), (nat_lit 2957, Int.ofNat (nat_lit 51141665433600))]
theorem block017_data_flat094_step : block017_data_flat094 = (CoefficientMerge.fastMerge block017_data_flat092 block017_data_flat093) := by decide +kernel
theorem block017_data_flat094_original : block017_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (31420158336000 : Int) atom1264Coded) (CoefficientMerge.scale (51141665433600 : Int) atom1265Coded)) := by
  rw [block017_data_flat094_step, block017_data_flat092_original, block017_data_flat093_original]
def block017_data_flat095 : CoefficientMerge.Poly := [(nat_lit 2955, Int.ofNat (nat_lit 32380953292800)), (nat_lit 2956, Int.ofNat (nat_lit 31420158336000)), (nat_lit 2957, Int.ofNat (nat_lit 51141665433600))]
theorem block017_data_flat095_step : block017_data_flat095 = (CoefficientMerge.fastMerge block017_data_flat091 block017_data_flat094) := by decide +kernel
theorem block017_data_flat095_original : block017_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (32380953292800 : Int) atom1263Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31420158336000 : Int) atom1264Coded) (CoefficientMerge.scale (51141665433600 : Int) atom1265Coded))) := by
  rw [block017_data_flat095_step, block017_data_flat091_original, block017_data_flat094_original]
def block017_data_flat096 : CoefficientMerge.Poly := [(nat_lit 2939, Int.ofNat (nat_lit 68517790488000)), (nat_lit 2954, Int.ofNat (nat_lit 15983651980800)), (nat_lit 2955, Int.ofNat (nat_lit 32380953292800)), (nat_lit 2956, Int.ofNat (nat_lit 31420158336000)), (nat_lit 2957, Int.ofNat (nat_lit 51141665433600))]
theorem block017_data_flat096_step : block017_data_flat096 = (CoefficientMerge.fastMerge block017_data_flat090 block017_data_flat095) := by decide +kernel
theorem block017_data_flat096_original : block017_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517790488000 : Int) atom1261Coded) (CoefficientMerge.scale (15983651980800 : Int) atom1262Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32380953292800 : Int) atom1263Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31420158336000 : Int) atom1264Coded) (CoefficientMerge.scale (51141665433600 : Int) atom1265Coded)))) := by
  rw [block017_data_flat096_step, block017_data_flat090_original, block017_data_flat095_original]
def block017_data_flat097 : CoefficientMerge.Poly := [(nat_lit 2934, Int.ofNat (nat_lit 27731989051200)), (nat_lit 2935, Int.ofNat (nat_lit 27457319044800)), (nat_lit 2936, Int.ofNat (nat_lit 42282031276800)), (nat_lit 2937, Int.ofNat (nat_lit 47812699267200)), (nat_lit 2938, Int.ofNat (nat_lit 51497513812800)), (nat_lit 2939, Int.ofNat (nat_lit 68517790488000)), (nat_lit 2954, Int.ofNat (nat_lit 15983651980800)), (nat_lit 2955, Int.ofNat (nat_lit 32380953292800)), (nat_lit 2956, Int.ofNat (nat_lit 31420158336000)), (nat_lit 2957, Int.ofNat (nat_lit 51141665433600))]
theorem block017_data_flat097_step : block017_data_flat097 = (CoefficientMerge.fastMerge block017_data_flat087 block017_data_flat096) := by decide +kernel
theorem block017_data_flat097_original : block017_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27731989051200 : Int) atom1256Coded) (CoefficientMerge.scale (27457319044800 : Int) atom1257Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42282031276800 : Int) atom1258Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47812699267200 : Int) atom1259Coded) (CoefficientMerge.scale (51497513812800 : Int) atom1260Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517790488000 : Int) atom1261Coded) (CoefficientMerge.scale (15983651980800 : Int) atom1262Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32380953292800 : Int) atom1263Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31420158336000 : Int) atom1264Coded) (CoefficientMerge.scale (51141665433600 : Int) atom1265Coded))))) := by
  rw [block017_data_flat097_step, block017_data_flat087_original, block017_data_flat096_original]
def block017_data_flat098 : CoefficientMerge.Poly := [(nat_lit 2958, Int.ofNat (nat_lit 58156348723200))]
theorem block017_data_flat098_step : block017_data_flat098 = (CoefficientMerge.scale (58156348723200 : Int) atom1266Coded) := by decide +kernel
theorem block017_data_flat098_original : block017_data_flat098 = (CoefficientMerge.scale (58156348723200 : Int) atom1266Coded) := by
  rw [block017_data_flat098_step]
def block017_data_flat099 : CoefficientMerge.Poly := [(nat_lit 2959, Int.ofNat (nat_lit 57274763212800))]
theorem block017_data_flat099_step : block017_data_flat099 = (CoefficientMerge.scale (57274763212800 : Int) atom1267Coded) := by decide +kernel
theorem block017_data_flat099_original : block017_data_flat099 = (CoefficientMerge.scale (57274763212800 : Int) atom1267Coded) := by
  rw [block017_data_flat099_step]
def block017_data_flat100 : CoefficientMerge.Poly := [(nat_lit 2958, Int.ofNat (nat_lit 58156348723200)), (nat_lit 2959, Int.ofNat (nat_lit 57274763212800))]
theorem block017_data_flat100_step : block017_data_flat100 = (CoefficientMerge.fastMerge block017_data_flat098 block017_data_flat099) := by decide +kernel
theorem block017_data_flat100_original : block017_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (58156348723200 : Int) atom1266Coded) (CoefficientMerge.scale (57274763212800 : Int) atom1267Coded)) := by
  rw [block017_data_flat100_step, block017_data_flat098_original, block017_data_flat099_original]
def block017_data_flat101 : CoefficientMerge.Poly := [(nat_lit 2960, Int.ofNat (nat_lit 80303655398400))]
theorem block017_data_flat101_step : block017_data_flat101 = (CoefficientMerge.scale (80303655398400 : Int) atom1268Coded) := by decide +kernel
theorem block017_data_flat101_original : block017_data_flat101 = (CoefficientMerge.scale (80303655398400 : Int) atom1268Coded) := by
  rw [block017_data_flat101_step]
def block017_data_flat102 : CoefficientMerge.Poly := [(nat_lit 2976, Int.ofNat (nat_lit 23458334054400))]
theorem block017_data_flat102_step : block017_data_flat102 = (CoefficientMerge.scale (23458334054400 : Int) atom1269Coded) := by decide +kernel
theorem block017_data_flat102_original : block017_data_flat102 = (CoefficientMerge.scale (23458334054400 : Int) atom1269Coded) := by
  rw [block017_data_flat102_step]
def block017_data_flat103 : CoefficientMerge.Poly := [(nat_lit 2977, Int.ofNat (nat_lit 44424079257600))]
theorem block017_data_flat103_step : block017_data_flat103 = (CoefficientMerge.scale (44424079257600 : Int) atom1270Coded) := by decide +kernel
theorem block017_data_flat103_original : block017_data_flat103 = (CoefficientMerge.scale (44424079257600 : Int) atom1270Coded) := by
  rw [block017_data_flat103_step]
def block017_data_flat104 : CoefficientMerge.Poly := [(nat_lit 2976, Int.ofNat (nat_lit 23458334054400)), (nat_lit 2977, Int.ofNat (nat_lit 44424079257600))]
theorem block017_data_flat104_step : block017_data_flat104 = (CoefficientMerge.fastMerge block017_data_flat102 block017_data_flat103) := by decide +kernel
theorem block017_data_flat104_original : block017_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23458334054400 : Int) atom1269Coded) (CoefficientMerge.scale (44424079257600 : Int) atom1270Coded)) := by
  rw [block017_data_flat104_step, block017_data_flat102_original, block017_data_flat103_original]
def block017_data_flat105 : CoefficientMerge.Poly := [(nat_lit 2960, Int.ofNat (nat_lit 80303655398400)), (nat_lit 2976, Int.ofNat (nat_lit 23458334054400)), (nat_lit 2977, Int.ofNat (nat_lit 44424079257600))]
theorem block017_data_flat105_step : block017_data_flat105 = (CoefficientMerge.fastMerge block017_data_flat101 block017_data_flat104) := by decide +kernel
theorem block017_data_flat105_original : block017_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (80303655398400 : Int) atom1268Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23458334054400 : Int) atom1269Coded) (CoefficientMerge.scale (44424079257600 : Int) atom1270Coded))) := by
  rw [block017_data_flat105_step, block017_data_flat101_original, block017_data_flat104_original]
def block017_data_flat106 : CoefficientMerge.Poly := [(nat_lit 2958, Int.ofNat (nat_lit 58156348723200)), (nat_lit 2959, Int.ofNat (nat_lit 57274763212800)), (nat_lit 2960, Int.ofNat (nat_lit 80303655398400)), (nat_lit 2976, Int.ofNat (nat_lit 23458334054400)), (nat_lit 2977, Int.ofNat (nat_lit 44424079257600))]
theorem block017_data_flat106_step : block017_data_flat106 = (CoefficientMerge.fastMerge block017_data_flat100 block017_data_flat105) := by decide +kernel
theorem block017_data_flat106_original : block017_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58156348723200 : Int) atom1266Coded) (CoefficientMerge.scale (57274763212800 : Int) atom1267Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80303655398400 : Int) atom1268Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23458334054400 : Int) atom1269Coded) (CoefficientMerge.scale (44424079257600 : Int) atom1270Coded)))) := by
  rw [block017_data_flat106_step, block017_data_flat100_original, block017_data_flat105_original]
def block017_data_flat107 : CoefficientMerge.Poly := [(nat_lit 2978, Int.ofNat (nat_lit 68201800934400))]
theorem block017_data_flat107_step : block017_data_flat107 = (CoefficientMerge.scale (68201800934400 : Int) atom1271Coded) := by decide +kernel
theorem block017_data_flat107_original : block017_data_flat107 = (CoefficientMerge.scale (68201800934400 : Int) atom1271Coded) := by
  rw [block017_data_flat107_step]
def block017_data_flat108 : CoefficientMerge.Poly := [(nat_lit 2979, Int.ofNat (nat_lit 70646230771200))]
theorem block017_data_flat108_step : block017_data_flat108 = (CoefficientMerge.scale (70646230771200 : Int) atom1272Coded) := by decide +kernel
theorem block017_data_flat108_original : block017_data_flat108 = (CoefficientMerge.scale (70646230771200 : Int) atom1272Coded) := by
  rw [block017_data_flat108_step]
def block017_data_flat109 : CoefficientMerge.Poly := [(nat_lit 2978, Int.ofNat (nat_lit 68201800934400)), (nat_lit 2979, Int.ofNat (nat_lit 70646230771200))]
theorem block017_data_flat109_step : block017_data_flat109 = (CoefficientMerge.fastMerge block017_data_flat107 block017_data_flat108) := by decide +kernel
theorem block017_data_flat109_original : block017_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (68201800934400 : Int) atom1271Coded) (CoefficientMerge.scale (70646230771200 : Int) atom1272Coded)) := by
  rw [block017_data_flat109_step, block017_data_flat107_original, block017_data_flat108_original]
def block017_data_flat110 : CoefficientMerge.Poly := [(nat_lit 2980, Int.ofNat (nat_lit 52545926361600))]
theorem block017_data_flat110_step : block017_data_flat110 = (CoefficientMerge.scale (52545926361600 : Int) atom1273Coded) := by decide +kernel
theorem block017_data_flat110_original : block017_data_flat110 = (CoefficientMerge.scale (52545926361600 : Int) atom1273Coded) := by
  rw [block017_data_flat110_step]
def block017_data_flat111 : CoefficientMerge.Poly := [(nat_lit 2981, Int.ofNat (nat_lit 79011669542400))]
theorem block017_data_flat111_step : block017_data_flat111 = (CoefficientMerge.scale (79011669542400 : Int) atom1274Coded) := by decide +kernel
theorem block017_data_flat111_original : block017_data_flat111 = (CoefficientMerge.scale (79011669542400 : Int) atom1274Coded) := by
  rw [block017_data_flat111_step]
def block017_data_flat112 : CoefficientMerge.Poly := [(nat_lit 2998, Int.ofNat (nat_lit 17545854735360))]
theorem block017_data_flat112_step : block017_data_flat112 = (CoefficientMerge.scale (17545854735360 : Int) atom1275Coded) := by decide +kernel
theorem block017_data_flat112_original : block017_data_flat112 = (CoefficientMerge.scale (17545854735360 : Int) atom1275Coded) := by
  rw [block017_data_flat112_step]
def block017_data_flat113 : CoefficientMerge.Poly := [(nat_lit 2981, Int.ofNat (nat_lit 79011669542400)), (nat_lit 2998, Int.ofNat (nat_lit 17545854735360))]
theorem block017_data_flat113_step : block017_data_flat113 = (CoefficientMerge.fastMerge block017_data_flat111 block017_data_flat112) := by decide +kernel
theorem block017_data_flat113_original : block017_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (79011669542400 : Int) atom1274Coded) (CoefficientMerge.scale (17545854735360 : Int) atom1275Coded)) := by
  rw [block017_data_flat113_step, block017_data_flat111_original, block017_data_flat112_original]
def block017_data_flat114 : CoefficientMerge.Poly := [(nat_lit 2980, Int.ofNat (nat_lit 52545926361600)), (nat_lit 2981, Int.ofNat (nat_lit 79011669542400)), (nat_lit 2998, Int.ofNat (nat_lit 17545854735360))]
theorem block017_data_flat114_step : block017_data_flat114 = (CoefficientMerge.fastMerge block017_data_flat110 block017_data_flat113) := by decide +kernel
theorem block017_data_flat114_original : block017_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (52545926361600 : Int) atom1273Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79011669542400 : Int) atom1274Coded) (CoefficientMerge.scale (17545854735360 : Int) atom1275Coded))) := by
  rw [block017_data_flat114_step, block017_data_flat110_original, block017_data_flat113_original]
def block017_data_flat115 : CoefficientMerge.Poly := [(nat_lit 2978, Int.ofNat (nat_lit 68201800934400)), (nat_lit 2979, Int.ofNat (nat_lit 70646230771200)), (nat_lit 2980, Int.ofNat (nat_lit 52545926361600)), (nat_lit 2981, Int.ofNat (nat_lit 79011669542400)), (nat_lit 2998, Int.ofNat (nat_lit 17545854735360))]
theorem block017_data_flat115_step : block017_data_flat115 = (CoefficientMerge.fastMerge block017_data_flat109 block017_data_flat114) := by decide +kernel
theorem block017_data_flat115_original : block017_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68201800934400 : Int) atom1271Coded) (CoefficientMerge.scale (70646230771200 : Int) atom1272Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52545926361600 : Int) atom1273Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79011669542400 : Int) atom1274Coded) (CoefficientMerge.scale (17545854735360 : Int) atom1275Coded)))) := by
  rw [block017_data_flat115_step, block017_data_flat109_original, block017_data_flat114_original]
def block017_data_flat116 : CoefficientMerge.Poly := [(nat_lit 2958, Int.ofNat (nat_lit 58156348723200)), (nat_lit 2959, Int.ofNat (nat_lit 57274763212800)), (nat_lit 2960, Int.ofNat (nat_lit 80303655398400)), (nat_lit 2976, Int.ofNat (nat_lit 23458334054400)), (nat_lit 2977, Int.ofNat (nat_lit 44424079257600)), (nat_lit 2978, Int.ofNat (nat_lit 68201800934400)), (nat_lit 2979, Int.ofNat (nat_lit 70646230771200)), (nat_lit 2980, Int.ofNat (nat_lit 52545926361600)), (nat_lit 2981, Int.ofNat (nat_lit 79011669542400)), (nat_lit 2998, Int.ofNat (nat_lit 17545854735360))]
theorem block017_data_flat116_step : block017_data_flat116 = (CoefficientMerge.fastMerge block017_data_flat106 block017_data_flat115) := by decide +kernel
theorem block017_data_flat116_original : block017_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58156348723200 : Int) atom1266Coded) (CoefficientMerge.scale (57274763212800 : Int) atom1267Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80303655398400 : Int) atom1268Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23458334054400 : Int) atom1269Coded) (CoefficientMerge.scale (44424079257600 : Int) atom1270Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68201800934400 : Int) atom1271Coded) (CoefficientMerge.scale (70646230771200 : Int) atom1272Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52545926361600 : Int) atom1273Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79011669542400 : Int) atom1274Coded) (CoefficientMerge.scale (17545854735360 : Int) atom1275Coded))))) := by
  rw [block017_data_flat116_step, block017_data_flat106_original, block017_data_flat115_original]
def block017_data_flat117 : CoefficientMerge.Poly := [(nat_lit 2934, Int.ofNat (nat_lit 27731989051200)), (nat_lit 2935, Int.ofNat (nat_lit 27457319044800)), (nat_lit 2936, Int.ofNat (nat_lit 42282031276800)), (nat_lit 2937, Int.ofNat (nat_lit 47812699267200)), (nat_lit 2938, Int.ofNat (nat_lit 51497513812800)), (nat_lit 2939, Int.ofNat (nat_lit 68517790488000)), (nat_lit 2954, Int.ofNat (nat_lit 15983651980800)), (nat_lit 2955, Int.ofNat (nat_lit 32380953292800)), (nat_lit 2956, Int.ofNat (nat_lit 31420158336000)), (nat_lit 2957, Int.ofNat (nat_lit 51141665433600)), (nat_lit 2958, Int.ofNat (nat_lit 58156348723200)), (nat_lit 2959, Int.ofNat (nat_lit 57274763212800)), (nat_lit 2960, Int.ofNat (nat_lit 80303655398400)), (nat_lit 2976, Int.ofNat (nat_lit 23458334054400)), (nat_lit 2977, Int.ofNat (nat_lit 44424079257600)), (nat_lit 2978, Int.ofNat (nat_lit 68201800934400)), (nat_lit 2979, Int.ofNat (nat_lit 70646230771200)), (nat_lit 2980, Int.ofNat (nat_lit 52545926361600)), (nat_lit 2981, Int.ofNat (nat_lit 79011669542400)), (nat_lit 2998, Int.ofNat (nat_lit 17545854735360))]
theorem block017_data_flat117_step : block017_data_flat117 = (CoefficientMerge.fastMerge block017_data_flat097 block017_data_flat116) := by decide +kernel
theorem block017_data_flat117_original : block017_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27731989051200 : Int) atom1256Coded) (CoefficientMerge.scale (27457319044800 : Int) atom1257Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42282031276800 : Int) atom1258Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47812699267200 : Int) atom1259Coded) (CoefficientMerge.scale (51497513812800 : Int) atom1260Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517790488000 : Int) atom1261Coded) (CoefficientMerge.scale (15983651980800 : Int) atom1262Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32380953292800 : Int) atom1263Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31420158336000 : Int) atom1264Coded) (CoefficientMerge.scale (51141665433600 : Int) atom1265Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58156348723200 : Int) atom1266Coded) (CoefficientMerge.scale (57274763212800 : Int) atom1267Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80303655398400 : Int) atom1268Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23458334054400 : Int) atom1269Coded) (CoefficientMerge.scale (44424079257600 : Int) atom1270Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68201800934400 : Int) atom1271Coded) (CoefficientMerge.scale (70646230771200 : Int) atom1272Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52545926361600 : Int) atom1273Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79011669542400 : Int) atom1274Coded) (CoefficientMerge.scale (17545854735360 : Int) atom1275Coded)))))) := by
  rw [block017_data_flat117_step, block017_data_flat097_original, block017_data_flat116_original]
def block017_data_flat118 : CoefficientMerge.Poly := [(nat_lit 2999, Int.ofNat (nat_lit 55664911411200))]
theorem block017_data_flat118_step : block017_data_flat118 = (CoefficientMerge.scale (55664911411200 : Int) atom1276Coded) := by decide +kernel
theorem block017_data_flat118_original : block017_data_flat118 = (CoefficientMerge.scale (55664911411200 : Int) atom1276Coded) := by
  rw [block017_data_flat118_step]
def block017_data_flat119 : CoefficientMerge.Poly := [(nat_lit 3000, Int.ofNat (nat_lit 60106665427200))]
theorem block017_data_flat119_step : block017_data_flat119 = (CoefficientMerge.scale (60106665427200 : Int) atom1277Coded) := by decide +kernel
theorem block017_data_flat119_original : block017_data_flat119 = (CoefficientMerge.scale (60106665427200 : Int) atom1277Coded) := by
  rw [block017_data_flat119_step]
def block017_data_flat120 : CoefficientMerge.Poly := [(nat_lit 2999, Int.ofNat (nat_lit 55664911411200)), (nat_lit 3000, Int.ofNat (nat_lit 60106665427200))]
theorem block017_data_flat120_step : block017_data_flat120 = (CoefficientMerge.fastMerge block017_data_flat118 block017_data_flat119) := by decide +kernel
theorem block017_data_flat120_original : block017_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (55664911411200 : Int) atom1276Coded) (CoefficientMerge.scale (60106665427200 : Int) atom1277Coded)) := by
  rw [block017_data_flat120_step, block017_data_flat118_original, block017_data_flat119_original]
def block017_data_flat121 : CoefficientMerge.Poly := [(nat_lit 3001, Int.ofNat (nat_lit 46866713241600))]
theorem block017_data_flat121_step : block017_data_flat121 = (CoefficientMerge.scale (46866713241600 : Int) atom1278Coded) := by decide +kernel
theorem block017_data_flat121_original : block017_data_flat121 = (CoefficientMerge.scale (46866713241600 : Int) atom1278Coded) := by
  rw [block017_data_flat121_step]
def block017_data_flat122 : CoefficientMerge.Poly := [(nat_lit 3002, Int.ofNat (nat_lit 57384114883200))]
theorem block017_data_flat122_step : block017_data_flat122 = (CoefficientMerge.scale (57384114883200 : Int) atom1279Coded) := by decide +kernel
theorem block017_data_flat122_original : block017_data_flat122 = (CoefficientMerge.scale (57384114883200 : Int) atom1279Coded) := by
  rw [block017_data_flat122_step]
def block017_data_flat123 : CoefficientMerge.Poly := [(nat_lit 3020, Int.ofNat (nat_lit 40457273472000))]
theorem block017_data_flat123_step : block017_data_flat123 = (CoefficientMerge.scale (40457273472000 : Int) atom1280Coded) := by decide +kernel
theorem block017_data_flat123_original : block017_data_flat123 = (CoefficientMerge.scale (40457273472000 : Int) atom1280Coded) := by
  rw [block017_data_flat123_step]
def block017_data_flat124 : CoefficientMerge.Poly := [(nat_lit 3002, Int.ofNat (nat_lit 57384114883200)), (nat_lit 3020, Int.ofNat (nat_lit 40457273472000))]
theorem block017_data_flat124_step : block017_data_flat124 = (CoefficientMerge.fastMerge block017_data_flat122 block017_data_flat123) := by decide +kernel
theorem block017_data_flat124_original : block017_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (57384114883200 : Int) atom1279Coded) (CoefficientMerge.scale (40457273472000 : Int) atom1280Coded)) := by
  rw [block017_data_flat124_step, block017_data_flat122_original, block017_data_flat123_original]
def block017_data_flat125 : CoefficientMerge.Poly := [(nat_lit 3001, Int.ofNat (nat_lit 46866713241600)), (nat_lit 3002, Int.ofNat (nat_lit 57384114883200)), (nat_lit 3020, Int.ofNat (nat_lit 40457273472000))]
theorem block017_data_flat125_step : block017_data_flat125 = (CoefficientMerge.fastMerge block017_data_flat121 block017_data_flat124) := by decide +kernel
theorem block017_data_flat125_original : block017_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (46866713241600 : Int) atom1278Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57384114883200 : Int) atom1279Coded) (CoefficientMerge.scale (40457273472000 : Int) atom1280Coded))) := by
  rw [block017_data_flat125_step, block017_data_flat121_original, block017_data_flat124_original]
def block017_data_flat126 : CoefficientMerge.Poly := [(nat_lit 2999, Int.ofNat (nat_lit 55664911411200)), (nat_lit 3000, Int.ofNat (nat_lit 60106665427200)), (nat_lit 3001, Int.ofNat (nat_lit 46866713241600)), (nat_lit 3002, Int.ofNat (nat_lit 57384114883200)), (nat_lit 3020, Int.ofNat (nat_lit 40457273472000))]
theorem block017_data_flat126_step : block017_data_flat126 = (CoefficientMerge.fastMerge block017_data_flat120 block017_data_flat125) := by decide +kernel
theorem block017_data_flat126_original : block017_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55664911411200 : Int) atom1276Coded) (CoefficientMerge.scale (60106665427200 : Int) atom1277Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46866713241600 : Int) atom1278Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57384114883200 : Int) atom1279Coded) (CoefficientMerge.scale (40457273472000 : Int) atom1280Coded)))) := by
  rw [block017_data_flat126_step, block017_data_flat120_original, block017_data_flat125_original]
def block017_data_flat127 : CoefficientMerge.Poly := [(nat_lit 3021, Int.ofNat (nat_lit 65177036467200))]
theorem block017_data_flat127_step : block017_data_flat127 = (CoefficientMerge.scale (65177036467200 : Int) atom1281Coded) := by decide +kernel
theorem block017_data_flat127_original : block017_data_flat127 = (CoefficientMerge.scale (65177036467200 : Int) atom1281Coded) := by
  rw [block017_data_flat127_step]
def block017_data_flat128 : CoefficientMerge.Poly := [(nat_lit 3022, Int.ofNat (nat_lit 46861654694400))]
theorem block017_data_flat128_step : block017_data_flat128 = (CoefficientMerge.scale (46861654694400 : Int) atom1282Coded) := by decide +kernel
theorem block017_data_flat128_original : block017_data_flat128 = (CoefficientMerge.scale (46861654694400 : Int) atom1282Coded) := by
  rw [block017_data_flat128_step]
def block017_data_flat129 : CoefficientMerge.Poly := [(nat_lit 3021, Int.ofNat (nat_lit 65177036467200)), (nat_lit 3022, Int.ofNat (nat_lit 46861654694400))]
theorem block017_data_flat129_step : block017_data_flat129 = (CoefficientMerge.fastMerge block017_data_flat127 block017_data_flat128) := by decide +kernel
theorem block017_data_flat129_original : block017_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (65177036467200 : Int) atom1281Coded) (CoefficientMerge.scale (46861654694400 : Int) atom1282Coded)) := by
  rw [block017_data_flat129_step, block017_data_flat127_original, block017_data_flat128_original]
def block017_data_flat130 : CoefficientMerge.Poly := [(nat_lit 3023, Int.ofNat (nat_lit 53756858937600))]
theorem block017_data_flat130_step : block017_data_flat130 = (CoefficientMerge.scale (53756858937600 : Int) atom1283Coded) := by decide +kernel
theorem block017_data_flat130_original : block017_data_flat130 = (CoefficientMerge.scale (53756858937600 : Int) atom1283Coded) := by
  rw [block017_data_flat130_step]
def block017_data_flat131 : CoefficientMerge.Poly := [(nat_lit 3042, Int.ofNat (nat_lit 18855796377600))]
theorem block017_data_flat131_step : block017_data_flat131 = (CoefficientMerge.scale (18855796377600 : Int) atom1284Coded) := by decide +kernel
theorem block017_data_flat131_original : block017_data_flat131 = (CoefficientMerge.scale (18855796377600 : Int) atom1284Coded) := by
  rw [block017_data_flat131_step]
def block017_data_flat132 : CoefficientMerge.Poly := [(nat_lit 3043, Int.ofNat (nat_lit 24005993760000))]
theorem block017_data_flat132_step : block017_data_flat132 = (CoefficientMerge.scale (24005993760000 : Int) atom1285Coded) := by decide +kernel
theorem block017_data_flat132_original : block017_data_flat132 = (CoefficientMerge.scale (24005993760000 : Int) atom1285Coded) := by
  rw [block017_data_flat132_step]
def block017_data_flat133 : CoefficientMerge.Poly := [(nat_lit 3042, Int.ofNat (nat_lit 18855796377600)), (nat_lit 3043, Int.ofNat (nat_lit 24005993760000))]
theorem block017_data_flat133_step : block017_data_flat133 = (CoefficientMerge.fastMerge block017_data_flat131 block017_data_flat132) := by decide +kernel
theorem block017_data_flat133_original : block017_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18855796377600 : Int) atom1284Coded) (CoefficientMerge.scale (24005993760000 : Int) atom1285Coded)) := by
  rw [block017_data_flat133_step, block017_data_flat131_original, block017_data_flat132_original]
def block017_data_flat134 : CoefficientMerge.Poly := [(nat_lit 3023, Int.ofNat (nat_lit 53756858937600)), (nat_lit 3042, Int.ofNat (nat_lit 18855796377600)), (nat_lit 3043, Int.ofNat (nat_lit 24005993760000))]
theorem block017_data_flat134_step : block017_data_flat134 = (CoefficientMerge.fastMerge block017_data_flat130 block017_data_flat133) := by decide +kernel
theorem block017_data_flat134_original : block017_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (53756858937600 : Int) atom1283Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18855796377600 : Int) atom1284Coded) (CoefficientMerge.scale (24005993760000 : Int) atom1285Coded))) := by
  rw [block017_data_flat134_step, block017_data_flat130_original, block017_data_flat133_original]
def block017_data_flat135 : CoefficientMerge.Poly := [(nat_lit 3021, Int.ofNat (nat_lit 65177036467200)), (nat_lit 3022, Int.ofNat (nat_lit 46861654694400)), (nat_lit 3023, Int.ofNat (nat_lit 53756858937600)), (nat_lit 3042, Int.ofNat (nat_lit 18855796377600)), (nat_lit 3043, Int.ofNat (nat_lit 24005993760000))]
theorem block017_data_flat135_step : block017_data_flat135 = (CoefficientMerge.fastMerge block017_data_flat129 block017_data_flat134) := by decide +kernel
theorem block017_data_flat135_original : block017_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65177036467200 : Int) atom1281Coded) (CoefficientMerge.scale (46861654694400 : Int) atom1282Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53756858937600 : Int) atom1283Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18855796377600 : Int) atom1284Coded) (CoefficientMerge.scale (24005993760000 : Int) atom1285Coded)))) := by
  rw [block017_data_flat135_step, block017_data_flat129_original, block017_data_flat134_original]
def block017_data_flat136 : CoefficientMerge.Poly := [(nat_lit 2999, Int.ofNat (nat_lit 55664911411200)), (nat_lit 3000, Int.ofNat (nat_lit 60106665427200)), (nat_lit 3001, Int.ofNat (nat_lit 46866713241600)), (nat_lit 3002, Int.ofNat (nat_lit 57384114883200)), (nat_lit 3020, Int.ofNat (nat_lit 40457273472000)), (nat_lit 3021, Int.ofNat (nat_lit 65177036467200)), (nat_lit 3022, Int.ofNat (nat_lit 46861654694400)), (nat_lit 3023, Int.ofNat (nat_lit 53756858937600)), (nat_lit 3042, Int.ofNat (nat_lit 18855796377600)), (nat_lit 3043, Int.ofNat (nat_lit 24005993760000))]
theorem block017_data_flat136_step : block017_data_flat136 = (CoefficientMerge.fastMerge block017_data_flat126 block017_data_flat135) := by decide +kernel
theorem block017_data_flat136_original : block017_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55664911411200 : Int) atom1276Coded) (CoefficientMerge.scale (60106665427200 : Int) atom1277Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46866713241600 : Int) atom1278Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57384114883200 : Int) atom1279Coded) (CoefficientMerge.scale (40457273472000 : Int) atom1280Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65177036467200 : Int) atom1281Coded) (CoefficientMerge.scale (46861654694400 : Int) atom1282Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53756858937600 : Int) atom1283Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18855796377600 : Int) atom1284Coded) (CoefficientMerge.scale (24005993760000 : Int) atom1285Coded))))) := by
  rw [block017_data_flat136_step, block017_data_flat126_original, block017_data_flat135_original]
def block017_data_flat137 : CoefficientMerge.Poly := [(nat_lit 3044, Int.ofNat (nat_lit 30962904739200))]
theorem block017_data_flat137_step : block017_data_flat137 = (CoefficientMerge.scale (30962904739200 : Int) atom1286Coded) := by decide +kernel
theorem block017_data_flat137_original : block017_data_flat137 = (CoefficientMerge.scale (30962904739200 : Int) atom1286Coded) := by
  rw [block017_data_flat137_step]
def block017_data_flat138 : CoefficientMerge.Poly := [(nat_lit 3241, Int.ofNat (nat_lit 2264279068800))]
theorem block017_data_flat138_step : block017_data_flat138 = (CoefficientMerge.scale (2264279068800 : Int) atom1287Coded) := by decide +kernel
theorem block017_data_flat138_original : block017_data_flat138 = (CoefficientMerge.scale (2264279068800 : Int) atom1287Coded) := by
  rw [block017_data_flat138_step]
def block017_data_flat139 : CoefficientMerge.Poly := [(nat_lit 3044, Int.ofNat (nat_lit 30962904739200)), (nat_lit 3241, Int.ofNat (nat_lit 2264279068800))]
theorem block017_data_flat139_step : block017_data_flat139 = (CoefficientMerge.fastMerge block017_data_flat137 block017_data_flat138) := by decide +kernel
theorem block017_data_flat139_original : block017_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30962904739200 : Int) atom1286Coded) (CoefficientMerge.scale (2264279068800 : Int) atom1287Coded)) := by
  rw [block017_data_flat139_step, block017_data_flat137_original, block017_data_flat138_original]
def block017_data_flat140 : CoefficientMerge.Poly := [(nat_lit 3242, Int.ofNat (nat_lit 3207232022400))]
theorem block017_data_flat140_step : block017_data_flat140 = (CoefficientMerge.scale (3207232022400 : Int) atom1288Coded) := by decide +kernel
theorem block017_data_flat140_original : block017_data_flat140 = (CoefficientMerge.scale (3207232022400 : Int) atom1288Coded) := by
  rw [block017_data_flat140_step]
def block017_data_flat141 : CoefficientMerge.Poly := [(nat_lit 3243, Int.ofNat (nat_lit 427179916800))]
theorem block017_data_flat141_step : block017_data_flat141 = (CoefficientMerge.scale (427179916800 : Int) atom1289Coded) := by decide +kernel
theorem block017_data_flat141_original : block017_data_flat141 = (CoefficientMerge.scale (427179916800 : Int) atom1289Coded) := by
  rw [block017_data_flat141_step]
def block017_data_flat142 : CoefficientMerge.Poly := [(nat_lit 3244, Int.ofNat (nat_lit 84082924800))]
theorem block017_data_flat142_step : block017_data_flat142 = (CoefficientMerge.scale (84082924800 : Int) atom1290Coded) := by decide +kernel
theorem block017_data_flat142_original : block017_data_flat142 = (CoefficientMerge.scale (84082924800 : Int) atom1290Coded) := by
  rw [block017_data_flat142_step]
def block017_data_flat143 : CoefficientMerge.Poly := [(nat_lit 3243, Int.ofNat (nat_lit 427179916800)), (nat_lit 3244, Int.ofNat (nat_lit 84082924800))]
theorem block017_data_flat143_step : block017_data_flat143 = (CoefficientMerge.fastMerge block017_data_flat141 block017_data_flat142) := by decide +kernel
theorem block017_data_flat143_original : block017_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1289Coded) (CoefficientMerge.scale (84082924800 : Int) atom1290Coded)) := by
  rw [block017_data_flat143_step, block017_data_flat141_original, block017_data_flat142_original]
def block017_data_flat144 : CoefficientMerge.Poly := [(nat_lit 3242, Int.ofNat (nat_lit 3207232022400)), (nat_lit 3243, Int.ofNat (nat_lit 427179916800)), (nat_lit 3244, Int.ofNat (nat_lit 84082924800))]
theorem block017_data_flat144_step : block017_data_flat144 = (CoefficientMerge.fastMerge block017_data_flat140 block017_data_flat143) := by decide +kernel
theorem block017_data_flat144_original : block017_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3207232022400 : Int) atom1288Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1289Coded) (CoefficientMerge.scale (84082924800 : Int) atom1290Coded))) := by
  rw [block017_data_flat144_step, block017_data_flat140_original, block017_data_flat143_original]
def block017_data_flat145 : CoefficientMerge.Poly := [(nat_lit 3044, Int.ofNat (nat_lit 30962904739200)), (nat_lit 3241, Int.ofNat (nat_lit 2264279068800)), (nat_lit 3242, Int.ofNat (nat_lit 3207232022400)), (nat_lit 3243, Int.ofNat (nat_lit 427179916800)), (nat_lit 3244, Int.ofNat (nat_lit 84082924800))]
theorem block017_data_flat145_step : block017_data_flat145 = (CoefficientMerge.fastMerge block017_data_flat139 block017_data_flat144) := by decide +kernel
theorem block017_data_flat145_original : block017_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30962904739200 : Int) atom1286Coded) (CoefficientMerge.scale (2264279068800 : Int) atom1287Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3207232022400 : Int) atom1288Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1289Coded) (CoefficientMerge.scale (84082924800 : Int) atom1290Coded)))) := by
  rw [block017_data_flat145_step, block017_data_flat139_original, block017_data_flat144_original]
def block017_data_flat146 : CoefficientMerge.Poly := [(nat_lit 3249, Int.ofNat (nat_lit 3734859508992))]
theorem block017_data_flat146_step : block017_data_flat146 = (CoefficientMerge.scale (3734859508992 : Int) atom1291Coded) := by decide +kernel
theorem block017_data_flat146_original : block017_data_flat146 = (CoefficientMerge.scale (3734859508992 : Int) atom1291Coded) := by
  rw [block017_data_flat146_step]
def block017_data_flat147 : CoefficientMerge.Poly := [(nat_lit 3263, Int.ofNat (nat_lit 2780052105600))]
theorem block017_data_flat147_step : block017_data_flat147 = (CoefficientMerge.scale (2780052105600 : Int) atom1292Coded) := by decide +kernel
theorem block017_data_flat147_original : block017_data_flat147 = (CoefficientMerge.scale (2780052105600 : Int) atom1292Coded) := by
  rw [block017_data_flat147_step]
def block017_data_flat148 : CoefficientMerge.Poly := [(nat_lit 3249, Int.ofNat (nat_lit 3734859508992)), (nat_lit 3263, Int.ofNat (nat_lit 2780052105600))]
theorem block017_data_flat148_step : block017_data_flat148 = (CoefficientMerge.fastMerge block017_data_flat146 block017_data_flat147) := by decide +kernel
theorem block017_data_flat148_original : block017_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3734859508992 : Int) atom1291Coded) (CoefficientMerge.scale (2780052105600 : Int) atom1292Coded)) := by
  rw [block017_data_flat148_step, block017_data_flat146_original, block017_data_flat147_original]
def block017_data_flat149 : CoefficientMerge.Poly := [(nat_lit 3264, Int.ofNat (nat_lit 518028134400))]
theorem block017_data_flat149_step : block017_data_flat149 = (CoefficientMerge.scale (518028134400 : Int) atom1293Coded) := by decide +kernel
theorem block017_data_flat149_original : block017_data_flat149 = (CoefficientMerge.scale (518028134400 : Int) atom1293Coded) := by
  rw [block017_data_flat149_step]
def block017_data_flat150 : CoefficientMerge.Poly := [(nat_lit 3268, Int.ofNat (nat_lit 427179916800))]
theorem block017_data_flat150_step : block017_data_flat150 = (CoefficientMerge.scale (427179916800 : Int) atom1294Coded) := by decide +kernel
theorem block017_data_flat150_original : block017_data_flat150 = (CoefficientMerge.scale (427179916800 : Int) atom1294Coded) := by
  rw [block017_data_flat150_step]
def block017_data_flat151 : CoefficientMerge.Poly := [(nat_lit 3269, Int.ofNat (nat_lit 854359833600))]
theorem block017_data_flat151_step : block017_data_flat151 = (CoefficientMerge.scale (854359833600 : Int) atom1295Coded) := by decide +kernel
theorem block017_data_flat151_original : block017_data_flat151 = (CoefficientMerge.scale (854359833600 : Int) atom1295Coded) := by
  rw [block017_data_flat151_step]
def block017_data_flat152 : CoefficientMerge.Poly := [(nat_lit 3268, Int.ofNat (nat_lit 427179916800)), (nat_lit 3269, Int.ofNat (nat_lit 854359833600))]
theorem block017_data_flat152_step : block017_data_flat152 = (CoefficientMerge.fastMerge block017_data_flat150 block017_data_flat151) := by decide +kernel
theorem block017_data_flat152_original : block017_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1294Coded) (CoefficientMerge.scale (854359833600 : Int) atom1295Coded)) := by
  rw [block017_data_flat152_step, block017_data_flat150_original, block017_data_flat151_original]
def block017_data_flat153 : CoefficientMerge.Poly := [(nat_lit 3264, Int.ofNat (nat_lit 518028134400)), (nat_lit 3268, Int.ofNat (nat_lit 427179916800)), (nat_lit 3269, Int.ofNat (nat_lit 854359833600))]
theorem block017_data_flat153_step : block017_data_flat153 = (CoefficientMerge.fastMerge block017_data_flat149 block017_data_flat152) := by decide +kernel
theorem block017_data_flat153_original : block017_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (518028134400 : Int) atom1293Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1294Coded) (CoefficientMerge.scale (854359833600 : Int) atom1295Coded))) := by
  rw [block017_data_flat153_step, block017_data_flat149_original, block017_data_flat152_original]
def block017_data_flat154 : CoefficientMerge.Poly := [(nat_lit 3249, Int.ofNat (nat_lit 3734859508992)), (nat_lit 3263, Int.ofNat (nat_lit 2780052105600)), (nat_lit 3264, Int.ofNat (nat_lit 518028134400)), (nat_lit 3268, Int.ofNat (nat_lit 427179916800)), (nat_lit 3269, Int.ofNat (nat_lit 854359833600))]
theorem block017_data_flat154_step : block017_data_flat154 = (CoefficientMerge.fastMerge block017_data_flat148 block017_data_flat153) := by decide +kernel
theorem block017_data_flat154_original : block017_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3734859508992 : Int) atom1291Coded) (CoefficientMerge.scale (2780052105600 : Int) atom1292Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (518028134400 : Int) atom1293Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1294Coded) (CoefficientMerge.scale (854359833600 : Int) atom1295Coded)))) := by
  rw [block017_data_flat154_step, block017_data_flat148_original, block017_data_flat153_original]
def block017_data_flat155 : CoefficientMerge.Poly := [(nat_lit 3044, Int.ofNat (nat_lit 30962904739200)), (nat_lit 3241, Int.ofNat (nat_lit 2264279068800)), (nat_lit 3242, Int.ofNat (nat_lit 3207232022400)), (nat_lit 3243, Int.ofNat (nat_lit 427179916800)), (nat_lit 3244, Int.ofNat (nat_lit 84082924800)), (nat_lit 3249, Int.ofNat (nat_lit 3734859508992)), (nat_lit 3263, Int.ofNat (nat_lit 2780052105600)), (nat_lit 3264, Int.ofNat (nat_lit 518028134400)), (nat_lit 3268, Int.ofNat (nat_lit 427179916800)), (nat_lit 3269, Int.ofNat (nat_lit 854359833600))]
theorem block017_data_flat155_step : block017_data_flat155 = (CoefficientMerge.fastMerge block017_data_flat145 block017_data_flat154) := by decide +kernel
theorem block017_data_flat155_original : block017_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30962904739200 : Int) atom1286Coded) (CoefficientMerge.scale (2264279068800 : Int) atom1287Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3207232022400 : Int) atom1288Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1289Coded) (CoefficientMerge.scale (84082924800 : Int) atom1290Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3734859508992 : Int) atom1291Coded) (CoefficientMerge.scale (2780052105600 : Int) atom1292Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (518028134400 : Int) atom1293Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1294Coded) (CoefficientMerge.scale (854359833600 : Int) atom1295Coded))))) := by
  rw [block017_data_flat155_step, block017_data_flat145_original, block017_data_flat154_original]
def block017_data_flat156 : CoefficientMerge.Poly := [(nat_lit 2999, Int.ofNat (nat_lit 55664911411200)), (nat_lit 3000, Int.ofNat (nat_lit 60106665427200)), (nat_lit 3001, Int.ofNat (nat_lit 46866713241600)), (nat_lit 3002, Int.ofNat (nat_lit 57384114883200)), (nat_lit 3020, Int.ofNat (nat_lit 40457273472000)), (nat_lit 3021, Int.ofNat (nat_lit 65177036467200)), (nat_lit 3022, Int.ofNat (nat_lit 46861654694400)), (nat_lit 3023, Int.ofNat (nat_lit 53756858937600)), (nat_lit 3042, Int.ofNat (nat_lit 18855796377600)), (nat_lit 3043, Int.ofNat (nat_lit 24005993760000)), (nat_lit 3044, Int.ofNat (nat_lit 30962904739200)), (nat_lit 3241, Int.ofNat (nat_lit 2264279068800)), (nat_lit 3242, Int.ofNat (nat_lit 3207232022400)), (nat_lit 3243, Int.ofNat (nat_lit 427179916800)), (nat_lit 3244, Int.ofNat (nat_lit 84082924800)), (nat_lit 3249, Int.ofNat (nat_lit 3734859508992)), (nat_lit 3263, Int.ofNat (nat_lit 2780052105600)), (nat_lit 3264, Int.ofNat (nat_lit 518028134400)), (nat_lit 3268, Int.ofNat (nat_lit 427179916800)), (nat_lit 3269, Int.ofNat (nat_lit 854359833600))]
theorem block017_data_flat156_step : block017_data_flat156 = (CoefficientMerge.fastMerge block017_data_flat136 block017_data_flat155) := by decide +kernel
theorem block017_data_flat156_original : block017_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55664911411200 : Int) atom1276Coded) (CoefficientMerge.scale (60106665427200 : Int) atom1277Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46866713241600 : Int) atom1278Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57384114883200 : Int) atom1279Coded) (CoefficientMerge.scale (40457273472000 : Int) atom1280Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65177036467200 : Int) atom1281Coded) (CoefficientMerge.scale (46861654694400 : Int) atom1282Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53756858937600 : Int) atom1283Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18855796377600 : Int) atom1284Coded) (CoefficientMerge.scale (24005993760000 : Int) atom1285Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30962904739200 : Int) atom1286Coded) (CoefficientMerge.scale (2264279068800 : Int) atom1287Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3207232022400 : Int) atom1288Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1289Coded) (CoefficientMerge.scale (84082924800 : Int) atom1290Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3734859508992 : Int) atom1291Coded) (CoefficientMerge.scale (2780052105600 : Int) atom1292Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (518028134400 : Int) atom1293Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1294Coded) (CoefficientMerge.scale (854359833600 : Int) atom1295Coded)))))) := by
  rw [block017_data_flat156_step, block017_data_flat136_original, block017_data_flat155_original]
def block017_data_flat157 : CoefficientMerge.Poly := [(nat_lit 2934, Int.ofNat (nat_lit 27731989051200)), (nat_lit 2935, Int.ofNat (nat_lit 27457319044800)), (nat_lit 2936, Int.ofNat (nat_lit 42282031276800)), (nat_lit 2937, Int.ofNat (nat_lit 47812699267200)), (nat_lit 2938, Int.ofNat (nat_lit 51497513812800)), (nat_lit 2939, Int.ofNat (nat_lit 68517790488000)), (nat_lit 2954, Int.ofNat (nat_lit 15983651980800)), (nat_lit 2955, Int.ofNat (nat_lit 32380953292800)), (nat_lit 2956, Int.ofNat (nat_lit 31420158336000)), (nat_lit 2957, Int.ofNat (nat_lit 51141665433600)), (nat_lit 2958, Int.ofNat (nat_lit 58156348723200)), (nat_lit 2959, Int.ofNat (nat_lit 57274763212800)), (nat_lit 2960, Int.ofNat (nat_lit 80303655398400)), (nat_lit 2976, Int.ofNat (nat_lit 23458334054400)), (nat_lit 2977, Int.ofNat (nat_lit 44424079257600)), (nat_lit 2978, Int.ofNat (nat_lit 68201800934400)), (nat_lit 2979, Int.ofNat (nat_lit 70646230771200)), (nat_lit 2980, Int.ofNat (nat_lit 52545926361600)), (nat_lit 2981, Int.ofNat (nat_lit 79011669542400)), (nat_lit 2998, Int.ofNat (nat_lit 17545854735360)), (nat_lit 2999, Int.ofNat (nat_lit 55664911411200)), (nat_lit 3000, Int.ofNat (nat_lit 60106665427200)), (nat_lit 3001, Int.ofNat (nat_lit 46866713241600)), (nat_lit 3002, Int.ofNat (nat_lit 57384114883200)), (nat_lit 3020, Int.ofNat (nat_lit 40457273472000)), (nat_lit 3021, Int.ofNat (nat_lit 65177036467200)), (nat_lit 3022, Int.ofNat (nat_lit 46861654694400)), (nat_lit 3023, Int.ofNat (nat_lit 53756858937600)), (nat_lit 3042, Int.ofNat (nat_lit 18855796377600)), (nat_lit 3043, Int.ofNat (nat_lit 24005993760000)), (nat_lit 3044, Int.ofNat (nat_lit 30962904739200)), (nat_lit 3241, Int.ofNat (nat_lit 2264279068800)), (nat_lit 3242, Int.ofNat (nat_lit 3207232022400)), (nat_lit 3243, Int.ofNat (nat_lit 427179916800)), (nat_lit 3244, Int.ofNat (nat_lit 84082924800)), (nat_lit 3249, Int.ofNat (nat_lit 3734859508992)), (nat_lit 3263, Int.ofNat (nat_lit 2780052105600)), (nat_lit 3264, Int.ofNat (nat_lit 518028134400)), (nat_lit 3268, Int.ofNat (nat_lit 427179916800)), (nat_lit 3269, Int.ofNat (nat_lit 854359833600))]
theorem block017_data_flat157_step : block017_data_flat157 = (CoefficientMerge.fastMerge block017_data_flat117 block017_data_flat156) := by decide +kernel
theorem block017_data_flat157_original : block017_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27731989051200 : Int) atom1256Coded) (CoefficientMerge.scale (27457319044800 : Int) atom1257Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42282031276800 : Int) atom1258Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47812699267200 : Int) atom1259Coded) (CoefficientMerge.scale (51497513812800 : Int) atom1260Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517790488000 : Int) atom1261Coded) (CoefficientMerge.scale (15983651980800 : Int) atom1262Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32380953292800 : Int) atom1263Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31420158336000 : Int) atom1264Coded) (CoefficientMerge.scale (51141665433600 : Int) atom1265Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58156348723200 : Int) atom1266Coded) (CoefficientMerge.scale (57274763212800 : Int) atom1267Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80303655398400 : Int) atom1268Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23458334054400 : Int) atom1269Coded) (CoefficientMerge.scale (44424079257600 : Int) atom1270Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68201800934400 : Int) atom1271Coded) (CoefficientMerge.scale (70646230771200 : Int) atom1272Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52545926361600 : Int) atom1273Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79011669542400 : Int) atom1274Coded) (CoefficientMerge.scale (17545854735360 : Int) atom1275Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55664911411200 : Int) atom1276Coded) (CoefficientMerge.scale (60106665427200 : Int) atom1277Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46866713241600 : Int) atom1278Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57384114883200 : Int) atom1279Coded) (CoefficientMerge.scale (40457273472000 : Int) atom1280Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65177036467200 : Int) atom1281Coded) (CoefficientMerge.scale (46861654694400 : Int) atom1282Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53756858937600 : Int) atom1283Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18855796377600 : Int) atom1284Coded) (CoefficientMerge.scale (24005993760000 : Int) atom1285Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30962904739200 : Int) atom1286Coded) (CoefficientMerge.scale (2264279068800 : Int) atom1287Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3207232022400 : Int) atom1288Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1289Coded) (CoefficientMerge.scale (84082924800 : Int) atom1290Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3734859508992 : Int) atom1291Coded) (CoefficientMerge.scale (2780052105600 : Int) atom1292Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (518028134400 : Int) atom1293Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1294Coded) (CoefficientMerge.scale (854359833600 : Int) atom1295Coded))))))) := by
  rw [block017_data_flat157_step, block017_data_flat117_original, block017_data_flat156_original]
def block017_data_flat158 : CoefficientMerge.Poly := [(nat_lit 2848, Int.ofNat (nat_lit 2066320569600)), (nat_lit 2849, Int.ofNat (nat_lit 2843362771200)), (nat_lit 2850, Int.ofNat (nat_lit 12526751865600)), (nat_lit 2851, Int.ofNat (nat_lit 9755314884000)), (nat_lit 2852, Int.ofNat (nat_lit 17449540819200)), (nat_lit 2853, Int.ofNat (nat_lit 24820650338400)), (nat_lit 2854, Int.ofNat (nat_lit 35164296367200)), (nat_lit 2855, Int.ofNat (nat_lit 45787493959200)), (nat_lit 2866, Int.ofNat (nat_lit 3204336038400)), (nat_lit 2867, Int.ofNat (nat_lit 5399676979200)), (nat_lit 2868, Int.ofNat (nat_lit 5672221632000)), (nat_lit 2869, Int.ofNat (nat_lit 6371946201600)), (nat_lit 2870, Int.ofNat (nat_lit 7071670771200)), (nat_lit 2871, Int.ofNat (nat_lit 17374084156800)), (nat_lit 2872, Int.ofNat (nat_lit 15150394274400)), (nat_lit 2873, Int.ofNat (nat_lit 25703681270400)), (nat_lit 2874, Int.ofNat (nat_lit 31388299941600)), (nat_lit 2875, Int.ofNat (nat_lit 42276310423200)), (nat_lit 2876, Int.ofNat (nat_lit 53312311684800)), (nat_lit 2888, Int.ofNat (nat_lit 5780946124800)), (nat_lit 2889, Int.ofNat (nat_lit 10139247820800)), (nat_lit 2890, Int.ofNat (nat_lit 10593488908800)), (nat_lit 2891, Int.ofNat (nat_lit 11047729996800)), (nat_lit 2892, Int.ofNat (nat_lit 21624024038400)), (nat_lit 2893, Int.ofNat (nat_lit 19839379392000)), (nat_lit 2894, Int.ofNat (nat_lit 33307519795200)), (nat_lit 2895, Int.ofNat (nat_lit 36744632870400)), (nat_lit 2896, Int.ofNat (nat_lit 47909475532800)), (nat_lit 2897, Int.ofNat (nat_lit 59097361881600)), (nat_lit 2910, Int.ofNat (nat_lit 8371086796800)), (nat_lit 2911, Int.ofNat (nat_lit 16355585433600)), (nat_lit 2912, Int.ofNat (nat_lit 16396177190400)), (nat_lit 2913, Int.ofNat (nat_lit 22971182707200)), (nat_lit 2914, Int.ofNat (nat_lit 23375330316800)), (nat_lit 2915, Int.ofNat (nat_lit 35615926976000)), (nat_lit 2916, Int.ofNat (nat_lit 39881932652800)), (nat_lit 2917, Int.ofNat (nat_lit 50170991001600)), (nat_lit 2918, Int.ofNat (nat_lit 61314928214400)), (nat_lit 2932, Int.ofNat (nat_lit 11705777856000)), (nat_lit 2933, Int.ofNat (nat_lit 21699798566400)), (nat_lit 2934, Int.ofNat (nat_lit 27731989051200)), (nat_lit 2935, Int.ofNat (nat_lit 27457319044800)), (nat_lit 2936, Int.ofNat (nat_lit 42282031276800)), (nat_lit 2937, Int.ofNat (nat_lit 47812699267200)), (nat_lit 2938, Int.ofNat (nat_lit 51497513812800)), (nat_lit 2939, Int.ofNat (nat_lit 68517790488000)), (nat_lit 2954, Int.ofNat (nat_lit 15983651980800)), (nat_lit 2955, Int.ofNat (nat_lit 32380953292800)), (nat_lit 2956, Int.ofNat (nat_lit 31420158336000)), (nat_lit 2957, Int.ofNat (nat_lit 51141665433600)), (nat_lit 2958, Int.ofNat (nat_lit 58156348723200)), (nat_lit 2959, Int.ofNat (nat_lit 57274763212800)), (nat_lit 2960, Int.ofNat (nat_lit 80303655398400)), (nat_lit 2976, Int.ofNat (nat_lit 23458334054400)), (nat_lit 2977, Int.ofNat (nat_lit 44424079257600)), (nat_lit 2978, Int.ofNat (nat_lit 68201800934400)), (nat_lit 2979, Int.ofNat (nat_lit 70646230771200)), (nat_lit 2980, Int.ofNat (nat_lit 52545926361600)), (nat_lit 2981, Int.ofNat (nat_lit 79011669542400)), (nat_lit 2998, Int.ofNat (nat_lit 17545854735360)), (nat_lit 2999, Int.ofNat (nat_lit 55664911411200)), (nat_lit 3000, Int.ofNat (nat_lit 60106665427200)), (nat_lit 3001, Int.ofNat (nat_lit 46866713241600)), (nat_lit 3002, Int.ofNat (nat_lit 57384114883200)), (nat_lit 3020, Int.ofNat (nat_lit 40457273472000)), (nat_lit 3021, Int.ofNat (nat_lit 65177036467200)), (nat_lit 3022, Int.ofNat (nat_lit 46861654694400)), (nat_lit 3023, Int.ofNat (nat_lit 53756858937600)), (nat_lit 3042, Int.ofNat (nat_lit 18855796377600)), (nat_lit 3043, Int.ofNat (nat_lit 24005993760000)), (nat_lit 3044, Int.ofNat (nat_lit 30962904739200)), (nat_lit 3241, Int.ofNat (nat_lit 2264279068800)), (nat_lit 3242, Int.ofNat (nat_lit 3207232022400)), (nat_lit 3243, Int.ofNat (nat_lit 427179916800)), (nat_lit 3244, Int.ofNat (nat_lit 84082924800)), (nat_lit 3249, Int.ofNat (nat_lit 3734859508992)), (nat_lit 3263, Int.ofNat (nat_lit 2780052105600)), (nat_lit 3264, Int.ofNat (nat_lit 518028134400)), (nat_lit 3268, Int.ofNat (nat_lit 427179916800)), (nat_lit 3269, Int.ofNat (nat_lit 854359833600))]
theorem block017_data_flat158_step : block017_data_flat158 = (CoefficientMerge.fastMerge block017_data_flat078 block017_data_flat157) := by decide +kernel
theorem block017_data_flat158_original : block017_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2066320569600 : Int) atom1216Coded) (CoefficientMerge.scale (2843362771200 : Int) atom1217Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12526751865600 : Int) atom1218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9755314884000 : Int) atom1219Coded) (CoefficientMerge.scale (17449540819200 : Int) atom1220Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24820650338400 : Int) atom1221Coded) (CoefficientMerge.scale (35164296367200 : Int) atom1222Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45787493959200 : Int) atom1223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3204336038400 : Int) atom1224Coded) (CoefficientMerge.scale (5399676979200 : Int) atom1225Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5672221632000 : Int) atom1226Coded) (CoefficientMerge.scale (6371946201600 : Int) atom1227Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7071670771200 : Int) atom1228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17374084156800 : Int) atom1229Coded) (CoefficientMerge.scale (15150394274400 : Int) atom1230Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25703681270400 : Int) atom1231Coded) (CoefficientMerge.scale (31388299941600 : Int) atom1232Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42276310423200 : Int) atom1233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53312311684800 : Int) atom1234Coded) (CoefficientMerge.scale (5780946124800 : Int) atom1235Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10139247820800 : Int) atom1236Coded) (CoefficientMerge.scale (10593488908800 : Int) atom1237Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11047729996800 : Int) atom1238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21624024038400 : Int) atom1239Coded) (CoefficientMerge.scale (19839379392000 : Int) atom1240Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33307519795200 : Int) atom1241Coded) (CoefficientMerge.scale (36744632870400 : Int) atom1242Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47909475532800 : Int) atom1243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59097361881600 : Int) atom1244Coded) (CoefficientMerge.scale (8371086796800 : Int) atom1245Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16355585433600 : Int) atom1246Coded) (CoefficientMerge.scale (16396177190400 : Int) atom1247Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22971182707200 : Int) atom1248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23375330316800 : Int) atom1249Coded) (CoefficientMerge.scale (35615926976000 : Int) atom1250Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39881932652800 : Int) atom1251Coded) (CoefficientMerge.scale (50170991001600 : Int) atom1252Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61314928214400 : Int) atom1253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11705777856000 : Int) atom1254Coded) (CoefficientMerge.scale (21699798566400 : Int) atom1255Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27731989051200 : Int) atom1256Coded) (CoefficientMerge.scale (27457319044800 : Int) atom1257Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42282031276800 : Int) atom1258Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47812699267200 : Int) atom1259Coded) (CoefficientMerge.scale (51497513812800 : Int) atom1260Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517790488000 : Int) atom1261Coded) (CoefficientMerge.scale (15983651980800 : Int) atom1262Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32380953292800 : Int) atom1263Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31420158336000 : Int) atom1264Coded) (CoefficientMerge.scale (51141665433600 : Int) atom1265Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58156348723200 : Int) atom1266Coded) (CoefficientMerge.scale (57274763212800 : Int) atom1267Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80303655398400 : Int) atom1268Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23458334054400 : Int) atom1269Coded) (CoefficientMerge.scale (44424079257600 : Int) atom1270Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68201800934400 : Int) atom1271Coded) (CoefficientMerge.scale (70646230771200 : Int) atom1272Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52545926361600 : Int) atom1273Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79011669542400 : Int) atom1274Coded) (CoefficientMerge.scale (17545854735360 : Int) atom1275Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55664911411200 : Int) atom1276Coded) (CoefficientMerge.scale (60106665427200 : Int) atom1277Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46866713241600 : Int) atom1278Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57384114883200 : Int) atom1279Coded) (CoefficientMerge.scale (40457273472000 : Int) atom1280Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65177036467200 : Int) atom1281Coded) (CoefficientMerge.scale (46861654694400 : Int) atom1282Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53756858937600 : Int) atom1283Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18855796377600 : Int) atom1284Coded) (CoefficientMerge.scale (24005993760000 : Int) atom1285Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30962904739200 : Int) atom1286Coded) (CoefficientMerge.scale (2264279068800 : Int) atom1287Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3207232022400 : Int) atom1288Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1289Coded) (CoefficientMerge.scale (84082924800 : Int) atom1290Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3734859508992 : Int) atom1291Coded) (CoefficientMerge.scale (2780052105600 : Int) atom1292Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (518028134400 : Int) atom1293Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1294Coded) (CoefficientMerge.scale (854359833600 : Int) atom1295Coded)))))))) := by
  rw [block017_data_flat158_step, block017_data_flat078_original, block017_data_flat157_original]
def block017_data_flat159 : CoefficientMerge.Poly := [(nat_lit 2848, Int.ofNat (nat_lit 2066320569600)), (nat_lit 2849, Int.ofNat (nat_lit 2843362771200)), (nat_lit 2850, Int.ofNat (nat_lit 12526751865600)), (nat_lit 2851, Int.ofNat (nat_lit 9755314884000)), (nat_lit 2852, Int.ofNat (nat_lit 17449540819200)), (nat_lit 2853, Int.ofNat (nat_lit 24820650338400)), (nat_lit 2854, Int.ofNat (nat_lit 35164296367200)), (nat_lit 2855, Int.ofNat (nat_lit 45787493959200)), (nat_lit 2866, Int.ofNat (nat_lit 3204336038400)), (nat_lit 2867, Int.ofNat (nat_lit 5399676979200)), (nat_lit 2868, Int.ofNat (nat_lit 5672221632000)), (nat_lit 2869, Int.ofNat (nat_lit 6371946201600)), (nat_lit 2870, Int.ofNat (nat_lit 7071670771200)), (nat_lit 2871, Int.ofNat (nat_lit 17374084156800)), (nat_lit 2872, Int.ofNat (nat_lit 15150394274400)), (nat_lit 2873, Int.ofNat (nat_lit 25703681270400)), (nat_lit 2874, Int.ofNat (nat_lit 31388299941600)), (nat_lit 2875, Int.ofNat (nat_lit 42276310423200)), (nat_lit 2876, Int.ofNat (nat_lit 53312311684800)), (nat_lit 2888, Int.ofNat (nat_lit 5780946124800)), (nat_lit 2889, Int.ofNat (nat_lit 10139247820800)), (nat_lit 2890, Int.ofNat (nat_lit 10593488908800)), (nat_lit 2891, Int.ofNat (nat_lit 11047729996800)), (nat_lit 2892, Int.ofNat (nat_lit 21624024038400)), (nat_lit 2893, Int.ofNat (nat_lit 19839379392000)), (nat_lit 2894, Int.ofNat (nat_lit 33307519795200)), (nat_lit 2895, Int.ofNat (nat_lit 36744632870400)), (nat_lit 2896, Int.ofNat (nat_lit 47909475532800)), (nat_lit 2897, Int.ofNat (nat_lit 59097361881600)), (nat_lit 2910, Int.ofNat (nat_lit 8371086796800)), (nat_lit 2911, Int.ofNat (nat_lit 16355585433600)), (nat_lit 2912, Int.ofNat (nat_lit 16396177190400)), (nat_lit 2913, Int.ofNat (nat_lit 22971182707200)), (nat_lit 2914, Int.ofNat (nat_lit 23375330316800)), (nat_lit 2915, Int.ofNat (nat_lit 35615926976000)), (nat_lit 2916, Int.ofNat (nat_lit 39881932652800)), (nat_lit 2917, Int.ofNat (nat_lit 50170991001600)), (nat_lit 2918, Int.ofNat (nat_lit 61314928214400)), (nat_lit 2932, Int.ofNat (nat_lit 11705777856000)), (nat_lit 2933, Int.ofNat (nat_lit 21699798566400)), (nat_lit 2934, Int.ofNat (nat_lit 27731989051200)), (nat_lit 2935, Int.ofNat (nat_lit 27457319044800)), (nat_lit 2936, Int.ofNat (nat_lit 42282031276800)), (nat_lit 2937, Int.ofNat (nat_lit 47812699267200)), (nat_lit 2938, Int.ofNat (nat_lit 51497513812800)), (nat_lit 2939, Int.ofNat (nat_lit 68517790488000)), (nat_lit 2954, Int.ofNat (nat_lit 15983651980800)), (nat_lit 2955, Int.ofNat (nat_lit 32380953292800)), (nat_lit 2956, Int.ofNat (nat_lit 31420158336000)), (nat_lit 2957, Int.ofNat (nat_lit 51141665433600)), (nat_lit 2958, Int.ofNat (nat_lit 58156348723200)), (nat_lit 2959, Int.ofNat (nat_lit 57274763212800)), (nat_lit 2960, Int.ofNat (nat_lit 80303655398400)), (nat_lit 2976, Int.ofNat (nat_lit 23458334054400)), (nat_lit 2977, Int.ofNat (nat_lit 44424079257600)), (nat_lit 2978, Int.ofNat (nat_lit 68201800934400)), (nat_lit 2979, Int.ofNat (nat_lit 70646230771200)), (nat_lit 2980, Int.ofNat (nat_lit 52545926361600)), (nat_lit 2981, Int.ofNat (nat_lit 79011669542400)), (nat_lit 2998, Int.ofNat (nat_lit 17545854735360)), (nat_lit 2999, Int.ofNat (nat_lit 55664911411200)), (nat_lit 3000, Int.ofNat (nat_lit 60106665427200)), (nat_lit 3001, Int.ofNat (nat_lit 46866713241600)), (nat_lit 3002, Int.ofNat (nat_lit 57384114883200)), (nat_lit 3020, Int.ofNat (nat_lit 40457273472000)), (nat_lit 3021, Int.ofNat (nat_lit 65177036467200)), (nat_lit 3022, Int.ofNat (nat_lit 46861654694400)), (nat_lit 3023, Int.ofNat (nat_lit 53756858937600)), (nat_lit 3042, Int.ofNat (nat_lit 18855796377600)), (nat_lit 3043, Int.ofNat (nat_lit 24005993760000)), (nat_lit 3044, Int.ofNat (nat_lit 30962904739200)), (nat_lit 3241, Int.ofNat (nat_lit 2264279068800)), (nat_lit 3242, Int.ofNat (nat_lit 3207232022400)), (nat_lit 3243, Int.ofNat (nat_lit 427179916800)), (nat_lit 3244, Int.ofNat (nat_lit 84082924800)), (nat_lit 3249, Int.ofNat (nat_lit 3734859508992)), (nat_lit 3263, Int.ofNat (nat_lit 2780052105600)), (nat_lit 3264, Int.ofNat (nat_lit 518028134400)), (nat_lit 3268, Int.ofNat (nat_lit 427179916800)), (nat_lit 3269, Int.ofNat (nat_lit 854359833600))]
theorem block017_data_flat159_step : block017_data_flat159 = (CoefficientMerge.trim block017_data_flat158) := by decide +kernel
theorem block017_data_flat159_original : block017_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2066320569600 : Int) atom1216Coded) (CoefficientMerge.scale (2843362771200 : Int) atom1217Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12526751865600 : Int) atom1218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9755314884000 : Int) atom1219Coded) (CoefficientMerge.scale (17449540819200 : Int) atom1220Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24820650338400 : Int) atom1221Coded) (CoefficientMerge.scale (35164296367200 : Int) atom1222Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45787493959200 : Int) atom1223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3204336038400 : Int) atom1224Coded) (CoefficientMerge.scale (5399676979200 : Int) atom1225Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5672221632000 : Int) atom1226Coded) (CoefficientMerge.scale (6371946201600 : Int) atom1227Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7071670771200 : Int) atom1228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17374084156800 : Int) atom1229Coded) (CoefficientMerge.scale (15150394274400 : Int) atom1230Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25703681270400 : Int) atom1231Coded) (CoefficientMerge.scale (31388299941600 : Int) atom1232Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42276310423200 : Int) atom1233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53312311684800 : Int) atom1234Coded) (CoefficientMerge.scale (5780946124800 : Int) atom1235Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10139247820800 : Int) atom1236Coded) (CoefficientMerge.scale (10593488908800 : Int) atom1237Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11047729996800 : Int) atom1238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21624024038400 : Int) atom1239Coded) (CoefficientMerge.scale (19839379392000 : Int) atom1240Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33307519795200 : Int) atom1241Coded) (CoefficientMerge.scale (36744632870400 : Int) atom1242Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47909475532800 : Int) atom1243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59097361881600 : Int) atom1244Coded) (CoefficientMerge.scale (8371086796800 : Int) atom1245Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16355585433600 : Int) atom1246Coded) (CoefficientMerge.scale (16396177190400 : Int) atom1247Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22971182707200 : Int) atom1248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23375330316800 : Int) atom1249Coded) (CoefficientMerge.scale (35615926976000 : Int) atom1250Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39881932652800 : Int) atom1251Coded) (CoefficientMerge.scale (50170991001600 : Int) atom1252Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61314928214400 : Int) atom1253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11705777856000 : Int) atom1254Coded) (CoefficientMerge.scale (21699798566400 : Int) atom1255Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27731989051200 : Int) atom1256Coded) (CoefficientMerge.scale (27457319044800 : Int) atom1257Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42282031276800 : Int) atom1258Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47812699267200 : Int) atom1259Coded) (CoefficientMerge.scale (51497513812800 : Int) atom1260Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517790488000 : Int) atom1261Coded) (CoefficientMerge.scale (15983651980800 : Int) atom1262Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32380953292800 : Int) atom1263Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31420158336000 : Int) atom1264Coded) (CoefficientMerge.scale (51141665433600 : Int) atom1265Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58156348723200 : Int) atom1266Coded) (CoefficientMerge.scale (57274763212800 : Int) atom1267Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80303655398400 : Int) atom1268Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23458334054400 : Int) atom1269Coded) (CoefficientMerge.scale (44424079257600 : Int) atom1270Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68201800934400 : Int) atom1271Coded) (CoefficientMerge.scale (70646230771200 : Int) atom1272Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52545926361600 : Int) atom1273Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79011669542400 : Int) atom1274Coded) (CoefficientMerge.scale (17545854735360 : Int) atom1275Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55664911411200 : Int) atom1276Coded) (CoefficientMerge.scale (60106665427200 : Int) atom1277Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46866713241600 : Int) atom1278Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57384114883200 : Int) atom1279Coded) (CoefficientMerge.scale (40457273472000 : Int) atom1280Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65177036467200 : Int) atom1281Coded) (CoefficientMerge.scale (46861654694400 : Int) atom1282Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53756858937600 : Int) atom1283Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18855796377600 : Int) atom1284Coded) (CoefficientMerge.scale (24005993760000 : Int) atom1285Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30962904739200 : Int) atom1286Coded) (CoefficientMerge.scale (2264279068800 : Int) atom1287Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3207232022400 : Int) atom1288Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1289Coded) (CoefficientMerge.scale (84082924800 : Int) atom1290Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3734859508992 : Int) atom1291Coded) (CoefficientMerge.scale (2780052105600 : Int) atom1292Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (518028134400 : Int) atom1293Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1294Coded) (CoefficientMerge.scale (854359833600 : Int) atom1295Coded))))))))) := by
  rw [block017_data_flat159_step, block017_data_flat158_original]
theorem block017_data : block017 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (2066320569600 : Int) atom1216Coded) (CoefficientMerge.scale (2843362771200 : Int) atom1217Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (12526751865600 : Int) atom1218Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (9755314884000 : Int) atom1219Coded) (CoefficientMerge.scale (17449540819200 : Int) atom1220Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (24820650338400 : Int) atom1221Coded) (CoefficientMerge.scale (35164296367200 : Int) atom1222Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (45787493959200 : Int) atom1223Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3204336038400 : Int) atom1224Coded) (CoefficientMerge.scale (5399676979200 : Int) atom1225Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (5672221632000 : Int) atom1226Coded) (CoefficientMerge.scale (6371946201600 : Int) atom1227Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7071670771200 : Int) atom1228Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (17374084156800 : Int) atom1229Coded) (CoefficientMerge.scale (15150394274400 : Int) atom1230Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25703681270400 : Int) atom1231Coded) (CoefficientMerge.scale (31388299941600 : Int) atom1232Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42276310423200 : Int) atom1233Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53312311684800 : Int) atom1234Coded) (CoefficientMerge.scale (5780946124800 : Int) atom1235Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (10139247820800 : Int) atom1236Coded) (CoefficientMerge.scale (10593488908800 : Int) atom1237Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11047729996800 : Int) atom1238Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (21624024038400 : Int) atom1239Coded) (CoefficientMerge.scale (19839379392000 : Int) atom1240Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (33307519795200 : Int) atom1241Coded) (CoefficientMerge.scale (36744632870400 : Int) atom1242Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47909475532800 : Int) atom1243Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (59097361881600 : Int) atom1244Coded) (CoefficientMerge.scale (8371086796800 : Int) atom1245Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16355585433600 : Int) atom1246Coded) (CoefficientMerge.scale (16396177190400 : Int) atom1247Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (22971182707200 : Int) atom1248Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23375330316800 : Int) atom1249Coded) (CoefficientMerge.scale (35615926976000 : Int) atom1250Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39881932652800 : Int) atom1251Coded) (CoefficientMerge.scale (50170991001600 : Int) atom1252Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (61314928214400 : Int) atom1253Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (11705777856000 : Int) atom1254Coded) (CoefficientMerge.scale (21699798566400 : Int) atom1255Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (27731989051200 : Int) atom1256Coded) (CoefficientMerge.scale (27457319044800 : Int) atom1257Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (42282031276800 : Int) atom1258Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47812699267200 : Int) atom1259Coded) (CoefficientMerge.scale (51497513812800 : Int) atom1260Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68517790488000 : Int) atom1261Coded) (CoefficientMerge.scale (15983651980800 : Int) atom1262Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (32380953292800 : Int) atom1263Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (31420158336000 : Int) atom1264Coded) (CoefficientMerge.scale (51141665433600 : Int) atom1265Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58156348723200 : Int) atom1266Coded) (CoefficientMerge.scale (57274763212800 : Int) atom1267Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (80303655398400 : Int) atom1268Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23458334054400 : Int) atom1269Coded) (CoefficientMerge.scale (44424079257600 : Int) atom1270Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (68201800934400 : Int) atom1271Coded) (CoefficientMerge.scale (70646230771200 : Int) atom1272Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (52545926361600 : Int) atom1273Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (79011669542400 : Int) atom1274Coded) (CoefficientMerge.scale (17545854735360 : Int) atom1275Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (55664911411200 : Int) atom1276Coded) (CoefficientMerge.scale (60106665427200 : Int) atom1277Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (46866713241600 : Int) atom1278Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (57384114883200 : Int) atom1279Coded) (CoefficientMerge.scale (40457273472000 : Int) atom1280Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (65177036467200 : Int) atom1281Coded) (CoefficientMerge.scale (46861654694400 : Int) atom1282Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53756858937600 : Int) atom1283Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18855796377600 : Int) atom1284Coded) (CoefficientMerge.scale (24005993760000 : Int) atom1285Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (30962904739200 : Int) atom1286Coded) (CoefficientMerge.scale (2264279068800 : Int) atom1287Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3207232022400 : Int) atom1288Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1289Coded) (CoefficientMerge.scale (84082924800 : Int) atom1290Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3734859508992 : Int) atom1291Coded) (CoefficientMerge.scale (2780052105600 : Int) atom1292Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (518028134400 : Int) atom1293Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (427179916800 : Int) atom1294Coded) (CoefficientMerge.scale (854359833600 : Int) atom1295Coded)))))))) := by
  have h : block017 = block017_data_flat159 := by decide +kernel
  exact h.trans block017_data_flat159_original
theorem block017_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block017 := by
  rw [block017_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1216Coded_nonneg g hg hA hB) (atom1217Coded_nonneg g hg hA hB)) (add_nonneg (atom1218Coded_nonneg g hg hA hB) (add_nonneg (atom1219Coded_nonneg g hg hA hB) (atom1220Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1221Coded_nonneg g hg hA hB) (atom1222Coded_nonneg g hg hA hB)) (add_nonneg (atom1223Coded_nonneg g hg hA hB) (add_nonneg (atom1224Coded_nonneg g hg hA hB) (atom1225Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1226Coded_nonneg g hg hA hB) (atom1227Coded_nonneg g hg hA hB)) (add_nonneg (atom1228Coded_nonneg g hg hA hB) (add_nonneg (atom1229Coded_nonneg g hg hA hB) (atom1230Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1231Coded_nonneg g hg hA hB) (atom1232Coded_nonneg g hg hA hB)) (add_nonneg (atom1233Coded_nonneg g hg hA hB) (add_nonneg (atom1234Coded_nonneg g hg hA hB) (atom1235Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1236Coded_nonneg g hg hA hB) (atom1237Coded_nonneg g hg hA hB)) (add_nonneg (atom1238Coded_nonneg g hg hA hB) (add_nonneg (atom1239Coded_nonneg g hg hA hB) (atom1240Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1241Coded_nonneg g hg hA hB) (atom1242Coded_nonneg g hg hA hB)) (add_nonneg (atom1243Coded_nonneg g hg hA hB) (add_nonneg (atom1244Coded_nonneg g hg hA hB) (atom1245Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1246Coded_nonneg g hg hA hB) (atom1247Coded_nonneg g hg hA hB)) (add_nonneg (atom1248Coded_nonneg g hg hA hB) (add_nonneg (atom1249Coded_nonneg g hg hA hB) (atom1250Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1251Coded_nonneg g hg hA hB) (atom1252Coded_nonneg g hg hA hB)) (add_nonneg (atom1253Coded_nonneg g hg hA hB) (add_nonneg (atom1254Coded_nonneg g hg hA hB) (atom1255Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1256Coded_nonneg g hg hA hB) (atom1257Coded_nonneg g hg hA hB)) (add_nonneg (atom1258Coded_nonneg g hg hA hB) (add_nonneg (atom1259Coded_nonneg g hg hA hB) (atom1260Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1261Coded_nonneg g hg hA hB) (atom1262Coded_nonneg g hg hA hB)) (add_nonneg (atom1263Coded_nonneg g hg hA hB) (add_nonneg (atom1264Coded_nonneg g hg hA hB) (atom1265Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1266Coded_nonneg g hg hA hB) (atom1267Coded_nonneg g hg hA hB)) (add_nonneg (atom1268Coded_nonneg g hg hA hB) (add_nonneg (atom1269Coded_nonneg g hg hA hB) (atom1270Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1271Coded_nonneg g hg hA hB) (atom1272Coded_nonneg g hg hA hB)) (add_nonneg (atom1273Coded_nonneg g hg hA hB) (add_nonneg (atom1274Coded_nonneg g hg hA hB) (atom1275Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1276Coded_nonneg g hg hA hB) (atom1277Coded_nonneg g hg hA hB)) (add_nonneg (atom1278Coded_nonneg g hg hA hB) (add_nonneg (atom1279Coded_nonneg g hg hA hB) (atom1280Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1281Coded_nonneg g hg hA hB) (atom1282Coded_nonneg g hg hA hB)) (add_nonneg (atom1283Coded_nonneg g hg hA hB) (add_nonneg (atom1284Coded_nonneg g hg hA hB) (atom1285Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1286Coded_nonneg g hg hA hB) (atom1287Coded_nonneg g hg hA hB)) (add_nonneg (atom1288Coded_nonneg g hg hA hB) (add_nonneg (atom1289Coded_nonneg g hg hA hB) (atom1290Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1291Coded_nonneg g hg hA hB) (atom1292Coded_nonneg g hg hA hB)) (add_nonneg (atom1293Coded_nonneg g hg hA hB) (add_nonneg (atom1294Coded_nonneg g hg hA hB) (atom1295Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
