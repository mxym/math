-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1169 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1169 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1169 = ((g 3) * (g 11) * (g 13)) := by
  norm_num [atom1169, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1169_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (355486091647104 : Int) atom1169) := by
  rw [SparsePolynomial.eval_scale, eval_atom1169]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1169Coded : CoefficientMerge.Poly := [(nat_lit 2005, Int.ofNat (nat_lit 1))]
theorem atom1169Coded_decode : atom1169 = SparsePolynomial.decodeCubic 24 atom1169Coded := by decide +kernel
theorem atom1169Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (355486091647104 : Int) atom1169Coded) := by
  have h := atom1169_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1169Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1170 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1170 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1170 = ((g 3) * (g 11) * (g 14)) := by
  norm_num [atom1170, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1170_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (329946779695104 : Int) atom1170) := by
  rw [SparsePolynomial.eval_scale, eval_atom1170]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1170Coded : CoefficientMerge.Poly := [(nat_lit 2006, Int.ofNat (nat_lit 1))]
theorem atom1170Coded_decode : atom1170 = SparsePolynomial.decodeCubic 24 atom1170Coded := by decide +kernel
theorem atom1170Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (329946779695104 : Int) atom1170Coded) := by
  have h := atom1170_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1170Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1171 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1171 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1171 = ((g 3) * (g 11) * (g 15)) := by
  norm_num [atom1171, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1171_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (319194474338304 : Int) atom1171) := by
  rw [SparsePolynomial.eval_scale, eval_atom1171]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1171Coded : CoefficientMerge.Poly := [(nat_lit 2007, Int.ofNat (nat_lit 1))]
theorem atom1171Coded_decode : atom1171 = SparsePolynomial.decodeCubic 24 atom1171Coded := by decide +kernel
theorem atom1171Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (319194474338304 : Int) atom1171Coded) := by
  have h := atom1171_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1171Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1172 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1172 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1172 = ((g 3) * (g 11) * (g 16)) := by
  norm_num [atom1172, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1172_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (299702699311104 : Int) atom1172) := by
  rw [SparsePolynomial.eval_scale, eval_atom1172]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1172Coded : CoefficientMerge.Poly := [(nat_lit 2008, Int.ofNat (nat_lit 1))]
theorem atom1172Coded_decode : atom1172 = SparsePolynomial.decodeCubic 24 atom1172Coded := by decide +kernel
theorem atom1172Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (299702699311104 : Int) atom1172Coded) := by
  have h := atom1172_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1172Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1173 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1173 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1173 = ((g 3) * (g 11) * (g 17)) := by
  norm_num [atom1173, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1173_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (290143662741504 : Int) atom1173) := by
  rw [SparsePolynomial.eval_scale, eval_atom1173]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1173Coded : CoefficientMerge.Poly := [(nat_lit 2009, Int.ofNat (nat_lit 1))]
theorem atom1173Coded_decode : atom1173 = SparsePolynomial.decodeCubic 24 atom1173Coded := by decide +kernel
theorem atom1173Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (290143662741504 : Int) atom1173Coded) := by
  have h := atom1173_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1173Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1174 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1174 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1174 = ((g 3) * (g 11) * (g 18)) := by
  norm_num [atom1174, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1174_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (337360560787008 : Int) atom1174) := by
  rw [SparsePolynomial.eval_scale, eval_atom1174]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1174Coded : CoefficientMerge.Poly := [(nat_lit 2010, Int.ofNat (nat_lit 1))]
theorem atom1174Coded_decode : atom1174 = SparsePolynomial.decodeCubic 24 atom1174Coded := by decide +kernel
theorem atom1174Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (337360560787008 : Int) atom1174Coded) := by
  have h := atom1174_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1174Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1175 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1175 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1175 = ((g 3) * (g 11) * (g 19)) := by
  norm_num [atom1175, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1175_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (304119222359040 : Int) atom1175) := by
  rw [SparsePolynomial.eval_scale, eval_atom1175]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1175Coded : CoefficientMerge.Poly := [(nat_lit 2011, Int.ofNat (nat_lit 1))]
theorem atom1175Coded_decode : atom1175 = SparsePolynomial.decodeCubic 24 atom1175Coded := by decide +kernel
theorem atom1175Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (304119222359040 : Int) atom1175Coded) := by
  have h := atom1175_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1175Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1176 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1176 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1176 = ((g 3) * (g 11) * (g 20)) := by
  norm_num [atom1176, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1176_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (377844072902208 : Int) atom1176) := by
  rw [SparsePolynomial.eval_scale, eval_atom1176]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1176Coded : CoefficientMerge.Poly := [(nat_lit 2012, Int.ofNat (nat_lit 1))]
theorem atom1176Coded_decode : atom1176 = SparsePolynomial.decodeCubic 24 atom1176Coded := by decide +kernel
theorem atom1176Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (377844072902208 : Int) atom1176Coded) := by
  have h := atom1176_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1176Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1177 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1177 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1177 = ((g 3) * (g 11) * (g 21)) := by
  norm_num [atom1177, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1177_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (389393633958912 : Int) atom1177) := by
  rw [SparsePolynomial.eval_scale, eval_atom1177]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1177Coded : CoefficientMerge.Poly := [(nat_lit 2013, Int.ofNat (nat_lit 1))]
theorem atom1177Coded_decode : atom1177 = SparsePolynomial.decodeCubic 24 atom1177Coded := by decide +kernel
theorem atom1177Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (389393633958912 : Int) atom1177Coded) := by
  have h := atom1177_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1177Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1178 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1178 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1178 = ((g 3) * (g 11) * (g 22)) := by
  norm_num [atom1178, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1178_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (447547332418560 : Int) atom1178) := by
  rw [SparsePolynomial.eval_scale, eval_atom1178]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1178Coded : CoefficientMerge.Poly := [(nat_lit 2014, Int.ofNat (nat_lit 1))]
theorem atom1178Coded_decode : atom1178 = SparsePolynomial.decodeCubic 24 atom1178Coded := by decide +kernel
theorem atom1178Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (447547332418560 : Int) atom1178Coded) := by
  have h := atom1178_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1178Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1179 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 11, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1179 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1179 = ((g 3) * (g 11) * (g 23)) := by
  norm_num [atom1179, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1179_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (505701030878208 : Int) atom1179) := by
  rw [SparsePolynomial.eval_scale, eval_atom1179]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1179Coded : CoefficientMerge.Poly := [(nat_lit 2015, Int.ofNat (nat_lit 1))]
theorem atom1179Coded_decode : atom1179 = SparsePolynomial.decodeCubic 24 atom1179Coded := by decide +kernel
theorem atom1179Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (505701030878208 : Int) atom1179Coded) := by
  have h := atom1179_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1179Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1180 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1180 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1180 = ((g 3) * (g 12) * (g 12)) := by
  norm_num [atom1180, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1180_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (230328777469824 : Int) atom1180) := by
  rw [SparsePolynomial.eval_scale, eval_atom1180]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1180Coded : CoefficientMerge.Poly := [(nat_lit 2028, Int.ofNat (nat_lit 1))]
theorem atom1180Coded_decode : atom1180 = SparsePolynomial.decodeCubic 24 atom1180Coded := by decide +kernel
theorem atom1180Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (230328777469824 : Int) atom1180Coded) := by
  have h := atom1180_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1180Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1181 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1181 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1181 = ((g 3) * (g 12) * (g 13)) := by
  norm_num [atom1181, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1181_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (424979952465024 : Int) atom1181) := by
  rw [SparsePolynomial.eval_scale, eval_atom1181]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1181Coded : CoefficientMerge.Poly := [(nat_lit 2029, Int.ofNat (nat_lit 1))]
theorem atom1181Coded_decode : atom1181 = SparsePolynomial.decodeCubic 24 atom1181Coded := by decide +kernel
theorem atom1181Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (424979952465024 : Int) atom1181Coded) := by
  have h := atom1181_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1181Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1182 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1182 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1182 = ((g 3) * (g 12) * (g 14)) := by
  norm_num [atom1182, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1182_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (397441979725824 : Int) atom1182) := by
  rw [SparsePolynomial.eval_scale, eval_atom1182]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1182Coded : CoefficientMerge.Poly := [(nat_lit 2030, Int.ofNat (nat_lit 1))]
theorem atom1182Coded_decode : atom1182 = SparsePolynomial.decodeCubic 24 atom1182Coded := by decide +kernel
theorem atom1182Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (397441979725824 : Int) atom1182Coded) := by
  have h := atom1182_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1182Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1183 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1183 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1183 = ((g 3) * (g 12) * (g 15)) := by
  norm_num [atom1183, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1183_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (384691013581824 : Int) atom1183) := by
  rw [SparsePolynomial.eval_scale, eval_atom1183]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1183Coded : CoefficientMerge.Poly := [(nat_lit 2031, Int.ofNat (nat_lit 1))]
theorem atom1183Coded_decode : atom1183 = SparsePolynomial.decodeCubic 24 atom1183Coded := by decide +kernel
theorem atom1183Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (384691013581824 : Int) atom1183Coded) := by
  have h := atom1183_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1183Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1184 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1184 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1184 = ((g 3) * (g 12) * (g 16)) := by
  norm_num [atom1184, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1184_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (360117537191424 : Int) atom1184) := by
  rw [SparsePolynomial.eval_scale, eval_atom1184]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1184Coded : CoefficientMerge.Poly := [(nat_lit 2032, Int.ofNat (nat_lit 1))]
theorem atom1184Coded_decode : atom1184 = SparsePolynomial.decodeCubic 24 atom1184Coded := by decide +kernel
theorem atom1184Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (360117537191424 : Int) atom1184Coded) := by
  have h := atom1184_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1184Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1185 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1185 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1185 = ((g 3) * (g 12) * (g 17)) := by
  norm_num [atom1185, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1185_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (345476799258624 : Int) atom1185) := by
  rw [SparsePolynomial.eval_scale, eval_atom1185]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1185Coded : CoefficientMerge.Poly := [(nat_lit 2033, Int.ofNat (nat_lit 1))]
theorem atom1185Coded_decode : atom1185 = SparsePolynomial.decodeCubic 24 atom1185Coded := by decide +kernel
theorem atom1185Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (345476799258624 : Int) atom1185Coded) := by
  have h := atom1185_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1185Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1186 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1186 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1186 = ((g 3) * (g 12) * (g 18)) := by
  norm_num [atom1186, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1186_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (413276182501248 : Int) atom1186) := by
  rw [SparsePolynomial.eval_scale, eval_atom1186]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1186Coded : CoefficientMerge.Poly := [(nat_lit 2034, Int.ofNat (nat_lit 1))]
theorem atom1186Coded_decode : atom1186 = SparsePolynomial.decodeCubic 24 atom1186Coded := by decide +kernel
theorem atom1186Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (413276182501248 : Int) atom1186Coded) := by
  have h := atom1186_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1186Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1187 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1187 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1187 = ((g 3) * (g 12) * (g 19)) := by
  norm_num [atom1187, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1187_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (340052591831040 : Int) atom1187) := by
  rw [SparsePolynomial.eval_scale, eval_atom1187]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1187Coded : CoefficientMerge.Poly := [(nat_lit 2035, Int.ofNat (nat_lit 1))]
theorem atom1187Coded_decode : atom1187 = SparsePolynomial.decodeCubic 24 atom1187Coded := by decide +kernel
theorem atom1187Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (340052591831040 : Int) atom1187Coded) := by
  have h := atom1187_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1187Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1188 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1188 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1188 = ((g 3) * (g 12) * (g 20)) := by
  norm_num [atom1188, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1188_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (461924436555648 : Int) atom1188) := by
  rw [SparsePolynomial.eval_scale, eval_atom1188]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1188Coded : CoefficientMerge.Poly := [(nat_lit 2036, Int.ofNat (nat_lit 1))]
theorem atom1188Coded_decode : atom1188 = SparsePolynomial.decodeCubic 24 atom1188Coded := by decide +kernel
theorem atom1188Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (461924436555648 : Int) atom1188Coded) := by
  have h := atom1188_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1188Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1189 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1189 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1189 = ((g 3) * (g 12) * (g 21)) := by
  norm_num [atom1189, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1189_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (396690872067072 : Int) atom1189) := by
  rw [SparsePolynomial.eval_scale, eval_atom1189]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1189Coded : CoefficientMerge.Poly := [(nat_lit 2037, Int.ofNat (nat_lit 1))]
theorem atom1189Coded_decode : atom1189 = SparsePolynomial.decodeCubic 24 atom1189Coded := by decide +kernel
theorem atom1189Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (396690872067072 : Int) atom1189Coded) := by
  have h := atom1189_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1189Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1190 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1190 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1190 = ((g 3) * (g 12) * (g 22)) := by
  norm_num [atom1190, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1190_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (437447716738560 : Int) atom1190) := by
  rw [SparsePolynomial.eval_scale, eval_atom1190]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1190Coded : CoefficientMerge.Poly := [(nat_lit 2038, Int.ofNat (nat_lit 1))]
theorem atom1190Coded_decode : atom1190 = SparsePolynomial.decodeCubic 24 atom1190Coded := by decide +kernel
theorem atom1190Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (437447716738560 : Int) atom1190Coded) := by
  have h := atom1190_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1190Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1191 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 12, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1191 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1191 = ((g 3) * (g 12) * (g 23)) := by
  norm_num [atom1191, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1191_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (478204561410048 : Int) atom1191) := by
  rw [SparsePolynomial.eval_scale, eval_atom1191]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1191Coded : CoefficientMerge.Poly := [(nat_lit 2039, Int.ofNat (nat_lit 1))]
theorem atom1191Coded_decode : atom1191 = SparsePolynomial.decodeCubic 24 atom1191Coded := by decide +kernel
theorem atom1191Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (478204561410048 : Int) atom1191Coded) := by
  have h := atom1191_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1191Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1192 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1192 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1192 = ((g 3) * (g 13) * (g 13)) := by
  norm_num [atom1192, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1192_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (238834335801600 : Int) atom1192) := by
  rw [SparsePolynomial.eval_scale, eval_atom1192]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1192Coded : CoefficientMerge.Poly := [(nat_lit 2053, Int.ofNat (nat_lit 1))]
theorem atom1192Coded_decode : atom1192 = SparsePolynomial.decodeCubic 24 atom1192Coded := by decide +kernel
theorem atom1192Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (238834335801600 : Int) atom1192Coded) := by
  have h := atom1192_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1192Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1193 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1193 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1193 = ((g 3) * (g 13) * (g 14)) := by
  norm_num [atom1193, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1193_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (431701558041600 : Int) atom1193) := by
  rw [SparsePolynomial.eval_scale, eval_atom1193]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1193Coded : CoefficientMerge.Poly := [(nat_lit 2054, Int.ofNat (nat_lit 1))]
theorem atom1193Coded_decode : atom1193 = SparsePolynomial.decodeCubic 24 atom1193Coded := by decide +kernel
theorem atom1193Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (431701558041600 : Int) atom1193Coded) := by
  have h := atom1193_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1193Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1194 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1194 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1194 = ((g 3) * (g 13) * (g 15)) := by
  norm_num [atom1194, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1194_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (409765257216000 : Int) atom1194) := by
  rw [SparsePolynomial.eval_scale, eval_atom1194]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1194Coded : CoefficientMerge.Poly := [(nat_lit 2055, Int.ofNat (nat_lit 1))]
theorem atom1194Coded_decode : atom1194 = SparsePolynomial.decodeCubic 24 atom1194Coded := by decide +kernel
theorem atom1194Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (409765257216000 : Int) atom1194Coded) := by
  have h := atom1194_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1194Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1195 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1195 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1195 = ((g 3) * (g 13) * (g 16)) := by
  norm_num [atom1195, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1195_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (379089486720000 : Int) atom1195) := by
  rw [SparsePolynomial.eval_scale, eval_atom1195]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1195Coded : CoefficientMerge.Poly := [(nat_lit 2056, Int.ofNat (nat_lit 1))]
theorem atom1195Coded_decode : atom1195 = SparsePolynomial.decodeCubic 24 atom1195Coded := by decide +kernel
theorem atom1195Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (379089486720000 : Int) atom1195Coded) := by
  have h := atom1195_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1195Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1196 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1196 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1196 = ((g 3) * (g 13) * (g 17)) := by
  norm_num [atom1196, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1196_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (358346454681600 : Int) atom1196) := by
  rw [SparsePolynomial.eval_scale, eval_atom1196]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1196Coded : CoefficientMerge.Poly := [(nat_lit 2057, Int.ofNat (nat_lit 1))]
theorem atom1196Coded_decode : atom1196 = SparsePolynomial.decodeCubic 24 atom1196Coded := by decide +kernel
theorem atom1196Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (358346454681600 : Int) atom1196Coded) := by
  have h := atom1196_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1196Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1197 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1197 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1197 = ((g 3) * (g 13) * (g 18)) := by
  norm_num [atom1197, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1197_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (416025578707200 : Int) atom1197) := by
  rw [SparsePolynomial.eval_scale, eval_atom1197]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1197Coded : CoefficientMerge.Poly := [(nat_lit 2058, Int.ofNat (nat_lit 1))]
theorem atom1197Coded_decode : atom1197 = SparsePolynomial.decodeCubic 24 atom1197Coded := by decide +kernel
theorem atom1197Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (416025578707200 : Int) atom1197Coded) := by
  have h := atom1197_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1197Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1198 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1198 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1198 = ((g 3) * (g 13) * (g 19)) := by
  norm_num [atom1198, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1198_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (345906104544000 : Int) atom1198) := by
  rw [SparsePolynomial.eval_scale, eval_atom1198]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1198Coded : CoefficientMerge.Poly := [(nat_lit 2059, Int.ofNat (nat_lit 1))]
theorem atom1198Coded_decode : atom1198 = SparsePolynomial.decodeCubic 24 atom1198Coded := by decide +kernel
theorem atom1198Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (345906104544000 : Int) atom1198Coded) := by
  have h := atom1198_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1198Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1199 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1199 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1199 = ((g 3) * (g 13) * (g 20)) := by
  norm_num [atom1199, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1199_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (472838574700800 : Int) atom1199) := by
  rw [SparsePolynomial.eval_scale, eval_atom1199]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1199Coded : CoefficientMerge.Poly := [(nat_lit 2060, Int.ofNat (nat_lit 1))]
theorem atom1199Coded_decode : atom1199 = SparsePolynomial.decodeCubic 24 atom1199Coded := by decide +kernel
theorem atom1199Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (472838574700800 : Int) atom1199Coded) := by
  have h := atom1199_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1199Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1200 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1200 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1200 = ((g 3) * (g 13) * (g 21)) := by
  norm_num [atom1200, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1200_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (400716687571200 : Int) atom1200) := by
  rw [SparsePolynomial.eval_scale, eval_atom1200]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1200Coded : CoefficientMerge.Poly := [(nat_lit 2061, Int.ofNat (nat_lit 1))]
theorem atom1200Coded_decode : atom1200 = SparsePolynomial.decodeCubic 24 atom1200Coded := by decide +kernel
theorem atom1200Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (400716687571200 : Int) atom1200Coded) := by
  have h := atom1200_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1200Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1201 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1201 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1201 = ((g 3) * (g 13) * (g 22)) := by
  norm_num [atom1201, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1201_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (442289165472000 : Int) atom1201) := by
  rw [SparsePolynomial.eval_scale, eval_atom1201]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1201Coded : CoefficientMerge.Poly := [(nat_lit 2062, Int.ofNat (nat_lit 1))]
theorem atom1201Coded_decode : atom1201 = SparsePolynomial.decodeCubic 24 atom1201Coded := by decide +kernel
theorem atom1201Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (442289165472000 : Int) atom1201Coded) := by
  have h := atom1201_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1201Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1202 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 13, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1202 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1202 = ((g 3) * (g 13) * (g 23)) := by
  norm_num [atom1202, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1202_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (483861643372800 : Int) atom1202) := by
  rw [SparsePolynomial.eval_scale, eval_atom1202]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1202Coded : CoefficientMerge.Poly := [(nat_lit 2063, Int.ofNat (nat_lit 1))]
theorem atom1202Coded_decode : atom1202 = SparsePolynomial.decodeCubic 24 atom1202Coded := by decide +kernel
theorem atom1202Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (483861643372800 : Int) atom1202Coded) := by
  have h := atom1202_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1202Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1203 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1203 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1203 = ((g 3) * (g 14) * (g 14)) := by
  norm_num [atom1203, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1203_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (237050383046400 : Int) atom1203) := by
  rw [SparsePolynomial.eval_scale, eval_atom1203]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1203Coded : CoefficientMerge.Poly := [(nat_lit 2078, Int.ofNat (nat_lit 1))]
theorem atom1203Coded_decode : atom1203 = SparsePolynomial.decodeCubic 24 atom1203Coded := by decide +kernel
theorem atom1203Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (237050383046400 : Int) atom1203Coded) := by
  have h := atom1203_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1203Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1204 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1204 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1204 = ((g 3) * (g 14) * (g 15)) := by
  norm_num [atom1204, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1204_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (439906721184000 : Int) atom1204) := by
  rw [SparsePolynomial.eval_scale, eval_atom1204]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1204Coded : CoefficientMerge.Poly := [(nat_lit 2079, Int.ofNat (nat_lit 1))]
theorem atom1204Coded_decode : atom1204 = SparsePolynomial.decodeCubic 24 atom1204Coded := by decide +kernel
theorem atom1204Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (439906721184000 : Int) atom1204Coded) := by
  have h := atom1204_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1204Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1205 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1205 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1205 = ((g 3) * (g 14) * (g 16)) := by
  norm_num [atom1205, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1205_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (402108063840000 : Int) atom1205) := by
  rw [SparsePolynomial.eval_scale, eval_atom1205]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1205Coded : CoefficientMerge.Poly := [(nat_lit 2080, Int.ofNat (nat_lit 1))]
theorem atom1205Coded_decode : atom1205 = SparsePolynomial.decodeCubic 24 atom1205Coded := by decide +kernel
theorem atom1205Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (402108063840000 : Int) atom1205Coded) := by
  have h := atom1205_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1205Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1206 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1206 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1206 = ((g 3) * (g 14) * (g 17)) := by
  norm_num [atom1206, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1206_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (374242144953600 : Int) atom1206) := by
  rw [SparsePolynomial.eval_scale, eval_atom1206]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1206Coded : CoefficientMerge.Poly := [(nat_lit 2081, Int.ofNat (nat_lit 1))]
theorem atom1206Coded_decode : atom1206 = SparsePolynomial.decodeCubic 24 atom1206Coded := by decide +kernel
theorem atom1206Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (374242144953600 : Int) atom1206Coded) := by
  have h := atom1206_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1206Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1207 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1207 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1207 = ((g 3) * (g 14) * (g 18)) := by
  norm_num [atom1207, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1207_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (411426449280000 : Int) atom1207) := by
  rw [SparsePolynomial.eval_scale, eval_atom1207]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1207Coded : CoefficientMerge.Poly := [(nat_lit 2082, Int.ofNat (nat_lit 1))]
theorem atom1207Coded_decode : atom1207 = SparsePolynomial.decodeCubic 24 atom1207Coded := by decide +kernel
theorem atom1207Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (411426449280000 : Int) atom1207Coded) := by
  have h := atom1207_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1207Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1208 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1208 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1208 = ((g 3) * (g 14) * (g 19)) := by
  norm_num [atom1208, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1208_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (350110707962400 : Int) atom1208) := by
  rw [SparsePolynomial.eval_scale, eval_atom1208]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1208Coded : CoefficientMerge.Poly := [(nat_lit 2083, Int.ofNat (nat_lit 1))]
theorem atom1208Coded_decode : atom1208 = SparsePolynomial.decodeCubic 24 atom1208Coded := by decide +kernel
theorem atom1208Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (350110707962400 : Int) atom1208Coded) := by
  have h := atom1208_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1208Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1209 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1209 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1209 = ((g 3) * (g 14) * (g 20)) := by
  norm_num [atom1209, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1209_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (476404187212800 : Int) atom1209) := by
  rw [SparsePolynomial.eval_scale, eval_atom1209]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1209Coded : CoefficientMerge.Poly := [(nat_lit 2084, Int.ofNat (nat_lit 1))]
theorem atom1209Coded_decode : atom1209 = SparsePolynomial.decodeCubic 24 atom1209Coded := by decide +kernel
theorem atom1209Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (476404187212800 : Int) atom1209Coded) := by
  have h := atom1209_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1209Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1210 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 14, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1210 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1210 = ((g 3) * (g 14) * (g 21)) := by
  norm_num [atom1210, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1210_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (408364671052800 : Int) atom1210) := by
  rw [SparsePolynomial.eval_scale, eval_atom1210]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1210Coded : CoefficientMerge.Poly := [(nat_lit 2085, Int.ofNat (nat_lit 1))]
theorem atom1210Coded_decode : atom1210 = SparsePolynomial.decodeCubic 24 atom1210Coded := by decide +kernel
theorem atom1210Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (408364671052800 : Int) atom1210Coded) := by
  have h := atom1210_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1210Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1211 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 14, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1211 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1211 = ((g 3) * (g 14) * (g 22)) := by
  norm_num [atom1211, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1211_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (433640731154400 : Int) atom1211) := by
  rw [SparsePolynomial.eval_scale, eval_atom1211]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1211Coded : CoefficientMerge.Poly := [(nat_lit 2086, Int.ofNat (nat_lit 1))]
theorem atom1211Coded_decode : atom1211 = SparsePolynomial.decodeCubic 24 atom1211Coded := by decide +kernel
theorem atom1211Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (433640731154400 : Int) atom1211Coded) := by
  have h := atom1211_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1211Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1212 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 14, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1212 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1212 = ((g 3) * (g 14) * (g 23)) := by
  norm_num [atom1212, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1212_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (471496571330400 : Int) atom1212) := by
  rw [SparsePolynomial.eval_scale, eval_atom1212]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1212Coded : CoefficientMerge.Poly := [(nat_lit 2087, Int.ofNat (nat_lit 1))]
theorem atom1212Coded_decode : atom1212 = SparsePolynomial.decodeCubic 24 atom1212Coded := by decide +kernel
theorem atom1212Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (471496571330400 : Int) atom1212Coded) := by
  have h := atom1212_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1212Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1213 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1213 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1213 = ((g 3) * (g 15) * (g 15)) := by
  norm_num [atom1213, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1213_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (250122539520000 : Int) atom1213) := by
  rw [SparsePolynomial.eval_scale, eval_atom1213]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1213Coded : CoefficientMerge.Poly := [(nat_lit 2103, Int.ofNat (nat_lit 1))]
theorem atom1213Coded_decode : atom1213 = SparsePolynomial.decodeCubic 24 atom1213Coded := by decide +kernel
theorem atom1213Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (250122539520000 : Int) atom1213Coded) := by
  have h := atom1213_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1213Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1214 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1214 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1214 = ((g 3) * (g 15) * (g 16)) := by
  norm_num [atom1214, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1214_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (440950187059200 : Int) atom1214) := by
  rw [SparsePolynomial.eval_scale, eval_atom1214]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1214Coded : CoefficientMerge.Poly := [(nat_lit 2104, Int.ofNat (nat_lit 1))]
theorem atom1214Coded_decode : atom1214 = SparsePolynomial.decodeCubic 24 atom1214Coded := by decide +kernel
theorem atom1214Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (440950187059200 : Int) atom1214Coded) := by
  have h := atom1214_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1214Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1215 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1215 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1215 = ((g 3) * (g 15) * (g 17)) := by
  norm_num [atom1215, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1215_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (404940788582400 : Int) atom1215) := by
  rw [SparsePolynomial.eval_scale, eval_atom1215]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1215Coded : CoefficientMerge.Poly := [(nat_lit 2105, Int.ofNat (nat_lit 1))]
theorem atom1215Coded_decode : atom1215 = SparsePolynomial.decodeCubic 24 atom1215Coded := by decide +kernel
theorem atom1215Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (404940788582400 : Int) atom1215Coded) := by
  have h := atom1215_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1215Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1216 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1216 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1216 = ((g 3) * (g 15) * (g 18)) := by
  norm_num [atom1216, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1216_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (436401333043200 : Int) atom1216) := by
  rw [SparsePolynomial.eval_scale, eval_atom1216]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1216Coded : CoefficientMerge.Poly := [(nat_lit 2106, Int.ofNat (nat_lit 1))]
theorem atom1216Coded_decode : atom1216 = SparsePolynomial.decodeCubic 24 atom1216Coded := by decide +kernel
theorem atom1216Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (436401333043200 : Int) atom1216Coded) := by
  have h := atom1216_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1216Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1217 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1217 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1217 = ((g 3) * (g 15) * (g 19)) := by
  norm_num [atom1217, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1217_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (360026976153600 : Int) atom1217) := by
  rw [SparsePolynomial.eval_scale, eval_atom1217]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1217Coded : CoefficientMerge.Poly := [(nat_lit 2107, Int.ofNat (nat_lit 1))]
theorem atom1217Coded_decode : atom1217 = SparsePolynomial.decodeCubic 24 atom1217Coded := by decide +kernel
theorem atom1217Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (360026976153600 : Int) atom1217Coded) := by
  have h := atom1217_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1217Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1218 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1218 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1218 = ((g 3) * (g 15) * (g 20)) := by
  norm_num [atom1218, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1218_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (509543812915200 : Int) atom1218) := by
  rw [SparsePolynomial.eval_scale, eval_atom1218]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1218Coded : CoefficientMerge.Poly := [(nat_lit 2108, Int.ofNat (nat_lit 1))]
theorem atom1218Coded_decode : atom1218 = SparsePolynomial.decodeCubic 24 atom1218Coded := by decide +kernel
theorem atom1218Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (509543812915200 : Int) atom1218Coded) := by
  have h := atom1218_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1218Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1219 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 15, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1219 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1219 = ((g 3) * (g 15) * (g 21)) := by
  norm_num [atom1219, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1219_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (445586667724800 : Int) atom1219) := by
  rw [SparsePolynomial.eval_scale, eval_atom1219]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1219Coded : CoefficientMerge.Poly := [(nat_lit 2109, Int.ofNat (nat_lit 1))]
theorem atom1219Coded_decode : atom1219 = SparsePolynomial.decodeCubic 24 atom1219Coded := by decide +kernel
theorem atom1219Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (445586667724800 : Int) atom1219Coded) := by
  have h := atom1219_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1219Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1220 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 15, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1220 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1220 = ((g 3) * (g 15) * (g 22)) := by
  norm_num [atom1220, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1220_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (404141839718400 : Int) atom1220) := by
  rw [SparsePolynomial.eval_scale, eval_atom1220]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1220Coded : CoefficientMerge.Poly := [(nat_lit 2110, Int.ofNat (nat_lit 1))]
theorem atom1220Coded_decode : atom1220 = SparsePolynomial.decodeCubic 24 atom1220Coded := by decide +kernel
theorem atom1220Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (404141839718400 : Int) atom1220Coded) := by
  have h := atom1220_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1220Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1221 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 15, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1221 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1221 = ((g 3) * (g 15) * (g 23)) := by
  norm_num [atom1221, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1221_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (433071520358400 : Int) atom1221) := by
  rw [SparsePolynomial.eval_scale, eval_atom1221]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1221Coded : CoefficientMerge.Poly := [(nat_lit 2111, Int.ofNat (nat_lit 1))]
theorem atom1221Coded_decode : atom1221 = SparsePolynomial.decodeCubic 24 atom1221Coded := by decide +kernel
theorem atom1221Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (433071520358400 : Int) atom1221Coded) := by
  have h := atom1221_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1221Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1222 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1222 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1222 = ((g 3) * (g 16) * (g 16)) := by
  norm_num [atom1222, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1222_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (241176889497600 : Int) atom1222) := by
  rw [SparsePolynomial.eval_scale, eval_atom1222]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1222Coded : CoefficientMerge.Poly := [(nat_lit 2128, Int.ofNat (nat_lit 1))]
theorem atom1222Coded_decode : atom1222 = SparsePolynomial.decodeCubic 24 atom1222Coded := by decide +kernel
theorem atom1222Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (241176889497600 : Int) atom1222Coded) := by
  have h := atom1222_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1222Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1223 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1223 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1223 = ((g 3) * (g 16) * (g 17)) := by
  norm_num [atom1223, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1223_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (434097267609600 : Int) atom1223) := by
  rw [SparsePolynomial.eval_scale, eval_atom1223]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1223Coded : CoefficientMerge.Poly := [(nat_lit 2129, Int.ofNat (nat_lit 1))]
theorem atom1223Coded_decode : atom1223 = SparsePolynomial.decodeCubic 24 atom1223Coded := by decide +kernel
theorem atom1223Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (434097267609600 : Int) atom1223Coded) := by
  have h := atom1223_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1223Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1224 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1224 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1224 = ((g 3) * (g 16) * (g 18)) := by
  norm_num [atom1224, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1224_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (437731196313600 : Int) atom1224) := by
  rw [SparsePolynomial.eval_scale, eval_atom1224]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1224Coded : CoefficientMerge.Poly := [(nat_lit 2130, Int.ofNat (nat_lit 1))]
theorem atom1224Coded_decode : atom1224 = SparsePolynomial.decodeCubic 24 atom1224Coded := by decide +kernel
theorem atom1224Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (437731196313600 : Int) atom1224Coded) := by
  have h := atom1224_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1224Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1225 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1225 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1225 = ((g 3) * (g 16) * (g 19)) := by
  norm_num [atom1225, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1225_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (365439210393600 : Int) atom1225) := by
  rw [SparsePolynomial.eval_scale, eval_atom1225]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1225Coded : CoefficientMerge.Poly := [(nat_lit 2131, Int.ofNat (nat_lit 1))]
theorem atom1225Coded_decode : atom1225 = SparsePolynomial.decodeCubic 24 atom1225Coded := by decide +kernel
theorem atom1225Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (365439210393600 : Int) atom1225Coded) := by
  have h := atom1225_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1225Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1226 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1226 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1226 = ((g 3) * (g 16) * (g 20)) := by
  norm_num [atom1226, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1226_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (519038418124800 : Int) atom1226) := by
  rw [SparsePolynomial.eval_scale, eval_atom1226]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1226Coded : CoefficientMerge.Poly := [(nat_lit 2132, Int.ofNat (nat_lit 1))]
theorem atom1226Coded_decode : atom1226 = SparsePolynomial.decodeCubic 24 atom1226Coded := by decide +kernel
theorem atom1226Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (519038418124800 : Int) atom1226Coded) := by
  have h := atom1226_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1226Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1227 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 16, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1227 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1227 = ((g 3) * (g 16) * (g 21)) := by
  norm_num [atom1227, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1227_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (459163643904000 : Int) atom1227) := by
  rw [SparsePolynomial.eval_scale, eval_atom1227]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1227Coded : CoefficientMerge.Poly := [(nat_lit 2133, Int.ofNat (nat_lit 1))]
theorem atom1227Coded_decode : atom1227 = SparsePolynomial.decodeCubic 24 atom1227Coded := by decide +kernel
theorem atom1227Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (459163643904000 : Int) atom1227Coded) := by
  have h := atom1227_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1227Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1228 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 16, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1228 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1228 = ((g 3) * (g 16) * (g 22)) := by
  norm_num [atom1228, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1228_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (364008189888000 : Int) atom1228) := by
  rw [SparsePolynomial.eval_scale, eval_atom1228]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1228Coded : CoefficientMerge.Poly := [(nat_lit 2134, Int.ofNat (nat_lit 1))]
theorem atom1228Coded_decode : atom1228 = SparsePolynomial.decodeCubic 24 atom1228Coded := by decide +kernel
theorem atom1228Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (364008189888000 : Int) atom1228Coded) := by
  have h := atom1228_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1228Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1229 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 16, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1229 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1229 = ((g 3) * (g 16) * (g 23)) := by
  norm_num [atom1229, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1229_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (473555032473600 : Int) atom1229) := by
  rw [SparsePolynomial.eval_scale, eval_atom1229]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1229Coded : CoefficientMerge.Poly := [(nat_lit 2135, Int.ofNat (nat_lit 1))]
theorem atom1229Coded_decode : atom1229 = SparsePolynomial.decodeCubic 24 atom1229Coded := by decide +kernel
theorem atom1229Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (473555032473600 : Int) atom1229Coded) := by
  have h := atom1229_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1229Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1230 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1230 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1230 = ((g 3) * (g 17) * (g 17)) := by
  norm_num [atom1230, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1230_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (238478504140800 : Int) atom1230) := by
  rw [SparsePolynomial.eval_scale, eval_atom1230]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1230Coded : CoefficientMerge.Poly := [(nat_lit 2153, Int.ofNat (nat_lit 1))]
theorem atom1230Coded_decode : atom1230 = SparsePolynomial.decodeCubic 24 atom1230Coded := by decide +kernel
theorem atom1230Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (238478504140800 : Int) atom1230Coded) := by
  have h := atom1230_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1230Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1231 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1231 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1231 = ((g 3) * (g 17) * (g 18)) := by
  norm_num [atom1231, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1231_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (458926536499200 : Int) atom1231) := by
  rw [SparsePolynomial.eval_scale, eval_atom1231]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1231Coded : CoefficientMerge.Poly := [(nat_lit 2154, Int.ofNat (nat_lit 1))]
theorem atom1231Coded_decode : atom1231 = SparsePolynomial.decodeCubic 24 atom1231Coded := by decide +kernel
theorem atom1231Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (458926536499200 : Int) atom1231Coded) := by
  have h := atom1231_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1231Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1232 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1232 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1232 = ((g 3) * (g 17) * (g 19)) := by
  norm_num [atom1232, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1232_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (390716921548800 : Int) atom1232) := by
  rw [SparsePolynomial.eval_scale, eval_atom1232]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1232Coded : CoefficientMerge.Poly := [(nat_lit 2155, Int.ofNat (nat_lit 1))]
theorem atom1232Coded_decode : atom1232 = SparsePolynomial.decodeCubic 24 atom1232Coded := by decide +kernel
theorem atom1232Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (390716921548800 : Int) atom1232Coded) := by
  have h := atom1232_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1232Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1233 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1233 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1233 = ((g 3) * (g 17) * (g 20)) := by
  norm_num [atom1233, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1233_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (548398500249600 : Int) atom1233) := by
  rw [SparsePolynomial.eval_scale, eval_atom1233]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1233Coded : CoefficientMerge.Poly := [(nat_lit 2156, Int.ofNat (nat_lit 1))]
theorem atom1233Coded_decode : atom1233 = SparsePolynomial.decodeCubic 24 atom1233Coded := by decide +kernel
theorem atom1233Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (548398500249600 : Int) atom1233Coded) := by
  have h := atom1233_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1233Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1234 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 17, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1234 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1234 = ((g 3) * (g 17) * (g 21)) := by
  norm_num [atom1234, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1234_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (492606096998400 : Int) atom1234) := by
  rw [SparsePolynomial.eval_scale, eval_atom1234]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1234Coded : CoefficientMerge.Poly := [(nat_lit 2157, Int.ofNat (nat_lit 1))]
theorem atom1234Coded_decode : atom1234 = SparsePolynomial.decodeCubic 24 atom1234Coded := by decide +kernel
theorem atom1234Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (492606096998400 : Int) atom1234Coded) := by
  have h := atom1234_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1234Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1235 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 17, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1235 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1235 = ((g 3) * (g 17) * (g 22)) := by
  norm_num [atom1235, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1235_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (400409331033600 : Int) atom1235) := by
  rw [SparsePolynomial.eval_scale, eval_atom1235]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1235Coded : CoefficientMerge.Poly := [(nat_lit 2158, Int.ofNat (nat_lit 1))]
theorem atom1235Coded_decode : atom1235 = SparsePolynomial.decodeCubic 24 atom1235Coded := by decide +kernel
theorem atom1235Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (400409331033600 : Int) atom1235Coded) := by
  have h := atom1235_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1235Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1236 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 17, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1236 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1236 = ((g 3) * (g 17) * (g 23)) := by
  norm_num [atom1236, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1236_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (514038544588800 : Int) atom1236) := by
  rw [SparsePolynomial.eval_scale, eval_atom1236]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1236Coded : CoefficientMerge.Poly := [(nat_lit 2159, Int.ofNat (nat_lit 1))]
theorem atom1236Coded_decode : atom1236 = SparsePolynomial.decodeCubic 24 atom1236Coded := by decide +kernel
theorem atom1236Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (514038544588800 : Int) atom1236Coded) := by
  have h := atom1236_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1236Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1237 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1237 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1237 = ((g 3) * (g 18) * (g 18)) := by
  norm_num [atom1237, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1237_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (269691632179200 : Int) atom1237) := by
  rw [SparsePolynomial.eval_scale, eval_atom1237]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1237Coded : CoefficientMerge.Poly := [(nat_lit 2178, Int.ofNat (nat_lit 1))]
theorem atom1237Coded_decode : atom1237 = SparsePolynomial.decodeCubic 24 atom1237Coded := by decide +kernel
theorem atom1237Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (269691632179200 : Int) atom1237Coded) := by
  have h := atom1237_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1237Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1238 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1238 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1238 = ((g 3) * (g 18) * (g 19)) := by
  norm_num [atom1238, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1238_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (461307919564800 : Int) atom1238) := by
  rw [SparsePolynomial.eval_scale, eval_atom1238]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1238Coded : CoefficientMerge.Poly := [(nat_lit 2179, Int.ofNat (nat_lit 1))]
theorem atom1238Coded_decode : atom1238 = SparsePolynomial.decodeCubic 24 atom1238Coded := by decide +kernel
theorem atom1238Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (461307919564800 : Int) atom1238Coded) := by
  have h := atom1238_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1238Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1239 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1239 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1239 = ((g 3) * (g 18) * (g 20)) := by
  norm_num [atom1239, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1239_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (637019970048000 : Int) atom1239) := by
  rw [SparsePolynomial.eval_scale, eval_atom1239]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1239Coded : CoefficientMerge.Poly := [(nat_lit 2180, Int.ofNat (nat_lit 1))]
theorem atom1239Coded_decode : atom1239 = SparsePolynomial.decodeCubic 24 atom1239Coded := by decide +kernel
theorem atom1239Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (637019970048000 : Int) atom1239Coded) := by
  have h := atom1239_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1239Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1240 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 18, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1240 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1240 = ((g 3) * (g 18) * (g 21)) := by
  norm_num [atom1240, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1240_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (565153231104000 : Int) atom1240) := by
  rw [SparsePolynomial.eval_scale, eval_atom1240]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1240Coded : CoefficientMerge.Poly := [(nat_lit 2181, Int.ofNat (nat_lit 1))]
theorem atom1240Coded_decode : atom1240 = SparsePolynomial.decodeCubic 24 atom1240Coded := by decide +kernel
theorem atom1240Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (565153231104000 : Int) atom1240Coded) := by
  have h := atom1240_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1240Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1241 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 18, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1241 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1241 = ((g 3) * (g 18) * (g 22)) := by
  norm_num [atom1241, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1241_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (382207149676800 : Int) atom1241) := by
  rw [SparsePolynomial.eval_scale, eval_atom1241]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1241Coded : CoefficientMerge.Poly := [(nat_lit 2182, Int.ofNat (nat_lit 1))]
theorem atom1241Coded_decode : atom1241 = SparsePolynomial.decodeCubic 24 atom1241Coded := by decide +kernel
theorem atom1241Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (382207149676800 : Int) atom1241Coded) := by
  have h := atom1241_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1241Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1242 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 18, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1242 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1242 = ((g 3) * (g 18) * (g 23)) := by
  norm_num [atom1242, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1242_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (528156744192000 : Int) atom1242) := by
  rw [SparsePolynomial.eval_scale, eval_atom1242]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1242Coded : CoefficientMerge.Poly := [(nat_lit 2183, Int.ofNat (nat_lit 1))]
theorem atom1242Coded_decode : atom1242 = SparsePolynomial.decodeCubic 24 atom1242Coded := by decide +kernel
theorem atom1242Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (528156744192000 : Int) atom1242Coded) := by
  have h := atom1242_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1242Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1243 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 19, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1243 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1243 = ((g 3) * (g 19) * (g 19)) := by
  norm_num [atom1243, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1243_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (175133714595840 : Int) atom1243) := by
  rw [SparsePolynomial.eval_scale, eval_atom1243]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1243Coded : CoefficientMerge.Poly := [(nat_lit 2203, Int.ofNat (nat_lit 1))]
theorem atom1243Coded_decode : atom1243 = SparsePolynomial.decodeCubic 24 atom1243Coded := by decide +kernel
theorem atom1243Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (175133714595840 : Int) atom1243Coded) := by
  have h := atom1243_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1243Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1244 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 19, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1244 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1244 = ((g 3) * (g 19) * (g 20)) := by
  norm_num [atom1244, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1244_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (510466469990400 : Int) atom1244) := by
  rw [SparsePolynomial.eval_scale, eval_atom1244]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1244Coded : CoefficientMerge.Poly := [(nat_lit 2204, Int.ofNat (nat_lit 1))]
theorem atom1244Coded_decode : atom1244 = SparsePolynomial.decodeCubic 24 atom1244Coded := by decide +kernel
theorem atom1244Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (510466469990400 : Int) atom1244Coded) := by
  have h := atom1244_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1244Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1245 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 19, nat_lit 21], Int.ofNat (nat_lit 1))]
theorem eval_atom1245 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1245 = ((g 3) * (g 19) * (g 21)) := by
  norm_num [atom1245, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1245_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (485972244172800 : Int) atom1245) := by
  rw [SparsePolynomial.eval_scale, eval_atom1245]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1245Coded : CoefficientMerge.Poly := [(nat_lit 2205, Int.ofNat (nat_lit 1))]
theorem atom1245Coded_decode : atom1245 = SparsePolynomial.decodeCubic 24 atom1245Coded := by decide +kernel
theorem atom1245Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (485972244172800 : Int) atom1245Coded) := by
  have h := atom1245_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1245Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1246 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 19, nat_lit 22], Int.ofNat (nat_lit 1))]
theorem eval_atom1246 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1246 = ((g 3) * (g 19) * (g 22)) := by
  norm_num [atom1246, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1246_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (349403855673600 : Int) atom1246) := by
  rw [SparsePolynomial.eval_scale, eval_atom1246]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1246Coded : CoefficientMerge.Poly := [(nat_lit 2206, Int.ofNat (nat_lit 1))]
theorem atom1246Coded_decode : atom1246 = SparsePolynomial.decodeCubic 24 atom1246Coded := by decide +kernel
theorem atom1246Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (349403855673600 : Int) atom1246Coded) := by
  have h := atom1246_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1246Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1247 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 19, nat_lit 23], Int.ofNat (nat_lit 1))]
theorem eval_atom1247 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1247 = ((g 3) * (g 19) * (g 23)) := by
  norm_num [atom1247, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1247_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (370049918515200 : Int) atom1247) := by
  rw [SparsePolynomial.eval_scale, eval_atom1247]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1247Coded : CoefficientMerge.Poly := [(nat_lit 2207, Int.ofNat (nat_lit 1))]
theorem atom1247Coded_decode : atom1247 = SparsePolynomial.decodeCubic 24 atom1247Coded := by decide +kernel
theorem atom1247Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (370049918515200 : Int) atom1247Coded) := by
  have h := atom1247_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1247Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1248 : SparsePolynomial.Poly := [([nat_lit 3, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1248 (g : Fin 24 → ℝ) : SparsePolynomial.eval (gapValues g) atom1248 = ((g 3) * (g 20) * (g 20)) := by
  norm_num [atom1248, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1248_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (346746384230400 : Int) atom1248) := by
  rw [SparsePolynomial.eval_scale, eval_atom1248]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1248Coded : CoefficientMerge.Poly := [(nat_lit 2228, Int.ofNat (nat_lit 1))]
theorem atom1248Coded_decode : atom1248 = SparsePolynomial.decodeCubic 24 atom1248Coded := by decide +kernel
theorem atom1248Coded_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) (CoefficientMerge.scale (346746384230400 : Int) atom1248Coded) := by
  have h := atom1248_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1248Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block017 : CoefficientMerge.Poly := [(nat_lit 2005, Int.ofNat (nat_lit 355486091647104)), (nat_lit 2006, Int.ofNat (nat_lit 329946779695104)), (nat_lit 2007, Int.ofNat (nat_lit 319194474338304)), (nat_lit 2008, Int.ofNat (nat_lit 299702699311104)), (nat_lit 2009, Int.ofNat (nat_lit 290143662741504)), (nat_lit 2010, Int.ofNat (nat_lit 337360560787008)), (nat_lit 2011, Int.ofNat (nat_lit 304119222359040)), (nat_lit 2012, Int.ofNat (nat_lit 377844072902208)), (nat_lit 2013, Int.ofNat (nat_lit 389393633958912)), (nat_lit 2014, Int.ofNat (nat_lit 447547332418560)), (nat_lit 2015, Int.ofNat (nat_lit 505701030878208)), (nat_lit 2028, Int.ofNat (nat_lit 230328777469824)), (nat_lit 2029, Int.ofNat (nat_lit 424979952465024)), (nat_lit 2030, Int.ofNat (nat_lit 397441979725824)), (nat_lit 2031, Int.ofNat (nat_lit 384691013581824)), (nat_lit 2032, Int.ofNat (nat_lit 360117537191424)), (nat_lit 2033, Int.ofNat (nat_lit 345476799258624)), (nat_lit 2034, Int.ofNat (nat_lit 413276182501248)), (nat_lit 2035, Int.ofNat (nat_lit 340052591831040)), (nat_lit 2036, Int.ofNat (nat_lit 461924436555648)), (nat_lit 2037, Int.ofNat (nat_lit 396690872067072)), (nat_lit 2038, Int.ofNat (nat_lit 437447716738560)), (nat_lit 2039, Int.ofNat (nat_lit 478204561410048)), (nat_lit 2053, Int.ofNat (nat_lit 238834335801600)), (nat_lit 2054, Int.ofNat (nat_lit 431701558041600)), (nat_lit 2055, Int.ofNat (nat_lit 409765257216000)), (nat_lit 2056, Int.ofNat (nat_lit 379089486720000)), (nat_lit 2057, Int.ofNat (nat_lit 358346454681600)), (nat_lit 2058, Int.ofNat (nat_lit 416025578707200)), (nat_lit 2059, Int.ofNat (nat_lit 345906104544000)), (nat_lit 2060, Int.ofNat (nat_lit 472838574700800)), (nat_lit 2061, Int.ofNat (nat_lit 400716687571200)), (nat_lit 2062, Int.ofNat (nat_lit 442289165472000)), (nat_lit 2063, Int.ofNat (nat_lit 483861643372800)), (nat_lit 2078, Int.ofNat (nat_lit 237050383046400)), (nat_lit 2079, Int.ofNat (nat_lit 439906721184000)), (nat_lit 2080, Int.ofNat (nat_lit 402108063840000)), (nat_lit 2081, Int.ofNat (nat_lit 374242144953600)), (nat_lit 2082, Int.ofNat (nat_lit 411426449280000)), (nat_lit 2083, Int.ofNat (nat_lit 350110707962400)), (nat_lit 2084, Int.ofNat (nat_lit 476404187212800)), (nat_lit 2085, Int.ofNat (nat_lit 408364671052800)), (nat_lit 2086, Int.ofNat (nat_lit 433640731154400)), (nat_lit 2087, Int.ofNat (nat_lit 471496571330400)), (nat_lit 2103, Int.ofNat (nat_lit 250122539520000)), (nat_lit 2104, Int.ofNat (nat_lit 440950187059200)), (nat_lit 2105, Int.ofNat (nat_lit 404940788582400)), (nat_lit 2106, Int.ofNat (nat_lit 436401333043200)), (nat_lit 2107, Int.ofNat (nat_lit 360026976153600)), (nat_lit 2108, Int.ofNat (nat_lit 509543812915200)), (nat_lit 2109, Int.ofNat (nat_lit 445586667724800)), (nat_lit 2110, Int.ofNat (nat_lit 404141839718400)), (nat_lit 2111, Int.ofNat (nat_lit 433071520358400)), (nat_lit 2128, Int.ofNat (nat_lit 241176889497600)), (nat_lit 2129, Int.ofNat (nat_lit 434097267609600)), (nat_lit 2130, Int.ofNat (nat_lit 437731196313600)), (nat_lit 2131, Int.ofNat (nat_lit 365439210393600)), (nat_lit 2132, Int.ofNat (nat_lit 519038418124800)), (nat_lit 2133, Int.ofNat (nat_lit 459163643904000)), (nat_lit 2134, Int.ofNat (nat_lit 364008189888000)), (nat_lit 2135, Int.ofNat (nat_lit 473555032473600)), (nat_lit 2153, Int.ofNat (nat_lit 238478504140800)), (nat_lit 2154, Int.ofNat (nat_lit 458926536499200)), (nat_lit 2155, Int.ofNat (nat_lit 390716921548800)), (nat_lit 2156, Int.ofNat (nat_lit 548398500249600)), (nat_lit 2157, Int.ofNat (nat_lit 492606096998400)), (nat_lit 2158, Int.ofNat (nat_lit 400409331033600)), (nat_lit 2159, Int.ofNat (nat_lit 514038544588800)), (nat_lit 2178, Int.ofNat (nat_lit 269691632179200)), (nat_lit 2179, Int.ofNat (nat_lit 461307919564800)), (nat_lit 2180, Int.ofNat (nat_lit 637019970048000)), (nat_lit 2181, Int.ofNat (nat_lit 565153231104000)), (nat_lit 2182, Int.ofNat (nat_lit 382207149676800)), (nat_lit 2183, Int.ofNat (nat_lit 528156744192000)), (nat_lit 2203, Int.ofNat (nat_lit 175133714595840)), (nat_lit 2204, Int.ofNat (nat_lit 510466469990400)), (nat_lit 2205, Int.ofNat (nat_lit 485972244172800)), (nat_lit 2206, Int.ofNat (nat_lit 349403855673600)), (nat_lit 2207, Int.ofNat (nat_lit 370049918515200)), (nat_lit 2228, Int.ofNat (nat_lit 346746384230400))]
def block017_data_flat000 : CoefficientMerge.Poly := [(nat_lit 2005, Int.ofNat (nat_lit 355486091647104))]
theorem block017_data_flat000_step : block017_data_flat000 = (CoefficientMerge.scale (355486091647104 : Int) atom1169Coded) := by decide +kernel
theorem block017_data_flat000_original : block017_data_flat000 = (CoefficientMerge.scale (355486091647104 : Int) atom1169Coded) := by
  rw [block017_data_flat000_step]
def block017_data_flat001 : CoefficientMerge.Poly := [(nat_lit 2006, Int.ofNat (nat_lit 329946779695104))]
theorem block017_data_flat001_step : block017_data_flat001 = (CoefficientMerge.scale (329946779695104 : Int) atom1170Coded) := by decide +kernel
theorem block017_data_flat001_original : block017_data_flat001 = (CoefficientMerge.scale (329946779695104 : Int) atom1170Coded) := by
  rw [block017_data_flat001_step]
def block017_data_flat002 : CoefficientMerge.Poly := [(nat_lit 2005, Int.ofNat (nat_lit 355486091647104)), (nat_lit 2006, Int.ofNat (nat_lit 329946779695104))]
theorem block017_data_flat002_step : block017_data_flat002 = (CoefficientMerge.fastMerge block017_data_flat000 block017_data_flat001) := by decide +kernel
theorem block017_data_flat002_original : block017_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (355486091647104 : Int) atom1169Coded) (CoefficientMerge.scale (329946779695104 : Int) atom1170Coded)) := by
  rw [block017_data_flat002_step, block017_data_flat000_original, block017_data_flat001_original]
def block017_data_flat003 : CoefficientMerge.Poly := [(nat_lit 2007, Int.ofNat (nat_lit 319194474338304))]
theorem block017_data_flat003_step : block017_data_flat003 = (CoefficientMerge.scale (319194474338304 : Int) atom1171Coded) := by decide +kernel
theorem block017_data_flat003_original : block017_data_flat003 = (CoefficientMerge.scale (319194474338304 : Int) atom1171Coded) := by
  rw [block017_data_flat003_step]
def block017_data_flat004 : CoefficientMerge.Poly := [(nat_lit 2008, Int.ofNat (nat_lit 299702699311104))]
theorem block017_data_flat004_step : block017_data_flat004 = (CoefficientMerge.scale (299702699311104 : Int) atom1172Coded) := by decide +kernel
theorem block017_data_flat004_original : block017_data_flat004 = (CoefficientMerge.scale (299702699311104 : Int) atom1172Coded) := by
  rw [block017_data_flat004_step]
def block017_data_flat005 : CoefficientMerge.Poly := [(nat_lit 2009, Int.ofNat (nat_lit 290143662741504))]
theorem block017_data_flat005_step : block017_data_flat005 = (CoefficientMerge.scale (290143662741504 : Int) atom1173Coded) := by decide +kernel
theorem block017_data_flat005_original : block017_data_flat005 = (CoefficientMerge.scale (290143662741504 : Int) atom1173Coded) := by
  rw [block017_data_flat005_step]
def block017_data_flat006 : CoefficientMerge.Poly := [(nat_lit 2008, Int.ofNat (nat_lit 299702699311104)), (nat_lit 2009, Int.ofNat (nat_lit 290143662741504))]
theorem block017_data_flat006_step : block017_data_flat006 = (CoefficientMerge.fastMerge block017_data_flat004 block017_data_flat005) := by decide +kernel
theorem block017_data_flat006_original : block017_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (299702699311104 : Int) atom1172Coded) (CoefficientMerge.scale (290143662741504 : Int) atom1173Coded)) := by
  rw [block017_data_flat006_step, block017_data_flat004_original, block017_data_flat005_original]
def block017_data_flat007 : CoefficientMerge.Poly := [(nat_lit 2007, Int.ofNat (nat_lit 319194474338304)), (nat_lit 2008, Int.ofNat (nat_lit 299702699311104)), (nat_lit 2009, Int.ofNat (nat_lit 290143662741504))]
theorem block017_data_flat007_step : block017_data_flat007 = (CoefficientMerge.fastMerge block017_data_flat003 block017_data_flat006) := by decide +kernel
theorem block017_data_flat007_original : block017_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (319194474338304 : Int) atom1171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299702699311104 : Int) atom1172Coded) (CoefficientMerge.scale (290143662741504 : Int) atom1173Coded))) := by
  rw [block017_data_flat007_step, block017_data_flat003_original, block017_data_flat006_original]
def block017_data_flat008 : CoefficientMerge.Poly := [(nat_lit 2005, Int.ofNat (nat_lit 355486091647104)), (nat_lit 2006, Int.ofNat (nat_lit 329946779695104)), (nat_lit 2007, Int.ofNat (nat_lit 319194474338304)), (nat_lit 2008, Int.ofNat (nat_lit 299702699311104)), (nat_lit 2009, Int.ofNat (nat_lit 290143662741504))]
theorem block017_data_flat008_step : block017_data_flat008 = (CoefficientMerge.fastMerge block017_data_flat002 block017_data_flat007) := by decide +kernel
theorem block017_data_flat008_original : block017_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (355486091647104 : Int) atom1169Coded) (CoefficientMerge.scale (329946779695104 : Int) atom1170Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (319194474338304 : Int) atom1171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299702699311104 : Int) atom1172Coded) (CoefficientMerge.scale (290143662741504 : Int) atom1173Coded)))) := by
  rw [block017_data_flat008_step, block017_data_flat002_original, block017_data_flat007_original]
def block017_data_flat009 : CoefficientMerge.Poly := [(nat_lit 2010, Int.ofNat (nat_lit 337360560787008))]
theorem block017_data_flat009_step : block017_data_flat009 = (CoefficientMerge.scale (337360560787008 : Int) atom1174Coded) := by decide +kernel
theorem block017_data_flat009_original : block017_data_flat009 = (CoefficientMerge.scale (337360560787008 : Int) atom1174Coded) := by
  rw [block017_data_flat009_step]
def block017_data_flat010 : CoefficientMerge.Poly := [(nat_lit 2011, Int.ofNat (nat_lit 304119222359040))]
theorem block017_data_flat010_step : block017_data_flat010 = (CoefficientMerge.scale (304119222359040 : Int) atom1175Coded) := by decide +kernel
theorem block017_data_flat010_original : block017_data_flat010 = (CoefficientMerge.scale (304119222359040 : Int) atom1175Coded) := by
  rw [block017_data_flat010_step]
def block017_data_flat011 : CoefficientMerge.Poly := [(nat_lit 2010, Int.ofNat (nat_lit 337360560787008)), (nat_lit 2011, Int.ofNat (nat_lit 304119222359040))]
theorem block017_data_flat011_step : block017_data_flat011 = (CoefficientMerge.fastMerge block017_data_flat009 block017_data_flat010) := by decide +kernel
theorem block017_data_flat011_original : block017_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (337360560787008 : Int) atom1174Coded) (CoefficientMerge.scale (304119222359040 : Int) atom1175Coded)) := by
  rw [block017_data_flat011_step, block017_data_flat009_original, block017_data_flat010_original]
def block017_data_flat012 : CoefficientMerge.Poly := [(nat_lit 2012, Int.ofNat (nat_lit 377844072902208))]
theorem block017_data_flat012_step : block017_data_flat012 = (CoefficientMerge.scale (377844072902208 : Int) atom1176Coded) := by decide +kernel
theorem block017_data_flat012_original : block017_data_flat012 = (CoefficientMerge.scale (377844072902208 : Int) atom1176Coded) := by
  rw [block017_data_flat012_step]
def block017_data_flat013 : CoefficientMerge.Poly := [(nat_lit 2013, Int.ofNat (nat_lit 389393633958912))]
theorem block017_data_flat013_step : block017_data_flat013 = (CoefficientMerge.scale (389393633958912 : Int) atom1177Coded) := by decide +kernel
theorem block017_data_flat013_original : block017_data_flat013 = (CoefficientMerge.scale (389393633958912 : Int) atom1177Coded) := by
  rw [block017_data_flat013_step]
def block017_data_flat014 : CoefficientMerge.Poly := [(nat_lit 2014, Int.ofNat (nat_lit 447547332418560))]
theorem block017_data_flat014_step : block017_data_flat014 = (CoefficientMerge.scale (447547332418560 : Int) atom1178Coded) := by decide +kernel
theorem block017_data_flat014_original : block017_data_flat014 = (CoefficientMerge.scale (447547332418560 : Int) atom1178Coded) := by
  rw [block017_data_flat014_step]
def block017_data_flat015 : CoefficientMerge.Poly := [(nat_lit 2013, Int.ofNat (nat_lit 389393633958912)), (nat_lit 2014, Int.ofNat (nat_lit 447547332418560))]
theorem block017_data_flat015_step : block017_data_flat015 = (CoefficientMerge.fastMerge block017_data_flat013 block017_data_flat014) := by decide +kernel
theorem block017_data_flat015_original : block017_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (389393633958912 : Int) atom1177Coded) (CoefficientMerge.scale (447547332418560 : Int) atom1178Coded)) := by
  rw [block017_data_flat015_step, block017_data_flat013_original, block017_data_flat014_original]
def block017_data_flat016 : CoefficientMerge.Poly := [(nat_lit 2012, Int.ofNat (nat_lit 377844072902208)), (nat_lit 2013, Int.ofNat (nat_lit 389393633958912)), (nat_lit 2014, Int.ofNat (nat_lit 447547332418560))]
theorem block017_data_flat016_step : block017_data_flat016 = (CoefficientMerge.fastMerge block017_data_flat012 block017_data_flat015) := by decide +kernel
theorem block017_data_flat016_original : block017_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (377844072902208 : Int) atom1176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (389393633958912 : Int) atom1177Coded) (CoefficientMerge.scale (447547332418560 : Int) atom1178Coded))) := by
  rw [block017_data_flat016_step, block017_data_flat012_original, block017_data_flat015_original]
def block017_data_flat017 : CoefficientMerge.Poly := [(nat_lit 2010, Int.ofNat (nat_lit 337360560787008)), (nat_lit 2011, Int.ofNat (nat_lit 304119222359040)), (nat_lit 2012, Int.ofNat (nat_lit 377844072902208)), (nat_lit 2013, Int.ofNat (nat_lit 389393633958912)), (nat_lit 2014, Int.ofNat (nat_lit 447547332418560))]
theorem block017_data_flat017_step : block017_data_flat017 = (CoefficientMerge.fastMerge block017_data_flat011 block017_data_flat016) := by decide +kernel
theorem block017_data_flat017_original : block017_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337360560787008 : Int) atom1174Coded) (CoefficientMerge.scale (304119222359040 : Int) atom1175Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377844072902208 : Int) atom1176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (389393633958912 : Int) atom1177Coded) (CoefficientMerge.scale (447547332418560 : Int) atom1178Coded)))) := by
  rw [block017_data_flat017_step, block017_data_flat011_original, block017_data_flat016_original]
def block017_data_flat018 : CoefficientMerge.Poly := [(nat_lit 2005, Int.ofNat (nat_lit 355486091647104)), (nat_lit 2006, Int.ofNat (nat_lit 329946779695104)), (nat_lit 2007, Int.ofNat (nat_lit 319194474338304)), (nat_lit 2008, Int.ofNat (nat_lit 299702699311104)), (nat_lit 2009, Int.ofNat (nat_lit 290143662741504)), (nat_lit 2010, Int.ofNat (nat_lit 337360560787008)), (nat_lit 2011, Int.ofNat (nat_lit 304119222359040)), (nat_lit 2012, Int.ofNat (nat_lit 377844072902208)), (nat_lit 2013, Int.ofNat (nat_lit 389393633958912)), (nat_lit 2014, Int.ofNat (nat_lit 447547332418560))]
theorem block017_data_flat018_step : block017_data_flat018 = (CoefficientMerge.fastMerge block017_data_flat008 block017_data_flat017) := by decide +kernel
theorem block017_data_flat018_original : block017_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (355486091647104 : Int) atom1169Coded) (CoefficientMerge.scale (329946779695104 : Int) atom1170Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (319194474338304 : Int) atom1171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299702699311104 : Int) atom1172Coded) (CoefficientMerge.scale (290143662741504 : Int) atom1173Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337360560787008 : Int) atom1174Coded) (CoefficientMerge.scale (304119222359040 : Int) atom1175Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377844072902208 : Int) atom1176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (389393633958912 : Int) atom1177Coded) (CoefficientMerge.scale (447547332418560 : Int) atom1178Coded))))) := by
  rw [block017_data_flat018_step, block017_data_flat008_original, block017_data_flat017_original]
def block017_data_flat019 : CoefficientMerge.Poly := [(nat_lit 2015, Int.ofNat (nat_lit 505701030878208))]
theorem block017_data_flat019_step : block017_data_flat019 = (CoefficientMerge.scale (505701030878208 : Int) atom1179Coded) := by decide +kernel
theorem block017_data_flat019_original : block017_data_flat019 = (CoefficientMerge.scale (505701030878208 : Int) atom1179Coded) := by
  rw [block017_data_flat019_step]
def block017_data_flat020 : CoefficientMerge.Poly := [(nat_lit 2028, Int.ofNat (nat_lit 230328777469824))]
theorem block017_data_flat020_step : block017_data_flat020 = (CoefficientMerge.scale (230328777469824 : Int) atom1180Coded) := by decide +kernel
theorem block017_data_flat020_original : block017_data_flat020 = (CoefficientMerge.scale (230328777469824 : Int) atom1180Coded) := by
  rw [block017_data_flat020_step]
def block017_data_flat021 : CoefficientMerge.Poly := [(nat_lit 2015, Int.ofNat (nat_lit 505701030878208)), (nat_lit 2028, Int.ofNat (nat_lit 230328777469824))]
theorem block017_data_flat021_step : block017_data_flat021 = (CoefficientMerge.fastMerge block017_data_flat019 block017_data_flat020) := by decide +kernel
theorem block017_data_flat021_original : block017_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (505701030878208 : Int) atom1179Coded) (CoefficientMerge.scale (230328777469824 : Int) atom1180Coded)) := by
  rw [block017_data_flat021_step, block017_data_flat019_original, block017_data_flat020_original]
def block017_data_flat022 : CoefficientMerge.Poly := [(nat_lit 2029, Int.ofNat (nat_lit 424979952465024))]
theorem block017_data_flat022_step : block017_data_flat022 = (CoefficientMerge.scale (424979952465024 : Int) atom1181Coded) := by decide +kernel
theorem block017_data_flat022_original : block017_data_flat022 = (CoefficientMerge.scale (424979952465024 : Int) atom1181Coded) := by
  rw [block017_data_flat022_step]
def block017_data_flat023 : CoefficientMerge.Poly := [(nat_lit 2030, Int.ofNat (nat_lit 397441979725824))]
theorem block017_data_flat023_step : block017_data_flat023 = (CoefficientMerge.scale (397441979725824 : Int) atom1182Coded) := by decide +kernel
theorem block017_data_flat023_original : block017_data_flat023 = (CoefficientMerge.scale (397441979725824 : Int) atom1182Coded) := by
  rw [block017_data_flat023_step]
def block017_data_flat024 : CoefficientMerge.Poly := [(nat_lit 2031, Int.ofNat (nat_lit 384691013581824))]
theorem block017_data_flat024_step : block017_data_flat024 = (CoefficientMerge.scale (384691013581824 : Int) atom1183Coded) := by decide +kernel
theorem block017_data_flat024_original : block017_data_flat024 = (CoefficientMerge.scale (384691013581824 : Int) atom1183Coded) := by
  rw [block017_data_flat024_step]
def block017_data_flat025 : CoefficientMerge.Poly := [(nat_lit 2030, Int.ofNat (nat_lit 397441979725824)), (nat_lit 2031, Int.ofNat (nat_lit 384691013581824))]
theorem block017_data_flat025_step : block017_data_flat025 = (CoefficientMerge.fastMerge block017_data_flat023 block017_data_flat024) := by decide +kernel
theorem block017_data_flat025_original : block017_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (397441979725824 : Int) atom1182Coded) (CoefficientMerge.scale (384691013581824 : Int) atom1183Coded)) := by
  rw [block017_data_flat025_step, block017_data_flat023_original, block017_data_flat024_original]
def block017_data_flat026 : CoefficientMerge.Poly := [(nat_lit 2029, Int.ofNat (nat_lit 424979952465024)), (nat_lit 2030, Int.ofNat (nat_lit 397441979725824)), (nat_lit 2031, Int.ofNat (nat_lit 384691013581824))]
theorem block017_data_flat026_step : block017_data_flat026 = (CoefficientMerge.fastMerge block017_data_flat022 block017_data_flat025) := by decide +kernel
theorem block017_data_flat026_original : block017_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (424979952465024 : Int) atom1181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (397441979725824 : Int) atom1182Coded) (CoefficientMerge.scale (384691013581824 : Int) atom1183Coded))) := by
  rw [block017_data_flat026_step, block017_data_flat022_original, block017_data_flat025_original]
def block017_data_flat027 : CoefficientMerge.Poly := [(nat_lit 2015, Int.ofNat (nat_lit 505701030878208)), (nat_lit 2028, Int.ofNat (nat_lit 230328777469824)), (nat_lit 2029, Int.ofNat (nat_lit 424979952465024)), (nat_lit 2030, Int.ofNat (nat_lit 397441979725824)), (nat_lit 2031, Int.ofNat (nat_lit 384691013581824))]
theorem block017_data_flat027_step : block017_data_flat027 = (CoefficientMerge.fastMerge block017_data_flat021 block017_data_flat026) := by decide +kernel
theorem block017_data_flat027_original : block017_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (505701030878208 : Int) atom1179Coded) (CoefficientMerge.scale (230328777469824 : Int) atom1180Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (424979952465024 : Int) atom1181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (397441979725824 : Int) atom1182Coded) (CoefficientMerge.scale (384691013581824 : Int) atom1183Coded)))) := by
  rw [block017_data_flat027_step, block017_data_flat021_original, block017_data_flat026_original]
def block017_data_flat028 : CoefficientMerge.Poly := [(nat_lit 2032, Int.ofNat (nat_lit 360117537191424))]
theorem block017_data_flat028_step : block017_data_flat028 = (CoefficientMerge.scale (360117537191424 : Int) atom1184Coded) := by decide +kernel
theorem block017_data_flat028_original : block017_data_flat028 = (CoefficientMerge.scale (360117537191424 : Int) atom1184Coded) := by
  rw [block017_data_flat028_step]
def block017_data_flat029 : CoefficientMerge.Poly := [(nat_lit 2033, Int.ofNat (nat_lit 345476799258624))]
theorem block017_data_flat029_step : block017_data_flat029 = (CoefficientMerge.scale (345476799258624 : Int) atom1185Coded) := by decide +kernel
theorem block017_data_flat029_original : block017_data_flat029 = (CoefficientMerge.scale (345476799258624 : Int) atom1185Coded) := by
  rw [block017_data_flat029_step]
def block017_data_flat030 : CoefficientMerge.Poly := [(nat_lit 2032, Int.ofNat (nat_lit 360117537191424)), (nat_lit 2033, Int.ofNat (nat_lit 345476799258624))]
theorem block017_data_flat030_step : block017_data_flat030 = (CoefficientMerge.fastMerge block017_data_flat028 block017_data_flat029) := by decide +kernel
theorem block017_data_flat030_original : block017_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (360117537191424 : Int) atom1184Coded) (CoefficientMerge.scale (345476799258624 : Int) atom1185Coded)) := by
  rw [block017_data_flat030_step, block017_data_flat028_original, block017_data_flat029_original]
def block017_data_flat031 : CoefficientMerge.Poly := [(nat_lit 2034, Int.ofNat (nat_lit 413276182501248))]
theorem block017_data_flat031_step : block017_data_flat031 = (CoefficientMerge.scale (413276182501248 : Int) atom1186Coded) := by decide +kernel
theorem block017_data_flat031_original : block017_data_flat031 = (CoefficientMerge.scale (413276182501248 : Int) atom1186Coded) := by
  rw [block017_data_flat031_step]
def block017_data_flat032 : CoefficientMerge.Poly := [(nat_lit 2035, Int.ofNat (nat_lit 340052591831040))]
theorem block017_data_flat032_step : block017_data_flat032 = (CoefficientMerge.scale (340052591831040 : Int) atom1187Coded) := by decide +kernel
theorem block017_data_flat032_original : block017_data_flat032 = (CoefficientMerge.scale (340052591831040 : Int) atom1187Coded) := by
  rw [block017_data_flat032_step]
def block017_data_flat033 : CoefficientMerge.Poly := [(nat_lit 2036, Int.ofNat (nat_lit 461924436555648))]
theorem block017_data_flat033_step : block017_data_flat033 = (CoefficientMerge.scale (461924436555648 : Int) atom1188Coded) := by decide +kernel
theorem block017_data_flat033_original : block017_data_flat033 = (CoefficientMerge.scale (461924436555648 : Int) atom1188Coded) := by
  rw [block017_data_flat033_step]
def block017_data_flat034 : CoefficientMerge.Poly := [(nat_lit 2035, Int.ofNat (nat_lit 340052591831040)), (nat_lit 2036, Int.ofNat (nat_lit 461924436555648))]
theorem block017_data_flat034_step : block017_data_flat034 = (CoefficientMerge.fastMerge block017_data_flat032 block017_data_flat033) := by decide +kernel
theorem block017_data_flat034_original : block017_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (340052591831040 : Int) atom1187Coded) (CoefficientMerge.scale (461924436555648 : Int) atom1188Coded)) := by
  rw [block017_data_flat034_step, block017_data_flat032_original, block017_data_flat033_original]
def block017_data_flat035 : CoefficientMerge.Poly := [(nat_lit 2034, Int.ofNat (nat_lit 413276182501248)), (nat_lit 2035, Int.ofNat (nat_lit 340052591831040)), (nat_lit 2036, Int.ofNat (nat_lit 461924436555648))]
theorem block017_data_flat035_step : block017_data_flat035 = (CoefficientMerge.fastMerge block017_data_flat031 block017_data_flat034) := by decide +kernel
theorem block017_data_flat035_original : block017_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (413276182501248 : Int) atom1186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (340052591831040 : Int) atom1187Coded) (CoefficientMerge.scale (461924436555648 : Int) atom1188Coded))) := by
  rw [block017_data_flat035_step, block017_data_flat031_original, block017_data_flat034_original]
def block017_data_flat036 : CoefficientMerge.Poly := [(nat_lit 2032, Int.ofNat (nat_lit 360117537191424)), (nat_lit 2033, Int.ofNat (nat_lit 345476799258624)), (nat_lit 2034, Int.ofNat (nat_lit 413276182501248)), (nat_lit 2035, Int.ofNat (nat_lit 340052591831040)), (nat_lit 2036, Int.ofNat (nat_lit 461924436555648))]
theorem block017_data_flat036_step : block017_data_flat036 = (CoefficientMerge.fastMerge block017_data_flat030 block017_data_flat035) := by decide +kernel
theorem block017_data_flat036_original : block017_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (360117537191424 : Int) atom1184Coded) (CoefficientMerge.scale (345476799258624 : Int) atom1185Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413276182501248 : Int) atom1186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (340052591831040 : Int) atom1187Coded) (CoefficientMerge.scale (461924436555648 : Int) atom1188Coded)))) := by
  rw [block017_data_flat036_step, block017_data_flat030_original, block017_data_flat035_original]
def block017_data_flat037 : CoefficientMerge.Poly := [(nat_lit 2015, Int.ofNat (nat_lit 505701030878208)), (nat_lit 2028, Int.ofNat (nat_lit 230328777469824)), (nat_lit 2029, Int.ofNat (nat_lit 424979952465024)), (nat_lit 2030, Int.ofNat (nat_lit 397441979725824)), (nat_lit 2031, Int.ofNat (nat_lit 384691013581824)), (nat_lit 2032, Int.ofNat (nat_lit 360117537191424)), (nat_lit 2033, Int.ofNat (nat_lit 345476799258624)), (nat_lit 2034, Int.ofNat (nat_lit 413276182501248)), (nat_lit 2035, Int.ofNat (nat_lit 340052591831040)), (nat_lit 2036, Int.ofNat (nat_lit 461924436555648))]
theorem block017_data_flat037_step : block017_data_flat037 = (CoefficientMerge.fastMerge block017_data_flat027 block017_data_flat036) := by decide +kernel
theorem block017_data_flat037_original : block017_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (505701030878208 : Int) atom1179Coded) (CoefficientMerge.scale (230328777469824 : Int) atom1180Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (424979952465024 : Int) atom1181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (397441979725824 : Int) atom1182Coded) (CoefficientMerge.scale (384691013581824 : Int) atom1183Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (360117537191424 : Int) atom1184Coded) (CoefficientMerge.scale (345476799258624 : Int) atom1185Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413276182501248 : Int) atom1186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (340052591831040 : Int) atom1187Coded) (CoefficientMerge.scale (461924436555648 : Int) atom1188Coded))))) := by
  rw [block017_data_flat037_step, block017_data_flat027_original, block017_data_flat036_original]
def block017_data_flat038 : CoefficientMerge.Poly := [(nat_lit 2005, Int.ofNat (nat_lit 355486091647104)), (nat_lit 2006, Int.ofNat (nat_lit 329946779695104)), (nat_lit 2007, Int.ofNat (nat_lit 319194474338304)), (nat_lit 2008, Int.ofNat (nat_lit 299702699311104)), (nat_lit 2009, Int.ofNat (nat_lit 290143662741504)), (nat_lit 2010, Int.ofNat (nat_lit 337360560787008)), (nat_lit 2011, Int.ofNat (nat_lit 304119222359040)), (nat_lit 2012, Int.ofNat (nat_lit 377844072902208)), (nat_lit 2013, Int.ofNat (nat_lit 389393633958912)), (nat_lit 2014, Int.ofNat (nat_lit 447547332418560)), (nat_lit 2015, Int.ofNat (nat_lit 505701030878208)), (nat_lit 2028, Int.ofNat (nat_lit 230328777469824)), (nat_lit 2029, Int.ofNat (nat_lit 424979952465024)), (nat_lit 2030, Int.ofNat (nat_lit 397441979725824)), (nat_lit 2031, Int.ofNat (nat_lit 384691013581824)), (nat_lit 2032, Int.ofNat (nat_lit 360117537191424)), (nat_lit 2033, Int.ofNat (nat_lit 345476799258624)), (nat_lit 2034, Int.ofNat (nat_lit 413276182501248)), (nat_lit 2035, Int.ofNat (nat_lit 340052591831040)), (nat_lit 2036, Int.ofNat (nat_lit 461924436555648))]
theorem block017_data_flat038_step : block017_data_flat038 = (CoefficientMerge.fastMerge block017_data_flat018 block017_data_flat037) := by decide +kernel
theorem block017_data_flat038_original : block017_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (355486091647104 : Int) atom1169Coded) (CoefficientMerge.scale (329946779695104 : Int) atom1170Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (319194474338304 : Int) atom1171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299702699311104 : Int) atom1172Coded) (CoefficientMerge.scale (290143662741504 : Int) atom1173Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337360560787008 : Int) atom1174Coded) (CoefficientMerge.scale (304119222359040 : Int) atom1175Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377844072902208 : Int) atom1176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (389393633958912 : Int) atom1177Coded) (CoefficientMerge.scale (447547332418560 : Int) atom1178Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (505701030878208 : Int) atom1179Coded) (CoefficientMerge.scale (230328777469824 : Int) atom1180Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (424979952465024 : Int) atom1181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (397441979725824 : Int) atom1182Coded) (CoefficientMerge.scale (384691013581824 : Int) atom1183Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (360117537191424 : Int) atom1184Coded) (CoefficientMerge.scale (345476799258624 : Int) atom1185Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413276182501248 : Int) atom1186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (340052591831040 : Int) atom1187Coded) (CoefficientMerge.scale (461924436555648 : Int) atom1188Coded)))))) := by
  rw [block017_data_flat038_step, block017_data_flat018_original, block017_data_flat037_original]
def block017_data_flat039 : CoefficientMerge.Poly := [(nat_lit 2037, Int.ofNat (nat_lit 396690872067072))]
theorem block017_data_flat039_step : block017_data_flat039 = (CoefficientMerge.scale (396690872067072 : Int) atom1189Coded) := by decide +kernel
theorem block017_data_flat039_original : block017_data_flat039 = (CoefficientMerge.scale (396690872067072 : Int) atom1189Coded) := by
  rw [block017_data_flat039_step]
def block017_data_flat040 : CoefficientMerge.Poly := [(nat_lit 2038, Int.ofNat (nat_lit 437447716738560))]
theorem block017_data_flat040_step : block017_data_flat040 = (CoefficientMerge.scale (437447716738560 : Int) atom1190Coded) := by decide +kernel
theorem block017_data_flat040_original : block017_data_flat040 = (CoefficientMerge.scale (437447716738560 : Int) atom1190Coded) := by
  rw [block017_data_flat040_step]
def block017_data_flat041 : CoefficientMerge.Poly := [(nat_lit 2037, Int.ofNat (nat_lit 396690872067072)), (nat_lit 2038, Int.ofNat (nat_lit 437447716738560))]
theorem block017_data_flat041_step : block017_data_flat041 = (CoefficientMerge.fastMerge block017_data_flat039 block017_data_flat040) := by decide +kernel
theorem block017_data_flat041_original : block017_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (396690872067072 : Int) atom1189Coded) (CoefficientMerge.scale (437447716738560 : Int) atom1190Coded)) := by
  rw [block017_data_flat041_step, block017_data_flat039_original, block017_data_flat040_original]
def block017_data_flat042 : CoefficientMerge.Poly := [(nat_lit 2039, Int.ofNat (nat_lit 478204561410048))]
theorem block017_data_flat042_step : block017_data_flat042 = (CoefficientMerge.scale (478204561410048 : Int) atom1191Coded) := by decide +kernel
theorem block017_data_flat042_original : block017_data_flat042 = (CoefficientMerge.scale (478204561410048 : Int) atom1191Coded) := by
  rw [block017_data_flat042_step]
def block017_data_flat043 : CoefficientMerge.Poly := [(nat_lit 2053, Int.ofNat (nat_lit 238834335801600))]
theorem block017_data_flat043_step : block017_data_flat043 = (CoefficientMerge.scale (238834335801600 : Int) atom1192Coded) := by decide +kernel
theorem block017_data_flat043_original : block017_data_flat043 = (CoefficientMerge.scale (238834335801600 : Int) atom1192Coded) := by
  rw [block017_data_flat043_step]
def block017_data_flat044 : CoefficientMerge.Poly := [(nat_lit 2054, Int.ofNat (nat_lit 431701558041600))]
theorem block017_data_flat044_step : block017_data_flat044 = (CoefficientMerge.scale (431701558041600 : Int) atom1193Coded) := by decide +kernel
theorem block017_data_flat044_original : block017_data_flat044 = (CoefficientMerge.scale (431701558041600 : Int) atom1193Coded) := by
  rw [block017_data_flat044_step]
def block017_data_flat045 : CoefficientMerge.Poly := [(nat_lit 2053, Int.ofNat (nat_lit 238834335801600)), (nat_lit 2054, Int.ofNat (nat_lit 431701558041600))]
theorem block017_data_flat045_step : block017_data_flat045 = (CoefficientMerge.fastMerge block017_data_flat043 block017_data_flat044) := by decide +kernel
theorem block017_data_flat045_original : block017_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (238834335801600 : Int) atom1192Coded) (CoefficientMerge.scale (431701558041600 : Int) atom1193Coded)) := by
  rw [block017_data_flat045_step, block017_data_flat043_original, block017_data_flat044_original]
def block017_data_flat046 : CoefficientMerge.Poly := [(nat_lit 2039, Int.ofNat (nat_lit 478204561410048)), (nat_lit 2053, Int.ofNat (nat_lit 238834335801600)), (nat_lit 2054, Int.ofNat (nat_lit 431701558041600))]
theorem block017_data_flat046_step : block017_data_flat046 = (CoefficientMerge.fastMerge block017_data_flat042 block017_data_flat045) := by decide +kernel
theorem block017_data_flat046_original : block017_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (478204561410048 : Int) atom1191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (238834335801600 : Int) atom1192Coded) (CoefficientMerge.scale (431701558041600 : Int) atom1193Coded))) := by
  rw [block017_data_flat046_step, block017_data_flat042_original, block017_data_flat045_original]
def block017_data_flat047 : CoefficientMerge.Poly := [(nat_lit 2037, Int.ofNat (nat_lit 396690872067072)), (nat_lit 2038, Int.ofNat (nat_lit 437447716738560)), (nat_lit 2039, Int.ofNat (nat_lit 478204561410048)), (nat_lit 2053, Int.ofNat (nat_lit 238834335801600)), (nat_lit 2054, Int.ofNat (nat_lit 431701558041600))]
theorem block017_data_flat047_step : block017_data_flat047 = (CoefficientMerge.fastMerge block017_data_flat041 block017_data_flat046) := by decide +kernel
theorem block017_data_flat047_original : block017_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (396690872067072 : Int) atom1189Coded) (CoefficientMerge.scale (437447716738560 : Int) atom1190Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (478204561410048 : Int) atom1191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (238834335801600 : Int) atom1192Coded) (CoefficientMerge.scale (431701558041600 : Int) atom1193Coded)))) := by
  rw [block017_data_flat047_step, block017_data_flat041_original, block017_data_flat046_original]
def block017_data_flat048 : CoefficientMerge.Poly := [(nat_lit 2055, Int.ofNat (nat_lit 409765257216000))]
theorem block017_data_flat048_step : block017_data_flat048 = (CoefficientMerge.scale (409765257216000 : Int) atom1194Coded) := by decide +kernel
theorem block017_data_flat048_original : block017_data_flat048 = (CoefficientMerge.scale (409765257216000 : Int) atom1194Coded) := by
  rw [block017_data_flat048_step]
def block017_data_flat049 : CoefficientMerge.Poly := [(nat_lit 2056, Int.ofNat (nat_lit 379089486720000))]
theorem block017_data_flat049_step : block017_data_flat049 = (CoefficientMerge.scale (379089486720000 : Int) atom1195Coded) := by decide +kernel
theorem block017_data_flat049_original : block017_data_flat049 = (CoefficientMerge.scale (379089486720000 : Int) atom1195Coded) := by
  rw [block017_data_flat049_step]
def block017_data_flat050 : CoefficientMerge.Poly := [(nat_lit 2055, Int.ofNat (nat_lit 409765257216000)), (nat_lit 2056, Int.ofNat (nat_lit 379089486720000))]
theorem block017_data_flat050_step : block017_data_flat050 = (CoefficientMerge.fastMerge block017_data_flat048 block017_data_flat049) := by decide +kernel
theorem block017_data_flat050_original : block017_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (409765257216000 : Int) atom1194Coded) (CoefficientMerge.scale (379089486720000 : Int) atom1195Coded)) := by
  rw [block017_data_flat050_step, block017_data_flat048_original, block017_data_flat049_original]
def block017_data_flat051 : CoefficientMerge.Poly := [(nat_lit 2057, Int.ofNat (nat_lit 358346454681600))]
theorem block017_data_flat051_step : block017_data_flat051 = (CoefficientMerge.scale (358346454681600 : Int) atom1196Coded) := by decide +kernel
theorem block017_data_flat051_original : block017_data_flat051 = (CoefficientMerge.scale (358346454681600 : Int) atom1196Coded) := by
  rw [block017_data_flat051_step]
def block017_data_flat052 : CoefficientMerge.Poly := [(nat_lit 2058, Int.ofNat (nat_lit 416025578707200))]
theorem block017_data_flat052_step : block017_data_flat052 = (CoefficientMerge.scale (416025578707200 : Int) atom1197Coded) := by decide +kernel
theorem block017_data_flat052_original : block017_data_flat052 = (CoefficientMerge.scale (416025578707200 : Int) atom1197Coded) := by
  rw [block017_data_flat052_step]
def block017_data_flat053 : CoefficientMerge.Poly := [(nat_lit 2059, Int.ofNat (nat_lit 345906104544000))]
theorem block017_data_flat053_step : block017_data_flat053 = (CoefficientMerge.scale (345906104544000 : Int) atom1198Coded) := by decide +kernel
theorem block017_data_flat053_original : block017_data_flat053 = (CoefficientMerge.scale (345906104544000 : Int) atom1198Coded) := by
  rw [block017_data_flat053_step]
def block017_data_flat054 : CoefficientMerge.Poly := [(nat_lit 2058, Int.ofNat (nat_lit 416025578707200)), (nat_lit 2059, Int.ofNat (nat_lit 345906104544000))]
theorem block017_data_flat054_step : block017_data_flat054 = (CoefficientMerge.fastMerge block017_data_flat052 block017_data_flat053) := by decide +kernel
theorem block017_data_flat054_original : block017_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (416025578707200 : Int) atom1197Coded) (CoefficientMerge.scale (345906104544000 : Int) atom1198Coded)) := by
  rw [block017_data_flat054_step, block017_data_flat052_original, block017_data_flat053_original]
def block017_data_flat055 : CoefficientMerge.Poly := [(nat_lit 2057, Int.ofNat (nat_lit 358346454681600)), (nat_lit 2058, Int.ofNat (nat_lit 416025578707200)), (nat_lit 2059, Int.ofNat (nat_lit 345906104544000))]
theorem block017_data_flat055_step : block017_data_flat055 = (CoefficientMerge.fastMerge block017_data_flat051 block017_data_flat054) := by decide +kernel
theorem block017_data_flat055_original : block017_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (358346454681600 : Int) atom1196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416025578707200 : Int) atom1197Coded) (CoefficientMerge.scale (345906104544000 : Int) atom1198Coded))) := by
  rw [block017_data_flat055_step, block017_data_flat051_original, block017_data_flat054_original]
def block017_data_flat056 : CoefficientMerge.Poly := [(nat_lit 2055, Int.ofNat (nat_lit 409765257216000)), (nat_lit 2056, Int.ofNat (nat_lit 379089486720000)), (nat_lit 2057, Int.ofNat (nat_lit 358346454681600)), (nat_lit 2058, Int.ofNat (nat_lit 416025578707200)), (nat_lit 2059, Int.ofNat (nat_lit 345906104544000))]
theorem block017_data_flat056_step : block017_data_flat056 = (CoefficientMerge.fastMerge block017_data_flat050 block017_data_flat055) := by decide +kernel
theorem block017_data_flat056_original : block017_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (409765257216000 : Int) atom1194Coded) (CoefficientMerge.scale (379089486720000 : Int) atom1195Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358346454681600 : Int) atom1196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416025578707200 : Int) atom1197Coded) (CoefficientMerge.scale (345906104544000 : Int) atom1198Coded)))) := by
  rw [block017_data_flat056_step, block017_data_flat050_original, block017_data_flat055_original]
def block017_data_flat057 : CoefficientMerge.Poly := [(nat_lit 2037, Int.ofNat (nat_lit 396690872067072)), (nat_lit 2038, Int.ofNat (nat_lit 437447716738560)), (nat_lit 2039, Int.ofNat (nat_lit 478204561410048)), (nat_lit 2053, Int.ofNat (nat_lit 238834335801600)), (nat_lit 2054, Int.ofNat (nat_lit 431701558041600)), (nat_lit 2055, Int.ofNat (nat_lit 409765257216000)), (nat_lit 2056, Int.ofNat (nat_lit 379089486720000)), (nat_lit 2057, Int.ofNat (nat_lit 358346454681600)), (nat_lit 2058, Int.ofNat (nat_lit 416025578707200)), (nat_lit 2059, Int.ofNat (nat_lit 345906104544000))]
theorem block017_data_flat057_step : block017_data_flat057 = (CoefficientMerge.fastMerge block017_data_flat047 block017_data_flat056) := by decide +kernel
theorem block017_data_flat057_original : block017_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (396690872067072 : Int) atom1189Coded) (CoefficientMerge.scale (437447716738560 : Int) atom1190Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (478204561410048 : Int) atom1191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (238834335801600 : Int) atom1192Coded) (CoefficientMerge.scale (431701558041600 : Int) atom1193Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (409765257216000 : Int) atom1194Coded) (CoefficientMerge.scale (379089486720000 : Int) atom1195Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358346454681600 : Int) atom1196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416025578707200 : Int) atom1197Coded) (CoefficientMerge.scale (345906104544000 : Int) atom1198Coded))))) := by
  rw [block017_data_flat057_step, block017_data_flat047_original, block017_data_flat056_original]
def block017_data_flat058 : CoefficientMerge.Poly := [(nat_lit 2060, Int.ofNat (nat_lit 472838574700800))]
theorem block017_data_flat058_step : block017_data_flat058 = (CoefficientMerge.scale (472838574700800 : Int) atom1199Coded) := by decide +kernel
theorem block017_data_flat058_original : block017_data_flat058 = (CoefficientMerge.scale (472838574700800 : Int) atom1199Coded) := by
  rw [block017_data_flat058_step]
def block017_data_flat059 : CoefficientMerge.Poly := [(nat_lit 2061, Int.ofNat (nat_lit 400716687571200))]
theorem block017_data_flat059_step : block017_data_flat059 = (CoefficientMerge.scale (400716687571200 : Int) atom1200Coded) := by decide +kernel
theorem block017_data_flat059_original : block017_data_flat059 = (CoefficientMerge.scale (400716687571200 : Int) atom1200Coded) := by
  rw [block017_data_flat059_step]
def block017_data_flat060 : CoefficientMerge.Poly := [(nat_lit 2060, Int.ofNat (nat_lit 472838574700800)), (nat_lit 2061, Int.ofNat (nat_lit 400716687571200))]
theorem block017_data_flat060_step : block017_data_flat060 = (CoefficientMerge.fastMerge block017_data_flat058 block017_data_flat059) := by decide +kernel
theorem block017_data_flat060_original : block017_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (472838574700800 : Int) atom1199Coded) (CoefficientMerge.scale (400716687571200 : Int) atom1200Coded)) := by
  rw [block017_data_flat060_step, block017_data_flat058_original, block017_data_flat059_original]
def block017_data_flat061 : CoefficientMerge.Poly := [(nat_lit 2062, Int.ofNat (nat_lit 442289165472000))]
theorem block017_data_flat061_step : block017_data_flat061 = (CoefficientMerge.scale (442289165472000 : Int) atom1201Coded) := by decide +kernel
theorem block017_data_flat061_original : block017_data_flat061 = (CoefficientMerge.scale (442289165472000 : Int) atom1201Coded) := by
  rw [block017_data_flat061_step]
def block017_data_flat062 : CoefficientMerge.Poly := [(nat_lit 2063, Int.ofNat (nat_lit 483861643372800))]
theorem block017_data_flat062_step : block017_data_flat062 = (CoefficientMerge.scale (483861643372800 : Int) atom1202Coded) := by decide +kernel
theorem block017_data_flat062_original : block017_data_flat062 = (CoefficientMerge.scale (483861643372800 : Int) atom1202Coded) := by
  rw [block017_data_flat062_step]
def block017_data_flat063 : CoefficientMerge.Poly := [(nat_lit 2078, Int.ofNat (nat_lit 237050383046400))]
theorem block017_data_flat063_step : block017_data_flat063 = (CoefficientMerge.scale (237050383046400 : Int) atom1203Coded) := by decide +kernel
theorem block017_data_flat063_original : block017_data_flat063 = (CoefficientMerge.scale (237050383046400 : Int) atom1203Coded) := by
  rw [block017_data_flat063_step]
def block017_data_flat064 : CoefficientMerge.Poly := [(nat_lit 2063, Int.ofNat (nat_lit 483861643372800)), (nat_lit 2078, Int.ofNat (nat_lit 237050383046400))]
theorem block017_data_flat064_step : block017_data_flat064 = (CoefficientMerge.fastMerge block017_data_flat062 block017_data_flat063) := by decide +kernel
theorem block017_data_flat064_original : block017_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (483861643372800 : Int) atom1202Coded) (CoefficientMerge.scale (237050383046400 : Int) atom1203Coded)) := by
  rw [block017_data_flat064_step, block017_data_flat062_original, block017_data_flat063_original]
def block017_data_flat065 : CoefficientMerge.Poly := [(nat_lit 2062, Int.ofNat (nat_lit 442289165472000)), (nat_lit 2063, Int.ofNat (nat_lit 483861643372800)), (nat_lit 2078, Int.ofNat (nat_lit 237050383046400))]
theorem block017_data_flat065_step : block017_data_flat065 = (CoefficientMerge.fastMerge block017_data_flat061 block017_data_flat064) := by decide +kernel
theorem block017_data_flat065_original : block017_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (442289165472000 : Int) atom1201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (483861643372800 : Int) atom1202Coded) (CoefficientMerge.scale (237050383046400 : Int) atom1203Coded))) := by
  rw [block017_data_flat065_step, block017_data_flat061_original, block017_data_flat064_original]
def block017_data_flat066 : CoefficientMerge.Poly := [(nat_lit 2060, Int.ofNat (nat_lit 472838574700800)), (nat_lit 2061, Int.ofNat (nat_lit 400716687571200)), (nat_lit 2062, Int.ofNat (nat_lit 442289165472000)), (nat_lit 2063, Int.ofNat (nat_lit 483861643372800)), (nat_lit 2078, Int.ofNat (nat_lit 237050383046400))]
theorem block017_data_flat066_step : block017_data_flat066 = (CoefficientMerge.fastMerge block017_data_flat060 block017_data_flat065) := by decide +kernel
theorem block017_data_flat066_original : block017_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (472838574700800 : Int) atom1199Coded) (CoefficientMerge.scale (400716687571200 : Int) atom1200Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (442289165472000 : Int) atom1201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (483861643372800 : Int) atom1202Coded) (CoefficientMerge.scale (237050383046400 : Int) atom1203Coded)))) := by
  rw [block017_data_flat066_step, block017_data_flat060_original, block017_data_flat065_original]
def block017_data_flat067 : CoefficientMerge.Poly := [(nat_lit 2079, Int.ofNat (nat_lit 439906721184000))]
theorem block017_data_flat067_step : block017_data_flat067 = (CoefficientMerge.scale (439906721184000 : Int) atom1204Coded) := by decide +kernel
theorem block017_data_flat067_original : block017_data_flat067 = (CoefficientMerge.scale (439906721184000 : Int) atom1204Coded) := by
  rw [block017_data_flat067_step]
def block017_data_flat068 : CoefficientMerge.Poly := [(nat_lit 2080, Int.ofNat (nat_lit 402108063840000))]
theorem block017_data_flat068_step : block017_data_flat068 = (CoefficientMerge.scale (402108063840000 : Int) atom1205Coded) := by decide +kernel
theorem block017_data_flat068_original : block017_data_flat068 = (CoefficientMerge.scale (402108063840000 : Int) atom1205Coded) := by
  rw [block017_data_flat068_step]
def block017_data_flat069 : CoefficientMerge.Poly := [(nat_lit 2079, Int.ofNat (nat_lit 439906721184000)), (nat_lit 2080, Int.ofNat (nat_lit 402108063840000))]
theorem block017_data_flat069_step : block017_data_flat069 = (CoefficientMerge.fastMerge block017_data_flat067 block017_data_flat068) := by decide +kernel
theorem block017_data_flat069_original : block017_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (439906721184000 : Int) atom1204Coded) (CoefficientMerge.scale (402108063840000 : Int) atom1205Coded)) := by
  rw [block017_data_flat069_step, block017_data_flat067_original, block017_data_flat068_original]
def block017_data_flat070 : CoefficientMerge.Poly := [(nat_lit 2081, Int.ofNat (nat_lit 374242144953600))]
theorem block017_data_flat070_step : block017_data_flat070 = (CoefficientMerge.scale (374242144953600 : Int) atom1206Coded) := by decide +kernel
theorem block017_data_flat070_original : block017_data_flat070 = (CoefficientMerge.scale (374242144953600 : Int) atom1206Coded) := by
  rw [block017_data_flat070_step]
def block017_data_flat071 : CoefficientMerge.Poly := [(nat_lit 2082, Int.ofNat (nat_lit 411426449280000))]
theorem block017_data_flat071_step : block017_data_flat071 = (CoefficientMerge.scale (411426449280000 : Int) atom1207Coded) := by decide +kernel
theorem block017_data_flat071_original : block017_data_flat071 = (CoefficientMerge.scale (411426449280000 : Int) atom1207Coded) := by
  rw [block017_data_flat071_step]
def block017_data_flat072 : CoefficientMerge.Poly := [(nat_lit 2083, Int.ofNat (nat_lit 350110707962400))]
theorem block017_data_flat072_step : block017_data_flat072 = (CoefficientMerge.scale (350110707962400 : Int) atom1208Coded) := by decide +kernel
theorem block017_data_flat072_original : block017_data_flat072 = (CoefficientMerge.scale (350110707962400 : Int) atom1208Coded) := by
  rw [block017_data_flat072_step]
def block017_data_flat073 : CoefficientMerge.Poly := [(nat_lit 2082, Int.ofNat (nat_lit 411426449280000)), (nat_lit 2083, Int.ofNat (nat_lit 350110707962400))]
theorem block017_data_flat073_step : block017_data_flat073 = (CoefficientMerge.fastMerge block017_data_flat071 block017_data_flat072) := by decide +kernel
theorem block017_data_flat073_original : block017_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (411426449280000 : Int) atom1207Coded) (CoefficientMerge.scale (350110707962400 : Int) atom1208Coded)) := by
  rw [block017_data_flat073_step, block017_data_flat071_original, block017_data_flat072_original]
def block017_data_flat074 : CoefficientMerge.Poly := [(nat_lit 2081, Int.ofNat (nat_lit 374242144953600)), (nat_lit 2082, Int.ofNat (nat_lit 411426449280000)), (nat_lit 2083, Int.ofNat (nat_lit 350110707962400))]
theorem block017_data_flat074_step : block017_data_flat074 = (CoefficientMerge.fastMerge block017_data_flat070 block017_data_flat073) := by decide +kernel
theorem block017_data_flat074_original : block017_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (374242144953600 : Int) atom1206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411426449280000 : Int) atom1207Coded) (CoefficientMerge.scale (350110707962400 : Int) atom1208Coded))) := by
  rw [block017_data_flat074_step, block017_data_flat070_original, block017_data_flat073_original]
def block017_data_flat075 : CoefficientMerge.Poly := [(nat_lit 2079, Int.ofNat (nat_lit 439906721184000)), (nat_lit 2080, Int.ofNat (nat_lit 402108063840000)), (nat_lit 2081, Int.ofNat (nat_lit 374242144953600)), (nat_lit 2082, Int.ofNat (nat_lit 411426449280000)), (nat_lit 2083, Int.ofNat (nat_lit 350110707962400))]
theorem block017_data_flat075_step : block017_data_flat075 = (CoefficientMerge.fastMerge block017_data_flat069 block017_data_flat074) := by decide +kernel
theorem block017_data_flat075_original : block017_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (439906721184000 : Int) atom1204Coded) (CoefficientMerge.scale (402108063840000 : Int) atom1205Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (374242144953600 : Int) atom1206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411426449280000 : Int) atom1207Coded) (CoefficientMerge.scale (350110707962400 : Int) atom1208Coded)))) := by
  rw [block017_data_flat075_step, block017_data_flat069_original, block017_data_flat074_original]
def block017_data_flat076 : CoefficientMerge.Poly := [(nat_lit 2060, Int.ofNat (nat_lit 472838574700800)), (nat_lit 2061, Int.ofNat (nat_lit 400716687571200)), (nat_lit 2062, Int.ofNat (nat_lit 442289165472000)), (nat_lit 2063, Int.ofNat (nat_lit 483861643372800)), (nat_lit 2078, Int.ofNat (nat_lit 237050383046400)), (nat_lit 2079, Int.ofNat (nat_lit 439906721184000)), (nat_lit 2080, Int.ofNat (nat_lit 402108063840000)), (nat_lit 2081, Int.ofNat (nat_lit 374242144953600)), (nat_lit 2082, Int.ofNat (nat_lit 411426449280000)), (nat_lit 2083, Int.ofNat (nat_lit 350110707962400))]
theorem block017_data_flat076_step : block017_data_flat076 = (CoefficientMerge.fastMerge block017_data_flat066 block017_data_flat075) := by decide +kernel
theorem block017_data_flat076_original : block017_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (472838574700800 : Int) atom1199Coded) (CoefficientMerge.scale (400716687571200 : Int) atom1200Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (442289165472000 : Int) atom1201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (483861643372800 : Int) atom1202Coded) (CoefficientMerge.scale (237050383046400 : Int) atom1203Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (439906721184000 : Int) atom1204Coded) (CoefficientMerge.scale (402108063840000 : Int) atom1205Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (374242144953600 : Int) atom1206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411426449280000 : Int) atom1207Coded) (CoefficientMerge.scale (350110707962400 : Int) atom1208Coded))))) := by
  rw [block017_data_flat076_step, block017_data_flat066_original, block017_data_flat075_original]
def block017_data_flat077 : CoefficientMerge.Poly := [(nat_lit 2037, Int.ofNat (nat_lit 396690872067072)), (nat_lit 2038, Int.ofNat (nat_lit 437447716738560)), (nat_lit 2039, Int.ofNat (nat_lit 478204561410048)), (nat_lit 2053, Int.ofNat (nat_lit 238834335801600)), (nat_lit 2054, Int.ofNat (nat_lit 431701558041600)), (nat_lit 2055, Int.ofNat (nat_lit 409765257216000)), (nat_lit 2056, Int.ofNat (nat_lit 379089486720000)), (nat_lit 2057, Int.ofNat (nat_lit 358346454681600)), (nat_lit 2058, Int.ofNat (nat_lit 416025578707200)), (nat_lit 2059, Int.ofNat (nat_lit 345906104544000)), (nat_lit 2060, Int.ofNat (nat_lit 472838574700800)), (nat_lit 2061, Int.ofNat (nat_lit 400716687571200)), (nat_lit 2062, Int.ofNat (nat_lit 442289165472000)), (nat_lit 2063, Int.ofNat (nat_lit 483861643372800)), (nat_lit 2078, Int.ofNat (nat_lit 237050383046400)), (nat_lit 2079, Int.ofNat (nat_lit 439906721184000)), (nat_lit 2080, Int.ofNat (nat_lit 402108063840000)), (nat_lit 2081, Int.ofNat (nat_lit 374242144953600)), (nat_lit 2082, Int.ofNat (nat_lit 411426449280000)), (nat_lit 2083, Int.ofNat (nat_lit 350110707962400))]
theorem block017_data_flat077_step : block017_data_flat077 = (CoefficientMerge.fastMerge block017_data_flat057 block017_data_flat076) := by decide +kernel
theorem block017_data_flat077_original : block017_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (396690872067072 : Int) atom1189Coded) (CoefficientMerge.scale (437447716738560 : Int) atom1190Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (478204561410048 : Int) atom1191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (238834335801600 : Int) atom1192Coded) (CoefficientMerge.scale (431701558041600 : Int) atom1193Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (409765257216000 : Int) atom1194Coded) (CoefficientMerge.scale (379089486720000 : Int) atom1195Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358346454681600 : Int) atom1196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416025578707200 : Int) atom1197Coded) (CoefficientMerge.scale (345906104544000 : Int) atom1198Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (472838574700800 : Int) atom1199Coded) (CoefficientMerge.scale (400716687571200 : Int) atom1200Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (442289165472000 : Int) atom1201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (483861643372800 : Int) atom1202Coded) (CoefficientMerge.scale (237050383046400 : Int) atom1203Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (439906721184000 : Int) atom1204Coded) (CoefficientMerge.scale (402108063840000 : Int) atom1205Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (374242144953600 : Int) atom1206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411426449280000 : Int) atom1207Coded) (CoefficientMerge.scale (350110707962400 : Int) atom1208Coded)))))) := by
  rw [block017_data_flat077_step, block017_data_flat057_original, block017_data_flat076_original]
def block017_data_flat078 : CoefficientMerge.Poly := [(nat_lit 2005, Int.ofNat (nat_lit 355486091647104)), (nat_lit 2006, Int.ofNat (nat_lit 329946779695104)), (nat_lit 2007, Int.ofNat (nat_lit 319194474338304)), (nat_lit 2008, Int.ofNat (nat_lit 299702699311104)), (nat_lit 2009, Int.ofNat (nat_lit 290143662741504)), (nat_lit 2010, Int.ofNat (nat_lit 337360560787008)), (nat_lit 2011, Int.ofNat (nat_lit 304119222359040)), (nat_lit 2012, Int.ofNat (nat_lit 377844072902208)), (nat_lit 2013, Int.ofNat (nat_lit 389393633958912)), (nat_lit 2014, Int.ofNat (nat_lit 447547332418560)), (nat_lit 2015, Int.ofNat (nat_lit 505701030878208)), (nat_lit 2028, Int.ofNat (nat_lit 230328777469824)), (nat_lit 2029, Int.ofNat (nat_lit 424979952465024)), (nat_lit 2030, Int.ofNat (nat_lit 397441979725824)), (nat_lit 2031, Int.ofNat (nat_lit 384691013581824)), (nat_lit 2032, Int.ofNat (nat_lit 360117537191424)), (nat_lit 2033, Int.ofNat (nat_lit 345476799258624)), (nat_lit 2034, Int.ofNat (nat_lit 413276182501248)), (nat_lit 2035, Int.ofNat (nat_lit 340052591831040)), (nat_lit 2036, Int.ofNat (nat_lit 461924436555648)), (nat_lit 2037, Int.ofNat (nat_lit 396690872067072)), (nat_lit 2038, Int.ofNat (nat_lit 437447716738560)), (nat_lit 2039, Int.ofNat (nat_lit 478204561410048)), (nat_lit 2053, Int.ofNat (nat_lit 238834335801600)), (nat_lit 2054, Int.ofNat (nat_lit 431701558041600)), (nat_lit 2055, Int.ofNat (nat_lit 409765257216000)), (nat_lit 2056, Int.ofNat (nat_lit 379089486720000)), (nat_lit 2057, Int.ofNat (nat_lit 358346454681600)), (nat_lit 2058, Int.ofNat (nat_lit 416025578707200)), (nat_lit 2059, Int.ofNat (nat_lit 345906104544000)), (nat_lit 2060, Int.ofNat (nat_lit 472838574700800)), (nat_lit 2061, Int.ofNat (nat_lit 400716687571200)), (nat_lit 2062, Int.ofNat (nat_lit 442289165472000)), (nat_lit 2063, Int.ofNat (nat_lit 483861643372800)), (nat_lit 2078, Int.ofNat (nat_lit 237050383046400)), (nat_lit 2079, Int.ofNat (nat_lit 439906721184000)), (nat_lit 2080, Int.ofNat (nat_lit 402108063840000)), (nat_lit 2081, Int.ofNat (nat_lit 374242144953600)), (nat_lit 2082, Int.ofNat (nat_lit 411426449280000)), (nat_lit 2083, Int.ofNat (nat_lit 350110707962400))]
theorem block017_data_flat078_step : block017_data_flat078 = (CoefficientMerge.fastMerge block017_data_flat038 block017_data_flat077) := by decide +kernel
theorem block017_data_flat078_original : block017_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (355486091647104 : Int) atom1169Coded) (CoefficientMerge.scale (329946779695104 : Int) atom1170Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (319194474338304 : Int) atom1171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299702699311104 : Int) atom1172Coded) (CoefficientMerge.scale (290143662741504 : Int) atom1173Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337360560787008 : Int) atom1174Coded) (CoefficientMerge.scale (304119222359040 : Int) atom1175Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377844072902208 : Int) atom1176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (389393633958912 : Int) atom1177Coded) (CoefficientMerge.scale (447547332418560 : Int) atom1178Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (505701030878208 : Int) atom1179Coded) (CoefficientMerge.scale (230328777469824 : Int) atom1180Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (424979952465024 : Int) atom1181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (397441979725824 : Int) atom1182Coded) (CoefficientMerge.scale (384691013581824 : Int) atom1183Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (360117537191424 : Int) atom1184Coded) (CoefficientMerge.scale (345476799258624 : Int) atom1185Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413276182501248 : Int) atom1186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (340052591831040 : Int) atom1187Coded) (CoefficientMerge.scale (461924436555648 : Int) atom1188Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (396690872067072 : Int) atom1189Coded) (CoefficientMerge.scale (437447716738560 : Int) atom1190Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (478204561410048 : Int) atom1191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (238834335801600 : Int) atom1192Coded) (CoefficientMerge.scale (431701558041600 : Int) atom1193Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (409765257216000 : Int) atom1194Coded) (CoefficientMerge.scale (379089486720000 : Int) atom1195Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358346454681600 : Int) atom1196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416025578707200 : Int) atom1197Coded) (CoefficientMerge.scale (345906104544000 : Int) atom1198Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (472838574700800 : Int) atom1199Coded) (CoefficientMerge.scale (400716687571200 : Int) atom1200Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (442289165472000 : Int) atom1201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (483861643372800 : Int) atom1202Coded) (CoefficientMerge.scale (237050383046400 : Int) atom1203Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (439906721184000 : Int) atom1204Coded) (CoefficientMerge.scale (402108063840000 : Int) atom1205Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (374242144953600 : Int) atom1206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411426449280000 : Int) atom1207Coded) (CoefficientMerge.scale (350110707962400 : Int) atom1208Coded))))))) := by
  rw [block017_data_flat078_step, block017_data_flat038_original, block017_data_flat077_original]
def block017_data_flat079 : CoefficientMerge.Poly := [(nat_lit 2084, Int.ofNat (nat_lit 476404187212800))]
theorem block017_data_flat079_step : block017_data_flat079 = (CoefficientMerge.scale (476404187212800 : Int) atom1209Coded) := by decide +kernel
theorem block017_data_flat079_original : block017_data_flat079 = (CoefficientMerge.scale (476404187212800 : Int) atom1209Coded) := by
  rw [block017_data_flat079_step]
def block017_data_flat080 : CoefficientMerge.Poly := [(nat_lit 2085, Int.ofNat (nat_lit 408364671052800))]
theorem block017_data_flat080_step : block017_data_flat080 = (CoefficientMerge.scale (408364671052800 : Int) atom1210Coded) := by decide +kernel
theorem block017_data_flat080_original : block017_data_flat080 = (CoefficientMerge.scale (408364671052800 : Int) atom1210Coded) := by
  rw [block017_data_flat080_step]
def block017_data_flat081 : CoefficientMerge.Poly := [(nat_lit 2084, Int.ofNat (nat_lit 476404187212800)), (nat_lit 2085, Int.ofNat (nat_lit 408364671052800))]
theorem block017_data_flat081_step : block017_data_flat081 = (CoefficientMerge.fastMerge block017_data_flat079 block017_data_flat080) := by decide +kernel
theorem block017_data_flat081_original : block017_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (476404187212800 : Int) atom1209Coded) (CoefficientMerge.scale (408364671052800 : Int) atom1210Coded)) := by
  rw [block017_data_flat081_step, block017_data_flat079_original, block017_data_flat080_original]
def block017_data_flat082 : CoefficientMerge.Poly := [(nat_lit 2086, Int.ofNat (nat_lit 433640731154400))]
theorem block017_data_flat082_step : block017_data_flat082 = (CoefficientMerge.scale (433640731154400 : Int) atom1211Coded) := by decide +kernel
theorem block017_data_flat082_original : block017_data_flat082 = (CoefficientMerge.scale (433640731154400 : Int) atom1211Coded) := by
  rw [block017_data_flat082_step]
def block017_data_flat083 : CoefficientMerge.Poly := [(nat_lit 2087, Int.ofNat (nat_lit 471496571330400))]
theorem block017_data_flat083_step : block017_data_flat083 = (CoefficientMerge.scale (471496571330400 : Int) atom1212Coded) := by decide +kernel
theorem block017_data_flat083_original : block017_data_flat083 = (CoefficientMerge.scale (471496571330400 : Int) atom1212Coded) := by
  rw [block017_data_flat083_step]
def block017_data_flat084 : CoefficientMerge.Poly := [(nat_lit 2103, Int.ofNat (nat_lit 250122539520000))]
theorem block017_data_flat084_step : block017_data_flat084 = (CoefficientMerge.scale (250122539520000 : Int) atom1213Coded) := by decide +kernel
theorem block017_data_flat084_original : block017_data_flat084 = (CoefficientMerge.scale (250122539520000 : Int) atom1213Coded) := by
  rw [block017_data_flat084_step]
def block017_data_flat085 : CoefficientMerge.Poly := [(nat_lit 2087, Int.ofNat (nat_lit 471496571330400)), (nat_lit 2103, Int.ofNat (nat_lit 250122539520000))]
theorem block017_data_flat085_step : block017_data_flat085 = (CoefficientMerge.fastMerge block017_data_flat083 block017_data_flat084) := by decide +kernel
theorem block017_data_flat085_original : block017_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (471496571330400 : Int) atom1212Coded) (CoefficientMerge.scale (250122539520000 : Int) atom1213Coded)) := by
  rw [block017_data_flat085_step, block017_data_flat083_original, block017_data_flat084_original]
def block017_data_flat086 : CoefficientMerge.Poly := [(nat_lit 2086, Int.ofNat (nat_lit 433640731154400)), (nat_lit 2087, Int.ofNat (nat_lit 471496571330400)), (nat_lit 2103, Int.ofNat (nat_lit 250122539520000))]
theorem block017_data_flat086_step : block017_data_flat086 = (CoefficientMerge.fastMerge block017_data_flat082 block017_data_flat085) := by decide +kernel
theorem block017_data_flat086_original : block017_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (433640731154400 : Int) atom1211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (471496571330400 : Int) atom1212Coded) (CoefficientMerge.scale (250122539520000 : Int) atom1213Coded))) := by
  rw [block017_data_flat086_step, block017_data_flat082_original, block017_data_flat085_original]
def block017_data_flat087 : CoefficientMerge.Poly := [(nat_lit 2084, Int.ofNat (nat_lit 476404187212800)), (nat_lit 2085, Int.ofNat (nat_lit 408364671052800)), (nat_lit 2086, Int.ofNat (nat_lit 433640731154400)), (nat_lit 2087, Int.ofNat (nat_lit 471496571330400)), (nat_lit 2103, Int.ofNat (nat_lit 250122539520000))]
theorem block017_data_flat087_step : block017_data_flat087 = (CoefficientMerge.fastMerge block017_data_flat081 block017_data_flat086) := by decide +kernel
theorem block017_data_flat087_original : block017_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (476404187212800 : Int) atom1209Coded) (CoefficientMerge.scale (408364671052800 : Int) atom1210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (433640731154400 : Int) atom1211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (471496571330400 : Int) atom1212Coded) (CoefficientMerge.scale (250122539520000 : Int) atom1213Coded)))) := by
  rw [block017_data_flat087_step, block017_data_flat081_original, block017_data_flat086_original]
def block017_data_flat088 : CoefficientMerge.Poly := [(nat_lit 2104, Int.ofNat (nat_lit 440950187059200))]
theorem block017_data_flat088_step : block017_data_flat088 = (CoefficientMerge.scale (440950187059200 : Int) atom1214Coded) := by decide +kernel
theorem block017_data_flat088_original : block017_data_flat088 = (CoefficientMerge.scale (440950187059200 : Int) atom1214Coded) := by
  rw [block017_data_flat088_step]
def block017_data_flat089 : CoefficientMerge.Poly := [(nat_lit 2105, Int.ofNat (nat_lit 404940788582400))]
theorem block017_data_flat089_step : block017_data_flat089 = (CoefficientMerge.scale (404940788582400 : Int) atom1215Coded) := by decide +kernel
theorem block017_data_flat089_original : block017_data_flat089 = (CoefficientMerge.scale (404940788582400 : Int) atom1215Coded) := by
  rw [block017_data_flat089_step]
def block017_data_flat090 : CoefficientMerge.Poly := [(nat_lit 2104, Int.ofNat (nat_lit 440950187059200)), (nat_lit 2105, Int.ofNat (nat_lit 404940788582400))]
theorem block017_data_flat090_step : block017_data_flat090 = (CoefficientMerge.fastMerge block017_data_flat088 block017_data_flat089) := by decide +kernel
theorem block017_data_flat090_original : block017_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (440950187059200 : Int) atom1214Coded) (CoefficientMerge.scale (404940788582400 : Int) atom1215Coded)) := by
  rw [block017_data_flat090_step, block017_data_flat088_original, block017_data_flat089_original]
def block017_data_flat091 : CoefficientMerge.Poly := [(nat_lit 2106, Int.ofNat (nat_lit 436401333043200))]
theorem block017_data_flat091_step : block017_data_flat091 = (CoefficientMerge.scale (436401333043200 : Int) atom1216Coded) := by decide +kernel
theorem block017_data_flat091_original : block017_data_flat091 = (CoefficientMerge.scale (436401333043200 : Int) atom1216Coded) := by
  rw [block017_data_flat091_step]
def block017_data_flat092 : CoefficientMerge.Poly := [(nat_lit 2107, Int.ofNat (nat_lit 360026976153600))]
theorem block017_data_flat092_step : block017_data_flat092 = (CoefficientMerge.scale (360026976153600 : Int) atom1217Coded) := by decide +kernel
theorem block017_data_flat092_original : block017_data_flat092 = (CoefficientMerge.scale (360026976153600 : Int) atom1217Coded) := by
  rw [block017_data_flat092_step]
def block017_data_flat093 : CoefficientMerge.Poly := [(nat_lit 2108, Int.ofNat (nat_lit 509543812915200))]
theorem block017_data_flat093_step : block017_data_flat093 = (CoefficientMerge.scale (509543812915200 : Int) atom1218Coded) := by decide +kernel
theorem block017_data_flat093_original : block017_data_flat093 = (CoefficientMerge.scale (509543812915200 : Int) atom1218Coded) := by
  rw [block017_data_flat093_step]
def block017_data_flat094 : CoefficientMerge.Poly := [(nat_lit 2107, Int.ofNat (nat_lit 360026976153600)), (nat_lit 2108, Int.ofNat (nat_lit 509543812915200))]
theorem block017_data_flat094_step : block017_data_flat094 = (CoefficientMerge.fastMerge block017_data_flat092 block017_data_flat093) := by decide +kernel
theorem block017_data_flat094_original : block017_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (360026976153600 : Int) atom1217Coded) (CoefficientMerge.scale (509543812915200 : Int) atom1218Coded)) := by
  rw [block017_data_flat094_step, block017_data_flat092_original, block017_data_flat093_original]
def block017_data_flat095 : CoefficientMerge.Poly := [(nat_lit 2106, Int.ofNat (nat_lit 436401333043200)), (nat_lit 2107, Int.ofNat (nat_lit 360026976153600)), (nat_lit 2108, Int.ofNat (nat_lit 509543812915200))]
theorem block017_data_flat095_step : block017_data_flat095 = (CoefficientMerge.fastMerge block017_data_flat091 block017_data_flat094) := by decide +kernel
theorem block017_data_flat095_original : block017_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (436401333043200 : Int) atom1216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360026976153600 : Int) atom1217Coded) (CoefficientMerge.scale (509543812915200 : Int) atom1218Coded))) := by
  rw [block017_data_flat095_step, block017_data_flat091_original, block017_data_flat094_original]
def block017_data_flat096 : CoefficientMerge.Poly := [(nat_lit 2104, Int.ofNat (nat_lit 440950187059200)), (nat_lit 2105, Int.ofNat (nat_lit 404940788582400)), (nat_lit 2106, Int.ofNat (nat_lit 436401333043200)), (nat_lit 2107, Int.ofNat (nat_lit 360026976153600)), (nat_lit 2108, Int.ofNat (nat_lit 509543812915200))]
theorem block017_data_flat096_step : block017_data_flat096 = (CoefficientMerge.fastMerge block017_data_flat090 block017_data_flat095) := by decide +kernel
theorem block017_data_flat096_original : block017_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (440950187059200 : Int) atom1214Coded) (CoefficientMerge.scale (404940788582400 : Int) atom1215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436401333043200 : Int) atom1216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360026976153600 : Int) atom1217Coded) (CoefficientMerge.scale (509543812915200 : Int) atom1218Coded)))) := by
  rw [block017_data_flat096_step, block017_data_flat090_original, block017_data_flat095_original]
def block017_data_flat097 : CoefficientMerge.Poly := [(nat_lit 2084, Int.ofNat (nat_lit 476404187212800)), (nat_lit 2085, Int.ofNat (nat_lit 408364671052800)), (nat_lit 2086, Int.ofNat (nat_lit 433640731154400)), (nat_lit 2087, Int.ofNat (nat_lit 471496571330400)), (nat_lit 2103, Int.ofNat (nat_lit 250122539520000)), (nat_lit 2104, Int.ofNat (nat_lit 440950187059200)), (nat_lit 2105, Int.ofNat (nat_lit 404940788582400)), (nat_lit 2106, Int.ofNat (nat_lit 436401333043200)), (nat_lit 2107, Int.ofNat (nat_lit 360026976153600)), (nat_lit 2108, Int.ofNat (nat_lit 509543812915200))]
theorem block017_data_flat097_step : block017_data_flat097 = (CoefficientMerge.fastMerge block017_data_flat087 block017_data_flat096) := by decide +kernel
theorem block017_data_flat097_original : block017_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (476404187212800 : Int) atom1209Coded) (CoefficientMerge.scale (408364671052800 : Int) atom1210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (433640731154400 : Int) atom1211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (471496571330400 : Int) atom1212Coded) (CoefficientMerge.scale (250122539520000 : Int) atom1213Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (440950187059200 : Int) atom1214Coded) (CoefficientMerge.scale (404940788582400 : Int) atom1215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436401333043200 : Int) atom1216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360026976153600 : Int) atom1217Coded) (CoefficientMerge.scale (509543812915200 : Int) atom1218Coded))))) := by
  rw [block017_data_flat097_step, block017_data_flat087_original, block017_data_flat096_original]
def block017_data_flat098 : CoefficientMerge.Poly := [(nat_lit 2109, Int.ofNat (nat_lit 445586667724800))]
theorem block017_data_flat098_step : block017_data_flat098 = (CoefficientMerge.scale (445586667724800 : Int) atom1219Coded) := by decide +kernel
theorem block017_data_flat098_original : block017_data_flat098 = (CoefficientMerge.scale (445586667724800 : Int) atom1219Coded) := by
  rw [block017_data_flat098_step]
def block017_data_flat099 : CoefficientMerge.Poly := [(nat_lit 2110, Int.ofNat (nat_lit 404141839718400))]
theorem block017_data_flat099_step : block017_data_flat099 = (CoefficientMerge.scale (404141839718400 : Int) atom1220Coded) := by decide +kernel
theorem block017_data_flat099_original : block017_data_flat099 = (CoefficientMerge.scale (404141839718400 : Int) atom1220Coded) := by
  rw [block017_data_flat099_step]
def block017_data_flat100 : CoefficientMerge.Poly := [(nat_lit 2109, Int.ofNat (nat_lit 445586667724800)), (nat_lit 2110, Int.ofNat (nat_lit 404141839718400))]
theorem block017_data_flat100_step : block017_data_flat100 = (CoefficientMerge.fastMerge block017_data_flat098 block017_data_flat099) := by decide +kernel
theorem block017_data_flat100_original : block017_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (445586667724800 : Int) atom1219Coded) (CoefficientMerge.scale (404141839718400 : Int) atom1220Coded)) := by
  rw [block017_data_flat100_step, block017_data_flat098_original, block017_data_flat099_original]
def block017_data_flat101 : CoefficientMerge.Poly := [(nat_lit 2111, Int.ofNat (nat_lit 433071520358400))]
theorem block017_data_flat101_step : block017_data_flat101 = (CoefficientMerge.scale (433071520358400 : Int) atom1221Coded) := by decide +kernel
theorem block017_data_flat101_original : block017_data_flat101 = (CoefficientMerge.scale (433071520358400 : Int) atom1221Coded) := by
  rw [block017_data_flat101_step]
def block017_data_flat102 : CoefficientMerge.Poly := [(nat_lit 2128, Int.ofNat (nat_lit 241176889497600))]
theorem block017_data_flat102_step : block017_data_flat102 = (CoefficientMerge.scale (241176889497600 : Int) atom1222Coded) := by decide +kernel
theorem block017_data_flat102_original : block017_data_flat102 = (CoefficientMerge.scale (241176889497600 : Int) atom1222Coded) := by
  rw [block017_data_flat102_step]
def block017_data_flat103 : CoefficientMerge.Poly := [(nat_lit 2129, Int.ofNat (nat_lit 434097267609600))]
theorem block017_data_flat103_step : block017_data_flat103 = (CoefficientMerge.scale (434097267609600 : Int) atom1223Coded) := by decide +kernel
theorem block017_data_flat103_original : block017_data_flat103 = (CoefficientMerge.scale (434097267609600 : Int) atom1223Coded) := by
  rw [block017_data_flat103_step]
def block017_data_flat104 : CoefficientMerge.Poly := [(nat_lit 2128, Int.ofNat (nat_lit 241176889497600)), (nat_lit 2129, Int.ofNat (nat_lit 434097267609600))]
theorem block017_data_flat104_step : block017_data_flat104 = (CoefficientMerge.fastMerge block017_data_flat102 block017_data_flat103) := by decide +kernel
theorem block017_data_flat104_original : block017_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (241176889497600 : Int) atom1222Coded) (CoefficientMerge.scale (434097267609600 : Int) atom1223Coded)) := by
  rw [block017_data_flat104_step, block017_data_flat102_original, block017_data_flat103_original]
def block017_data_flat105 : CoefficientMerge.Poly := [(nat_lit 2111, Int.ofNat (nat_lit 433071520358400)), (nat_lit 2128, Int.ofNat (nat_lit 241176889497600)), (nat_lit 2129, Int.ofNat (nat_lit 434097267609600))]
theorem block017_data_flat105_step : block017_data_flat105 = (CoefficientMerge.fastMerge block017_data_flat101 block017_data_flat104) := by decide +kernel
theorem block017_data_flat105_original : block017_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (433071520358400 : Int) atom1221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241176889497600 : Int) atom1222Coded) (CoefficientMerge.scale (434097267609600 : Int) atom1223Coded))) := by
  rw [block017_data_flat105_step, block017_data_flat101_original, block017_data_flat104_original]
def block017_data_flat106 : CoefficientMerge.Poly := [(nat_lit 2109, Int.ofNat (nat_lit 445586667724800)), (nat_lit 2110, Int.ofNat (nat_lit 404141839718400)), (nat_lit 2111, Int.ofNat (nat_lit 433071520358400)), (nat_lit 2128, Int.ofNat (nat_lit 241176889497600)), (nat_lit 2129, Int.ofNat (nat_lit 434097267609600))]
theorem block017_data_flat106_step : block017_data_flat106 = (CoefficientMerge.fastMerge block017_data_flat100 block017_data_flat105) := by decide +kernel
theorem block017_data_flat106_original : block017_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (445586667724800 : Int) atom1219Coded) (CoefficientMerge.scale (404141839718400 : Int) atom1220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (433071520358400 : Int) atom1221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241176889497600 : Int) atom1222Coded) (CoefficientMerge.scale (434097267609600 : Int) atom1223Coded)))) := by
  rw [block017_data_flat106_step, block017_data_flat100_original, block017_data_flat105_original]
def block017_data_flat107 : CoefficientMerge.Poly := [(nat_lit 2130, Int.ofNat (nat_lit 437731196313600))]
theorem block017_data_flat107_step : block017_data_flat107 = (CoefficientMerge.scale (437731196313600 : Int) atom1224Coded) := by decide +kernel
theorem block017_data_flat107_original : block017_data_flat107 = (CoefficientMerge.scale (437731196313600 : Int) atom1224Coded) := by
  rw [block017_data_flat107_step]
def block017_data_flat108 : CoefficientMerge.Poly := [(nat_lit 2131, Int.ofNat (nat_lit 365439210393600))]
theorem block017_data_flat108_step : block017_data_flat108 = (CoefficientMerge.scale (365439210393600 : Int) atom1225Coded) := by decide +kernel
theorem block017_data_flat108_original : block017_data_flat108 = (CoefficientMerge.scale (365439210393600 : Int) atom1225Coded) := by
  rw [block017_data_flat108_step]
def block017_data_flat109 : CoefficientMerge.Poly := [(nat_lit 2130, Int.ofNat (nat_lit 437731196313600)), (nat_lit 2131, Int.ofNat (nat_lit 365439210393600))]
theorem block017_data_flat109_step : block017_data_flat109 = (CoefficientMerge.fastMerge block017_data_flat107 block017_data_flat108) := by decide +kernel
theorem block017_data_flat109_original : block017_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (437731196313600 : Int) atom1224Coded) (CoefficientMerge.scale (365439210393600 : Int) atom1225Coded)) := by
  rw [block017_data_flat109_step, block017_data_flat107_original, block017_data_flat108_original]
def block017_data_flat110 : CoefficientMerge.Poly := [(nat_lit 2132, Int.ofNat (nat_lit 519038418124800))]
theorem block017_data_flat110_step : block017_data_flat110 = (CoefficientMerge.scale (519038418124800 : Int) atom1226Coded) := by decide +kernel
theorem block017_data_flat110_original : block017_data_flat110 = (CoefficientMerge.scale (519038418124800 : Int) atom1226Coded) := by
  rw [block017_data_flat110_step]
def block017_data_flat111 : CoefficientMerge.Poly := [(nat_lit 2133, Int.ofNat (nat_lit 459163643904000))]
theorem block017_data_flat111_step : block017_data_flat111 = (CoefficientMerge.scale (459163643904000 : Int) atom1227Coded) := by decide +kernel
theorem block017_data_flat111_original : block017_data_flat111 = (CoefficientMerge.scale (459163643904000 : Int) atom1227Coded) := by
  rw [block017_data_flat111_step]
def block017_data_flat112 : CoefficientMerge.Poly := [(nat_lit 2134, Int.ofNat (nat_lit 364008189888000))]
theorem block017_data_flat112_step : block017_data_flat112 = (CoefficientMerge.scale (364008189888000 : Int) atom1228Coded) := by decide +kernel
theorem block017_data_flat112_original : block017_data_flat112 = (CoefficientMerge.scale (364008189888000 : Int) atom1228Coded) := by
  rw [block017_data_flat112_step]
def block017_data_flat113 : CoefficientMerge.Poly := [(nat_lit 2133, Int.ofNat (nat_lit 459163643904000)), (nat_lit 2134, Int.ofNat (nat_lit 364008189888000))]
theorem block017_data_flat113_step : block017_data_flat113 = (CoefficientMerge.fastMerge block017_data_flat111 block017_data_flat112) := by decide +kernel
theorem block017_data_flat113_original : block017_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (459163643904000 : Int) atom1227Coded) (CoefficientMerge.scale (364008189888000 : Int) atom1228Coded)) := by
  rw [block017_data_flat113_step, block017_data_flat111_original, block017_data_flat112_original]
def block017_data_flat114 : CoefficientMerge.Poly := [(nat_lit 2132, Int.ofNat (nat_lit 519038418124800)), (nat_lit 2133, Int.ofNat (nat_lit 459163643904000)), (nat_lit 2134, Int.ofNat (nat_lit 364008189888000))]
theorem block017_data_flat114_step : block017_data_flat114 = (CoefficientMerge.fastMerge block017_data_flat110 block017_data_flat113) := by decide +kernel
theorem block017_data_flat114_original : block017_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (519038418124800 : Int) atom1226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (459163643904000 : Int) atom1227Coded) (CoefficientMerge.scale (364008189888000 : Int) atom1228Coded))) := by
  rw [block017_data_flat114_step, block017_data_flat110_original, block017_data_flat113_original]
def block017_data_flat115 : CoefficientMerge.Poly := [(nat_lit 2130, Int.ofNat (nat_lit 437731196313600)), (nat_lit 2131, Int.ofNat (nat_lit 365439210393600)), (nat_lit 2132, Int.ofNat (nat_lit 519038418124800)), (nat_lit 2133, Int.ofNat (nat_lit 459163643904000)), (nat_lit 2134, Int.ofNat (nat_lit 364008189888000))]
theorem block017_data_flat115_step : block017_data_flat115 = (CoefficientMerge.fastMerge block017_data_flat109 block017_data_flat114) := by decide +kernel
theorem block017_data_flat115_original : block017_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (437731196313600 : Int) atom1224Coded) (CoefficientMerge.scale (365439210393600 : Int) atom1225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519038418124800 : Int) atom1226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (459163643904000 : Int) atom1227Coded) (CoefficientMerge.scale (364008189888000 : Int) atom1228Coded)))) := by
  rw [block017_data_flat115_step, block017_data_flat109_original, block017_data_flat114_original]
def block017_data_flat116 : CoefficientMerge.Poly := [(nat_lit 2109, Int.ofNat (nat_lit 445586667724800)), (nat_lit 2110, Int.ofNat (nat_lit 404141839718400)), (nat_lit 2111, Int.ofNat (nat_lit 433071520358400)), (nat_lit 2128, Int.ofNat (nat_lit 241176889497600)), (nat_lit 2129, Int.ofNat (nat_lit 434097267609600)), (nat_lit 2130, Int.ofNat (nat_lit 437731196313600)), (nat_lit 2131, Int.ofNat (nat_lit 365439210393600)), (nat_lit 2132, Int.ofNat (nat_lit 519038418124800)), (nat_lit 2133, Int.ofNat (nat_lit 459163643904000)), (nat_lit 2134, Int.ofNat (nat_lit 364008189888000))]
theorem block017_data_flat116_step : block017_data_flat116 = (CoefficientMerge.fastMerge block017_data_flat106 block017_data_flat115) := by decide +kernel
theorem block017_data_flat116_original : block017_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (445586667724800 : Int) atom1219Coded) (CoefficientMerge.scale (404141839718400 : Int) atom1220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (433071520358400 : Int) atom1221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241176889497600 : Int) atom1222Coded) (CoefficientMerge.scale (434097267609600 : Int) atom1223Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (437731196313600 : Int) atom1224Coded) (CoefficientMerge.scale (365439210393600 : Int) atom1225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519038418124800 : Int) atom1226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (459163643904000 : Int) atom1227Coded) (CoefficientMerge.scale (364008189888000 : Int) atom1228Coded))))) := by
  rw [block017_data_flat116_step, block017_data_flat106_original, block017_data_flat115_original]
def block017_data_flat117 : CoefficientMerge.Poly := [(nat_lit 2084, Int.ofNat (nat_lit 476404187212800)), (nat_lit 2085, Int.ofNat (nat_lit 408364671052800)), (nat_lit 2086, Int.ofNat (nat_lit 433640731154400)), (nat_lit 2087, Int.ofNat (nat_lit 471496571330400)), (nat_lit 2103, Int.ofNat (nat_lit 250122539520000)), (nat_lit 2104, Int.ofNat (nat_lit 440950187059200)), (nat_lit 2105, Int.ofNat (nat_lit 404940788582400)), (nat_lit 2106, Int.ofNat (nat_lit 436401333043200)), (nat_lit 2107, Int.ofNat (nat_lit 360026976153600)), (nat_lit 2108, Int.ofNat (nat_lit 509543812915200)), (nat_lit 2109, Int.ofNat (nat_lit 445586667724800)), (nat_lit 2110, Int.ofNat (nat_lit 404141839718400)), (nat_lit 2111, Int.ofNat (nat_lit 433071520358400)), (nat_lit 2128, Int.ofNat (nat_lit 241176889497600)), (nat_lit 2129, Int.ofNat (nat_lit 434097267609600)), (nat_lit 2130, Int.ofNat (nat_lit 437731196313600)), (nat_lit 2131, Int.ofNat (nat_lit 365439210393600)), (nat_lit 2132, Int.ofNat (nat_lit 519038418124800)), (nat_lit 2133, Int.ofNat (nat_lit 459163643904000)), (nat_lit 2134, Int.ofNat (nat_lit 364008189888000))]
theorem block017_data_flat117_step : block017_data_flat117 = (CoefficientMerge.fastMerge block017_data_flat097 block017_data_flat116) := by decide +kernel
theorem block017_data_flat117_original : block017_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (476404187212800 : Int) atom1209Coded) (CoefficientMerge.scale (408364671052800 : Int) atom1210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (433640731154400 : Int) atom1211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (471496571330400 : Int) atom1212Coded) (CoefficientMerge.scale (250122539520000 : Int) atom1213Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (440950187059200 : Int) atom1214Coded) (CoefficientMerge.scale (404940788582400 : Int) atom1215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436401333043200 : Int) atom1216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360026976153600 : Int) atom1217Coded) (CoefficientMerge.scale (509543812915200 : Int) atom1218Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (445586667724800 : Int) atom1219Coded) (CoefficientMerge.scale (404141839718400 : Int) atom1220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (433071520358400 : Int) atom1221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241176889497600 : Int) atom1222Coded) (CoefficientMerge.scale (434097267609600 : Int) atom1223Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (437731196313600 : Int) atom1224Coded) (CoefficientMerge.scale (365439210393600 : Int) atom1225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519038418124800 : Int) atom1226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (459163643904000 : Int) atom1227Coded) (CoefficientMerge.scale (364008189888000 : Int) atom1228Coded)))))) := by
  rw [block017_data_flat117_step, block017_data_flat097_original, block017_data_flat116_original]
def block017_data_flat118 : CoefficientMerge.Poly := [(nat_lit 2135, Int.ofNat (nat_lit 473555032473600))]
theorem block017_data_flat118_step : block017_data_flat118 = (CoefficientMerge.scale (473555032473600 : Int) atom1229Coded) := by decide +kernel
theorem block017_data_flat118_original : block017_data_flat118 = (CoefficientMerge.scale (473555032473600 : Int) atom1229Coded) := by
  rw [block017_data_flat118_step]
def block017_data_flat119 : CoefficientMerge.Poly := [(nat_lit 2153, Int.ofNat (nat_lit 238478504140800))]
theorem block017_data_flat119_step : block017_data_flat119 = (CoefficientMerge.scale (238478504140800 : Int) atom1230Coded) := by decide +kernel
theorem block017_data_flat119_original : block017_data_flat119 = (CoefficientMerge.scale (238478504140800 : Int) atom1230Coded) := by
  rw [block017_data_flat119_step]
def block017_data_flat120 : CoefficientMerge.Poly := [(nat_lit 2135, Int.ofNat (nat_lit 473555032473600)), (nat_lit 2153, Int.ofNat (nat_lit 238478504140800))]
theorem block017_data_flat120_step : block017_data_flat120 = (CoefficientMerge.fastMerge block017_data_flat118 block017_data_flat119) := by decide +kernel
theorem block017_data_flat120_original : block017_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (473555032473600 : Int) atom1229Coded) (CoefficientMerge.scale (238478504140800 : Int) atom1230Coded)) := by
  rw [block017_data_flat120_step, block017_data_flat118_original, block017_data_flat119_original]
def block017_data_flat121 : CoefficientMerge.Poly := [(nat_lit 2154, Int.ofNat (nat_lit 458926536499200))]
theorem block017_data_flat121_step : block017_data_flat121 = (CoefficientMerge.scale (458926536499200 : Int) atom1231Coded) := by decide +kernel
theorem block017_data_flat121_original : block017_data_flat121 = (CoefficientMerge.scale (458926536499200 : Int) atom1231Coded) := by
  rw [block017_data_flat121_step]
def block017_data_flat122 : CoefficientMerge.Poly := [(nat_lit 2155, Int.ofNat (nat_lit 390716921548800))]
theorem block017_data_flat122_step : block017_data_flat122 = (CoefficientMerge.scale (390716921548800 : Int) atom1232Coded) := by decide +kernel
theorem block017_data_flat122_original : block017_data_flat122 = (CoefficientMerge.scale (390716921548800 : Int) atom1232Coded) := by
  rw [block017_data_flat122_step]
def block017_data_flat123 : CoefficientMerge.Poly := [(nat_lit 2156, Int.ofNat (nat_lit 548398500249600))]
theorem block017_data_flat123_step : block017_data_flat123 = (CoefficientMerge.scale (548398500249600 : Int) atom1233Coded) := by decide +kernel
theorem block017_data_flat123_original : block017_data_flat123 = (CoefficientMerge.scale (548398500249600 : Int) atom1233Coded) := by
  rw [block017_data_flat123_step]
def block017_data_flat124 : CoefficientMerge.Poly := [(nat_lit 2155, Int.ofNat (nat_lit 390716921548800)), (nat_lit 2156, Int.ofNat (nat_lit 548398500249600))]
theorem block017_data_flat124_step : block017_data_flat124 = (CoefficientMerge.fastMerge block017_data_flat122 block017_data_flat123) := by decide +kernel
theorem block017_data_flat124_original : block017_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (390716921548800 : Int) atom1232Coded) (CoefficientMerge.scale (548398500249600 : Int) atom1233Coded)) := by
  rw [block017_data_flat124_step, block017_data_flat122_original, block017_data_flat123_original]
def block017_data_flat125 : CoefficientMerge.Poly := [(nat_lit 2154, Int.ofNat (nat_lit 458926536499200)), (nat_lit 2155, Int.ofNat (nat_lit 390716921548800)), (nat_lit 2156, Int.ofNat (nat_lit 548398500249600))]
theorem block017_data_flat125_step : block017_data_flat125 = (CoefficientMerge.fastMerge block017_data_flat121 block017_data_flat124) := by decide +kernel
theorem block017_data_flat125_original : block017_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (458926536499200 : Int) atom1231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390716921548800 : Int) atom1232Coded) (CoefficientMerge.scale (548398500249600 : Int) atom1233Coded))) := by
  rw [block017_data_flat125_step, block017_data_flat121_original, block017_data_flat124_original]
def block017_data_flat126 : CoefficientMerge.Poly := [(nat_lit 2135, Int.ofNat (nat_lit 473555032473600)), (nat_lit 2153, Int.ofNat (nat_lit 238478504140800)), (nat_lit 2154, Int.ofNat (nat_lit 458926536499200)), (nat_lit 2155, Int.ofNat (nat_lit 390716921548800)), (nat_lit 2156, Int.ofNat (nat_lit 548398500249600))]
theorem block017_data_flat126_step : block017_data_flat126 = (CoefficientMerge.fastMerge block017_data_flat120 block017_data_flat125) := by decide +kernel
theorem block017_data_flat126_original : block017_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (473555032473600 : Int) atom1229Coded) (CoefficientMerge.scale (238478504140800 : Int) atom1230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (458926536499200 : Int) atom1231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390716921548800 : Int) atom1232Coded) (CoefficientMerge.scale (548398500249600 : Int) atom1233Coded)))) := by
  rw [block017_data_flat126_step, block017_data_flat120_original, block017_data_flat125_original]
def block017_data_flat127 : CoefficientMerge.Poly := [(nat_lit 2157, Int.ofNat (nat_lit 492606096998400))]
theorem block017_data_flat127_step : block017_data_flat127 = (CoefficientMerge.scale (492606096998400 : Int) atom1234Coded) := by decide +kernel
theorem block017_data_flat127_original : block017_data_flat127 = (CoefficientMerge.scale (492606096998400 : Int) atom1234Coded) := by
  rw [block017_data_flat127_step]
def block017_data_flat128 : CoefficientMerge.Poly := [(nat_lit 2158, Int.ofNat (nat_lit 400409331033600))]
theorem block017_data_flat128_step : block017_data_flat128 = (CoefficientMerge.scale (400409331033600 : Int) atom1235Coded) := by decide +kernel
theorem block017_data_flat128_original : block017_data_flat128 = (CoefficientMerge.scale (400409331033600 : Int) atom1235Coded) := by
  rw [block017_data_flat128_step]
def block017_data_flat129 : CoefficientMerge.Poly := [(nat_lit 2157, Int.ofNat (nat_lit 492606096998400)), (nat_lit 2158, Int.ofNat (nat_lit 400409331033600))]
theorem block017_data_flat129_step : block017_data_flat129 = (CoefficientMerge.fastMerge block017_data_flat127 block017_data_flat128) := by decide +kernel
theorem block017_data_flat129_original : block017_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (492606096998400 : Int) atom1234Coded) (CoefficientMerge.scale (400409331033600 : Int) atom1235Coded)) := by
  rw [block017_data_flat129_step, block017_data_flat127_original, block017_data_flat128_original]
def block017_data_flat130 : CoefficientMerge.Poly := [(nat_lit 2159, Int.ofNat (nat_lit 514038544588800))]
theorem block017_data_flat130_step : block017_data_flat130 = (CoefficientMerge.scale (514038544588800 : Int) atom1236Coded) := by decide +kernel
theorem block017_data_flat130_original : block017_data_flat130 = (CoefficientMerge.scale (514038544588800 : Int) atom1236Coded) := by
  rw [block017_data_flat130_step]
def block017_data_flat131 : CoefficientMerge.Poly := [(nat_lit 2178, Int.ofNat (nat_lit 269691632179200))]
theorem block017_data_flat131_step : block017_data_flat131 = (CoefficientMerge.scale (269691632179200 : Int) atom1237Coded) := by decide +kernel
theorem block017_data_flat131_original : block017_data_flat131 = (CoefficientMerge.scale (269691632179200 : Int) atom1237Coded) := by
  rw [block017_data_flat131_step]
def block017_data_flat132 : CoefficientMerge.Poly := [(nat_lit 2179, Int.ofNat (nat_lit 461307919564800))]
theorem block017_data_flat132_step : block017_data_flat132 = (CoefficientMerge.scale (461307919564800 : Int) atom1238Coded) := by decide +kernel
theorem block017_data_flat132_original : block017_data_flat132 = (CoefficientMerge.scale (461307919564800 : Int) atom1238Coded) := by
  rw [block017_data_flat132_step]
def block017_data_flat133 : CoefficientMerge.Poly := [(nat_lit 2178, Int.ofNat (nat_lit 269691632179200)), (nat_lit 2179, Int.ofNat (nat_lit 461307919564800))]
theorem block017_data_flat133_step : block017_data_flat133 = (CoefficientMerge.fastMerge block017_data_flat131 block017_data_flat132) := by decide +kernel
theorem block017_data_flat133_original : block017_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (269691632179200 : Int) atom1237Coded) (CoefficientMerge.scale (461307919564800 : Int) atom1238Coded)) := by
  rw [block017_data_flat133_step, block017_data_flat131_original, block017_data_flat132_original]
def block017_data_flat134 : CoefficientMerge.Poly := [(nat_lit 2159, Int.ofNat (nat_lit 514038544588800)), (nat_lit 2178, Int.ofNat (nat_lit 269691632179200)), (nat_lit 2179, Int.ofNat (nat_lit 461307919564800))]
theorem block017_data_flat134_step : block017_data_flat134 = (CoefficientMerge.fastMerge block017_data_flat130 block017_data_flat133) := by decide +kernel
theorem block017_data_flat134_original : block017_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (514038544588800 : Int) atom1236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269691632179200 : Int) atom1237Coded) (CoefficientMerge.scale (461307919564800 : Int) atom1238Coded))) := by
  rw [block017_data_flat134_step, block017_data_flat130_original, block017_data_flat133_original]
def block017_data_flat135 : CoefficientMerge.Poly := [(nat_lit 2157, Int.ofNat (nat_lit 492606096998400)), (nat_lit 2158, Int.ofNat (nat_lit 400409331033600)), (nat_lit 2159, Int.ofNat (nat_lit 514038544588800)), (nat_lit 2178, Int.ofNat (nat_lit 269691632179200)), (nat_lit 2179, Int.ofNat (nat_lit 461307919564800))]
theorem block017_data_flat135_step : block017_data_flat135 = (CoefficientMerge.fastMerge block017_data_flat129 block017_data_flat134) := by decide +kernel
theorem block017_data_flat135_original : block017_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (492606096998400 : Int) atom1234Coded) (CoefficientMerge.scale (400409331033600 : Int) atom1235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (514038544588800 : Int) atom1236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269691632179200 : Int) atom1237Coded) (CoefficientMerge.scale (461307919564800 : Int) atom1238Coded)))) := by
  rw [block017_data_flat135_step, block017_data_flat129_original, block017_data_flat134_original]
def block017_data_flat136 : CoefficientMerge.Poly := [(nat_lit 2135, Int.ofNat (nat_lit 473555032473600)), (nat_lit 2153, Int.ofNat (nat_lit 238478504140800)), (nat_lit 2154, Int.ofNat (nat_lit 458926536499200)), (nat_lit 2155, Int.ofNat (nat_lit 390716921548800)), (nat_lit 2156, Int.ofNat (nat_lit 548398500249600)), (nat_lit 2157, Int.ofNat (nat_lit 492606096998400)), (nat_lit 2158, Int.ofNat (nat_lit 400409331033600)), (nat_lit 2159, Int.ofNat (nat_lit 514038544588800)), (nat_lit 2178, Int.ofNat (nat_lit 269691632179200)), (nat_lit 2179, Int.ofNat (nat_lit 461307919564800))]
theorem block017_data_flat136_step : block017_data_flat136 = (CoefficientMerge.fastMerge block017_data_flat126 block017_data_flat135) := by decide +kernel
theorem block017_data_flat136_original : block017_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (473555032473600 : Int) atom1229Coded) (CoefficientMerge.scale (238478504140800 : Int) atom1230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (458926536499200 : Int) atom1231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390716921548800 : Int) atom1232Coded) (CoefficientMerge.scale (548398500249600 : Int) atom1233Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (492606096998400 : Int) atom1234Coded) (CoefficientMerge.scale (400409331033600 : Int) atom1235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (514038544588800 : Int) atom1236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269691632179200 : Int) atom1237Coded) (CoefficientMerge.scale (461307919564800 : Int) atom1238Coded))))) := by
  rw [block017_data_flat136_step, block017_data_flat126_original, block017_data_flat135_original]
def block017_data_flat137 : CoefficientMerge.Poly := [(nat_lit 2180, Int.ofNat (nat_lit 637019970048000))]
theorem block017_data_flat137_step : block017_data_flat137 = (CoefficientMerge.scale (637019970048000 : Int) atom1239Coded) := by decide +kernel
theorem block017_data_flat137_original : block017_data_flat137 = (CoefficientMerge.scale (637019970048000 : Int) atom1239Coded) := by
  rw [block017_data_flat137_step]
def block017_data_flat138 : CoefficientMerge.Poly := [(nat_lit 2181, Int.ofNat (nat_lit 565153231104000))]
theorem block017_data_flat138_step : block017_data_flat138 = (CoefficientMerge.scale (565153231104000 : Int) atom1240Coded) := by decide +kernel
theorem block017_data_flat138_original : block017_data_flat138 = (CoefficientMerge.scale (565153231104000 : Int) atom1240Coded) := by
  rw [block017_data_flat138_step]
def block017_data_flat139 : CoefficientMerge.Poly := [(nat_lit 2180, Int.ofNat (nat_lit 637019970048000)), (nat_lit 2181, Int.ofNat (nat_lit 565153231104000))]
theorem block017_data_flat139_step : block017_data_flat139 = (CoefficientMerge.fastMerge block017_data_flat137 block017_data_flat138) := by decide +kernel
theorem block017_data_flat139_original : block017_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (637019970048000 : Int) atom1239Coded) (CoefficientMerge.scale (565153231104000 : Int) atom1240Coded)) := by
  rw [block017_data_flat139_step, block017_data_flat137_original, block017_data_flat138_original]
def block017_data_flat140 : CoefficientMerge.Poly := [(nat_lit 2182, Int.ofNat (nat_lit 382207149676800))]
theorem block017_data_flat140_step : block017_data_flat140 = (CoefficientMerge.scale (382207149676800 : Int) atom1241Coded) := by decide +kernel
theorem block017_data_flat140_original : block017_data_flat140 = (CoefficientMerge.scale (382207149676800 : Int) atom1241Coded) := by
  rw [block017_data_flat140_step]
def block017_data_flat141 : CoefficientMerge.Poly := [(nat_lit 2183, Int.ofNat (nat_lit 528156744192000))]
theorem block017_data_flat141_step : block017_data_flat141 = (CoefficientMerge.scale (528156744192000 : Int) atom1242Coded) := by decide +kernel
theorem block017_data_flat141_original : block017_data_flat141 = (CoefficientMerge.scale (528156744192000 : Int) atom1242Coded) := by
  rw [block017_data_flat141_step]
def block017_data_flat142 : CoefficientMerge.Poly := [(nat_lit 2203, Int.ofNat (nat_lit 175133714595840))]
theorem block017_data_flat142_step : block017_data_flat142 = (CoefficientMerge.scale (175133714595840 : Int) atom1243Coded) := by decide +kernel
theorem block017_data_flat142_original : block017_data_flat142 = (CoefficientMerge.scale (175133714595840 : Int) atom1243Coded) := by
  rw [block017_data_flat142_step]
def block017_data_flat143 : CoefficientMerge.Poly := [(nat_lit 2183, Int.ofNat (nat_lit 528156744192000)), (nat_lit 2203, Int.ofNat (nat_lit 175133714595840))]
theorem block017_data_flat143_step : block017_data_flat143 = (CoefficientMerge.fastMerge block017_data_flat141 block017_data_flat142) := by decide +kernel
theorem block017_data_flat143_original : block017_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (528156744192000 : Int) atom1242Coded) (CoefficientMerge.scale (175133714595840 : Int) atom1243Coded)) := by
  rw [block017_data_flat143_step, block017_data_flat141_original, block017_data_flat142_original]
def block017_data_flat144 : CoefficientMerge.Poly := [(nat_lit 2182, Int.ofNat (nat_lit 382207149676800)), (nat_lit 2183, Int.ofNat (nat_lit 528156744192000)), (nat_lit 2203, Int.ofNat (nat_lit 175133714595840))]
theorem block017_data_flat144_step : block017_data_flat144 = (CoefficientMerge.fastMerge block017_data_flat140 block017_data_flat143) := by decide +kernel
theorem block017_data_flat144_original : block017_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (382207149676800 : Int) atom1241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (528156744192000 : Int) atom1242Coded) (CoefficientMerge.scale (175133714595840 : Int) atom1243Coded))) := by
  rw [block017_data_flat144_step, block017_data_flat140_original, block017_data_flat143_original]
def block017_data_flat145 : CoefficientMerge.Poly := [(nat_lit 2180, Int.ofNat (nat_lit 637019970048000)), (nat_lit 2181, Int.ofNat (nat_lit 565153231104000)), (nat_lit 2182, Int.ofNat (nat_lit 382207149676800)), (nat_lit 2183, Int.ofNat (nat_lit 528156744192000)), (nat_lit 2203, Int.ofNat (nat_lit 175133714595840))]
theorem block017_data_flat145_step : block017_data_flat145 = (CoefficientMerge.fastMerge block017_data_flat139 block017_data_flat144) := by decide +kernel
theorem block017_data_flat145_original : block017_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (637019970048000 : Int) atom1239Coded) (CoefficientMerge.scale (565153231104000 : Int) atom1240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (382207149676800 : Int) atom1241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (528156744192000 : Int) atom1242Coded) (CoefficientMerge.scale (175133714595840 : Int) atom1243Coded)))) := by
  rw [block017_data_flat145_step, block017_data_flat139_original, block017_data_flat144_original]
def block017_data_flat146 : CoefficientMerge.Poly := [(nat_lit 2204, Int.ofNat (nat_lit 510466469990400))]
theorem block017_data_flat146_step : block017_data_flat146 = (CoefficientMerge.scale (510466469990400 : Int) atom1244Coded) := by decide +kernel
theorem block017_data_flat146_original : block017_data_flat146 = (CoefficientMerge.scale (510466469990400 : Int) atom1244Coded) := by
  rw [block017_data_flat146_step]
def block017_data_flat147 : CoefficientMerge.Poly := [(nat_lit 2205, Int.ofNat (nat_lit 485972244172800))]
theorem block017_data_flat147_step : block017_data_flat147 = (CoefficientMerge.scale (485972244172800 : Int) atom1245Coded) := by decide +kernel
theorem block017_data_flat147_original : block017_data_flat147 = (CoefficientMerge.scale (485972244172800 : Int) atom1245Coded) := by
  rw [block017_data_flat147_step]
def block017_data_flat148 : CoefficientMerge.Poly := [(nat_lit 2204, Int.ofNat (nat_lit 510466469990400)), (nat_lit 2205, Int.ofNat (nat_lit 485972244172800))]
theorem block017_data_flat148_step : block017_data_flat148 = (CoefficientMerge.fastMerge block017_data_flat146 block017_data_flat147) := by decide +kernel
theorem block017_data_flat148_original : block017_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (510466469990400 : Int) atom1244Coded) (CoefficientMerge.scale (485972244172800 : Int) atom1245Coded)) := by
  rw [block017_data_flat148_step, block017_data_flat146_original, block017_data_flat147_original]
def block017_data_flat149 : CoefficientMerge.Poly := [(nat_lit 2206, Int.ofNat (nat_lit 349403855673600))]
theorem block017_data_flat149_step : block017_data_flat149 = (CoefficientMerge.scale (349403855673600 : Int) atom1246Coded) := by decide +kernel
theorem block017_data_flat149_original : block017_data_flat149 = (CoefficientMerge.scale (349403855673600 : Int) atom1246Coded) := by
  rw [block017_data_flat149_step]
def block017_data_flat150 : CoefficientMerge.Poly := [(nat_lit 2207, Int.ofNat (nat_lit 370049918515200))]
theorem block017_data_flat150_step : block017_data_flat150 = (CoefficientMerge.scale (370049918515200 : Int) atom1247Coded) := by decide +kernel
theorem block017_data_flat150_original : block017_data_flat150 = (CoefficientMerge.scale (370049918515200 : Int) atom1247Coded) := by
  rw [block017_data_flat150_step]
def block017_data_flat151 : CoefficientMerge.Poly := [(nat_lit 2228, Int.ofNat (nat_lit 346746384230400))]
theorem block017_data_flat151_step : block017_data_flat151 = (CoefficientMerge.scale (346746384230400 : Int) atom1248Coded) := by decide +kernel
theorem block017_data_flat151_original : block017_data_flat151 = (CoefficientMerge.scale (346746384230400 : Int) atom1248Coded) := by
  rw [block017_data_flat151_step]
def block017_data_flat152 : CoefficientMerge.Poly := [(nat_lit 2207, Int.ofNat (nat_lit 370049918515200)), (nat_lit 2228, Int.ofNat (nat_lit 346746384230400))]
theorem block017_data_flat152_step : block017_data_flat152 = (CoefficientMerge.fastMerge block017_data_flat150 block017_data_flat151) := by decide +kernel
theorem block017_data_flat152_original : block017_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (370049918515200 : Int) atom1247Coded) (CoefficientMerge.scale (346746384230400 : Int) atom1248Coded)) := by
  rw [block017_data_flat152_step, block017_data_flat150_original, block017_data_flat151_original]
def block017_data_flat153 : CoefficientMerge.Poly := [(nat_lit 2206, Int.ofNat (nat_lit 349403855673600)), (nat_lit 2207, Int.ofNat (nat_lit 370049918515200)), (nat_lit 2228, Int.ofNat (nat_lit 346746384230400))]
theorem block017_data_flat153_step : block017_data_flat153 = (CoefficientMerge.fastMerge block017_data_flat149 block017_data_flat152) := by decide +kernel
theorem block017_data_flat153_original : block017_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (349403855673600 : Int) atom1246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370049918515200 : Int) atom1247Coded) (CoefficientMerge.scale (346746384230400 : Int) atom1248Coded))) := by
  rw [block017_data_flat153_step, block017_data_flat149_original, block017_data_flat152_original]
def block017_data_flat154 : CoefficientMerge.Poly := [(nat_lit 2204, Int.ofNat (nat_lit 510466469990400)), (nat_lit 2205, Int.ofNat (nat_lit 485972244172800)), (nat_lit 2206, Int.ofNat (nat_lit 349403855673600)), (nat_lit 2207, Int.ofNat (nat_lit 370049918515200)), (nat_lit 2228, Int.ofNat (nat_lit 346746384230400))]
theorem block017_data_flat154_step : block017_data_flat154 = (CoefficientMerge.fastMerge block017_data_flat148 block017_data_flat153) := by decide +kernel
theorem block017_data_flat154_original : block017_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (510466469990400 : Int) atom1244Coded) (CoefficientMerge.scale (485972244172800 : Int) atom1245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (349403855673600 : Int) atom1246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370049918515200 : Int) atom1247Coded) (CoefficientMerge.scale (346746384230400 : Int) atom1248Coded)))) := by
  rw [block017_data_flat154_step, block017_data_flat148_original, block017_data_flat153_original]
def block017_data_flat155 : CoefficientMerge.Poly := [(nat_lit 2180, Int.ofNat (nat_lit 637019970048000)), (nat_lit 2181, Int.ofNat (nat_lit 565153231104000)), (nat_lit 2182, Int.ofNat (nat_lit 382207149676800)), (nat_lit 2183, Int.ofNat (nat_lit 528156744192000)), (nat_lit 2203, Int.ofNat (nat_lit 175133714595840)), (nat_lit 2204, Int.ofNat (nat_lit 510466469990400)), (nat_lit 2205, Int.ofNat (nat_lit 485972244172800)), (nat_lit 2206, Int.ofNat (nat_lit 349403855673600)), (nat_lit 2207, Int.ofNat (nat_lit 370049918515200)), (nat_lit 2228, Int.ofNat (nat_lit 346746384230400))]
theorem block017_data_flat155_step : block017_data_flat155 = (CoefficientMerge.fastMerge block017_data_flat145 block017_data_flat154) := by decide +kernel
theorem block017_data_flat155_original : block017_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (637019970048000 : Int) atom1239Coded) (CoefficientMerge.scale (565153231104000 : Int) atom1240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (382207149676800 : Int) atom1241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (528156744192000 : Int) atom1242Coded) (CoefficientMerge.scale (175133714595840 : Int) atom1243Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (510466469990400 : Int) atom1244Coded) (CoefficientMerge.scale (485972244172800 : Int) atom1245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (349403855673600 : Int) atom1246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370049918515200 : Int) atom1247Coded) (CoefficientMerge.scale (346746384230400 : Int) atom1248Coded))))) := by
  rw [block017_data_flat155_step, block017_data_flat145_original, block017_data_flat154_original]
def block017_data_flat156 : CoefficientMerge.Poly := [(nat_lit 2135, Int.ofNat (nat_lit 473555032473600)), (nat_lit 2153, Int.ofNat (nat_lit 238478504140800)), (nat_lit 2154, Int.ofNat (nat_lit 458926536499200)), (nat_lit 2155, Int.ofNat (nat_lit 390716921548800)), (nat_lit 2156, Int.ofNat (nat_lit 548398500249600)), (nat_lit 2157, Int.ofNat (nat_lit 492606096998400)), (nat_lit 2158, Int.ofNat (nat_lit 400409331033600)), (nat_lit 2159, Int.ofNat (nat_lit 514038544588800)), (nat_lit 2178, Int.ofNat (nat_lit 269691632179200)), (nat_lit 2179, Int.ofNat (nat_lit 461307919564800)), (nat_lit 2180, Int.ofNat (nat_lit 637019970048000)), (nat_lit 2181, Int.ofNat (nat_lit 565153231104000)), (nat_lit 2182, Int.ofNat (nat_lit 382207149676800)), (nat_lit 2183, Int.ofNat (nat_lit 528156744192000)), (nat_lit 2203, Int.ofNat (nat_lit 175133714595840)), (nat_lit 2204, Int.ofNat (nat_lit 510466469990400)), (nat_lit 2205, Int.ofNat (nat_lit 485972244172800)), (nat_lit 2206, Int.ofNat (nat_lit 349403855673600)), (nat_lit 2207, Int.ofNat (nat_lit 370049918515200)), (nat_lit 2228, Int.ofNat (nat_lit 346746384230400))]
theorem block017_data_flat156_step : block017_data_flat156 = (CoefficientMerge.fastMerge block017_data_flat136 block017_data_flat155) := by decide +kernel
theorem block017_data_flat156_original : block017_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (473555032473600 : Int) atom1229Coded) (CoefficientMerge.scale (238478504140800 : Int) atom1230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (458926536499200 : Int) atom1231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390716921548800 : Int) atom1232Coded) (CoefficientMerge.scale (548398500249600 : Int) atom1233Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (492606096998400 : Int) atom1234Coded) (CoefficientMerge.scale (400409331033600 : Int) atom1235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (514038544588800 : Int) atom1236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269691632179200 : Int) atom1237Coded) (CoefficientMerge.scale (461307919564800 : Int) atom1238Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (637019970048000 : Int) atom1239Coded) (CoefficientMerge.scale (565153231104000 : Int) atom1240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (382207149676800 : Int) atom1241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (528156744192000 : Int) atom1242Coded) (CoefficientMerge.scale (175133714595840 : Int) atom1243Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (510466469990400 : Int) atom1244Coded) (CoefficientMerge.scale (485972244172800 : Int) atom1245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (349403855673600 : Int) atom1246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370049918515200 : Int) atom1247Coded) (CoefficientMerge.scale (346746384230400 : Int) atom1248Coded)))))) := by
  rw [block017_data_flat156_step, block017_data_flat136_original, block017_data_flat155_original]
def block017_data_flat157 : CoefficientMerge.Poly := [(nat_lit 2084, Int.ofNat (nat_lit 476404187212800)), (nat_lit 2085, Int.ofNat (nat_lit 408364671052800)), (nat_lit 2086, Int.ofNat (nat_lit 433640731154400)), (nat_lit 2087, Int.ofNat (nat_lit 471496571330400)), (nat_lit 2103, Int.ofNat (nat_lit 250122539520000)), (nat_lit 2104, Int.ofNat (nat_lit 440950187059200)), (nat_lit 2105, Int.ofNat (nat_lit 404940788582400)), (nat_lit 2106, Int.ofNat (nat_lit 436401333043200)), (nat_lit 2107, Int.ofNat (nat_lit 360026976153600)), (nat_lit 2108, Int.ofNat (nat_lit 509543812915200)), (nat_lit 2109, Int.ofNat (nat_lit 445586667724800)), (nat_lit 2110, Int.ofNat (nat_lit 404141839718400)), (nat_lit 2111, Int.ofNat (nat_lit 433071520358400)), (nat_lit 2128, Int.ofNat (nat_lit 241176889497600)), (nat_lit 2129, Int.ofNat (nat_lit 434097267609600)), (nat_lit 2130, Int.ofNat (nat_lit 437731196313600)), (nat_lit 2131, Int.ofNat (nat_lit 365439210393600)), (nat_lit 2132, Int.ofNat (nat_lit 519038418124800)), (nat_lit 2133, Int.ofNat (nat_lit 459163643904000)), (nat_lit 2134, Int.ofNat (nat_lit 364008189888000)), (nat_lit 2135, Int.ofNat (nat_lit 473555032473600)), (nat_lit 2153, Int.ofNat (nat_lit 238478504140800)), (nat_lit 2154, Int.ofNat (nat_lit 458926536499200)), (nat_lit 2155, Int.ofNat (nat_lit 390716921548800)), (nat_lit 2156, Int.ofNat (nat_lit 548398500249600)), (nat_lit 2157, Int.ofNat (nat_lit 492606096998400)), (nat_lit 2158, Int.ofNat (nat_lit 400409331033600)), (nat_lit 2159, Int.ofNat (nat_lit 514038544588800)), (nat_lit 2178, Int.ofNat (nat_lit 269691632179200)), (nat_lit 2179, Int.ofNat (nat_lit 461307919564800)), (nat_lit 2180, Int.ofNat (nat_lit 637019970048000)), (nat_lit 2181, Int.ofNat (nat_lit 565153231104000)), (nat_lit 2182, Int.ofNat (nat_lit 382207149676800)), (nat_lit 2183, Int.ofNat (nat_lit 528156744192000)), (nat_lit 2203, Int.ofNat (nat_lit 175133714595840)), (nat_lit 2204, Int.ofNat (nat_lit 510466469990400)), (nat_lit 2205, Int.ofNat (nat_lit 485972244172800)), (nat_lit 2206, Int.ofNat (nat_lit 349403855673600)), (nat_lit 2207, Int.ofNat (nat_lit 370049918515200)), (nat_lit 2228, Int.ofNat (nat_lit 346746384230400))]
theorem block017_data_flat157_step : block017_data_flat157 = (CoefficientMerge.fastMerge block017_data_flat117 block017_data_flat156) := by decide +kernel
theorem block017_data_flat157_original : block017_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (476404187212800 : Int) atom1209Coded) (CoefficientMerge.scale (408364671052800 : Int) atom1210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (433640731154400 : Int) atom1211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (471496571330400 : Int) atom1212Coded) (CoefficientMerge.scale (250122539520000 : Int) atom1213Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (440950187059200 : Int) atom1214Coded) (CoefficientMerge.scale (404940788582400 : Int) atom1215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436401333043200 : Int) atom1216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360026976153600 : Int) atom1217Coded) (CoefficientMerge.scale (509543812915200 : Int) atom1218Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (445586667724800 : Int) atom1219Coded) (CoefficientMerge.scale (404141839718400 : Int) atom1220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (433071520358400 : Int) atom1221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241176889497600 : Int) atom1222Coded) (CoefficientMerge.scale (434097267609600 : Int) atom1223Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (437731196313600 : Int) atom1224Coded) (CoefficientMerge.scale (365439210393600 : Int) atom1225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519038418124800 : Int) atom1226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (459163643904000 : Int) atom1227Coded) (CoefficientMerge.scale (364008189888000 : Int) atom1228Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (473555032473600 : Int) atom1229Coded) (CoefficientMerge.scale (238478504140800 : Int) atom1230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (458926536499200 : Int) atom1231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390716921548800 : Int) atom1232Coded) (CoefficientMerge.scale (548398500249600 : Int) atom1233Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (492606096998400 : Int) atom1234Coded) (CoefficientMerge.scale (400409331033600 : Int) atom1235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (514038544588800 : Int) atom1236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269691632179200 : Int) atom1237Coded) (CoefficientMerge.scale (461307919564800 : Int) atom1238Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (637019970048000 : Int) atom1239Coded) (CoefficientMerge.scale (565153231104000 : Int) atom1240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (382207149676800 : Int) atom1241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (528156744192000 : Int) atom1242Coded) (CoefficientMerge.scale (175133714595840 : Int) atom1243Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (510466469990400 : Int) atom1244Coded) (CoefficientMerge.scale (485972244172800 : Int) atom1245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (349403855673600 : Int) atom1246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370049918515200 : Int) atom1247Coded) (CoefficientMerge.scale (346746384230400 : Int) atom1248Coded))))))) := by
  rw [block017_data_flat157_step, block017_data_flat117_original, block017_data_flat156_original]
def block017_data_flat158 : CoefficientMerge.Poly := [(nat_lit 2005, Int.ofNat (nat_lit 355486091647104)), (nat_lit 2006, Int.ofNat (nat_lit 329946779695104)), (nat_lit 2007, Int.ofNat (nat_lit 319194474338304)), (nat_lit 2008, Int.ofNat (nat_lit 299702699311104)), (nat_lit 2009, Int.ofNat (nat_lit 290143662741504)), (nat_lit 2010, Int.ofNat (nat_lit 337360560787008)), (nat_lit 2011, Int.ofNat (nat_lit 304119222359040)), (nat_lit 2012, Int.ofNat (nat_lit 377844072902208)), (nat_lit 2013, Int.ofNat (nat_lit 389393633958912)), (nat_lit 2014, Int.ofNat (nat_lit 447547332418560)), (nat_lit 2015, Int.ofNat (nat_lit 505701030878208)), (nat_lit 2028, Int.ofNat (nat_lit 230328777469824)), (nat_lit 2029, Int.ofNat (nat_lit 424979952465024)), (nat_lit 2030, Int.ofNat (nat_lit 397441979725824)), (nat_lit 2031, Int.ofNat (nat_lit 384691013581824)), (nat_lit 2032, Int.ofNat (nat_lit 360117537191424)), (nat_lit 2033, Int.ofNat (nat_lit 345476799258624)), (nat_lit 2034, Int.ofNat (nat_lit 413276182501248)), (nat_lit 2035, Int.ofNat (nat_lit 340052591831040)), (nat_lit 2036, Int.ofNat (nat_lit 461924436555648)), (nat_lit 2037, Int.ofNat (nat_lit 396690872067072)), (nat_lit 2038, Int.ofNat (nat_lit 437447716738560)), (nat_lit 2039, Int.ofNat (nat_lit 478204561410048)), (nat_lit 2053, Int.ofNat (nat_lit 238834335801600)), (nat_lit 2054, Int.ofNat (nat_lit 431701558041600)), (nat_lit 2055, Int.ofNat (nat_lit 409765257216000)), (nat_lit 2056, Int.ofNat (nat_lit 379089486720000)), (nat_lit 2057, Int.ofNat (nat_lit 358346454681600)), (nat_lit 2058, Int.ofNat (nat_lit 416025578707200)), (nat_lit 2059, Int.ofNat (nat_lit 345906104544000)), (nat_lit 2060, Int.ofNat (nat_lit 472838574700800)), (nat_lit 2061, Int.ofNat (nat_lit 400716687571200)), (nat_lit 2062, Int.ofNat (nat_lit 442289165472000)), (nat_lit 2063, Int.ofNat (nat_lit 483861643372800)), (nat_lit 2078, Int.ofNat (nat_lit 237050383046400)), (nat_lit 2079, Int.ofNat (nat_lit 439906721184000)), (nat_lit 2080, Int.ofNat (nat_lit 402108063840000)), (nat_lit 2081, Int.ofNat (nat_lit 374242144953600)), (nat_lit 2082, Int.ofNat (nat_lit 411426449280000)), (nat_lit 2083, Int.ofNat (nat_lit 350110707962400)), (nat_lit 2084, Int.ofNat (nat_lit 476404187212800)), (nat_lit 2085, Int.ofNat (nat_lit 408364671052800)), (nat_lit 2086, Int.ofNat (nat_lit 433640731154400)), (nat_lit 2087, Int.ofNat (nat_lit 471496571330400)), (nat_lit 2103, Int.ofNat (nat_lit 250122539520000)), (nat_lit 2104, Int.ofNat (nat_lit 440950187059200)), (nat_lit 2105, Int.ofNat (nat_lit 404940788582400)), (nat_lit 2106, Int.ofNat (nat_lit 436401333043200)), (nat_lit 2107, Int.ofNat (nat_lit 360026976153600)), (nat_lit 2108, Int.ofNat (nat_lit 509543812915200)), (nat_lit 2109, Int.ofNat (nat_lit 445586667724800)), (nat_lit 2110, Int.ofNat (nat_lit 404141839718400)), (nat_lit 2111, Int.ofNat (nat_lit 433071520358400)), (nat_lit 2128, Int.ofNat (nat_lit 241176889497600)), (nat_lit 2129, Int.ofNat (nat_lit 434097267609600)), (nat_lit 2130, Int.ofNat (nat_lit 437731196313600)), (nat_lit 2131, Int.ofNat (nat_lit 365439210393600)), (nat_lit 2132, Int.ofNat (nat_lit 519038418124800)), (nat_lit 2133, Int.ofNat (nat_lit 459163643904000)), (nat_lit 2134, Int.ofNat (nat_lit 364008189888000)), (nat_lit 2135, Int.ofNat (nat_lit 473555032473600)), (nat_lit 2153, Int.ofNat (nat_lit 238478504140800)), (nat_lit 2154, Int.ofNat (nat_lit 458926536499200)), (nat_lit 2155, Int.ofNat (nat_lit 390716921548800)), (nat_lit 2156, Int.ofNat (nat_lit 548398500249600)), (nat_lit 2157, Int.ofNat (nat_lit 492606096998400)), (nat_lit 2158, Int.ofNat (nat_lit 400409331033600)), (nat_lit 2159, Int.ofNat (nat_lit 514038544588800)), (nat_lit 2178, Int.ofNat (nat_lit 269691632179200)), (nat_lit 2179, Int.ofNat (nat_lit 461307919564800)), (nat_lit 2180, Int.ofNat (nat_lit 637019970048000)), (nat_lit 2181, Int.ofNat (nat_lit 565153231104000)), (nat_lit 2182, Int.ofNat (nat_lit 382207149676800)), (nat_lit 2183, Int.ofNat (nat_lit 528156744192000)), (nat_lit 2203, Int.ofNat (nat_lit 175133714595840)), (nat_lit 2204, Int.ofNat (nat_lit 510466469990400)), (nat_lit 2205, Int.ofNat (nat_lit 485972244172800)), (nat_lit 2206, Int.ofNat (nat_lit 349403855673600)), (nat_lit 2207, Int.ofNat (nat_lit 370049918515200)), (nat_lit 2228, Int.ofNat (nat_lit 346746384230400))]
theorem block017_data_flat158_step : block017_data_flat158 = (CoefficientMerge.fastMerge block017_data_flat078 block017_data_flat157) := by decide +kernel
theorem block017_data_flat158_original : block017_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (355486091647104 : Int) atom1169Coded) (CoefficientMerge.scale (329946779695104 : Int) atom1170Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (319194474338304 : Int) atom1171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299702699311104 : Int) atom1172Coded) (CoefficientMerge.scale (290143662741504 : Int) atom1173Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337360560787008 : Int) atom1174Coded) (CoefficientMerge.scale (304119222359040 : Int) atom1175Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377844072902208 : Int) atom1176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (389393633958912 : Int) atom1177Coded) (CoefficientMerge.scale (447547332418560 : Int) atom1178Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (505701030878208 : Int) atom1179Coded) (CoefficientMerge.scale (230328777469824 : Int) atom1180Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (424979952465024 : Int) atom1181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (397441979725824 : Int) atom1182Coded) (CoefficientMerge.scale (384691013581824 : Int) atom1183Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (360117537191424 : Int) atom1184Coded) (CoefficientMerge.scale (345476799258624 : Int) atom1185Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413276182501248 : Int) atom1186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (340052591831040 : Int) atom1187Coded) (CoefficientMerge.scale (461924436555648 : Int) atom1188Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (396690872067072 : Int) atom1189Coded) (CoefficientMerge.scale (437447716738560 : Int) atom1190Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (478204561410048 : Int) atom1191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (238834335801600 : Int) atom1192Coded) (CoefficientMerge.scale (431701558041600 : Int) atom1193Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (409765257216000 : Int) atom1194Coded) (CoefficientMerge.scale (379089486720000 : Int) atom1195Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358346454681600 : Int) atom1196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416025578707200 : Int) atom1197Coded) (CoefficientMerge.scale (345906104544000 : Int) atom1198Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (472838574700800 : Int) atom1199Coded) (CoefficientMerge.scale (400716687571200 : Int) atom1200Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (442289165472000 : Int) atom1201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (483861643372800 : Int) atom1202Coded) (CoefficientMerge.scale (237050383046400 : Int) atom1203Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (439906721184000 : Int) atom1204Coded) (CoefficientMerge.scale (402108063840000 : Int) atom1205Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (374242144953600 : Int) atom1206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411426449280000 : Int) atom1207Coded) (CoefficientMerge.scale (350110707962400 : Int) atom1208Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (476404187212800 : Int) atom1209Coded) (CoefficientMerge.scale (408364671052800 : Int) atom1210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (433640731154400 : Int) atom1211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (471496571330400 : Int) atom1212Coded) (CoefficientMerge.scale (250122539520000 : Int) atom1213Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (440950187059200 : Int) atom1214Coded) (CoefficientMerge.scale (404940788582400 : Int) atom1215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436401333043200 : Int) atom1216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360026976153600 : Int) atom1217Coded) (CoefficientMerge.scale (509543812915200 : Int) atom1218Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (445586667724800 : Int) atom1219Coded) (CoefficientMerge.scale (404141839718400 : Int) atom1220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (433071520358400 : Int) atom1221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241176889497600 : Int) atom1222Coded) (CoefficientMerge.scale (434097267609600 : Int) atom1223Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (437731196313600 : Int) atom1224Coded) (CoefficientMerge.scale (365439210393600 : Int) atom1225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519038418124800 : Int) atom1226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (459163643904000 : Int) atom1227Coded) (CoefficientMerge.scale (364008189888000 : Int) atom1228Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (473555032473600 : Int) atom1229Coded) (CoefficientMerge.scale (238478504140800 : Int) atom1230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (458926536499200 : Int) atom1231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390716921548800 : Int) atom1232Coded) (CoefficientMerge.scale (548398500249600 : Int) atom1233Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (492606096998400 : Int) atom1234Coded) (CoefficientMerge.scale (400409331033600 : Int) atom1235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (514038544588800 : Int) atom1236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269691632179200 : Int) atom1237Coded) (CoefficientMerge.scale (461307919564800 : Int) atom1238Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (637019970048000 : Int) atom1239Coded) (CoefficientMerge.scale (565153231104000 : Int) atom1240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (382207149676800 : Int) atom1241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (528156744192000 : Int) atom1242Coded) (CoefficientMerge.scale (175133714595840 : Int) atom1243Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (510466469990400 : Int) atom1244Coded) (CoefficientMerge.scale (485972244172800 : Int) atom1245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (349403855673600 : Int) atom1246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370049918515200 : Int) atom1247Coded) (CoefficientMerge.scale (346746384230400 : Int) atom1248Coded)))))))) := by
  rw [block017_data_flat158_step, block017_data_flat078_original, block017_data_flat157_original]
def block017_data_flat159 : CoefficientMerge.Poly := [(nat_lit 2005, Int.ofNat (nat_lit 355486091647104)), (nat_lit 2006, Int.ofNat (nat_lit 329946779695104)), (nat_lit 2007, Int.ofNat (nat_lit 319194474338304)), (nat_lit 2008, Int.ofNat (nat_lit 299702699311104)), (nat_lit 2009, Int.ofNat (nat_lit 290143662741504)), (nat_lit 2010, Int.ofNat (nat_lit 337360560787008)), (nat_lit 2011, Int.ofNat (nat_lit 304119222359040)), (nat_lit 2012, Int.ofNat (nat_lit 377844072902208)), (nat_lit 2013, Int.ofNat (nat_lit 389393633958912)), (nat_lit 2014, Int.ofNat (nat_lit 447547332418560)), (nat_lit 2015, Int.ofNat (nat_lit 505701030878208)), (nat_lit 2028, Int.ofNat (nat_lit 230328777469824)), (nat_lit 2029, Int.ofNat (nat_lit 424979952465024)), (nat_lit 2030, Int.ofNat (nat_lit 397441979725824)), (nat_lit 2031, Int.ofNat (nat_lit 384691013581824)), (nat_lit 2032, Int.ofNat (nat_lit 360117537191424)), (nat_lit 2033, Int.ofNat (nat_lit 345476799258624)), (nat_lit 2034, Int.ofNat (nat_lit 413276182501248)), (nat_lit 2035, Int.ofNat (nat_lit 340052591831040)), (nat_lit 2036, Int.ofNat (nat_lit 461924436555648)), (nat_lit 2037, Int.ofNat (nat_lit 396690872067072)), (nat_lit 2038, Int.ofNat (nat_lit 437447716738560)), (nat_lit 2039, Int.ofNat (nat_lit 478204561410048)), (nat_lit 2053, Int.ofNat (nat_lit 238834335801600)), (nat_lit 2054, Int.ofNat (nat_lit 431701558041600)), (nat_lit 2055, Int.ofNat (nat_lit 409765257216000)), (nat_lit 2056, Int.ofNat (nat_lit 379089486720000)), (nat_lit 2057, Int.ofNat (nat_lit 358346454681600)), (nat_lit 2058, Int.ofNat (nat_lit 416025578707200)), (nat_lit 2059, Int.ofNat (nat_lit 345906104544000)), (nat_lit 2060, Int.ofNat (nat_lit 472838574700800)), (nat_lit 2061, Int.ofNat (nat_lit 400716687571200)), (nat_lit 2062, Int.ofNat (nat_lit 442289165472000)), (nat_lit 2063, Int.ofNat (nat_lit 483861643372800)), (nat_lit 2078, Int.ofNat (nat_lit 237050383046400)), (nat_lit 2079, Int.ofNat (nat_lit 439906721184000)), (nat_lit 2080, Int.ofNat (nat_lit 402108063840000)), (nat_lit 2081, Int.ofNat (nat_lit 374242144953600)), (nat_lit 2082, Int.ofNat (nat_lit 411426449280000)), (nat_lit 2083, Int.ofNat (nat_lit 350110707962400)), (nat_lit 2084, Int.ofNat (nat_lit 476404187212800)), (nat_lit 2085, Int.ofNat (nat_lit 408364671052800)), (nat_lit 2086, Int.ofNat (nat_lit 433640731154400)), (nat_lit 2087, Int.ofNat (nat_lit 471496571330400)), (nat_lit 2103, Int.ofNat (nat_lit 250122539520000)), (nat_lit 2104, Int.ofNat (nat_lit 440950187059200)), (nat_lit 2105, Int.ofNat (nat_lit 404940788582400)), (nat_lit 2106, Int.ofNat (nat_lit 436401333043200)), (nat_lit 2107, Int.ofNat (nat_lit 360026976153600)), (nat_lit 2108, Int.ofNat (nat_lit 509543812915200)), (nat_lit 2109, Int.ofNat (nat_lit 445586667724800)), (nat_lit 2110, Int.ofNat (nat_lit 404141839718400)), (nat_lit 2111, Int.ofNat (nat_lit 433071520358400)), (nat_lit 2128, Int.ofNat (nat_lit 241176889497600)), (nat_lit 2129, Int.ofNat (nat_lit 434097267609600)), (nat_lit 2130, Int.ofNat (nat_lit 437731196313600)), (nat_lit 2131, Int.ofNat (nat_lit 365439210393600)), (nat_lit 2132, Int.ofNat (nat_lit 519038418124800)), (nat_lit 2133, Int.ofNat (nat_lit 459163643904000)), (nat_lit 2134, Int.ofNat (nat_lit 364008189888000)), (nat_lit 2135, Int.ofNat (nat_lit 473555032473600)), (nat_lit 2153, Int.ofNat (nat_lit 238478504140800)), (nat_lit 2154, Int.ofNat (nat_lit 458926536499200)), (nat_lit 2155, Int.ofNat (nat_lit 390716921548800)), (nat_lit 2156, Int.ofNat (nat_lit 548398500249600)), (nat_lit 2157, Int.ofNat (nat_lit 492606096998400)), (nat_lit 2158, Int.ofNat (nat_lit 400409331033600)), (nat_lit 2159, Int.ofNat (nat_lit 514038544588800)), (nat_lit 2178, Int.ofNat (nat_lit 269691632179200)), (nat_lit 2179, Int.ofNat (nat_lit 461307919564800)), (nat_lit 2180, Int.ofNat (nat_lit 637019970048000)), (nat_lit 2181, Int.ofNat (nat_lit 565153231104000)), (nat_lit 2182, Int.ofNat (nat_lit 382207149676800)), (nat_lit 2183, Int.ofNat (nat_lit 528156744192000)), (nat_lit 2203, Int.ofNat (nat_lit 175133714595840)), (nat_lit 2204, Int.ofNat (nat_lit 510466469990400)), (nat_lit 2205, Int.ofNat (nat_lit 485972244172800)), (nat_lit 2206, Int.ofNat (nat_lit 349403855673600)), (nat_lit 2207, Int.ofNat (nat_lit 370049918515200)), (nat_lit 2228, Int.ofNat (nat_lit 346746384230400))]
theorem block017_data_flat159_step : block017_data_flat159 = (CoefficientMerge.trim block017_data_flat158) := by decide +kernel
theorem block017_data_flat159_original : block017_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (355486091647104 : Int) atom1169Coded) (CoefficientMerge.scale (329946779695104 : Int) atom1170Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (319194474338304 : Int) atom1171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299702699311104 : Int) atom1172Coded) (CoefficientMerge.scale (290143662741504 : Int) atom1173Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337360560787008 : Int) atom1174Coded) (CoefficientMerge.scale (304119222359040 : Int) atom1175Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377844072902208 : Int) atom1176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (389393633958912 : Int) atom1177Coded) (CoefficientMerge.scale (447547332418560 : Int) atom1178Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (505701030878208 : Int) atom1179Coded) (CoefficientMerge.scale (230328777469824 : Int) atom1180Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (424979952465024 : Int) atom1181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (397441979725824 : Int) atom1182Coded) (CoefficientMerge.scale (384691013581824 : Int) atom1183Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (360117537191424 : Int) atom1184Coded) (CoefficientMerge.scale (345476799258624 : Int) atom1185Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413276182501248 : Int) atom1186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (340052591831040 : Int) atom1187Coded) (CoefficientMerge.scale (461924436555648 : Int) atom1188Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (396690872067072 : Int) atom1189Coded) (CoefficientMerge.scale (437447716738560 : Int) atom1190Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (478204561410048 : Int) atom1191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (238834335801600 : Int) atom1192Coded) (CoefficientMerge.scale (431701558041600 : Int) atom1193Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (409765257216000 : Int) atom1194Coded) (CoefficientMerge.scale (379089486720000 : Int) atom1195Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358346454681600 : Int) atom1196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416025578707200 : Int) atom1197Coded) (CoefficientMerge.scale (345906104544000 : Int) atom1198Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (472838574700800 : Int) atom1199Coded) (CoefficientMerge.scale (400716687571200 : Int) atom1200Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (442289165472000 : Int) atom1201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (483861643372800 : Int) atom1202Coded) (CoefficientMerge.scale (237050383046400 : Int) atom1203Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (439906721184000 : Int) atom1204Coded) (CoefficientMerge.scale (402108063840000 : Int) atom1205Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (374242144953600 : Int) atom1206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411426449280000 : Int) atom1207Coded) (CoefficientMerge.scale (350110707962400 : Int) atom1208Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (476404187212800 : Int) atom1209Coded) (CoefficientMerge.scale (408364671052800 : Int) atom1210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (433640731154400 : Int) atom1211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (471496571330400 : Int) atom1212Coded) (CoefficientMerge.scale (250122539520000 : Int) atom1213Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (440950187059200 : Int) atom1214Coded) (CoefficientMerge.scale (404940788582400 : Int) atom1215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436401333043200 : Int) atom1216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360026976153600 : Int) atom1217Coded) (CoefficientMerge.scale (509543812915200 : Int) atom1218Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (445586667724800 : Int) atom1219Coded) (CoefficientMerge.scale (404141839718400 : Int) atom1220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (433071520358400 : Int) atom1221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241176889497600 : Int) atom1222Coded) (CoefficientMerge.scale (434097267609600 : Int) atom1223Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (437731196313600 : Int) atom1224Coded) (CoefficientMerge.scale (365439210393600 : Int) atom1225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519038418124800 : Int) atom1226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (459163643904000 : Int) atom1227Coded) (CoefficientMerge.scale (364008189888000 : Int) atom1228Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (473555032473600 : Int) atom1229Coded) (CoefficientMerge.scale (238478504140800 : Int) atom1230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (458926536499200 : Int) atom1231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390716921548800 : Int) atom1232Coded) (CoefficientMerge.scale (548398500249600 : Int) atom1233Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (492606096998400 : Int) atom1234Coded) (CoefficientMerge.scale (400409331033600 : Int) atom1235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (514038544588800 : Int) atom1236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269691632179200 : Int) atom1237Coded) (CoefficientMerge.scale (461307919564800 : Int) atom1238Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (637019970048000 : Int) atom1239Coded) (CoefficientMerge.scale (565153231104000 : Int) atom1240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (382207149676800 : Int) atom1241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (528156744192000 : Int) atom1242Coded) (CoefficientMerge.scale (175133714595840 : Int) atom1243Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (510466469990400 : Int) atom1244Coded) (CoefficientMerge.scale (485972244172800 : Int) atom1245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (349403855673600 : Int) atom1246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370049918515200 : Int) atom1247Coded) (CoefficientMerge.scale (346746384230400 : Int) atom1248Coded))))))))) := by
  rw [block017_data_flat159_step, block017_data_flat158_original]
theorem block017_data : block017 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (355486091647104 : Int) atom1169Coded) (CoefficientMerge.scale (329946779695104 : Int) atom1170Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (319194474338304 : Int) atom1171Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (299702699311104 : Int) atom1172Coded) (CoefficientMerge.scale (290143662741504 : Int) atom1173Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (337360560787008 : Int) atom1174Coded) (CoefficientMerge.scale (304119222359040 : Int) atom1175Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (377844072902208 : Int) atom1176Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (389393633958912 : Int) atom1177Coded) (CoefficientMerge.scale (447547332418560 : Int) atom1178Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (505701030878208 : Int) atom1179Coded) (CoefficientMerge.scale (230328777469824 : Int) atom1180Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (424979952465024 : Int) atom1181Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (397441979725824 : Int) atom1182Coded) (CoefficientMerge.scale (384691013581824 : Int) atom1183Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (360117537191424 : Int) atom1184Coded) (CoefficientMerge.scale (345476799258624 : Int) atom1185Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (413276182501248 : Int) atom1186Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (340052591831040 : Int) atom1187Coded) (CoefficientMerge.scale (461924436555648 : Int) atom1188Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (396690872067072 : Int) atom1189Coded) (CoefficientMerge.scale (437447716738560 : Int) atom1190Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (478204561410048 : Int) atom1191Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (238834335801600 : Int) atom1192Coded) (CoefficientMerge.scale (431701558041600 : Int) atom1193Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (409765257216000 : Int) atom1194Coded) (CoefficientMerge.scale (379089486720000 : Int) atom1195Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (358346454681600 : Int) atom1196Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (416025578707200 : Int) atom1197Coded) (CoefficientMerge.scale (345906104544000 : Int) atom1198Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (472838574700800 : Int) atom1199Coded) (CoefficientMerge.scale (400716687571200 : Int) atom1200Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (442289165472000 : Int) atom1201Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (483861643372800 : Int) atom1202Coded) (CoefficientMerge.scale (237050383046400 : Int) atom1203Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (439906721184000 : Int) atom1204Coded) (CoefficientMerge.scale (402108063840000 : Int) atom1205Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (374242144953600 : Int) atom1206Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (411426449280000 : Int) atom1207Coded) (CoefficientMerge.scale (350110707962400 : Int) atom1208Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (476404187212800 : Int) atom1209Coded) (CoefficientMerge.scale (408364671052800 : Int) atom1210Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (433640731154400 : Int) atom1211Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (471496571330400 : Int) atom1212Coded) (CoefficientMerge.scale (250122539520000 : Int) atom1213Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (440950187059200 : Int) atom1214Coded) (CoefficientMerge.scale (404940788582400 : Int) atom1215Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (436401333043200 : Int) atom1216Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (360026976153600 : Int) atom1217Coded) (CoefficientMerge.scale (509543812915200 : Int) atom1218Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (445586667724800 : Int) atom1219Coded) (CoefficientMerge.scale (404141839718400 : Int) atom1220Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (433071520358400 : Int) atom1221Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (241176889497600 : Int) atom1222Coded) (CoefficientMerge.scale (434097267609600 : Int) atom1223Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (437731196313600 : Int) atom1224Coded) (CoefficientMerge.scale (365439210393600 : Int) atom1225Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (519038418124800 : Int) atom1226Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (459163643904000 : Int) atom1227Coded) (CoefficientMerge.scale (364008189888000 : Int) atom1228Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (473555032473600 : Int) atom1229Coded) (CoefficientMerge.scale (238478504140800 : Int) atom1230Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (458926536499200 : Int) atom1231Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (390716921548800 : Int) atom1232Coded) (CoefficientMerge.scale (548398500249600 : Int) atom1233Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (492606096998400 : Int) atom1234Coded) (CoefficientMerge.scale (400409331033600 : Int) atom1235Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (514038544588800 : Int) atom1236Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (269691632179200 : Int) atom1237Coded) (CoefficientMerge.scale (461307919564800 : Int) atom1238Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (637019970048000 : Int) atom1239Coded) (CoefficientMerge.scale (565153231104000 : Int) atom1240Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (382207149676800 : Int) atom1241Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (528156744192000 : Int) atom1242Coded) (CoefficientMerge.scale (175133714595840 : Int) atom1243Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (510466469990400 : Int) atom1244Coded) (CoefficientMerge.scale (485972244172800 : Int) atom1245Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (349403855673600 : Int) atom1246Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (370049918515200 : Int) atom1247Coded) (CoefficientMerge.scale (346746384230400 : Int) atom1248Coded)))))))) := by
  have h : block017 = block017_data_flat159 := by decide +kernel
  exact h.trans block017_data_flat159_original
theorem block017_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 24) block017 := by
  rw [block017_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1169Coded_nonneg g hg hA hB) (atom1170Coded_nonneg g hg hA hB)) (add_nonneg (atom1171Coded_nonneg g hg hA hB) (add_nonneg (atom1172Coded_nonneg g hg hA hB) (atom1173Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1174Coded_nonneg g hg hA hB) (atom1175Coded_nonneg g hg hA hB)) (add_nonneg (atom1176Coded_nonneg g hg hA hB) (add_nonneg (atom1177Coded_nonneg g hg hA hB) (atom1178Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1179Coded_nonneg g hg hA hB) (atom1180Coded_nonneg g hg hA hB)) (add_nonneg (atom1181Coded_nonneg g hg hA hB) (add_nonneg (atom1182Coded_nonneg g hg hA hB) (atom1183Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1184Coded_nonneg g hg hA hB) (atom1185Coded_nonneg g hg hA hB)) (add_nonneg (atom1186Coded_nonneg g hg hA hB) (add_nonneg (atom1187Coded_nonneg g hg hA hB) (atom1188Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1189Coded_nonneg g hg hA hB) (atom1190Coded_nonneg g hg hA hB)) (add_nonneg (atom1191Coded_nonneg g hg hA hB) (add_nonneg (atom1192Coded_nonneg g hg hA hB) (atom1193Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1194Coded_nonneg g hg hA hB) (atom1195Coded_nonneg g hg hA hB)) (add_nonneg (atom1196Coded_nonneg g hg hA hB) (add_nonneg (atom1197Coded_nonneg g hg hA hB) (atom1198Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1199Coded_nonneg g hg hA hB) (atom1200Coded_nonneg g hg hA hB)) (add_nonneg (atom1201Coded_nonneg g hg hA hB) (add_nonneg (atom1202Coded_nonneg g hg hA hB) (atom1203Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1204Coded_nonneg g hg hA hB) (atom1205Coded_nonneg g hg hA hB)) (add_nonneg (atom1206Coded_nonneg g hg hA hB) (add_nonneg (atom1207Coded_nonneg g hg hA hB) (atom1208Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1209Coded_nonneg g hg hA hB) (atom1210Coded_nonneg g hg hA hB)) (add_nonneg (atom1211Coded_nonneg g hg hA hB) (add_nonneg (atom1212Coded_nonneg g hg hA hB) (atom1213Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1214Coded_nonneg g hg hA hB) (atom1215Coded_nonneg g hg hA hB)) (add_nonneg (atom1216Coded_nonneg g hg hA hB) (add_nonneg (atom1217Coded_nonneg g hg hA hB) (atom1218Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1219Coded_nonneg g hg hA hB) (atom1220Coded_nonneg g hg hA hB)) (add_nonneg (atom1221Coded_nonneg g hg hA hB) (add_nonneg (atom1222Coded_nonneg g hg hA hB) (atom1223Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1224Coded_nonneg g hg hA hB) (atom1225Coded_nonneg g hg hA hB)) (add_nonneg (atom1226Coded_nonneg g hg hA hB) (add_nonneg (atom1227Coded_nonneg g hg hA hB) (atom1228Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1229Coded_nonneg g hg hA hB) (atom1230Coded_nonneg g hg hA hB)) (add_nonneg (atom1231Coded_nonneg g hg hA hB) (add_nonneg (atom1232Coded_nonneg g hg hA hB) (atom1233Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1234Coded_nonneg g hg hA hB) (atom1235Coded_nonneg g hg hA hB)) (add_nonneg (atom1236Coded_nonneg g hg hA hB) (add_nonneg (atom1237Coded_nonneg g hg hA hB) (atom1238Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1239Coded_nonneg g hg hA hB) (atom1240Coded_nonneg g hg hA hB)) (add_nonneg (atom1241Coded_nonneg g hg hA hB) (add_nonneg (atom1242Coded_nonneg g hg hA hB) (atom1243Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1244Coded_nonneg g hg hA hB) (atom1245Coded_nonneg g hg hA hB)) (add_nonneg (atom1246Coded_nonneg g hg hA hB) (add_nonneg (atom1247Coded_nonneg g hg hA hB) (atom1248Coded_nonneg g hg hA hB))))))))

end APPT.Finite24
