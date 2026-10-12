-- FLAT_COEFFICIENT_MERGES_V1: kernel-checked literal barriers.
import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1136 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1136 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1136 = ((g 5) * (g 11) * (g 13)) := by
  norm_num [atom1136, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1136_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20238042645504 : Int) atom1136) := by
  rw [SparsePolynomial.eval_scale, eval_atom1136]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1136Coded : CoefficientMerge.Poly := [(nat_lit 2449, Int.ofNat (nat_lit 1))]
theorem atom1136Coded_decode : atom1136 = SparsePolynomial.decodeCubic 21 atom1136Coded := by decide +kernel
theorem atom1136Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20238042645504 : Int) atom1136Coded) := by
  have h := atom1136_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1136Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1137 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1137 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1137 = ((g 5) * (g 11) * (g 14)) := by
  norm_num [atom1137, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1137_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20278634402304 : Int) atom1137) := by
  rw [SparsePolynomial.eval_scale, eval_atom1137]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1137Coded : CoefficientMerge.Poly := [(nat_lit 2450, Int.ofNat (nat_lit 1))]
theorem atom1137Coded_decode : atom1137 = SparsePolynomial.decodeCubic 21 atom1137Coded := by decide +kernel
theorem atom1137Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20278634402304 : Int) atom1137Coded) := by
  have h := atom1137_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1137Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1138 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1138 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1138 = ((g 5) * (g 11) * (g 15)) := by
  norm_num [atom1138, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1138_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29238383522304 : Int) atom1138) := by
  rw [SparsePolynomial.eval_scale, eval_atom1138]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1138Coded : CoefficientMerge.Poly := [(nat_lit 2451, Int.ofNat (nat_lit 1))]
theorem atom1138Coded_decode : atom1138 = SparsePolynomial.decodeCubic 21 atom1138Coded := by decide +kernel
theorem atom1138Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29238383522304 : Int) atom1138Coded) := by
  have h := atom1138_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1138Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1139 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1139 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1139 = ((g 5) * (g 11) * (g 16)) := by
  norm_num [atom1139, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1139_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26787755370240 : Int) atom1139) := by
  rw [SparsePolynomial.eval_scale, eval_atom1139]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1139Coded : CoefficientMerge.Poly := [(nat_lit 2452, Int.ofNat (nat_lit 1))]
theorem atom1139Coded_decode : atom1139 = SparsePolynomial.decodeCubic 21 atom1139Coded := by decide +kernel
theorem atom1139Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26787755370240 : Int) atom1139Coded) := by
  have h := atom1139_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1139Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1140 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1140 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1140 = ((g 5) * (g 11) * (g 17)) := by
  norm_num [atom1140, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1140_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39115299746304 : Int) atom1140) := by
  rw [SparsePolynomial.eval_scale, eval_atom1140]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1140Coded : CoefficientMerge.Poly := [(nat_lit 2453, Int.ofNat (nat_lit 1))]
theorem atom1140Coded_decode : atom1140 = SparsePolynomial.decodeCubic 21 atom1140Coded := by decide +kernel
theorem atom1140Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39115299746304 : Int) atom1140Coded) := by
  have h := atom1140_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1140Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1141 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1141 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1141 = ((g 5) * (g 11) * (g 18)) := by
  norm_num [atom1141, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1141_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39724813792512 : Int) atom1141) := by
  rw [SparsePolynomial.eval_scale, eval_atom1141]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1141Coded : CoefficientMerge.Poly := [(nat_lit 2454, Int.ofNat (nat_lit 1))]
theorem atom1141Coded_decode : atom1141 = SparsePolynomial.decodeCubic 21 atom1141Coded := by decide +kernel
theorem atom1141Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39724813792512 : Int) atom1141Coded) := by
  have h := atom1141_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1141Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1142 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1142 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1142 = ((g 5) * (g 11) * (g 19)) := by
  norm_num [atom1142, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1142_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48335988821760 : Int) atom1142) := by
  rw [SparsePolynomial.eval_scale, eval_atom1142]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1142Coded : CoefficientMerge.Poly := [(nat_lit 2455, Int.ofNat (nat_lit 1))]
theorem atom1142Coded_decode : atom1142 = SparsePolynomial.decodeCubic 21 atom1142Coded := by decide +kernel
theorem atom1142Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48335988821760 : Int) atom1142Coded) := by
  have h := atom1142_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1142Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1143 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 11, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1143 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1143 = ((g 5) * (g 11) * (g 20)) := by
  norm_num [atom1143, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1143_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56947163851008 : Int) atom1143) := by
  rw [SparsePolynomial.eval_scale, eval_atom1143]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1143Coded : CoefficientMerge.Poly := [(nat_lit 2456, Int.ofNat (nat_lit 1))]
theorem atom1143Coded_decode : atom1143 = SparsePolynomial.decodeCubic 21 atom1143Coded := by decide +kernel
theorem atom1143Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (56947163851008 : Int) atom1143Coded) := by
  have h := atom1143_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1143Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1144 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1144 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1144 = ((g 5) * (g 12) * (g 12)) := by
  norm_num [atom1144, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1144_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13458536612352 : Int) atom1144) := by
  rw [SparsePolynomial.eval_scale, eval_atom1144]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1144Coded : CoefficientMerge.Poly := [(nat_lit 2469, Int.ofNat (nat_lit 1))]
theorem atom1144Coded_decode : atom1144 = SparsePolynomial.decodeCubic 21 atom1144Coded := by decide +kernel
theorem atom1144Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13458536612352 : Int) atom1144Coded) := by
  have h := atom1144_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1144Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1145 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1145 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1145 = ((g 5) * (g 12) * (g 13)) := by
  norm_num [atom1145, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1145_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25686756405504 : Int) atom1145) := by
  rw [SparsePolynomial.eval_scale, eval_atom1145]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1145Coded : CoefficientMerge.Poly := [(nat_lit 2470, Int.ofNat (nat_lit 1))]
theorem atom1145Coded_decode : atom1145 = SparsePolynomial.decodeCubic 21 atom1145Coded := by decide +kernel
theorem atom1145Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25686756405504 : Int) atom1145Coded) := by
  have h := atom1145_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1145Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1146 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1146 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1146 = ((g 5) * (g 12) * (g 14)) := by
  norm_num [atom1146, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1146_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25145532981504 : Int) atom1146) := by
  rw [SparsePolynomial.eval_scale, eval_atom1146]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1146Coded : CoefficientMerge.Poly := [(nat_lit 2471, Int.ofNat (nat_lit 1))]
theorem atom1146Coded_decode : atom1146 = SparsePolynomial.decodeCubic 21 atom1146Coded := by decide +kernel
theorem atom1146Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25145532981504 : Int) atom1146Coded) := by
  have h := atom1146_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1146Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1147 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1147 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1147 = ((g 5) * (g 12) * (g 15)) := by
  norm_num [atom1147, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1147_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29937883845504 : Int) atom1147) := by
  rw [SparsePolynomial.eval_scale, eval_atom1147]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1147Coded : CoefficientMerge.Poly := [(nat_lit 2472, Int.ofNat (nat_lit 1))]
theorem atom1147Coded_decode : atom1147 = SparsePolynomial.decodeCubic 21 atom1147Coded := by decide +kernel
theorem atom1147Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29937883845504 : Int) atom1147Coded) := by
  have h := atom1147_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1147Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1148 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1148 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1148 = ((g 5) * (g 12) * (g 16)) := by
  norm_num [atom1148, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1148_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29509938218240 : Int) atom1148) := by
  rw [SparsePolynomial.eval_scale, eval_atom1148]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1148Coded : CoefficientMerge.Poly := [(nat_lit 2473, Int.ofNat (nat_lit 1))]
theorem atom1148Coded_decode : atom1148 = SparsePolynomial.decodeCubic 21 atom1148Coded := by decide +kernel
theorem atom1148Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29509938218240 : Int) atom1148Coded) := by
  have h := atom1148_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1148Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1149 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1149 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1149 = ((g 5) * (g 12) * (g 17)) := by
  norm_num [atom1149, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1149_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40443829119104 : Int) atom1149) := by
  rw [SparsePolynomial.eval_scale, eval_atom1149]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1149Coded : CoefficientMerge.Poly := [(nat_lit 2474, Int.ofNat (nat_lit 1))]
theorem atom1149Coded_decode : atom1149 = SparsePolynomial.decodeCubic 21 atom1149Coded := by decide +kernel
theorem atom1149Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40443829119104 : Int) atom1149Coded) := by
  have h := atom1149_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1149Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1150 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1150 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1150 = ((g 5) * (g 12) * (g 18)) := by
  norm_num [atom1150, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1150_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41715097976512 : Int) atom1150) := by
  rw [SparsePolynomial.eval_scale, eval_atom1150]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1150Coded : CoefficientMerge.Poly := [(nat_lit 2475, Int.ofNat (nat_lit 1))]
theorem atom1150Coded_decode : atom1150 = SparsePolynomial.decodeCubic 21 atom1150Coded := by decide +kernel
theorem atom1150Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41715097976512 : Int) atom1150Coded) := by
  have h := atom1150_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1150Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1151 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1151 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1151 = ((g 5) * (g 12) * (g 19)) := by
  norm_num [atom1151, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1151_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49283350901760 : Int) atom1151) := by
  rw [SparsePolynomial.eval_scale, eval_atom1151]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1151Coded : CoefficientMerge.Poly := [(nat_lit 2476, Int.ofNat (nat_lit 1))]
theorem atom1151Coded_decode : atom1151 = SparsePolynomial.decodeCubic 21 atom1151Coded := by decide +kernel
theorem atom1151Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49283350901760 : Int) atom1151Coded) := by
  have h := atom1151_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1151Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1152 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 12, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1152 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1152 = ((g 5) * (g 12) * (g 20)) := by
  norm_num [atom1152, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1152_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57682924975008 : Int) atom1152) := by
  rw [SparsePolynomial.eval_scale, eval_atom1152]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1152Coded : CoefficientMerge.Poly := [(nat_lit 2477, Int.ofNat (nat_lit 1))]
theorem atom1152Coded_decode : atom1152 = SparsePolynomial.decodeCubic 21 atom1152Coded := by decide +kernel
theorem atom1152Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (57682924975008 : Int) atom1152Coded) := by
  have h := atom1152_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1152Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1153 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1153 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1153 = ((g 5) * (g 13) * (g 13)) := by
  norm_num [atom1153, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1153_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16376678929152 : Int) atom1153) := by
  rw [SparsePolynomial.eval_scale, eval_atom1153]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1153Coded : CoefficientMerge.Poly := [(nat_lit 2491, Int.ofNat (nat_lit 1))]
theorem atom1153Coded_decode : atom1153 = SparsePolynomial.decodeCubic 21 atom1153Coded := by decide +kernel
theorem atom1153Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16376678929152 : Int) atom1153Coded) := by
  have h := atom1153_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1153Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1154 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1154 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1154 = ((g 5) * (g 13) * (g 14)) := by
  norm_num [atom1154, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1154_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (30291619682304 : Int) atom1154) := by
  rw [SparsePolynomial.eval_scale, eval_atom1154]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1154Coded : CoefficientMerge.Poly := [(nat_lit 2492, Int.ofNat (nat_lit 1))]
theorem atom1154Coded_decode : atom1154 = SparsePolynomial.decodeCubic 21 atom1154Coded := by decide +kernel
theorem atom1154Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30291619682304 : Int) atom1154Coded) := by
  have h := atom1154_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1154Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1155 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1155 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1155 = ((g 5) * (g 13) * (g 15)) := by
  norm_num [atom1155, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1155_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34213038813504 : Int) atom1155) := by
  rw [SparsePolynomial.eval_scale, eval_atom1155]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1155Coded : CoefficientMerge.Poly := [(nat_lit 2493, Int.ofNat (nat_lit 1))]
theorem atom1155Coded_decode : atom1155 = SparsePolynomial.decodeCubic 21 atom1155Coded := by decide +kernel
theorem atom1155Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34213038813504 : Int) atom1155Coded) := by
  have h := atom1155_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1155Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1156 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1156 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1156 = ((g 5) * (g 13) * (g 16)) := by
  norm_num [atom1156, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1156_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32778158869440 : Int) atom1156) := by
  rw [SparsePolynomial.eval_scale, eval_atom1156]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1156Coded : CoefficientMerge.Poly := [(nat_lit 2494, Int.ofNat (nat_lit 1))]
theorem atom1156Coded_decode : atom1156 = SparsePolynomial.decodeCubic 21 atom1156Coded := by decide +kernel
theorem atom1156Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32778158869440 : Int) atom1156Coded) := by
  have h := atom1156_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1156Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1157 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1157 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1157 = ((g 5) * (g 13) * (g 17)) := by
  norm_num [atom1157, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1157_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45968048642304 : Int) atom1157) := by
  rw [SparsePolynomial.eval_scale, eval_atom1157]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1157Coded : CoefficientMerge.Poly := [(nat_lit 2495, Int.ofNat (nat_lit 1))]
theorem atom1157Coded_decode : atom1157 = SparsePolynomial.decodeCubic 21 atom1157Coded := by decide +kernel
theorem atom1157Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (45968048642304 : Int) atom1157Coded) := by
  have h := atom1157_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1157Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1158 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1158 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1158 = ((g 5) * (g 13) * (g 18)) := by
  norm_num [atom1158, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1158_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48255838538112 : Int) atom1158) := by
  rw [SparsePolynomial.eval_scale, eval_atom1158]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1158Coded : CoefficientMerge.Poly := [(nat_lit 2496, Int.ofNat (nat_lit 1))]
theorem atom1158Coded_decode : atom1158 = SparsePolynomial.decodeCubic 21 atom1158Coded := by decide +kernel
theorem atom1158Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48255838538112 : Int) atom1158Coded) := by
  have h := atom1158_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1158Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1159 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1159 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1159 = ((g 5) * (g 13) * (g 19)) := by
  norm_num [atom1159, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1159_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48971706384960 : Int) atom1159) := by
  rw [SparsePolynomial.eval_scale, eval_atom1159]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1159Coded : CoefficientMerge.Poly := [(nat_lit 2497, Int.ofNat (nat_lit 1))]
theorem atom1159Coded_decode : atom1159 = SparsePolynomial.decodeCubic 21 atom1159Coded := by decide +kernel
theorem atom1159Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48971706384960 : Int) atom1159Coded) := by
  have h := atom1159_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1159Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1160 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 13, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1160 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1160 = ((g 5) * (g 13) * (g 20)) := by
  norm_num [atom1160, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1160_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63039466358208 : Int) atom1160) := by
  rw [SparsePolynomial.eval_scale, eval_atom1160]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1160Coded : CoefficientMerge.Poly := [(nat_lit 2498, Int.ofNat (nat_lit 1))]
theorem atom1160Coded_decode : atom1160 = SparsePolynomial.decodeCubic 21 atom1160Coded := by decide +kernel
theorem atom1160Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (63039466358208 : Int) atom1160Coded) := by
  have h := atom1160_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1160Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1161 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1161 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1161 = ((g 5) * (g 14) * (g 14)) := by
  norm_num [atom1161, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1161_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20331751940352 : Int) atom1161) := by
  rw [SparsePolynomial.eval_scale, eval_atom1161]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1161Coded : CoefficientMerge.Poly := [(nat_lit 2513, Int.ofNat (nat_lit 1))]
theorem atom1161Coded_decode : atom1161 = SparsePolynomial.decodeCubic 21 atom1161Coded := by decide +kernel
theorem atom1161Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20331751940352 : Int) atom1161Coded) := by
  have h := atom1161_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1161Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1162 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1162 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1162 = ((g 5) * (g 14) * (g 15)) := by
  norm_num [atom1162, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1162_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (38507308418304 : Int) atom1162) := by
  rw [SparsePolynomial.eval_scale, eval_atom1162]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1162Coded : CoefficientMerge.Poly := [(nat_lit 2514, Int.ofNat (nat_lit 1))]
theorem atom1162Coded_decode : atom1162 = SparsePolynomial.decodeCubic 21 atom1162Coded := by decide +kernel
theorem atom1162Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38507308418304 : Int) atom1162Coded) := by
  have h := atom1162_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1162Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1163 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1163 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1163 = ((g 5) * (g 14) * (g 16)) := by
  norm_num [atom1163, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1163_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (35927230083840 : Int) atom1163) := by
  rw [SparsePolynomial.eval_scale, eval_atom1163]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1163Coded : CoefficientMerge.Poly := [(nat_lit 2515, Int.ofNat (nat_lit 1))]
theorem atom1163Coded_decode : atom1163 = SparsePolynomial.decodeCubic 21 atom1163Coded := by decide +kernel
theorem atom1163Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35927230083840 : Int) atom1163Coded) := by
  have h := atom1163_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1163Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1164 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1164 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1164 = ((g 5) * (g 14) * (g 17)) := by
  norm_num [atom1164, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1164_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53554841282304 : Int) atom1164) := by
  rw [SparsePolynomial.eval_scale, eval_atom1164]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1164Coded : CoefficientMerge.Poly := [(nat_lit 2516, Int.ofNat (nat_lit 1))]
theorem atom1164Coded_decode : atom1164 = SparsePolynomial.decodeCubic 21 atom1164Coded := by decide +kernel
theorem atom1164Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53554841282304 : Int) atom1164Coded) := by
  have h := atom1164_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1164Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1165 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1165 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1165 = ((g 5) * (g 14) * (g 18)) := by
  norm_num [atom1165, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1165_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (57013026832512 : Int) atom1165) := by
  rw [SparsePolynomial.eval_scale, eval_atom1165]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1165Coded : CoefficientMerge.Poly := [(nat_lit 2517, Int.ofNat (nat_lit 1))]
theorem atom1165Coded_decode : atom1165 = SparsePolynomial.decodeCubic 21 atom1165Coded := by decide +kernel
theorem atom1165Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (57013026832512 : Int) atom1165Coded) := by
  have h := atom1165_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1165Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1166 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1166 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1166 = ((g 5) * (g 14) * (g 19)) := by
  norm_num [atom1166, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1166_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (52848874978560 : Int) atom1166) := by
  rw [SparsePolynomial.eval_scale, eval_atom1166]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1166Coded : CoefficientMerge.Poly := [(nat_lit 2518, Int.ofNat (nat_lit 1))]
theorem atom1166Coded_decode : atom1166 = SparsePolynomial.decodeCubic 21 atom1166Coded := by decide +kernel
theorem atom1166Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52848874978560 : Int) atom1166Coded) := by
  have h := atom1166_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1166Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1167 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 14, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1167 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1167 = ((g 5) * (g 14) * (g 20)) := by
  norm_num [atom1167, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1167_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (72684357715008 : Int) atom1167) := by
  rw [SparsePolynomial.eval_scale, eval_atom1167]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1167Coded : CoefficientMerge.Poly := [(nat_lit 2519, Int.ofNat (nat_lit 1))]
theorem atom1167Coded_decode : atom1167 = SparsePolynomial.decodeCubic 21 atom1167Coded := by decide +kernel
theorem atom1167Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (72684357715008 : Int) atom1167Coded) := by
  have h := atom1167_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1167Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1168 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1168 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1168 = ((g 5) * (g 15) * (g 15)) := by
  norm_num [atom1168, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1168_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26020396714752 : Int) atom1168) := by
  rw [SparsePolynomial.eval_scale, eval_atom1168]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1168Coded : CoefficientMerge.Poly := [(nat_lit 2535, Int.ofNat (nat_lit 1))]
theorem atom1168Coded_decode : atom1168 = SparsePolynomial.decodeCubic 21 atom1168Coded := by decide +kernel
theorem atom1168Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26020396714752 : Int) atom1168Coded) := by
  have h := atom1168_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1168Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1169 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1169 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1169 = ((g 5) * (g 15) * (g 16)) := by
  norm_num [atom1169, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1169_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47998729798272 : Int) atom1169) := by
  rw [SparsePolynomial.eval_scale, eval_atom1169]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1169Coded : CoefficientMerge.Poly := [(nat_lit 2536, Int.ofNat (nat_lit 1))]
theorem atom1169Coded_decode : atom1169 = SparsePolynomial.decodeCubic 21 atom1169Coded := by decide +kernel
theorem atom1169Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47998729798272 : Int) atom1169Coded) := by
  have h := atom1169_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1169Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1170 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1170 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1170 = ((g 5) * (g 15) * (g 17)) := by
  norm_num [atom1170, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1170_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69989670434304 : Int) atom1170) := by
  rw [SparsePolynomial.eval_scale, eval_atom1170]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1170Coded : CoefficientMerge.Poly := [(nat_lit 2537, Int.ofNat (nat_lit 1))]
theorem atom1170Coded_decode : atom1170 = SparsePolynomial.decodeCubic 21 atom1170Coded := by decide +kernel
theorem atom1170Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (69989670434304 : Int) atom1170Coded) := by
  have h := atom1170_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1170Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1171 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1171 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1171 = ((g 5) * (g 15) * (g 18)) := by
  norm_num [atom1171, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1171_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (69826861415808 : Int) atom1171) := by
  rw [SparsePolynomial.eval_scale, eval_atom1171]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1171Coded : CoefficientMerge.Poly := [(nat_lit 2538, Int.ofNat (nat_lit 1))]
theorem atom1171Coded_decode : atom1171 = SparsePolynomial.decodeCubic 21 atom1171Coded := by decide +kernel
theorem atom1171Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (69826861415808 : Int) atom1171Coded) := by
  have h := atom1171_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1171Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1172 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1172 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1172 = ((g 5) * (g 15) * (g 19)) := by
  norm_num [atom1172, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1172_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49709608836480 : Int) atom1172) := by
  rw [SparsePolynomial.eval_scale, eval_atom1172]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1172Coded : CoefficientMerge.Poly := [(nat_lit 2539, Int.ofNat (nat_lit 1))]
theorem atom1172Coded_decode : atom1172 = SparsePolynomial.decodeCubic 21 atom1172Coded := by decide +kernel
theorem atom1172Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49709608836480 : Int) atom1172Coded) := by
  have h := atom1172_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1172Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1173 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 15, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1173 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1173 = ((g 5) * (g 15) * (g 20)) := by
  norm_num [atom1173, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1173_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (73705078859904 : Int) atom1173) := by
  rw [SparsePolynomial.eval_scale, eval_atom1173]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1173Coded : CoefficientMerge.Poly := [(nat_lit 2540, Int.ofNat (nat_lit 1))]
theorem atom1173Coded_decode : atom1173 = SparsePolynomial.decodeCubic 21 atom1173Coded := by decide +kernel
theorem atom1173Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (73705078859904 : Int) atom1173Coded) := by
  have h := atom1173_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1173Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1174 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 16, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1174 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1174 = ((g 5) * (g 16) * (g 16)) := by
  norm_num [atom1174, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1174_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18866969402112 : Int) atom1174) := by
  rw [SparsePolynomial.eval_scale, eval_atom1174]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1174Coded : CoefficientMerge.Poly := [(nat_lit 2557, Int.ofNat (nat_lit 1))]
theorem atom1174Coded_decode : atom1174 = SparsePolynomial.decodeCubic 21 atom1174Coded := by decide +kernel
theorem atom1174Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18866969402112 : Int) atom1174Coded) := by
  have h := atom1174_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1174Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1175 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 16, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1175 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1175 = ((g 5) * (g 16) * (g 17)) := by
  norm_num [atom1175, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1175_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56352193854336 : Int) atom1175) := by
  rw [SparsePolynomial.eval_scale, eval_atom1175]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1175Coded : CoefficientMerge.Poly := [(nat_lit 2558, Int.ofNat (nat_lit 1))]
theorem atom1175Coded_decode : atom1175 = SparsePolynomial.decodeCubic 21 atom1175Coded := by decide +kernel
theorem atom1175Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (56352193854336 : Int) atom1175Coded) := by
  have h := atom1175_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1175Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1176 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 16, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1176 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1176 = ((g 5) * (g 16) * (g 18)) := by
  norm_num [atom1176, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1176_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (58898327545152 : Int) atom1176) := by
  rw [SparsePolynomial.eval_scale, eval_atom1176]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1176Coded : CoefficientMerge.Poly := [(nat_lit 2559, Int.ofNat (nat_lit 1))]
theorem atom1176Coded_decode : atom1176 = SparsePolynomial.decodeCubic 21 atom1176Coded := by decide +kernel
theorem atom1176Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (58898327545152 : Int) atom1176Coded) := by
  have h := atom1176_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1176Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1177 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 16, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1177 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1177 = ((g 5) * (g 16) * (g 19)) := by
  norm_num [atom1177, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1177_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43714896386304 : Int) atom1177) := by
  rw [SparsePolynomial.eval_scale, eval_atom1177]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1177Coded : CoefficientMerge.Poly := [(nat_lit 2560, Int.ofNat (nat_lit 1))]
theorem atom1177Coded_decode : atom1177 = SparsePolynomial.decodeCubic 21 atom1177Coded := by decide +kernel
theorem atom1177Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43714896386304 : Int) atom1177Coded) := by
  have h := atom1177_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1177Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1178 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 16, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1178 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1178 = ((g 5) * (g 16) * (g 20)) := by
  norm_num [atom1178, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1178_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50328202741536 : Int) atom1178) := by
  rw [SparsePolynomial.eval_scale, eval_atom1178]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1178Coded : CoefficientMerge.Poly := [(nat_lit 2561, Int.ofNat (nat_lit 1))]
theorem atom1178Coded_decode : atom1178 = SparsePolynomial.decodeCubic 21 atom1178Coded := by decide +kernel
theorem atom1178Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50328202741536 : Int) atom1178Coded) := by
  have h := atom1178_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1178Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1179 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 17, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1179 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1179 = ((g 5) * (g 17) * (g 17)) := by
  norm_num [atom1179, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1179_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40369274295552 : Int) atom1179) := by
  rw [SparsePolynomial.eval_scale, eval_atom1179]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1179Coded : CoefficientMerge.Poly := [(nat_lit 2579, Int.ofNat (nat_lit 1))]
theorem atom1179Coded_decode : atom1179 = SparsePolynomial.decodeCubic 21 atom1179Coded := by decide +kernel
theorem atom1179Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40369274295552 : Int) atom1179Coded) := by
  have h := atom1179_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1179Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1180 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 17, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1180 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1180 = ((g 5) * (g 17) * (g 18)) := by
  norm_num [atom1180, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1180_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63935689449600 : Int) atom1180) := by
  rw [SparsePolynomial.eval_scale, eval_atom1180]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1180Coded : CoefficientMerge.Poly := [(nat_lit 2580, Int.ofNat (nat_lit 1))]
theorem atom1180Coded_decode : atom1180 = SparsePolynomial.decodeCubic 21 atom1180Coded := by decide +kernel
theorem atom1180Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (63935689449600 : Int) atom1180Coded) := by
  have h := atom1180_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1180Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1181 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 17, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1181 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1181 = ((g 5) * (g 17) * (g 19)) := by
  norm_num [atom1181, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1181_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (44823459653760 : Int) atom1181) := by
  rw [SparsePolynomial.eval_scale, eval_atom1181]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1181Coded : CoefficientMerge.Poly := [(nat_lit 2581, Int.ofNat (nat_lit 1))]
theorem atom1181Coded_decode : atom1181 = SparsePolynomial.decodeCubic 21 atom1181Coded := by decide +kernel
theorem atom1181Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44823459653760 : Int) atom1181Coded) := by
  have h := atom1181_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1181Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1182 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 17, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1182 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1182 = ((g 5) * (g 17) * (g 20)) := by
  norm_num [atom1182, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1182_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50291511241152 : Int) atom1182) := by
  rw [SparsePolynomial.eval_scale, eval_atom1182]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1182Coded : CoefficientMerge.Poly := [(nat_lit 2582, Int.ofNat (nat_lit 1))]
theorem atom1182Coded_decode : atom1182 = SparsePolynomial.decodeCubic 21 atom1182Coded := by decide +kernel
theorem atom1182Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50291511241152 : Int) atom1182Coded) := by
  have h := atom1182_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1182Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1183 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 18, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1183 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1183 = ((g 5) * (g 18) * (g 18)) := by
  norm_num [atom1183, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1183_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18599183925696 : Int) atom1183) := by
  rw [SparsePolynomial.eval_scale, eval_atom1183]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1183Coded : CoefficientMerge.Poly := [(nat_lit 2601, Int.ofNat (nat_lit 1))]
theorem atom1183Coded_decode : atom1183 = SparsePolynomial.decodeCubic 21 atom1183Coded := by decide +kernel
theorem atom1183Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18599183925696 : Int) atom1183Coded) := by
  have h := atom1183_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1183Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1184 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 18, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1184 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1184 = ((g 5) * (g 18) * (g 19)) := by
  norm_num [atom1184, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1184_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23147791261632 : Int) atom1184) := by
  rw [SparsePolynomial.eval_scale, eval_atom1184]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1184Coded : CoefficientMerge.Poly := [(nat_lit 2602, Int.ofNat (nat_lit 1))]
theorem atom1184Coded_decode : atom1184 = SparsePolynomial.decodeCubic 21 atom1184Coded := by decide +kernel
theorem atom1184Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23147791261632 : Int) atom1184Coded) := by
  have h := atom1184_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1184Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1185 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 18, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1185 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1185 = ((g 5) * (g 18) * (g 20)) := by
  norm_num [atom1185, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1185_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (28126164973248 : Int) atom1185) := by
  rw [SparsePolynomial.eval_scale, eval_atom1185]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1185Coded : CoefficientMerge.Poly := [(nat_lit 2603, Int.ofNat (nat_lit 1))]
theorem atom1185Coded_decode : atom1185 = SparsePolynomial.decodeCubic 21 atom1185Coded := by decide +kernel
theorem atom1185Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28126164973248 : Int) atom1185Coded) := by
  have h := atom1185_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1185Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1186 : SparsePolynomial.Poly := [([nat_lit 5, nat_lit 20, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1186 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1186 = ((g 5) * (g 20) * (g 20)) := by
  norm_num [atom1186, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1186_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3684923594208 : Int) atom1186) := by
  rw [SparsePolynomial.eval_scale, eval_atom1186]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1186Coded : CoefficientMerge.Poly := [(nat_lit 2645, Int.ofNat (nat_lit 1))]
theorem atom1186Coded_decode : atom1186 = SparsePolynomial.decodeCubic 21 atom1186Coded := by decide +kernel
theorem atom1186Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3684923594208 : Int) atom1186Coded) := by
  have h := atom1186_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1186Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1187 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 6], Int.ofNat (nat_lit 1))]
theorem eval_atom1187 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1187 = ((g 6) * (g 6) * (g 6)) := by
  norm_num [atom1187, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1187_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4122798220800 : Int) atom1187) := by
  rw [SparsePolynomial.eval_scale, eval_atom1187]
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 6) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1187Coded : CoefficientMerge.Poly := [(nat_lit 2778, Int.ofNat (nat_lit 1))]
theorem atom1187Coded_decode : atom1187 = SparsePolynomial.decodeCubic 21 atom1187Coded := by decide +kernel
theorem atom1187Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4122798220800 : Int) atom1187Coded) := by
  have h := atom1187_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1187Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1188 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1188 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1188 = ((g 6) * (g 6) * (g 7)) := by
  norm_num [atom1188, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1188_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7834685443200 : Int) atom1188) := by
  rw [SparsePolynomial.eval_scale, eval_atom1188]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1188Coded : CoefficientMerge.Poly := [(nat_lit 2779, Int.ofNat (nat_lit 1))]
theorem atom1188Coded_decode : atom1188 = SparsePolynomial.decodeCubic 21 atom1188Coded := by decide +kernel
theorem atom1188Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7834685443200 : Int) atom1188Coded) := by
  have h := atom1188_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1188Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1189 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1189 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1189 = ((g 6) * (g 6) * (g 8)) := by
  norm_num [atom1189, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1189_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3472038057600 : Int) atom1189) := by
  rw [SparsePolynomial.eval_scale, eval_atom1189]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1189Coded : CoefficientMerge.Poly := [(nat_lit 2780, Int.ofNat (nat_lit 1))]
theorem atom1189Coded_decode : atom1189 = SparsePolynomial.decodeCubic 21 atom1189Coded := by decide +kernel
theorem atom1189Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3472038057600 : Int) atom1189Coded) := by
  have h := atom1189_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1189Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1190 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1190 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1190 = ((g 6) * (g 6) * (g 9)) := by
  norm_num [atom1190, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1190_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1190) := by
  rw [SparsePolynomial.eval_scale, eval_atom1190]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1190Coded : CoefficientMerge.Poly := [(nat_lit 2781, Int.ofNat (nat_lit 1))]
theorem atom1190Coded_decode : atom1190 = SparsePolynomial.decodeCubic 21 atom1190Coded := by decide +kernel
theorem atom1190Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1190Coded) := by
  have h := atom1190_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1190Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1191 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1191 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1191 = ((g 6) * (g 6) * (g 10)) := by
  norm_num [atom1191, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1191_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (343096992000 : Int) atom1191) := by
  rw [SparsePolynomial.eval_scale, eval_atom1191]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1191Coded : CoefficientMerge.Poly := [(nat_lit 2782, Int.ofNat (nat_lit 1))]
theorem atom1191Coded_decode : atom1191 = SparsePolynomial.decodeCubic 21 atom1191Coded := by decide +kernel
theorem atom1191Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (343096992000 : Int) atom1191Coded) := by
  have h := atom1191_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1191Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1192 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 6, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1192 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1192 = ((g 6) * (g 6) * (g 15)) := by
  norm_num [atom1192, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1192_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4497994368000 : Int) atom1192) := by
  rw [SparsePolynomial.eval_scale, eval_atom1192]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1192Coded : CoefficientMerge.Poly := [(nat_lit 2787, Int.ofNat (nat_lit 1))]
theorem atom1192Coded_decode : atom1192 = SparsePolynomial.decodeCubic 21 atom1192Coded := by decide +kernel
theorem atom1192Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4497994368000 : Int) atom1192Coded) := by
  have h := atom1192_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1192Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1193 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 7], Int.ofNat (nat_lit 1))]
theorem eval_atom1193 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1193 = ((g 6) * (g 7) * (g 7)) := by
  norm_num [atom1193, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1193_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6459401491200 : Int) atom1193) := by
  rw [SparsePolynomial.eval_scale, eval_atom1193]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1193Coded : CoefficientMerge.Poly := [(nat_lit 2800, Int.ofNat (nat_lit 1))]
theorem atom1193Coded_decode : atom1193 = SparsePolynomial.decodeCubic 21 atom1193Coded := by decide +kernel
theorem atom1193Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6459401491200 : Int) atom1193Coded) := by
  have h := atom1193_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1193Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1194 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1194 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1194 = ((g 6) * (g 7) * (g 8)) := by
  norm_num [atom1194, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1194_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5397730329600 : Int) atom1194) := by
  rw [SparsePolynomial.eval_scale, eval_atom1194]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1194Coded : CoefficientMerge.Poly := [(nat_lit 2801, Int.ofNat (nat_lit 1))]
theorem atom1194Coded_decode : atom1194 = SparsePolynomial.decodeCubic 21 atom1194Coded := by decide +kernel
theorem atom1194Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5397730329600 : Int) atom1194Coded) := by
  have h := atom1194_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1194Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1195 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1195 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1195 = ((g 6) * (g 7) * (g 12)) := by
  norm_num [atom1195, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1195_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1195) := by
  rw [SparsePolynomial.eval_scale, eval_atom1195]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1195Coded : CoefficientMerge.Poly := [(nat_lit 2805, Int.ofNat (nat_lit 1))]
theorem atom1195Coded_decode : atom1195 = SparsePolynomial.decodeCubic 21 atom1195Coded := by decide +kernel
theorem atom1195Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1195Coded) := by
  have h := atom1195_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1195Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1196 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1196 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1196 = ((g 6) * (g 7) * (g 13)) := by
  norm_num [atom1196, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1196_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (854359833600 : Int) atom1196) := by
  rw [SparsePolynomial.eval_scale, eval_atom1196]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1196Coded : CoefficientMerge.Poly := [(nat_lit 2806, Int.ofNat (nat_lit 1))]
theorem atom1196Coded_decode : atom1196 = SparsePolynomial.decodeCubic 21 atom1196Coded := by decide +kernel
theorem atom1196Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (854359833600 : Int) atom1196Coded) := by
  have h := atom1196_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1196Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1197 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1197 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1197 = ((g 6) * (g 7) * (g 14)) := by
  norm_num [atom1197, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1197_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1281539750400 : Int) atom1197) := by
  rw [SparsePolynomial.eval_scale, eval_atom1197]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1197Coded : CoefficientMerge.Poly := [(nat_lit 2807, Int.ofNat (nat_lit 1))]
theorem atom1197Coded_decode : atom1197 = SparsePolynomial.decodeCubic 21 atom1197Coded := by decide +kernel
theorem atom1197Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1281539750400 : Int) atom1197Coded) := by
  have h := atom1197_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1197Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1198 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1198 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1198 = ((g 6) * (g 7) * (g 15)) := by
  norm_num [atom1198, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1198_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8045165325312 : Int) atom1198) := by
  rw [SparsePolynomial.eval_scale, eval_atom1198]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1198Coded : CoefficientMerge.Poly := [(nat_lit 2808, Int.ofNat (nat_lit 1))]
theorem atom1198Coded_decode : atom1198 = SparsePolynomial.decodeCubic 21 atom1198Coded := by decide +kernel
theorem atom1198Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8045165325312 : Int) atom1198Coded) := by
  have h := atom1198_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1198Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1199 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1199 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1199 = ((g 6) * (g 7) * (g 18)) := by
  norm_num [atom1199, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1199_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5465873347200 : Int) atom1199) := by
  rw [SparsePolynomial.eval_scale, eval_atom1199]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1199Coded : CoefficientMerge.Poly := [(nat_lit 2811, Int.ofNat (nat_lit 1))]
theorem atom1199Coded_decode : atom1199 = SparsePolynomial.decodeCubic 21 atom1199Coded := by decide +kernel
theorem atom1199Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5465873347200 : Int) atom1199Coded) := by
  have h := atom1199_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1199Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1200 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1200 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1200 = ((g 6) * (g 7) * (g 19)) := by
  norm_num [atom1200, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1200_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10744058142720 : Int) atom1200) := by
  rw [SparsePolynomial.eval_scale, eval_atom1200]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1200Coded : CoefficientMerge.Poly := [(nat_lit 2812, Int.ofNat (nat_lit 1))]
theorem atom1200Coded_decode : atom1200 = SparsePolynomial.decodeCubic 21 atom1200Coded := by decide +kernel
theorem atom1200Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10744058142720 : Int) atom1200Coded) := by
  have h := atom1200_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1200Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1201 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 7, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1201 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1201 = ((g 6) * (g 7) * (g 20)) := by
  norm_num [atom1201, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1201_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16910574206400 : Int) atom1201) := by
  rw [SparsePolynomial.eval_scale, eval_atom1201]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1201Coded : CoefficientMerge.Poly := [(nat_lit 2813, Int.ofNat (nat_lit 1))]
theorem atom1201Coded_decode : atom1201 = SparsePolynomial.decodeCubic 21 atom1201Coded := by decide +kernel
theorem atom1201Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16910574206400 : Int) atom1201Coded) := by
  have h := atom1201_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1201Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1202 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 8], Int.ofNat (nat_lit 1))]
theorem eval_atom1202 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1202 = ((g 6) * (g 8) * (g 8)) := by
  norm_num [atom1202, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1202_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2523934022400 : Int) atom1202) := by
  rw [SparsePolynomial.eval_scale, eval_atom1202]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1202Coded : CoefficientMerge.Poly := [(nat_lit 2822, Int.ofNat (nat_lit 1))]
theorem atom1202Coded_decode : atom1202 = SparsePolynomial.decodeCubic 21 atom1202Coded := by decide +kernel
theorem atom1202Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2523934022400 : Int) atom1202Coded) := by
  have h := atom1202_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1202Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1203 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1203 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1203 = ((g 6) * (g 8) * (g 12)) := by
  norm_num [atom1203, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1203_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (259014067200 : Int) atom1203) := by
  rw [SparsePolynomial.eval_scale, eval_atom1203]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1203Coded : CoefficientMerge.Poly := [(nat_lit 2826, Int.ofNat (nat_lit 1))]
theorem atom1203Coded_decode : atom1203 = SparsePolynomial.decodeCubic 21 atom1203Coded := by decide +kernel
theorem atom1203Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (259014067200 : Int) atom1203Coded) := by
  have h := atom1203_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1203Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1204 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 13], Int.ofNat (nat_lit 1))]
theorem eval_atom1204 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1204 = ((g 6) * (g 8) * (g 13)) := by
  norm_num [atom1204, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1204_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (945208051200 : Int) atom1204) := by
  rw [SparsePolynomial.eval_scale, eval_atom1204]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1204Coded : CoefficientMerge.Poly := [(nat_lit 2827, Int.ofNat (nat_lit 1))]
theorem atom1204Coded_decode : atom1204 = SparsePolynomial.decodeCubic 21 atom1204Coded := by decide +kernel
theorem atom1204Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (945208051200 : Int) atom1204Coded) := by
  have h := atom1204_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1204Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1205 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 14], Int.ofNat (nat_lit 1))]
theorem eval_atom1205 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1205 = ((g 6) * (g 8) * (g 14)) := by
  norm_num [atom1205, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1205_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1631402035200 : Int) atom1205) := by
  rw [SparsePolynomial.eval_scale, eval_atom1205]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1205Coded : CoefficientMerge.Poly := [(nat_lit 2828, Int.ofNat (nat_lit 1))]
theorem atom1205Coded_decode : atom1205 = SparsePolynomial.decodeCubic 21 atom1205Coded := by decide +kernel
theorem atom1205Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1631402035200 : Int) atom1205Coded) := by
  have h := atom1205_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1205Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1206 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 15], Int.ofNat (nat_lit 1))]
theorem eval_atom1206 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1206 = ((g 6) * (g 8) * (g 15)) := by
  norm_num [atom1206, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1206_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9159807182400 : Int) atom1206) := by
  rw [SparsePolynomial.eval_scale, eval_atom1206]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1206Coded : CoefficientMerge.Poly := [(nat_lit 2829, Int.ofNat (nat_lit 1))]
theorem atom1206Coded_decode : atom1206 = SparsePolynomial.decodeCubic 21 atom1206Coded := by decide +kernel
theorem atom1206Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9159807182400 : Int) atom1206Coded) := by
  have h := atom1206_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1206Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1207 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 16], Int.ofNat (nat_lit 1))]
theorem eval_atom1207 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1207 = ((g 6) * (g 8) * (g 16)) := by
  norm_num [atom1207, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1207_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3879597682800 : Int) atom1207) := by
  rw [SparsePolynomial.eval_scale, eval_atom1207]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1207Coded : CoefficientMerge.Poly := [(nat_lit 2830, Int.ofNat (nat_lit 1))]
theorem atom1207Coded_decode : atom1207 = SparsePolynomial.decodeCubic 21 atom1207Coded := by decide +kernel
theorem atom1207Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3879597682800 : Int) atom1207Coded) := by
  have h := atom1207_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1207Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1208 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 17], Int.ofNat (nat_lit 1))]
theorem eval_atom1208 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1208 = ((g 6) * (g 8) * (g 17)) := by
  norm_num [atom1208, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1208_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7715012760000 : Int) atom1208) := by
  rw [SparsePolynomial.eval_scale, eval_atom1208]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1208Coded : CoefficientMerge.Poly := [(nat_lit 2831, Int.ofNat (nat_lit 1))]
theorem atom1208Coded_decode : atom1208 = SparsePolynomial.decodeCubic 21 atom1208Coded := by decide +kernel
theorem atom1208Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7715012760000 : Int) atom1208Coded) := by
  have h := atom1208_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1208Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1209 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 18], Int.ofNat (nat_lit 1))]
theorem eval_atom1209 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1209 = ((g 6) * (g 8) * (g 18)) := by
  norm_num [atom1209, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1209_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14815693494000 : Int) atom1209) := by
  rw [SparsePolynomial.eval_scale, eval_atom1209]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1209Coded : CoefficientMerge.Poly := [(nat_lit 2832, Int.ofNat (nat_lit 1))]
theorem atom1209Coded_decode : atom1209 = SparsePolynomial.decodeCubic 21 atom1209Coded := by decide +kernel
theorem atom1209Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14815693494000 : Int) atom1209Coded) := by
  have h := atom1209_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1209Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1210 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 19], Int.ofNat (nat_lit 1))]
theorem eval_atom1210 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1210 = ((g 6) * (g 8) * (g 19)) := by
  norm_num [atom1210, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1210_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23440111203600 : Int) atom1210) := by
  rw [SparsePolynomial.eval_scale, eval_atom1210]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1210Coded : CoefficientMerge.Poly := [(nat_lit 2833, Int.ofNat (nat_lit 1))]
theorem atom1210Coded_decode : atom1210 = SparsePolynomial.decodeCubic 21 atom1210Coded := by decide +kernel
theorem atom1210Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23440111203600 : Int) atom1210Coded) := by
  have h := atom1210_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1210Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1211 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 8, nat_lit 20], Int.ofNat (nat_lit 1))]
theorem eval_atom1211 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1211 = ((g 6) * (g 8) * (g 20)) := by
  norm_num [atom1211, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1211_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32845738161600 : Int) atom1211) := by
  rw [SparsePolynomial.eval_scale, eval_atom1211]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1211Coded : CoefficientMerge.Poly := [(nat_lit 2834, Int.ofNat (nat_lit 1))]
theorem atom1211Coded_decode : atom1211 = SparsePolynomial.decodeCubic 21 atom1211Coded := by decide +kernel
theorem atom1211Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32845738161600 : Int) atom1211Coded) := by
  have h := atom1211_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1211Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1212 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 9], Int.ofNat (nat_lit 1))]
theorem eval_atom1212 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1212 = ((g 6) * (g 9) * (g 9)) := by
  norm_num [atom1212, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1212_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1061671161600 : Int) atom1212) := by
  rw [SparsePolynomial.eval_scale, eval_atom1212]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1212Coded : CoefficientMerge.Poly := [(nat_lit 2844, Int.ofNat (nat_lit 1))]
theorem atom1212Coded_decode : atom1212 = SparsePolynomial.decodeCubic 21 atom1212Coded := by decide +kernel
theorem atom1212Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1061671161600 : Int) atom1212Coded) := by
  have h := atom1212_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1212Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1213 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 10], Int.ofNat (nat_lit 1))]
theorem eval_atom1213 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1213 = ((g 6) * (g 9) * (g 10)) := by
  norm_num [atom1213, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1213_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (680402016000 : Int) atom1213) := by
  rw [SparsePolynomial.eval_scale, eval_atom1213]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1213Coded : CoefficientMerge.Poly := [(nat_lit 2845, Int.ofNat (nat_lit 1))]
theorem atom1213Coded_decode : atom1213 = SparsePolynomial.decodeCubic 21 atom1213Coded := by decide +kernel
theorem atom1213Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (680402016000 : Int) atom1213Coded) := by
  have h := atom1213_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1213Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1214 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 11], Int.ofNat (nat_lit 1))]
theorem eval_atom1214 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1214 = ((g 6) * (g 9) * (g 11)) := by
  norm_num [atom1214, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1214_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (512236166400 : Int) atom1214) := by
  rw [SparsePolynomial.eval_scale, eval_atom1214]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1214Coded : CoefficientMerge.Poly := [(nat_lit 2846, Int.ofNat (nat_lit 1))]
theorem atom1214Coded_decode : atom1214 = SparsePolynomial.decodeCubic 21 atom1214Coded := by decide +kernel
theorem atom1214Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (512236166400 : Int) atom1214Coded) := by
  have h := atom1214_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1214Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1215 : SparsePolynomial.Poly := [([nat_lit 6, nat_lit 9, nat_lit 12], Int.ofNat (nat_lit 1))]
theorem eval_atom1215 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1215 = ((g 6) * (g 9) * (g 12)) := by
  norm_num [atom1215, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1215_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1289278368000 : Int) atom1215) := by
  rw [SparsePolynomial.eval_scale, eval_atom1215]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1215Coded : CoefficientMerge.Poly := [(nat_lit 2847, Int.ofNat (nat_lit 1))]
theorem atom1215Coded_decode : atom1215 = SparsePolynomial.decodeCubic 21 atom1215Coded := by decide +kernel
theorem atom1215Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1289278368000 : Int) atom1215Coded) := by
  have h := atom1215_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1215Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block016 : CoefficientMerge.Poly := [(nat_lit 2449, Int.ofNat (nat_lit 20238042645504)), (nat_lit 2450, Int.ofNat (nat_lit 20278634402304)), (nat_lit 2451, Int.ofNat (nat_lit 29238383522304)), (nat_lit 2452, Int.ofNat (nat_lit 26787755370240)), (nat_lit 2453, Int.ofNat (nat_lit 39115299746304)), (nat_lit 2454, Int.ofNat (nat_lit 39724813792512)), (nat_lit 2455, Int.ofNat (nat_lit 48335988821760)), (nat_lit 2456, Int.ofNat (nat_lit 56947163851008)), (nat_lit 2469, Int.ofNat (nat_lit 13458536612352)), (nat_lit 2470, Int.ofNat (nat_lit 25686756405504)), (nat_lit 2471, Int.ofNat (nat_lit 25145532981504)), (nat_lit 2472, Int.ofNat (nat_lit 29937883845504)), (nat_lit 2473, Int.ofNat (nat_lit 29509938218240)), (nat_lit 2474, Int.ofNat (nat_lit 40443829119104)), (nat_lit 2475, Int.ofNat (nat_lit 41715097976512)), (nat_lit 2476, Int.ofNat (nat_lit 49283350901760)), (nat_lit 2477, Int.ofNat (nat_lit 57682924975008)), (nat_lit 2491, Int.ofNat (nat_lit 16376678929152)), (nat_lit 2492, Int.ofNat (nat_lit 30291619682304)), (nat_lit 2493, Int.ofNat (nat_lit 34213038813504)), (nat_lit 2494, Int.ofNat (nat_lit 32778158869440)), (nat_lit 2495, Int.ofNat (nat_lit 45968048642304)), (nat_lit 2496, Int.ofNat (nat_lit 48255838538112)), (nat_lit 2497, Int.ofNat (nat_lit 48971706384960)), (nat_lit 2498, Int.ofNat (nat_lit 63039466358208)), (nat_lit 2513, Int.ofNat (nat_lit 20331751940352)), (nat_lit 2514, Int.ofNat (nat_lit 38507308418304)), (nat_lit 2515, Int.ofNat (nat_lit 35927230083840)), (nat_lit 2516, Int.ofNat (nat_lit 53554841282304)), (nat_lit 2517, Int.ofNat (nat_lit 57013026832512)), (nat_lit 2518, Int.ofNat (nat_lit 52848874978560)), (nat_lit 2519, Int.ofNat (nat_lit 72684357715008)), (nat_lit 2535, Int.ofNat (nat_lit 26020396714752)), (nat_lit 2536, Int.ofNat (nat_lit 47998729798272)), (nat_lit 2537, Int.ofNat (nat_lit 69989670434304)), (nat_lit 2538, Int.ofNat (nat_lit 69826861415808)), (nat_lit 2539, Int.ofNat (nat_lit 49709608836480)), (nat_lit 2540, Int.ofNat (nat_lit 73705078859904)), (nat_lit 2557, Int.ofNat (nat_lit 18866969402112)), (nat_lit 2558, Int.ofNat (nat_lit 56352193854336)), (nat_lit 2559, Int.ofNat (nat_lit 58898327545152)), (nat_lit 2560, Int.ofNat (nat_lit 43714896386304)), (nat_lit 2561, Int.ofNat (nat_lit 50328202741536)), (nat_lit 2579, Int.ofNat (nat_lit 40369274295552)), (nat_lit 2580, Int.ofNat (nat_lit 63935689449600)), (nat_lit 2581, Int.ofNat (nat_lit 44823459653760)), (nat_lit 2582, Int.ofNat (nat_lit 50291511241152)), (nat_lit 2601, Int.ofNat (nat_lit 18599183925696)), (nat_lit 2602, Int.ofNat (nat_lit 23147791261632)), (nat_lit 2603, Int.ofNat (nat_lit 28126164973248)), (nat_lit 2645, Int.ofNat (nat_lit 3684923594208)), (nat_lit 2778, Int.ofNat (nat_lit 4122798220800)), (nat_lit 2779, Int.ofNat (nat_lit 7834685443200)), (nat_lit 2780, Int.ofNat (nat_lit 3472038057600)), (nat_lit 2781, Int.ofNat (nat_lit 427179916800)), (nat_lit 2782, Int.ofNat (nat_lit 343096992000)), (nat_lit 2787, Int.ofNat (nat_lit 4497994368000)), (nat_lit 2800, Int.ofNat (nat_lit 6459401491200)), (nat_lit 2801, Int.ofNat (nat_lit 5397730329600)), (nat_lit 2805, Int.ofNat (nat_lit 427179916800)), (nat_lit 2806, Int.ofNat (nat_lit 854359833600)), (nat_lit 2807, Int.ofNat (nat_lit 1281539750400)), (nat_lit 2808, Int.ofNat (nat_lit 8045165325312)), (nat_lit 2811, Int.ofNat (nat_lit 5465873347200)), (nat_lit 2812, Int.ofNat (nat_lit 10744058142720)), (nat_lit 2813, Int.ofNat (nat_lit 16910574206400)), (nat_lit 2822, Int.ofNat (nat_lit 2523934022400)), (nat_lit 2826, Int.ofNat (nat_lit 259014067200)), (nat_lit 2827, Int.ofNat (nat_lit 945208051200)), (nat_lit 2828, Int.ofNat (nat_lit 1631402035200)), (nat_lit 2829, Int.ofNat (nat_lit 9159807182400)), (nat_lit 2830, Int.ofNat (nat_lit 3879597682800)), (nat_lit 2831, Int.ofNat (nat_lit 7715012760000)), (nat_lit 2832, Int.ofNat (nat_lit 14815693494000)), (nat_lit 2833, Int.ofNat (nat_lit 23440111203600)), (nat_lit 2834, Int.ofNat (nat_lit 32845738161600)), (nat_lit 2844, Int.ofNat (nat_lit 1061671161600)), (nat_lit 2845, Int.ofNat (nat_lit 680402016000)), (nat_lit 2846, Int.ofNat (nat_lit 512236166400)), (nat_lit 2847, Int.ofNat (nat_lit 1289278368000))]
def block016_data_flat000 : CoefficientMerge.Poly := [(nat_lit 2449, Int.ofNat (nat_lit 20238042645504))]
theorem block016_data_flat000_step : block016_data_flat000 = (CoefficientMerge.scale (20238042645504 : Int) atom1136Coded) := by decide +kernel
theorem block016_data_flat000_original : block016_data_flat000 = (CoefficientMerge.scale (20238042645504 : Int) atom1136Coded) := by
  rw [block016_data_flat000_step]
def block016_data_flat001 : CoefficientMerge.Poly := [(nat_lit 2450, Int.ofNat (nat_lit 20278634402304))]
theorem block016_data_flat001_step : block016_data_flat001 = (CoefficientMerge.scale (20278634402304 : Int) atom1137Coded) := by decide +kernel
theorem block016_data_flat001_original : block016_data_flat001 = (CoefficientMerge.scale (20278634402304 : Int) atom1137Coded) := by
  rw [block016_data_flat001_step]
def block016_data_flat002 : CoefficientMerge.Poly := [(nat_lit 2449, Int.ofNat (nat_lit 20238042645504)), (nat_lit 2450, Int.ofNat (nat_lit 20278634402304))]
theorem block016_data_flat002_step : block016_data_flat002 = (CoefficientMerge.fastMerge block016_data_flat000 block016_data_flat001) := by decide +kernel
theorem block016_data_flat002_original : block016_data_flat002 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20238042645504 : Int) atom1136Coded) (CoefficientMerge.scale (20278634402304 : Int) atom1137Coded)) := by
  rw [block016_data_flat002_step, block016_data_flat000_original, block016_data_flat001_original]
def block016_data_flat003 : CoefficientMerge.Poly := [(nat_lit 2451, Int.ofNat (nat_lit 29238383522304))]
theorem block016_data_flat003_step : block016_data_flat003 = (CoefficientMerge.scale (29238383522304 : Int) atom1138Coded) := by decide +kernel
theorem block016_data_flat003_original : block016_data_flat003 = (CoefficientMerge.scale (29238383522304 : Int) atom1138Coded) := by
  rw [block016_data_flat003_step]
def block016_data_flat004 : CoefficientMerge.Poly := [(nat_lit 2452, Int.ofNat (nat_lit 26787755370240))]
theorem block016_data_flat004_step : block016_data_flat004 = (CoefficientMerge.scale (26787755370240 : Int) atom1139Coded) := by decide +kernel
theorem block016_data_flat004_original : block016_data_flat004 = (CoefficientMerge.scale (26787755370240 : Int) atom1139Coded) := by
  rw [block016_data_flat004_step]
def block016_data_flat005 : CoefficientMerge.Poly := [(nat_lit 2453, Int.ofNat (nat_lit 39115299746304))]
theorem block016_data_flat005_step : block016_data_flat005 = (CoefficientMerge.scale (39115299746304 : Int) atom1140Coded) := by decide +kernel
theorem block016_data_flat005_original : block016_data_flat005 = (CoefficientMerge.scale (39115299746304 : Int) atom1140Coded) := by
  rw [block016_data_flat005_step]
def block016_data_flat006 : CoefficientMerge.Poly := [(nat_lit 2452, Int.ofNat (nat_lit 26787755370240)), (nat_lit 2453, Int.ofNat (nat_lit 39115299746304))]
theorem block016_data_flat006_step : block016_data_flat006 = (CoefficientMerge.fastMerge block016_data_flat004 block016_data_flat005) := by decide +kernel
theorem block016_data_flat006_original : block016_data_flat006 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26787755370240 : Int) atom1139Coded) (CoefficientMerge.scale (39115299746304 : Int) atom1140Coded)) := by
  rw [block016_data_flat006_step, block016_data_flat004_original, block016_data_flat005_original]
def block016_data_flat007 : CoefficientMerge.Poly := [(nat_lit 2451, Int.ofNat (nat_lit 29238383522304)), (nat_lit 2452, Int.ofNat (nat_lit 26787755370240)), (nat_lit 2453, Int.ofNat (nat_lit 39115299746304))]
theorem block016_data_flat007_step : block016_data_flat007 = (CoefficientMerge.fastMerge block016_data_flat003 block016_data_flat006) := by decide +kernel
theorem block016_data_flat007_original : block016_data_flat007 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (29238383522304 : Int) atom1138Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26787755370240 : Int) atom1139Coded) (CoefficientMerge.scale (39115299746304 : Int) atom1140Coded))) := by
  rw [block016_data_flat007_step, block016_data_flat003_original, block016_data_flat006_original]
def block016_data_flat008 : CoefficientMerge.Poly := [(nat_lit 2449, Int.ofNat (nat_lit 20238042645504)), (nat_lit 2450, Int.ofNat (nat_lit 20278634402304)), (nat_lit 2451, Int.ofNat (nat_lit 29238383522304)), (nat_lit 2452, Int.ofNat (nat_lit 26787755370240)), (nat_lit 2453, Int.ofNat (nat_lit 39115299746304))]
theorem block016_data_flat008_step : block016_data_flat008 = (CoefficientMerge.fastMerge block016_data_flat002 block016_data_flat007) := by decide +kernel
theorem block016_data_flat008_original : block016_data_flat008 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20238042645504 : Int) atom1136Coded) (CoefficientMerge.scale (20278634402304 : Int) atom1137Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29238383522304 : Int) atom1138Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26787755370240 : Int) atom1139Coded) (CoefficientMerge.scale (39115299746304 : Int) atom1140Coded)))) := by
  rw [block016_data_flat008_step, block016_data_flat002_original, block016_data_flat007_original]
def block016_data_flat009 : CoefficientMerge.Poly := [(nat_lit 2454, Int.ofNat (nat_lit 39724813792512))]
theorem block016_data_flat009_step : block016_data_flat009 = (CoefficientMerge.scale (39724813792512 : Int) atom1141Coded) := by decide +kernel
theorem block016_data_flat009_original : block016_data_flat009 = (CoefficientMerge.scale (39724813792512 : Int) atom1141Coded) := by
  rw [block016_data_flat009_step]
def block016_data_flat010 : CoefficientMerge.Poly := [(nat_lit 2455, Int.ofNat (nat_lit 48335988821760))]
theorem block016_data_flat010_step : block016_data_flat010 = (CoefficientMerge.scale (48335988821760 : Int) atom1142Coded) := by decide +kernel
theorem block016_data_flat010_original : block016_data_flat010 = (CoefficientMerge.scale (48335988821760 : Int) atom1142Coded) := by
  rw [block016_data_flat010_step]
def block016_data_flat011 : CoefficientMerge.Poly := [(nat_lit 2454, Int.ofNat (nat_lit 39724813792512)), (nat_lit 2455, Int.ofNat (nat_lit 48335988821760))]
theorem block016_data_flat011_step : block016_data_flat011 = (CoefficientMerge.fastMerge block016_data_flat009 block016_data_flat010) := by decide +kernel
theorem block016_data_flat011_original : block016_data_flat011 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (39724813792512 : Int) atom1141Coded) (CoefficientMerge.scale (48335988821760 : Int) atom1142Coded)) := by
  rw [block016_data_flat011_step, block016_data_flat009_original, block016_data_flat010_original]
def block016_data_flat012 : CoefficientMerge.Poly := [(nat_lit 2456, Int.ofNat (nat_lit 56947163851008))]
theorem block016_data_flat012_step : block016_data_flat012 = (CoefficientMerge.scale (56947163851008 : Int) atom1143Coded) := by decide +kernel
theorem block016_data_flat012_original : block016_data_flat012 = (CoefficientMerge.scale (56947163851008 : Int) atom1143Coded) := by
  rw [block016_data_flat012_step]
def block016_data_flat013 : CoefficientMerge.Poly := [(nat_lit 2469, Int.ofNat (nat_lit 13458536612352))]
theorem block016_data_flat013_step : block016_data_flat013 = (CoefficientMerge.scale (13458536612352 : Int) atom1144Coded) := by decide +kernel
theorem block016_data_flat013_original : block016_data_flat013 = (CoefficientMerge.scale (13458536612352 : Int) atom1144Coded) := by
  rw [block016_data_flat013_step]
def block016_data_flat014 : CoefficientMerge.Poly := [(nat_lit 2470, Int.ofNat (nat_lit 25686756405504))]
theorem block016_data_flat014_step : block016_data_flat014 = (CoefficientMerge.scale (25686756405504 : Int) atom1145Coded) := by decide +kernel
theorem block016_data_flat014_original : block016_data_flat014 = (CoefficientMerge.scale (25686756405504 : Int) atom1145Coded) := by
  rw [block016_data_flat014_step]
def block016_data_flat015 : CoefficientMerge.Poly := [(nat_lit 2469, Int.ofNat (nat_lit 13458536612352)), (nat_lit 2470, Int.ofNat (nat_lit 25686756405504))]
theorem block016_data_flat015_step : block016_data_flat015 = (CoefficientMerge.fastMerge block016_data_flat013 block016_data_flat014) := by decide +kernel
theorem block016_data_flat015_original : block016_data_flat015 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (13458536612352 : Int) atom1144Coded) (CoefficientMerge.scale (25686756405504 : Int) atom1145Coded)) := by
  rw [block016_data_flat015_step, block016_data_flat013_original, block016_data_flat014_original]
def block016_data_flat016 : CoefficientMerge.Poly := [(nat_lit 2456, Int.ofNat (nat_lit 56947163851008)), (nat_lit 2469, Int.ofNat (nat_lit 13458536612352)), (nat_lit 2470, Int.ofNat (nat_lit 25686756405504))]
theorem block016_data_flat016_step : block016_data_flat016 = (CoefficientMerge.fastMerge block016_data_flat012 block016_data_flat015) := by decide +kernel
theorem block016_data_flat016_original : block016_data_flat016 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (56947163851008 : Int) atom1143Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13458536612352 : Int) atom1144Coded) (CoefficientMerge.scale (25686756405504 : Int) atom1145Coded))) := by
  rw [block016_data_flat016_step, block016_data_flat012_original, block016_data_flat015_original]
def block016_data_flat017 : CoefficientMerge.Poly := [(nat_lit 2454, Int.ofNat (nat_lit 39724813792512)), (nat_lit 2455, Int.ofNat (nat_lit 48335988821760)), (nat_lit 2456, Int.ofNat (nat_lit 56947163851008)), (nat_lit 2469, Int.ofNat (nat_lit 13458536612352)), (nat_lit 2470, Int.ofNat (nat_lit 25686756405504))]
theorem block016_data_flat017_step : block016_data_flat017 = (CoefficientMerge.fastMerge block016_data_flat011 block016_data_flat016) := by decide +kernel
theorem block016_data_flat017_original : block016_data_flat017 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39724813792512 : Int) atom1141Coded) (CoefficientMerge.scale (48335988821760 : Int) atom1142Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56947163851008 : Int) atom1143Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13458536612352 : Int) atom1144Coded) (CoefficientMerge.scale (25686756405504 : Int) atom1145Coded)))) := by
  rw [block016_data_flat017_step, block016_data_flat011_original, block016_data_flat016_original]
def block016_data_flat018 : CoefficientMerge.Poly := [(nat_lit 2449, Int.ofNat (nat_lit 20238042645504)), (nat_lit 2450, Int.ofNat (nat_lit 20278634402304)), (nat_lit 2451, Int.ofNat (nat_lit 29238383522304)), (nat_lit 2452, Int.ofNat (nat_lit 26787755370240)), (nat_lit 2453, Int.ofNat (nat_lit 39115299746304)), (nat_lit 2454, Int.ofNat (nat_lit 39724813792512)), (nat_lit 2455, Int.ofNat (nat_lit 48335988821760)), (nat_lit 2456, Int.ofNat (nat_lit 56947163851008)), (nat_lit 2469, Int.ofNat (nat_lit 13458536612352)), (nat_lit 2470, Int.ofNat (nat_lit 25686756405504))]
theorem block016_data_flat018_step : block016_data_flat018 = (CoefficientMerge.fastMerge block016_data_flat008 block016_data_flat017) := by decide +kernel
theorem block016_data_flat018_original : block016_data_flat018 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20238042645504 : Int) atom1136Coded) (CoefficientMerge.scale (20278634402304 : Int) atom1137Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29238383522304 : Int) atom1138Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26787755370240 : Int) atom1139Coded) (CoefficientMerge.scale (39115299746304 : Int) atom1140Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39724813792512 : Int) atom1141Coded) (CoefficientMerge.scale (48335988821760 : Int) atom1142Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56947163851008 : Int) atom1143Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13458536612352 : Int) atom1144Coded) (CoefficientMerge.scale (25686756405504 : Int) atom1145Coded))))) := by
  rw [block016_data_flat018_step, block016_data_flat008_original, block016_data_flat017_original]
def block016_data_flat019 : CoefficientMerge.Poly := [(nat_lit 2471, Int.ofNat (nat_lit 25145532981504))]
theorem block016_data_flat019_step : block016_data_flat019 = (CoefficientMerge.scale (25145532981504 : Int) atom1146Coded) := by decide +kernel
theorem block016_data_flat019_original : block016_data_flat019 = (CoefficientMerge.scale (25145532981504 : Int) atom1146Coded) := by
  rw [block016_data_flat019_step]
def block016_data_flat020 : CoefficientMerge.Poly := [(nat_lit 2472, Int.ofNat (nat_lit 29937883845504))]
theorem block016_data_flat020_step : block016_data_flat020 = (CoefficientMerge.scale (29937883845504 : Int) atom1147Coded) := by decide +kernel
theorem block016_data_flat020_original : block016_data_flat020 = (CoefficientMerge.scale (29937883845504 : Int) atom1147Coded) := by
  rw [block016_data_flat020_step]
def block016_data_flat021 : CoefficientMerge.Poly := [(nat_lit 2471, Int.ofNat (nat_lit 25145532981504)), (nat_lit 2472, Int.ofNat (nat_lit 29937883845504))]
theorem block016_data_flat021_step : block016_data_flat021 = (CoefficientMerge.fastMerge block016_data_flat019 block016_data_flat020) := by decide +kernel
theorem block016_data_flat021_original : block016_data_flat021 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (25145532981504 : Int) atom1146Coded) (CoefficientMerge.scale (29937883845504 : Int) atom1147Coded)) := by
  rw [block016_data_flat021_step, block016_data_flat019_original, block016_data_flat020_original]
def block016_data_flat022 : CoefficientMerge.Poly := [(nat_lit 2473, Int.ofNat (nat_lit 29509938218240))]
theorem block016_data_flat022_step : block016_data_flat022 = (CoefficientMerge.scale (29509938218240 : Int) atom1148Coded) := by decide +kernel
theorem block016_data_flat022_original : block016_data_flat022 = (CoefficientMerge.scale (29509938218240 : Int) atom1148Coded) := by
  rw [block016_data_flat022_step]
def block016_data_flat023 : CoefficientMerge.Poly := [(nat_lit 2474, Int.ofNat (nat_lit 40443829119104))]
theorem block016_data_flat023_step : block016_data_flat023 = (CoefficientMerge.scale (40443829119104 : Int) atom1149Coded) := by decide +kernel
theorem block016_data_flat023_original : block016_data_flat023 = (CoefficientMerge.scale (40443829119104 : Int) atom1149Coded) := by
  rw [block016_data_flat023_step]
def block016_data_flat024 : CoefficientMerge.Poly := [(nat_lit 2475, Int.ofNat (nat_lit 41715097976512))]
theorem block016_data_flat024_step : block016_data_flat024 = (CoefficientMerge.scale (41715097976512 : Int) atom1150Coded) := by decide +kernel
theorem block016_data_flat024_original : block016_data_flat024 = (CoefficientMerge.scale (41715097976512 : Int) atom1150Coded) := by
  rw [block016_data_flat024_step]
def block016_data_flat025 : CoefficientMerge.Poly := [(nat_lit 2474, Int.ofNat (nat_lit 40443829119104)), (nat_lit 2475, Int.ofNat (nat_lit 41715097976512))]
theorem block016_data_flat025_step : block016_data_flat025 = (CoefficientMerge.fastMerge block016_data_flat023 block016_data_flat024) := by decide +kernel
theorem block016_data_flat025_original : block016_data_flat025 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40443829119104 : Int) atom1149Coded) (CoefficientMerge.scale (41715097976512 : Int) atom1150Coded)) := by
  rw [block016_data_flat025_step, block016_data_flat023_original, block016_data_flat024_original]
def block016_data_flat026 : CoefficientMerge.Poly := [(nat_lit 2473, Int.ofNat (nat_lit 29509938218240)), (nat_lit 2474, Int.ofNat (nat_lit 40443829119104)), (nat_lit 2475, Int.ofNat (nat_lit 41715097976512))]
theorem block016_data_flat026_step : block016_data_flat026 = (CoefficientMerge.fastMerge block016_data_flat022 block016_data_flat025) := by decide +kernel
theorem block016_data_flat026_original : block016_data_flat026 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (29509938218240 : Int) atom1148Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40443829119104 : Int) atom1149Coded) (CoefficientMerge.scale (41715097976512 : Int) atom1150Coded))) := by
  rw [block016_data_flat026_step, block016_data_flat022_original, block016_data_flat025_original]
def block016_data_flat027 : CoefficientMerge.Poly := [(nat_lit 2471, Int.ofNat (nat_lit 25145532981504)), (nat_lit 2472, Int.ofNat (nat_lit 29937883845504)), (nat_lit 2473, Int.ofNat (nat_lit 29509938218240)), (nat_lit 2474, Int.ofNat (nat_lit 40443829119104)), (nat_lit 2475, Int.ofNat (nat_lit 41715097976512))]
theorem block016_data_flat027_step : block016_data_flat027 = (CoefficientMerge.fastMerge block016_data_flat021 block016_data_flat026) := by decide +kernel
theorem block016_data_flat027_original : block016_data_flat027 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25145532981504 : Int) atom1146Coded) (CoefficientMerge.scale (29937883845504 : Int) atom1147Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29509938218240 : Int) atom1148Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40443829119104 : Int) atom1149Coded) (CoefficientMerge.scale (41715097976512 : Int) atom1150Coded)))) := by
  rw [block016_data_flat027_step, block016_data_flat021_original, block016_data_flat026_original]
def block016_data_flat028 : CoefficientMerge.Poly := [(nat_lit 2476, Int.ofNat (nat_lit 49283350901760))]
theorem block016_data_flat028_step : block016_data_flat028 = (CoefficientMerge.scale (49283350901760 : Int) atom1151Coded) := by decide +kernel
theorem block016_data_flat028_original : block016_data_flat028 = (CoefficientMerge.scale (49283350901760 : Int) atom1151Coded) := by
  rw [block016_data_flat028_step]
def block016_data_flat029 : CoefficientMerge.Poly := [(nat_lit 2477, Int.ofNat (nat_lit 57682924975008))]
theorem block016_data_flat029_step : block016_data_flat029 = (CoefficientMerge.scale (57682924975008 : Int) atom1152Coded) := by decide +kernel
theorem block016_data_flat029_original : block016_data_flat029 = (CoefficientMerge.scale (57682924975008 : Int) atom1152Coded) := by
  rw [block016_data_flat029_step]
def block016_data_flat030 : CoefficientMerge.Poly := [(nat_lit 2476, Int.ofNat (nat_lit 49283350901760)), (nat_lit 2477, Int.ofNat (nat_lit 57682924975008))]
theorem block016_data_flat030_step : block016_data_flat030 = (CoefficientMerge.fastMerge block016_data_flat028 block016_data_flat029) := by decide +kernel
theorem block016_data_flat030_original : block016_data_flat030 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (49283350901760 : Int) atom1151Coded) (CoefficientMerge.scale (57682924975008 : Int) atom1152Coded)) := by
  rw [block016_data_flat030_step, block016_data_flat028_original, block016_data_flat029_original]
def block016_data_flat031 : CoefficientMerge.Poly := [(nat_lit 2491, Int.ofNat (nat_lit 16376678929152))]
theorem block016_data_flat031_step : block016_data_flat031 = (CoefficientMerge.scale (16376678929152 : Int) atom1153Coded) := by decide +kernel
theorem block016_data_flat031_original : block016_data_flat031 = (CoefficientMerge.scale (16376678929152 : Int) atom1153Coded) := by
  rw [block016_data_flat031_step]
def block016_data_flat032 : CoefficientMerge.Poly := [(nat_lit 2492, Int.ofNat (nat_lit 30291619682304))]
theorem block016_data_flat032_step : block016_data_flat032 = (CoefficientMerge.scale (30291619682304 : Int) atom1154Coded) := by decide +kernel
theorem block016_data_flat032_original : block016_data_flat032 = (CoefficientMerge.scale (30291619682304 : Int) atom1154Coded) := by
  rw [block016_data_flat032_step]
def block016_data_flat033 : CoefficientMerge.Poly := [(nat_lit 2493, Int.ofNat (nat_lit 34213038813504))]
theorem block016_data_flat033_step : block016_data_flat033 = (CoefficientMerge.scale (34213038813504 : Int) atom1155Coded) := by decide +kernel
theorem block016_data_flat033_original : block016_data_flat033 = (CoefficientMerge.scale (34213038813504 : Int) atom1155Coded) := by
  rw [block016_data_flat033_step]
def block016_data_flat034 : CoefficientMerge.Poly := [(nat_lit 2492, Int.ofNat (nat_lit 30291619682304)), (nat_lit 2493, Int.ofNat (nat_lit 34213038813504))]
theorem block016_data_flat034_step : block016_data_flat034 = (CoefficientMerge.fastMerge block016_data_flat032 block016_data_flat033) := by decide +kernel
theorem block016_data_flat034_original : block016_data_flat034 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (30291619682304 : Int) atom1154Coded) (CoefficientMerge.scale (34213038813504 : Int) atom1155Coded)) := by
  rw [block016_data_flat034_step, block016_data_flat032_original, block016_data_flat033_original]
def block016_data_flat035 : CoefficientMerge.Poly := [(nat_lit 2491, Int.ofNat (nat_lit 16376678929152)), (nat_lit 2492, Int.ofNat (nat_lit 30291619682304)), (nat_lit 2493, Int.ofNat (nat_lit 34213038813504))]
theorem block016_data_flat035_step : block016_data_flat035 = (CoefficientMerge.fastMerge block016_data_flat031 block016_data_flat034) := by decide +kernel
theorem block016_data_flat035_original : block016_data_flat035 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16376678929152 : Int) atom1153Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30291619682304 : Int) atom1154Coded) (CoefficientMerge.scale (34213038813504 : Int) atom1155Coded))) := by
  rw [block016_data_flat035_step, block016_data_flat031_original, block016_data_flat034_original]
def block016_data_flat036 : CoefficientMerge.Poly := [(nat_lit 2476, Int.ofNat (nat_lit 49283350901760)), (nat_lit 2477, Int.ofNat (nat_lit 57682924975008)), (nat_lit 2491, Int.ofNat (nat_lit 16376678929152)), (nat_lit 2492, Int.ofNat (nat_lit 30291619682304)), (nat_lit 2493, Int.ofNat (nat_lit 34213038813504))]
theorem block016_data_flat036_step : block016_data_flat036 = (CoefficientMerge.fastMerge block016_data_flat030 block016_data_flat035) := by decide +kernel
theorem block016_data_flat036_original : block016_data_flat036 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49283350901760 : Int) atom1151Coded) (CoefficientMerge.scale (57682924975008 : Int) atom1152Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16376678929152 : Int) atom1153Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30291619682304 : Int) atom1154Coded) (CoefficientMerge.scale (34213038813504 : Int) atom1155Coded)))) := by
  rw [block016_data_flat036_step, block016_data_flat030_original, block016_data_flat035_original]
def block016_data_flat037 : CoefficientMerge.Poly := [(nat_lit 2471, Int.ofNat (nat_lit 25145532981504)), (nat_lit 2472, Int.ofNat (nat_lit 29937883845504)), (nat_lit 2473, Int.ofNat (nat_lit 29509938218240)), (nat_lit 2474, Int.ofNat (nat_lit 40443829119104)), (nat_lit 2475, Int.ofNat (nat_lit 41715097976512)), (nat_lit 2476, Int.ofNat (nat_lit 49283350901760)), (nat_lit 2477, Int.ofNat (nat_lit 57682924975008)), (nat_lit 2491, Int.ofNat (nat_lit 16376678929152)), (nat_lit 2492, Int.ofNat (nat_lit 30291619682304)), (nat_lit 2493, Int.ofNat (nat_lit 34213038813504))]
theorem block016_data_flat037_step : block016_data_flat037 = (CoefficientMerge.fastMerge block016_data_flat027 block016_data_flat036) := by decide +kernel
theorem block016_data_flat037_original : block016_data_flat037 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25145532981504 : Int) atom1146Coded) (CoefficientMerge.scale (29937883845504 : Int) atom1147Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29509938218240 : Int) atom1148Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40443829119104 : Int) atom1149Coded) (CoefficientMerge.scale (41715097976512 : Int) atom1150Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49283350901760 : Int) atom1151Coded) (CoefficientMerge.scale (57682924975008 : Int) atom1152Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16376678929152 : Int) atom1153Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30291619682304 : Int) atom1154Coded) (CoefficientMerge.scale (34213038813504 : Int) atom1155Coded))))) := by
  rw [block016_data_flat037_step, block016_data_flat027_original, block016_data_flat036_original]
def block016_data_flat038 : CoefficientMerge.Poly := [(nat_lit 2449, Int.ofNat (nat_lit 20238042645504)), (nat_lit 2450, Int.ofNat (nat_lit 20278634402304)), (nat_lit 2451, Int.ofNat (nat_lit 29238383522304)), (nat_lit 2452, Int.ofNat (nat_lit 26787755370240)), (nat_lit 2453, Int.ofNat (nat_lit 39115299746304)), (nat_lit 2454, Int.ofNat (nat_lit 39724813792512)), (nat_lit 2455, Int.ofNat (nat_lit 48335988821760)), (nat_lit 2456, Int.ofNat (nat_lit 56947163851008)), (nat_lit 2469, Int.ofNat (nat_lit 13458536612352)), (nat_lit 2470, Int.ofNat (nat_lit 25686756405504)), (nat_lit 2471, Int.ofNat (nat_lit 25145532981504)), (nat_lit 2472, Int.ofNat (nat_lit 29937883845504)), (nat_lit 2473, Int.ofNat (nat_lit 29509938218240)), (nat_lit 2474, Int.ofNat (nat_lit 40443829119104)), (nat_lit 2475, Int.ofNat (nat_lit 41715097976512)), (nat_lit 2476, Int.ofNat (nat_lit 49283350901760)), (nat_lit 2477, Int.ofNat (nat_lit 57682924975008)), (nat_lit 2491, Int.ofNat (nat_lit 16376678929152)), (nat_lit 2492, Int.ofNat (nat_lit 30291619682304)), (nat_lit 2493, Int.ofNat (nat_lit 34213038813504))]
theorem block016_data_flat038_step : block016_data_flat038 = (CoefficientMerge.fastMerge block016_data_flat018 block016_data_flat037) := by decide +kernel
theorem block016_data_flat038_original : block016_data_flat038 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20238042645504 : Int) atom1136Coded) (CoefficientMerge.scale (20278634402304 : Int) atom1137Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29238383522304 : Int) atom1138Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26787755370240 : Int) atom1139Coded) (CoefficientMerge.scale (39115299746304 : Int) atom1140Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39724813792512 : Int) atom1141Coded) (CoefficientMerge.scale (48335988821760 : Int) atom1142Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56947163851008 : Int) atom1143Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13458536612352 : Int) atom1144Coded) (CoefficientMerge.scale (25686756405504 : Int) atom1145Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25145532981504 : Int) atom1146Coded) (CoefficientMerge.scale (29937883845504 : Int) atom1147Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29509938218240 : Int) atom1148Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40443829119104 : Int) atom1149Coded) (CoefficientMerge.scale (41715097976512 : Int) atom1150Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49283350901760 : Int) atom1151Coded) (CoefficientMerge.scale (57682924975008 : Int) atom1152Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16376678929152 : Int) atom1153Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30291619682304 : Int) atom1154Coded) (CoefficientMerge.scale (34213038813504 : Int) atom1155Coded)))))) := by
  rw [block016_data_flat038_step, block016_data_flat018_original, block016_data_flat037_original]
def block016_data_flat039 : CoefficientMerge.Poly := [(nat_lit 2494, Int.ofNat (nat_lit 32778158869440))]
theorem block016_data_flat039_step : block016_data_flat039 = (CoefficientMerge.scale (32778158869440 : Int) atom1156Coded) := by decide +kernel
theorem block016_data_flat039_original : block016_data_flat039 = (CoefficientMerge.scale (32778158869440 : Int) atom1156Coded) := by
  rw [block016_data_flat039_step]
def block016_data_flat040 : CoefficientMerge.Poly := [(nat_lit 2495, Int.ofNat (nat_lit 45968048642304))]
theorem block016_data_flat040_step : block016_data_flat040 = (CoefficientMerge.scale (45968048642304 : Int) atom1157Coded) := by decide +kernel
theorem block016_data_flat040_original : block016_data_flat040 = (CoefficientMerge.scale (45968048642304 : Int) atom1157Coded) := by
  rw [block016_data_flat040_step]
def block016_data_flat041 : CoefficientMerge.Poly := [(nat_lit 2494, Int.ofNat (nat_lit 32778158869440)), (nat_lit 2495, Int.ofNat (nat_lit 45968048642304))]
theorem block016_data_flat041_step : block016_data_flat041 = (CoefficientMerge.fastMerge block016_data_flat039 block016_data_flat040) := by decide +kernel
theorem block016_data_flat041_original : block016_data_flat041 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (32778158869440 : Int) atom1156Coded) (CoefficientMerge.scale (45968048642304 : Int) atom1157Coded)) := by
  rw [block016_data_flat041_step, block016_data_flat039_original, block016_data_flat040_original]
def block016_data_flat042 : CoefficientMerge.Poly := [(nat_lit 2496, Int.ofNat (nat_lit 48255838538112))]
theorem block016_data_flat042_step : block016_data_flat042 = (CoefficientMerge.scale (48255838538112 : Int) atom1158Coded) := by decide +kernel
theorem block016_data_flat042_original : block016_data_flat042 = (CoefficientMerge.scale (48255838538112 : Int) atom1158Coded) := by
  rw [block016_data_flat042_step]
def block016_data_flat043 : CoefficientMerge.Poly := [(nat_lit 2497, Int.ofNat (nat_lit 48971706384960))]
theorem block016_data_flat043_step : block016_data_flat043 = (CoefficientMerge.scale (48971706384960 : Int) atom1159Coded) := by decide +kernel
theorem block016_data_flat043_original : block016_data_flat043 = (CoefficientMerge.scale (48971706384960 : Int) atom1159Coded) := by
  rw [block016_data_flat043_step]
def block016_data_flat044 : CoefficientMerge.Poly := [(nat_lit 2498, Int.ofNat (nat_lit 63039466358208))]
theorem block016_data_flat044_step : block016_data_flat044 = (CoefficientMerge.scale (63039466358208 : Int) atom1160Coded) := by decide +kernel
theorem block016_data_flat044_original : block016_data_flat044 = (CoefficientMerge.scale (63039466358208 : Int) atom1160Coded) := by
  rw [block016_data_flat044_step]
def block016_data_flat045 : CoefficientMerge.Poly := [(nat_lit 2497, Int.ofNat (nat_lit 48971706384960)), (nat_lit 2498, Int.ofNat (nat_lit 63039466358208))]
theorem block016_data_flat045_step : block016_data_flat045 = (CoefficientMerge.fastMerge block016_data_flat043 block016_data_flat044) := by decide +kernel
theorem block016_data_flat045_original : block016_data_flat045 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48971706384960 : Int) atom1159Coded) (CoefficientMerge.scale (63039466358208 : Int) atom1160Coded)) := by
  rw [block016_data_flat045_step, block016_data_flat043_original, block016_data_flat044_original]
def block016_data_flat046 : CoefficientMerge.Poly := [(nat_lit 2496, Int.ofNat (nat_lit 48255838538112)), (nat_lit 2497, Int.ofNat (nat_lit 48971706384960)), (nat_lit 2498, Int.ofNat (nat_lit 63039466358208))]
theorem block016_data_flat046_step : block016_data_flat046 = (CoefficientMerge.fastMerge block016_data_flat042 block016_data_flat045) := by decide +kernel
theorem block016_data_flat046_original : block016_data_flat046 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (48255838538112 : Int) atom1158Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48971706384960 : Int) atom1159Coded) (CoefficientMerge.scale (63039466358208 : Int) atom1160Coded))) := by
  rw [block016_data_flat046_step, block016_data_flat042_original, block016_data_flat045_original]
def block016_data_flat047 : CoefficientMerge.Poly := [(nat_lit 2494, Int.ofNat (nat_lit 32778158869440)), (nat_lit 2495, Int.ofNat (nat_lit 45968048642304)), (nat_lit 2496, Int.ofNat (nat_lit 48255838538112)), (nat_lit 2497, Int.ofNat (nat_lit 48971706384960)), (nat_lit 2498, Int.ofNat (nat_lit 63039466358208))]
theorem block016_data_flat047_step : block016_data_flat047 = (CoefficientMerge.fastMerge block016_data_flat041 block016_data_flat046) := by decide +kernel
theorem block016_data_flat047_original : block016_data_flat047 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32778158869440 : Int) atom1156Coded) (CoefficientMerge.scale (45968048642304 : Int) atom1157Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48255838538112 : Int) atom1158Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48971706384960 : Int) atom1159Coded) (CoefficientMerge.scale (63039466358208 : Int) atom1160Coded)))) := by
  rw [block016_data_flat047_step, block016_data_flat041_original, block016_data_flat046_original]
def block016_data_flat048 : CoefficientMerge.Poly := [(nat_lit 2513, Int.ofNat (nat_lit 20331751940352))]
theorem block016_data_flat048_step : block016_data_flat048 = (CoefficientMerge.scale (20331751940352 : Int) atom1161Coded) := by decide +kernel
theorem block016_data_flat048_original : block016_data_flat048 = (CoefficientMerge.scale (20331751940352 : Int) atom1161Coded) := by
  rw [block016_data_flat048_step]
def block016_data_flat049 : CoefficientMerge.Poly := [(nat_lit 2514, Int.ofNat (nat_lit 38507308418304))]
theorem block016_data_flat049_step : block016_data_flat049 = (CoefficientMerge.scale (38507308418304 : Int) atom1162Coded) := by decide +kernel
theorem block016_data_flat049_original : block016_data_flat049 = (CoefficientMerge.scale (38507308418304 : Int) atom1162Coded) := by
  rw [block016_data_flat049_step]
def block016_data_flat050 : CoefficientMerge.Poly := [(nat_lit 2513, Int.ofNat (nat_lit 20331751940352)), (nat_lit 2514, Int.ofNat (nat_lit 38507308418304))]
theorem block016_data_flat050_step : block016_data_flat050 = (CoefficientMerge.fastMerge block016_data_flat048 block016_data_flat049) := by decide +kernel
theorem block016_data_flat050_original : block016_data_flat050 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (20331751940352 : Int) atom1161Coded) (CoefficientMerge.scale (38507308418304 : Int) atom1162Coded)) := by
  rw [block016_data_flat050_step, block016_data_flat048_original, block016_data_flat049_original]
def block016_data_flat051 : CoefficientMerge.Poly := [(nat_lit 2515, Int.ofNat (nat_lit 35927230083840))]
theorem block016_data_flat051_step : block016_data_flat051 = (CoefficientMerge.scale (35927230083840 : Int) atom1163Coded) := by decide +kernel
theorem block016_data_flat051_original : block016_data_flat051 = (CoefficientMerge.scale (35927230083840 : Int) atom1163Coded) := by
  rw [block016_data_flat051_step]
def block016_data_flat052 : CoefficientMerge.Poly := [(nat_lit 2516, Int.ofNat (nat_lit 53554841282304))]
theorem block016_data_flat052_step : block016_data_flat052 = (CoefficientMerge.scale (53554841282304 : Int) atom1164Coded) := by decide +kernel
theorem block016_data_flat052_original : block016_data_flat052 = (CoefficientMerge.scale (53554841282304 : Int) atom1164Coded) := by
  rw [block016_data_flat052_step]
def block016_data_flat053 : CoefficientMerge.Poly := [(nat_lit 2517, Int.ofNat (nat_lit 57013026832512))]
theorem block016_data_flat053_step : block016_data_flat053 = (CoefficientMerge.scale (57013026832512 : Int) atom1165Coded) := by decide +kernel
theorem block016_data_flat053_original : block016_data_flat053 = (CoefficientMerge.scale (57013026832512 : Int) atom1165Coded) := by
  rw [block016_data_flat053_step]
def block016_data_flat054 : CoefficientMerge.Poly := [(nat_lit 2516, Int.ofNat (nat_lit 53554841282304)), (nat_lit 2517, Int.ofNat (nat_lit 57013026832512))]
theorem block016_data_flat054_step : block016_data_flat054 = (CoefficientMerge.fastMerge block016_data_flat052 block016_data_flat053) := by decide +kernel
theorem block016_data_flat054_original : block016_data_flat054 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (53554841282304 : Int) atom1164Coded) (CoefficientMerge.scale (57013026832512 : Int) atom1165Coded)) := by
  rw [block016_data_flat054_step, block016_data_flat052_original, block016_data_flat053_original]
def block016_data_flat055 : CoefficientMerge.Poly := [(nat_lit 2515, Int.ofNat (nat_lit 35927230083840)), (nat_lit 2516, Int.ofNat (nat_lit 53554841282304)), (nat_lit 2517, Int.ofNat (nat_lit 57013026832512))]
theorem block016_data_flat055_step : block016_data_flat055 = (CoefficientMerge.fastMerge block016_data_flat051 block016_data_flat054) := by decide +kernel
theorem block016_data_flat055_original : block016_data_flat055 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (35927230083840 : Int) atom1163Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53554841282304 : Int) atom1164Coded) (CoefficientMerge.scale (57013026832512 : Int) atom1165Coded))) := by
  rw [block016_data_flat055_step, block016_data_flat051_original, block016_data_flat054_original]
def block016_data_flat056 : CoefficientMerge.Poly := [(nat_lit 2513, Int.ofNat (nat_lit 20331751940352)), (nat_lit 2514, Int.ofNat (nat_lit 38507308418304)), (nat_lit 2515, Int.ofNat (nat_lit 35927230083840)), (nat_lit 2516, Int.ofNat (nat_lit 53554841282304)), (nat_lit 2517, Int.ofNat (nat_lit 57013026832512))]
theorem block016_data_flat056_step : block016_data_flat056 = (CoefficientMerge.fastMerge block016_data_flat050 block016_data_flat055) := by decide +kernel
theorem block016_data_flat056_original : block016_data_flat056 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20331751940352 : Int) atom1161Coded) (CoefficientMerge.scale (38507308418304 : Int) atom1162Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35927230083840 : Int) atom1163Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53554841282304 : Int) atom1164Coded) (CoefficientMerge.scale (57013026832512 : Int) atom1165Coded)))) := by
  rw [block016_data_flat056_step, block016_data_flat050_original, block016_data_flat055_original]
def block016_data_flat057 : CoefficientMerge.Poly := [(nat_lit 2494, Int.ofNat (nat_lit 32778158869440)), (nat_lit 2495, Int.ofNat (nat_lit 45968048642304)), (nat_lit 2496, Int.ofNat (nat_lit 48255838538112)), (nat_lit 2497, Int.ofNat (nat_lit 48971706384960)), (nat_lit 2498, Int.ofNat (nat_lit 63039466358208)), (nat_lit 2513, Int.ofNat (nat_lit 20331751940352)), (nat_lit 2514, Int.ofNat (nat_lit 38507308418304)), (nat_lit 2515, Int.ofNat (nat_lit 35927230083840)), (nat_lit 2516, Int.ofNat (nat_lit 53554841282304)), (nat_lit 2517, Int.ofNat (nat_lit 57013026832512))]
theorem block016_data_flat057_step : block016_data_flat057 = (CoefficientMerge.fastMerge block016_data_flat047 block016_data_flat056) := by decide +kernel
theorem block016_data_flat057_original : block016_data_flat057 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32778158869440 : Int) atom1156Coded) (CoefficientMerge.scale (45968048642304 : Int) atom1157Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48255838538112 : Int) atom1158Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48971706384960 : Int) atom1159Coded) (CoefficientMerge.scale (63039466358208 : Int) atom1160Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20331751940352 : Int) atom1161Coded) (CoefficientMerge.scale (38507308418304 : Int) atom1162Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35927230083840 : Int) atom1163Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53554841282304 : Int) atom1164Coded) (CoefficientMerge.scale (57013026832512 : Int) atom1165Coded))))) := by
  rw [block016_data_flat057_step, block016_data_flat047_original, block016_data_flat056_original]
def block016_data_flat058 : CoefficientMerge.Poly := [(nat_lit 2518, Int.ofNat (nat_lit 52848874978560))]
theorem block016_data_flat058_step : block016_data_flat058 = (CoefficientMerge.scale (52848874978560 : Int) atom1166Coded) := by decide +kernel
theorem block016_data_flat058_original : block016_data_flat058 = (CoefficientMerge.scale (52848874978560 : Int) atom1166Coded) := by
  rw [block016_data_flat058_step]
def block016_data_flat059 : CoefficientMerge.Poly := [(nat_lit 2519, Int.ofNat (nat_lit 72684357715008))]
theorem block016_data_flat059_step : block016_data_flat059 = (CoefficientMerge.scale (72684357715008 : Int) atom1167Coded) := by decide +kernel
theorem block016_data_flat059_original : block016_data_flat059 = (CoefficientMerge.scale (72684357715008 : Int) atom1167Coded) := by
  rw [block016_data_flat059_step]
def block016_data_flat060 : CoefficientMerge.Poly := [(nat_lit 2518, Int.ofNat (nat_lit 52848874978560)), (nat_lit 2519, Int.ofNat (nat_lit 72684357715008))]
theorem block016_data_flat060_step : block016_data_flat060 = (CoefficientMerge.fastMerge block016_data_flat058 block016_data_flat059) := by decide +kernel
theorem block016_data_flat060_original : block016_data_flat060 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (52848874978560 : Int) atom1166Coded) (CoefficientMerge.scale (72684357715008 : Int) atom1167Coded)) := by
  rw [block016_data_flat060_step, block016_data_flat058_original, block016_data_flat059_original]
def block016_data_flat061 : CoefficientMerge.Poly := [(nat_lit 2535, Int.ofNat (nat_lit 26020396714752))]
theorem block016_data_flat061_step : block016_data_flat061 = (CoefficientMerge.scale (26020396714752 : Int) atom1168Coded) := by decide +kernel
theorem block016_data_flat061_original : block016_data_flat061 = (CoefficientMerge.scale (26020396714752 : Int) atom1168Coded) := by
  rw [block016_data_flat061_step]
def block016_data_flat062 : CoefficientMerge.Poly := [(nat_lit 2536, Int.ofNat (nat_lit 47998729798272))]
theorem block016_data_flat062_step : block016_data_flat062 = (CoefficientMerge.scale (47998729798272 : Int) atom1169Coded) := by decide +kernel
theorem block016_data_flat062_original : block016_data_flat062 = (CoefficientMerge.scale (47998729798272 : Int) atom1169Coded) := by
  rw [block016_data_flat062_step]
def block016_data_flat063 : CoefficientMerge.Poly := [(nat_lit 2537, Int.ofNat (nat_lit 69989670434304))]
theorem block016_data_flat063_step : block016_data_flat063 = (CoefficientMerge.scale (69989670434304 : Int) atom1170Coded) := by decide +kernel
theorem block016_data_flat063_original : block016_data_flat063 = (CoefficientMerge.scale (69989670434304 : Int) atom1170Coded) := by
  rw [block016_data_flat063_step]
def block016_data_flat064 : CoefficientMerge.Poly := [(nat_lit 2536, Int.ofNat (nat_lit 47998729798272)), (nat_lit 2537, Int.ofNat (nat_lit 69989670434304))]
theorem block016_data_flat064_step : block016_data_flat064 = (CoefficientMerge.fastMerge block016_data_flat062 block016_data_flat063) := by decide +kernel
theorem block016_data_flat064_original : block016_data_flat064 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (47998729798272 : Int) atom1169Coded) (CoefficientMerge.scale (69989670434304 : Int) atom1170Coded)) := by
  rw [block016_data_flat064_step, block016_data_flat062_original, block016_data_flat063_original]
def block016_data_flat065 : CoefficientMerge.Poly := [(nat_lit 2535, Int.ofNat (nat_lit 26020396714752)), (nat_lit 2536, Int.ofNat (nat_lit 47998729798272)), (nat_lit 2537, Int.ofNat (nat_lit 69989670434304))]
theorem block016_data_flat065_step : block016_data_flat065 = (CoefficientMerge.fastMerge block016_data_flat061 block016_data_flat064) := by decide +kernel
theorem block016_data_flat065_original : block016_data_flat065 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (26020396714752 : Int) atom1168Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47998729798272 : Int) atom1169Coded) (CoefficientMerge.scale (69989670434304 : Int) atom1170Coded))) := by
  rw [block016_data_flat065_step, block016_data_flat061_original, block016_data_flat064_original]
def block016_data_flat066 : CoefficientMerge.Poly := [(nat_lit 2518, Int.ofNat (nat_lit 52848874978560)), (nat_lit 2519, Int.ofNat (nat_lit 72684357715008)), (nat_lit 2535, Int.ofNat (nat_lit 26020396714752)), (nat_lit 2536, Int.ofNat (nat_lit 47998729798272)), (nat_lit 2537, Int.ofNat (nat_lit 69989670434304))]
theorem block016_data_flat066_step : block016_data_flat066 = (CoefficientMerge.fastMerge block016_data_flat060 block016_data_flat065) := by decide +kernel
theorem block016_data_flat066_original : block016_data_flat066 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52848874978560 : Int) atom1166Coded) (CoefficientMerge.scale (72684357715008 : Int) atom1167Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26020396714752 : Int) atom1168Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47998729798272 : Int) atom1169Coded) (CoefficientMerge.scale (69989670434304 : Int) atom1170Coded)))) := by
  rw [block016_data_flat066_step, block016_data_flat060_original, block016_data_flat065_original]
def block016_data_flat067 : CoefficientMerge.Poly := [(nat_lit 2538, Int.ofNat (nat_lit 69826861415808))]
theorem block016_data_flat067_step : block016_data_flat067 = (CoefficientMerge.scale (69826861415808 : Int) atom1171Coded) := by decide +kernel
theorem block016_data_flat067_original : block016_data_flat067 = (CoefficientMerge.scale (69826861415808 : Int) atom1171Coded) := by
  rw [block016_data_flat067_step]
def block016_data_flat068 : CoefficientMerge.Poly := [(nat_lit 2539, Int.ofNat (nat_lit 49709608836480))]
theorem block016_data_flat068_step : block016_data_flat068 = (CoefficientMerge.scale (49709608836480 : Int) atom1172Coded) := by decide +kernel
theorem block016_data_flat068_original : block016_data_flat068 = (CoefficientMerge.scale (49709608836480 : Int) atom1172Coded) := by
  rw [block016_data_flat068_step]
def block016_data_flat069 : CoefficientMerge.Poly := [(nat_lit 2538, Int.ofNat (nat_lit 69826861415808)), (nat_lit 2539, Int.ofNat (nat_lit 49709608836480))]
theorem block016_data_flat069_step : block016_data_flat069 = (CoefficientMerge.fastMerge block016_data_flat067 block016_data_flat068) := by decide +kernel
theorem block016_data_flat069_original : block016_data_flat069 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (69826861415808 : Int) atom1171Coded) (CoefficientMerge.scale (49709608836480 : Int) atom1172Coded)) := by
  rw [block016_data_flat069_step, block016_data_flat067_original, block016_data_flat068_original]
def block016_data_flat070 : CoefficientMerge.Poly := [(nat_lit 2540, Int.ofNat (nat_lit 73705078859904))]
theorem block016_data_flat070_step : block016_data_flat070 = (CoefficientMerge.scale (73705078859904 : Int) atom1173Coded) := by decide +kernel
theorem block016_data_flat070_original : block016_data_flat070 = (CoefficientMerge.scale (73705078859904 : Int) atom1173Coded) := by
  rw [block016_data_flat070_step]
def block016_data_flat071 : CoefficientMerge.Poly := [(nat_lit 2557, Int.ofNat (nat_lit 18866969402112))]
theorem block016_data_flat071_step : block016_data_flat071 = (CoefficientMerge.scale (18866969402112 : Int) atom1174Coded) := by decide +kernel
theorem block016_data_flat071_original : block016_data_flat071 = (CoefficientMerge.scale (18866969402112 : Int) atom1174Coded) := by
  rw [block016_data_flat071_step]
def block016_data_flat072 : CoefficientMerge.Poly := [(nat_lit 2558, Int.ofNat (nat_lit 56352193854336))]
theorem block016_data_flat072_step : block016_data_flat072 = (CoefficientMerge.scale (56352193854336 : Int) atom1175Coded) := by decide +kernel
theorem block016_data_flat072_original : block016_data_flat072 = (CoefficientMerge.scale (56352193854336 : Int) atom1175Coded) := by
  rw [block016_data_flat072_step]
def block016_data_flat073 : CoefficientMerge.Poly := [(nat_lit 2557, Int.ofNat (nat_lit 18866969402112)), (nat_lit 2558, Int.ofNat (nat_lit 56352193854336))]
theorem block016_data_flat073_step : block016_data_flat073 = (CoefficientMerge.fastMerge block016_data_flat071 block016_data_flat072) := by decide +kernel
theorem block016_data_flat073_original : block016_data_flat073 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18866969402112 : Int) atom1174Coded) (CoefficientMerge.scale (56352193854336 : Int) atom1175Coded)) := by
  rw [block016_data_flat073_step, block016_data_flat071_original, block016_data_flat072_original]
def block016_data_flat074 : CoefficientMerge.Poly := [(nat_lit 2540, Int.ofNat (nat_lit 73705078859904)), (nat_lit 2557, Int.ofNat (nat_lit 18866969402112)), (nat_lit 2558, Int.ofNat (nat_lit 56352193854336))]
theorem block016_data_flat074_step : block016_data_flat074 = (CoefficientMerge.fastMerge block016_data_flat070 block016_data_flat073) := by decide +kernel
theorem block016_data_flat074_original : block016_data_flat074 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (73705078859904 : Int) atom1173Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18866969402112 : Int) atom1174Coded) (CoefficientMerge.scale (56352193854336 : Int) atom1175Coded))) := by
  rw [block016_data_flat074_step, block016_data_flat070_original, block016_data_flat073_original]
def block016_data_flat075 : CoefficientMerge.Poly := [(nat_lit 2538, Int.ofNat (nat_lit 69826861415808)), (nat_lit 2539, Int.ofNat (nat_lit 49709608836480)), (nat_lit 2540, Int.ofNat (nat_lit 73705078859904)), (nat_lit 2557, Int.ofNat (nat_lit 18866969402112)), (nat_lit 2558, Int.ofNat (nat_lit 56352193854336))]
theorem block016_data_flat075_step : block016_data_flat075 = (CoefficientMerge.fastMerge block016_data_flat069 block016_data_flat074) := by decide +kernel
theorem block016_data_flat075_original : block016_data_flat075 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69826861415808 : Int) atom1171Coded) (CoefficientMerge.scale (49709608836480 : Int) atom1172Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73705078859904 : Int) atom1173Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18866969402112 : Int) atom1174Coded) (CoefficientMerge.scale (56352193854336 : Int) atom1175Coded)))) := by
  rw [block016_data_flat075_step, block016_data_flat069_original, block016_data_flat074_original]
def block016_data_flat076 : CoefficientMerge.Poly := [(nat_lit 2518, Int.ofNat (nat_lit 52848874978560)), (nat_lit 2519, Int.ofNat (nat_lit 72684357715008)), (nat_lit 2535, Int.ofNat (nat_lit 26020396714752)), (nat_lit 2536, Int.ofNat (nat_lit 47998729798272)), (nat_lit 2537, Int.ofNat (nat_lit 69989670434304)), (nat_lit 2538, Int.ofNat (nat_lit 69826861415808)), (nat_lit 2539, Int.ofNat (nat_lit 49709608836480)), (nat_lit 2540, Int.ofNat (nat_lit 73705078859904)), (nat_lit 2557, Int.ofNat (nat_lit 18866969402112)), (nat_lit 2558, Int.ofNat (nat_lit 56352193854336))]
theorem block016_data_flat076_step : block016_data_flat076 = (CoefficientMerge.fastMerge block016_data_flat066 block016_data_flat075) := by decide +kernel
theorem block016_data_flat076_original : block016_data_flat076 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52848874978560 : Int) atom1166Coded) (CoefficientMerge.scale (72684357715008 : Int) atom1167Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26020396714752 : Int) atom1168Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47998729798272 : Int) atom1169Coded) (CoefficientMerge.scale (69989670434304 : Int) atom1170Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69826861415808 : Int) atom1171Coded) (CoefficientMerge.scale (49709608836480 : Int) atom1172Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73705078859904 : Int) atom1173Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18866969402112 : Int) atom1174Coded) (CoefficientMerge.scale (56352193854336 : Int) atom1175Coded))))) := by
  rw [block016_data_flat076_step, block016_data_flat066_original, block016_data_flat075_original]
def block016_data_flat077 : CoefficientMerge.Poly := [(nat_lit 2494, Int.ofNat (nat_lit 32778158869440)), (nat_lit 2495, Int.ofNat (nat_lit 45968048642304)), (nat_lit 2496, Int.ofNat (nat_lit 48255838538112)), (nat_lit 2497, Int.ofNat (nat_lit 48971706384960)), (nat_lit 2498, Int.ofNat (nat_lit 63039466358208)), (nat_lit 2513, Int.ofNat (nat_lit 20331751940352)), (nat_lit 2514, Int.ofNat (nat_lit 38507308418304)), (nat_lit 2515, Int.ofNat (nat_lit 35927230083840)), (nat_lit 2516, Int.ofNat (nat_lit 53554841282304)), (nat_lit 2517, Int.ofNat (nat_lit 57013026832512)), (nat_lit 2518, Int.ofNat (nat_lit 52848874978560)), (nat_lit 2519, Int.ofNat (nat_lit 72684357715008)), (nat_lit 2535, Int.ofNat (nat_lit 26020396714752)), (nat_lit 2536, Int.ofNat (nat_lit 47998729798272)), (nat_lit 2537, Int.ofNat (nat_lit 69989670434304)), (nat_lit 2538, Int.ofNat (nat_lit 69826861415808)), (nat_lit 2539, Int.ofNat (nat_lit 49709608836480)), (nat_lit 2540, Int.ofNat (nat_lit 73705078859904)), (nat_lit 2557, Int.ofNat (nat_lit 18866969402112)), (nat_lit 2558, Int.ofNat (nat_lit 56352193854336))]
theorem block016_data_flat077_step : block016_data_flat077 = (CoefficientMerge.fastMerge block016_data_flat057 block016_data_flat076) := by decide +kernel
theorem block016_data_flat077_original : block016_data_flat077 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32778158869440 : Int) atom1156Coded) (CoefficientMerge.scale (45968048642304 : Int) atom1157Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48255838538112 : Int) atom1158Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48971706384960 : Int) atom1159Coded) (CoefficientMerge.scale (63039466358208 : Int) atom1160Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20331751940352 : Int) atom1161Coded) (CoefficientMerge.scale (38507308418304 : Int) atom1162Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35927230083840 : Int) atom1163Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53554841282304 : Int) atom1164Coded) (CoefficientMerge.scale (57013026832512 : Int) atom1165Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52848874978560 : Int) atom1166Coded) (CoefficientMerge.scale (72684357715008 : Int) atom1167Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26020396714752 : Int) atom1168Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47998729798272 : Int) atom1169Coded) (CoefficientMerge.scale (69989670434304 : Int) atom1170Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69826861415808 : Int) atom1171Coded) (CoefficientMerge.scale (49709608836480 : Int) atom1172Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73705078859904 : Int) atom1173Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18866969402112 : Int) atom1174Coded) (CoefficientMerge.scale (56352193854336 : Int) atom1175Coded)))))) := by
  rw [block016_data_flat077_step, block016_data_flat057_original, block016_data_flat076_original]
def block016_data_flat078 : CoefficientMerge.Poly := [(nat_lit 2449, Int.ofNat (nat_lit 20238042645504)), (nat_lit 2450, Int.ofNat (nat_lit 20278634402304)), (nat_lit 2451, Int.ofNat (nat_lit 29238383522304)), (nat_lit 2452, Int.ofNat (nat_lit 26787755370240)), (nat_lit 2453, Int.ofNat (nat_lit 39115299746304)), (nat_lit 2454, Int.ofNat (nat_lit 39724813792512)), (nat_lit 2455, Int.ofNat (nat_lit 48335988821760)), (nat_lit 2456, Int.ofNat (nat_lit 56947163851008)), (nat_lit 2469, Int.ofNat (nat_lit 13458536612352)), (nat_lit 2470, Int.ofNat (nat_lit 25686756405504)), (nat_lit 2471, Int.ofNat (nat_lit 25145532981504)), (nat_lit 2472, Int.ofNat (nat_lit 29937883845504)), (nat_lit 2473, Int.ofNat (nat_lit 29509938218240)), (nat_lit 2474, Int.ofNat (nat_lit 40443829119104)), (nat_lit 2475, Int.ofNat (nat_lit 41715097976512)), (nat_lit 2476, Int.ofNat (nat_lit 49283350901760)), (nat_lit 2477, Int.ofNat (nat_lit 57682924975008)), (nat_lit 2491, Int.ofNat (nat_lit 16376678929152)), (nat_lit 2492, Int.ofNat (nat_lit 30291619682304)), (nat_lit 2493, Int.ofNat (nat_lit 34213038813504)), (nat_lit 2494, Int.ofNat (nat_lit 32778158869440)), (nat_lit 2495, Int.ofNat (nat_lit 45968048642304)), (nat_lit 2496, Int.ofNat (nat_lit 48255838538112)), (nat_lit 2497, Int.ofNat (nat_lit 48971706384960)), (nat_lit 2498, Int.ofNat (nat_lit 63039466358208)), (nat_lit 2513, Int.ofNat (nat_lit 20331751940352)), (nat_lit 2514, Int.ofNat (nat_lit 38507308418304)), (nat_lit 2515, Int.ofNat (nat_lit 35927230083840)), (nat_lit 2516, Int.ofNat (nat_lit 53554841282304)), (nat_lit 2517, Int.ofNat (nat_lit 57013026832512)), (nat_lit 2518, Int.ofNat (nat_lit 52848874978560)), (nat_lit 2519, Int.ofNat (nat_lit 72684357715008)), (nat_lit 2535, Int.ofNat (nat_lit 26020396714752)), (nat_lit 2536, Int.ofNat (nat_lit 47998729798272)), (nat_lit 2537, Int.ofNat (nat_lit 69989670434304)), (nat_lit 2538, Int.ofNat (nat_lit 69826861415808)), (nat_lit 2539, Int.ofNat (nat_lit 49709608836480)), (nat_lit 2540, Int.ofNat (nat_lit 73705078859904)), (nat_lit 2557, Int.ofNat (nat_lit 18866969402112)), (nat_lit 2558, Int.ofNat (nat_lit 56352193854336))]
theorem block016_data_flat078_step : block016_data_flat078 = (CoefficientMerge.fastMerge block016_data_flat038 block016_data_flat077) := by decide +kernel
theorem block016_data_flat078_original : block016_data_flat078 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20238042645504 : Int) atom1136Coded) (CoefficientMerge.scale (20278634402304 : Int) atom1137Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29238383522304 : Int) atom1138Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26787755370240 : Int) atom1139Coded) (CoefficientMerge.scale (39115299746304 : Int) atom1140Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39724813792512 : Int) atom1141Coded) (CoefficientMerge.scale (48335988821760 : Int) atom1142Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56947163851008 : Int) atom1143Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13458536612352 : Int) atom1144Coded) (CoefficientMerge.scale (25686756405504 : Int) atom1145Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25145532981504 : Int) atom1146Coded) (CoefficientMerge.scale (29937883845504 : Int) atom1147Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29509938218240 : Int) atom1148Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40443829119104 : Int) atom1149Coded) (CoefficientMerge.scale (41715097976512 : Int) atom1150Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49283350901760 : Int) atom1151Coded) (CoefficientMerge.scale (57682924975008 : Int) atom1152Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16376678929152 : Int) atom1153Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30291619682304 : Int) atom1154Coded) (CoefficientMerge.scale (34213038813504 : Int) atom1155Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32778158869440 : Int) atom1156Coded) (CoefficientMerge.scale (45968048642304 : Int) atom1157Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48255838538112 : Int) atom1158Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48971706384960 : Int) atom1159Coded) (CoefficientMerge.scale (63039466358208 : Int) atom1160Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20331751940352 : Int) atom1161Coded) (CoefficientMerge.scale (38507308418304 : Int) atom1162Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35927230083840 : Int) atom1163Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53554841282304 : Int) atom1164Coded) (CoefficientMerge.scale (57013026832512 : Int) atom1165Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52848874978560 : Int) atom1166Coded) (CoefficientMerge.scale (72684357715008 : Int) atom1167Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26020396714752 : Int) atom1168Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47998729798272 : Int) atom1169Coded) (CoefficientMerge.scale (69989670434304 : Int) atom1170Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69826861415808 : Int) atom1171Coded) (CoefficientMerge.scale (49709608836480 : Int) atom1172Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73705078859904 : Int) atom1173Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18866969402112 : Int) atom1174Coded) (CoefficientMerge.scale (56352193854336 : Int) atom1175Coded))))))) := by
  rw [block016_data_flat078_step, block016_data_flat038_original, block016_data_flat077_original]
def block016_data_flat079 : CoefficientMerge.Poly := [(nat_lit 2559, Int.ofNat (nat_lit 58898327545152))]
theorem block016_data_flat079_step : block016_data_flat079 = (CoefficientMerge.scale (58898327545152 : Int) atom1176Coded) := by decide +kernel
theorem block016_data_flat079_original : block016_data_flat079 = (CoefficientMerge.scale (58898327545152 : Int) atom1176Coded) := by
  rw [block016_data_flat079_step]
def block016_data_flat080 : CoefficientMerge.Poly := [(nat_lit 2560, Int.ofNat (nat_lit 43714896386304))]
theorem block016_data_flat080_step : block016_data_flat080 = (CoefficientMerge.scale (43714896386304 : Int) atom1177Coded) := by decide +kernel
theorem block016_data_flat080_original : block016_data_flat080 = (CoefficientMerge.scale (43714896386304 : Int) atom1177Coded) := by
  rw [block016_data_flat080_step]
def block016_data_flat081 : CoefficientMerge.Poly := [(nat_lit 2559, Int.ofNat (nat_lit 58898327545152)), (nat_lit 2560, Int.ofNat (nat_lit 43714896386304))]
theorem block016_data_flat081_step : block016_data_flat081 = (CoefficientMerge.fastMerge block016_data_flat079 block016_data_flat080) := by decide +kernel
theorem block016_data_flat081_original : block016_data_flat081 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (58898327545152 : Int) atom1176Coded) (CoefficientMerge.scale (43714896386304 : Int) atom1177Coded)) := by
  rw [block016_data_flat081_step, block016_data_flat079_original, block016_data_flat080_original]
def block016_data_flat082 : CoefficientMerge.Poly := [(nat_lit 2561, Int.ofNat (nat_lit 50328202741536))]
theorem block016_data_flat082_step : block016_data_flat082 = (CoefficientMerge.scale (50328202741536 : Int) atom1178Coded) := by decide +kernel
theorem block016_data_flat082_original : block016_data_flat082 = (CoefficientMerge.scale (50328202741536 : Int) atom1178Coded) := by
  rw [block016_data_flat082_step]
def block016_data_flat083 : CoefficientMerge.Poly := [(nat_lit 2579, Int.ofNat (nat_lit 40369274295552))]
theorem block016_data_flat083_step : block016_data_flat083 = (CoefficientMerge.scale (40369274295552 : Int) atom1179Coded) := by decide +kernel
theorem block016_data_flat083_original : block016_data_flat083 = (CoefficientMerge.scale (40369274295552 : Int) atom1179Coded) := by
  rw [block016_data_flat083_step]
def block016_data_flat084 : CoefficientMerge.Poly := [(nat_lit 2580, Int.ofNat (nat_lit 63935689449600))]
theorem block016_data_flat084_step : block016_data_flat084 = (CoefficientMerge.scale (63935689449600 : Int) atom1180Coded) := by decide +kernel
theorem block016_data_flat084_original : block016_data_flat084 = (CoefficientMerge.scale (63935689449600 : Int) atom1180Coded) := by
  rw [block016_data_flat084_step]
def block016_data_flat085 : CoefficientMerge.Poly := [(nat_lit 2579, Int.ofNat (nat_lit 40369274295552)), (nat_lit 2580, Int.ofNat (nat_lit 63935689449600))]
theorem block016_data_flat085_step : block016_data_flat085 = (CoefficientMerge.fastMerge block016_data_flat083 block016_data_flat084) := by decide +kernel
theorem block016_data_flat085_original : block016_data_flat085 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (40369274295552 : Int) atom1179Coded) (CoefficientMerge.scale (63935689449600 : Int) atom1180Coded)) := by
  rw [block016_data_flat085_step, block016_data_flat083_original, block016_data_flat084_original]
def block016_data_flat086 : CoefficientMerge.Poly := [(nat_lit 2561, Int.ofNat (nat_lit 50328202741536)), (nat_lit 2579, Int.ofNat (nat_lit 40369274295552)), (nat_lit 2580, Int.ofNat (nat_lit 63935689449600))]
theorem block016_data_flat086_step : block016_data_flat086 = (CoefficientMerge.fastMerge block016_data_flat082 block016_data_flat085) := by decide +kernel
theorem block016_data_flat086_original : block016_data_flat086 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (50328202741536 : Int) atom1178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40369274295552 : Int) atom1179Coded) (CoefficientMerge.scale (63935689449600 : Int) atom1180Coded))) := by
  rw [block016_data_flat086_step, block016_data_flat082_original, block016_data_flat085_original]
def block016_data_flat087 : CoefficientMerge.Poly := [(nat_lit 2559, Int.ofNat (nat_lit 58898327545152)), (nat_lit 2560, Int.ofNat (nat_lit 43714896386304)), (nat_lit 2561, Int.ofNat (nat_lit 50328202741536)), (nat_lit 2579, Int.ofNat (nat_lit 40369274295552)), (nat_lit 2580, Int.ofNat (nat_lit 63935689449600))]
theorem block016_data_flat087_step : block016_data_flat087 = (CoefficientMerge.fastMerge block016_data_flat081 block016_data_flat086) := by decide +kernel
theorem block016_data_flat087_original : block016_data_flat087 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58898327545152 : Int) atom1176Coded) (CoefficientMerge.scale (43714896386304 : Int) atom1177Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50328202741536 : Int) atom1178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40369274295552 : Int) atom1179Coded) (CoefficientMerge.scale (63935689449600 : Int) atom1180Coded)))) := by
  rw [block016_data_flat087_step, block016_data_flat081_original, block016_data_flat086_original]
def block016_data_flat088 : CoefficientMerge.Poly := [(nat_lit 2581, Int.ofNat (nat_lit 44823459653760))]
theorem block016_data_flat088_step : block016_data_flat088 = (CoefficientMerge.scale (44823459653760 : Int) atom1181Coded) := by decide +kernel
theorem block016_data_flat088_original : block016_data_flat088 = (CoefficientMerge.scale (44823459653760 : Int) atom1181Coded) := by
  rw [block016_data_flat088_step]
def block016_data_flat089 : CoefficientMerge.Poly := [(nat_lit 2582, Int.ofNat (nat_lit 50291511241152))]
theorem block016_data_flat089_step : block016_data_flat089 = (CoefficientMerge.scale (50291511241152 : Int) atom1182Coded) := by decide +kernel
theorem block016_data_flat089_original : block016_data_flat089 = (CoefficientMerge.scale (50291511241152 : Int) atom1182Coded) := by
  rw [block016_data_flat089_step]
def block016_data_flat090 : CoefficientMerge.Poly := [(nat_lit 2581, Int.ofNat (nat_lit 44823459653760)), (nat_lit 2582, Int.ofNat (nat_lit 50291511241152))]
theorem block016_data_flat090_step : block016_data_flat090 = (CoefficientMerge.fastMerge block016_data_flat088 block016_data_flat089) := by decide +kernel
theorem block016_data_flat090_original : block016_data_flat090 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (44823459653760 : Int) atom1181Coded) (CoefficientMerge.scale (50291511241152 : Int) atom1182Coded)) := by
  rw [block016_data_flat090_step, block016_data_flat088_original, block016_data_flat089_original]
def block016_data_flat091 : CoefficientMerge.Poly := [(nat_lit 2601, Int.ofNat (nat_lit 18599183925696))]
theorem block016_data_flat091_step : block016_data_flat091 = (CoefficientMerge.scale (18599183925696 : Int) atom1183Coded) := by decide +kernel
theorem block016_data_flat091_original : block016_data_flat091 = (CoefficientMerge.scale (18599183925696 : Int) atom1183Coded) := by
  rw [block016_data_flat091_step]
def block016_data_flat092 : CoefficientMerge.Poly := [(nat_lit 2602, Int.ofNat (nat_lit 23147791261632))]
theorem block016_data_flat092_step : block016_data_flat092 = (CoefficientMerge.scale (23147791261632 : Int) atom1184Coded) := by decide +kernel
theorem block016_data_flat092_original : block016_data_flat092 = (CoefficientMerge.scale (23147791261632 : Int) atom1184Coded) := by
  rw [block016_data_flat092_step]
def block016_data_flat093 : CoefficientMerge.Poly := [(nat_lit 2603, Int.ofNat (nat_lit 28126164973248))]
theorem block016_data_flat093_step : block016_data_flat093 = (CoefficientMerge.scale (28126164973248 : Int) atom1185Coded) := by decide +kernel
theorem block016_data_flat093_original : block016_data_flat093 = (CoefficientMerge.scale (28126164973248 : Int) atom1185Coded) := by
  rw [block016_data_flat093_step]
def block016_data_flat094 : CoefficientMerge.Poly := [(nat_lit 2602, Int.ofNat (nat_lit 23147791261632)), (nat_lit 2603, Int.ofNat (nat_lit 28126164973248))]
theorem block016_data_flat094_step : block016_data_flat094 = (CoefficientMerge.fastMerge block016_data_flat092 block016_data_flat093) := by decide +kernel
theorem block016_data_flat094_original : block016_data_flat094 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (23147791261632 : Int) atom1184Coded) (CoefficientMerge.scale (28126164973248 : Int) atom1185Coded)) := by
  rw [block016_data_flat094_step, block016_data_flat092_original, block016_data_flat093_original]
def block016_data_flat095 : CoefficientMerge.Poly := [(nat_lit 2601, Int.ofNat (nat_lit 18599183925696)), (nat_lit 2602, Int.ofNat (nat_lit 23147791261632)), (nat_lit 2603, Int.ofNat (nat_lit 28126164973248))]
theorem block016_data_flat095_step : block016_data_flat095 = (CoefficientMerge.fastMerge block016_data_flat091 block016_data_flat094) := by decide +kernel
theorem block016_data_flat095_original : block016_data_flat095 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (18599183925696 : Int) atom1183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23147791261632 : Int) atom1184Coded) (CoefficientMerge.scale (28126164973248 : Int) atom1185Coded))) := by
  rw [block016_data_flat095_step, block016_data_flat091_original, block016_data_flat094_original]
def block016_data_flat096 : CoefficientMerge.Poly := [(nat_lit 2581, Int.ofNat (nat_lit 44823459653760)), (nat_lit 2582, Int.ofNat (nat_lit 50291511241152)), (nat_lit 2601, Int.ofNat (nat_lit 18599183925696)), (nat_lit 2602, Int.ofNat (nat_lit 23147791261632)), (nat_lit 2603, Int.ofNat (nat_lit 28126164973248))]
theorem block016_data_flat096_step : block016_data_flat096 = (CoefficientMerge.fastMerge block016_data_flat090 block016_data_flat095) := by decide +kernel
theorem block016_data_flat096_original : block016_data_flat096 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44823459653760 : Int) atom1181Coded) (CoefficientMerge.scale (50291511241152 : Int) atom1182Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18599183925696 : Int) atom1183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23147791261632 : Int) atom1184Coded) (CoefficientMerge.scale (28126164973248 : Int) atom1185Coded)))) := by
  rw [block016_data_flat096_step, block016_data_flat090_original, block016_data_flat095_original]
def block016_data_flat097 : CoefficientMerge.Poly := [(nat_lit 2559, Int.ofNat (nat_lit 58898327545152)), (nat_lit 2560, Int.ofNat (nat_lit 43714896386304)), (nat_lit 2561, Int.ofNat (nat_lit 50328202741536)), (nat_lit 2579, Int.ofNat (nat_lit 40369274295552)), (nat_lit 2580, Int.ofNat (nat_lit 63935689449600)), (nat_lit 2581, Int.ofNat (nat_lit 44823459653760)), (nat_lit 2582, Int.ofNat (nat_lit 50291511241152)), (nat_lit 2601, Int.ofNat (nat_lit 18599183925696)), (nat_lit 2602, Int.ofNat (nat_lit 23147791261632)), (nat_lit 2603, Int.ofNat (nat_lit 28126164973248))]
theorem block016_data_flat097_step : block016_data_flat097 = (CoefficientMerge.fastMerge block016_data_flat087 block016_data_flat096) := by decide +kernel
theorem block016_data_flat097_original : block016_data_flat097 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58898327545152 : Int) atom1176Coded) (CoefficientMerge.scale (43714896386304 : Int) atom1177Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50328202741536 : Int) atom1178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40369274295552 : Int) atom1179Coded) (CoefficientMerge.scale (63935689449600 : Int) atom1180Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44823459653760 : Int) atom1181Coded) (CoefficientMerge.scale (50291511241152 : Int) atom1182Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18599183925696 : Int) atom1183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23147791261632 : Int) atom1184Coded) (CoefficientMerge.scale (28126164973248 : Int) atom1185Coded))))) := by
  rw [block016_data_flat097_step, block016_data_flat087_original, block016_data_flat096_original]
def block016_data_flat098 : CoefficientMerge.Poly := [(nat_lit 2645, Int.ofNat (nat_lit 3684923594208))]
theorem block016_data_flat098_step : block016_data_flat098 = (CoefficientMerge.scale (3684923594208 : Int) atom1186Coded) := by decide +kernel
theorem block016_data_flat098_original : block016_data_flat098 = (CoefficientMerge.scale (3684923594208 : Int) atom1186Coded) := by
  rw [block016_data_flat098_step]
def block016_data_flat099 : CoefficientMerge.Poly := [(nat_lit 2778, Int.ofNat (nat_lit 4122798220800))]
theorem block016_data_flat099_step : block016_data_flat099 = (CoefficientMerge.scale (4122798220800 : Int) atom1187Coded) := by decide +kernel
theorem block016_data_flat099_original : block016_data_flat099 = (CoefficientMerge.scale (4122798220800 : Int) atom1187Coded) := by
  rw [block016_data_flat099_step]
def block016_data_flat100 : CoefficientMerge.Poly := [(nat_lit 2645, Int.ofNat (nat_lit 3684923594208)), (nat_lit 2778, Int.ofNat (nat_lit 4122798220800))]
theorem block016_data_flat100_step : block016_data_flat100 = (CoefficientMerge.fastMerge block016_data_flat098 block016_data_flat099) := by decide +kernel
theorem block016_data_flat100_original : block016_data_flat100 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3684923594208 : Int) atom1186Coded) (CoefficientMerge.scale (4122798220800 : Int) atom1187Coded)) := by
  rw [block016_data_flat100_step, block016_data_flat098_original, block016_data_flat099_original]
def block016_data_flat101 : CoefficientMerge.Poly := [(nat_lit 2779, Int.ofNat (nat_lit 7834685443200))]
theorem block016_data_flat101_step : block016_data_flat101 = (CoefficientMerge.scale (7834685443200 : Int) atom1188Coded) := by decide +kernel
theorem block016_data_flat101_original : block016_data_flat101 = (CoefficientMerge.scale (7834685443200 : Int) atom1188Coded) := by
  rw [block016_data_flat101_step]
def block016_data_flat102 : CoefficientMerge.Poly := [(nat_lit 2780, Int.ofNat (nat_lit 3472038057600))]
theorem block016_data_flat102_step : block016_data_flat102 = (CoefficientMerge.scale (3472038057600 : Int) atom1189Coded) := by decide +kernel
theorem block016_data_flat102_original : block016_data_flat102 = (CoefficientMerge.scale (3472038057600 : Int) atom1189Coded) := by
  rw [block016_data_flat102_step]
def block016_data_flat103 : CoefficientMerge.Poly := [(nat_lit 2781, Int.ofNat (nat_lit 427179916800))]
theorem block016_data_flat103_step : block016_data_flat103 = (CoefficientMerge.scale (427179916800 : Int) atom1190Coded) := by decide +kernel
theorem block016_data_flat103_original : block016_data_flat103 = (CoefficientMerge.scale (427179916800 : Int) atom1190Coded) := by
  rw [block016_data_flat103_step]
def block016_data_flat104 : CoefficientMerge.Poly := [(nat_lit 2780, Int.ofNat (nat_lit 3472038057600)), (nat_lit 2781, Int.ofNat (nat_lit 427179916800))]
theorem block016_data_flat104_step : block016_data_flat104 = (CoefficientMerge.fastMerge block016_data_flat102 block016_data_flat103) := by decide +kernel
theorem block016_data_flat104_original : block016_data_flat104 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (3472038057600 : Int) atom1189Coded) (CoefficientMerge.scale (427179916800 : Int) atom1190Coded)) := by
  rw [block016_data_flat104_step, block016_data_flat102_original, block016_data_flat103_original]
def block016_data_flat105 : CoefficientMerge.Poly := [(nat_lit 2779, Int.ofNat (nat_lit 7834685443200)), (nat_lit 2780, Int.ofNat (nat_lit 3472038057600)), (nat_lit 2781, Int.ofNat (nat_lit 427179916800))]
theorem block016_data_flat105_step : block016_data_flat105 = (CoefficientMerge.fastMerge block016_data_flat101 block016_data_flat104) := by decide +kernel
theorem block016_data_flat105_original : block016_data_flat105 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7834685443200 : Int) atom1188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3472038057600 : Int) atom1189Coded) (CoefficientMerge.scale (427179916800 : Int) atom1190Coded))) := by
  rw [block016_data_flat105_step, block016_data_flat101_original, block016_data_flat104_original]
def block016_data_flat106 : CoefficientMerge.Poly := [(nat_lit 2645, Int.ofNat (nat_lit 3684923594208)), (nat_lit 2778, Int.ofNat (nat_lit 4122798220800)), (nat_lit 2779, Int.ofNat (nat_lit 7834685443200)), (nat_lit 2780, Int.ofNat (nat_lit 3472038057600)), (nat_lit 2781, Int.ofNat (nat_lit 427179916800))]
theorem block016_data_flat106_step : block016_data_flat106 = (CoefficientMerge.fastMerge block016_data_flat100 block016_data_flat105) := by decide +kernel
theorem block016_data_flat106_original : block016_data_flat106 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3684923594208 : Int) atom1186Coded) (CoefficientMerge.scale (4122798220800 : Int) atom1187Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7834685443200 : Int) atom1188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3472038057600 : Int) atom1189Coded) (CoefficientMerge.scale (427179916800 : Int) atom1190Coded)))) := by
  rw [block016_data_flat106_step, block016_data_flat100_original, block016_data_flat105_original]
def block016_data_flat107 : CoefficientMerge.Poly := [(nat_lit 2782, Int.ofNat (nat_lit 343096992000))]
theorem block016_data_flat107_step : block016_data_flat107 = (CoefficientMerge.scale (343096992000 : Int) atom1191Coded) := by decide +kernel
theorem block016_data_flat107_original : block016_data_flat107 = (CoefficientMerge.scale (343096992000 : Int) atom1191Coded) := by
  rw [block016_data_flat107_step]
def block016_data_flat108 : CoefficientMerge.Poly := [(nat_lit 2787, Int.ofNat (nat_lit 4497994368000))]
theorem block016_data_flat108_step : block016_data_flat108 = (CoefficientMerge.scale (4497994368000 : Int) atom1192Coded) := by decide +kernel
theorem block016_data_flat108_original : block016_data_flat108 = (CoefficientMerge.scale (4497994368000 : Int) atom1192Coded) := by
  rw [block016_data_flat108_step]
def block016_data_flat109 : CoefficientMerge.Poly := [(nat_lit 2782, Int.ofNat (nat_lit 343096992000)), (nat_lit 2787, Int.ofNat (nat_lit 4497994368000))]
theorem block016_data_flat109_step : block016_data_flat109 = (CoefficientMerge.fastMerge block016_data_flat107 block016_data_flat108) := by decide +kernel
theorem block016_data_flat109_original : block016_data_flat109 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (343096992000 : Int) atom1191Coded) (CoefficientMerge.scale (4497994368000 : Int) atom1192Coded)) := by
  rw [block016_data_flat109_step, block016_data_flat107_original, block016_data_flat108_original]
def block016_data_flat110 : CoefficientMerge.Poly := [(nat_lit 2800, Int.ofNat (nat_lit 6459401491200))]
theorem block016_data_flat110_step : block016_data_flat110 = (CoefficientMerge.scale (6459401491200 : Int) atom1193Coded) := by decide +kernel
theorem block016_data_flat110_original : block016_data_flat110 = (CoefficientMerge.scale (6459401491200 : Int) atom1193Coded) := by
  rw [block016_data_flat110_step]
def block016_data_flat111 : CoefficientMerge.Poly := [(nat_lit 2801, Int.ofNat (nat_lit 5397730329600))]
theorem block016_data_flat111_step : block016_data_flat111 = (CoefficientMerge.scale (5397730329600 : Int) atom1194Coded) := by decide +kernel
theorem block016_data_flat111_original : block016_data_flat111 = (CoefficientMerge.scale (5397730329600 : Int) atom1194Coded) := by
  rw [block016_data_flat111_step]
def block016_data_flat112 : CoefficientMerge.Poly := [(nat_lit 2805, Int.ofNat (nat_lit 427179916800))]
theorem block016_data_flat112_step : block016_data_flat112 = (CoefficientMerge.scale (427179916800 : Int) atom1195Coded) := by decide +kernel
theorem block016_data_flat112_original : block016_data_flat112 = (CoefficientMerge.scale (427179916800 : Int) atom1195Coded) := by
  rw [block016_data_flat112_step]
def block016_data_flat113 : CoefficientMerge.Poly := [(nat_lit 2801, Int.ofNat (nat_lit 5397730329600)), (nat_lit 2805, Int.ofNat (nat_lit 427179916800))]
theorem block016_data_flat113_step : block016_data_flat113 = (CoefficientMerge.fastMerge block016_data_flat111 block016_data_flat112) := by decide +kernel
theorem block016_data_flat113_original : block016_data_flat113 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5397730329600 : Int) atom1194Coded) (CoefficientMerge.scale (427179916800 : Int) atom1195Coded)) := by
  rw [block016_data_flat113_step, block016_data_flat111_original, block016_data_flat112_original]
def block016_data_flat114 : CoefficientMerge.Poly := [(nat_lit 2800, Int.ofNat (nat_lit 6459401491200)), (nat_lit 2801, Int.ofNat (nat_lit 5397730329600)), (nat_lit 2805, Int.ofNat (nat_lit 427179916800))]
theorem block016_data_flat114_step : block016_data_flat114 = (CoefficientMerge.fastMerge block016_data_flat110 block016_data_flat113) := by decide +kernel
theorem block016_data_flat114_original : block016_data_flat114 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (6459401491200 : Int) atom1193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5397730329600 : Int) atom1194Coded) (CoefficientMerge.scale (427179916800 : Int) atom1195Coded))) := by
  rw [block016_data_flat114_step, block016_data_flat110_original, block016_data_flat113_original]
def block016_data_flat115 : CoefficientMerge.Poly := [(nat_lit 2782, Int.ofNat (nat_lit 343096992000)), (nat_lit 2787, Int.ofNat (nat_lit 4497994368000)), (nat_lit 2800, Int.ofNat (nat_lit 6459401491200)), (nat_lit 2801, Int.ofNat (nat_lit 5397730329600)), (nat_lit 2805, Int.ofNat (nat_lit 427179916800))]
theorem block016_data_flat115_step : block016_data_flat115 = (CoefficientMerge.fastMerge block016_data_flat109 block016_data_flat114) := by decide +kernel
theorem block016_data_flat115_original : block016_data_flat115 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (343096992000 : Int) atom1191Coded) (CoefficientMerge.scale (4497994368000 : Int) atom1192Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6459401491200 : Int) atom1193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5397730329600 : Int) atom1194Coded) (CoefficientMerge.scale (427179916800 : Int) atom1195Coded)))) := by
  rw [block016_data_flat115_step, block016_data_flat109_original, block016_data_flat114_original]
def block016_data_flat116 : CoefficientMerge.Poly := [(nat_lit 2645, Int.ofNat (nat_lit 3684923594208)), (nat_lit 2778, Int.ofNat (nat_lit 4122798220800)), (nat_lit 2779, Int.ofNat (nat_lit 7834685443200)), (nat_lit 2780, Int.ofNat (nat_lit 3472038057600)), (nat_lit 2781, Int.ofNat (nat_lit 427179916800)), (nat_lit 2782, Int.ofNat (nat_lit 343096992000)), (nat_lit 2787, Int.ofNat (nat_lit 4497994368000)), (nat_lit 2800, Int.ofNat (nat_lit 6459401491200)), (nat_lit 2801, Int.ofNat (nat_lit 5397730329600)), (nat_lit 2805, Int.ofNat (nat_lit 427179916800))]
theorem block016_data_flat116_step : block016_data_flat116 = (CoefficientMerge.fastMerge block016_data_flat106 block016_data_flat115) := by decide +kernel
theorem block016_data_flat116_original : block016_data_flat116 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3684923594208 : Int) atom1186Coded) (CoefficientMerge.scale (4122798220800 : Int) atom1187Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7834685443200 : Int) atom1188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3472038057600 : Int) atom1189Coded) (CoefficientMerge.scale (427179916800 : Int) atom1190Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (343096992000 : Int) atom1191Coded) (CoefficientMerge.scale (4497994368000 : Int) atom1192Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6459401491200 : Int) atom1193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5397730329600 : Int) atom1194Coded) (CoefficientMerge.scale (427179916800 : Int) atom1195Coded))))) := by
  rw [block016_data_flat116_step, block016_data_flat106_original, block016_data_flat115_original]
def block016_data_flat117 : CoefficientMerge.Poly := [(nat_lit 2559, Int.ofNat (nat_lit 58898327545152)), (nat_lit 2560, Int.ofNat (nat_lit 43714896386304)), (nat_lit 2561, Int.ofNat (nat_lit 50328202741536)), (nat_lit 2579, Int.ofNat (nat_lit 40369274295552)), (nat_lit 2580, Int.ofNat (nat_lit 63935689449600)), (nat_lit 2581, Int.ofNat (nat_lit 44823459653760)), (nat_lit 2582, Int.ofNat (nat_lit 50291511241152)), (nat_lit 2601, Int.ofNat (nat_lit 18599183925696)), (nat_lit 2602, Int.ofNat (nat_lit 23147791261632)), (nat_lit 2603, Int.ofNat (nat_lit 28126164973248)), (nat_lit 2645, Int.ofNat (nat_lit 3684923594208)), (nat_lit 2778, Int.ofNat (nat_lit 4122798220800)), (nat_lit 2779, Int.ofNat (nat_lit 7834685443200)), (nat_lit 2780, Int.ofNat (nat_lit 3472038057600)), (nat_lit 2781, Int.ofNat (nat_lit 427179916800)), (nat_lit 2782, Int.ofNat (nat_lit 343096992000)), (nat_lit 2787, Int.ofNat (nat_lit 4497994368000)), (nat_lit 2800, Int.ofNat (nat_lit 6459401491200)), (nat_lit 2801, Int.ofNat (nat_lit 5397730329600)), (nat_lit 2805, Int.ofNat (nat_lit 427179916800))]
theorem block016_data_flat117_step : block016_data_flat117 = (CoefficientMerge.fastMerge block016_data_flat097 block016_data_flat116) := by decide +kernel
theorem block016_data_flat117_original : block016_data_flat117 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58898327545152 : Int) atom1176Coded) (CoefficientMerge.scale (43714896386304 : Int) atom1177Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50328202741536 : Int) atom1178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40369274295552 : Int) atom1179Coded) (CoefficientMerge.scale (63935689449600 : Int) atom1180Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44823459653760 : Int) atom1181Coded) (CoefficientMerge.scale (50291511241152 : Int) atom1182Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18599183925696 : Int) atom1183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23147791261632 : Int) atom1184Coded) (CoefficientMerge.scale (28126164973248 : Int) atom1185Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3684923594208 : Int) atom1186Coded) (CoefficientMerge.scale (4122798220800 : Int) atom1187Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7834685443200 : Int) atom1188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3472038057600 : Int) atom1189Coded) (CoefficientMerge.scale (427179916800 : Int) atom1190Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (343096992000 : Int) atom1191Coded) (CoefficientMerge.scale (4497994368000 : Int) atom1192Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6459401491200 : Int) atom1193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5397730329600 : Int) atom1194Coded) (CoefficientMerge.scale (427179916800 : Int) atom1195Coded)))))) := by
  rw [block016_data_flat117_step, block016_data_flat097_original, block016_data_flat116_original]
def block016_data_flat118 : CoefficientMerge.Poly := [(nat_lit 2806, Int.ofNat (nat_lit 854359833600))]
theorem block016_data_flat118_step : block016_data_flat118 = (CoefficientMerge.scale (854359833600 : Int) atom1196Coded) := by decide +kernel
theorem block016_data_flat118_original : block016_data_flat118 = (CoefficientMerge.scale (854359833600 : Int) atom1196Coded) := by
  rw [block016_data_flat118_step]
def block016_data_flat119 : CoefficientMerge.Poly := [(nat_lit 2807, Int.ofNat (nat_lit 1281539750400))]
theorem block016_data_flat119_step : block016_data_flat119 = (CoefficientMerge.scale (1281539750400 : Int) atom1197Coded) := by decide +kernel
theorem block016_data_flat119_original : block016_data_flat119 = (CoefficientMerge.scale (1281539750400 : Int) atom1197Coded) := by
  rw [block016_data_flat119_step]
def block016_data_flat120 : CoefficientMerge.Poly := [(nat_lit 2806, Int.ofNat (nat_lit 854359833600)), (nat_lit 2807, Int.ofNat (nat_lit 1281539750400))]
theorem block016_data_flat120_step : block016_data_flat120 = (CoefficientMerge.fastMerge block016_data_flat118 block016_data_flat119) := by decide +kernel
theorem block016_data_flat120_original : block016_data_flat120 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1196Coded) (CoefficientMerge.scale (1281539750400 : Int) atom1197Coded)) := by
  rw [block016_data_flat120_step, block016_data_flat118_original, block016_data_flat119_original]
def block016_data_flat121 : CoefficientMerge.Poly := [(nat_lit 2808, Int.ofNat (nat_lit 8045165325312))]
theorem block016_data_flat121_step : block016_data_flat121 = (CoefficientMerge.scale (8045165325312 : Int) atom1198Coded) := by decide +kernel
theorem block016_data_flat121_original : block016_data_flat121 = (CoefficientMerge.scale (8045165325312 : Int) atom1198Coded) := by
  rw [block016_data_flat121_step]
def block016_data_flat122 : CoefficientMerge.Poly := [(nat_lit 2811, Int.ofNat (nat_lit 5465873347200))]
theorem block016_data_flat122_step : block016_data_flat122 = (CoefficientMerge.scale (5465873347200 : Int) atom1199Coded) := by decide +kernel
theorem block016_data_flat122_original : block016_data_flat122 = (CoefficientMerge.scale (5465873347200 : Int) atom1199Coded) := by
  rw [block016_data_flat122_step]
def block016_data_flat123 : CoefficientMerge.Poly := [(nat_lit 2812, Int.ofNat (nat_lit 10744058142720))]
theorem block016_data_flat123_step : block016_data_flat123 = (CoefficientMerge.scale (10744058142720 : Int) atom1200Coded) := by decide +kernel
theorem block016_data_flat123_original : block016_data_flat123 = (CoefficientMerge.scale (10744058142720 : Int) atom1200Coded) := by
  rw [block016_data_flat123_step]
def block016_data_flat124 : CoefficientMerge.Poly := [(nat_lit 2811, Int.ofNat (nat_lit 5465873347200)), (nat_lit 2812, Int.ofNat (nat_lit 10744058142720))]
theorem block016_data_flat124_step : block016_data_flat124 = (CoefficientMerge.fastMerge block016_data_flat122 block016_data_flat123) := by decide +kernel
theorem block016_data_flat124_original : block016_data_flat124 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (5465873347200 : Int) atom1199Coded) (CoefficientMerge.scale (10744058142720 : Int) atom1200Coded)) := by
  rw [block016_data_flat124_step, block016_data_flat122_original, block016_data_flat123_original]
def block016_data_flat125 : CoefficientMerge.Poly := [(nat_lit 2808, Int.ofNat (nat_lit 8045165325312)), (nat_lit 2811, Int.ofNat (nat_lit 5465873347200)), (nat_lit 2812, Int.ofNat (nat_lit 10744058142720))]
theorem block016_data_flat125_step : block016_data_flat125 = (CoefficientMerge.fastMerge block016_data_flat121 block016_data_flat124) := by decide +kernel
theorem block016_data_flat125_original : block016_data_flat125 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (8045165325312 : Int) atom1198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5465873347200 : Int) atom1199Coded) (CoefficientMerge.scale (10744058142720 : Int) atom1200Coded))) := by
  rw [block016_data_flat125_step, block016_data_flat121_original, block016_data_flat124_original]
def block016_data_flat126 : CoefficientMerge.Poly := [(nat_lit 2806, Int.ofNat (nat_lit 854359833600)), (nat_lit 2807, Int.ofNat (nat_lit 1281539750400)), (nat_lit 2808, Int.ofNat (nat_lit 8045165325312)), (nat_lit 2811, Int.ofNat (nat_lit 5465873347200)), (nat_lit 2812, Int.ofNat (nat_lit 10744058142720))]
theorem block016_data_flat126_step : block016_data_flat126 = (CoefficientMerge.fastMerge block016_data_flat120 block016_data_flat125) := by decide +kernel
theorem block016_data_flat126_original : block016_data_flat126 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1196Coded) (CoefficientMerge.scale (1281539750400 : Int) atom1197Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8045165325312 : Int) atom1198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5465873347200 : Int) atom1199Coded) (CoefficientMerge.scale (10744058142720 : Int) atom1200Coded)))) := by
  rw [block016_data_flat126_step, block016_data_flat120_original, block016_data_flat125_original]
def block016_data_flat127 : CoefficientMerge.Poly := [(nat_lit 2813, Int.ofNat (nat_lit 16910574206400))]
theorem block016_data_flat127_step : block016_data_flat127 = (CoefficientMerge.scale (16910574206400 : Int) atom1201Coded) := by decide +kernel
theorem block016_data_flat127_original : block016_data_flat127 = (CoefficientMerge.scale (16910574206400 : Int) atom1201Coded) := by
  rw [block016_data_flat127_step]
def block016_data_flat128 : CoefficientMerge.Poly := [(nat_lit 2822, Int.ofNat (nat_lit 2523934022400))]
theorem block016_data_flat128_step : block016_data_flat128 = (CoefficientMerge.scale (2523934022400 : Int) atom1202Coded) := by decide +kernel
theorem block016_data_flat128_original : block016_data_flat128 = (CoefficientMerge.scale (2523934022400 : Int) atom1202Coded) := by
  rw [block016_data_flat128_step]
def block016_data_flat129 : CoefficientMerge.Poly := [(nat_lit 2813, Int.ofNat (nat_lit 16910574206400)), (nat_lit 2822, Int.ofNat (nat_lit 2523934022400))]
theorem block016_data_flat129_step : block016_data_flat129 = (CoefficientMerge.fastMerge block016_data_flat127 block016_data_flat128) := by decide +kernel
theorem block016_data_flat129_original : block016_data_flat129 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (16910574206400 : Int) atom1201Coded) (CoefficientMerge.scale (2523934022400 : Int) atom1202Coded)) := by
  rw [block016_data_flat129_step, block016_data_flat127_original, block016_data_flat128_original]
def block016_data_flat130 : CoefficientMerge.Poly := [(nat_lit 2826, Int.ofNat (nat_lit 259014067200))]
theorem block016_data_flat130_step : block016_data_flat130 = (CoefficientMerge.scale (259014067200 : Int) atom1203Coded) := by decide +kernel
theorem block016_data_flat130_original : block016_data_flat130 = (CoefficientMerge.scale (259014067200 : Int) atom1203Coded) := by
  rw [block016_data_flat130_step]
def block016_data_flat131 : CoefficientMerge.Poly := [(nat_lit 2827, Int.ofNat (nat_lit 945208051200))]
theorem block016_data_flat131_step : block016_data_flat131 = (CoefficientMerge.scale (945208051200 : Int) atom1204Coded) := by decide +kernel
theorem block016_data_flat131_original : block016_data_flat131 = (CoefficientMerge.scale (945208051200 : Int) atom1204Coded) := by
  rw [block016_data_flat131_step]
def block016_data_flat132 : CoefficientMerge.Poly := [(nat_lit 2828, Int.ofNat (nat_lit 1631402035200))]
theorem block016_data_flat132_step : block016_data_flat132 = (CoefficientMerge.scale (1631402035200 : Int) atom1205Coded) := by decide +kernel
theorem block016_data_flat132_original : block016_data_flat132 = (CoefficientMerge.scale (1631402035200 : Int) atom1205Coded) := by
  rw [block016_data_flat132_step]
def block016_data_flat133 : CoefficientMerge.Poly := [(nat_lit 2827, Int.ofNat (nat_lit 945208051200)), (nat_lit 2828, Int.ofNat (nat_lit 1631402035200))]
theorem block016_data_flat133_step : block016_data_flat133 = (CoefficientMerge.fastMerge block016_data_flat131 block016_data_flat132) := by decide +kernel
theorem block016_data_flat133_original : block016_data_flat133 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (945208051200 : Int) atom1204Coded) (CoefficientMerge.scale (1631402035200 : Int) atom1205Coded)) := by
  rw [block016_data_flat133_step, block016_data_flat131_original, block016_data_flat132_original]
def block016_data_flat134 : CoefficientMerge.Poly := [(nat_lit 2826, Int.ofNat (nat_lit 259014067200)), (nat_lit 2827, Int.ofNat (nat_lit 945208051200)), (nat_lit 2828, Int.ofNat (nat_lit 1631402035200))]
theorem block016_data_flat134_step : block016_data_flat134 = (CoefficientMerge.fastMerge block016_data_flat130 block016_data_flat133) := by decide +kernel
theorem block016_data_flat134_original : block016_data_flat134 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (259014067200 : Int) atom1203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (945208051200 : Int) atom1204Coded) (CoefficientMerge.scale (1631402035200 : Int) atom1205Coded))) := by
  rw [block016_data_flat134_step, block016_data_flat130_original, block016_data_flat133_original]
def block016_data_flat135 : CoefficientMerge.Poly := [(nat_lit 2813, Int.ofNat (nat_lit 16910574206400)), (nat_lit 2822, Int.ofNat (nat_lit 2523934022400)), (nat_lit 2826, Int.ofNat (nat_lit 259014067200)), (nat_lit 2827, Int.ofNat (nat_lit 945208051200)), (nat_lit 2828, Int.ofNat (nat_lit 1631402035200))]
theorem block016_data_flat135_step : block016_data_flat135 = (CoefficientMerge.fastMerge block016_data_flat129 block016_data_flat134) := by decide +kernel
theorem block016_data_flat135_original : block016_data_flat135 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16910574206400 : Int) atom1201Coded) (CoefficientMerge.scale (2523934022400 : Int) atom1202Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (259014067200 : Int) atom1203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (945208051200 : Int) atom1204Coded) (CoefficientMerge.scale (1631402035200 : Int) atom1205Coded)))) := by
  rw [block016_data_flat135_step, block016_data_flat129_original, block016_data_flat134_original]
def block016_data_flat136 : CoefficientMerge.Poly := [(nat_lit 2806, Int.ofNat (nat_lit 854359833600)), (nat_lit 2807, Int.ofNat (nat_lit 1281539750400)), (nat_lit 2808, Int.ofNat (nat_lit 8045165325312)), (nat_lit 2811, Int.ofNat (nat_lit 5465873347200)), (nat_lit 2812, Int.ofNat (nat_lit 10744058142720)), (nat_lit 2813, Int.ofNat (nat_lit 16910574206400)), (nat_lit 2822, Int.ofNat (nat_lit 2523934022400)), (nat_lit 2826, Int.ofNat (nat_lit 259014067200)), (nat_lit 2827, Int.ofNat (nat_lit 945208051200)), (nat_lit 2828, Int.ofNat (nat_lit 1631402035200))]
theorem block016_data_flat136_step : block016_data_flat136 = (CoefficientMerge.fastMerge block016_data_flat126 block016_data_flat135) := by decide +kernel
theorem block016_data_flat136_original : block016_data_flat136 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1196Coded) (CoefficientMerge.scale (1281539750400 : Int) atom1197Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8045165325312 : Int) atom1198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5465873347200 : Int) atom1199Coded) (CoefficientMerge.scale (10744058142720 : Int) atom1200Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16910574206400 : Int) atom1201Coded) (CoefficientMerge.scale (2523934022400 : Int) atom1202Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (259014067200 : Int) atom1203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (945208051200 : Int) atom1204Coded) (CoefficientMerge.scale (1631402035200 : Int) atom1205Coded))))) := by
  rw [block016_data_flat136_step, block016_data_flat126_original, block016_data_flat135_original]
def block016_data_flat137 : CoefficientMerge.Poly := [(nat_lit 2829, Int.ofNat (nat_lit 9159807182400))]
theorem block016_data_flat137_step : block016_data_flat137 = (CoefficientMerge.scale (9159807182400 : Int) atom1206Coded) := by decide +kernel
theorem block016_data_flat137_original : block016_data_flat137 = (CoefficientMerge.scale (9159807182400 : Int) atom1206Coded) := by
  rw [block016_data_flat137_step]
def block016_data_flat138 : CoefficientMerge.Poly := [(nat_lit 2830, Int.ofNat (nat_lit 3879597682800))]
theorem block016_data_flat138_step : block016_data_flat138 = (CoefficientMerge.scale (3879597682800 : Int) atom1207Coded) := by decide +kernel
theorem block016_data_flat138_original : block016_data_flat138 = (CoefficientMerge.scale (3879597682800 : Int) atom1207Coded) := by
  rw [block016_data_flat138_step]
def block016_data_flat139 : CoefficientMerge.Poly := [(nat_lit 2829, Int.ofNat (nat_lit 9159807182400)), (nat_lit 2830, Int.ofNat (nat_lit 3879597682800))]
theorem block016_data_flat139_step : block016_data_flat139 = (CoefficientMerge.fastMerge block016_data_flat137 block016_data_flat138) := by decide +kernel
theorem block016_data_flat139_original : block016_data_flat139 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (9159807182400 : Int) atom1206Coded) (CoefficientMerge.scale (3879597682800 : Int) atom1207Coded)) := by
  rw [block016_data_flat139_step, block016_data_flat137_original, block016_data_flat138_original]
def block016_data_flat140 : CoefficientMerge.Poly := [(nat_lit 2831, Int.ofNat (nat_lit 7715012760000))]
theorem block016_data_flat140_step : block016_data_flat140 = (CoefficientMerge.scale (7715012760000 : Int) atom1208Coded) := by decide +kernel
theorem block016_data_flat140_original : block016_data_flat140 = (CoefficientMerge.scale (7715012760000 : Int) atom1208Coded) := by
  rw [block016_data_flat140_step]
def block016_data_flat141 : CoefficientMerge.Poly := [(nat_lit 2832, Int.ofNat (nat_lit 14815693494000))]
theorem block016_data_flat141_step : block016_data_flat141 = (CoefficientMerge.scale (14815693494000 : Int) atom1209Coded) := by decide +kernel
theorem block016_data_flat141_original : block016_data_flat141 = (CoefficientMerge.scale (14815693494000 : Int) atom1209Coded) := by
  rw [block016_data_flat141_step]
def block016_data_flat142 : CoefficientMerge.Poly := [(nat_lit 2833, Int.ofNat (nat_lit 23440111203600))]
theorem block016_data_flat142_step : block016_data_flat142 = (CoefficientMerge.scale (23440111203600 : Int) atom1210Coded) := by decide +kernel
theorem block016_data_flat142_original : block016_data_flat142 = (CoefficientMerge.scale (23440111203600 : Int) atom1210Coded) := by
  rw [block016_data_flat142_step]
def block016_data_flat143 : CoefficientMerge.Poly := [(nat_lit 2832, Int.ofNat (nat_lit 14815693494000)), (nat_lit 2833, Int.ofNat (nat_lit 23440111203600))]
theorem block016_data_flat143_step : block016_data_flat143 = (CoefficientMerge.fastMerge block016_data_flat141 block016_data_flat142) := by decide +kernel
theorem block016_data_flat143_original : block016_data_flat143 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (14815693494000 : Int) atom1209Coded) (CoefficientMerge.scale (23440111203600 : Int) atom1210Coded)) := by
  rw [block016_data_flat143_step, block016_data_flat141_original, block016_data_flat142_original]
def block016_data_flat144 : CoefficientMerge.Poly := [(nat_lit 2831, Int.ofNat (nat_lit 7715012760000)), (nat_lit 2832, Int.ofNat (nat_lit 14815693494000)), (nat_lit 2833, Int.ofNat (nat_lit 23440111203600))]
theorem block016_data_flat144_step : block016_data_flat144 = (CoefficientMerge.fastMerge block016_data_flat140 block016_data_flat143) := by decide +kernel
theorem block016_data_flat144_original : block016_data_flat144 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715012760000 : Int) atom1208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14815693494000 : Int) atom1209Coded) (CoefficientMerge.scale (23440111203600 : Int) atom1210Coded))) := by
  rw [block016_data_flat144_step, block016_data_flat140_original, block016_data_flat143_original]
def block016_data_flat145 : CoefficientMerge.Poly := [(nat_lit 2829, Int.ofNat (nat_lit 9159807182400)), (nat_lit 2830, Int.ofNat (nat_lit 3879597682800)), (nat_lit 2831, Int.ofNat (nat_lit 7715012760000)), (nat_lit 2832, Int.ofNat (nat_lit 14815693494000)), (nat_lit 2833, Int.ofNat (nat_lit 23440111203600))]
theorem block016_data_flat145_step : block016_data_flat145 = (CoefficientMerge.fastMerge block016_data_flat139 block016_data_flat144) := by decide +kernel
theorem block016_data_flat145_original : block016_data_flat145 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9159807182400 : Int) atom1206Coded) (CoefficientMerge.scale (3879597682800 : Int) atom1207Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715012760000 : Int) atom1208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14815693494000 : Int) atom1209Coded) (CoefficientMerge.scale (23440111203600 : Int) atom1210Coded)))) := by
  rw [block016_data_flat145_step, block016_data_flat139_original, block016_data_flat144_original]
def block016_data_flat146 : CoefficientMerge.Poly := [(nat_lit 2834, Int.ofNat (nat_lit 32845738161600))]
theorem block016_data_flat146_step : block016_data_flat146 = (CoefficientMerge.scale (32845738161600 : Int) atom1211Coded) := by decide +kernel
theorem block016_data_flat146_original : block016_data_flat146 = (CoefficientMerge.scale (32845738161600 : Int) atom1211Coded) := by
  rw [block016_data_flat146_step]
def block016_data_flat147 : CoefficientMerge.Poly := [(nat_lit 2844, Int.ofNat (nat_lit 1061671161600))]
theorem block016_data_flat147_step : block016_data_flat147 = (CoefficientMerge.scale (1061671161600 : Int) atom1212Coded) := by decide +kernel
theorem block016_data_flat147_original : block016_data_flat147 = (CoefficientMerge.scale (1061671161600 : Int) atom1212Coded) := by
  rw [block016_data_flat147_step]
def block016_data_flat148 : CoefficientMerge.Poly := [(nat_lit 2834, Int.ofNat (nat_lit 32845738161600)), (nat_lit 2844, Int.ofNat (nat_lit 1061671161600))]
theorem block016_data_flat148_step : block016_data_flat148 = (CoefficientMerge.fastMerge block016_data_flat146 block016_data_flat147) := by decide +kernel
theorem block016_data_flat148_original : block016_data_flat148 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (32845738161600 : Int) atom1211Coded) (CoefficientMerge.scale (1061671161600 : Int) atom1212Coded)) := by
  rw [block016_data_flat148_step, block016_data_flat146_original, block016_data_flat147_original]
def block016_data_flat149 : CoefficientMerge.Poly := [(nat_lit 2845, Int.ofNat (nat_lit 680402016000))]
theorem block016_data_flat149_step : block016_data_flat149 = (CoefficientMerge.scale (680402016000 : Int) atom1213Coded) := by decide +kernel
theorem block016_data_flat149_original : block016_data_flat149 = (CoefficientMerge.scale (680402016000 : Int) atom1213Coded) := by
  rw [block016_data_flat149_step]
def block016_data_flat150 : CoefficientMerge.Poly := [(nat_lit 2846, Int.ofNat (nat_lit 512236166400))]
theorem block016_data_flat150_step : block016_data_flat150 = (CoefficientMerge.scale (512236166400 : Int) atom1214Coded) := by decide +kernel
theorem block016_data_flat150_original : block016_data_flat150 = (CoefficientMerge.scale (512236166400 : Int) atom1214Coded) := by
  rw [block016_data_flat150_step]
def block016_data_flat151 : CoefficientMerge.Poly := [(nat_lit 2847, Int.ofNat (nat_lit 1289278368000))]
theorem block016_data_flat151_step : block016_data_flat151 = (CoefficientMerge.scale (1289278368000 : Int) atom1215Coded) := by decide +kernel
theorem block016_data_flat151_original : block016_data_flat151 = (CoefficientMerge.scale (1289278368000 : Int) atom1215Coded) := by
  rw [block016_data_flat151_step]
def block016_data_flat152 : CoefficientMerge.Poly := [(nat_lit 2846, Int.ofNat (nat_lit 512236166400)), (nat_lit 2847, Int.ofNat (nat_lit 1289278368000))]
theorem block016_data_flat152_step : block016_data_flat152 = (CoefficientMerge.fastMerge block016_data_flat150 block016_data_flat151) := by decide +kernel
theorem block016_data_flat152_original : block016_data_flat152 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (512236166400 : Int) atom1214Coded) (CoefficientMerge.scale (1289278368000 : Int) atom1215Coded)) := by
  rw [block016_data_flat152_step, block016_data_flat150_original, block016_data_flat151_original]
def block016_data_flat153 : CoefficientMerge.Poly := [(nat_lit 2845, Int.ofNat (nat_lit 680402016000)), (nat_lit 2846, Int.ofNat (nat_lit 512236166400)), (nat_lit 2847, Int.ofNat (nat_lit 1289278368000))]
theorem block016_data_flat153_step : block016_data_flat153 = (CoefficientMerge.fastMerge block016_data_flat149 block016_data_flat152) := by decide +kernel
theorem block016_data_flat153_original : block016_data_flat153 = (CoefficientMerge.fastMerge (CoefficientMerge.scale (680402016000 : Int) atom1213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (512236166400 : Int) atom1214Coded) (CoefficientMerge.scale (1289278368000 : Int) atom1215Coded))) := by
  rw [block016_data_flat153_step, block016_data_flat149_original, block016_data_flat152_original]
def block016_data_flat154 : CoefficientMerge.Poly := [(nat_lit 2834, Int.ofNat (nat_lit 32845738161600)), (nat_lit 2844, Int.ofNat (nat_lit 1061671161600)), (nat_lit 2845, Int.ofNat (nat_lit 680402016000)), (nat_lit 2846, Int.ofNat (nat_lit 512236166400)), (nat_lit 2847, Int.ofNat (nat_lit 1289278368000))]
theorem block016_data_flat154_step : block016_data_flat154 = (CoefficientMerge.fastMerge block016_data_flat148 block016_data_flat153) := by decide +kernel
theorem block016_data_flat154_original : block016_data_flat154 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32845738161600 : Int) atom1211Coded) (CoefficientMerge.scale (1061671161600 : Int) atom1212Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (680402016000 : Int) atom1213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (512236166400 : Int) atom1214Coded) (CoefficientMerge.scale (1289278368000 : Int) atom1215Coded)))) := by
  rw [block016_data_flat154_step, block016_data_flat148_original, block016_data_flat153_original]
def block016_data_flat155 : CoefficientMerge.Poly := [(nat_lit 2829, Int.ofNat (nat_lit 9159807182400)), (nat_lit 2830, Int.ofNat (nat_lit 3879597682800)), (nat_lit 2831, Int.ofNat (nat_lit 7715012760000)), (nat_lit 2832, Int.ofNat (nat_lit 14815693494000)), (nat_lit 2833, Int.ofNat (nat_lit 23440111203600)), (nat_lit 2834, Int.ofNat (nat_lit 32845738161600)), (nat_lit 2844, Int.ofNat (nat_lit 1061671161600)), (nat_lit 2845, Int.ofNat (nat_lit 680402016000)), (nat_lit 2846, Int.ofNat (nat_lit 512236166400)), (nat_lit 2847, Int.ofNat (nat_lit 1289278368000))]
theorem block016_data_flat155_step : block016_data_flat155 = (CoefficientMerge.fastMerge block016_data_flat145 block016_data_flat154) := by decide +kernel
theorem block016_data_flat155_original : block016_data_flat155 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9159807182400 : Int) atom1206Coded) (CoefficientMerge.scale (3879597682800 : Int) atom1207Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715012760000 : Int) atom1208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14815693494000 : Int) atom1209Coded) (CoefficientMerge.scale (23440111203600 : Int) atom1210Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32845738161600 : Int) atom1211Coded) (CoefficientMerge.scale (1061671161600 : Int) atom1212Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (680402016000 : Int) atom1213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (512236166400 : Int) atom1214Coded) (CoefficientMerge.scale (1289278368000 : Int) atom1215Coded))))) := by
  rw [block016_data_flat155_step, block016_data_flat145_original, block016_data_flat154_original]
def block016_data_flat156 : CoefficientMerge.Poly := [(nat_lit 2806, Int.ofNat (nat_lit 854359833600)), (nat_lit 2807, Int.ofNat (nat_lit 1281539750400)), (nat_lit 2808, Int.ofNat (nat_lit 8045165325312)), (nat_lit 2811, Int.ofNat (nat_lit 5465873347200)), (nat_lit 2812, Int.ofNat (nat_lit 10744058142720)), (nat_lit 2813, Int.ofNat (nat_lit 16910574206400)), (nat_lit 2822, Int.ofNat (nat_lit 2523934022400)), (nat_lit 2826, Int.ofNat (nat_lit 259014067200)), (nat_lit 2827, Int.ofNat (nat_lit 945208051200)), (nat_lit 2828, Int.ofNat (nat_lit 1631402035200)), (nat_lit 2829, Int.ofNat (nat_lit 9159807182400)), (nat_lit 2830, Int.ofNat (nat_lit 3879597682800)), (nat_lit 2831, Int.ofNat (nat_lit 7715012760000)), (nat_lit 2832, Int.ofNat (nat_lit 14815693494000)), (nat_lit 2833, Int.ofNat (nat_lit 23440111203600)), (nat_lit 2834, Int.ofNat (nat_lit 32845738161600)), (nat_lit 2844, Int.ofNat (nat_lit 1061671161600)), (nat_lit 2845, Int.ofNat (nat_lit 680402016000)), (nat_lit 2846, Int.ofNat (nat_lit 512236166400)), (nat_lit 2847, Int.ofNat (nat_lit 1289278368000))]
theorem block016_data_flat156_step : block016_data_flat156 = (CoefficientMerge.fastMerge block016_data_flat136 block016_data_flat155) := by decide +kernel
theorem block016_data_flat156_original : block016_data_flat156 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1196Coded) (CoefficientMerge.scale (1281539750400 : Int) atom1197Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8045165325312 : Int) atom1198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5465873347200 : Int) atom1199Coded) (CoefficientMerge.scale (10744058142720 : Int) atom1200Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16910574206400 : Int) atom1201Coded) (CoefficientMerge.scale (2523934022400 : Int) atom1202Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (259014067200 : Int) atom1203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (945208051200 : Int) atom1204Coded) (CoefficientMerge.scale (1631402035200 : Int) atom1205Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9159807182400 : Int) atom1206Coded) (CoefficientMerge.scale (3879597682800 : Int) atom1207Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715012760000 : Int) atom1208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14815693494000 : Int) atom1209Coded) (CoefficientMerge.scale (23440111203600 : Int) atom1210Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32845738161600 : Int) atom1211Coded) (CoefficientMerge.scale (1061671161600 : Int) atom1212Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (680402016000 : Int) atom1213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (512236166400 : Int) atom1214Coded) (CoefficientMerge.scale (1289278368000 : Int) atom1215Coded)))))) := by
  rw [block016_data_flat156_step, block016_data_flat136_original, block016_data_flat155_original]
def block016_data_flat157 : CoefficientMerge.Poly := [(nat_lit 2559, Int.ofNat (nat_lit 58898327545152)), (nat_lit 2560, Int.ofNat (nat_lit 43714896386304)), (nat_lit 2561, Int.ofNat (nat_lit 50328202741536)), (nat_lit 2579, Int.ofNat (nat_lit 40369274295552)), (nat_lit 2580, Int.ofNat (nat_lit 63935689449600)), (nat_lit 2581, Int.ofNat (nat_lit 44823459653760)), (nat_lit 2582, Int.ofNat (nat_lit 50291511241152)), (nat_lit 2601, Int.ofNat (nat_lit 18599183925696)), (nat_lit 2602, Int.ofNat (nat_lit 23147791261632)), (nat_lit 2603, Int.ofNat (nat_lit 28126164973248)), (nat_lit 2645, Int.ofNat (nat_lit 3684923594208)), (nat_lit 2778, Int.ofNat (nat_lit 4122798220800)), (nat_lit 2779, Int.ofNat (nat_lit 7834685443200)), (nat_lit 2780, Int.ofNat (nat_lit 3472038057600)), (nat_lit 2781, Int.ofNat (nat_lit 427179916800)), (nat_lit 2782, Int.ofNat (nat_lit 343096992000)), (nat_lit 2787, Int.ofNat (nat_lit 4497994368000)), (nat_lit 2800, Int.ofNat (nat_lit 6459401491200)), (nat_lit 2801, Int.ofNat (nat_lit 5397730329600)), (nat_lit 2805, Int.ofNat (nat_lit 427179916800)), (nat_lit 2806, Int.ofNat (nat_lit 854359833600)), (nat_lit 2807, Int.ofNat (nat_lit 1281539750400)), (nat_lit 2808, Int.ofNat (nat_lit 8045165325312)), (nat_lit 2811, Int.ofNat (nat_lit 5465873347200)), (nat_lit 2812, Int.ofNat (nat_lit 10744058142720)), (nat_lit 2813, Int.ofNat (nat_lit 16910574206400)), (nat_lit 2822, Int.ofNat (nat_lit 2523934022400)), (nat_lit 2826, Int.ofNat (nat_lit 259014067200)), (nat_lit 2827, Int.ofNat (nat_lit 945208051200)), (nat_lit 2828, Int.ofNat (nat_lit 1631402035200)), (nat_lit 2829, Int.ofNat (nat_lit 9159807182400)), (nat_lit 2830, Int.ofNat (nat_lit 3879597682800)), (nat_lit 2831, Int.ofNat (nat_lit 7715012760000)), (nat_lit 2832, Int.ofNat (nat_lit 14815693494000)), (nat_lit 2833, Int.ofNat (nat_lit 23440111203600)), (nat_lit 2834, Int.ofNat (nat_lit 32845738161600)), (nat_lit 2844, Int.ofNat (nat_lit 1061671161600)), (nat_lit 2845, Int.ofNat (nat_lit 680402016000)), (nat_lit 2846, Int.ofNat (nat_lit 512236166400)), (nat_lit 2847, Int.ofNat (nat_lit 1289278368000))]
theorem block016_data_flat157_step : block016_data_flat157 = (CoefficientMerge.fastMerge block016_data_flat117 block016_data_flat156) := by decide +kernel
theorem block016_data_flat157_original : block016_data_flat157 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58898327545152 : Int) atom1176Coded) (CoefficientMerge.scale (43714896386304 : Int) atom1177Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50328202741536 : Int) atom1178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40369274295552 : Int) atom1179Coded) (CoefficientMerge.scale (63935689449600 : Int) atom1180Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44823459653760 : Int) atom1181Coded) (CoefficientMerge.scale (50291511241152 : Int) atom1182Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18599183925696 : Int) atom1183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23147791261632 : Int) atom1184Coded) (CoefficientMerge.scale (28126164973248 : Int) atom1185Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3684923594208 : Int) atom1186Coded) (CoefficientMerge.scale (4122798220800 : Int) atom1187Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7834685443200 : Int) atom1188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3472038057600 : Int) atom1189Coded) (CoefficientMerge.scale (427179916800 : Int) atom1190Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (343096992000 : Int) atom1191Coded) (CoefficientMerge.scale (4497994368000 : Int) atom1192Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6459401491200 : Int) atom1193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5397730329600 : Int) atom1194Coded) (CoefficientMerge.scale (427179916800 : Int) atom1195Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1196Coded) (CoefficientMerge.scale (1281539750400 : Int) atom1197Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8045165325312 : Int) atom1198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5465873347200 : Int) atom1199Coded) (CoefficientMerge.scale (10744058142720 : Int) atom1200Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16910574206400 : Int) atom1201Coded) (CoefficientMerge.scale (2523934022400 : Int) atom1202Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (259014067200 : Int) atom1203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (945208051200 : Int) atom1204Coded) (CoefficientMerge.scale (1631402035200 : Int) atom1205Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9159807182400 : Int) atom1206Coded) (CoefficientMerge.scale (3879597682800 : Int) atom1207Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715012760000 : Int) atom1208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14815693494000 : Int) atom1209Coded) (CoefficientMerge.scale (23440111203600 : Int) atom1210Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32845738161600 : Int) atom1211Coded) (CoefficientMerge.scale (1061671161600 : Int) atom1212Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (680402016000 : Int) atom1213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (512236166400 : Int) atom1214Coded) (CoefficientMerge.scale (1289278368000 : Int) atom1215Coded))))))) := by
  rw [block016_data_flat157_step, block016_data_flat117_original, block016_data_flat156_original]
def block016_data_flat158 : CoefficientMerge.Poly := [(nat_lit 2449, Int.ofNat (nat_lit 20238042645504)), (nat_lit 2450, Int.ofNat (nat_lit 20278634402304)), (nat_lit 2451, Int.ofNat (nat_lit 29238383522304)), (nat_lit 2452, Int.ofNat (nat_lit 26787755370240)), (nat_lit 2453, Int.ofNat (nat_lit 39115299746304)), (nat_lit 2454, Int.ofNat (nat_lit 39724813792512)), (nat_lit 2455, Int.ofNat (nat_lit 48335988821760)), (nat_lit 2456, Int.ofNat (nat_lit 56947163851008)), (nat_lit 2469, Int.ofNat (nat_lit 13458536612352)), (nat_lit 2470, Int.ofNat (nat_lit 25686756405504)), (nat_lit 2471, Int.ofNat (nat_lit 25145532981504)), (nat_lit 2472, Int.ofNat (nat_lit 29937883845504)), (nat_lit 2473, Int.ofNat (nat_lit 29509938218240)), (nat_lit 2474, Int.ofNat (nat_lit 40443829119104)), (nat_lit 2475, Int.ofNat (nat_lit 41715097976512)), (nat_lit 2476, Int.ofNat (nat_lit 49283350901760)), (nat_lit 2477, Int.ofNat (nat_lit 57682924975008)), (nat_lit 2491, Int.ofNat (nat_lit 16376678929152)), (nat_lit 2492, Int.ofNat (nat_lit 30291619682304)), (nat_lit 2493, Int.ofNat (nat_lit 34213038813504)), (nat_lit 2494, Int.ofNat (nat_lit 32778158869440)), (nat_lit 2495, Int.ofNat (nat_lit 45968048642304)), (nat_lit 2496, Int.ofNat (nat_lit 48255838538112)), (nat_lit 2497, Int.ofNat (nat_lit 48971706384960)), (nat_lit 2498, Int.ofNat (nat_lit 63039466358208)), (nat_lit 2513, Int.ofNat (nat_lit 20331751940352)), (nat_lit 2514, Int.ofNat (nat_lit 38507308418304)), (nat_lit 2515, Int.ofNat (nat_lit 35927230083840)), (nat_lit 2516, Int.ofNat (nat_lit 53554841282304)), (nat_lit 2517, Int.ofNat (nat_lit 57013026832512)), (nat_lit 2518, Int.ofNat (nat_lit 52848874978560)), (nat_lit 2519, Int.ofNat (nat_lit 72684357715008)), (nat_lit 2535, Int.ofNat (nat_lit 26020396714752)), (nat_lit 2536, Int.ofNat (nat_lit 47998729798272)), (nat_lit 2537, Int.ofNat (nat_lit 69989670434304)), (nat_lit 2538, Int.ofNat (nat_lit 69826861415808)), (nat_lit 2539, Int.ofNat (nat_lit 49709608836480)), (nat_lit 2540, Int.ofNat (nat_lit 73705078859904)), (nat_lit 2557, Int.ofNat (nat_lit 18866969402112)), (nat_lit 2558, Int.ofNat (nat_lit 56352193854336)), (nat_lit 2559, Int.ofNat (nat_lit 58898327545152)), (nat_lit 2560, Int.ofNat (nat_lit 43714896386304)), (nat_lit 2561, Int.ofNat (nat_lit 50328202741536)), (nat_lit 2579, Int.ofNat (nat_lit 40369274295552)), (nat_lit 2580, Int.ofNat (nat_lit 63935689449600)), (nat_lit 2581, Int.ofNat (nat_lit 44823459653760)), (nat_lit 2582, Int.ofNat (nat_lit 50291511241152)), (nat_lit 2601, Int.ofNat (nat_lit 18599183925696)), (nat_lit 2602, Int.ofNat (nat_lit 23147791261632)), (nat_lit 2603, Int.ofNat (nat_lit 28126164973248)), (nat_lit 2645, Int.ofNat (nat_lit 3684923594208)), (nat_lit 2778, Int.ofNat (nat_lit 4122798220800)), (nat_lit 2779, Int.ofNat (nat_lit 7834685443200)), (nat_lit 2780, Int.ofNat (nat_lit 3472038057600)), (nat_lit 2781, Int.ofNat (nat_lit 427179916800)), (nat_lit 2782, Int.ofNat (nat_lit 343096992000)), (nat_lit 2787, Int.ofNat (nat_lit 4497994368000)), (nat_lit 2800, Int.ofNat (nat_lit 6459401491200)), (nat_lit 2801, Int.ofNat (nat_lit 5397730329600)), (nat_lit 2805, Int.ofNat (nat_lit 427179916800)), (nat_lit 2806, Int.ofNat (nat_lit 854359833600)), (nat_lit 2807, Int.ofNat (nat_lit 1281539750400)), (nat_lit 2808, Int.ofNat (nat_lit 8045165325312)), (nat_lit 2811, Int.ofNat (nat_lit 5465873347200)), (nat_lit 2812, Int.ofNat (nat_lit 10744058142720)), (nat_lit 2813, Int.ofNat (nat_lit 16910574206400)), (nat_lit 2822, Int.ofNat (nat_lit 2523934022400)), (nat_lit 2826, Int.ofNat (nat_lit 259014067200)), (nat_lit 2827, Int.ofNat (nat_lit 945208051200)), (nat_lit 2828, Int.ofNat (nat_lit 1631402035200)), (nat_lit 2829, Int.ofNat (nat_lit 9159807182400)), (nat_lit 2830, Int.ofNat (nat_lit 3879597682800)), (nat_lit 2831, Int.ofNat (nat_lit 7715012760000)), (nat_lit 2832, Int.ofNat (nat_lit 14815693494000)), (nat_lit 2833, Int.ofNat (nat_lit 23440111203600)), (nat_lit 2834, Int.ofNat (nat_lit 32845738161600)), (nat_lit 2844, Int.ofNat (nat_lit 1061671161600)), (nat_lit 2845, Int.ofNat (nat_lit 680402016000)), (nat_lit 2846, Int.ofNat (nat_lit 512236166400)), (nat_lit 2847, Int.ofNat (nat_lit 1289278368000))]
theorem block016_data_flat158_step : block016_data_flat158 = (CoefficientMerge.fastMerge block016_data_flat078 block016_data_flat157) := by decide +kernel
theorem block016_data_flat158_original : block016_data_flat158 = (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20238042645504 : Int) atom1136Coded) (CoefficientMerge.scale (20278634402304 : Int) atom1137Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29238383522304 : Int) atom1138Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26787755370240 : Int) atom1139Coded) (CoefficientMerge.scale (39115299746304 : Int) atom1140Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39724813792512 : Int) atom1141Coded) (CoefficientMerge.scale (48335988821760 : Int) atom1142Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56947163851008 : Int) atom1143Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13458536612352 : Int) atom1144Coded) (CoefficientMerge.scale (25686756405504 : Int) atom1145Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25145532981504 : Int) atom1146Coded) (CoefficientMerge.scale (29937883845504 : Int) atom1147Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29509938218240 : Int) atom1148Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40443829119104 : Int) atom1149Coded) (CoefficientMerge.scale (41715097976512 : Int) atom1150Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49283350901760 : Int) atom1151Coded) (CoefficientMerge.scale (57682924975008 : Int) atom1152Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16376678929152 : Int) atom1153Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30291619682304 : Int) atom1154Coded) (CoefficientMerge.scale (34213038813504 : Int) atom1155Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32778158869440 : Int) atom1156Coded) (CoefficientMerge.scale (45968048642304 : Int) atom1157Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48255838538112 : Int) atom1158Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48971706384960 : Int) atom1159Coded) (CoefficientMerge.scale (63039466358208 : Int) atom1160Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20331751940352 : Int) atom1161Coded) (CoefficientMerge.scale (38507308418304 : Int) atom1162Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35927230083840 : Int) atom1163Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53554841282304 : Int) atom1164Coded) (CoefficientMerge.scale (57013026832512 : Int) atom1165Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52848874978560 : Int) atom1166Coded) (CoefficientMerge.scale (72684357715008 : Int) atom1167Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26020396714752 : Int) atom1168Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47998729798272 : Int) atom1169Coded) (CoefficientMerge.scale (69989670434304 : Int) atom1170Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69826861415808 : Int) atom1171Coded) (CoefficientMerge.scale (49709608836480 : Int) atom1172Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73705078859904 : Int) atom1173Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18866969402112 : Int) atom1174Coded) (CoefficientMerge.scale (56352193854336 : Int) atom1175Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58898327545152 : Int) atom1176Coded) (CoefficientMerge.scale (43714896386304 : Int) atom1177Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50328202741536 : Int) atom1178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40369274295552 : Int) atom1179Coded) (CoefficientMerge.scale (63935689449600 : Int) atom1180Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44823459653760 : Int) atom1181Coded) (CoefficientMerge.scale (50291511241152 : Int) atom1182Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18599183925696 : Int) atom1183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23147791261632 : Int) atom1184Coded) (CoefficientMerge.scale (28126164973248 : Int) atom1185Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3684923594208 : Int) atom1186Coded) (CoefficientMerge.scale (4122798220800 : Int) atom1187Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7834685443200 : Int) atom1188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3472038057600 : Int) atom1189Coded) (CoefficientMerge.scale (427179916800 : Int) atom1190Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (343096992000 : Int) atom1191Coded) (CoefficientMerge.scale (4497994368000 : Int) atom1192Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6459401491200 : Int) atom1193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5397730329600 : Int) atom1194Coded) (CoefficientMerge.scale (427179916800 : Int) atom1195Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1196Coded) (CoefficientMerge.scale (1281539750400 : Int) atom1197Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8045165325312 : Int) atom1198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5465873347200 : Int) atom1199Coded) (CoefficientMerge.scale (10744058142720 : Int) atom1200Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16910574206400 : Int) atom1201Coded) (CoefficientMerge.scale (2523934022400 : Int) atom1202Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (259014067200 : Int) atom1203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (945208051200 : Int) atom1204Coded) (CoefficientMerge.scale (1631402035200 : Int) atom1205Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9159807182400 : Int) atom1206Coded) (CoefficientMerge.scale (3879597682800 : Int) atom1207Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715012760000 : Int) atom1208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14815693494000 : Int) atom1209Coded) (CoefficientMerge.scale (23440111203600 : Int) atom1210Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32845738161600 : Int) atom1211Coded) (CoefficientMerge.scale (1061671161600 : Int) atom1212Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (680402016000 : Int) atom1213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (512236166400 : Int) atom1214Coded) (CoefficientMerge.scale (1289278368000 : Int) atom1215Coded)))))))) := by
  rw [block016_data_flat158_step, block016_data_flat078_original, block016_data_flat157_original]
def block016_data_flat159 : CoefficientMerge.Poly := [(nat_lit 2449, Int.ofNat (nat_lit 20238042645504)), (nat_lit 2450, Int.ofNat (nat_lit 20278634402304)), (nat_lit 2451, Int.ofNat (nat_lit 29238383522304)), (nat_lit 2452, Int.ofNat (nat_lit 26787755370240)), (nat_lit 2453, Int.ofNat (nat_lit 39115299746304)), (nat_lit 2454, Int.ofNat (nat_lit 39724813792512)), (nat_lit 2455, Int.ofNat (nat_lit 48335988821760)), (nat_lit 2456, Int.ofNat (nat_lit 56947163851008)), (nat_lit 2469, Int.ofNat (nat_lit 13458536612352)), (nat_lit 2470, Int.ofNat (nat_lit 25686756405504)), (nat_lit 2471, Int.ofNat (nat_lit 25145532981504)), (nat_lit 2472, Int.ofNat (nat_lit 29937883845504)), (nat_lit 2473, Int.ofNat (nat_lit 29509938218240)), (nat_lit 2474, Int.ofNat (nat_lit 40443829119104)), (nat_lit 2475, Int.ofNat (nat_lit 41715097976512)), (nat_lit 2476, Int.ofNat (nat_lit 49283350901760)), (nat_lit 2477, Int.ofNat (nat_lit 57682924975008)), (nat_lit 2491, Int.ofNat (nat_lit 16376678929152)), (nat_lit 2492, Int.ofNat (nat_lit 30291619682304)), (nat_lit 2493, Int.ofNat (nat_lit 34213038813504)), (nat_lit 2494, Int.ofNat (nat_lit 32778158869440)), (nat_lit 2495, Int.ofNat (nat_lit 45968048642304)), (nat_lit 2496, Int.ofNat (nat_lit 48255838538112)), (nat_lit 2497, Int.ofNat (nat_lit 48971706384960)), (nat_lit 2498, Int.ofNat (nat_lit 63039466358208)), (nat_lit 2513, Int.ofNat (nat_lit 20331751940352)), (nat_lit 2514, Int.ofNat (nat_lit 38507308418304)), (nat_lit 2515, Int.ofNat (nat_lit 35927230083840)), (nat_lit 2516, Int.ofNat (nat_lit 53554841282304)), (nat_lit 2517, Int.ofNat (nat_lit 57013026832512)), (nat_lit 2518, Int.ofNat (nat_lit 52848874978560)), (nat_lit 2519, Int.ofNat (nat_lit 72684357715008)), (nat_lit 2535, Int.ofNat (nat_lit 26020396714752)), (nat_lit 2536, Int.ofNat (nat_lit 47998729798272)), (nat_lit 2537, Int.ofNat (nat_lit 69989670434304)), (nat_lit 2538, Int.ofNat (nat_lit 69826861415808)), (nat_lit 2539, Int.ofNat (nat_lit 49709608836480)), (nat_lit 2540, Int.ofNat (nat_lit 73705078859904)), (nat_lit 2557, Int.ofNat (nat_lit 18866969402112)), (nat_lit 2558, Int.ofNat (nat_lit 56352193854336)), (nat_lit 2559, Int.ofNat (nat_lit 58898327545152)), (nat_lit 2560, Int.ofNat (nat_lit 43714896386304)), (nat_lit 2561, Int.ofNat (nat_lit 50328202741536)), (nat_lit 2579, Int.ofNat (nat_lit 40369274295552)), (nat_lit 2580, Int.ofNat (nat_lit 63935689449600)), (nat_lit 2581, Int.ofNat (nat_lit 44823459653760)), (nat_lit 2582, Int.ofNat (nat_lit 50291511241152)), (nat_lit 2601, Int.ofNat (nat_lit 18599183925696)), (nat_lit 2602, Int.ofNat (nat_lit 23147791261632)), (nat_lit 2603, Int.ofNat (nat_lit 28126164973248)), (nat_lit 2645, Int.ofNat (nat_lit 3684923594208)), (nat_lit 2778, Int.ofNat (nat_lit 4122798220800)), (nat_lit 2779, Int.ofNat (nat_lit 7834685443200)), (nat_lit 2780, Int.ofNat (nat_lit 3472038057600)), (nat_lit 2781, Int.ofNat (nat_lit 427179916800)), (nat_lit 2782, Int.ofNat (nat_lit 343096992000)), (nat_lit 2787, Int.ofNat (nat_lit 4497994368000)), (nat_lit 2800, Int.ofNat (nat_lit 6459401491200)), (nat_lit 2801, Int.ofNat (nat_lit 5397730329600)), (nat_lit 2805, Int.ofNat (nat_lit 427179916800)), (nat_lit 2806, Int.ofNat (nat_lit 854359833600)), (nat_lit 2807, Int.ofNat (nat_lit 1281539750400)), (nat_lit 2808, Int.ofNat (nat_lit 8045165325312)), (nat_lit 2811, Int.ofNat (nat_lit 5465873347200)), (nat_lit 2812, Int.ofNat (nat_lit 10744058142720)), (nat_lit 2813, Int.ofNat (nat_lit 16910574206400)), (nat_lit 2822, Int.ofNat (nat_lit 2523934022400)), (nat_lit 2826, Int.ofNat (nat_lit 259014067200)), (nat_lit 2827, Int.ofNat (nat_lit 945208051200)), (nat_lit 2828, Int.ofNat (nat_lit 1631402035200)), (nat_lit 2829, Int.ofNat (nat_lit 9159807182400)), (nat_lit 2830, Int.ofNat (nat_lit 3879597682800)), (nat_lit 2831, Int.ofNat (nat_lit 7715012760000)), (nat_lit 2832, Int.ofNat (nat_lit 14815693494000)), (nat_lit 2833, Int.ofNat (nat_lit 23440111203600)), (nat_lit 2834, Int.ofNat (nat_lit 32845738161600)), (nat_lit 2844, Int.ofNat (nat_lit 1061671161600)), (nat_lit 2845, Int.ofNat (nat_lit 680402016000)), (nat_lit 2846, Int.ofNat (nat_lit 512236166400)), (nat_lit 2847, Int.ofNat (nat_lit 1289278368000))]
theorem block016_data_flat159_step : block016_data_flat159 = (CoefficientMerge.trim block016_data_flat158) := by decide +kernel
theorem block016_data_flat159_original : block016_data_flat159 = (CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20238042645504 : Int) atom1136Coded) (CoefficientMerge.scale (20278634402304 : Int) atom1137Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29238383522304 : Int) atom1138Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26787755370240 : Int) atom1139Coded) (CoefficientMerge.scale (39115299746304 : Int) atom1140Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39724813792512 : Int) atom1141Coded) (CoefficientMerge.scale (48335988821760 : Int) atom1142Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56947163851008 : Int) atom1143Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13458536612352 : Int) atom1144Coded) (CoefficientMerge.scale (25686756405504 : Int) atom1145Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25145532981504 : Int) atom1146Coded) (CoefficientMerge.scale (29937883845504 : Int) atom1147Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29509938218240 : Int) atom1148Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40443829119104 : Int) atom1149Coded) (CoefficientMerge.scale (41715097976512 : Int) atom1150Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49283350901760 : Int) atom1151Coded) (CoefficientMerge.scale (57682924975008 : Int) atom1152Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16376678929152 : Int) atom1153Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30291619682304 : Int) atom1154Coded) (CoefficientMerge.scale (34213038813504 : Int) atom1155Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32778158869440 : Int) atom1156Coded) (CoefficientMerge.scale (45968048642304 : Int) atom1157Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48255838538112 : Int) atom1158Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48971706384960 : Int) atom1159Coded) (CoefficientMerge.scale (63039466358208 : Int) atom1160Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20331751940352 : Int) atom1161Coded) (CoefficientMerge.scale (38507308418304 : Int) atom1162Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35927230083840 : Int) atom1163Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53554841282304 : Int) atom1164Coded) (CoefficientMerge.scale (57013026832512 : Int) atom1165Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52848874978560 : Int) atom1166Coded) (CoefficientMerge.scale (72684357715008 : Int) atom1167Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26020396714752 : Int) atom1168Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47998729798272 : Int) atom1169Coded) (CoefficientMerge.scale (69989670434304 : Int) atom1170Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69826861415808 : Int) atom1171Coded) (CoefficientMerge.scale (49709608836480 : Int) atom1172Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73705078859904 : Int) atom1173Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18866969402112 : Int) atom1174Coded) (CoefficientMerge.scale (56352193854336 : Int) atom1175Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58898327545152 : Int) atom1176Coded) (CoefficientMerge.scale (43714896386304 : Int) atom1177Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50328202741536 : Int) atom1178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40369274295552 : Int) atom1179Coded) (CoefficientMerge.scale (63935689449600 : Int) atom1180Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44823459653760 : Int) atom1181Coded) (CoefficientMerge.scale (50291511241152 : Int) atom1182Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18599183925696 : Int) atom1183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23147791261632 : Int) atom1184Coded) (CoefficientMerge.scale (28126164973248 : Int) atom1185Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3684923594208 : Int) atom1186Coded) (CoefficientMerge.scale (4122798220800 : Int) atom1187Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7834685443200 : Int) atom1188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3472038057600 : Int) atom1189Coded) (CoefficientMerge.scale (427179916800 : Int) atom1190Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (343096992000 : Int) atom1191Coded) (CoefficientMerge.scale (4497994368000 : Int) atom1192Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6459401491200 : Int) atom1193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5397730329600 : Int) atom1194Coded) (CoefficientMerge.scale (427179916800 : Int) atom1195Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1196Coded) (CoefficientMerge.scale (1281539750400 : Int) atom1197Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8045165325312 : Int) atom1198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5465873347200 : Int) atom1199Coded) (CoefficientMerge.scale (10744058142720 : Int) atom1200Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16910574206400 : Int) atom1201Coded) (CoefficientMerge.scale (2523934022400 : Int) atom1202Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (259014067200 : Int) atom1203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (945208051200 : Int) atom1204Coded) (CoefficientMerge.scale (1631402035200 : Int) atom1205Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9159807182400 : Int) atom1206Coded) (CoefficientMerge.scale (3879597682800 : Int) atom1207Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715012760000 : Int) atom1208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14815693494000 : Int) atom1209Coded) (CoefficientMerge.scale (23440111203600 : Int) atom1210Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32845738161600 : Int) atom1211Coded) (CoefficientMerge.scale (1061671161600 : Int) atom1212Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (680402016000 : Int) atom1213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (512236166400 : Int) atom1214Coded) (CoefficientMerge.scale (1289278368000 : Int) atom1215Coded))))))))) := by
  rw [block016_data_flat159_step, block016_data_flat158_original]
theorem block016_data : block016 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20238042645504 : Int) atom1136Coded) (CoefficientMerge.scale (20278634402304 : Int) atom1137Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29238383522304 : Int) atom1138Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26787755370240 : Int) atom1139Coded) (CoefficientMerge.scale (39115299746304 : Int) atom1140Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39724813792512 : Int) atom1141Coded) (CoefficientMerge.scale (48335988821760 : Int) atom1142Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56947163851008 : Int) atom1143Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13458536612352 : Int) atom1144Coded) (CoefficientMerge.scale (25686756405504 : Int) atom1145Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25145532981504 : Int) atom1146Coded) (CoefficientMerge.scale (29937883845504 : Int) atom1147Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29509938218240 : Int) atom1148Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40443829119104 : Int) atom1149Coded) (CoefficientMerge.scale (41715097976512 : Int) atom1150Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49283350901760 : Int) atom1151Coded) (CoefficientMerge.scale (57682924975008 : Int) atom1152Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16376678929152 : Int) atom1153Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30291619682304 : Int) atom1154Coded) (CoefficientMerge.scale (34213038813504 : Int) atom1155Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32778158869440 : Int) atom1156Coded) (CoefficientMerge.scale (45968048642304 : Int) atom1157Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48255838538112 : Int) atom1158Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48971706384960 : Int) atom1159Coded) (CoefficientMerge.scale (63039466358208 : Int) atom1160Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20331751940352 : Int) atom1161Coded) (CoefficientMerge.scale (38507308418304 : Int) atom1162Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35927230083840 : Int) atom1163Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53554841282304 : Int) atom1164Coded) (CoefficientMerge.scale (57013026832512 : Int) atom1165Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52848874978560 : Int) atom1166Coded) (CoefficientMerge.scale (72684357715008 : Int) atom1167Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26020396714752 : Int) atom1168Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47998729798272 : Int) atom1169Coded) (CoefficientMerge.scale (69989670434304 : Int) atom1170Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69826861415808 : Int) atom1171Coded) (CoefficientMerge.scale (49709608836480 : Int) atom1172Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73705078859904 : Int) atom1173Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18866969402112 : Int) atom1174Coded) (CoefficientMerge.scale (56352193854336 : Int) atom1175Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58898327545152 : Int) atom1176Coded) (CoefficientMerge.scale (43714896386304 : Int) atom1177Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50328202741536 : Int) atom1178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40369274295552 : Int) atom1179Coded) (CoefficientMerge.scale (63935689449600 : Int) atom1180Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44823459653760 : Int) atom1181Coded) (CoefficientMerge.scale (50291511241152 : Int) atom1182Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18599183925696 : Int) atom1183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23147791261632 : Int) atom1184Coded) (CoefficientMerge.scale (28126164973248 : Int) atom1185Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3684923594208 : Int) atom1186Coded) (CoefficientMerge.scale (4122798220800 : Int) atom1187Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7834685443200 : Int) atom1188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3472038057600 : Int) atom1189Coded) (CoefficientMerge.scale (427179916800 : Int) atom1190Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (343096992000 : Int) atom1191Coded) (CoefficientMerge.scale (4497994368000 : Int) atom1192Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6459401491200 : Int) atom1193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5397730329600 : Int) atom1194Coded) (CoefficientMerge.scale (427179916800 : Int) atom1195Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1196Coded) (CoefficientMerge.scale (1281539750400 : Int) atom1197Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8045165325312 : Int) atom1198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5465873347200 : Int) atom1199Coded) (CoefficientMerge.scale (10744058142720 : Int) atom1200Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16910574206400 : Int) atom1201Coded) (CoefficientMerge.scale (2523934022400 : Int) atom1202Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (259014067200 : Int) atom1203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (945208051200 : Int) atom1204Coded) (CoefficientMerge.scale (1631402035200 : Int) atom1205Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9159807182400 : Int) atom1206Coded) (CoefficientMerge.scale (3879597682800 : Int) atom1207Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715012760000 : Int) atom1208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14815693494000 : Int) atom1209Coded) (CoefficientMerge.scale (23440111203600 : Int) atom1210Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32845738161600 : Int) atom1211Coded) (CoefficientMerge.scale (1061671161600 : Int) atom1212Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (680402016000 : Int) atom1213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (512236166400 : Int) atom1214Coded) (CoefficientMerge.scale (1289278368000 : Int) atom1215Coded)))))))) := by
  have h : block016 = block016_data_flat159 := by decide +kernel
  exact h.trans block016_data_flat159_original
theorem block016_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block016 := by
  rw [block016_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1136Coded_nonneg g hg hA hB) (atom1137Coded_nonneg g hg hA hB)) (add_nonneg (atom1138Coded_nonneg g hg hA hB) (add_nonneg (atom1139Coded_nonneg g hg hA hB) (atom1140Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1141Coded_nonneg g hg hA hB) (atom1142Coded_nonneg g hg hA hB)) (add_nonneg (atom1143Coded_nonneg g hg hA hB) (add_nonneg (atom1144Coded_nonneg g hg hA hB) (atom1145Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1146Coded_nonneg g hg hA hB) (atom1147Coded_nonneg g hg hA hB)) (add_nonneg (atom1148Coded_nonneg g hg hA hB) (add_nonneg (atom1149Coded_nonneg g hg hA hB) (atom1150Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1151Coded_nonneg g hg hA hB) (atom1152Coded_nonneg g hg hA hB)) (add_nonneg (atom1153Coded_nonneg g hg hA hB) (add_nonneg (atom1154Coded_nonneg g hg hA hB) (atom1155Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1156Coded_nonneg g hg hA hB) (atom1157Coded_nonneg g hg hA hB)) (add_nonneg (atom1158Coded_nonneg g hg hA hB) (add_nonneg (atom1159Coded_nonneg g hg hA hB) (atom1160Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1161Coded_nonneg g hg hA hB) (atom1162Coded_nonneg g hg hA hB)) (add_nonneg (atom1163Coded_nonneg g hg hA hB) (add_nonneg (atom1164Coded_nonneg g hg hA hB) (atom1165Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1166Coded_nonneg g hg hA hB) (atom1167Coded_nonneg g hg hA hB)) (add_nonneg (atom1168Coded_nonneg g hg hA hB) (add_nonneg (atom1169Coded_nonneg g hg hA hB) (atom1170Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1171Coded_nonneg g hg hA hB) (atom1172Coded_nonneg g hg hA hB)) (add_nonneg (atom1173Coded_nonneg g hg hA hB) (add_nonneg (atom1174Coded_nonneg g hg hA hB) (atom1175Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1176Coded_nonneg g hg hA hB) (atom1177Coded_nonneg g hg hA hB)) (add_nonneg (atom1178Coded_nonneg g hg hA hB) (add_nonneg (atom1179Coded_nonneg g hg hA hB) (atom1180Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1181Coded_nonneg g hg hA hB) (atom1182Coded_nonneg g hg hA hB)) (add_nonneg (atom1183Coded_nonneg g hg hA hB) (add_nonneg (atom1184Coded_nonneg g hg hA hB) (atom1185Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1186Coded_nonneg g hg hA hB) (atom1187Coded_nonneg g hg hA hB)) (add_nonneg (atom1188Coded_nonneg g hg hA hB) (add_nonneg (atom1189Coded_nonneg g hg hA hB) (atom1190Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1191Coded_nonneg g hg hA hB) (atom1192Coded_nonneg g hg hA hB)) (add_nonneg (atom1193Coded_nonneg g hg hA hB) (add_nonneg (atom1194Coded_nonneg g hg hA hB) (atom1195Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1196Coded_nonneg g hg hA hB) (atom1197Coded_nonneg g hg hA hB)) (add_nonneg (atom1198Coded_nonneg g hg hA hB) (add_nonneg (atom1199Coded_nonneg g hg hA hB) (atom1200Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1201Coded_nonneg g hg hA hB) (atom1202Coded_nonneg g hg hA hB)) (add_nonneg (atom1203Coded_nonneg g hg hA hB) (add_nonneg (atom1204Coded_nonneg g hg hA hB) (atom1205Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1206Coded_nonneg g hg hA hB) (atom1207Coded_nonneg g hg hA hB)) (add_nonneg (atom1208Coded_nonneg g hg hA hB) (add_nonneg (atom1209Coded_nonneg g hg hA hB) (atom1210Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1211Coded_nonneg g hg hA hB) (atom1212Coded_nonneg g hg hA hB)) (add_nonneg (atom1213Coded_nonneg g hg hA hB) (add_nonneg (atom1214Coded_nonneg g hg hA hB) (atom1215Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
