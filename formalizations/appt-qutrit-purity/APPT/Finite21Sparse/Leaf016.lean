import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1136 : SparsePolynomial.Poly := [([5,11,13], 1)]
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
def atom1136Coded : CoefficientMerge.Poly := [(2449, 1)]
theorem atom1136Coded_decode : atom1136 = SparsePolynomial.decodeCubic 21 atom1136Coded := by decide +kernel
theorem atom1136Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20238042645504 : Int) atom1136Coded) := by
  have h := atom1136_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1136Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1137 : SparsePolynomial.Poly := [([5,11,14], 1)]
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
def atom1137Coded : CoefficientMerge.Poly := [(2450, 1)]
theorem atom1137Coded_decode : atom1137 = SparsePolynomial.decodeCubic 21 atom1137Coded := by decide +kernel
theorem atom1137Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20278634402304 : Int) atom1137Coded) := by
  have h := atom1137_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1137Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1138 : SparsePolynomial.Poly := [([5,11,15], 1)]
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
def atom1138Coded : CoefficientMerge.Poly := [(2451, 1)]
theorem atom1138Coded_decode : atom1138 = SparsePolynomial.decodeCubic 21 atom1138Coded := by decide +kernel
theorem atom1138Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29238383522304 : Int) atom1138Coded) := by
  have h := atom1138_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1138Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1139 : SparsePolynomial.Poly := [([5,11,16], 1)]
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
def atom1139Coded : CoefficientMerge.Poly := [(2452, 1)]
theorem atom1139Coded_decode : atom1139 = SparsePolynomial.decodeCubic 21 atom1139Coded := by decide +kernel
theorem atom1139Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26787755370240 : Int) atom1139Coded) := by
  have h := atom1139_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1139Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1140 : SparsePolynomial.Poly := [([5,11,17], 1)]
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
def atom1140Coded : CoefficientMerge.Poly := [(2453, 1)]
theorem atom1140Coded_decode : atom1140 = SparsePolynomial.decodeCubic 21 atom1140Coded := by decide +kernel
theorem atom1140Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39115299746304 : Int) atom1140Coded) := by
  have h := atom1140_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1140Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1141 : SparsePolynomial.Poly := [([5,11,18], 1)]
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
def atom1141Coded : CoefficientMerge.Poly := [(2454, 1)]
theorem atom1141Coded_decode : atom1141 = SparsePolynomial.decodeCubic 21 atom1141Coded := by decide +kernel
theorem atom1141Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (39724813792512 : Int) atom1141Coded) := by
  have h := atom1141_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1141Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1142 : SparsePolynomial.Poly := [([5,11,19], 1)]
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
def atom1142Coded : CoefficientMerge.Poly := [(2455, 1)]
theorem atom1142Coded_decode : atom1142 = SparsePolynomial.decodeCubic 21 atom1142Coded := by decide +kernel
theorem atom1142Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48335988821760 : Int) atom1142Coded) := by
  have h := atom1142_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1142Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1143 : SparsePolynomial.Poly := [([5,11,20], 1)]
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
def atom1143Coded : CoefficientMerge.Poly := [(2456, 1)]
theorem atom1143Coded_decode : atom1143 = SparsePolynomial.decodeCubic 21 atom1143Coded := by decide +kernel
theorem atom1143Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (56947163851008 : Int) atom1143Coded) := by
  have h := atom1143_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1143Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1144 : SparsePolynomial.Poly := [([5,12,12], 1)]
theorem eval_atom1144 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1144 = ((g 5) * (g 12) * (g 12)) := by
  norm_num [atom1144, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1144_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13458536612352 : Int) atom1144) := by
  rw [SparsePolynomial.eval_scale, eval_atom1144]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1144Coded : CoefficientMerge.Poly := [(2469, 1)]
theorem atom1144Coded_decode : atom1144 = SparsePolynomial.decodeCubic 21 atom1144Coded := by decide +kernel
theorem atom1144Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (13458536612352 : Int) atom1144Coded) := by
  have h := atom1144_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1144Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1145 : SparsePolynomial.Poly := [([5,12,13], 1)]
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
def atom1145Coded : CoefficientMerge.Poly := [(2470, 1)]
theorem atom1145Coded_decode : atom1145 = SparsePolynomial.decodeCubic 21 atom1145Coded := by decide +kernel
theorem atom1145Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25686756405504 : Int) atom1145Coded) := by
  have h := atom1145_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1145Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1146 : SparsePolynomial.Poly := [([5,12,14], 1)]
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
def atom1146Coded : CoefficientMerge.Poly := [(2471, 1)]
theorem atom1146Coded_decode : atom1146 = SparsePolynomial.decodeCubic 21 atom1146Coded := by decide +kernel
theorem atom1146Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (25145532981504 : Int) atom1146Coded) := by
  have h := atom1146_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1146Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1147 : SparsePolynomial.Poly := [([5,12,15], 1)]
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
def atom1147Coded : CoefficientMerge.Poly := [(2472, 1)]
theorem atom1147Coded_decode : atom1147 = SparsePolynomial.decodeCubic 21 atom1147Coded := by decide +kernel
theorem atom1147Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29937883845504 : Int) atom1147Coded) := by
  have h := atom1147_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1147Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1148 : SparsePolynomial.Poly := [([5,12,16], 1)]
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
def atom1148Coded : CoefficientMerge.Poly := [(2473, 1)]
theorem atom1148Coded_decode : atom1148 = SparsePolynomial.decodeCubic 21 atom1148Coded := by decide +kernel
theorem atom1148Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (29509938218240 : Int) atom1148Coded) := by
  have h := atom1148_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1148Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1149 : SparsePolynomial.Poly := [([5,12,17], 1)]
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
def atom1149Coded : CoefficientMerge.Poly := [(2474, 1)]
theorem atom1149Coded_decode : atom1149 = SparsePolynomial.decodeCubic 21 atom1149Coded := by decide +kernel
theorem atom1149Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40443829119104 : Int) atom1149Coded) := by
  have h := atom1149_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1149Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1150 : SparsePolynomial.Poly := [([5,12,18], 1)]
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
def atom1150Coded : CoefficientMerge.Poly := [(2475, 1)]
theorem atom1150Coded_decode : atom1150 = SparsePolynomial.decodeCubic 21 atom1150Coded := by decide +kernel
theorem atom1150Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (41715097976512 : Int) atom1150Coded) := by
  have h := atom1150_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1150Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1151 : SparsePolynomial.Poly := [([5,12,19], 1)]
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
def atom1151Coded : CoefficientMerge.Poly := [(2476, 1)]
theorem atom1151Coded_decode : atom1151 = SparsePolynomial.decodeCubic 21 atom1151Coded := by decide +kernel
theorem atom1151Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49283350901760 : Int) atom1151Coded) := by
  have h := atom1151_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1151Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1152 : SparsePolynomial.Poly := [([5,12,20], 1)]
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
def atom1152Coded : CoefficientMerge.Poly := [(2477, 1)]
theorem atom1152Coded_decode : atom1152 = SparsePolynomial.decodeCubic 21 atom1152Coded := by decide +kernel
theorem atom1152Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (57682924975008 : Int) atom1152Coded) := by
  have h := atom1152_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1152Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1153 : SparsePolynomial.Poly := [([5,13,13], 1)]
theorem eval_atom1153 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1153 = ((g 5) * (g 13) * (g 13)) := by
  norm_num [atom1153, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1153_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16376678929152 : Int) atom1153) := by
  rw [SparsePolynomial.eval_scale, eval_atom1153]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1153Coded : CoefficientMerge.Poly := [(2491, 1)]
theorem atom1153Coded_decode : atom1153 = SparsePolynomial.decodeCubic 21 atom1153Coded := by decide +kernel
theorem atom1153Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16376678929152 : Int) atom1153Coded) := by
  have h := atom1153_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1153Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1154 : SparsePolynomial.Poly := [([5,13,14], 1)]
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
def atom1154Coded : CoefficientMerge.Poly := [(2492, 1)]
theorem atom1154Coded_decode : atom1154 = SparsePolynomial.decodeCubic 21 atom1154Coded := by decide +kernel
theorem atom1154Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (30291619682304 : Int) atom1154Coded) := by
  have h := atom1154_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1154Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1155 : SparsePolynomial.Poly := [([5,13,15], 1)]
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
def atom1155Coded : CoefficientMerge.Poly := [(2493, 1)]
theorem atom1155Coded_decode : atom1155 = SparsePolynomial.decodeCubic 21 atom1155Coded := by decide +kernel
theorem atom1155Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (34213038813504 : Int) atom1155Coded) := by
  have h := atom1155_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1155Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1156 : SparsePolynomial.Poly := [([5,13,16], 1)]
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
def atom1156Coded : CoefficientMerge.Poly := [(2494, 1)]
theorem atom1156Coded_decode : atom1156 = SparsePolynomial.decodeCubic 21 atom1156Coded := by decide +kernel
theorem atom1156Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32778158869440 : Int) atom1156Coded) := by
  have h := atom1156_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1156Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1157 : SparsePolynomial.Poly := [([5,13,17], 1)]
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
def atom1157Coded : CoefficientMerge.Poly := [(2495, 1)]
theorem atom1157Coded_decode : atom1157 = SparsePolynomial.decodeCubic 21 atom1157Coded := by decide +kernel
theorem atom1157Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (45968048642304 : Int) atom1157Coded) := by
  have h := atom1157_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1157Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1158 : SparsePolynomial.Poly := [([5,13,18], 1)]
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
def atom1158Coded : CoefficientMerge.Poly := [(2496, 1)]
theorem atom1158Coded_decode : atom1158 = SparsePolynomial.decodeCubic 21 atom1158Coded := by decide +kernel
theorem atom1158Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48255838538112 : Int) atom1158Coded) := by
  have h := atom1158_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1158Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1159 : SparsePolynomial.Poly := [([5,13,19], 1)]
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
def atom1159Coded : CoefficientMerge.Poly := [(2497, 1)]
theorem atom1159Coded_decode : atom1159 = SparsePolynomial.decodeCubic 21 atom1159Coded := by decide +kernel
theorem atom1159Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (48971706384960 : Int) atom1159Coded) := by
  have h := atom1159_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1159Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1160 : SparsePolynomial.Poly := [([5,13,20], 1)]
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
def atom1160Coded : CoefficientMerge.Poly := [(2498, 1)]
theorem atom1160Coded_decode : atom1160 = SparsePolynomial.decodeCubic 21 atom1160Coded := by decide +kernel
theorem atom1160Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (63039466358208 : Int) atom1160Coded) := by
  have h := atom1160_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1160Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1161 : SparsePolynomial.Poly := [([5,14,14], 1)]
theorem eval_atom1161 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1161 = ((g 5) * (g 14) * (g 14)) := by
  norm_num [atom1161, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1161_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20331751940352 : Int) atom1161) := by
  rw [SparsePolynomial.eval_scale, eval_atom1161]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1161Coded : CoefficientMerge.Poly := [(2513, 1)]
theorem atom1161Coded_decode : atom1161 = SparsePolynomial.decodeCubic 21 atom1161Coded := by decide +kernel
theorem atom1161Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (20331751940352 : Int) atom1161Coded) := by
  have h := atom1161_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1161Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1162 : SparsePolynomial.Poly := [([5,14,15], 1)]
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
def atom1162Coded : CoefficientMerge.Poly := [(2514, 1)]
theorem atom1162Coded_decode : atom1162 = SparsePolynomial.decodeCubic 21 atom1162Coded := by decide +kernel
theorem atom1162Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (38507308418304 : Int) atom1162Coded) := by
  have h := atom1162_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1162Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1163 : SparsePolynomial.Poly := [([5,14,16], 1)]
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
def atom1163Coded : CoefficientMerge.Poly := [(2515, 1)]
theorem atom1163Coded_decode : atom1163 = SparsePolynomial.decodeCubic 21 atom1163Coded := by decide +kernel
theorem atom1163Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (35927230083840 : Int) atom1163Coded) := by
  have h := atom1163_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1163Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1164 : SparsePolynomial.Poly := [([5,14,17], 1)]
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
def atom1164Coded : CoefficientMerge.Poly := [(2516, 1)]
theorem atom1164Coded_decode : atom1164 = SparsePolynomial.decodeCubic 21 atom1164Coded := by decide +kernel
theorem atom1164Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (53554841282304 : Int) atom1164Coded) := by
  have h := atom1164_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1164Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1165 : SparsePolynomial.Poly := [([5,14,18], 1)]
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
def atom1165Coded : CoefficientMerge.Poly := [(2517, 1)]
theorem atom1165Coded_decode : atom1165 = SparsePolynomial.decodeCubic 21 atom1165Coded := by decide +kernel
theorem atom1165Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (57013026832512 : Int) atom1165Coded) := by
  have h := atom1165_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1165Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1166 : SparsePolynomial.Poly := [([5,14,19], 1)]
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
def atom1166Coded : CoefficientMerge.Poly := [(2518, 1)]
theorem atom1166Coded_decode : atom1166 = SparsePolynomial.decodeCubic 21 atom1166Coded := by decide +kernel
theorem atom1166Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (52848874978560 : Int) atom1166Coded) := by
  have h := atom1166_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1166Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1167 : SparsePolynomial.Poly := [([5,14,20], 1)]
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
def atom1167Coded : CoefficientMerge.Poly := [(2519, 1)]
theorem atom1167Coded_decode : atom1167 = SparsePolynomial.decodeCubic 21 atom1167Coded := by decide +kernel
theorem atom1167Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (72684357715008 : Int) atom1167Coded) := by
  have h := atom1167_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1167Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1168 : SparsePolynomial.Poly := [([5,15,15], 1)]
theorem eval_atom1168 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1168 = ((g 5) * (g 15) * (g 15)) := by
  norm_num [atom1168, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1168_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (26020396714752 : Int) atom1168) := by
  rw [SparsePolynomial.eval_scale, eval_atom1168]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1168Coded : CoefficientMerge.Poly := [(2535, 1)]
theorem atom1168Coded_decode : atom1168 = SparsePolynomial.decodeCubic 21 atom1168Coded := by decide +kernel
theorem atom1168Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (26020396714752 : Int) atom1168Coded) := by
  have h := atom1168_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1168Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1169 : SparsePolynomial.Poly := [([5,15,16], 1)]
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
def atom1169Coded : CoefficientMerge.Poly := [(2536, 1)]
theorem atom1169Coded_decode : atom1169 = SparsePolynomial.decodeCubic 21 atom1169Coded := by decide +kernel
theorem atom1169Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (47998729798272 : Int) atom1169Coded) := by
  have h := atom1169_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1169Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1170 : SparsePolynomial.Poly := [([5,15,17], 1)]
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
def atom1170Coded : CoefficientMerge.Poly := [(2537, 1)]
theorem atom1170Coded_decode : atom1170 = SparsePolynomial.decodeCubic 21 atom1170Coded := by decide +kernel
theorem atom1170Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (69989670434304 : Int) atom1170Coded) := by
  have h := atom1170_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1170Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1171 : SparsePolynomial.Poly := [([5,15,18], 1)]
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
def atom1171Coded : CoefficientMerge.Poly := [(2538, 1)]
theorem atom1171Coded_decode : atom1171 = SparsePolynomial.decodeCubic 21 atom1171Coded := by decide +kernel
theorem atom1171Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (69826861415808 : Int) atom1171Coded) := by
  have h := atom1171_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1171Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1172 : SparsePolynomial.Poly := [([5,15,19], 1)]
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
def atom1172Coded : CoefficientMerge.Poly := [(2539, 1)]
theorem atom1172Coded_decode : atom1172 = SparsePolynomial.decodeCubic 21 atom1172Coded := by decide +kernel
theorem atom1172Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (49709608836480 : Int) atom1172Coded) := by
  have h := atom1172_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1172Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1173 : SparsePolynomial.Poly := [([5,15,20], 1)]
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
def atom1173Coded : CoefficientMerge.Poly := [(2540, 1)]
theorem atom1173Coded_decode : atom1173 = SparsePolynomial.decodeCubic 21 atom1173Coded := by decide +kernel
theorem atom1173Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (73705078859904 : Int) atom1173Coded) := by
  have h := atom1173_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1173Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1174 : SparsePolynomial.Poly := [([5,16,16], 1)]
theorem eval_atom1174 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1174 = ((g 5) * (g 16) * (g 16)) := by
  norm_num [atom1174, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1174_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18866969402112 : Int) atom1174) := by
  rw [SparsePolynomial.eval_scale, eval_atom1174]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1174Coded : CoefficientMerge.Poly := [(2557, 1)]
theorem atom1174Coded_decode : atom1174 = SparsePolynomial.decodeCubic 21 atom1174Coded := by decide +kernel
theorem atom1174Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18866969402112 : Int) atom1174Coded) := by
  have h := atom1174_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1174Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1175 : SparsePolynomial.Poly := [([5,16,17], 1)]
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
def atom1175Coded : CoefficientMerge.Poly := [(2558, 1)]
theorem atom1175Coded_decode : atom1175 = SparsePolynomial.decodeCubic 21 atom1175Coded := by decide +kernel
theorem atom1175Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (56352193854336 : Int) atom1175Coded) := by
  have h := atom1175_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1175Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1176 : SparsePolynomial.Poly := [([5,16,18], 1)]
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
def atom1176Coded : CoefficientMerge.Poly := [(2559, 1)]
theorem atom1176Coded_decode : atom1176 = SparsePolynomial.decodeCubic 21 atom1176Coded := by decide +kernel
theorem atom1176Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (58898327545152 : Int) atom1176Coded) := by
  have h := atom1176_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1176Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1177 : SparsePolynomial.Poly := [([5,16,19], 1)]
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
def atom1177Coded : CoefficientMerge.Poly := [(2560, 1)]
theorem atom1177Coded_decode : atom1177 = SparsePolynomial.decodeCubic 21 atom1177Coded := by decide +kernel
theorem atom1177Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (43714896386304 : Int) atom1177Coded) := by
  have h := atom1177_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1177Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1178 : SparsePolynomial.Poly := [([5,16,20], 1)]
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
def atom1178Coded : CoefficientMerge.Poly := [(2561, 1)]
theorem atom1178Coded_decode : atom1178 = SparsePolynomial.decodeCubic 21 atom1178Coded := by decide +kernel
theorem atom1178Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50328202741536 : Int) atom1178Coded) := by
  have h := atom1178_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1178Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1179 : SparsePolynomial.Poly := [([5,17,17], 1)]
theorem eval_atom1179 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1179 = ((g 5) * (g 17) * (g 17)) := by
  norm_num [atom1179, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1179_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40369274295552 : Int) atom1179) := by
  rw [SparsePolynomial.eval_scale, eval_atom1179]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1179Coded : CoefficientMerge.Poly := [(2579, 1)]
theorem atom1179Coded_decode : atom1179 = SparsePolynomial.decodeCubic 21 atom1179Coded := by decide +kernel
theorem atom1179Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (40369274295552 : Int) atom1179Coded) := by
  have h := atom1179_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1179Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1180 : SparsePolynomial.Poly := [([5,17,18], 1)]
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
def atom1180Coded : CoefficientMerge.Poly := [(2580, 1)]
theorem atom1180Coded_decode : atom1180 = SparsePolynomial.decodeCubic 21 atom1180Coded := by decide +kernel
theorem atom1180Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (63935689449600 : Int) atom1180Coded) := by
  have h := atom1180_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1180Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1181 : SparsePolynomial.Poly := [([5,17,19], 1)]
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
def atom1181Coded : CoefficientMerge.Poly := [(2581, 1)]
theorem atom1181Coded_decode : atom1181 = SparsePolynomial.decodeCubic 21 atom1181Coded := by decide +kernel
theorem atom1181Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (44823459653760 : Int) atom1181Coded) := by
  have h := atom1181_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1181Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1182 : SparsePolynomial.Poly := [([5,17,20], 1)]
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
def atom1182Coded : CoefficientMerge.Poly := [(2582, 1)]
theorem atom1182Coded_decode : atom1182 = SparsePolynomial.decodeCubic 21 atom1182Coded := by decide +kernel
theorem atom1182Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (50291511241152 : Int) atom1182Coded) := by
  have h := atom1182_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1182Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1183 : SparsePolynomial.Poly := [([5,18,18], 1)]
theorem eval_atom1183 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1183 = ((g 5) * (g 18) * (g 18)) := by
  norm_num [atom1183, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1183_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18599183925696 : Int) atom1183) := by
  rw [SparsePolynomial.eval_scale, eval_atom1183]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1183Coded : CoefficientMerge.Poly := [(2601, 1)]
theorem atom1183Coded_decode : atom1183 = SparsePolynomial.decodeCubic 21 atom1183Coded := by decide +kernel
theorem atom1183Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (18599183925696 : Int) atom1183Coded) := by
  have h := atom1183_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1183Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1184 : SparsePolynomial.Poly := [([5,18,19], 1)]
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
def atom1184Coded : CoefficientMerge.Poly := [(2602, 1)]
theorem atom1184Coded_decode : atom1184 = SparsePolynomial.decodeCubic 21 atom1184Coded := by decide +kernel
theorem atom1184Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23147791261632 : Int) atom1184Coded) := by
  have h := atom1184_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1184Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1185 : SparsePolynomial.Poly := [([5,18,20], 1)]
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
def atom1185Coded : CoefficientMerge.Poly := [(2603, 1)]
theorem atom1185Coded_decode : atom1185 = SparsePolynomial.decodeCubic 21 atom1185Coded := by decide +kernel
theorem atom1185Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (28126164973248 : Int) atom1185Coded) := by
  have h := atom1185_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1185Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1186 : SparsePolynomial.Poly := [([5,20,20], 1)]
theorem eval_atom1186 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1186 = ((g 5) * (g 20) * (g 20)) := by
  norm_num [atom1186, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1186_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3684923594208 : Int) atom1186) := by
  rw [SparsePolynomial.eval_scale, eval_atom1186]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1186Coded : CoefficientMerge.Poly := [(2645, 1)]
theorem atom1186Coded_decode : atom1186 = SparsePolynomial.decodeCubic 21 atom1186Coded := by decide +kernel
theorem atom1186Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3684923594208 : Int) atom1186Coded) := by
  have h := atom1186_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1186Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1187 : SparsePolynomial.Poly := [([6,6,6], 1)]
theorem eval_atom1187 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1187 = ((g 6) * (g 6) * (g 6)) := by
  norm_num [atom1187, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1187_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4122798220800 : Int) atom1187) := by
  rw [SparsePolynomial.eval_scale, eval_atom1187]
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 6) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1187Coded : CoefficientMerge.Poly := [(2778, 1)]
theorem atom1187Coded_decode : atom1187 = SparsePolynomial.decodeCubic 21 atom1187Coded := by decide +kernel
theorem atom1187Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4122798220800 : Int) atom1187Coded) := by
  have h := atom1187_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1187Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1188 : SparsePolynomial.Poly := [([6,6,7], 1)]
theorem eval_atom1188 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1188 = ((g 6) * (g 6) * (g 7)) := by
  norm_num [atom1188, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1188_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7834685443200 : Int) atom1188) := by
  rw [SparsePolynomial.eval_scale, eval_atom1188]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1188Coded : CoefficientMerge.Poly := [(2779, 1)]
theorem atom1188Coded_decode : atom1188 = SparsePolynomial.decodeCubic 21 atom1188Coded := by decide +kernel
theorem atom1188Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7834685443200 : Int) atom1188Coded) := by
  have h := atom1188_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1188Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1189 : SparsePolynomial.Poly := [([6,6,8], 1)]
theorem eval_atom1189 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1189 = ((g 6) * (g 6) * (g 8)) := by
  norm_num [atom1189, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1189_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3472038057600 : Int) atom1189) := by
  rw [SparsePolynomial.eval_scale, eval_atom1189]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1189Coded : CoefficientMerge.Poly := [(2780, 1)]
theorem atom1189Coded_decode : atom1189 = SparsePolynomial.decodeCubic 21 atom1189Coded := by decide +kernel
theorem atom1189Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3472038057600 : Int) atom1189Coded) := by
  have h := atom1189_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1189Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1190 : SparsePolynomial.Poly := [([6,6,9], 1)]
theorem eval_atom1190 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1190 = ((g 6) * (g 6) * (g 9)) := by
  norm_num [atom1190, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1190_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1190) := by
  rw [SparsePolynomial.eval_scale, eval_atom1190]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1190Coded : CoefficientMerge.Poly := [(2781, 1)]
theorem atom1190Coded_decode : atom1190 = SparsePolynomial.decodeCubic 21 atom1190Coded := by decide +kernel
theorem atom1190Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1190Coded) := by
  have h := atom1190_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1190Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1191 : SparsePolynomial.Poly := [([6,6,10], 1)]
theorem eval_atom1191 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1191 = ((g 6) * (g 6) * (g 10)) := by
  norm_num [atom1191, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1191_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (343096992000 : Int) atom1191) := by
  rw [SparsePolynomial.eval_scale, eval_atom1191]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1191Coded : CoefficientMerge.Poly := [(2782, 1)]
theorem atom1191Coded_decode : atom1191 = SparsePolynomial.decodeCubic 21 atom1191Coded := by decide +kernel
theorem atom1191Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (343096992000 : Int) atom1191Coded) := by
  have h := atom1191_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1191Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1192 : SparsePolynomial.Poly := [([6,6,15], 1)]
theorem eval_atom1192 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1192 = ((g 6) * (g 6) * (g 15)) := by
  norm_num [atom1192, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1192_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4497994368000 : Int) atom1192) := by
  rw [SparsePolynomial.eval_scale, eval_atom1192]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1192Coded : CoefficientMerge.Poly := [(2787, 1)]
theorem atom1192Coded_decode : atom1192 = SparsePolynomial.decodeCubic 21 atom1192Coded := by decide +kernel
theorem atom1192Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (4497994368000 : Int) atom1192Coded) := by
  have h := atom1192_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1192Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1193 : SparsePolynomial.Poly := [([6,7,7], 1)]
theorem eval_atom1193 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1193 = ((g 6) * (g 7) * (g 7)) := by
  norm_num [atom1193, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1193_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6459401491200 : Int) atom1193) := by
  rw [SparsePolynomial.eval_scale, eval_atom1193]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1193Coded : CoefficientMerge.Poly := [(2800, 1)]
theorem atom1193Coded_decode : atom1193 = SparsePolynomial.decodeCubic 21 atom1193Coded := by decide +kernel
theorem atom1193Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (6459401491200 : Int) atom1193Coded) := by
  have h := atom1193_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1193Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1194 : SparsePolynomial.Poly := [([6,7,8], 1)]
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
def atom1194Coded : CoefficientMerge.Poly := [(2801, 1)]
theorem atom1194Coded_decode : atom1194 = SparsePolynomial.decodeCubic 21 atom1194Coded := by decide +kernel
theorem atom1194Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5397730329600 : Int) atom1194Coded) := by
  have h := atom1194_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1194Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1195 : SparsePolynomial.Poly := [([6,7,12], 1)]
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
def atom1195Coded : CoefficientMerge.Poly := [(2805, 1)]
theorem atom1195Coded_decode : atom1195 = SparsePolynomial.decodeCubic 21 atom1195Coded := by decide +kernel
theorem atom1195Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (427179916800 : Int) atom1195Coded) := by
  have h := atom1195_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1195Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1196 : SparsePolynomial.Poly := [([6,7,13], 1)]
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
def atom1196Coded : CoefficientMerge.Poly := [(2806, 1)]
theorem atom1196Coded_decode : atom1196 = SparsePolynomial.decodeCubic 21 atom1196Coded := by decide +kernel
theorem atom1196Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (854359833600 : Int) atom1196Coded) := by
  have h := atom1196_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1196Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1197 : SparsePolynomial.Poly := [([6,7,14], 1)]
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
def atom1197Coded : CoefficientMerge.Poly := [(2807, 1)]
theorem atom1197Coded_decode : atom1197 = SparsePolynomial.decodeCubic 21 atom1197Coded := by decide +kernel
theorem atom1197Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1281539750400 : Int) atom1197Coded) := by
  have h := atom1197_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1197Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1198 : SparsePolynomial.Poly := [([6,7,15], 1)]
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
def atom1198Coded : CoefficientMerge.Poly := [(2808, 1)]
theorem atom1198Coded_decode : atom1198 = SparsePolynomial.decodeCubic 21 atom1198Coded := by decide +kernel
theorem atom1198Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (8045165325312 : Int) atom1198Coded) := by
  have h := atom1198_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1198Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1199 : SparsePolynomial.Poly := [([6,7,18], 1)]
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
def atom1199Coded : CoefficientMerge.Poly := [(2811, 1)]
theorem atom1199Coded_decode : atom1199 = SparsePolynomial.decodeCubic 21 atom1199Coded := by decide +kernel
theorem atom1199Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (5465873347200 : Int) atom1199Coded) := by
  have h := atom1199_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1199Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1200 : SparsePolynomial.Poly := [([6,7,19], 1)]
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
def atom1200Coded : CoefficientMerge.Poly := [(2812, 1)]
theorem atom1200Coded_decode : atom1200 = SparsePolynomial.decodeCubic 21 atom1200Coded := by decide +kernel
theorem atom1200Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (10744058142720 : Int) atom1200Coded) := by
  have h := atom1200_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1200Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1201 : SparsePolynomial.Poly := [([6,7,20], 1)]
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
def atom1201Coded : CoefficientMerge.Poly := [(2813, 1)]
theorem atom1201Coded_decode : atom1201 = SparsePolynomial.decodeCubic 21 atom1201Coded := by decide +kernel
theorem atom1201Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (16910574206400 : Int) atom1201Coded) := by
  have h := atom1201_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1201Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1202 : SparsePolynomial.Poly := [([6,8,8], 1)]
theorem eval_atom1202 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1202 = ((g 6) * (g 8) * (g 8)) := by
  norm_num [atom1202, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1202_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2523934022400 : Int) atom1202) := by
  rw [SparsePolynomial.eval_scale, eval_atom1202]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1202Coded : CoefficientMerge.Poly := [(2822, 1)]
theorem atom1202Coded_decode : atom1202 = SparsePolynomial.decodeCubic 21 atom1202Coded := by decide +kernel
theorem atom1202Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (2523934022400 : Int) atom1202Coded) := by
  have h := atom1202_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1202Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1203 : SparsePolynomial.Poly := [([6,8,12], 1)]
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
def atom1203Coded : CoefficientMerge.Poly := [(2826, 1)]
theorem atom1203Coded_decode : atom1203 = SparsePolynomial.decodeCubic 21 atom1203Coded := by decide +kernel
theorem atom1203Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (259014067200 : Int) atom1203Coded) := by
  have h := atom1203_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1203Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1204 : SparsePolynomial.Poly := [([6,8,13], 1)]
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
def atom1204Coded : CoefficientMerge.Poly := [(2827, 1)]
theorem atom1204Coded_decode : atom1204 = SparsePolynomial.decodeCubic 21 atom1204Coded := by decide +kernel
theorem atom1204Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (945208051200 : Int) atom1204Coded) := by
  have h := atom1204_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1204Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1205 : SparsePolynomial.Poly := [([6,8,14], 1)]
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
def atom1205Coded : CoefficientMerge.Poly := [(2828, 1)]
theorem atom1205Coded_decode : atom1205 = SparsePolynomial.decodeCubic 21 atom1205Coded := by decide +kernel
theorem atom1205Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1631402035200 : Int) atom1205Coded) := by
  have h := atom1205_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1205Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1206 : SparsePolynomial.Poly := [([6,8,15], 1)]
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
def atom1206Coded : CoefficientMerge.Poly := [(2829, 1)]
theorem atom1206Coded_decode : atom1206 = SparsePolynomial.decodeCubic 21 atom1206Coded := by decide +kernel
theorem atom1206Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (9159807182400 : Int) atom1206Coded) := by
  have h := atom1206_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1206Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1207 : SparsePolynomial.Poly := [([6,8,16], 1)]
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
def atom1207Coded : CoefficientMerge.Poly := [(2830, 1)]
theorem atom1207Coded_decode : atom1207 = SparsePolynomial.decodeCubic 21 atom1207Coded := by decide +kernel
theorem atom1207Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (3879597682800 : Int) atom1207Coded) := by
  have h := atom1207_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1207Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1208 : SparsePolynomial.Poly := [([6,8,17], 1)]
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
def atom1208Coded : CoefficientMerge.Poly := [(2831, 1)]
theorem atom1208Coded_decode : atom1208 = SparsePolynomial.decodeCubic 21 atom1208Coded := by decide +kernel
theorem atom1208Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (7715012760000 : Int) atom1208Coded) := by
  have h := atom1208_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1208Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1209 : SparsePolynomial.Poly := [([6,8,18], 1)]
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
def atom1209Coded : CoefficientMerge.Poly := [(2832, 1)]
theorem atom1209Coded_decode : atom1209 = SparsePolynomial.decodeCubic 21 atom1209Coded := by decide +kernel
theorem atom1209Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (14815693494000 : Int) atom1209Coded) := by
  have h := atom1209_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1209Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1210 : SparsePolynomial.Poly := [([6,8,19], 1)]
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
def atom1210Coded : CoefficientMerge.Poly := [(2833, 1)]
theorem atom1210Coded_decode : atom1210 = SparsePolynomial.decodeCubic 21 atom1210Coded := by decide +kernel
theorem atom1210Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (23440111203600 : Int) atom1210Coded) := by
  have h := atom1210_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1210Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1211 : SparsePolynomial.Poly := [([6,8,20], 1)]
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
def atom1211Coded : CoefficientMerge.Poly := [(2834, 1)]
theorem atom1211Coded_decode : atom1211 = SparsePolynomial.decodeCubic 21 atom1211Coded := by decide +kernel
theorem atom1211Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (32845738161600 : Int) atom1211Coded) := by
  have h := atom1211_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1211Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1212 : SparsePolynomial.Poly := [([6,9,9], 1)]
theorem eval_atom1212 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1212 = ((g 6) * (g 9) * (g 9)) := by
  norm_num [atom1212, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1212_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1061671161600 : Int) atom1212) := by
  rw [SparsePolynomial.eval_scale, eval_atom1212]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1212Coded : CoefficientMerge.Poly := [(2844, 1)]
theorem atom1212Coded_decode : atom1212 = SparsePolynomial.decodeCubic 21 atom1212Coded := by decide +kernel
theorem atom1212Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1061671161600 : Int) atom1212Coded) := by
  have h := atom1212_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1212Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1213 : SparsePolynomial.Poly := [([6,9,10], 1)]
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
def atom1213Coded : CoefficientMerge.Poly := [(2845, 1)]
theorem atom1213Coded_decode : atom1213 = SparsePolynomial.decodeCubic 21 atom1213Coded := by decide +kernel
theorem atom1213Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (680402016000 : Int) atom1213Coded) := by
  have h := atom1213_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1213Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1214 : SparsePolynomial.Poly := [([6,9,11], 1)]
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
def atom1214Coded : CoefficientMerge.Poly := [(2846, 1)]
theorem atom1214Coded_decode : atom1214 = SparsePolynomial.decodeCubic 21 atom1214Coded := by decide +kernel
theorem atom1214Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (512236166400 : Int) atom1214Coded) := by
  have h := atom1214_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1214Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def atom1215 : SparsePolynomial.Poly := [([6,9,12], 1)]
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
def atom1215Coded : CoefficientMerge.Poly := [(2847, 1)]
theorem atom1215Coded_decode : atom1215 = SparsePolynomial.decodeCubic 21 atom1215Coded := by decide +kernel
theorem atom1215Coded_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) (CoefficientMerge.scale (1289278368000 : Int) atom1215Coded) := by
  have h := atom1215_nonneg g hg hA hB
  rw [SparsePolynomial.eval_scale, atom1215Coded_decode, SparsePolynomial.eval_decodeCubic] at h
  simpa only [CoefficientMerge.eval_scale] using h
def block016 : CoefficientMerge.Poly := [(2449, 20238042645504), (2450, 20278634402304), (2451, 29238383522304), (2452, 26787755370240), (2453, 39115299746304), (2454, 39724813792512), (2455, 48335988821760), (2456, 56947163851008), (2469, 13458536612352), (2470, 25686756405504), (2471, 25145532981504), (2472, 29937883845504), (2473, 29509938218240), (2474, 40443829119104), (2475, 41715097976512), (2476, 49283350901760), (2477, 57682924975008), (2491, 16376678929152), (2492, 30291619682304), (2493, 34213038813504), (2494, 32778158869440), (2495, 45968048642304), (2496, 48255838538112), (2497, 48971706384960), (2498, 63039466358208), (2513, 20331751940352), (2514, 38507308418304), (2515, 35927230083840), (2516, 53554841282304), (2517, 57013026832512), (2518, 52848874978560), (2519, 72684357715008), (2535, 26020396714752), (2536, 47998729798272), (2537, 69989670434304), (2538, 69826861415808), (2539, 49709608836480), (2540, 73705078859904), (2557, 18866969402112), (2558, 56352193854336), (2559, 58898327545152), (2560, 43714896386304), (2561, 50328202741536), (2579, 40369274295552), (2580, 63935689449600), (2581, 44823459653760), (2582, 50291511241152), (2601, 18599183925696), (2602, 23147791261632), (2603, 28126164973248), (2645, 3684923594208), (2778, 4122798220800), (2779, 7834685443200), (2780, 3472038057600), (2781, 427179916800), (2782, 343096992000), (2787, 4497994368000), (2800, 6459401491200), (2801, 5397730329600), (2805, 427179916800), (2806, 854359833600), (2807, 1281539750400), (2808, 8045165325312), (2811, 5465873347200), (2812, 10744058142720), (2813, 16910574206400), (2822, 2523934022400), (2826, 259014067200), (2827, 945208051200), (2828, 1631402035200), (2829, 9159807182400), (2830, 3879597682800), (2831, 7715012760000), (2832, 14815693494000), (2833, 23440111203600), (2834, 32845738161600), (2844, 1061671161600), (2845, 680402016000), (2846, 512236166400), (2847, 1289278368000)]
theorem block016_data : block016 = CoefficientMerge.trim (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20238042645504 : Int) atom1136Coded) (CoefficientMerge.scale (20278634402304 : Int) atom1137Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29238383522304 : Int) atom1138Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26787755370240 : Int) atom1139Coded) (CoefficientMerge.scale (39115299746304 : Int) atom1140Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (39724813792512 : Int) atom1141Coded) (CoefficientMerge.scale (48335988821760 : Int) atom1142Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (56947163851008 : Int) atom1143Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (13458536612352 : Int) atom1144Coded) (CoefficientMerge.scale (25686756405504 : Int) atom1145Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (25145532981504 : Int) atom1146Coded) (CoefficientMerge.scale (29937883845504 : Int) atom1147Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (29509938218240 : Int) atom1148Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40443829119104 : Int) atom1149Coded) (CoefficientMerge.scale (41715097976512 : Int) atom1150Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (49283350901760 : Int) atom1151Coded) (CoefficientMerge.scale (57682924975008 : Int) atom1152Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (16376678929152 : Int) atom1153Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (30291619682304 : Int) atom1154Coded) (CoefficientMerge.scale (34213038813504 : Int) atom1155Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32778158869440 : Int) atom1156Coded) (CoefficientMerge.scale (45968048642304 : Int) atom1157Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48255838538112 : Int) atom1158Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (48971706384960 : Int) atom1159Coded) (CoefficientMerge.scale (63039466358208 : Int) atom1160Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (20331751940352 : Int) atom1161Coded) (CoefficientMerge.scale (38507308418304 : Int) atom1162Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (35927230083840 : Int) atom1163Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (53554841282304 : Int) atom1164Coded) (CoefficientMerge.scale (57013026832512 : Int) atom1165Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (52848874978560 : Int) atom1166Coded) (CoefficientMerge.scale (72684357715008 : Int) atom1167Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (26020396714752 : Int) atom1168Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (47998729798272 : Int) atom1169Coded) (CoefficientMerge.scale (69989670434304 : Int) atom1170Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (69826861415808 : Int) atom1171Coded) (CoefficientMerge.scale (49709608836480 : Int) atom1172Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (73705078859904 : Int) atom1173Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18866969402112 : Int) atom1174Coded) (CoefficientMerge.scale (56352193854336 : Int) atom1175Coded))))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (58898327545152 : Int) atom1176Coded) (CoefficientMerge.scale (43714896386304 : Int) atom1177Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (50328202741536 : Int) atom1178Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (40369274295552 : Int) atom1179Coded) (CoefficientMerge.scale (63935689449600 : Int) atom1180Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (44823459653760 : Int) atom1181Coded) (CoefficientMerge.scale (50291511241152 : Int) atom1182Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (18599183925696 : Int) atom1183Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (23147791261632 : Int) atom1184Coded) (CoefficientMerge.scale (28126164973248 : Int) atom1185Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (3684923594208 : Int) atom1186Coded) (CoefficientMerge.scale (4122798220800 : Int) atom1187Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7834685443200 : Int) atom1188Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (3472038057600 : Int) atom1189Coded) (CoefficientMerge.scale (427179916800 : Int) atom1190Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (343096992000 : Int) atom1191Coded) (CoefficientMerge.scale (4497994368000 : Int) atom1192Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (6459401491200 : Int) atom1193Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5397730329600 : Int) atom1194Coded) (CoefficientMerge.scale (427179916800 : Int) atom1195Coded)))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (854359833600 : Int) atom1196Coded) (CoefficientMerge.scale (1281539750400 : Int) atom1197Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (8045165325312 : Int) atom1198Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (5465873347200 : Int) atom1199Coded) (CoefficientMerge.scale (10744058142720 : Int) atom1200Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (16910574206400 : Int) atom1201Coded) (CoefficientMerge.scale (2523934022400 : Int) atom1202Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (259014067200 : Int) atom1203Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (945208051200 : Int) atom1204Coded) (CoefficientMerge.scale (1631402035200 : Int) atom1205Coded))))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (9159807182400 : Int) atom1206Coded) (CoefficientMerge.scale (3879597682800 : Int) atom1207Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (7715012760000 : Int) atom1208Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (14815693494000 : Int) atom1209Coded) (CoefficientMerge.scale (23440111203600 : Int) atom1210Coded)))) (CoefficientMerge.fastMerge (CoefficientMerge.fastMerge (CoefficientMerge.scale (32845738161600 : Int) atom1211Coded) (CoefficientMerge.scale (1061671161600 : Int) atom1212Coded)) (CoefficientMerge.fastMerge (CoefficientMerge.scale (680402016000 : Int) atom1213Coded) (CoefficientMerge.fastMerge (CoefficientMerge.scale (512236166400 : Int) atom1214Coded) (CoefficientMerge.scale (1289278368000 : Int) atom1215Coded)))))))) := by decide +kernel
theorem block016_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ CoefficientMerge.eval (SparsePolynomial.cubeValue (gapValues g) 21) block016 := by
  rw [block016_data, CoefficientMerge.eval_trim]
  try simp only [CoefficientMerge.eval_fastMerge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1136Coded_nonneg g hg hA hB) (atom1137Coded_nonneg g hg hA hB)) (add_nonneg (atom1138Coded_nonneg g hg hA hB) (add_nonneg (atom1139Coded_nonneg g hg hA hB) (atom1140Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1141Coded_nonneg g hg hA hB) (atom1142Coded_nonneg g hg hA hB)) (add_nonneg (atom1143Coded_nonneg g hg hA hB) (add_nonneg (atom1144Coded_nonneg g hg hA hB) (atom1145Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1146Coded_nonneg g hg hA hB) (atom1147Coded_nonneg g hg hA hB)) (add_nonneg (atom1148Coded_nonneg g hg hA hB) (add_nonneg (atom1149Coded_nonneg g hg hA hB) (atom1150Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1151Coded_nonneg g hg hA hB) (atom1152Coded_nonneg g hg hA hB)) (add_nonneg (atom1153Coded_nonneg g hg hA hB) (add_nonneg (atom1154Coded_nonneg g hg hA hB) (atom1155Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1156Coded_nonneg g hg hA hB) (atom1157Coded_nonneg g hg hA hB)) (add_nonneg (atom1158Coded_nonneg g hg hA hB) (add_nonneg (atom1159Coded_nonneg g hg hA hB) (atom1160Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1161Coded_nonneg g hg hA hB) (atom1162Coded_nonneg g hg hA hB)) (add_nonneg (atom1163Coded_nonneg g hg hA hB) (add_nonneg (atom1164Coded_nonneg g hg hA hB) (atom1165Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1166Coded_nonneg g hg hA hB) (atom1167Coded_nonneg g hg hA hB)) (add_nonneg (atom1168Coded_nonneg g hg hA hB) (add_nonneg (atom1169Coded_nonneg g hg hA hB) (atom1170Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1171Coded_nonneg g hg hA hB) (atom1172Coded_nonneg g hg hA hB)) (add_nonneg (atom1173Coded_nonneg g hg hA hB) (add_nonneg (atom1174Coded_nonneg g hg hA hB) (atom1175Coded_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1176Coded_nonneg g hg hA hB) (atom1177Coded_nonneg g hg hA hB)) (add_nonneg (atom1178Coded_nonneg g hg hA hB) (add_nonneg (atom1179Coded_nonneg g hg hA hB) (atom1180Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1181Coded_nonneg g hg hA hB) (atom1182Coded_nonneg g hg hA hB)) (add_nonneg (atom1183Coded_nonneg g hg hA hB) (add_nonneg (atom1184Coded_nonneg g hg hA hB) (atom1185Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1186Coded_nonneg g hg hA hB) (atom1187Coded_nonneg g hg hA hB)) (add_nonneg (atom1188Coded_nonneg g hg hA hB) (add_nonneg (atom1189Coded_nonneg g hg hA hB) (atom1190Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1191Coded_nonneg g hg hA hB) (atom1192Coded_nonneg g hg hA hB)) (add_nonneg (atom1193Coded_nonneg g hg hA hB) (add_nonneg (atom1194Coded_nonneg g hg hA hB) (atom1195Coded_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1196Coded_nonneg g hg hA hB) (atom1197Coded_nonneg g hg hA hB)) (add_nonneg (atom1198Coded_nonneg g hg hA hB) (add_nonneg (atom1199Coded_nonneg g hg hA hB) (atom1200Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1201Coded_nonneg g hg hA hB) (atom1202Coded_nonneg g hg hA hB)) (add_nonneg (atom1203Coded_nonneg g hg hA hB) (add_nonneg (atom1204Coded_nonneg g hg hA hB) (atom1205Coded_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1206Coded_nonneg g hg hA hB) (atom1207Coded_nonneg g hg hA hB)) (add_nonneg (atom1208Coded_nonneg g hg hA hB) (add_nonneg (atom1209Coded_nonneg g hg hA hB) (atom1210Coded_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1211Coded_nonneg g hg hA hB) (atom1212Coded_nonneg g hg hA hB)) (add_nonneg (atom1213Coded_nonneg g hg hA hB) (add_nonneg (atom1214Coded_nonneg g hg hA hB) (atom1215Coded_nonneg g hg hA hB))))))))

end APPT.Finite21
