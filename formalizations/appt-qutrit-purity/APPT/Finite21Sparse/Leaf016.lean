import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1136 : SparsePolynomial.Poly := [([5,11,13], 1)]
theorem eval_atom1136 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1136 = ((g 5) * (g 11) * (g 13)) := by
  norm_num [atom1136, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1136_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20238042645504 : Int) atom1136) := by
  rw [SparsePolynomial.eval_scale, eval_atom1136]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1137 : SparsePolynomial.Poly := [([5,11,14], 1)]
theorem eval_atom1137 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1137 = ((g 5) * (g 11) * (g 14)) := by
  norm_num [atom1137, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1137_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20278634402304 : Int) atom1137) := by
  rw [SparsePolynomial.eval_scale, eval_atom1137]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1138 : SparsePolynomial.Poly := [([5,11,15], 1)]
theorem eval_atom1138 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1138 = ((g 5) * (g 11) * (g 15)) := by
  norm_num [atom1138, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1138_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (29238383522304 : Int) atom1138) := by
  rw [SparsePolynomial.eval_scale, eval_atom1138]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1139 : SparsePolynomial.Poly := [([5,11,16], 1)]
theorem eval_atom1139 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1139 = ((g 5) * (g 11) * (g 16)) := by
  norm_num [atom1139, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1139_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26787755370240 : Int) atom1139) := by
  rw [SparsePolynomial.eval_scale, eval_atom1139]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1140 : SparsePolynomial.Poly := [([5,11,17], 1)]
theorem eval_atom1140 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1140 = ((g 5) * (g 11) * (g 17)) := by
  norm_num [atom1140, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1140_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39115299746304 : Int) atom1140) := by
  rw [SparsePolynomial.eval_scale, eval_atom1140]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1141 : SparsePolynomial.Poly := [([5,11,18], 1)]
theorem eval_atom1141 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1141 = ((g 5) * (g 11) * (g 18)) := by
  norm_num [atom1141, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1141_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39724813792512 : Int) atom1141) := by
  rw [SparsePolynomial.eval_scale, eval_atom1141]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1142 : SparsePolynomial.Poly := [([5,11,19], 1)]
theorem eval_atom1142 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1142 = ((g 5) * (g 11) * (g 19)) := by
  norm_num [atom1142, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1142_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48335988821760 : Int) atom1142) := by
  rw [SparsePolynomial.eval_scale, eval_atom1142]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1143 : SparsePolynomial.Poly := [([5,11,20], 1)]
theorem eval_atom1143 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1143 = ((g 5) * (g 11) * (g 20)) := by
  norm_num [atom1143, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1143_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (56947163851008 : Int) atom1143) := by
  rw [SparsePolynomial.eval_scale, eval_atom1143]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1144 : SparsePolynomial.Poly := [([5,12,12], 1)]
theorem eval_atom1144 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1144 = ((g 5) * (g 12) * (g 12)) := by
  norm_num [atom1144, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1144_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13458536612352 : Int) atom1144) := by
  rw [SparsePolynomial.eval_scale, eval_atom1144]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1145 : SparsePolynomial.Poly := [([5,12,13], 1)]
theorem eval_atom1145 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1145 = ((g 5) * (g 12) * (g 13)) := by
  norm_num [atom1145, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1145_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25686756405504 : Int) atom1145) := by
  rw [SparsePolynomial.eval_scale, eval_atom1145]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1146 : SparsePolynomial.Poly := [([5,12,14], 1)]
theorem eval_atom1146 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1146 = ((g 5) * (g 12) * (g 14)) := by
  norm_num [atom1146, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1146_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25145532981504 : Int) atom1146) := by
  rw [SparsePolynomial.eval_scale, eval_atom1146]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1147 : SparsePolynomial.Poly := [([5,12,15], 1)]
theorem eval_atom1147 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1147 = ((g 5) * (g 12) * (g 15)) := by
  norm_num [atom1147, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1147_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (29937883845504 : Int) atom1147) := by
  rw [SparsePolynomial.eval_scale, eval_atom1147]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1148 : SparsePolynomial.Poly := [([5,12,16], 1)]
theorem eval_atom1148 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1148 = ((g 5) * (g 12) * (g 16)) := by
  norm_num [atom1148, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1148_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (29509938218240 : Int) atom1148) := by
  rw [SparsePolynomial.eval_scale, eval_atom1148]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1149 : SparsePolynomial.Poly := [([5,12,17], 1)]
theorem eval_atom1149 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1149 = ((g 5) * (g 12) * (g 17)) := by
  norm_num [atom1149, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1149_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40443829119104 : Int) atom1149) := by
  rw [SparsePolynomial.eval_scale, eval_atom1149]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1150 : SparsePolynomial.Poly := [([5,12,18], 1)]
theorem eval_atom1150 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1150 = ((g 5) * (g 12) * (g 18)) := by
  norm_num [atom1150, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1150_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41715097976512 : Int) atom1150) := by
  rw [SparsePolynomial.eval_scale, eval_atom1150]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1151 : SparsePolynomial.Poly := [([5,12,19], 1)]
theorem eval_atom1151 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1151 = ((g 5) * (g 12) * (g 19)) := by
  norm_num [atom1151, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1151_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (49283350901760 : Int) atom1151) := by
  rw [SparsePolynomial.eval_scale, eval_atom1151]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1152 : SparsePolynomial.Poly := [([5,12,20], 1)]
theorem eval_atom1152 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1152 = ((g 5) * (g 12) * (g 20)) := by
  norm_num [atom1152, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1152_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (57682924975008 : Int) atom1152) := by
  rw [SparsePolynomial.eval_scale, eval_atom1152]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1153 : SparsePolynomial.Poly := [([5,13,13], 1)]
theorem eval_atom1153 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1153 = ((g 5) * (g 13) * (g 13)) := by
  norm_num [atom1153, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1153_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16376678929152 : Int) atom1153) := by
  rw [SparsePolynomial.eval_scale, eval_atom1153]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1154 : SparsePolynomial.Poly := [([5,13,14], 1)]
theorem eval_atom1154 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1154 = ((g 5) * (g 13) * (g 14)) := by
  norm_num [atom1154, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1154_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30291619682304 : Int) atom1154) := by
  rw [SparsePolynomial.eval_scale, eval_atom1154]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1155 : SparsePolynomial.Poly := [([5,13,15], 1)]
theorem eval_atom1155 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1155 = ((g 5) * (g 13) * (g 15)) := by
  norm_num [atom1155, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1155_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34213038813504 : Int) atom1155) := by
  rw [SparsePolynomial.eval_scale, eval_atom1155]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1156 : SparsePolynomial.Poly := [([5,13,16], 1)]
theorem eval_atom1156 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1156 = ((g 5) * (g 13) * (g 16)) := by
  norm_num [atom1156, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1156_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (32778158869440 : Int) atom1156) := by
  rw [SparsePolynomial.eval_scale, eval_atom1156]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1157 : SparsePolynomial.Poly := [([5,13,17], 1)]
theorem eval_atom1157 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1157 = ((g 5) * (g 13) * (g 17)) := by
  norm_num [atom1157, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1157_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (45968048642304 : Int) atom1157) := by
  rw [SparsePolynomial.eval_scale, eval_atom1157]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1158 : SparsePolynomial.Poly := [([5,13,18], 1)]
theorem eval_atom1158 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1158 = ((g 5) * (g 13) * (g 18)) := by
  norm_num [atom1158, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1158_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48255838538112 : Int) atom1158) := by
  rw [SparsePolynomial.eval_scale, eval_atom1158]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1159 : SparsePolynomial.Poly := [([5,13,19], 1)]
theorem eval_atom1159 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1159 = ((g 5) * (g 13) * (g 19)) := by
  norm_num [atom1159, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1159_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48971706384960 : Int) atom1159) := by
  rw [SparsePolynomial.eval_scale, eval_atom1159]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1160 : SparsePolynomial.Poly := [([5,13,20], 1)]
theorem eval_atom1160 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1160 = ((g 5) * (g 13) * (g 20)) := by
  norm_num [atom1160, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1160_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (63039466358208 : Int) atom1160) := by
  rw [SparsePolynomial.eval_scale, eval_atom1160]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1161 : SparsePolynomial.Poly := [([5,14,14], 1)]
theorem eval_atom1161 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1161 = ((g 5) * (g 14) * (g 14)) := by
  norm_num [atom1161, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1161_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20331751940352 : Int) atom1161) := by
  rw [SparsePolynomial.eval_scale, eval_atom1161]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1162 : SparsePolynomial.Poly := [([5,14,15], 1)]
theorem eval_atom1162 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1162 = ((g 5) * (g 14) * (g 15)) := by
  norm_num [atom1162, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1162_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38507308418304 : Int) atom1162) := by
  rw [SparsePolynomial.eval_scale, eval_atom1162]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1163 : SparsePolynomial.Poly := [([5,14,16], 1)]
theorem eval_atom1163 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1163 = ((g 5) * (g 14) * (g 16)) := by
  norm_num [atom1163, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1163_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35927230083840 : Int) atom1163) := by
  rw [SparsePolynomial.eval_scale, eval_atom1163]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1164 : SparsePolynomial.Poly := [([5,14,17], 1)]
theorem eval_atom1164 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1164 = ((g 5) * (g 14) * (g 17)) := by
  norm_num [atom1164, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1164_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (53554841282304 : Int) atom1164) := by
  rw [SparsePolynomial.eval_scale, eval_atom1164]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1165 : SparsePolynomial.Poly := [([5,14,18], 1)]
theorem eval_atom1165 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1165 = ((g 5) * (g 14) * (g 18)) := by
  norm_num [atom1165, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1165_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (57013026832512 : Int) atom1165) := by
  rw [SparsePolynomial.eval_scale, eval_atom1165]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1166 : SparsePolynomial.Poly := [([5,14,19], 1)]
theorem eval_atom1166 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1166 = ((g 5) * (g 14) * (g 19)) := by
  norm_num [atom1166, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1166_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (52848874978560 : Int) atom1166) := by
  rw [SparsePolynomial.eval_scale, eval_atom1166]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1167 : SparsePolynomial.Poly := [([5,14,20], 1)]
theorem eval_atom1167 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1167 = ((g 5) * (g 14) * (g 20)) := by
  norm_num [atom1167, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1167_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (72684357715008 : Int) atom1167) := by
  rw [SparsePolynomial.eval_scale, eval_atom1167]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1168 : SparsePolynomial.Poly := [([5,15,15], 1)]
theorem eval_atom1168 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1168 = ((g 5) * (g 15) * (g 15)) := by
  norm_num [atom1168, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1168_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26020396714752 : Int) atom1168) := by
  rw [SparsePolynomial.eval_scale, eval_atom1168]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1169 : SparsePolynomial.Poly := [([5,15,16], 1)]
theorem eval_atom1169 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1169 = ((g 5) * (g 15) * (g 16)) := by
  norm_num [atom1169, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1169_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47998729798272 : Int) atom1169) := by
  rw [SparsePolynomial.eval_scale, eval_atom1169]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1170 : SparsePolynomial.Poly := [([5,15,17], 1)]
theorem eval_atom1170 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1170 = ((g 5) * (g 15) * (g 17)) := by
  norm_num [atom1170, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1170_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (69989670434304 : Int) atom1170) := by
  rw [SparsePolynomial.eval_scale, eval_atom1170]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1171 : SparsePolynomial.Poly := [([5,15,18], 1)]
theorem eval_atom1171 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1171 = ((g 5) * (g 15) * (g 18)) := by
  norm_num [atom1171, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1171_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (69826861415808 : Int) atom1171) := by
  rw [SparsePolynomial.eval_scale, eval_atom1171]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1172 : SparsePolynomial.Poly := [([5,15,19], 1)]
theorem eval_atom1172 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1172 = ((g 5) * (g 15) * (g 19)) := by
  norm_num [atom1172, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1172_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (49709608836480 : Int) atom1172) := by
  rw [SparsePolynomial.eval_scale, eval_atom1172]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1173 : SparsePolynomial.Poly := [([5,15,20], 1)]
theorem eval_atom1173 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1173 = ((g 5) * (g 15) * (g 20)) := by
  norm_num [atom1173, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1173_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (73705078859904 : Int) atom1173) := by
  rw [SparsePolynomial.eval_scale, eval_atom1173]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1174 : SparsePolynomial.Poly := [([5,16,16], 1)]
theorem eval_atom1174 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1174 = ((g 5) * (g 16) * (g 16)) := by
  norm_num [atom1174, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1174_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18866969402112 : Int) atom1174) := by
  rw [SparsePolynomial.eval_scale, eval_atom1174]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1175 : SparsePolynomial.Poly := [([5,16,17], 1)]
theorem eval_atom1175 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1175 = ((g 5) * (g 16) * (g 17)) := by
  norm_num [atom1175, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1175_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (56352193854336 : Int) atom1175) := by
  rw [SparsePolynomial.eval_scale, eval_atom1175]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1176 : SparsePolynomial.Poly := [([5,16,18], 1)]
theorem eval_atom1176 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1176 = ((g 5) * (g 16) * (g 18)) := by
  norm_num [atom1176, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1176_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (58898327545152 : Int) atom1176) := by
  rw [SparsePolynomial.eval_scale, eval_atom1176]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1177 : SparsePolynomial.Poly := [([5,16,19], 1)]
theorem eval_atom1177 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1177 = ((g 5) * (g 16) * (g 19)) := by
  norm_num [atom1177, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1177_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (43714896386304 : Int) atom1177) := by
  rw [SparsePolynomial.eval_scale, eval_atom1177]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1178 : SparsePolynomial.Poly := [([5,16,20], 1)]
theorem eval_atom1178 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1178 = ((g 5) * (g 16) * (g 20)) := by
  norm_num [atom1178, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1178_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (50328202741536 : Int) atom1178) := by
  rw [SparsePolynomial.eval_scale, eval_atom1178]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1179 : SparsePolynomial.Poly := [([5,17,17], 1)]
theorem eval_atom1179 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1179 = ((g 5) * (g 17) * (g 17)) := by
  norm_num [atom1179, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1179_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40369274295552 : Int) atom1179) := by
  rw [SparsePolynomial.eval_scale, eval_atom1179]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1180 : SparsePolynomial.Poly := [([5,17,18], 1)]
theorem eval_atom1180 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1180 = ((g 5) * (g 17) * (g 18)) := by
  norm_num [atom1180, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1180_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (63935689449600 : Int) atom1180) := by
  rw [SparsePolynomial.eval_scale, eval_atom1180]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1181 : SparsePolynomial.Poly := [([5,17,19], 1)]
theorem eval_atom1181 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1181 = ((g 5) * (g 17) * (g 19)) := by
  norm_num [atom1181, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1181_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (44823459653760 : Int) atom1181) := by
  rw [SparsePolynomial.eval_scale, eval_atom1181]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1182 : SparsePolynomial.Poly := [([5,17,20], 1)]
theorem eval_atom1182 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1182 = ((g 5) * (g 17) * (g 20)) := by
  norm_num [atom1182, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1182_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (50291511241152 : Int) atom1182) := by
  rw [SparsePolynomial.eval_scale, eval_atom1182]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1183 : SparsePolynomial.Poly := [([5,18,18], 1)]
theorem eval_atom1183 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1183 = ((g 5) * (g 18) * (g 18)) := by
  norm_num [atom1183, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1183_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18599183925696 : Int) atom1183) := by
  rw [SparsePolynomial.eval_scale, eval_atom1183]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1184 : SparsePolynomial.Poly := [([5,18,19], 1)]
theorem eval_atom1184 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1184 = ((g 5) * (g 18) * (g 19)) := by
  norm_num [atom1184, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1184_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23147791261632 : Int) atom1184) := by
  rw [SparsePolynomial.eval_scale, eval_atom1184]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1185 : SparsePolynomial.Poly := [([5,18,20], 1)]
theorem eval_atom1185 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1185 = ((g 5) * (g 18) * (g 20)) := by
  norm_num [atom1185, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1185_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28126164973248 : Int) atom1185) := by
  rw [SparsePolynomial.eval_scale, eval_atom1185]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1186 : SparsePolynomial.Poly := [([5,20,20], 1)]
theorem eval_atom1186 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1186 = ((g 5) * (g 20) * (g 20)) := by
  norm_num [atom1186, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1186_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3684923594208 : Int) atom1186) := by
  rw [SparsePolynomial.eval_scale, eval_atom1186]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1187 : SparsePolynomial.Poly := [([6,6,6], 1)]
theorem eval_atom1187 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1187 = ((g 6) * (g 6) * (g 6)) := by
  norm_num [atom1187, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1187_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4122798220800 : Int) atom1187) := by
  rw [SparsePolynomial.eval_scale, eval_atom1187]
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 6) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1188 : SparsePolynomial.Poly := [([6,6,7], 1)]
theorem eval_atom1188 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1188 = ((g 6) * (g 6) * (g 7)) := by
  norm_num [atom1188, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1188_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7834685443200 : Int) atom1188) := by
  rw [SparsePolynomial.eval_scale, eval_atom1188]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1189 : SparsePolynomial.Poly := [([6,6,8], 1)]
theorem eval_atom1189 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1189 = ((g 6) * (g 6) * (g 8)) := by
  norm_num [atom1189, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1189_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3472038057600 : Int) atom1189) := by
  rw [SparsePolynomial.eval_scale, eval_atom1189]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1190 : SparsePolynomial.Poly := [([6,6,9], 1)]
theorem eval_atom1190 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1190 = ((g 6) * (g 6) * (g 9)) := by
  norm_num [atom1190, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1190_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (427179916800 : Int) atom1190) := by
  rw [SparsePolynomial.eval_scale, eval_atom1190]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1191 : SparsePolynomial.Poly := [([6,6,10], 1)]
theorem eval_atom1191 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1191 = ((g 6) * (g 6) * (g 10)) := by
  norm_num [atom1191, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1191_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (343096992000 : Int) atom1191) := by
  rw [SparsePolynomial.eval_scale, eval_atom1191]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1192 : SparsePolynomial.Poly := [([6,6,15], 1)]
theorem eval_atom1192 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1192 = ((g 6) * (g 6) * (g 15)) := by
  norm_num [atom1192, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1192_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4497994368000 : Int) atom1192) := by
  rw [SparsePolynomial.eval_scale, eval_atom1192]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1193 : SparsePolynomial.Poly := [([6,7,7], 1)]
theorem eval_atom1193 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1193 = ((g 6) * (g 7) * (g 7)) := by
  norm_num [atom1193, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1193_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6459401491200 : Int) atom1193) := by
  rw [SparsePolynomial.eval_scale, eval_atom1193]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1194 : SparsePolynomial.Poly := [([6,7,8], 1)]
theorem eval_atom1194 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1194 = ((g 6) * (g 7) * (g 8)) := by
  norm_num [atom1194, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1194_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5397730329600 : Int) atom1194) := by
  rw [SparsePolynomial.eval_scale, eval_atom1194]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1195 : SparsePolynomial.Poly := [([6,7,12], 1)]
theorem eval_atom1195 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1195 = ((g 6) * (g 7) * (g 12)) := by
  norm_num [atom1195, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1195_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (427179916800 : Int) atom1195) := by
  rw [SparsePolynomial.eval_scale, eval_atom1195]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1196 : SparsePolynomial.Poly := [([6,7,13], 1)]
theorem eval_atom1196 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1196 = ((g 6) * (g 7) * (g 13)) := by
  norm_num [atom1196, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1196_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (854359833600 : Int) atom1196) := by
  rw [SparsePolynomial.eval_scale, eval_atom1196]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1197 : SparsePolynomial.Poly := [([6,7,14], 1)]
theorem eval_atom1197 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1197 = ((g 6) * (g 7) * (g 14)) := by
  norm_num [atom1197, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1197_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1281539750400 : Int) atom1197) := by
  rw [SparsePolynomial.eval_scale, eval_atom1197]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1198 : SparsePolynomial.Poly := [([6,7,15], 1)]
theorem eval_atom1198 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1198 = ((g 6) * (g 7) * (g 15)) := by
  norm_num [atom1198, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1198_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8045165325312 : Int) atom1198) := by
  rw [SparsePolynomial.eval_scale, eval_atom1198]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1199 : SparsePolynomial.Poly := [([6,7,18], 1)]
theorem eval_atom1199 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1199 = ((g 6) * (g 7) * (g 18)) := by
  norm_num [atom1199, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1199_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5465873347200 : Int) atom1199) := by
  rw [SparsePolynomial.eval_scale, eval_atom1199]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1200 : SparsePolynomial.Poly := [([6,7,19], 1)]
theorem eval_atom1200 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1200 = ((g 6) * (g 7) * (g 19)) := by
  norm_num [atom1200, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1200_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10744058142720 : Int) atom1200) := by
  rw [SparsePolynomial.eval_scale, eval_atom1200]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1201 : SparsePolynomial.Poly := [([6,7,20], 1)]
theorem eval_atom1201 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1201 = ((g 6) * (g 7) * (g 20)) := by
  norm_num [atom1201, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1201_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16910574206400 : Int) atom1201) := by
  rw [SparsePolynomial.eval_scale, eval_atom1201]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1202 : SparsePolynomial.Poly := [([6,8,8], 1)]
theorem eval_atom1202 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1202 = ((g 6) * (g 8) * (g 8)) := by
  norm_num [atom1202, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1202_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2523934022400 : Int) atom1202) := by
  rw [SparsePolynomial.eval_scale, eval_atom1202]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1203 : SparsePolynomial.Poly := [([6,8,12], 1)]
theorem eval_atom1203 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1203 = ((g 6) * (g 8) * (g 12)) := by
  norm_num [atom1203, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1203_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (259014067200 : Int) atom1203) := by
  rw [SparsePolynomial.eval_scale, eval_atom1203]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1204 : SparsePolynomial.Poly := [([6,8,13], 1)]
theorem eval_atom1204 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1204 = ((g 6) * (g 8) * (g 13)) := by
  norm_num [atom1204, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1204_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (945208051200 : Int) atom1204) := by
  rw [SparsePolynomial.eval_scale, eval_atom1204]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1205 : SparsePolynomial.Poly := [([6,8,14], 1)]
theorem eval_atom1205 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1205 = ((g 6) * (g 8) * (g 14)) := by
  norm_num [atom1205, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1205_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1631402035200 : Int) atom1205) := by
  rw [SparsePolynomial.eval_scale, eval_atom1205]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1206 : SparsePolynomial.Poly := [([6,8,15], 1)]
theorem eval_atom1206 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1206 = ((g 6) * (g 8) * (g 15)) := by
  norm_num [atom1206, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1206_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9159807182400 : Int) atom1206) := by
  rw [SparsePolynomial.eval_scale, eval_atom1206]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1207 : SparsePolynomial.Poly := [([6,8,16], 1)]
theorem eval_atom1207 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1207 = ((g 6) * (g 8) * (g 16)) := by
  norm_num [atom1207, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1207_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3879597682800 : Int) atom1207) := by
  rw [SparsePolynomial.eval_scale, eval_atom1207]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1208 : SparsePolynomial.Poly := [([6,8,17], 1)]
theorem eval_atom1208 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1208 = ((g 6) * (g 8) * (g 17)) := by
  norm_num [atom1208, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1208_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7715012760000 : Int) atom1208) := by
  rw [SparsePolynomial.eval_scale, eval_atom1208]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1209 : SparsePolynomial.Poly := [([6,8,18], 1)]
theorem eval_atom1209 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1209 = ((g 6) * (g 8) * (g 18)) := by
  norm_num [atom1209, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1209_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14815693494000 : Int) atom1209) := by
  rw [SparsePolynomial.eval_scale, eval_atom1209]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1210 : SparsePolynomial.Poly := [([6,8,19], 1)]
theorem eval_atom1210 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1210 = ((g 6) * (g 8) * (g 19)) := by
  norm_num [atom1210, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1210_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23440111203600 : Int) atom1210) := by
  rw [SparsePolynomial.eval_scale, eval_atom1210]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 6) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1211 : SparsePolynomial.Poly := [([6,8,20], 1)]
theorem eval_atom1211 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1211 = ((g 6) * (g 8) * (g 20)) := by
  norm_num [atom1211, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1211_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (32845738161600 : Int) atom1211) := by
  rw [SparsePolynomial.eval_scale, eval_atom1211]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 6) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1212 : SparsePolynomial.Poly := [([6,9,9], 1)]
theorem eval_atom1212 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1212 = ((g 6) * (g 9) * (g 9)) := by
  norm_num [atom1212, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1212_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1061671161600 : Int) atom1212) := by
  rw [SparsePolynomial.eval_scale, eval_atom1212]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1213 : SparsePolynomial.Poly := [([6,9,10], 1)]
theorem eval_atom1213 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1213 = ((g 6) * (g 9) * (g 10)) := by
  norm_num [atom1213, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1213_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (680402016000 : Int) atom1213) := by
  rw [SparsePolynomial.eval_scale, eval_atom1213]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1214 : SparsePolynomial.Poly := [([6,9,11], 1)]
theorem eval_atom1214 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1214 = ((g 6) * (g 9) * (g 11)) := by
  norm_num [atom1214, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1214_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (512236166400 : Int) atom1214) := by
  rw [SparsePolynomial.eval_scale, eval_atom1214]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1215 : SparsePolynomial.Poly := [([6,9,12], 1)]
theorem eval_atom1215 (g : Fin 21 → ℝ) : SparsePolynomial.eval (variables g) atom1215 = ((g 6) * (g 9) * (g 12)) := by
  norm_num [atom1215, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1215_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1289278368000 : Int) atom1215) := by
  rw [SparsePolynomial.eval_scale, eval_atom1215]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block016 : SparsePolynomial.Poly := [([5,11,13], 20238042645504), ([5,11,14], 20278634402304), ([5,11,15], 29238383522304), ([5,11,16], 26787755370240), ([5,11,17], 39115299746304), ([5,11,18], 39724813792512), ([5,11,19], 48335988821760), ([5,11,20], 56947163851008), ([5,12,12], 13458536612352), ([5,12,13], 25686756405504), ([5,12,14], 25145532981504), ([5,12,15], 29937883845504), ([5,12,16], 29509938218240), ([5,12,17], 40443829119104), ([5,12,18], 41715097976512), ([5,12,19], 49283350901760), ([5,12,20], 57682924975008), ([5,13,13], 16376678929152), ([5,13,14], 30291619682304), ([5,13,15], 34213038813504), ([5,13,16], 32778158869440), ([5,13,17], 45968048642304), ([5,13,18], 48255838538112), ([5,13,19], 48971706384960), ([5,13,20], 63039466358208), ([5,14,14], 20331751940352), ([5,14,15], 38507308418304), ([5,14,16], 35927230083840), ([5,14,17], 53554841282304), ([5,14,18], 57013026832512), ([5,14,19], 52848874978560), ([5,14,20], 72684357715008), ([5,15,15], 26020396714752), ([5,15,16], 47998729798272), ([5,15,17], 69989670434304), ([5,15,18], 69826861415808), ([5,15,19], 49709608836480), ([5,15,20], 73705078859904), ([5,16,16], 18866969402112), ([5,16,17], 56352193854336), ([5,16,18], 58898327545152), ([5,16,19], 43714896386304), ([5,16,20], 50328202741536), ([5,17,17], 40369274295552), ([5,17,18], 63935689449600), ([5,17,19], 44823459653760), ([5,17,20], 50291511241152), ([5,18,18], 18599183925696), ([5,18,19], 23147791261632), ([5,18,20], 28126164973248), ([5,20,20], 3684923594208), ([6,6,6], 4122798220800), ([6,6,7], 7834685443200), ([6,6,8], 3472038057600), ([6,6,9], 427179916800), ([6,6,10], 343096992000), ([6,6,15], 4497994368000), ([6,7,7], 6459401491200), ([6,7,8], 5397730329600), ([6,7,12], 427179916800), ([6,7,13], 854359833600), ([6,7,14], 1281539750400), ([6,7,15], 8045165325312), ([6,7,18], 5465873347200), ([6,7,19], 10744058142720), ([6,7,20], 16910574206400), ([6,8,8], 2523934022400), ([6,8,12], 259014067200), ([6,8,13], 945208051200), ([6,8,14], 1631402035200), ([6,8,15], 9159807182400), ([6,8,16], 3879597682800), ([6,8,17], 7715012760000), ([6,8,18], 14815693494000), ([6,8,19], 23440111203600), ([6,8,20], 32845738161600), ([6,9,9], 1061671161600), ([6,9,10], 680402016000), ([6,9,11], 512236166400), ([6,9,12], 1289278368000)]
theorem block016_data : block016 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (20238042645504 : Int) atom1136) (SparsePolynomial.scale (20278634402304 : Int) atom1137)) (SparsePolynomial.merge (SparsePolynomial.scale (29238383522304 : Int) atom1138) (SparsePolynomial.merge (SparsePolynomial.scale (26787755370240 : Int) atom1139) (SparsePolynomial.scale (39115299746304 : Int) atom1140)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (39724813792512 : Int) atom1141) (SparsePolynomial.scale (48335988821760 : Int) atom1142)) (SparsePolynomial.merge (SparsePolynomial.scale (56947163851008 : Int) atom1143) (SparsePolynomial.merge (SparsePolynomial.scale (13458536612352 : Int) atom1144) (SparsePolynomial.scale (25686756405504 : Int) atom1145))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (25145532981504 : Int) atom1146) (SparsePolynomial.scale (29937883845504 : Int) atom1147)) (SparsePolynomial.merge (SparsePolynomial.scale (29509938218240 : Int) atom1148) (SparsePolynomial.merge (SparsePolynomial.scale (40443829119104 : Int) atom1149) (SparsePolynomial.scale (41715097976512 : Int) atom1150)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (49283350901760 : Int) atom1151) (SparsePolynomial.scale (57682924975008 : Int) atom1152)) (SparsePolynomial.merge (SparsePolynomial.scale (16376678929152 : Int) atom1153) (SparsePolynomial.merge (SparsePolynomial.scale (30291619682304 : Int) atom1154) (SparsePolynomial.scale (34213038813504 : Int) atom1155)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (32778158869440 : Int) atom1156) (SparsePolynomial.scale (45968048642304 : Int) atom1157)) (SparsePolynomial.merge (SparsePolynomial.scale (48255838538112 : Int) atom1158) (SparsePolynomial.merge (SparsePolynomial.scale (48971706384960 : Int) atom1159) (SparsePolynomial.scale (63039466358208 : Int) atom1160)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (20331751940352 : Int) atom1161) (SparsePolynomial.scale (38507308418304 : Int) atom1162)) (SparsePolynomial.merge (SparsePolynomial.scale (35927230083840 : Int) atom1163) (SparsePolynomial.merge (SparsePolynomial.scale (53554841282304 : Int) atom1164) (SparsePolynomial.scale (57013026832512 : Int) atom1165))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (52848874978560 : Int) atom1166) (SparsePolynomial.scale (72684357715008 : Int) atom1167)) (SparsePolynomial.merge (SparsePolynomial.scale (26020396714752 : Int) atom1168) (SparsePolynomial.merge (SparsePolynomial.scale (47998729798272 : Int) atom1169) (SparsePolynomial.scale (69989670434304 : Int) atom1170)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (69826861415808 : Int) atom1171) (SparsePolynomial.scale (49709608836480 : Int) atom1172)) (SparsePolynomial.merge (SparsePolynomial.scale (73705078859904 : Int) atom1173) (SparsePolynomial.merge (SparsePolynomial.scale (18866969402112 : Int) atom1174) (SparsePolynomial.scale (56352193854336 : Int) atom1175))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (58898327545152 : Int) atom1176) (SparsePolynomial.scale (43714896386304 : Int) atom1177)) (SparsePolynomial.merge (SparsePolynomial.scale (50328202741536 : Int) atom1178) (SparsePolynomial.merge (SparsePolynomial.scale (40369274295552 : Int) atom1179) (SparsePolynomial.scale (63935689449600 : Int) atom1180)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (44823459653760 : Int) atom1181) (SparsePolynomial.scale (50291511241152 : Int) atom1182)) (SparsePolynomial.merge (SparsePolynomial.scale (18599183925696 : Int) atom1183) (SparsePolynomial.merge (SparsePolynomial.scale (23147791261632 : Int) atom1184) (SparsePolynomial.scale (28126164973248 : Int) atom1185))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3684923594208 : Int) atom1186) (SparsePolynomial.scale (4122798220800 : Int) atom1187)) (SparsePolynomial.merge (SparsePolynomial.scale (7834685443200 : Int) atom1188) (SparsePolynomial.merge (SparsePolynomial.scale (3472038057600 : Int) atom1189) (SparsePolynomial.scale (427179916800 : Int) atom1190)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (343096992000 : Int) atom1191) (SparsePolynomial.scale (4497994368000 : Int) atom1192)) (SparsePolynomial.merge (SparsePolynomial.scale (6459401491200 : Int) atom1193) (SparsePolynomial.merge (SparsePolynomial.scale (5397730329600 : Int) atom1194) (SparsePolynomial.scale (427179916800 : Int) atom1195)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (854359833600 : Int) atom1196) (SparsePolynomial.scale (1281539750400 : Int) atom1197)) (SparsePolynomial.merge (SparsePolynomial.scale (8045165325312 : Int) atom1198) (SparsePolynomial.merge (SparsePolynomial.scale (5465873347200 : Int) atom1199) (SparsePolynomial.scale (10744058142720 : Int) atom1200)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (16910574206400 : Int) atom1201) (SparsePolynomial.scale (2523934022400 : Int) atom1202)) (SparsePolynomial.merge (SparsePolynomial.scale (259014067200 : Int) atom1203) (SparsePolynomial.merge (SparsePolynomial.scale (945208051200 : Int) atom1204) (SparsePolynomial.scale (1631402035200 : Int) atom1205))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (9159807182400 : Int) atom1206) (SparsePolynomial.scale (3879597682800 : Int) atom1207)) (SparsePolynomial.merge (SparsePolynomial.scale (7715012760000 : Int) atom1208) (SparsePolynomial.merge (SparsePolynomial.scale (14815693494000 : Int) atom1209) (SparsePolynomial.scale (23440111203600 : Int) atom1210)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (32845738161600 : Int) atom1211) (SparsePolynomial.scale (1061671161600 : Int) atom1212)) (SparsePolynomial.merge (SparsePolynomial.scale (680402016000 : Int) atom1213) (SparsePolynomial.merge (SparsePolynomial.scale (512236166400 : Int) atom1214) (SparsePolynomial.scale (1289278368000 : Int) atom1215)))))))) := by decide +kernel
theorem block016_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block016 := by
  rw [block016_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1136_nonneg g hg hA hB) (atom1137_nonneg g hg hA hB)) (add_nonneg (atom1138_nonneg g hg hA hB) (add_nonneg (atom1139_nonneg g hg hA hB) (atom1140_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1141_nonneg g hg hA hB) (atom1142_nonneg g hg hA hB)) (add_nonneg (atom1143_nonneg g hg hA hB) (add_nonneg (atom1144_nonneg g hg hA hB) (atom1145_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1146_nonneg g hg hA hB) (atom1147_nonneg g hg hA hB)) (add_nonneg (atom1148_nonneg g hg hA hB) (add_nonneg (atom1149_nonneg g hg hA hB) (atom1150_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1151_nonneg g hg hA hB) (atom1152_nonneg g hg hA hB)) (add_nonneg (atom1153_nonneg g hg hA hB) (add_nonneg (atom1154_nonneg g hg hA hB) (atom1155_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1156_nonneg g hg hA hB) (atom1157_nonneg g hg hA hB)) (add_nonneg (atom1158_nonneg g hg hA hB) (add_nonneg (atom1159_nonneg g hg hA hB) (atom1160_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1161_nonneg g hg hA hB) (atom1162_nonneg g hg hA hB)) (add_nonneg (atom1163_nonneg g hg hA hB) (add_nonneg (atom1164_nonneg g hg hA hB) (atom1165_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1166_nonneg g hg hA hB) (atom1167_nonneg g hg hA hB)) (add_nonneg (atom1168_nonneg g hg hA hB) (add_nonneg (atom1169_nonneg g hg hA hB) (atom1170_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1171_nonneg g hg hA hB) (atom1172_nonneg g hg hA hB)) (add_nonneg (atom1173_nonneg g hg hA hB) (add_nonneg (atom1174_nonneg g hg hA hB) (atom1175_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1176_nonneg g hg hA hB) (atom1177_nonneg g hg hA hB)) (add_nonneg (atom1178_nonneg g hg hA hB) (add_nonneg (atom1179_nonneg g hg hA hB) (atom1180_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1181_nonneg g hg hA hB) (atom1182_nonneg g hg hA hB)) (add_nonneg (atom1183_nonneg g hg hA hB) (add_nonneg (atom1184_nonneg g hg hA hB) (atom1185_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1186_nonneg g hg hA hB) (atom1187_nonneg g hg hA hB)) (add_nonneg (atom1188_nonneg g hg hA hB) (add_nonneg (atom1189_nonneg g hg hA hB) (atom1190_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1191_nonneg g hg hA hB) (atom1192_nonneg g hg hA hB)) (add_nonneg (atom1193_nonneg g hg hA hB) (add_nonneg (atom1194_nonneg g hg hA hB) (atom1195_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1196_nonneg g hg hA hB) (atom1197_nonneg g hg hA hB)) (add_nonneg (atom1198_nonneg g hg hA hB) (add_nonneg (atom1199_nonneg g hg hA hB) (atom1200_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1201_nonneg g hg hA hB) (atom1202_nonneg g hg hA hB)) (add_nonneg (atom1203_nonneg g hg hA hB) (add_nonneg (atom1204_nonneg g hg hA hB) (atom1205_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1206_nonneg g hg hA hB) (atom1207_nonneg g hg hA hB)) (add_nonneg (atom1208_nonneg g hg hA hB) (add_nonneg (atom1209_nonneg g hg hA hB) (atom1210_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1211_nonneg g hg hA hB) (atom1212_nonneg g hg hA hB)) (add_nonneg (atom1213_nonneg g hg hA hB) (add_nonneg (atom1214_nonneg g hg hA hB) (atom1215_nonneg g hg hA hB))))))))

end APPT.Finite21
