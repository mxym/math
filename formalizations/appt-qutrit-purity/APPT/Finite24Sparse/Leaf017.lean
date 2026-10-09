import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1169 : SparsePolynomial.Poly := [([3,11,13], 1)]
theorem eval_atom1169 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1169 = ((g 3) * (g 11) * (g 13)) := by
  norm_num [atom1169, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1169_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (355486091647104 : Int) atom1169) := by
  rw [SparsePolynomial.eval_scale, eval_atom1169]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1170 : SparsePolynomial.Poly := [([3,11,14], 1)]
theorem eval_atom1170 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1170 = ((g 3) * (g 11) * (g 14)) := by
  norm_num [atom1170, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1170_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (329946779695104 : Int) atom1170) := by
  rw [SparsePolynomial.eval_scale, eval_atom1170]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1171 : SparsePolynomial.Poly := [([3,11,15], 1)]
theorem eval_atom1171 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1171 = ((g 3) * (g 11) * (g 15)) := by
  norm_num [atom1171, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1171_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (319194474338304 : Int) atom1171) := by
  rw [SparsePolynomial.eval_scale, eval_atom1171]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1172 : SparsePolynomial.Poly := [([3,11,16], 1)]
theorem eval_atom1172 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1172 = ((g 3) * (g 11) * (g 16)) := by
  norm_num [atom1172, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1172_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (299702699311104 : Int) atom1172) := by
  rw [SparsePolynomial.eval_scale, eval_atom1172]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1173 : SparsePolynomial.Poly := [([3,11,17], 1)]
theorem eval_atom1173 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1173 = ((g 3) * (g 11) * (g 17)) := by
  norm_num [atom1173, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1173_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (290143662741504 : Int) atom1173) := by
  rw [SparsePolynomial.eval_scale, eval_atom1173]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1174 : SparsePolynomial.Poly := [([3,11,18], 1)]
theorem eval_atom1174 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1174 = ((g 3) * (g 11) * (g 18)) := by
  norm_num [atom1174, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1174_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (337360560787008 : Int) atom1174) := by
  rw [SparsePolynomial.eval_scale, eval_atom1174]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1175 : SparsePolynomial.Poly := [([3,11,19], 1)]
theorem eval_atom1175 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1175 = ((g 3) * (g 11) * (g 19)) := by
  norm_num [atom1175, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1175_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (304119222359040 : Int) atom1175) := by
  rw [SparsePolynomial.eval_scale, eval_atom1175]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1176 : SparsePolynomial.Poly := [([3,11,20], 1)]
theorem eval_atom1176 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1176 = ((g 3) * (g 11) * (g 20)) := by
  norm_num [atom1176, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1176_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (377844072902208 : Int) atom1176) := by
  rw [SparsePolynomial.eval_scale, eval_atom1176]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1177 : SparsePolynomial.Poly := [([3,11,21], 1)]
theorem eval_atom1177 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1177 = ((g 3) * (g 11) * (g 21)) := by
  norm_num [atom1177, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1177_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (389393633958912 : Int) atom1177) := by
  rw [SparsePolynomial.eval_scale, eval_atom1177]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 11) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1178 : SparsePolynomial.Poly := [([3,11,22], 1)]
theorem eval_atom1178 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1178 = ((g 3) * (g 11) * (g 22)) := by
  norm_num [atom1178, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1178_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (447547332418560 : Int) atom1178) := by
  rw [SparsePolynomial.eval_scale, eval_atom1178]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 11) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1179 : SparsePolynomial.Poly := [([3,11,23], 1)]
theorem eval_atom1179 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1179 = ((g 3) * (g 11) * (g 23)) := by
  norm_num [atom1179, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1179_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (505701030878208 : Int) atom1179) := by
  rw [SparsePolynomial.eval_scale, eval_atom1179]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 11) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1180 : SparsePolynomial.Poly := [([3,12,12], 1)]
theorem eval_atom1180 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1180 = ((g 3) * (g 12) * (g 12)) := by
  norm_num [atom1180, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1180_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (230328777469824 : Int) atom1180) := by
  rw [SparsePolynomial.eval_scale, eval_atom1180]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1181 : SparsePolynomial.Poly := [([3,12,13], 1)]
theorem eval_atom1181 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1181 = ((g 3) * (g 12) * (g 13)) := by
  norm_num [atom1181, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1181_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (424979952465024 : Int) atom1181) := by
  rw [SparsePolynomial.eval_scale, eval_atom1181]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1182 : SparsePolynomial.Poly := [([3,12,14], 1)]
theorem eval_atom1182 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1182 = ((g 3) * (g 12) * (g 14)) := by
  norm_num [atom1182, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1182_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (397441979725824 : Int) atom1182) := by
  rw [SparsePolynomial.eval_scale, eval_atom1182]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1183 : SparsePolynomial.Poly := [([3,12,15], 1)]
theorem eval_atom1183 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1183 = ((g 3) * (g 12) * (g 15)) := by
  norm_num [atom1183, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1183_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (384691013581824 : Int) atom1183) := by
  rw [SparsePolynomial.eval_scale, eval_atom1183]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1184 : SparsePolynomial.Poly := [([3,12,16], 1)]
theorem eval_atom1184 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1184 = ((g 3) * (g 12) * (g 16)) := by
  norm_num [atom1184, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1184_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (360117537191424 : Int) atom1184) := by
  rw [SparsePolynomial.eval_scale, eval_atom1184]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1185 : SparsePolynomial.Poly := [([3,12,17], 1)]
theorem eval_atom1185 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1185 = ((g 3) * (g 12) * (g 17)) := by
  norm_num [atom1185, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1185_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (345476799258624 : Int) atom1185) := by
  rw [SparsePolynomial.eval_scale, eval_atom1185]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1186 : SparsePolynomial.Poly := [([3,12,18], 1)]
theorem eval_atom1186 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1186 = ((g 3) * (g 12) * (g 18)) := by
  norm_num [atom1186, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1186_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (413276182501248 : Int) atom1186) := by
  rw [SparsePolynomial.eval_scale, eval_atom1186]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1187 : SparsePolynomial.Poly := [([3,12,19], 1)]
theorem eval_atom1187 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1187 = ((g 3) * (g 12) * (g 19)) := by
  norm_num [atom1187, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1187_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (340052591831040 : Int) atom1187) := by
  rw [SparsePolynomial.eval_scale, eval_atom1187]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1188 : SparsePolynomial.Poly := [([3,12,20], 1)]
theorem eval_atom1188 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1188 = ((g 3) * (g 12) * (g 20)) := by
  norm_num [atom1188, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1188_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (461924436555648 : Int) atom1188) := by
  rw [SparsePolynomial.eval_scale, eval_atom1188]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1189 : SparsePolynomial.Poly := [([3,12,21], 1)]
theorem eval_atom1189 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1189 = ((g 3) * (g 12) * (g 21)) := by
  norm_num [atom1189, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1189_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (396690872067072 : Int) atom1189) := by
  rw [SparsePolynomial.eval_scale, eval_atom1189]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 12) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1190 : SparsePolynomial.Poly := [([3,12,22], 1)]
theorem eval_atom1190 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1190 = ((g 3) * (g 12) * (g 22)) := by
  norm_num [atom1190, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1190_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (437447716738560 : Int) atom1190) := by
  rw [SparsePolynomial.eval_scale, eval_atom1190]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 12) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1191 : SparsePolynomial.Poly := [([3,12,23], 1)]
theorem eval_atom1191 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1191 = ((g 3) * (g 12) * (g 23)) := by
  norm_num [atom1191, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1191_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (478204561410048 : Int) atom1191) := by
  rw [SparsePolynomial.eval_scale, eval_atom1191]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 12) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1192 : SparsePolynomial.Poly := [([3,13,13], 1)]
theorem eval_atom1192 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1192 = ((g 3) * (g 13) * (g 13)) := by
  norm_num [atom1192, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1192_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (238834335801600 : Int) atom1192) := by
  rw [SparsePolynomial.eval_scale, eval_atom1192]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1193 : SparsePolynomial.Poly := [([3,13,14], 1)]
theorem eval_atom1193 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1193 = ((g 3) * (g 13) * (g 14)) := by
  norm_num [atom1193, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1193_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (431701558041600 : Int) atom1193) := by
  rw [SparsePolynomial.eval_scale, eval_atom1193]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1194 : SparsePolynomial.Poly := [([3,13,15], 1)]
theorem eval_atom1194 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1194 = ((g 3) * (g 13) * (g 15)) := by
  norm_num [atom1194, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1194_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (409765257216000 : Int) atom1194) := by
  rw [SparsePolynomial.eval_scale, eval_atom1194]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1195 : SparsePolynomial.Poly := [([3,13,16], 1)]
theorem eval_atom1195 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1195 = ((g 3) * (g 13) * (g 16)) := by
  norm_num [atom1195, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1195_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (379089486720000 : Int) atom1195) := by
  rw [SparsePolynomial.eval_scale, eval_atom1195]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1196 : SparsePolynomial.Poly := [([3,13,17], 1)]
theorem eval_atom1196 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1196 = ((g 3) * (g 13) * (g 17)) := by
  norm_num [atom1196, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1196_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (358346454681600 : Int) atom1196) := by
  rw [SparsePolynomial.eval_scale, eval_atom1196]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1197 : SparsePolynomial.Poly := [([3,13,18], 1)]
theorem eval_atom1197 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1197 = ((g 3) * (g 13) * (g 18)) := by
  norm_num [atom1197, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1197_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (416025578707200 : Int) atom1197) := by
  rw [SparsePolynomial.eval_scale, eval_atom1197]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1198 : SparsePolynomial.Poly := [([3,13,19], 1)]
theorem eval_atom1198 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1198 = ((g 3) * (g 13) * (g 19)) := by
  norm_num [atom1198, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1198_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (345906104544000 : Int) atom1198) := by
  rw [SparsePolynomial.eval_scale, eval_atom1198]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1199 : SparsePolynomial.Poly := [([3,13,20], 1)]
theorem eval_atom1199 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1199 = ((g 3) * (g 13) * (g 20)) := by
  norm_num [atom1199, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1199_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (472838574700800 : Int) atom1199) := by
  rw [SparsePolynomial.eval_scale, eval_atom1199]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1200 : SparsePolynomial.Poly := [([3,13,21], 1)]
theorem eval_atom1200 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1200 = ((g 3) * (g 13) * (g 21)) := by
  norm_num [atom1200, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1200_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (400716687571200 : Int) atom1200) := by
  rw [SparsePolynomial.eval_scale, eval_atom1200]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 13) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1201 : SparsePolynomial.Poly := [([3,13,22], 1)]
theorem eval_atom1201 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1201 = ((g 3) * (g 13) * (g 22)) := by
  norm_num [atom1201, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1201_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (442289165472000 : Int) atom1201) := by
  rw [SparsePolynomial.eval_scale, eval_atom1201]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 13) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1202 : SparsePolynomial.Poly := [([3,13,23], 1)]
theorem eval_atom1202 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1202 = ((g 3) * (g 13) * (g 23)) := by
  norm_num [atom1202, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1202_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (483861643372800 : Int) atom1202) := by
  rw [SparsePolynomial.eval_scale, eval_atom1202]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 13) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1203 : SparsePolynomial.Poly := [([3,14,14], 1)]
theorem eval_atom1203 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1203 = ((g 3) * (g 14) * (g 14)) := by
  norm_num [atom1203, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1203_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (237050383046400 : Int) atom1203) := by
  rw [SparsePolynomial.eval_scale, eval_atom1203]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1204 : SparsePolynomial.Poly := [([3,14,15], 1)]
theorem eval_atom1204 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1204 = ((g 3) * (g 14) * (g 15)) := by
  norm_num [atom1204, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1204_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (439906721184000 : Int) atom1204) := by
  rw [SparsePolynomial.eval_scale, eval_atom1204]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1205 : SparsePolynomial.Poly := [([3,14,16], 1)]
theorem eval_atom1205 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1205 = ((g 3) * (g 14) * (g 16)) := by
  norm_num [atom1205, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1205_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (402108063840000 : Int) atom1205) := by
  rw [SparsePolynomial.eval_scale, eval_atom1205]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1206 : SparsePolynomial.Poly := [([3,14,17], 1)]
theorem eval_atom1206 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1206 = ((g 3) * (g 14) * (g 17)) := by
  norm_num [atom1206, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1206_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (374242144953600 : Int) atom1206) := by
  rw [SparsePolynomial.eval_scale, eval_atom1206]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1207 : SparsePolynomial.Poly := [([3,14,18], 1)]
theorem eval_atom1207 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1207 = ((g 3) * (g 14) * (g 18)) := by
  norm_num [atom1207, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1207_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (411426449280000 : Int) atom1207) := by
  rw [SparsePolynomial.eval_scale, eval_atom1207]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1208 : SparsePolynomial.Poly := [([3,14,19], 1)]
theorem eval_atom1208 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1208 = ((g 3) * (g 14) * (g 19)) := by
  norm_num [atom1208, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1208_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (350110707962400 : Int) atom1208) := by
  rw [SparsePolynomial.eval_scale, eval_atom1208]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1209 : SparsePolynomial.Poly := [([3,14,20], 1)]
theorem eval_atom1209 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1209 = ((g 3) * (g 14) * (g 20)) := by
  norm_num [atom1209, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1209_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (476404187212800 : Int) atom1209) := by
  rw [SparsePolynomial.eval_scale, eval_atom1209]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1210 : SparsePolynomial.Poly := [([3,14,21], 1)]
theorem eval_atom1210 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1210 = ((g 3) * (g 14) * (g 21)) := by
  norm_num [atom1210, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1210_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (408364671052800 : Int) atom1210) := by
  rw [SparsePolynomial.eval_scale, eval_atom1210]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 14) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1211 : SparsePolynomial.Poly := [([3,14,22], 1)]
theorem eval_atom1211 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1211 = ((g 3) * (g 14) * (g 22)) := by
  norm_num [atom1211, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1211_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (433640731154400 : Int) atom1211) := by
  rw [SparsePolynomial.eval_scale, eval_atom1211]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 14) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1212 : SparsePolynomial.Poly := [([3,14,23], 1)]
theorem eval_atom1212 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1212 = ((g 3) * (g 14) * (g 23)) := by
  norm_num [atom1212, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1212_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (471496571330400 : Int) atom1212) := by
  rw [SparsePolynomial.eval_scale, eval_atom1212]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 14) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1213 : SparsePolynomial.Poly := [([3,15,15], 1)]
theorem eval_atom1213 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1213 = ((g 3) * (g 15) * (g 15)) := by
  norm_num [atom1213, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1213_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (250122539520000 : Int) atom1213) := by
  rw [SparsePolynomial.eval_scale, eval_atom1213]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1214 : SparsePolynomial.Poly := [([3,15,16], 1)]
theorem eval_atom1214 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1214 = ((g 3) * (g 15) * (g 16)) := by
  norm_num [atom1214, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1214_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (440950187059200 : Int) atom1214) := by
  rw [SparsePolynomial.eval_scale, eval_atom1214]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1215 : SparsePolynomial.Poly := [([3,15,17], 1)]
theorem eval_atom1215 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1215 = ((g 3) * (g 15) * (g 17)) := by
  norm_num [atom1215, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1215_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (404940788582400 : Int) atom1215) := by
  rw [SparsePolynomial.eval_scale, eval_atom1215]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1216 : SparsePolynomial.Poly := [([3,15,18], 1)]
theorem eval_atom1216 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1216 = ((g 3) * (g 15) * (g 18)) := by
  norm_num [atom1216, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1216_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (436401333043200 : Int) atom1216) := by
  rw [SparsePolynomial.eval_scale, eval_atom1216]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1217 : SparsePolynomial.Poly := [([3,15,19], 1)]
theorem eval_atom1217 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1217 = ((g 3) * (g 15) * (g 19)) := by
  norm_num [atom1217, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1217_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (360026976153600 : Int) atom1217) := by
  rw [SparsePolynomial.eval_scale, eval_atom1217]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1218 : SparsePolynomial.Poly := [([3,15,20], 1)]
theorem eval_atom1218 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1218 = ((g 3) * (g 15) * (g 20)) := by
  norm_num [atom1218, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1218_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (509543812915200 : Int) atom1218) := by
  rw [SparsePolynomial.eval_scale, eval_atom1218]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1219 : SparsePolynomial.Poly := [([3,15,21], 1)]
theorem eval_atom1219 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1219 = ((g 3) * (g 15) * (g 21)) := by
  norm_num [atom1219, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1219_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (445586667724800 : Int) atom1219) := by
  rw [SparsePolynomial.eval_scale, eval_atom1219]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 15) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1220 : SparsePolynomial.Poly := [([3,15,22], 1)]
theorem eval_atom1220 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1220 = ((g 3) * (g 15) * (g 22)) := by
  norm_num [atom1220, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1220_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (404141839718400 : Int) atom1220) := by
  rw [SparsePolynomial.eval_scale, eval_atom1220]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 15) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1221 : SparsePolynomial.Poly := [([3,15,23], 1)]
theorem eval_atom1221 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1221 = ((g 3) * (g 15) * (g 23)) := by
  norm_num [atom1221, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1221_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (433071520358400 : Int) atom1221) := by
  rw [SparsePolynomial.eval_scale, eval_atom1221]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg15 : 0 ≤ g 15 := hg 15
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 15) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1222 : SparsePolynomial.Poly := [([3,16,16], 1)]
theorem eval_atom1222 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1222 = ((g 3) * (g 16) * (g 16)) := by
  norm_num [atom1222, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1222_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (241176889497600 : Int) atom1222) := by
  rw [SparsePolynomial.eval_scale, eval_atom1222]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1223 : SparsePolynomial.Poly := [([3,16,17], 1)]
theorem eval_atom1223 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1223 = ((g 3) * (g 16) * (g 17)) := by
  norm_num [atom1223, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1223_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (434097267609600 : Int) atom1223) := by
  rw [SparsePolynomial.eval_scale, eval_atom1223]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1224 : SparsePolynomial.Poly := [([3,16,18], 1)]
theorem eval_atom1224 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1224 = ((g 3) * (g 16) * (g 18)) := by
  norm_num [atom1224, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1224_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (437731196313600 : Int) atom1224) := by
  rw [SparsePolynomial.eval_scale, eval_atom1224]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1225 : SparsePolynomial.Poly := [([3,16,19], 1)]
theorem eval_atom1225 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1225 = ((g 3) * (g 16) * (g 19)) := by
  norm_num [atom1225, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1225_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (365439210393600 : Int) atom1225) := by
  rw [SparsePolynomial.eval_scale, eval_atom1225]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1226 : SparsePolynomial.Poly := [([3,16,20], 1)]
theorem eval_atom1226 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1226 = ((g 3) * (g 16) * (g 20)) := by
  norm_num [atom1226, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1226_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (519038418124800 : Int) atom1226) := by
  rw [SparsePolynomial.eval_scale, eval_atom1226]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1227 : SparsePolynomial.Poly := [([3,16,21], 1)]
theorem eval_atom1227 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1227 = ((g 3) * (g 16) * (g 21)) := by
  norm_num [atom1227, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1227_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (459163643904000 : Int) atom1227) := by
  rw [SparsePolynomial.eval_scale, eval_atom1227]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 16) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1228 : SparsePolynomial.Poly := [([3,16,22], 1)]
theorem eval_atom1228 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1228 = ((g 3) * (g 16) * (g 22)) := by
  norm_num [atom1228, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1228_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (364008189888000 : Int) atom1228) := by
  rw [SparsePolynomial.eval_scale, eval_atom1228]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 16) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1229 : SparsePolynomial.Poly := [([3,16,23], 1)]
theorem eval_atom1229 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1229 = ((g 3) * (g 16) * (g 23)) := by
  norm_num [atom1229, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1229_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (473555032473600 : Int) atom1229) := by
  rw [SparsePolynomial.eval_scale, eval_atom1229]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg16 : 0 ≤ g 16 := hg 16
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 16) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1230 : SparsePolynomial.Poly := [([3,17,17], 1)]
theorem eval_atom1230 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1230 = ((g 3) * (g 17) * (g 17)) := by
  norm_num [atom1230, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1230_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (238478504140800 : Int) atom1230) := by
  rw [SparsePolynomial.eval_scale, eval_atom1230]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1231 : SparsePolynomial.Poly := [([3,17,18], 1)]
theorem eval_atom1231 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1231 = ((g 3) * (g 17) * (g 18)) := by
  norm_num [atom1231, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1231_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (458926536499200 : Int) atom1231) := by
  rw [SparsePolynomial.eval_scale, eval_atom1231]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1232 : SparsePolynomial.Poly := [([3,17,19], 1)]
theorem eval_atom1232 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1232 = ((g 3) * (g 17) * (g 19)) := by
  norm_num [atom1232, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1232_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (390716921548800 : Int) atom1232) := by
  rw [SparsePolynomial.eval_scale, eval_atom1232]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1233 : SparsePolynomial.Poly := [([3,17,20], 1)]
theorem eval_atom1233 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1233 = ((g 3) * (g 17) * (g 20)) := by
  norm_num [atom1233, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1233_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (548398500249600 : Int) atom1233) := by
  rw [SparsePolynomial.eval_scale, eval_atom1233]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1234 : SparsePolynomial.Poly := [([3,17,21], 1)]
theorem eval_atom1234 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1234 = ((g 3) * (g 17) * (g 21)) := by
  norm_num [atom1234, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1234_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (492606096998400 : Int) atom1234) := by
  rw [SparsePolynomial.eval_scale, eval_atom1234]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 17) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1235 : SparsePolynomial.Poly := [([3,17,22], 1)]
theorem eval_atom1235 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1235 = ((g 3) * (g 17) * (g 22)) := by
  norm_num [atom1235, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1235_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (400409331033600 : Int) atom1235) := by
  rw [SparsePolynomial.eval_scale, eval_atom1235]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 17) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1236 : SparsePolynomial.Poly := [([3,17,23], 1)]
theorem eval_atom1236 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1236 = ((g 3) * (g 17) * (g 23)) := by
  norm_num [atom1236, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1236_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (514038544588800 : Int) atom1236) := by
  rw [SparsePolynomial.eval_scale, eval_atom1236]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg17 : 0 ≤ g 17 := hg 17
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 17) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1237 : SparsePolynomial.Poly := [([3,18,18], 1)]
theorem eval_atom1237 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1237 = ((g 3) * (g 18) * (g 18)) := by
  norm_num [atom1237, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1237_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (269691632179200 : Int) atom1237) := by
  rw [SparsePolynomial.eval_scale, eval_atom1237]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1238 : SparsePolynomial.Poly := [([3,18,19], 1)]
theorem eval_atom1238 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1238 = ((g 3) * (g 18) * (g 19)) := by
  norm_num [atom1238, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1238_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (461307919564800 : Int) atom1238) := by
  rw [SparsePolynomial.eval_scale, eval_atom1238]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1239 : SparsePolynomial.Poly := [([3,18,20], 1)]
theorem eval_atom1239 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1239 = ((g 3) * (g 18) * (g 20)) := by
  norm_num [atom1239, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1239_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (637019970048000 : Int) atom1239) := by
  rw [SparsePolynomial.eval_scale, eval_atom1239]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1240 : SparsePolynomial.Poly := [([3,18,21], 1)]
theorem eval_atom1240 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1240 = ((g 3) * (g 18) * (g 21)) := by
  norm_num [atom1240, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1240_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (565153231104000 : Int) atom1240) := by
  rw [SparsePolynomial.eval_scale, eval_atom1240]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 18) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1241 : SparsePolynomial.Poly := [([3,18,22], 1)]
theorem eval_atom1241 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1241 = ((g 3) * (g 18) * (g 22)) := by
  norm_num [atom1241, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1241_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (382207149676800 : Int) atom1241) := by
  rw [SparsePolynomial.eval_scale, eval_atom1241]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 18) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1242 : SparsePolynomial.Poly := [([3,18,23], 1)]
theorem eval_atom1242 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1242 = ((g 3) * (g 18) * (g 23)) := by
  norm_num [atom1242, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1242_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (528156744192000 : Int) atom1242) := by
  rw [SparsePolynomial.eval_scale, eval_atom1242]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg18 : 0 ≤ g 18 := hg 18
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 18) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1243 : SparsePolynomial.Poly := [([3,19,19], 1)]
theorem eval_atom1243 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1243 = ((g 3) * (g 19) * (g 19)) := by
  norm_num [atom1243, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1243_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (175133714595840 : Int) atom1243) := by
  rw [SparsePolynomial.eval_scale, eval_atom1243]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 19) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1244 : SparsePolynomial.Poly := [([3,19,20], 1)]
theorem eval_atom1244 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1244 = ((g 3) * (g 19) * (g 20)) := by
  norm_num [atom1244, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1244_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (510466469990400 : Int) atom1244) := by
  rw [SparsePolynomial.eval_scale, eval_atom1244]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1245 : SparsePolynomial.Poly := [([3,19,21], 1)]
theorem eval_atom1245 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1245 = ((g 3) * (g 19) * (g 21)) := by
  norm_num [atom1245, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1245_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (485972244172800 : Int) atom1245) := by
  rw [SparsePolynomial.eval_scale, eval_atom1245]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 19) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1246 : SparsePolynomial.Poly := [([3,19,22], 1)]
theorem eval_atom1246 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1246 = ((g 3) * (g 19) * (g 22)) := by
  norm_num [atom1246, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1246_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (349403855673600 : Int) atom1246) := by
  rw [SparsePolynomial.eval_scale, eval_atom1246]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 19) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1247 : SparsePolynomial.Poly := [([3,19,23], 1)]
theorem eval_atom1247 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1247 = ((g 3) * (g 19) * (g 23)) := by
  norm_num [atom1247, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1247_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (370049918515200 : Int) atom1247) := by
  rw [SparsePolynomial.eval_scale, eval_atom1247]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg19 : 0 ≤ g 19 := hg 19
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 19) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1248 : SparsePolynomial.Poly := [([3,20,20], 1)]
theorem eval_atom1248 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1248 = ((g 3) * (g 20) * (g 20)) := by
  norm_num [atom1248, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1248_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (346746384230400 : Int) atom1248) := by
  rw [SparsePolynomial.eval_scale, eval_atom1248]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block017 : SparsePolynomial.Poly := [([3,11,13], 355486091647104), ([3,11,14], 329946779695104), ([3,11,15], 319194474338304), ([3,11,16], 299702699311104), ([3,11,17], 290143662741504), ([3,11,18], 337360560787008), ([3,11,19], 304119222359040), ([3,11,20], 377844072902208), ([3,11,21], 389393633958912), ([3,11,22], 447547332418560), ([3,11,23], 505701030878208), ([3,12,12], 230328777469824), ([3,12,13], 424979952465024), ([3,12,14], 397441979725824), ([3,12,15], 384691013581824), ([3,12,16], 360117537191424), ([3,12,17], 345476799258624), ([3,12,18], 413276182501248), ([3,12,19], 340052591831040), ([3,12,20], 461924436555648), ([3,12,21], 396690872067072), ([3,12,22], 437447716738560), ([3,12,23], 478204561410048), ([3,13,13], 238834335801600), ([3,13,14], 431701558041600), ([3,13,15], 409765257216000), ([3,13,16], 379089486720000), ([3,13,17], 358346454681600), ([3,13,18], 416025578707200), ([3,13,19], 345906104544000), ([3,13,20], 472838574700800), ([3,13,21], 400716687571200), ([3,13,22], 442289165472000), ([3,13,23], 483861643372800), ([3,14,14], 237050383046400), ([3,14,15], 439906721184000), ([3,14,16], 402108063840000), ([3,14,17], 374242144953600), ([3,14,18], 411426449280000), ([3,14,19], 350110707962400), ([3,14,20], 476404187212800), ([3,14,21], 408364671052800), ([3,14,22], 433640731154400), ([3,14,23], 471496571330400), ([3,15,15], 250122539520000), ([3,15,16], 440950187059200), ([3,15,17], 404940788582400), ([3,15,18], 436401333043200), ([3,15,19], 360026976153600), ([3,15,20], 509543812915200), ([3,15,21], 445586667724800), ([3,15,22], 404141839718400), ([3,15,23], 433071520358400), ([3,16,16], 241176889497600), ([3,16,17], 434097267609600), ([3,16,18], 437731196313600), ([3,16,19], 365439210393600), ([3,16,20], 519038418124800), ([3,16,21], 459163643904000), ([3,16,22], 364008189888000), ([3,16,23], 473555032473600), ([3,17,17], 238478504140800), ([3,17,18], 458926536499200), ([3,17,19], 390716921548800), ([3,17,20], 548398500249600), ([3,17,21], 492606096998400), ([3,17,22], 400409331033600), ([3,17,23], 514038544588800), ([3,18,18], 269691632179200), ([3,18,19], 461307919564800), ([3,18,20], 637019970048000), ([3,18,21], 565153231104000), ([3,18,22], 382207149676800), ([3,18,23], 528156744192000), ([3,19,19], 175133714595840), ([3,19,20], 510466469990400), ([3,19,21], 485972244172800), ([3,19,22], 349403855673600), ([3,19,23], 370049918515200), ([3,20,20], 346746384230400)]
theorem block017_data : block017 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (355486091647104 : Int) atom1169) (SparsePolynomial.scale (329946779695104 : Int) atom1170)) (SparsePolynomial.merge (SparsePolynomial.scale (319194474338304 : Int) atom1171) (SparsePolynomial.merge (SparsePolynomial.scale (299702699311104 : Int) atom1172) (SparsePolynomial.scale (290143662741504 : Int) atom1173)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (337360560787008 : Int) atom1174) (SparsePolynomial.scale (304119222359040 : Int) atom1175)) (SparsePolynomial.merge (SparsePolynomial.scale (377844072902208 : Int) atom1176) (SparsePolynomial.merge (SparsePolynomial.scale (389393633958912 : Int) atom1177) (SparsePolynomial.scale (447547332418560 : Int) atom1178))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (505701030878208 : Int) atom1179) (SparsePolynomial.scale (230328777469824 : Int) atom1180)) (SparsePolynomial.merge (SparsePolynomial.scale (424979952465024 : Int) atom1181) (SparsePolynomial.merge (SparsePolynomial.scale (397441979725824 : Int) atom1182) (SparsePolynomial.scale (384691013581824 : Int) atom1183)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (360117537191424 : Int) atom1184) (SparsePolynomial.scale (345476799258624 : Int) atom1185)) (SparsePolynomial.merge (SparsePolynomial.scale (413276182501248 : Int) atom1186) (SparsePolynomial.merge (SparsePolynomial.scale (340052591831040 : Int) atom1187) (SparsePolynomial.scale (461924436555648 : Int) atom1188)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (396690872067072 : Int) atom1189) (SparsePolynomial.scale (437447716738560 : Int) atom1190)) (SparsePolynomial.merge (SparsePolynomial.scale (478204561410048 : Int) atom1191) (SparsePolynomial.merge (SparsePolynomial.scale (238834335801600 : Int) atom1192) (SparsePolynomial.scale (431701558041600 : Int) atom1193)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (409765257216000 : Int) atom1194) (SparsePolynomial.scale (379089486720000 : Int) atom1195)) (SparsePolynomial.merge (SparsePolynomial.scale (358346454681600 : Int) atom1196) (SparsePolynomial.merge (SparsePolynomial.scale (416025578707200 : Int) atom1197) (SparsePolynomial.scale (345906104544000 : Int) atom1198))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (472838574700800 : Int) atom1199) (SparsePolynomial.scale (400716687571200 : Int) atom1200)) (SparsePolynomial.merge (SparsePolynomial.scale (442289165472000 : Int) atom1201) (SparsePolynomial.merge (SparsePolynomial.scale (483861643372800 : Int) atom1202) (SparsePolynomial.scale (237050383046400 : Int) atom1203)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (439906721184000 : Int) atom1204) (SparsePolynomial.scale (402108063840000 : Int) atom1205)) (SparsePolynomial.merge (SparsePolynomial.scale (374242144953600 : Int) atom1206) (SparsePolynomial.merge (SparsePolynomial.scale (411426449280000 : Int) atom1207) (SparsePolynomial.scale (350110707962400 : Int) atom1208))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (476404187212800 : Int) atom1209) (SparsePolynomial.scale (408364671052800 : Int) atom1210)) (SparsePolynomial.merge (SparsePolynomial.scale (433640731154400 : Int) atom1211) (SparsePolynomial.merge (SparsePolynomial.scale (471496571330400 : Int) atom1212) (SparsePolynomial.scale (250122539520000 : Int) atom1213)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (440950187059200 : Int) atom1214) (SparsePolynomial.scale (404940788582400 : Int) atom1215)) (SparsePolynomial.merge (SparsePolynomial.scale (436401333043200 : Int) atom1216) (SparsePolynomial.merge (SparsePolynomial.scale (360026976153600 : Int) atom1217) (SparsePolynomial.scale (509543812915200 : Int) atom1218))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (445586667724800 : Int) atom1219) (SparsePolynomial.scale (404141839718400 : Int) atom1220)) (SparsePolynomial.merge (SparsePolynomial.scale (433071520358400 : Int) atom1221) (SparsePolynomial.merge (SparsePolynomial.scale (241176889497600 : Int) atom1222) (SparsePolynomial.scale (434097267609600 : Int) atom1223)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (437731196313600 : Int) atom1224) (SparsePolynomial.scale (365439210393600 : Int) atom1225)) (SparsePolynomial.merge (SparsePolynomial.scale (519038418124800 : Int) atom1226) (SparsePolynomial.merge (SparsePolynomial.scale (459163643904000 : Int) atom1227) (SparsePolynomial.scale (364008189888000 : Int) atom1228)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (473555032473600 : Int) atom1229) (SparsePolynomial.scale (238478504140800 : Int) atom1230)) (SparsePolynomial.merge (SparsePolynomial.scale (458926536499200 : Int) atom1231) (SparsePolynomial.merge (SparsePolynomial.scale (390716921548800 : Int) atom1232) (SparsePolynomial.scale (548398500249600 : Int) atom1233)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (492606096998400 : Int) atom1234) (SparsePolynomial.scale (400409331033600 : Int) atom1235)) (SparsePolynomial.merge (SparsePolynomial.scale (514038544588800 : Int) atom1236) (SparsePolynomial.merge (SparsePolynomial.scale (269691632179200 : Int) atom1237) (SparsePolynomial.scale (461307919564800 : Int) atom1238))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (637019970048000 : Int) atom1239) (SparsePolynomial.scale (565153231104000 : Int) atom1240)) (SparsePolynomial.merge (SparsePolynomial.scale (382207149676800 : Int) atom1241) (SparsePolynomial.merge (SparsePolynomial.scale (528156744192000 : Int) atom1242) (SparsePolynomial.scale (175133714595840 : Int) atom1243)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (510466469990400 : Int) atom1244) (SparsePolynomial.scale (485972244172800 : Int) atom1245)) (SparsePolynomial.merge (SparsePolynomial.scale (349403855673600 : Int) atom1246) (SparsePolynomial.merge (SparsePolynomial.scale (370049918515200 : Int) atom1247) (SparsePolynomial.scale (346746384230400 : Int) atom1248)))))))) := by decide +kernel
theorem block017_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block017 := by
  rw [block017_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1169_nonneg g hg hA hB) (atom1170_nonneg g hg hA hB)) (add_nonneg (atom1171_nonneg g hg hA hB) (add_nonneg (atom1172_nonneg g hg hA hB) (atom1173_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1174_nonneg g hg hA hB) (atom1175_nonneg g hg hA hB)) (add_nonneg (atom1176_nonneg g hg hA hB) (add_nonneg (atom1177_nonneg g hg hA hB) (atom1178_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1179_nonneg g hg hA hB) (atom1180_nonneg g hg hA hB)) (add_nonneg (atom1181_nonneg g hg hA hB) (add_nonneg (atom1182_nonneg g hg hA hB) (atom1183_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1184_nonneg g hg hA hB) (atom1185_nonneg g hg hA hB)) (add_nonneg (atom1186_nonneg g hg hA hB) (add_nonneg (atom1187_nonneg g hg hA hB) (atom1188_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1189_nonneg g hg hA hB) (atom1190_nonneg g hg hA hB)) (add_nonneg (atom1191_nonneg g hg hA hB) (add_nonneg (atom1192_nonneg g hg hA hB) (atom1193_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1194_nonneg g hg hA hB) (atom1195_nonneg g hg hA hB)) (add_nonneg (atom1196_nonneg g hg hA hB) (add_nonneg (atom1197_nonneg g hg hA hB) (atom1198_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1199_nonneg g hg hA hB) (atom1200_nonneg g hg hA hB)) (add_nonneg (atom1201_nonneg g hg hA hB) (add_nonneg (atom1202_nonneg g hg hA hB) (atom1203_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1204_nonneg g hg hA hB) (atom1205_nonneg g hg hA hB)) (add_nonneg (atom1206_nonneg g hg hA hB) (add_nonneg (atom1207_nonneg g hg hA hB) (atom1208_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1209_nonneg g hg hA hB) (atom1210_nonneg g hg hA hB)) (add_nonneg (atom1211_nonneg g hg hA hB) (add_nonneg (atom1212_nonneg g hg hA hB) (atom1213_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1214_nonneg g hg hA hB) (atom1215_nonneg g hg hA hB)) (add_nonneg (atom1216_nonneg g hg hA hB) (add_nonneg (atom1217_nonneg g hg hA hB) (atom1218_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1219_nonneg g hg hA hB) (atom1220_nonneg g hg hA hB)) (add_nonneg (atom1221_nonneg g hg hA hB) (add_nonneg (atom1222_nonneg g hg hA hB) (atom1223_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1224_nonneg g hg hA hB) (atom1225_nonneg g hg hA hB)) (add_nonneg (atom1226_nonneg g hg hA hB) (add_nonneg (atom1227_nonneg g hg hA hB) (atom1228_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1229_nonneg g hg hA hB) (atom1230_nonneg g hg hA hB)) (add_nonneg (atom1231_nonneg g hg hA hB) (add_nonneg (atom1232_nonneg g hg hA hB) (atom1233_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1234_nonneg g hg hA hB) (atom1235_nonneg g hg hA hB)) (add_nonneg (atom1236_nonneg g hg hA hB) (add_nonneg (atom1237_nonneg g hg hA hB) (atom1238_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1239_nonneg g hg hA hB) (atom1240_nonneg g hg hA hB)) (add_nonneg (atom1241_nonneg g hg hA hB) (add_nonneg (atom1242_nonneg g hg hA hB) (atom1243_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1244_nonneg g hg hA hB) (atom1245_nonneg g hg hA hB)) (add_nonneg (atom1246_nonneg g hg hA hB) (add_nonneg (atom1247_nonneg g hg hA hB) (atom1248_nonneg g hg hA hB))))))))

end APPT.Finite24
