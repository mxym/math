import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def atom0153 : SparsePolynomial.Poly := [([0,8,11], 1)]
theorem eval_atom0153 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0153 = ((g 0) * (g 8) * (g 11)) := by
  norm_num [atom0153, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0153_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (62330040 : Int) atom0153) := by
  rw [SparsePolynomial.eval_scale, eval_atom0153]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0154 : SparsePolynomial.Poly := [([0,8,12], 1)]
theorem eval_atom0154 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0154 = ((g 0) * (g 8) * (g 12)) := by
  norm_num [atom0154, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0154_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39342240 : Int) atom0154) := by
  rw [SparsePolynomial.eval_scale, eval_atom0154]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0155 : SparsePolynomial.Poly := [([0,8,13], 1)]
theorem eval_atom0155 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0155 = ((g 0) * (g 8) * (g 13)) := by
  norm_num [atom0155, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0155_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (33632280 : Int) atom0155) := by
  rw [SparsePolynomial.eval_scale, eval_atom0155]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0156 : SparsePolynomial.Poly := [([0,8,14], 1)]
theorem eval_atom0156 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0156 = ((g 0) * (g 8) * (g 14)) := by
  norm_num [atom0156, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0156_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17500320 : Int) atom0156) := by
  rw [SparsePolynomial.eval_scale, eval_atom0156]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0157 : SparsePolynomial.Poly := [([0,9,9], 1)]
theorem eval_atom0157 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0157 = ((g 0) * (g 9) * (g 9)) := by
  norm_num [atom0157, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0157_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (68653440 : Int) atom0157) := by
  rw [SparsePolynomial.eval_scale, eval_atom0157]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 0) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0158 : SparsePolynomial.Poly := [([0,9,10], 1)]
theorem eval_atom0158 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0158 = ((g 0) * (g 9) * (g 10)) := by
  norm_num [atom0158, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0158_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (117020160 : Int) atom0158) := by
  rw [SparsePolynomial.eval_scale, eval_atom0158]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0159 : SparsePolynomial.Poly := [([0,9,11], 1)]
theorem eval_atom0159 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0159 = ((g 0) * (g 9) * (g 11)) := by
  norm_num [atom0159, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0159_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (116705880 : Int) atom0159) := by
  rw [SparsePolynomial.eval_scale, eval_atom0159]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0160 : SparsePolynomial.Poly := [([0,9,12], 1)]
theorem eval_atom0160 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0160 = ((g 0) * (g 9) * (g 12)) := by
  norm_num [atom0160, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0160_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (103662720 : Int) atom0160) := by
  rw [SparsePolynomial.eval_scale, eval_atom0160]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0161 : SparsePolynomial.Poly := [([0,9,13], 1)]
theorem eval_atom0161 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0161 = ((g 0) * (g 9) * (g 13)) := by
  norm_num [atom0161, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0161_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (59244480 : Int) atom0161) := by
  rw [SparsePolynomial.eval_scale, eval_atom0161]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0162 : SparsePolynomial.Poly := [([0,9,14], 1)]
theorem eval_atom0162 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0162 = ((g 0) * (g 9) * (g 14)) := by
  norm_num [atom0162, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0162_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (64782720 : Int) atom0162) := by
  rw [SparsePolynomial.eval_scale, eval_atom0162]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0163 : SparsePolynomial.Poly := [([0,10,10], 1)]
theorem eval_atom0163 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0163 = ((g 0) * (g 10) * (g 10)) := by
  norm_num [atom0163, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0163_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (54801792 : Int) atom0163) := by
  rw [SparsePolynomial.eval_scale, eval_atom0163]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 0) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0164 : SparsePolynomial.Poly := [([0,10,11], 1)]
theorem eval_atom0164 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0164 = ((g 0) * (g 10) * (g 11)) := by
  norm_num [atom0164, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0164_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (101053440 : Int) atom0164) := by
  rw [SparsePolynomial.eval_scale, eval_atom0164]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0165 : SparsePolynomial.Poly := [([0,10,12], 1)]
theorem eval_atom0165 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0165 = ((g 0) * (g 10) * (g 12)) := by
  norm_num [atom0165, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0165_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (109175040 : Int) atom0165) := by
  rw [SparsePolynomial.eval_scale, eval_atom0165]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0166 : SparsePolynomial.Poly := [([0,10,13], 1)]
theorem eval_atom0166 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0166 = ((g 0) * (g 10) * (g 13)) := by
  norm_num [atom0166, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0166_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (63754560 : Int) atom0166) := by
  rw [SparsePolynomial.eval_scale, eval_atom0166]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0167 : SparsePolynomial.Poly := [([0,10,14], 1)]
theorem eval_atom0167 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0167 = ((g 0) * (g 10) * (g 14)) := by
  norm_num [atom0167, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0167_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (72679680 : Int) atom0167) := by
  rw [SparsePolynomial.eval_scale, eval_atom0167]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0168 : SparsePolynomial.Poly := [([0,11,11], 1)]
theorem eval_atom0168 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0168 = ((g 0) * (g 11) * (g 11)) := by
  norm_num [atom0168, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0168_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (52686720 : Int) atom0168) := by
  rw [SparsePolynomial.eval_scale, eval_atom0168]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 0) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0169 : SparsePolynomial.Poly := [([0,11,12], 1)]
theorem eval_atom0169 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0169 = ((g 0) * (g 11) * (g 12)) := by
  norm_num [atom0169, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0169_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (114687360 : Int) atom0169) := by
  rw [SparsePolynomial.eval_scale, eval_atom0169]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0170 : SparsePolynomial.Poly := [([0,11,13], 1)]
theorem eval_atom0170 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0170 = ((g 0) * (g 11) * (g 13)) := by
  norm_num [atom0170, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0170_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (66070080 : Int) atom0170) := by
  rw [SparsePolynomial.eval_scale, eval_atom0170]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0171 : SparsePolynomial.Poly := [([0,11,14], 1)]
theorem eval_atom0171 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0171 = ((g 0) * (g 11) * (g 14)) := by
  norm_num [atom0171, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0171_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (65093760 : Int) atom0171) := by
  rw [SparsePolynomial.eval_scale, eval_atom0171]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0172 : SparsePolynomial.Poly := [([0,12,12], 1)]
theorem eval_atom0172 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0172 = ((g 0) * (g 12) * (g 12)) := by
  norm_num [atom0172, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0172_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (60099840 : Int) atom0172) := by
  rw [SparsePolynomial.eval_scale, eval_atom0172]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 0) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0173 : SparsePolynomial.Poly := [([0,12,13], 1)]
theorem eval_atom0173 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0173 = ((g 0) * (g 12) * (g 13)) := by
  norm_num [atom0173, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0173_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (70580160 : Int) atom0173) := by
  rw [SparsePolynomial.eval_scale, eval_atom0173]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0174 : SparsePolynomial.Poly := [([0,12,14], 1)]
theorem eval_atom0174 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0174 = ((g 0) * (g 12) * (g 14)) := by
  norm_num [atom0174, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0174_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (72990720 : Int) atom0174) := by
  rw [SparsePolynomial.eval_scale, eval_atom0174]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0175 : SparsePolynomial.Poly := [([0,13,13], 1)]
theorem eval_atom0175 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0175 = ((g 0) * (g 13) * (g 13)) := by
  norm_num [atom0175, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0175_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6488640 : Int) atom0175) := by
  rw [SparsePolynomial.eval_scale, eval_atom0175]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 0) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0176 : SparsePolynomial.Poly := [([0,13,14], 1)]
theorem eval_atom0176 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0176 = ((g 0) * (g 13) * (g 14)) := by
  norm_num [atom0176, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0176_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10290240 : Int) atom0176) := by
  rw [SparsePolynomial.eval_scale, eval_atom0176]
  have hg0 : 0 ≤ g 0 := hg 0
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 0) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0177 : SparsePolynomial.Poly := [([1,1,1], 1)]
theorem eval_atom0177 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0177 = ((g 1) * (g 1) * (g 1)) := by
  norm_num [atom0177, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0177_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1827360 : Int) atom0177) := by
  rw [SparsePolynomial.eval_scale, eval_atom0177]
  have hg1 : 0 ≤ g 1 := hg 1
  have ht : 0 ≤ ((g 1) * (g 1) * (g 1)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0178 : SparsePolynomial.Poly := [([1,1,2], 1)]
theorem eval_atom0178 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0178 = ((g 1) * (g 1) * (g 2)) := by
  norm_num [atom0178, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0178_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13046400 : Int) atom0178) := by
  rw [SparsePolynomial.eval_scale, eval_atom0178]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 1) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0179 : SparsePolynomial.Poly := [([1,1,3], 1)]
theorem eval_atom0179 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0179 = ((g 1) * (g 1) * (g 3)) := by
  norm_num [atom0179, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0179_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10437120 : Int) atom0179) := by
  rw [SparsePolynomial.eval_scale, eval_atom0179]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 1) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0180 : SparsePolynomial.Poly := [([1,1,4], 1)]
theorem eval_atom0180 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0180 = ((g 1) * (g 1) * (g 4)) := by
  norm_num [atom0180, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0180_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7827840 : Int) atom0180) := by
  rw [SparsePolynomial.eval_scale, eval_atom0180]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 1) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0181 : SparsePolynomial.Poly := [([1,1,5], 1)]
theorem eval_atom0181 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0181 = ((g 1) * (g 1) * (g 5)) := by
  norm_num [atom0181, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0181_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5218560 : Int) atom0181) := by
  rw [SparsePolynomial.eval_scale, eval_atom0181]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 1) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0182 : SparsePolynomial.Poly := [([1,1,6], 1)]
theorem eval_atom0182 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0182 = ((g 1) * (g 1) * (g 6)) := by
  norm_num [atom0182, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0182_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2609280 : Int) atom0182) := by
  rw [SparsePolynomial.eval_scale, eval_atom0182]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 1) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0183 : SparsePolynomial.Poly := [([1,1,9], 1)]
theorem eval_atom0183 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0183 = ((g 1) * (g 1) * (g 9)) := by
  norm_num [atom0183, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0183_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20293200 : Int) atom0183) := by
  rw [SparsePolynomial.eval_scale, eval_atom0183]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 1) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0184 : SparsePolynomial.Poly := [([1,2,2], 1)]
theorem eval_atom0184 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0184 = ((g 1) * (g 2) * (g 2)) := by
  norm_num [atom0184, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0184_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20217600 : Int) atom0184) := by
  rw [SparsePolynomial.eval_scale, eval_atom0184]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 1) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0185 : SparsePolynomial.Poly := [([1,2,3], 1)]
theorem eval_atom0185 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0185 = ((g 1) * (g 2) * (g 3)) := by
  norm_num [atom0185, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0185_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (37601280 : Int) atom0185) := by
  rw [SparsePolynomial.eval_scale, eval_atom0185]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0186 : SparsePolynomial.Poly := [([1,2,4], 1)]
theorem eval_atom0186 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0186 = ((g 1) * (g 2) * (g 4)) := by
  norm_num [atom0186, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0186_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34767360 : Int) atom0186) := by
  rw [SparsePolynomial.eval_scale, eval_atom0186]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0187 : SparsePolynomial.Poly := [([1,2,5], 1)]
theorem eval_atom0187 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0187 = ((g 1) * (g 2) * (g 5)) := by
  norm_num [atom0187, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0187_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31933440 : Int) atom0187) := by
  rw [SparsePolynomial.eval_scale, eval_atom0187]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0188 : SparsePolynomial.Poly := [([1,2,6], 1)]
theorem eval_atom0188 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0188 = ((g 1) * (g 2) * (g 6)) := by
  norm_num [atom0188, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0188_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (29099520 : Int) atom0188) := by
  rw [SparsePolynomial.eval_scale, eval_atom0188]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0189 : SparsePolynomial.Poly := [([1,2,7], 1)]
theorem eval_atom0189 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0189 = ((g 1) * (g 2) * (g 7)) := by
  norm_num [atom0189, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0189_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26265600 : Int) atom0189) := by
  rw [SparsePolynomial.eval_scale, eval_atom0189]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0190 : SparsePolynomial.Poly := [([1,2,8], 1)]
theorem eval_atom0190 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0190 = ((g 1) * (g 2) * (g 8)) := by
  norm_num [atom0190, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0190_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26910720 : Int) atom0190) := by
  rw [SparsePolynomial.eval_scale, eval_atom0190]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0191 : SparsePolynomial.Poly := [([1,2,9], 1)]
theorem eval_atom0191 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0191 = ((g 1) * (g 2) * (g 9)) := by
  norm_num [atom0191, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0191_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (75029760 : Int) atom0191) := by
  rw [SparsePolynomial.eval_scale, eval_atom0191]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0192 : SparsePolynomial.Poly := [([1,2,10], 1)]
theorem eval_atom0192 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0192 = ((g 1) * (g 2) * (g 10)) := by
  norm_num [atom0192, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0192_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (35017920 : Int) atom0192) := by
  rw [SparsePolynomial.eval_scale, eval_atom0192]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0193 : SparsePolynomial.Poly := [([1,2,11], 1)]
theorem eval_atom0193 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0193 = ((g 1) * (g 2) * (g 11)) := by
  norm_num [atom0193, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0193_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47631240 : Int) atom0193) := by
  rw [SparsePolynomial.eval_scale, eval_atom0193]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0194 : SparsePolynomial.Poly := [([1,2,12], 1)]
theorem eval_atom0194 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0194 = ((g 1) * (g 2) * (g 12)) := by
  norm_num [atom0194, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0194_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40870080 : Int) atom0194) := by
  rw [SparsePolynomial.eval_scale, eval_atom0194]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0195 : SparsePolynomial.Poly := [([1,2,13], 1)]
theorem eval_atom0195 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0195 = ((g 1) * (g 2) * (g 13)) := by
  norm_num [atom0195, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0195_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (33523200 : Int) atom0195) := by
  rw [SparsePolynomial.eval_scale, eval_atom0195]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 2) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0196 : SparsePolynomial.Poly := [([1,2,14], 1)]
theorem eval_atom0196 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0196 = ((g 1) * (g 2) * (g 14)) := by
  norm_num [atom0196, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0196_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39453840 : Int) atom0196) := by
  rw [SparsePolynomial.eval_scale, eval_atom0196]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0197 : SparsePolynomial.Poly := [([1,3,3], 1)]
theorem eval_atom0197 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0197 = ((g 1) * (g 3) * (g 3)) := by
  norm_num [atom0197, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0197_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14631840 : Int) atom0197) := by
  rw [SparsePolynomial.eval_scale, eval_atom0197]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 1) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0198 : SparsePolynomial.Poly := [([1,3,4], 1)]
theorem eval_atom0198 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0198 = ((g 1) * (g 3) * (g 4)) := by
  norm_num [atom0198, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0198_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26714880 : Int) atom0198) := by
  rw [SparsePolynomial.eval_scale, eval_atom0198]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0199 : SparsePolynomial.Poly := [([1,3,5], 1)]
theorem eval_atom0199 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0199 = ((g 1) * (g 3) * (g 5)) := by
  norm_num [atom0199, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0199_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26265600 : Int) atom0199) := by
  rw [SparsePolynomial.eval_scale, eval_atom0199]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0200 : SparsePolynomial.Poly := [([1,3,6], 1)]
theorem eval_atom0200 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0200 = ((g 1) * (g 3) * (g 6)) := by
  norm_num [atom0200, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0200_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25816320 : Int) atom0200) := by
  rw [SparsePolynomial.eval_scale, eval_atom0200]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0201 : SparsePolynomial.Poly := [([1,3,7], 1)]
theorem eval_atom0201 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0201 = ((g 1) * (g 3) * (g 7)) := by
  norm_num [atom0201, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0201_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25591680 : Int) atom0201) := by
  rw [SparsePolynomial.eval_scale, eval_atom0201]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0202 : SparsePolynomial.Poly := [([1,3,8], 1)]
theorem eval_atom0202 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0202 = ((g 1) * (g 3) * (g 8)) := by
  norm_num [atom0202, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0202_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28846080 : Int) atom0202) := by
  rw [SparsePolynomial.eval_scale, eval_atom0202]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0203 : SparsePolynomial.Poly := [([1,3,9], 1)]
theorem eval_atom0203 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0203 = ((g 1) * (g 3) * (g 9)) := by
  norm_num [atom0203, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0203_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (78900480 : Int) atom0203) := by
  rw [SparsePolynomial.eval_scale, eval_atom0203]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0204 : SparsePolynomial.Poly := [([1,3,10], 1)]
theorem eval_atom0204 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0204 = ((g 1) * (g 3) * (g 10)) := by
  norm_num [atom0204, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0204_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (42434280 : Int) atom0204) := by
  rw [SparsePolynomial.eval_scale, eval_atom0204]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0205 : SparsePolynomial.Poly := [([1,3,11], 1)]
theorem eval_atom0205 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0205 = ((g 1) * (g 3) * (g 11)) := by
  norm_num [atom0205, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0205_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (56271240 : Int) atom0205) := by
  rw [SparsePolynomial.eval_scale, eval_atom0205]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0206 : SparsePolynomial.Poly := [([1,3,12], 1)]
theorem eval_atom0206 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0206 = ((g 1) * (g 3) * (g 12)) := by
  norm_num [atom0206, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0206_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (54029880 : Int) atom0206) := by
  rw [SparsePolynomial.eval_scale, eval_atom0206]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0207 : SparsePolynomial.Poly := [([1,3,13], 1)]
theorem eval_atom0207 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0207 = ((g 1) * (g 3) * (g 13)) := by
  norm_num [atom0207, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0207_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (53115480 : Int) atom0207) := by
  rw [SparsePolynomial.eval_scale, eval_atom0207]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0208 : SparsePolynomial.Poly := [([1,3,14], 1)]
theorem eval_atom0208 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0208 = ((g 1) * (g 3) * (g 14)) := by
  norm_num [atom0208, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0208_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (52201080 : Int) atom0208) := by
  rw [SparsePolynomial.eval_scale, eval_atom0208]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0209 : SparsePolynomial.Poly := [([1,4,4], 1)]
theorem eval_atom0209 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0209 = ((g 1) * (g 4) * (g 4)) := by
  norm_num [atom0209, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0209_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19306080 : Int) atom0209) := by
  rw [SparsePolynomial.eval_scale, eval_atom0209]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 1) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0210 : SparsePolynomial.Poly := [([1,4,5], 1)]
theorem eval_atom0210 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0210 = ((g 1) * (g 4) * (g 5)) := by
  norm_num [atom0210, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0210_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28290240 : Int) atom0210) := by
  rw [SparsePolynomial.eval_scale, eval_atom0210]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0211 : SparsePolynomial.Poly := [([1,4,6], 1)]
theorem eval_atom0211 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0211 = ((g 1) * (g 4) * (g 6)) := by
  norm_num [atom0211, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0211_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (29016000 : Int) atom0211) := by
  rw [SparsePolynomial.eval_scale, eval_atom0211]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0212 : SparsePolynomial.Poly := [([1,4,7], 1)]
theorem eval_atom0212 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0212 = ((g 1) * (g 4) * (g 7)) := by
  norm_num [atom0212, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0212_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (29741760 : Int) atom0212) := by
  rw [SparsePolynomial.eval_scale, eval_atom0212]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0213 : SparsePolynomial.Poly := [([1,4,8], 1)]
theorem eval_atom0213 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0213 = ((g 1) * (g 4) * (g 8)) := by
  norm_num [atom0213, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0213_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (33946560 : Int) atom0213) := by
  rw [SparsePolynomial.eval_scale, eval_atom0213]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0214 : SparsePolynomial.Poly := [([1,4,9], 1)]
theorem eval_atom0214 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0214 = ((g 1) * (g 4) * (g 9)) := by
  norm_num [atom0214, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0214_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (82771200 : Int) atom0214) := by
  rw [SparsePolynomial.eval_scale, eval_atom0214]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0215 : SparsePolynomial.Poly := [([1,4,10], 1)]
theorem eval_atom0215 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0215 = ((g 1) * (g 4) * (g 10)) := by
  norm_num [atom0215, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0215_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (51666840 : Int) atom0215) := by
  rw [SparsePolynomial.eval_scale, eval_atom0215]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0216 : SparsePolynomial.Poly := [([1,4,11], 1)]
theorem eval_atom0216 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0216 = ((g 1) * (g 4) * (g 11)) := by
  norm_num [atom0216, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0216_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (64911240 : Int) atom0216) := by
  rw [SparsePolynomial.eval_scale, eval_atom0216]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0217 : SparsePolynomial.Poly := [([1,4,12], 1)]
theorem eval_atom0217 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0217 = ((g 1) * (g 4) * (g 12)) := by
  norm_num [atom0217, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0217_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (69625800 : Int) atom0217) := by
  rw [SparsePolynomial.eval_scale, eval_atom0217]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0218 : SparsePolynomial.Poly := [([1,4,13], 1)]
theorem eval_atom0218 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0218 = ((g 1) * (g 4) * (g 13)) := by
  norm_num [atom0218, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0218_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (72636840 : Int) atom0218) := by
  rw [SparsePolynomial.eval_scale, eval_atom0218]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0219 : SparsePolynomial.Poly := [([1,4,14], 1)]
theorem eval_atom0219 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0219 = ((g 1) * (g 4) * (g 14)) := by
  norm_num [atom0219, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0219_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (75647880 : Int) atom0219) := by
  rw [SparsePolynomial.eval_scale, eval_atom0219]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0220 : SparsePolynomial.Poly := [([1,5,5], 1)]
theorem eval_atom0220 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0220 = ((g 1) * (g 5) * (g 5)) := by
  norm_num [atom0220, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0220_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22753440 : Int) atom0220) := by
  rw [SparsePolynomial.eval_scale, eval_atom0220]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 1) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0221 : SparsePolynomial.Poly := [([1,5,6], 1)]
theorem eval_atom0221 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0221 = ((g 1) * (g 5) * (g 6)) := by
  norm_num [atom0221, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0221_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36922752 : Int) atom0221) := by
  rw [SparsePolynomial.eval_scale, eval_atom0221]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0222 : SparsePolynomial.Poly := [([1,5,7], 1)]
theorem eval_atom0222 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0222 = ((g 1) * (g 5) * (g 7)) := by
  norm_num [atom0222, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0222_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36524160 : Int) atom0222) := by
  rw [SparsePolynomial.eval_scale, eval_atom0222]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0223 : SparsePolynomial.Poly := [([1,5,8], 1)]
theorem eval_atom0223 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0223 = ((g 1) * (g 5) * (g 8)) := by
  norm_num [atom0223, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0223_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41083200 : Int) atom0223) := by
  rw [SparsePolynomial.eval_scale, eval_atom0223]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0224 : SparsePolynomial.Poly := [([1,5,9], 1)]
theorem eval_atom0224 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0224 = ((g 1) * (g 5) * (g 9)) := by
  norm_num [atom0224, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0224_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (86641920 : Int) atom0224) := by
  rw [SparsePolynomial.eval_scale, eval_atom0224]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0225 : SparsePolynomial.Poly := [([1,5,10], 1)]
theorem eval_atom0225 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0225 = ((g 1) * (g 5) * (g 10)) := by
  norm_num [atom0225, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0225_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (60840360 : Int) atom0225) := by
  rw [SparsePolynomial.eval_scale, eval_atom0225]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0226 : SparsePolynomial.Poly := [([1,5,11], 1)]
theorem eval_atom0226 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0226 = ((g 1) * (g 5) * (g 11)) := by
  norm_num [atom0226, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0226_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (73551240 : Int) atom0226) := by
  rw [SparsePolynomial.eval_scale, eval_atom0226]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0227 : SparsePolynomial.Poly := [([1,5,12], 1)]
theorem eval_atom0227 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0227 = ((g 1) * (g 5) * (g 12)) := by
  norm_num [atom0227, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0227_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (82164600 : Int) atom0227) := by
  rw [SparsePolynomial.eval_scale, eval_atom0227]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0228 : SparsePolynomial.Poly := [([1,5,13], 1)]
theorem eval_atom0228 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0228 = ((g 1) * (g 5) * (g 13)) := by
  norm_num [atom0228, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0228_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (87301080 : Int) atom0228) := by
  rw [SparsePolynomial.eval_scale, eval_atom0228]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0229 : SparsePolynomial.Poly := [([1,5,14], 1)]
theorem eval_atom0229 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0229 = ((g 1) * (g 5) * (g 14)) := by
  norm_num [atom0229, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0229_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (92437560 : Int) atom0229) := by
  rw [SparsePolynomial.eval_scale, eval_atom0229]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0230 : SparsePolynomial.Poly := [([1,6,6], 1)]
theorem eval_atom0230 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0230 = ((g 1) * (g 6) * (g 6)) := by
  norm_num [atom0230, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0230_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28213920 : Int) atom0230) := by
  rw [SparsePolynomial.eval_scale, eval_atom0230]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 1) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0231 : SparsePolynomial.Poly := [([1,6,7], 1)]
theorem eval_atom0231 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0231 = ((g 1) * (g 6) * (g 7)) := by
  norm_num [atom0231, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0231_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47875872 : Int) atom0231) := by
  rw [SparsePolynomial.eval_scale, eval_atom0231]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0232 : SparsePolynomial.Poly := [([1,6,8], 1)]
theorem eval_atom0232 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0232 = ((g 1) * (g 6) * (g 8)) := by
  norm_num [atom0232, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0232_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48096000 : Int) atom0232) := by
  rw [SparsePolynomial.eval_scale, eval_atom0232]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block002 : SparsePolynomial.Poly := [([0,8,11], 62330040), ([0,8,12], 39342240), ([0,8,13], 33632280), ([0,8,14], 17500320), ([0,9,9], 68653440), ([0,9,10], 117020160), ([0,9,11], 116705880), ([0,9,12], 103662720), ([0,9,13], 59244480), ([0,9,14], 64782720), ([0,10,10], 54801792), ([0,10,11], 101053440), ([0,10,12], 109175040), ([0,10,13], 63754560), ([0,10,14], 72679680), ([0,11,11], 52686720), ([0,11,12], 114687360), ([0,11,13], 66070080), ([0,11,14], 65093760), ([0,12,12], 60099840), ([0,12,13], 70580160), ([0,12,14], 72990720), ([0,13,13], 6488640), ([0,13,14], 10290240), ([1,1,1], 1827360), ([1,1,2], 13046400), ([1,1,3], 10437120), ([1,1,4], 7827840), ([1,1,5], 5218560), ([1,1,6], 2609280), ([1,1,9], 20293200), ([1,2,2], 20217600), ([1,2,3], 37601280), ([1,2,4], 34767360), ([1,2,5], 31933440), ([1,2,6], 29099520), ([1,2,7], 26265600), ([1,2,8], 26910720), ([1,2,9], 75029760), ([1,2,10], 35017920), ([1,2,11], 47631240), ([1,2,12], 40870080), ([1,2,13], 33523200), ([1,2,14], 39453840), ([1,3,3], 14631840), ([1,3,4], 26714880), ([1,3,5], 26265600), ([1,3,6], 25816320), ([1,3,7], 25591680), ([1,3,8], 28846080), ([1,3,9], 78900480), ([1,3,10], 42434280), ([1,3,11], 56271240), ([1,3,12], 54029880), ([1,3,13], 53115480), ([1,3,14], 52201080), ([1,4,4], 19306080), ([1,4,5], 28290240), ([1,4,6], 29016000), ([1,4,7], 29741760), ([1,4,8], 33946560), ([1,4,9], 82771200), ([1,4,10], 51666840), ([1,4,11], 64911240), ([1,4,12], 69625800), ([1,4,13], 72636840), ([1,4,14], 75647880), ([1,5,5], 22753440), ([1,5,6], 36922752), ([1,5,7], 36524160), ([1,5,8], 41083200), ([1,5,9], 86641920), ([1,5,10], 60840360), ([1,5,11], 73551240), ([1,5,12], 82164600), ([1,5,13], 87301080), ([1,5,14], 92437560), ([1,6,6], 28213920), ([1,6,7], 47875872), ([1,6,8], 48096000)]
theorem block002_data : block002 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (62330040 : Int) atom0153) (SparsePolynomial.scale (39342240 : Int) atom0154)) (SparsePolynomial.merge (SparsePolynomial.scale (33632280 : Int) atom0155) (SparsePolynomial.merge (SparsePolynomial.scale (17500320 : Int) atom0156) (SparsePolynomial.scale (68653440 : Int) atom0157)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (117020160 : Int) atom0158) (SparsePolynomial.scale (116705880 : Int) atom0159)) (SparsePolynomial.merge (SparsePolynomial.scale (103662720 : Int) atom0160) (SparsePolynomial.merge (SparsePolynomial.scale (59244480 : Int) atom0161) (SparsePolynomial.scale (64782720 : Int) atom0162))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (54801792 : Int) atom0163) (SparsePolynomial.scale (101053440 : Int) atom0164)) (SparsePolynomial.merge (SparsePolynomial.scale (109175040 : Int) atom0165) (SparsePolynomial.merge (SparsePolynomial.scale (63754560 : Int) atom0166) (SparsePolynomial.scale (72679680 : Int) atom0167)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (52686720 : Int) atom0168) (SparsePolynomial.scale (114687360 : Int) atom0169)) (SparsePolynomial.merge (SparsePolynomial.scale (66070080 : Int) atom0170) (SparsePolynomial.merge (SparsePolynomial.scale (65093760 : Int) atom0171) (SparsePolynomial.scale (60099840 : Int) atom0172)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (70580160 : Int) atom0173) (SparsePolynomial.scale (72990720 : Int) atom0174)) (SparsePolynomial.merge (SparsePolynomial.scale (6488640 : Int) atom0175) (SparsePolynomial.merge (SparsePolynomial.scale (10290240 : Int) atom0176) (SparsePolynomial.scale (1827360 : Int) atom0177)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13046400 : Int) atom0178) (SparsePolynomial.scale (10437120 : Int) atom0179)) (SparsePolynomial.merge (SparsePolynomial.scale (7827840 : Int) atom0180) (SparsePolynomial.merge (SparsePolynomial.scale (5218560 : Int) atom0181) (SparsePolynomial.scale (2609280 : Int) atom0182))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (20293200 : Int) atom0183) (SparsePolynomial.scale (20217600 : Int) atom0184)) (SparsePolynomial.merge (SparsePolynomial.scale (37601280 : Int) atom0185) (SparsePolynomial.merge (SparsePolynomial.scale (34767360 : Int) atom0186) (SparsePolynomial.scale (31933440 : Int) atom0187)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (29099520 : Int) atom0188) (SparsePolynomial.scale (26265600 : Int) atom0189)) (SparsePolynomial.merge (SparsePolynomial.scale (26910720 : Int) atom0190) (SparsePolynomial.merge (SparsePolynomial.scale (75029760 : Int) atom0191) (SparsePolynomial.scale (35017920 : Int) atom0192))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (47631240 : Int) atom0193) (SparsePolynomial.scale (40870080 : Int) atom0194)) (SparsePolynomial.merge (SparsePolynomial.scale (33523200 : Int) atom0195) (SparsePolynomial.merge (SparsePolynomial.scale (39453840 : Int) atom0196) (SparsePolynomial.scale (14631840 : Int) atom0197)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (26714880 : Int) atom0198) (SparsePolynomial.scale (26265600 : Int) atom0199)) (SparsePolynomial.merge (SparsePolynomial.scale (25816320 : Int) atom0200) (SparsePolynomial.merge (SparsePolynomial.scale (25591680 : Int) atom0201) (SparsePolynomial.scale (28846080 : Int) atom0202))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (78900480 : Int) atom0203) (SparsePolynomial.scale (42434280 : Int) atom0204)) (SparsePolynomial.merge (SparsePolynomial.scale (56271240 : Int) atom0205) (SparsePolynomial.merge (SparsePolynomial.scale (54029880 : Int) atom0206) (SparsePolynomial.scale (53115480 : Int) atom0207)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (52201080 : Int) atom0208) (SparsePolynomial.scale (19306080 : Int) atom0209)) (SparsePolynomial.merge (SparsePolynomial.scale (28290240 : Int) atom0210) (SparsePolynomial.merge (SparsePolynomial.scale (29016000 : Int) atom0211) (SparsePolynomial.scale (29741760 : Int) atom0212)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (33946560 : Int) atom0213) (SparsePolynomial.scale (82771200 : Int) atom0214)) (SparsePolynomial.merge (SparsePolynomial.scale (51666840 : Int) atom0215) (SparsePolynomial.merge (SparsePolynomial.scale (64911240 : Int) atom0216) (SparsePolynomial.scale (69625800 : Int) atom0217)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (72636840 : Int) atom0218) (SparsePolynomial.scale (75647880 : Int) atom0219)) (SparsePolynomial.merge (SparsePolynomial.scale (22753440 : Int) atom0220) (SparsePolynomial.merge (SparsePolynomial.scale (36922752 : Int) atom0221) (SparsePolynomial.scale (36524160 : Int) atom0222))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (41083200 : Int) atom0223) (SparsePolynomial.scale (86641920 : Int) atom0224)) (SparsePolynomial.merge (SparsePolynomial.scale (60840360 : Int) atom0225) (SparsePolynomial.merge (SparsePolynomial.scale (73551240 : Int) atom0226) (SparsePolynomial.scale (82164600 : Int) atom0227)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (87301080 : Int) atom0228) (SparsePolynomial.scale (92437560 : Int) atom0229)) (SparsePolynomial.merge (SparsePolynomial.scale (28213920 : Int) atom0230) (SparsePolynomial.merge (SparsePolynomial.scale (47875872 : Int) atom0231) (SparsePolynomial.scale (48096000 : Int) atom0232)))))))) := by decide +kernel
theorem block002_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block002 := by
  rw [block002_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0153_nonneg g hg hA hB) (atom0154_nonneg g hg hA hB)) (add_nonneg (atom0155_nonneg g hg hA hB) (add_nonneg (atom0156_nonneg g hg hA hB) (atom0157_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0158_nonneg g hg hA hB) (atom0159_nonneg g hg hA hB)) (add_nonneg (atom0160_nonneg g hg hA hB) (add_nonneg (atom0161_nonneg g hg hA hB) (atom0162_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0163_nonneg g hg hA hB) (atom0164_nonneg g hg hA hB)) (add_nonneg (atom0165_nonneg g hg hA hB) (add_nonneg (atom0166_nonneg g hg hA hB) (atom0167_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0168_nonneg g hg hA hB) (atom0169_nonneg g hg hA hB)) (add_nonneg (atom0170_nonneg g hg hA hB) (add_nonneg (atom0171_nonneg g hg hA hB) (atom0172_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0173_nonneg g hg hA hB) (atom0174_nonneg g hg hA hB)) (add_nonneg (atom0175_nonneg g hg hA hB) (add_nonneg (atom0176_nonneg g hg hA hB) (atom0177_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0178_nonneg g hg hA hB) (atom0179_nonneg g hg hA hB)) (add_nonneg (atom0180_nonneg g hg hA hB) (add_nonneg (atom0181_nonneg g hg hA hB) (atom0182_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0183_nonneg g hg hA hB) (atom0184_nonneg g hg hA hB)) (add_nonneg (atom0185_nonneg g hg hA hB) (add_nonneg (atom0186_nonneg g hg hA hB) (atom0187_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0188_nonneg g hg hA hB) (atom0189_nonneg g hg hA hB)) (add_nonneg (atom0190_nonneg g hg hA hB) (add_nonneg (atom0191_nonneg g hg hA hB) (atom0192_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0193_nonneg g hg hA hB) (atom0194_nonneg g hg hA hB)) (add_nonneg (atom0195_nonneg g hg hA hB) (add_nonneg (atom0196_nonneg g hg hA hB) (atom0197_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0198_nonneg g hg hA hB) (atom0199_nonneg g hg hA hB)) (add_nonneg (atom0200_nonneg g hg hA hB) (add_nonneg (atom0201_nonneg g hg hA hB) (atom0202_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0203_nonneg g hg hA hB) (atom0204_nonneg g hg hA hB)) (add_nonneg (atom0205_nonneg g hg hA hB) (add_nonneg (atom0206_nonneg g hg hA hB) (atom0207_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0208_nonneg g hg hA hB) (atom0209_nonneg g hg hA hB)) (add_nonneg (atom0210_nonneg g hg hA hB) (add_nonneg (atom0211_nonneg g hg hA hB) (atom0212_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0213_nonneg g hg hA hB) (atom0214_nonneg g hg hA hB)) (add_nonneg (atom0215_nonneg g hg hA hB) (add_nonneg (atom0216_nonneg g hg hA hB) (atom0217_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0218_nonneg g hg hA hB) (atom0219_nonneg g hg hA hB)) (add_nonneg (atom0220_nonneg g hg hA hB) (add_nonneg (atom0221_nonneg g hg hA hB) (atom0222_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0223_nonneg g hg hA hB) (atom0224_nonneg g hg hA hB)) (add_nonneg (atom0225_nonneg g hg hA hB) (add_nonneg (atom0226_nonneg g hg hA hB) (atom0227_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0228_nonneg g hg hA hB) (atom0229_nonneg g hg hA hB)) (add_nonneg (atom0230_nonneg g hg hA hB) (add_nonneg (atom0231_nonneg g hg hA hB) (atom0232_nonneg g hg hA hB))))))))

end APPT.Finite15
