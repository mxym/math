import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1089 : SparsePolynomial.Poly := [([3,6,8], 1)]
theorem eval_atom1089 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1089 = ((g 3) * (g 6) * (g 8)) := by
  norm_num [atom1089, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1089_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (101846650752000 : Int) atom1089) := by
  rw [SparsePolynomial.eval_scale, eval_atom1089]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1090 : SparsePolynomial.Poly := [([3,6,9], 1)]
theorem eval_atom1090 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1090 = ((g 3) * (g 6) * (g 9)) := by
  norm_num [atom1090, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1090_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (105562098127728 : Int) atom1090) := by
  rw [SparsePolynomial.eval_scale, eval_atom1090]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1091 : SparsePolynomial.Poly := [([3,6,10], 1)]
theorem eval_atom1091 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1091 = ((g 3) * (g 6) * (g 10)) := by
  norm_num [atom1091, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1091_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (125826931427472 : Int) atom1091) := by
  rw [SparsePolynomial.eval_scale, eval_atom1091]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1092 : SparsePolynomial.Poly := [([3,6,11], 1)]
theorem eval_atom1092 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1092 = ((g 3) * (g 6) * (g 11)) := by
  norm_num [atom1092, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1092_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (136085099683104 : Int) atom1092) := by
  rw [SparsePolynomial.eval_scale, eval_atom1092]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1093 : SparsePolynomial.Poly := [([3,6,12], 1)]
theorem eval_atom1093 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1093 = ((g 3) * (g 6) * (g 12)) := by
  norm_num [atom1093, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1093_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (161923371724224 : Int) atom1093) := by
  rw [SparsePolynomial.eval_scale, eval_atom1093]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1094 : SparsePolynomial.Poly := [([3,6,13], 1)]
theorem eval_atom1094 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1094 = ((g 3) * (g 6) * (g 13)) := by
  norm_num [atom1094, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1094_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (153240978844800 : Int) atom1094) := by
  rw [SparsePolynomial.eval_scale, eval_atom1094]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1095 : SparsePolynomial.Poly := [([3,6,14], 1)]
theorem eval_atom1095 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1095 = ((g 3) * (g 6) * (g 14)) := by
  norm_num [atom1095, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1095_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (140884323148800 : Int) atom1095) := by
  rw [SparsePolynomial.eval_scale, eval_atom1095]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1096 : SparsePolynomial.Poly := [([3,6,15], 1)]
theorem eval_atom1096 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1096 = ((g 3) * (g 6) * (g 15)) := by
  norm_num [atom1096, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1096_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (143314674048000 : Int) atom1096) := by
  rw [SparsePolynomial.eval_scale, eval_atom1096]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1097 : SparsePolynomial.Poly := [([3,6,16], 1)]
theorem eval_atom1097 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1097 = ((g 3) * (g 6) * (g 16)) := by
  norm_num [atom1097, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1097_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (133922514700800 : Int) atom1097) := by
  rw [SparsePolynomial.eval_scale, eval_atom1097]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1098 : SparsePolynomial.Poly := [([3,6,17], 1)]
theorem eval_atom1098 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1098 = ((g 3) * (g 6) * (g 17)) := by
  norm_num [atom1098, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1098_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (134463093811200 : Int) atom1098) := by
  rw [SparsePolynomial.eval_scale, eval_atom1098]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1099 : SparsePolynomial.Poly := [([3,6,18], 1)]
theorem eval_atom1099 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1099 = ((g 3) * (g 6) * (g 18)) := by
  norm_num [atom1099, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1099_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (172926682790400 : Int) atom1099) := by
  rw [SparsePolynomial.eval_scale, eval_atom1099]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1100 : SparsePolynomial.Poly := [([3,6,19], 1)]
theorem eval_atom1100 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1100 = ((g 3) * (g 6) * (g 19)) := by
  norm_num [atom1100, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1100_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (146965354905600 : Int) atom1100) := by
  rw [SparsePolynomial.eval_scale, eval_atom1100]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1101 : SparsePolynomial.Poly := [([3,6,20], 1)]
theorem eval_atom1101 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1101 = ((g 3) * (g 6) * (g 20)) := by
  norm_num [atom1101, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1101_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (206053422220800 : Int) atom1101) := by
  rw [SparsePolynomial.eval_scale, eval_atom1101]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1102 : SparsePolynomial.Poly := [([3,6,21], 1)]
theorem eval_atom1102 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1102 = ((g 3) * (g 6) * (g 21)) := by
  norm_num [atom1102, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1102_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (209093938099200 : Int) atom1102) := by
  rw [SparsePolynomial.eval_scale, eval_atom1102]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 6) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1103 : SparsePolynomial.Poly := [([3,6,22], 1)]
theorem eval_atom1103 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1103 = ((g 3) * (g 6) * (g 22)) := by
  norm_num [atom1103, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1103_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (248450545728000 : Int) atom1103) := by
  rw [SparsePolynomial.eval_scale, eval_atom1103]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 6) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1104 : SparsePolynomial.Poly := [([3,6,23], 1)]
theorem eval_atom1104 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1104 = ((g 3) * (g 6) * (g 23)) := by
  norm_num [atom1104, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1104_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (287807153356800 : Int) atom1104) := by
  rw [SparsePolynomial.eval_scale, eval_atom1104]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 6) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1105 : SparsePolynomial.Poly := [([3,7,7], 1)]
theorem eval_atom1105 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1105 = ((g 3) * (g 7) * (g 7)) := by
  norm_num [atom1105, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1105_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (81912017510400 : Int) atom1105) := by
  rw [SparsePolynomial.eval_scale, eval_atom1105]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 3) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1106 : SparsePolynomial.Poly := [([3,7,8], 1)]
theorem eval_atom1106 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1106 = ((g 3) * (g 7) * (g 8)) := by
  norm_num [atom1106, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1106_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (148101709324800 : Int) atom1106) := by
  rw [SparsePolynomial.eval_scale, eval_atom1106]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1107 : SparsePolynomial.Poly := [([3,7,9], 1)]
theorem eval_atom1107 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1107 = ((g 3) * (g 7) * (g 9)) := by
  norm_num [atom1107, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1107_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (135383723561328 : Int) atom1107) := by
  rw [SparsePolynomial.eval_scale, eval_atom1107]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1108 : SparsePolynomial.Poly := [([3,7,10], 1)]
theorem eval_atom1108 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1108 = ((g 3) * (g 7) * (g 10)) := by
  norm_num [atom1108, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1108_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (153607371376272 : Int) atom1108) := by
  rw [SparsePolynomial.eval_scale, eval_atom1108]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1109 : SparsePolynomial.Poly := [([3,7,11], 1)]
theorem eval_atom1109 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1109 = ((g 3) * (g 7) * (g 11)) := by
  norm_num [atom1109, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1109_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (165949249814304 : Int) atom1109) := by
  rw [SparsePolynomial.eval_scale, eval_atom1109]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1110 : SparsePolynomial.Poly := [([3,7,12], 1)]
theorem eval_atom1110 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1110 = ((g 3) * (g 7) * (g 12)) := by
  norm_num [atom1110, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1110_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (193871232037824 : Int) atom1110) := by
  rw [SparsePolynomial.eval_scale, eval_atom1110]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1111 : SparsePolynomial.Poly := [([3,7,13], 1)]
theorem eval_atom1111 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1111 = ((g 3) * (g 7) * (g 13)) := by
  norm_num [atom1111, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1111_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (185210101507200 : Int) atom1111) := by
  rw [SparsePolynomial.eval_scale, eval_atom1111]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1112 : SparsePolynomial.Poly := [([3,7,14], 1)]
theorem eval_atom1112 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1112 = ((g 3) * (g 7) * (g 14)) := by
  norm_num [atom1112, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1112_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (172874708160000 : Int) atom1112) := by
  rw [SparsePolynomial.eval_scale, eval_atom1112]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1113 : SparsePolynomial.Poly := [([3,7,15], 1)]
theorem eval_atom1113 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1113 = ((g 3) * (g 7) * (g 15)) := by
  norm_num [atom1113, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1113_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (175326321408000 : Int) atom1113) := by
  rw [SparsePolynomial.eval_scale, eval_atom1113]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1114 : SparsePolynomial.Poly := [([3,7,16], 1)]
theorem eval_atom1114 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1114 = ((g 3) * (g 7) * (g 16)) := by
  norm_num [atom1114, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1114_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (165955424409600 : Int) atom1114) := by
  rw [SparsePolynomial.eval_scale, eval_atom1114]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1115 : SparsePolynomial.Poly := [([3,7,17], 1)]
theorem eval_atom1115 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1115 = ((g 3) * (g 7) * (g 17)) := by
  norm_num [atom1115, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1115_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (166517265868800 : Int) atom1115) := by
  rw [SparsePolynomial.eval_scale, eval_atom1115]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1116 : SparsePolynomial.Poly := [([3,7,18], 1)]
theorem eval_atom1116 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1116 = ((g 3) * (g 7) * (g 18)) := by
  norm_num [atom1116, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1116_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (207331525632000 : Int) atom1116) := by
  rw [SparsePolynomial.eval_scale, eval_atom1116]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1117 : SparsePolynomial.Poly := [([3,7,19], 1)]
theorem eval_atom1117 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1117 = ((g 3) * (g 7) * (g 19)) := by
  norm_num [atom1117, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1117_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (186050276966400 : Int) atom1117) := by
  rw [SparsePolynomial.eval_scale, eval_atom1117]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1118 : SparsePolynomial.Poly := [([3,7,20], 1)]
theorem eval_atom1118 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1118 = ((g 3) * (g 7) * (g 20)) := by
  norm_num [atom1118, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1118_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (249818423500800 : Int) atom1118) := by
  rw [SparsePolynomial.eval_scale, eval_atom1118]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1119 : SparsePolynomial.Poly := [([3,7,21], 1)]
theorem eval_atom1119 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1119 = ((g 3) * (g 7) * (g 21)) := by
  norm_num [atom1119, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1119_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (262197835468800 : Int) atom1119) := by
  rw [SparsePolynomial.eval_scale, eval_atom1119]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 7) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1120 : SparsePolynomial.Poly := [([3,7,22], 1)]
theorem eval_atom1120 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1120 = ((g 3) * (g 7) * (g 22)) := by
  norm_num [atom1120, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1120_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (310893339187200 : Int) atom1120) := by
  rw [SparsePolynomial.eval_scale, eval_atom1120]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 7) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1121 : SparsePolynomial.Poly := [([3,7,23], 1)]
theorem eval_atom1121 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1121 = ((g 3) * (g 7) * (g 23)) := by
  norm_num [atom1121, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1121_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (359588842905600 : Int) atom1121) := by
  rw [SparsePolynomial.eval_scale, eval_atom1121]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 7) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1122 : SparsePolynomial.Poly := [([3,8,8], 1)]
theorem eval_atom1122 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1122 = ((g 3) * (g 8) * (g 8)) := by
  norm_num [atom1122, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1122_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (101123730892800 : Int) atom1122) := by
  rw [SparsePolynomial.eval_scale, eval_atom1122]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 3) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1123 : SparsePolynomial.Poly := [([3,8,9], 1)]
theorem eval_atom1123 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1123 = ((g 3) * (g 8) * (g 9)) := by
  norm_num [atom1123, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1123_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (189544167714528 : Int) atom1123) := by
  rw [SparsePolynomial.eval_scale, eval_atom1123]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1124 : SparsePolynomial.Poly := [([3,8,10], 1)]
theorem eval_atom1124 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1124 = ((g 3) * (g 8) * (g 10)) := by
  norm_num [atom1124, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1124_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (178502897027664 : Int) atom1124) := by
  rw [SparsePolynomial.eval_scale, eval_atom1124]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1125 : SparsePolynomial.Poly := [([3,8,11], 1)]
theorem eval_atom1125 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1125 = ((g 3) * (g 8) * (g 11)) := by
  norm_num [atom1125, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1125_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (194088787209504 : Int) atom1125) := by
  rw [SparsePolynomial.eval_scale, eval_atom1125]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1126 : SparsePolynomial.Poly := [([3,8,12], 1)]
theorem eval_atom1126 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1126 = ((g 3) * (g 8) * (g 12)) := by
  norm_num [atom1126, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1126_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (217928398463424 : Int) atom1126) := by
  rw [SparsePolynomial.eval_scale, eval_atom1126]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1127 : SparsePolynomial.Poly := [([3,8,13], 1)]
theorem eval_atom1127 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1127 = ((g 3) * (g 8) * (g 13)) := by
  norm_num [atom1127, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1127_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (208267937539200 : Int) atom1127) := by
  rw [SparsePolynomial.eval_scale, eval_atom1127]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1128 : SparsePolynomial.Poly := [([3,8,14], 1)]
theorem eval_atom1128 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1128 = ((g 3) * (g 8) * (g 14)) := by
  norm_num [atom1128, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1128_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (194933213798400 : Int) atom1128) := by
  rw [SparsePolynomial.eval_scale, eval_atom1128]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1129 : SparsePolynomial.Poly := [([3,8,15], 1)]
theorem eval_atom1129 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1129 = ((g 3) * (g 8) * (g 15)) := by
  norm_num [atom1129, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1129_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (196385496652800 : Int) atom1129) := by
  rw [SparsePolynomial.eval_scale, eval_atom1129]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1130 : SparsePolynomial.Poly := [([3,8,16], 1)]
theorem eval_atom1130 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1130 = ((g 3) * (g 8) * (g 16)) := by
  norm_num [atom1130, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1130_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (186015269260800 : Int) atom1130) := by
  rw [SparsePolynomial.eval_scale, eval_atom1130]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1131 : SparsePolynomial.Poly := [([3,8,17], 1)]
theorem eval_atom1131 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1131 = ((g 3) * (g 8) * (g 17)) := by
  norm_num [atom1131, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1131_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (185577780326400 : Int) atom1131) := by
  rw [SparsePolynomial.eval_scale, eval_atom1131]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1132 : SparsePolynomial.Poly := [([3,8,18], 1)]
theorem eval_atom1132 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1132 = ((g 3) * (g 8) * (g 18)) := by
  norm_num [atom1132, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1132_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (228846660134400 : Int) atom1132) := by
  rw [SparsePolynomial.eval_scale, eval_atom1132]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1133 : SparsePolynomial.Poly := [([3,8,19], 1)]
theorem eval_atom1133 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1133 = ((g 3) * (g 8) * (g 19)) := by
  norm_num [atom1133, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1133_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (213473981952000 : Int) atom1133) := by
  rw [SparsePolynomial.eval_scale, eval_atom1133]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1134 : SparsePolynomial.Poly := [([3,8,20], 1)]
theorem eval_atom1134 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1134 = ((g 3) * (g 8) * (g 20)) := by
  norm_num [atom1134, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1134_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (283150698969600 : Int) atom1134) := by
  rw [SparsePolynomial.eval_scale, eval_atom1134]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1135 : SparsePolynomial.Poly := [([3,8,21], 1)]
theorem eval_atom1135 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1135 = ((g 3) * (g 8) * (g 21)) := by
  norm_num [atom1135, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1135_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (308346582297600 : Int) atom1135) := by
  rw [SparsePolynomial.eval_scale, eval_atom1135]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 8) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1136 : SparsePolynomial.Poly := [([3,8,22], 1)]
theorem eval_atom1136 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1136 = ((g 3) * (g 8) * (g 22)) := by
  norm_num [atom1136, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1136_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (369858557376000 : Int) atom1136) := by
  rw [SparsePolynomial.eval_scale, eval_atom1136]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 8) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1137 : SparsePolynomial.Poly := [([3,8,23], 1)]
theorem eval_atom1137 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1137 = ((g 3) * (g 8) * (g 23)) := by
  norm_num [atom1137, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1137_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (431370532454400 : Int) atom1137) := by
  rw [SparsePolynomial.eval_scale, eval_atom1137]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 8) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1138 : SparsePolynomial.Poly := [([3,9,9], 1)]
theorem eval_atom1138 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1138 = ((g 3) * (g 9) * (g 9)) := by
  norm_num [atom1138, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1138_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (126437516476128 : Int) atom1138) := by
  rw [SparsePolynomial.eval_scale, eval_atom1138]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 3) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1139 : SparsePolynomial.Poly := [([3,9,10], 1)]
theorem eval_atom1139 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1139 = ((g 3) * (g 9) * (g 10)) := by
  norm_num [atom1139, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1139_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (239751911272896 : Int) atom1139) := by
  rw [SparsePolynomial.eval_scale, eval_atom1139]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1140 : SparsePolynomial.Poly := [([3,9,11], 1)]
theorem eval_atom1140 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1140 = ((g 3) * (g 9) * (g 11)) := by
  norm_num [atom1140, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1140_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (231275379769632 : Int) atom1140) := by
  rw [SparsePolynomial.eval_scale, eval_atom1140]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1141 : SparsePolynomial.Poly := [([3,9,12], 1)]
theorem eval_atom1141 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1141 = ((g 3) * (g 9) * (g 12)) := by
  norm_num [atom1141, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1141_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (256178108463552 : Int) atom1141) := by
  rw [SparsePolynomial.eval_scale, eval_atom1141]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1142 : SparsePolynomial.Poly := [([3,9,13], 1)]
theorem eval_atom1142 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1142 = ((g 3) * (g 9) * (g 13)) := by
  norm_num [atom1142, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1142_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (241414683827328 : Int) atom1142) := by
  rw [SparsePolynomial.eval_scale, eval_atom1142]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1143 : SparsePolynomial.Poly := [([3,9,14], 1)]
theorem eval_atom1143 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1143 = ((g 3) * (g 9) * (g 14)) := by
  norm_num [atom1143, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1143_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (226060036950528 : Int) atom1143) := by
  rw [SparsePolynomial.eval_scale, eval_atom1143]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1144 : SparsePolynomial.Poly := [([3,9,15], 1)]
theorem eval_atom1144 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1144 = ((g 3) * (g 9) * (g 15)) := by
  norm_num [atom1144, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1144_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (225492396668928 : Int) atom1144) := by
  rw [SparsePolynomial.eval_scale, eval_atom1144]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1145 : SparsePolynomial.Poly := [([3,9,16], 1)]
theorem eval_atom1145 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1145 = ((g 3) * (g 9) * (g 16)) := by
  norm_num [atom1145, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1145_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (213102246140928 : Int) atom1145) := by
  rw [SparsePolynomial.eval_scale, eval_atom1145]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1146 : SparsePolynomial.Poly := [([3,9,17], 1)]
theorem eval_atom1146 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1146 = ((g 3) * (g 9) * (g 17)) := by
  norm_num [atom1146, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1146_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (210644834070528 : Int) atom1146) := by
  rw [SparsePolynomial.eval_scale, eval_atom1146]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1147 : SparsePolynomial.Poly := [([3,9,18], 1)]
theorem eval_atom1147 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1147 = ((g 3) * (g 9) * (g 18)) := by
  norm_num [atom1147, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1147_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (254097258573312 : Int) atom1147) := by
  rw [SparsePolynomial.eval_scale, eval_atom1147]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1148 : SparsePolynomial.Poly := [([3,9,19], 1)]
theorem eval_atom1148 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1148 = ((g 3) * (g 9) * (g 19)) := by
  norm_num [atom1148, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1148_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (241111592916480 : Int) atom1148) := by
  rw [SparsePolynomial.eval_scale, eval_atom1148]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1149 : SparsePolynomial.Poly := [([3,9,20], 1)]
theorem eval_atom1149 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1149 = ((g 3) * (g 9) * (g 20)) := by
  norm_num [atom1149, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1149_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (313175322459648 : Int) atom1149) := by
  rw [SparsePolynomial.eval_scale, eval_atom1149]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1150 : SparsePolynomial.Poly := [([3,9,21], 1)]
theorem eval_atom1150 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1150 = ((g 3) * (g 9) * (g 21)) := by
  norm_num [atom1150, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1150_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (345165153974784 : Int) atom1150) := by
  rw [SparsePolynomial.eval_scale, eval_atom1150]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 9) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1151 : SparsePolynomial.Poly := [([3,9,22], 1)]
theorem eval_atom1151 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1151 = ((g 3) * (g 9) * (g 22)) := by
  norm_num [atom1151, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1151_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (413471077240320 : Int) atom1151) := by
  rw [SparsePolynomial.eval_scale, eval_atom1151]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 9) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1152 : SparsePolynomial.Poly := [([3,9,23], 1)]
theorem eval_atom1152 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1152 = ((g 3) * (g 9) * (g 23)) := by
  norm_num [atom1152, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1152_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (481777000505856 : Int) atom1152) := by
  rw [SparsePolynomial.eval_scale, eval_atom1152]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 9) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1153 : SparsePolynomial.Poly := [([3,10,10], 1)]
theorem eval_atom1153 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1153 = ((g 3) * (g 10) * (g 10)) := by
  norm_num [atom1153, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1153_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (151331474451168 : Int) atom1153) := by
  rw [SparsePolynomial.eval_scale, eval_atom1153]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 3) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1154 : SparsePolynomial.Poly := [([3,10,11], 1)]
theorem eval_atom1154 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1154 = ((g 3) * (g 10) * (g 11)) := by
  norm_num [atom1154, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1154_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (298353837763872 : Int) atom1154) := by
  rw [SparsePolynomial.eval_scale, eval_atom1154]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1155 : SparsePolynomial.Poly := [([3,10,12], 1)]
theorem eval_atom1155 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1155 = ((g 3) * (g 10) * (g 12)) := by
  norm_num [atom1155, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1155_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (317133010003392 : Int) atom1155) := by
  rw [SparsePolynomial.eval_scale, eval_atom1155]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1156 : SparsePolynomial.Poly := [([3,10,13], 1)]
theorem eval_atom1156 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1156 = ((g 3) * (g 10) * (g 13)) := by
  norm_num [atom1156, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1156_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (302412110064768 : Int) atom1156) := by
  rw [SparsePolynomial.eval_scale, eval_atom1156]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 3) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1157 : SparsePolynomial.Poly := [([3,10,14], 1)]
theorem eval_atom1157 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1157 = ((g 3) * (g 10) * (g 14)) := by
  norm_num [atom1157, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1157_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (284016947309568 : Int) atom1157) := by
  rw [SparsePolynomial.eval_scale, eval_atom1157]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 3) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1158 : SparsePolynomial.Poly := [([3,10,15], 1)]
theorem eval_atom1158 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1158 = ((g 3) * (g 10) * (g 15)) := by
  norm_num [atom1158, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1158_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (280408791149568 : Int) atom1158) := by
  rw [SparsePolynomial.eval_scale, eval_atom1158]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 3) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1159 : SparsePolynomial.Poly := [([3,10,16], 1)]
theorem eval_atom1159 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1159 = ((g 3) * (g 10) * (g 16)) := by
  norm_num [atom1159, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1159_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (264978124743168 : Int) atom1159) := by
  rw [SparsePolynomial.eval_scale, eval_atom1159]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 3) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1160 : SparsePolynomial.Poly := [([3,10,17], 1)]
theorem eval_atom1160 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1160 = ((g 3) * (g 10) * (g 17)) := by
  norm_num [atom1160, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1160_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (259480196794368 : Int) atom1160) := by
  rw [SparsePolynomial.eval_scale, eval_atom1160]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 3) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1161 : SparsePolynomial.Poly := [([3,10,18], 1)]
theorem eval_atom1161 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1161 = ((g 3) * (g 10) * (g 18)) := by
  norm_num [atom1161, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1161_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (298624869430272 : Int) atom1161) := by
  rw [SparsePolynomial.eval_scale, eval_atom1161]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 3) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1162 : SparsePolynomial.Poly := [([3,10,19], 1)]
theorem eval_atom1162 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1162 = ((g 3) * (g 10) * (g 19)) := by
  norm_num [atom1162, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1162_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (280064215918080 : Int) atom1162) := by
  rw [SparsePolynomial.eval_scale, eval_atom1162]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 3) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1163 : SparsePolynomial.Poly := [([3,10,20], 1)]
theorem eval_atom1163 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1163 = ((g 3) * (g 10) * (g 20)) := by
  norm_num [atom1163, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1163_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (346552957605888 : Int) atom1163) := by
  rw [SparsePolynomial.eval_scale, eval_atom1163]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 3) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1164 : SparsePolynomial.Poly := [([3,10,21], 1)]
theorem eval_atom1164 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1164 = ((g 3) * (g 10) * (g 21)) := by
  norm_num [atom1164, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1164_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (370433329288704 : Int) atom1164) := by
  rw [SparsePolynomial.eval_scale, eval_atom1164]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 10) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1165 : SparsePolynomial.Poly := [([3,10,22], 1)]
theorem eval_atom1165 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1165 = ((g 3) * (g 10) * (g 22)) := by
  norm_num [atom1165, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1165_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (430629792721920 : Int) atom1165) := by
  rw [SparsePolynomial.eval_scale, eval_atom1165]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 10) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1166 : SparsePolynomial.Poly := [([3,10,23], 1)]
theorem eval_atom1166 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1166 = ((g 3) * (g 10) * (g 23)) := by
  norm_num [atom1166, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1166_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (490826256155136 : Int) atom1166) := by
  rw [SparsePolynomial.eval_scale, eval_atom1166]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 10) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1167 : SparsePolynomial.Poly := [([3,11,11], 1)]
theorem eval_atom1167 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1167 = ((g 3) * (g 11) * (g 11)) := by
  norm_num [atom1167, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1167_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (191205524119104 : Int) atom1167) := by
  rw [SparsePolynomial.eval_scale, eval_atom1167]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 3) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1168 : SparsePolynomial.Poly := [([3,11,12], 1)]
theorem eval_atom1168 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1168 = ((g 3) * (g 11) * (g 12)) := by
  norm_num [atom1168, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1168_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (377351140782528 : Int) atom1168) := by
  rw [SparsePolynomial.eval_scale, eval_atom1168]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 3) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block016 : SparsePolynomial.Poly := [([3,6,8], 101846650752000), ([3,6,9], 105562098127728), ([3,6,10], 125826931427472), ([3,6,11], 136085099683104), ([3,6,12], 161923371724224), ([3,6,13], 153240978844800), ([3,6,14], 140884323148800), ([3,6,15], 143314674048000), ([3,6,16], 133922514700800), ([3,6,17], 134463093811200), ([3,6,18], 172926682790400), ([3,6,19], 146965354905600), ([3,6,20], 206053422220800), ([3,6,21], 209093938099200), ([3,6,22], 248450545728000), ([3,6,23], 287807153356800), ([3,7,7], 81912017510400), ([3,7,8], 148101709324800), ([3,7,9], 135383723561328), ([3,7,10], 153607371376272), ([3,7,11], 165949249814304), ([3,7,12], 193871232037824), ([3,7,13], 185210101507200), ([3,7,14], 172874708160000), ([3,7,15], 175326321408000), ([3,7,16], 165955424409600), ([3,7,17], 166517265868800), ([3,7,18], 207331525632000), ([3,7,19], 186050276966400), ([3,7,20], 249818423500800), ([3,7,21], 262197835468800), ([3,7,22], 310893339187200), ([3,7,23], 359588842905600), ([3,8,8], 101123730892800), ([3,8,9], 189544167714528), ([3,8,10], 178502897027664), ([3,8,11], 194088787209504), ([3,8,12], 217928398463424), ([3,8,13], 208267937539200), ([3,8,14], 194933213798400), ([3,8,15], 196385496652800), ([3,8,16], 186015269260800), ([3,8,17], 185577780326400), ([3,8,18], 228846660134400), ([3,8,19], 213473981952000), ([3,8,20], 283150698969600), ([3,8,21], 308346582297600), ([3,8,22], 369858557376000), ([3,8,23], 431370532454400), ([3,9,9], 126437516476128), ([3,9,10], 239751911272896), ([3,9,11], 231275379769632), ([3,9,12], 256178108463552), ([3,9,13], 241414683827328), ([3,9,14], 226060036950528), ([3,9,15], 225492396668928), ([3,9,16], 213102246140928), ([3,9,17], 210644834070528), ([3,9,18], 254097258573312), ([3,9,19], 241111592916480), ([3,9,20], 313175322459648), ([3,9,21], 345165153974784), ([3,9,22], 413471077240320), ([3,9,23], 481777000505856), ([3,10,10], 151331474451168), ([3,10,11], 298353837763872), ([3,10,12], 317133010003392), ([3,10,13], 302412110064768), ([3,10,14], 284016947309568), ([3,10,15], 280408791149568), ([3,10,16], 264978124743168), ([3,10,17], 259480196794368), ([3,10,18], 298624869430272), ([3,10,19], 280064215918080), ([3,10,20], 346552957605888), ([3,10,21], 370433329288704), ([3,10,22], 430629792721920), ([3,10,23], 490826256155136), ([3,11,11], 191205524119104), ([3,11,12], 377351140782528)]
theorem block016_data : block016 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (101846650752000 : Int) atom1089) (SparsePolynomial.scale (105562098127728 : Int) atom1090)) (SparsePolynomial.merge (SparsePolynomial.scale (125826931427472 : Int) atom1091) (SparsePolynomial.merge (SparsePolynomial.scale (136085099683104 : Int) atom1092) (SparsePolynomial.scale (161923371724224 : Int) atom1093)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (153240978844800 : Int) atom1094) (SparsePolynomial.scale (140884323148800 : Int) atom1095)) (SparsePolynomial.merge (SparsePolynomial.scale (143314674048000 : Int) atom1096) (SparsePolynomial.merge (SparsePolynomial.scale (133922514700800 : Int) atom1097) (SparsePolynomial.scale (134463093811200 : Int) atom1098))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (172926682790400 : Int) atom1099) (SparsePolynomial.scale (146965354905600 : Int) atom1100)) (SparsePolynomial.merge (SparsePolynomial.scale (206053422220800 : Int) atom1101) (SparsePolynomial.merge (SparsePolynomial.scale (209093938099200 : Int) atom1102) (SparsePolynomial.scale (248450545728000 : Int) atom1103)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (287807153356800 : Int) atom1104) (SparsePolynomial.scale (81912017510400 : Int) atom1105)) (SparsePolynomial.merge (SparsePolynomial.scale (148101709324800 : Int) atom1106) (SparsePolynomial.merge (SparsePolynomial.scale (135383723561328 : Int) atom1107) (SparsePolynomial.scale (153607371376272 : Int) atom1108)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (165949249814304 : Int) atom1109) (SparsePolynomial.scale (193871232037824 : Int) atom1110)) (SparsePolynomial.merge (SparsePolynomial.scale (185210101507200 : Int) atom1111) (SparsePolynomial.merge (SparsePolynomial.scale (172874708160000 : Int) atom1112) (SparsePolynomial.scale (175326321408000 : Int) atom1113)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (165955424409600 : Int) atom1114) (SparsePolynomial.scale (166517265868800 : Int) atom1115)) (SparsePolynomial.merge (SparsePolynomial.scale (207331525632000 : Int) atom1116) (SparsePolynomial.merge (SparsePolynomial.scale (186050276966400 : Int) atom1117) (SparsePolynomial.scale (249818423500800 : Int) atom1118))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (262197835468800 : Int) atom1119) (SparsePolynomial.scale (310893339187200 : Int) atom1120)) (SparsePolynomial.merge (SparsePolynomial.scale (359588842905600 : Int) atom1121) (SparsePolynomial.merge (SparsePolynomial.scale (101123730892800 : Int) atom1122) (SparsePolynomial.scale (189544167714528 : Int) atom1123)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (178502897027664 : Int) atom1124) (SparsePolynomial.scale (194088787209504 : Int) atom1125)) (SparsePolynomial.merge (SparsePolynomial.scale (217928398463424 : Int) atom1126) (SparsePolynomial.merge (SparsePolynomial.scale (208267937539200 : Int) atom1127) (SparsePolynomial.scale (194933213798400 : Int) atom1128))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (196385496652800 : Int) atom1129) (SparsePolynomial.scale (186015269260800 : Int) atom1130)) (SparsePolynomial.merge (SparsePolynomial.scale (185577780326400 : Int) atom1131) (SparsePolynomial.merge (SparsePolynomial.scale (228846660134400 : Int) atom1132) (SparsePolynomial.scale (213473981952000 : Int) atom1133)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (283150698969600 : Int) atom1134) (SparsePolynomial.scale (308346582297600 : Int) atom1135)) (SparsePolynomial.merge (SparsePolynomial.scale (369858557376000 : Int) atom1136) (SparsePolynomial.merge (SparsePolynomial.scale (431370532454400 : Int) atom1137) (SparsePolynomial.scale (126437516476128 : Int) atom1138))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (239751911272896 : Int) atom1139) (SparsePolynomial.scale (231275379769632 : Int) atom1140)) (SparsePolynomial.merge (SparsePolynomial.scale (256178108463552 : Int) atom1141) (SparsePolynomial.merge (SparsePolynomial.scale (241414683827328 : Int) atom1142) (SparsePolynomial.scale (226060036950528 : Int) atom1143)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (225492396668928 : Int) atom1144) (SparsePolynomial.scale (213102246140928 : Int) atom1145)) (SparsePolynomial.merge (SparsePolynomial.scale (210644834070528 : Int) atom1146) (SparsePolynomial.merge (SparsePolynomial.scale (254097258573312 : Int) atom1147) (SparsePolynomial.scale (241111592916480 : Int) atom1148)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (313175322459648 : Int) atom1149) (SparsePolynomial.scale (345165153974784 : Int) atom1150)) (SparsePolynomial.merge (SparsePolynomial.scale (413471077240320 : Int) atom1151) (SparsePolynomial.merge (SparsePolynomial.scale (481777000505856 : Int) atom1152) (SparsePolynomial.scale (151331474451168 : Int) atom1153)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (298353837763872 : Int) atom1154) (SparsePolynomial.scale (317133010003392 : Int) atom1155)) (SparsePolynomial.merge (SparsePolynomial.scale (302412110064768 : Int) atom1156) (SparsePolynomial.merge (SparsePolynomial.scale (284016947309568 : Int) atom1157) (SparsePolynomial.scale (280408791149568 : Int) atom1158))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (264978124743168 : Int) atom1159) (SparsePolynomial.scale (259480196794368 : Int) atom1160)) (SparsePolynomial.merge (SparsePolynomial.scale (298624869430272 : Int) atom1161) (SparsePolynomial.merge (SparsePolynomial.scale (280064215918080 : Int) atom1162) (SparsePolynomial.scale (346552957605888 : Int) atom1163)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (370433329288704 : Int) atom1164) (SparsePolynomial.scale (430629792721920 : Int) atom1165)) (SparsePolynomial.merge (SparsePolynomial.scale (490826256155136 : Int) atom1166) (SparsePolynomial.merge (SparsePolynomial.scale (191205524119104 : Int) atom1167) (SparsePolynomial.scale (377351140782528 : Int) atom1168)))))))) := by decide +kernel
theorem block016_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block016 := by
  rw [block016_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1089_nonneg g hg hA hB) (atom1090_nonneg g hg hA hB)) (add_nonneg (atom1091_nonneg g hg hA hB) (add_nonneg (atom1092_nonneg g hg hA hB) (atom1093_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1094_nonneg g hg hA hB) (atom1095_nonneg g hg hA hB)) (add_nonneg (atom1096_nonneg g hg hA hB) (add_nonneg (atom1097_nonneg g hg hA hB) (atom1098_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1099_nonneg g hg hA hB) (atom1100_nonneg g hg hA hB)) (add_nonneg (atom1101_nonneg g hg hA hB) (add_nonneg (atom1102_nonneg g hg hA hB) (atom1103_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1104_nonneg g hg hA hB) (atom1105_nonneg g hg hA hB)) (add_nonneg (atom1106_nonneg g hg hA hB) (add_nonneg (atom1107_nonneg g hg hA hB) (atom1108_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1109_nonneg g hg hA hB) (atom1110_nonneg g hg hA hB)) (add_nonneg (atom1111_nonneg g hg hA hB) (add_nonneg (atom1112_nonneg g hg hA hB) (atom1113_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1114_nonneg g hg hA hB) (atom1115_nonneg g hg hA hB)) (add_nonneg (atom1116_nonneg g hg hA hB) (add_nonneg (atom1117_nonneg g hg hA hB) (atom1118_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1119_nonneg g hg hA hB) (atom1120_nonneg g hg hA hB)) (add_nonneg (atom1121_nonneg g hg hA hB) (add_nonneg (atom1122_nonneg g hg hA hB) (atom1123_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1124_nonneg g hg hA hB) (atom1125_nonneg g hg hA hB)) (add_nonneg (atom1126_nonneg g hg hA hB) (add_nonneg (atom1127_nonneg g hg hA hB) (atom1128_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1129_nonneg g hg hA hB) (atom1130_nonneg g hg hA hB)) (add_nonneg (atom1131_nonneg g hg hA hB) (add_nonneg (atom1132_nonneg g hg hA hB) (atom1133_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1134_nonneg g hg hA hB) (atom1135_nonneg g hg hA hB)) (add_nonneg (atom1136_nonneg g hg hA hB) (add_nonneg (atom1137_nonneg g hg hA hB) (atom1138_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1139_nonneg g hg hA hB) (atom1140_nonneg g hg hA hB)) (add_nonneg (atom1141_nonneg g hg hA hB) (add_nonneg (atom1142_nonneg g hg hA hB) (atom1143_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1144_nonneg g hg hA hB) (atom1145_nonneg g hg hA hB)) (add_nonneg (atom1146_nonneg g hg hA hB) (add_nonneg (atom1147_nonneg g hg hA hB) (atom1148_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1149_nonneg g hg hA hB) (atom1150_nonneg g hg hA hB)) (add_nonneg (atom1151_nonneg g hg hA hB) (add_nonneg (atom1152_nonneg g hg hA hB) (atom1153_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1154_nonneg g hg hA hB) (atom1155_nonneg g hg hA hB)) (add_nonneg (atom1156_nonneg g hg hA hB) (add_nonneg (atom1157_nonneg g hg hA hB) (atom1158_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1159_nonneg g hg hA hB) (atom1160_nonneg g hg hA hB)) (add_nonneg (atom1161_nonneg g hg hA hB) (add_nonneg (atom1162_nonneg g hg hA hB) (atom1163_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1164_nonneg g hg hA hB) (atom1165_nonneg g hg hA hB)) (add_nonneg (atom1166_nonneg g hg hA hB) (add_nonneg (atom1167_nonneg g hg hA hB) (atom1168_nonneg g hg hA hB))))))))

end APPT.Finite24
