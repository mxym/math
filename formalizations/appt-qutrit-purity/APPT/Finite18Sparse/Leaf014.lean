import APPT.Finite18Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite18
open SparsePolynomial

def atom1055 : SparsePolynomial.Poly := [([10,15,15], 1)]
theorem eval_atom1055 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1055 = ((g 10) * (g 15) * (g 15)) := by
  norm_num [atom1055, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1055_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6248911920 : Int) atom1055) := by
  rw [SparsePolynomial.eval_scale, eval_atom1055]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 10) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1056 : SparsePolynomial.Poly := [([10,15,16], 1)]
theorem eval_atom1056 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1056 = ((g 10) * (g 15) * (g 16)) := by
  norm_num [atom1056, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1056_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13592934960 : Int) atom1056) := by
  rw [SparsePolynomial.eval_scale, eval_atom1056]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1057 : SparsePolynomial.Poly := [([10,15,17], 1)]
theorem eval_atom1057 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1057 = ((g 10) * (g 15) * (g 17)) := by
  norm_num [atom1057, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1057_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20673746760 : Int) atom1057) := by
  rw [SparsePolynomial.eval_scale, eval_atom1057]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1058 : SparsePolynomial.Poly := [([10,16,16], 1)]
theorem eval_atom1058 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1058 = ((g 10) * (g 16) * (g 16)) := by
  norm_num [atom1058, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1058_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5852063040 : Int) atom1058) := by
  rw [SparsePolynomial.eval_scale, eval_atom1058]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 10) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1059 : SparsePolynomial.Poly := [([10,16,17], 1)]
theorem eval_atom1059 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1059 = ((g 10) * (g 16) * (g 17)) := by
  norm_num [atom1059, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1059_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19571583720 : Int) atom1059) := by
  rw [SparsePolynomial.eval_scale, eval_atom1059]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1060 : SparsePolynomial.Poly := [([10,17,17], 1)]
theorem eval_atom1060 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1060 = ((g 10) * (g 17) * (g 17)) := by
  norm_num [atom1060, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1060_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12795525120 : Int) atom1060) := by
  rw [SparsePolynomial.eval_scale, eval_atom1060]
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 10) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1061 : SparsePolynomial.Poly := [([11,11,11], 1)]
theorem eval_atom1061 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1061 = ((g 11) * (g 11) * (g 11)) := by
  norm_num [atom1061, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1061_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (352235520 : Int) atom1061) := by
  rw [SparsePolynomial.eval_scale, eval_atom1061]
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 11) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1062 : SparsePolynomial.Poly := [([11,11,14], 1)]
theorem eval_atom1062 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1062 = ((g 11) * (g 11) * (g 14)) := by
  norm_num [atom1062, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1062_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1293593040 : Int) atom1062) := by
  rw [SparsePolynomial.eval_scale, eval_atom1062]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1063 : SparsePolynomial.Poly := [([11,11,15], 1)]
theorem eval_atom1063 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1063 = ((g 11) * (g 11) * (g 15)) := by
  norm_num [atom1063, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1063_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1033482240 : Int) atom1063) := by
  rw [SparsePolynomial.eval_scale, eval_atom1063]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1064 : SparsePolynomial.Poly := [([11,11,17], 1)]
theorem eval_atom1064 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1064 = ((g 11) * (g 11) * (g 17)) := by
  norm_num [atom1064, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1064_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2519838720 : Int) atom1064) := by
  rw [SparsePolynomial.eval_scale, eval_atom1064]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1065 : SparsePolynomial.Poly := [([11,12,13], 1)]
theorem eval_atom1065 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1065 = ((g 11) * (g 12) * (g 13)) := by
  norm_num [atom1065, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1065_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (974776320 : Int) atom1065) := by
  rw [SparsePolynomial.eval_scale, eval_atom1065]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1066 : SparsePolynomial.Poly := [([11,12,14], 1)]
theorem eval_atom1066 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1066 = ((g 11) * (g 12) * (g 14)) := by
  norm_num [atom1066, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1066_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8131347360 : Int) atom1066) := by
  rw [SparsePolynomial.eval_scale, eval_atom1066]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1067 : SparsePolynomial.Poly := [([11,12,15], 1)]
theorem eval_atom1067 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1067 = ((g 11) * (g 12) * (g 15)) := by
  norm_num [atom1067, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1067_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9358755840 : Int) atom1067) := by
  rw [SparsePolynomial.eval_scale, eval_atom1067]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1068 : SparsePolynomial.Poly := [([11,12,16], 1)]
theorem eval_atom1068 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1068 = ((g 11) * (g 12) * (g 16)) := by
  norm_num [atom1068, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1068_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6750535680 : Int) atom1068) := by
  rw [SparsePolynomial.eval_scale, eval_atom1068]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1069 : SparsePolynomial.Poly := [([11,12,17], 1)]
theorem eval_atom1069 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1069 = ((g 11) * (g 12) * (g 17)) := by
  norm_num [atom1069, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1069_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14862597120 : Int) atom1069) := by
  rw [SparsePolynomial.eval_scale, eval_atom1069]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1070 : SparsePolynomial.Poly := [([11,13,13], 1)]
theorem eval_atom1070 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1070 = ((g 11) * (g 13) * (g 13)) := by
  norm_num [atom1070, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1070_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (276369408 : Int) atom1070) := by
  rw [SparsePolynomial.eval_scale, eval_atom1070]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 11) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1071 : SparsePolynomial.Poly := [([11,13,14], 1)]
theorem eval_atom1071 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1071 = ((g 11) * (g 13) * (g 14)) := by
  norm_num [atom1071, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1071_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7144572600 : Int) atom1071) := by
  rw [SparsePolynomial.eval_scale, eval_atom1071]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1072 : SparsePolynomial.Poly := [([11,13,15], 1)]
theorem eval_atom1072 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1072 = ((g 11) * (g 13) * (g 15)) := by
  norm_num [atom1072, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1072_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10606740480 : Int) atom1072) := by
  rw [SparsePolynomial.eval_scale, eval_atom1072]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1073 : SparsePolynomial.Poly := [([11,13,16], 1)]
theorem eval_atom1073 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1073 = ((g 11) * (g 13) * (g 16)) := by
  norm_num [atom1073, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1073_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10354176000 : Int) atom1073) := by
  rw [SparsePolynomial.eval_scale, eval_atom1073]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1074 : SparsePolynomial.Poly := [([11,13,17], 1)]
theorem eval_atom1074 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1074 = ((g 11) * (g 13) * (g 17)) := by
  norm_num [atom1074, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1074_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15571422720 : Int) atom1074) := by
  rw [SparsePolynomial.eval_scale, eval_atom1074]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1075 : SparsePolynomial.Poly := [([11,14,14], 1)]
theorem eval_atom1075 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1075 = ((g 11) * (g 14) * (g 14)) := by
  norm_num [atom1075, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1075_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6980067000 : Int) atom1075) := by
  rw [SparsePolynomial.eval_scale, eval_atom1075]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 11) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1076 : SparsePolynomial.Poly := [([11,14,15], 1)]
theorem eval_atom1076 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1076 = ((g 11) * (g 14) * (g 15)) := by
  norm_num [atom1076, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1076_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14752472760 : Int) atom1076) := by
  rw [SparsePolynomial.eval_scale, eval_atom1076]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1077 : SparsePolynomial.Poly := [([11,14,16], 1)]
theorem eval_atom1077 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1077 = ((g 11) * (g 14) * (g 16)) := by
  norm_num [atom1077, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1077_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15437203920 : Int) atom1077) := by
  rw [SparsePolynomial.eval_scale, eval_atom1077]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1078 : SparsePolynomial.Poly := [([11,14,17], 1)]
theorem eval_atom1078 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1078 = ((g 11) * (g 14) * (g 17)) := by
  norm_num [atom1078, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1078_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21398112720 : Int) atom1078) := by
  rw [SparsePolynomial.eval_scale, eval_atom1078]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1079 : SparsePolynomial.Poly := [([11,15,15], 1)]
theorem eval_atom1079 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1079 = ((g 11) * (g 15) * (g 15)) := by
  norm_num [atom1079, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1079_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6526033920 : Int) atom1079) := by
  rw [SparsePolynomial.eval_scale, eval_atom1079]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 11) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1080 : SparsePolynomial.Poly := [([11,15,16], 1)]
theorem eval_atom1080 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1080 = ((g 11) * (g 15) * (g 16)) := by
  norm_num [atom1080, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1080_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16063488000 : Int) atom1080) := by
  rw [SparsePolynomial.eval_scale, eval_atom1080]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1081 : SparsePolynomial.Poly := [([11,15,17], 1)]
theorem eval_atom1081 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1081 = ((g 11) * (g 15) * (g 17)) := by
  norm_num [atom1081, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1081_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22628229120 : Int) atom1081) := by
  rw [SparsePolynomial.eval_scale, eval_atom1081]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1082 : SparsePolynomial.Poly := [([11,16,16], 1)]
theorem eval_atom1082 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1082 = ((g 11) * (g 16) * (g 16)) := by
  norm_num [atom1082, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1082_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8291082240 : Int) atom1082) := by
  rw [SparsePolynomial.eval_scale, eval_atom1082]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 11) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1083 : SparsePolynomial.Poly := [([11,16,17], 1)]
theorem eval_atom1083 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1083 = ((g 11) * (g 16) * (g 17)) := by
  norm_num [atom1083, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1083_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23750737920 : Int) atom1083) := by
  rw [SparsePolynomial.eval_scale, eval_atom1083]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1084 : SparsePolynomial.Poly := [([11,17,17], 1)]
theorem eval_atom1084 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1084 = ((g 11) * (g 17) * (g 17)) := by
  norm_num [atom1084, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1084_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14213283840 : Int) atom1084) := by
  rw [SparsePolynomial.eval_scale, eval_atom1084]
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 11) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1085 : SparsePolynomial.Poly := [([12,12,12], 1)]
theorem eval_atom1085 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1085 = ((g 12) * (g 12) * (g 12)) := by
  norm_num [atom1085, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1085_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (173537280 : Int) atom1085) := by
  rw [SparsePolynomial.eval_scale, eval_atom1085]
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 12) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1086 : SparsePolynomial.Poly := [([12,12,13], 1)]
theorem eval_atom1086 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1086 = ((g 12) * (g 12) * (g 13)) := by
  norm_num [atom1086, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1086_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1318625280 : Int) atom1086) := by
  rw [SparsePolynomial.eval_scale, eval_atom1086]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 12) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1087 : SparsePolynomial.Poly := [([12,12,14], 1)]
theorem eval_atom1087 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1087 = ((g 12) * (g 12) * (g 14)) := by
  norm_num [atom1087, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1087_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5562352080 : Int) atom1087) := by
  rw [SparsePolynomial.eval_scale, eval_atom1087]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1088 : SparsePolynomial.Poly := [([12,12,15], 1)]
theorem eval_atom1088 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1088 = ((g 12) * (g 12) * (g 15)) := by
  norm_num [atom1088, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1088_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6467973120 : Int) atom1088) := by
  rw [SparsePolynomial.eval_scale, eval_atom1088]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 12) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1089 : SparsePolynomial.Poly := [([12,12,16], 1)]
theorem eval_atom1089 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1089 = ((g 12) * (g 12) * (g 16)) := by
  norm_num [atom1089, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1089_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3712665600 : Int) atom1089) := by
  rw [SparsePolynomial.eval_scale, eval_atom1089]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1090 : SparsePolynomial.Poly := [([12,12,17], 1)]
theorem eval_atom1090 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1090 = ((g 12) * (g 12) * (g 17)) := by
  norm_num [atom1090, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1090_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8064000000 : Int) atom1090) := by
  rw [SparsePolynomial.eval_scale, eval_atom1090]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1091 : SparsePolynomial.Poly := [([12,13,13], 1)]
theorem eval_atom1091 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1091 = ((g 12) * (g 13) * (g 13)) := by
  norm_num [atom1091, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1091_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (1465454592 : Int) atom1091) := by
  rw [SparsePolynomial.eval_scale, eval_atom1091]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 12) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1092 : SparsePolynomial.Poly := [([12,13,14], 1)]
theorem eval_atom1092 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1092 = ((g 12) * (g 13) * (g 14)) := by
  norm_num [atom1092, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1092_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10728214200 : Int) atom1092) := by
  rw [SparsePolynomial.eval_scale, eval_atom1092]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1093 : SparsePolynomial.Poly := [([12,13,15], 1)]
theorem eval_atom1093 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1093 = ((g 12) * (g 13) * (g 15)) := by
  norm_num [atom1093, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1093_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14916464640 : Int) atom1093) := by
  rw [SparsePolynomial.eval_scale, eval_atom1093]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 12) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1094 : SparsePolynomial.Poly := [([12,13,16], 1)]
theorem eval_atom1094 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1094 = ((g 12) * (g 13) * (g 16)) := by
  norm_num [atom1094, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1094_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11836661760 : Int) atom1094) := by
  rw [SparsePolynomial.eval_scale, eval_atom1094]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1095 : SparsePolynomial.Poly := [([12,13,17], 1)]
theorem eval_atom1095 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1095 = ((g 12) * (g 13) * (g 17)) := by
  norm_num [atom1095, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1095_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17640161280 : Int) atom1095) := by
  rw [SparsePolynomial.eval_scale, eval_atom1095]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1096 : SparsePolynomial.Poly := [([12,14,14], 1)]
theorem eval_atom1096 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1096 = ((g 12) * (g 14) * (g 14)) := by
  norm_num [atom1096, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1096_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8611575480 : Int) atom1096) := by
  rw [SparsePolynomial.eval_scale, eval_atom1096]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 12) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1097 : SparsePolynomial.Poly := [([12,14,15], 1)]
theorem eval_atom1097 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1097 = ((g 12) * (g 14) * (g 15)) := by
  norm_num [atom1097, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1097_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18512232120 : Int) atom1097) := by
  rw [SparsePolynomial.eval_scale, eval_atom1097]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 12) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1098 : SparsePolynomial.Poly := [([12,14,16], 1)]
theorem eval_atom1098 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1098 = ((g 12) * (g 14) * (g 16)) := by
  norm_num [atom1098, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1098_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16140384720 : Int) atom1098) := by
  rw [SparsePolynomial.eval_scale, eval_atom1098]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1099 : SparsePolynomial.Poly := [([12,14,17], 1)]
theorem eval_atom1099 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1099 = ((g 12) * (g 14) * (g 17)) := by
  norm_num [atom1099, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1099_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15706609200 : Int) atom1099) := by
  rw [SparsePolynomial.eval_scale, eval_atom1099]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1100 : SparsePolynomial.Poly := [([12,15,15], 1)]
theorem eval_atom1100 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1100 = ((g 12) * (g 15) * (g 15)) := by
  norm_num [atom1100, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1100_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8550420480 : Int) atom1100) := by
  rw [SparsePolynomial.eval_scale, eval_atom1100]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 12) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1101 : SparsePolynomial.Poly := [([12,15,16], 1)]
theorem eval_atom1101 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1101 = ((g 12) * (g 15) * (g 16)) := by
  norm_num [atom1101, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1101_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17106001920 : Int) atom1101) := by
  rw [SparsePolynomial.eval_scale, eval_atom1101]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1102 : SparsePolynomial.Poly := [([12,15,17], 1)]
theorem eval_atom1102 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1102 = ((g 12) * (g 15) * (g 17)) := by
  norm_num [atom1102, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1102_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17111162880 : Int) atom1102) := by
  rw [SparsePolynomial.eval_scale, eval_atom1102]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1103 : SparsePolynomial.Poly := [([12,16,16], 1)]
theorem eval_atom1103 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1103 = ((g 12) * (g 16) * (g 16)) := by
  norm_num [atom1103, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1103_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8982005760 : Int) atom1103) := by
  rw [SparsePolynomial.eval_scale, eval_atom1103]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 12) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1104 : SparsePolynomial.Poly := [([12,16,17], 1)]
theorem eval_atom1104 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1104 = ((g 12) * (g 16) * (g 17)) := by
  norm_num [atom1104, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1104_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18623324160 : Int) atom1104) := by
  rw [SparsePolynomial.eval_scale, eval_atom1104]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1105 : SparsePolynomial.Poly := [([12,17,17], 1)]
theorem eval_atom1105 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1105 = ((g 12) * (g 17) * (g 17)) := by
  norm_num [atom1105, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1105_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8291082240 : Int) atom1105) := by
  rw [SparsePolynomial.eval_scale, eval_atom1105]
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 12) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1106 : SparsePolynomial.Poly := [([13,13,14], 1)]
theorem eval_atom1106 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1106 = ((g 13) * (g 13) * (g 14)) := by
  norm_num [atom1106, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1106_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3449713896 : Int) atom1106) := by
  rw [SparsePolynomial.eval_scale, eval_atom1106]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 13) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1107 : SparsePolynomial.Poly := [([13,13,15], 1)]
theorem eval_atom1107 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1107 = ((g 13) * (g 13) * (g 15)) := by
  norm_num [atom1107, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1107_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6428749824 : Int) atom1107) := by
  rw [SparsePolynomial.eval_scale, eval_atom1107]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 13) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1108 : SparsePolynomial.Poly := [([13,13,16], 1)]
theorem eval_atom1108 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1108 = ((g 13) * (g 13) * (g 16)) := by
  norm_num [atom1108, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1108_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5600931840 : Int) atom1108) := by
  rw [SparsePolynomial.eval_scale, eval_atom1108]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1109 : SparsePolynomial.Poly := [([13,13,17], 1)]
theorem eval_atom1109 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1109 = ((g 13) * (g 13) * (g 17)) := by
  norm_num [atom1109, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1109_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8326434816 : Int) atom1109) := by
  rw [SparsePolynomial.eval_scale, eval_atom1109]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1110 : SparsePolynomial.Poly := [([13,14,14], 1)]
theorem eval_atom1110 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1110 = ((g 13) * (g 14) * (g 14)) := by
  norm_num [atom1110, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1110_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (6743566800 : Int) atom1110) := by
  rw [SparsePolynomial.eval_scale, eval_atom1110]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 13) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1111 : SparsePolynomial.Poly := [([13,14,15], 1)]
theorem eval_atom1111 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1111 = ((g 13) * (g 14) * (g 15)) := by
  norm_num [atom1111, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1111_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16995813840 : Int) atom1111) := by
  rw [SparsePolynomial.eval_scale, eval_atom1111]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 13) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1112 : SparsePolynomial.Poly := [([13,14,16], 1)]
theorem eval_atom1112 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1112 = ((g 13) * (g 14) * (g 16)) := by
  norm_num [atom1112, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1112_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16843565520 : Int) atom1112) := by
  rw [SparsePolynomial.eval_scale, eval_atom1112]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1113 : SparsePolynomial.Poly := [([13,14,17], 1)]
theorem eval_atom1113 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1113 = ((g 13) * (g 14) * (g 17)) := by
  norm_num [atom1113, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1113_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16906532400 : Int) atom1113) := by
  rw [SparsePolynomial.eval_scale, eval_atom1113]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1114 : SparsePolynomial.Poly := [([13,15,15], 1)]
theorem eval_atom1114 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1114 = ((g 13) * (g 15) * (g 15)) := by
  norm_num [atom1114, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1114_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8798146560 : Int) atom1114) := by
  rw [SparsePolynomial.eval_scale, eval_atom1114]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 13) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1115 : SparsePolynomial.Poly := [([13,15,16], 1)]
theorem eval_atom1115 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1115 = ((g 13) * (g 15) * (g 16)) := by
  norm_num [atom1115, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1115_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18148515840 : Int) atom1115) := by
  rw [SparsePolynomial.eval_scale, eval_atom1115]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1116 : SparsePolynomial.Poly := [([13,15,17], 1)]
theorem eval_atom1116 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1116 = ((g 13) * (g 15) * (g 17)) := by
  norm_num [atom1116, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1116_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18700738560 : Int) atom1116) := by
  rw [SparsePolynomial.eval_scale, eval_atom1116]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1117 : SparsePolynomial.Poly := [([13,16,16], 1)]
theorem eval_atom1117 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1117 = ((g 13) * (g 16) * (g 16)) := by
  norm_num [atom1117, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1117_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9672929280 : Int) atom1117) := by
  rw [SparsePolynomial.eval_scale, eval_atom1117]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 13) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1118 : SparsePolynomial.Poly := [([13,16,17], 1)]
theorem eval_atom1118 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1118 = ((g 13) * (g 16) * (g 17)) := by
  norm_num [atom1118, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1118_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20602552320 : Int) atom1118) := by
  rw [SparsePolynomial.eval_scale, eval_atom1118]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1119 : SparsePolynomial.Poly := [([13,17,17], 1)]
theorem eval_atom1119 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1119 = ((g 13) * (g 17) * (g 17)) := by
  norm_num [atom1119, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1119_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9475522560 : Int) atom1119) := by
  rw [SparsePolynomial.eval_scale, eval_atom1119]
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 13) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1120 : SparsePolynomial.Poly := [([14,14,14], 1)]
theorem eval_atom1120 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1120 = ((g 14) * (g 14) * (g 14)) := by
  norm_num [atom1120, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1120_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2773757160 : Int) atom1120) := by
  rw [SparsePolynomial.eval_scale, eval_atom1120]
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 14) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1121 : SparsePolynomial.Poly := [([14,14,15], 1)]
theorem eval_atom1121 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1121 = ((g 14) * (g 14) * (g 15)) := by
  norm_num [atom1121, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1121_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8601126120 : Int) atom1121) := by
  rw [SparsePolynomial.eval_scale, eval_atom1121]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 14) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1122 : SparsePolynomial.Poly := [([14,14,16], 1)]
theorem eval_atom1122 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1122 = ((g 14) * (g 14) * (g 16)) := by
  norm_num [atom1122, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1122_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8773373160 : Int) atom1122) := by
  rw [SparsePolynomial.eval_scale, eval_atom1122]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 14) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1123 : SparsePolynomial.Poly := [([14,14,17], 1)]
theorem eval_atom1123 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1123 = ((g 14) * (g 14) * (g 17)) := by
  norm_num [atom1123, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1123_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (5607514440 : Int) atom1123) := by
  rw [SparsePolynomial.eval_scale, eval_atom1123]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1124 : SparsePolynomial.Poly := [([14,15,15], 1)]
theorem eval_atom1124 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1124 = ((g 14) * (g 15) * (g 15)) := by
  norm_num [atom1124, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1124_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9045872640 : Int) atom1124) := by
  rw [SparsePolynomial.eval_scale, eval_atom1124]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 14) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1125 : SparsePolynomial.Poly := [([14,15,16], 1)]
theorem eval_atom1125 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1125 = ((g 14) * (g 15) * (g 16)) := by
  norm_num [atom1125, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1125_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19191029760 : Int) atom1125) := by
  rw [SparsePolynomial.eval_scale, eval_atom1125]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 14) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1126 : SparsePolynomial.Poly := [([14,15,17], 1)]
theorem eval_atom1126 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1126 = ((g 14) * (g 15) * (g 17)) := by
  norm_num [atom1126, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1126_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13398887520 : Int) atom1126) := by
  rw [SparsePolynomial.eval_scale, eval_atom1126]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1127 : SparsePolynomial.Poly := [([14,16,16], 1)]
theorem eval_atom1127 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1127 = ((g 14) * (g 16) * (g 16)) := by
  norm_num [atom1127, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1127_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10363852800 : Int) atom1127) := by
  rw [SparsePolynomial.eval_scale, eval_atom1127]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 14) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1128 : SparsePolynomial.Poly := [([14,16,17], 1)]
theorem eval_atom1128 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1128 = ((g 14) * (g 16) * (g 17)) := by
  norm_num [atom1128, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1128_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15690353760 : Int) atom1128) := by
  rw [SparsePolynomial.eval_scale, eval_atom1128]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1129 : SparsePolynomial.Poly := [([14,17,17], 1)]
theorem eval_atom1129 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1129 = ((g 14) * (g 17) * (g 17)) := by
  norm_num [atom1129, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1129_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3768536160 : Int) atom1129) := by
  rw [SparsePolynomial.eval_scale, eval_atom1129]
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 14) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1130 : SparsePolynomial.Poly := [([15,15,15], 1)]
theorem eval_atom1130 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1130 = ((g 15) * (g 15) * (g 15)) := by
  norm_num [atom1130, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1130_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3097866240 : Int) atom1130) := by
  rw [SparsePolynomial.eval_scale, eval_atom1130]
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 15) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1131 : SparsePolynomial.Poly := [([15,15,16], 1)]
theorem eval_atom1131 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1131 = ((g 15) * (g 15) * (g 16)) := by
  norm_num [atom1131, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1131_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10116771840 : Int) atom1131) := by
  rw [SparsePolynomial.eval_scale, eval_atom1131]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 15) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1132 : SparsePolynomial.Poly := [([15,15,17], 1)]
theorem eval_atom1132 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1132 = ((g 15) * (g 15) * (g 17)) := by
  norm_num [atom1132, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1132_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7386624000 : Int) atom1132) := by
  rw [SparsePolynomial.eval_scale, eval_atom1132]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 15) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1133 : SparsePolynomial.Poly := [([15,16,16], 1)]
theorem eval_atom1133 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1133 = ((g 15) * (g 16) * (g 16)) := by
  norm_num [atom1133, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1133_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (11054776320 : Int) atom1133) := by
  rw [SparsePolynomial.eval_scale, eval_atom1133]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 15) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1134 : SparsePolynomial.Poly := [([15,16,17], 1)]
theorem eval_atom1134 (g : Fin 18 → ℝ) : SparsePolynomial.eval (variables g) atom1134 = ((g 15) * (g 16) * (g 17)) := by
  norm_num [atom1134, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1134_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17454366720 : Int) atom1134) := by
  rw [SparsePolynomial.eval_scale, eval_atom1134]
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 15) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block014 : SparsePolynomial.Poly := [([10,15,15], 6248911920), ([10,15,16], 13592934960), ([10,15,17], 20673746760), ([10,16,16], 5852063040), ([10,16,17], 19571583720), ([10,17,17], 12795525120), ([11,11,11], 352235520), ([11,11,14], 1293593040), ([11,11,15], 1033482240), ([11,11,17], 2519838720), ([11,12,13], 974776320), ([11,12,14], 8131347360), ([11,12,15], 9358755840), ([11,12,16], 6750535680), ([11,12,17], 14862597120), ([11,13,13], 276369408), ([11,13,14], 7144572600), ([11,13,15], 10606740480), ([11,13,16], 10354176000), ([11,13,17], 15571422720), ([11,14,14], 6980067000), ([11,14,15], 14752472760), ([11,14,16], 15437203920), ([11,14,17], 21398112720), ([11,15,15], 6526033920), ([11,15,16], 16063488000), ([11,15,17], 22628229120), ([11,16,16], 8291082240), ([11,16,17], 23750737920), ([11,17,17], 14213283840), ([12,12,12], 173537280), ([12,12,13], 1318625280), ([12,12,14], 5562352080), ([12,12,15], 6467973120), ([12,12,16], 3712665600), ([12,12,17], 8064000000), ([12,13,13], 1465454592), ([12,13,14], 10728214200), ([12,13,15], 14916464640), ([12,13,16], 11836661760), ([12,13,17], 17640161280), ([12,14,14], 8611575480), ([12,14,15], 18512232120), ([12,14,16], 16140384720), ([12,14,17], 15706609200), ([12,15,15], 8550420480), ([12,15,16], 17106001920), ([12,15,17], 17111162880), ([12,16,16], 8982005760), ([12,16,17], 18623324160), ([12,17,17], 8291082240), ([13,13,14], 3449713896), ([13,13,15], 6428749824), ([13,13,16], 5600931840), ([13,13,17], 8326434816), ([13,14,14], 6743566800), ([13,14,15], 16995813840), ([13,14,16], 16843565520), ([13,14,17], 16906532400), ([13,15,15], 8798146560), ([13,15,16], 18148515840), ([13,15,17], 18700738560), ([13,16,16], 9672929280), ([13,16,17], 20602552320), ([13,17,17], 9475522560), ([14,14,14], 2773757160), ([14,14,15], 8601126120), ([14,14,16], 8773373160), ([14,14,17], 5607514440), ([14,15,15], 9045872640), ([14,15,16], 19191029760), ([14,15,17], 13398887520), ([14,16,16], 10363852800), ([14,16,17], 15690353760), ([14,17,17], 3768536160), ([15,15,15], 3097866240), ([15,15,16], 10116771840), ([15,15,17], 7386624000), ([15,16,16], 11054776320), ([15,16,17], 17454366720)]
theorem block014_data : block014 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6248911920 : Int) atom1055) (SparsePolynomial.scale (13592934960 : Int) atom1056)) (SparsePolynomial.merge (SparsePolynomial.scale (20673746760 : Int) atom1057) (SparsePolynomial.merge (SparsePolynomial.scale (5852063040 : Int) atom1058) (SparsePolynomial.scale (19571583720 : Int) atom1059)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (12795525120 : Int) atom1060) (SparsePolynomial.scale (352235520 : Int) atom1061)) (SparsePolynomial.merge (SparsePolynomial.scale (1293593040 : Int) atom1062) (SparsePolynomial.merge (SparsePolynomial.scale (1033482240 : Int) atom1063) (SparsePolynomial.scale (2519838720 : Int) atom1064))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (974776320 : Int) atom1065) (SparsePolynomial.scale (8131347360 : Int) atom1066)) (SparsePolynomial.merge (SparsePolynomial.scale (9358755840 : Int) atom1067) (SparsePolynomial.merge (SparsePolynomial.scale (6750535680 : Int) atom1068) (SparsePolynomial.scale (14862597120 : Int) atom1069)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (276369408 : Int) atom1070) (SparsePolynomial.scale (7144572600 : Int) atom1071)) (SparsePolynomial.merge (SparsePolynomial.scale (10606740480 : Int) atom1072) (SparsePolynomial.merge (SparsePolynomial.scale (10354176000 : Int) atom1073) (SparsePolynomial.scale (15571422720 : Int) atom1074)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6980067000 : Int) atom1075) (SparsePolynomial.scale (14752472760 : Int) atom1076)) (SparsePolynomial.merge (SparsePolynomial.scale (15437203920 : Int) atom1077) (SparsePolynomial.merge (SparsePolynomial.scale (21398112720 : Int) atom1078) (SparsePolynomial.scale (6526033920 : Int) atom1079)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (16063488000 : Int) atom1080) (SparsePolynomial.scale (22628229120 : Int) atom1081)) (SparsePolynomial.merge (SparsePolynomial.scale (8291082240 : Int) atom1082) (SparsePolynomial.merge (SparsePolynomial.scale (23750737920 : Int) atom1083) (SparsePolynomial.scale (14213283840 : Int) atom1084))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (173537280 : Int) atom1085) (SparsePolynomial.scale (1318625280 : Int) atom1086)) (SparsePolynomial.merge (SparsePolynomial.scale (5562352080 : Int) atom1087) (SparsePolynomial.merge (SparsePolynomial.scale (6467973120 : Int) atom1088) (SparsePolynomial.scale (3712665600 : Int) atom1089)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8064000000 : Int) atom1090) (SparsePolynomial.scale (1465454592 : Int) atom1091)) (SparsePolynomial.merge (SparsePolynomial.scale (10728214200 : Int) atom1092) (SparsePolynomial.merge (SparsePolynomial.scale (14916464640 : Int) atom1093) (SparsePolynomial.scale (11836661760 : Int) atom1094))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (17640161280 : Int) atom1095) (SparsePolynomial.scale (8611575480 : Int) atom1096)) (SparsePolynomial.merge (SparsePolynomial.scale (18512232120 : Int) atom1097) (SparsePolynomial.merge (SparsePolynomial.scale (16140384720 : Int) atom1098) (SparsePolynomial.scale (15706609200 : Int) atom1099)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8550420480 : Int) atom1100) (SparsePolynomial.scale (17106001920 : Int) atom1101)) (SparsePolynomial.merge (SparsePolynomial.scale (17111162880 : Int) atom1102) (SparsePolynomial.merge (SparsePolynomial.scale (8982005760 : Int) atom1103) (SparsePolynomial.scale (18623324160 : Int) atom1104))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (8291082240 : Int) atom1105) (SparsePolynomial.scale (3449713896 : Int) atom1106)) (SparsePolynomial.merge (SparsePolynomial.scale (6428749824 : Int) atom1107) (SparsePolynomial.merge (SparsePolynomial.scale (5600931840 : Int) atom1108) (SparsePolynomial.scale (8326434816 : Int) atom1109)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6743566800 : Int) atom1110) (SparsePolynomial.scale (16995813840 : Int) atom1111)) (SparsePolynomial.merge (SparsePolynomial.scale (16843565520 : Int) atom1112) (SparsePolynomial.merge (SparsePolynomial.scale (16906532400 : Int) atom1113) (SparsePolynomial.scale (8798146560 : Int) atom1114)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (18148515840 : Int) atom1115) (SparsePolynomial.scale (18700738560 : Int) atom1116)) (SparsePolynomial.merge (SparsePolynomial.scale (9672929280 : Int) atom1117) (SparsePolynomial.merge (SparsePolynomial.scale (20602552320 : Int) atom1118) (SparsePolynomial.scale (9475522560 : Int) atom1119)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2773757160 : Int) atom1120) (SparsePolynomial.scale (8601126120 : Int) atom1121)) (SparsePolynomial.merge (SparsePolynomial.scale (8773373160 : Int) atom1122) (SparsePolynomial.merge (SparsePolynomial.scale (5607514440 : Int) atom1123) (SparsePolynomial.scale (9045872640 : Int) atom1124))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19191029760 : Int) atom1125) (SparsePolynomial.scale (13398887520 : Int) atom1126)) (SparsePolynomial.merge (SparsePolynomial.scale (10363852800 : Int) atom1127) (SparsePolynomial.merge (SparsePolynomial.scale (15690353760 : Int) atom1128) (SparsePolynomial.scale (3768536160 : Int) atom1129)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3097866240 : Int) atom1130) (SparsePolynomial.scale (10116771840 : Int) atom1131)) (SparsePolynomial.merge (SparsePolynomial.scale (7386624000 : Int) atom1132) (SparsePolynomial.merge (SparsePolynomial.scale (11054776320 : Int) atom1133) (SparsePolynomial.scale (17454366720 : Int) atom1134)))))))) := by decide +kernel
theorem block014_nonneg (g : Fin 18 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block014 := by
  rw [block014_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1055_nonneg g hg hA hB) (atom1056_nonneg g hg hA hB)) (add_nonneg (atom1057_nonneg g hg hA hB) (add_nonneg (atom1058_nonneg g hg hA hB) (atom1059_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1060_nonneg g hg hA hB) (atom1061_nonneg g hg hA hB)) (add_nonneg (atom1062_nonneg g hg hA hB) (add_nonneg (atom1063_nonneg g hg hA hB) (atom1064_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1065_nonneg g hg hA hB) (atom1066_nonneg g hg hA hB)) (add_nonneg (atom1067_nonneg g hg hA hB) (add_nonneg (atom1068_nonneg g hg hA hB) (atom1069_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1070_nonneg g hg hA hB) (atom1071_nonneg g hg hA hB)) (add_nonneg (atom1072_nonneg g hg hA hB) (add_nonneg (atom1073_nonneg g hg hA hB) (atom1074_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1075_nonneg g hg hA hB) (atom1076_nonneg g hg hA hB)) (add_nonneg (atom1077_nonneg g hg hA hB) (add_nonneg (atom1078_nonneg g hg hA hB) (atom1079_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1080_nonneg g hg hA hB) (atom1081_nonneg g hg hA hB)) (add_nonneg (atom1082_nonneg g hg hA hB) (add_nonneg (atom1083_nonneg g hg hA hB) (atom1084_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1085_nonneg g hg hA hB) (atom1086_nonneg g hg hA hB)) (add_nonneg (atom1087_nonneg g hg hA hB) (add_nonneg (atom1088_nonneg g hg hA hB) (atom1089_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1090_nonneg g hg hA hB) (atom1091_nonneg g hg hA hB)) (add_nonneg (atom1092_nonneg g hg hA hB) (add_nonneg (atom1093_nonneg g hg hA hB) (atom1094_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1095_nonneg g hg hA hB) (atom1096_nonneg g hg hA hB)) (add_nonneg (atom1097_nonneg g hg hA hB) (add_nonneg (atom1098_nonneg g hg hA hB) (atom1099_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1100_nonneg g hg hA hB) (atom1101_nonneg g hg hA hB)) (add_nonneg (atom1102_nonneg g hg hA hB) (add_nonneg (atom1103_nonneg g hg hA hB) (atom1104_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1105_nonneg g hg hA hB) (atom1106_nonneg g hg hA hB)) (add_nonneg (atom1107_nonneg g hg hA hB) (add_nonneg (atom1108_nonneg g hg hA hB) (atom1109_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1110_nonneg g hg hA hB) (atom1111_nonneg g hg hA hB)) (add_nonneg (atom1112_nonneg g hg hA hB) (add_nonneg (atom1113_nonneg g hg hA hB) (atom1114_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1115_nonneg g hg hA hB) (atom1116_nonneg g hg hA hB)) (add_nonneg (atom1117_nonneg g hg hA hB) (add_nonneg (atom1118_nonneg g hg hA hB) (atom1119_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1120_nonneg g hg hA hB) (atom1121_nonneg g hg hA hB)) (add_nonneg (atom1122_nonneg g hg hA hB) (add_nonneg (atom1123_nonneg g hg hA hB) (atom1124_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1125_nonneg g hg hA hB) (atom1126_nonneg g hg hA hB)) (add_nonneg (atom1127_nonneg g hg hA hB) (add_nonneg (atom1128_nonneg g hg hA hB) (atom1129_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1130_nonneg g hg hA hB) (atom1131_nonneg g hg hA hB)) (add_nonneg (atom1132_nonneg g hg hA hB) (add_nonneg (atom1133_nonneg g hg hA hB) (atom1134_nonneg g hg hA hB))))))))

end APPT.Finite18
