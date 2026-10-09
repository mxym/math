import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1056 : SparsePolynomial.Poly := [([4,16,19], 1)]
theorem eval_atom1056 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1056 = ((g 4) * (g 16) * (g 19)) := by
  norm_num [atom1056, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1056_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40297587372000 : Int) atom1056) := by
  rw [SparsePolynomial.eval_scale, eval_atom1056]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1057 : SparsePolynomial.Poly := [([4,16,20], 1)]
theorem eval_atom1057 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1057 = ((g 4) * (g 16) * (g 20)) := by
  norm_num [atom1057, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1057_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45912704890500 : Int) atom1057) := by
  rw [SparsePolynomial.eval_scale, eval_atom1057]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1058 : SparsePolynomial.Poly := [([4,17,17], 1)]
theorem eval_atom1058 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1058 = ((g 4) * (g 17) * (g 17)) := by
  norm_num [atom1058, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1058_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39243222144000 : Int) atom1058) := by
  rw [SparsePolynomial.eval_scale, eval_atom1058]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1059 : SparsePolynomial.Poly := [([4,17,18], 1)]
theorem eval_atom1059 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1059 = ((g 4) * (g 17) * (g 18)) := by
  norm_num [atom1059, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1059_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (60042692026800 : Int) atom1059) := by
  rw [SparsePolynomial.eval_scale, eval_atom1059]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1060 : SparsePolynomial.Poly := [([4,17,19], 1)]
theorem eval_atom1060 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1060 = ((g 4) * (g 17) * (g 19)) := by
  norm_num [atom1060, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1060_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42753122622000 : Int) atom1060) := by
  rw [SparsePolynomial.eval_scale, eval_atom1060]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1061 : SparsePolynomial.Poly := [([4,17,20], 1)]
theorem eval_atom1061 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1061 = ((g 4) * (g 17) * (g 20)) := by
  norm_num [atom1061, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1061_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53503172881200 : Int) atom1061) := by
  rw [SparsePolynomial.eval_scale, eval_atom1061]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1062 : SparsePolynomial.Poly := [([4,18,18], 1)]
theorem eval_atom1062 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1062 = ((g 4) * (g 18) * (g 18)) := by
  norm_num [atom1062, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1062_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (16441201816200 : Int) atom1062) := by
  rw [SparsePolynomial.eval_scale, eval_atom1062]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1063 : SparsePolynomial.Poly := [([4,18,19], 1)]
theorem eval_atom1063 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1063 = ((g 4) * (g 18) * (g 19)) := by
  norm_num [atom1063, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1063_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21090286866600 : Int) atom1063) := by
  rw [SparsePolynomial.eval_scale, eval_atom1063]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1064 : SparsePolynomial.Poly := [([4,18,20], 1)]
theorem eval_atom1064 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1064 = ((g 4) * (g 18) * (g 20)) := by
  norm_num [atom1064, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1064_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31933858238100 : Int) atom1064) := by
  rw [SparsePolynomial.eval_scale, eval_atom1064]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1065 : SparsePolynomial.Poly := [([4,19,20], 1)]
theorem eval_atom1065 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1065 = ((g 4) * (g 19) * (g 20)) := by
  norm_num [atom1065, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1065_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8021538207900 : Int) atom1065) := by
  rw [SparsePolynomial.eval_scale, eval_atom1065]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg19 : 0 ≤ g 19 := hg 19
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 19) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1066 : SparsePolynomial.Poly := [([4,20,20], 1)]
theorem eval_atom1066 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1066 = ((g 4) * (g 20) * (g 20)) := by
  norm_num [atom1066, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1066_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10915331798700 : Int) atom1066) := by
  rw [SparsePolynomial.eval_scale, eval_atom1066]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 20) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1067 : SparsePolynomial.Poly := [([5,5,5], 1)]
theorem eval_atom1067 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1067 = ((g 5) * (g 5) * (g 5)) := by
  norm_num [atom1067, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1067_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2384168341248 : Int) atom1067) := by
  rw [SparsePolynomial.eval_scale, eval_atom1067]
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 5) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1068 : SparsePolynomial.Poly := [([5,5,6], 1)]
theorem eval_atom1068 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1068 = ((g 5) * (g 5) * (g 6)) := by
  norm_num [atom1068, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1068_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5099671524096 : Int) atom1068) := by
  rw [SparsePolynomial.eval_scale, eval_atom1068]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1069 : SparsePolynomial.Poly := [([5,5,7], 1)]
theorem eval_atom1069 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1069 = ((g 5) * (g 5) * (g 7)) := by
  norm_num [atom1069, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1069_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (475114087296 : Int) atom1069) := by
  rw [SparsePolynomial.eval_scale, eval_atom1069]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1070 : SparsePolynomial.Poly := [([5,5,9], 1)]
theorem eval_atom1070 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1070 = ((g 5) * (g 5) * (g 9)) := by
  norm_num [atom1070, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1070_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1116273312000 : Int) atom1070) := by
  rw [SparsePolynomial.eval_scale, eval_atom1070]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1071 : SparsePolynomial.Poly := [([5,5,10], 1)]
theorem eval_atom1071 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1071 = ((g 5) * (g 5) * (g 10)) := by
  norm_num [atom1071, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1071_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (773176320000 : Int) atom1071) := by
  rw [SparsePolynomial.eval_scale, eval_atom1071]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1072 : SparsePolynomial.Poly := [([5,5,11], 1)]
theorem eval_atom1072 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1072 = ((g 5) * (g 5) * (g 11)) := by
  norm_num [atom1072, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1072_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (847840896000 : Int) atom1072) := by
  rw [SparsePolynomial.eval_scale, eval_atom1072]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1073 : SparsePolynomial.Poly := [([5,5,12], 1)]
theorem eval_atom1073 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1073 = ((g 5) * (g 5) * (g 12)) := by
  norm_num [atom1073, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1073_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (261913478400 : Int) atom1073) := by
  rw [SparsePolynomial.eval_scale, eval_atom1073]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1074 : SparsePolynomial.Poly := [([5,5,15], 1)]
theorem eval_atom1074 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1074 = ((g 5) * (g 5) * (g 15)) := by
  norm_num [atom1074, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1074_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3749450450688 : Int) atom1074) := by
  rw [SparsePolynomial.eval_scale, eval_atom1074]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1075 : SparsePolynomial.Poly := [([5,6,6], 1)]
theorem eval_atom1075 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1075 = ((g 5) * (g 6) * (g 6)) := by
  norm_num [atom1075, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1075_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7321536603648 : Int) atom1075) := by
  rw [SparsePolynomial.eval_scale, eval_atom1075]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1076 : SparsePolynomial.Poly := [([5,6,7], 1)]
theorem eval_atom1076 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1076 = ((g 5) * (g 6) * (g 7)) := by
  norm_num [atom1076, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1076_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5911986468096 : Int) atom1076) := by
  rw [SparsePolynomial.eval_scale, eval_atom1076]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1077 : SparsePolynomial.Poly := [([5,6,8], 1)]
theorem eval_atom1077 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1077 = ((g 5) * (g 6) * (g 8)) := by
  norm_num [atom1077, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1077_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1501404912000 : Int) atom1077) := by
  rw [SparsePolynomial.eval_scale, eval_atom1077]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1078 : SparsePolynomial.Poly := [([5,6,11], 1)]
theorem eval_atom1078 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1078 = ((g 5) * (g 6) * (g 11)) := by
  norm_num [atom1078, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1078_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (158747500800 : Int) atom1078) := by
  rw [SparsePolynomial.eval_scale, eval_atom1078]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1079 : SparsePolynomial.Poly := [([5,6,13], 1)]
theorem eval_atom1079 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1079 = ((g 5) * (g 6) * (g 13)) := by
  norm_num [atom1079, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1079_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (165266438400 : Int) atom1079) := by
  rw [SparsePolynomial.eval_scale, eval_atom1079]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1080 : SparsePolynomial.Poly := [([5,6,14], 1)]
theorem eval_atom1080 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1080 = ((g 5) * (g 6) * (g 14)) := by
  norm_num [atom1080, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1080_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (592446355200 : Int) atom1080) := by
  rw [SparsePolynomial.eval_scale, eval_atom1080]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1081 : SparsePolynomial.Poly := [([5,6,15], 1)]
theorem eval_atom1081 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1081 = ((g 5) * (g 6) * (g 15)) := by
  norm_num [atom1081, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1081_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7715209569408 : Int) atom1081) := by
  rw [SparsePolynomial.eval_scale, eval_atom1081]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1082 : SparsePolynomial.Poly := [([5,6,17], 1)]
theorem eval_atom1082 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1082 = ((g 5) * (g 6) * (g 17)) := by
  norm_num [atom1082, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1082_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (666940934016 : Int) atom1082) := by
  rw [SparsePolynomial.eval_scale, eval_atom1082]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1083 : SparsePolynomial.Poly := [([5,6,18], 1)]
theorem eval_atom1083 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1083 = ((g 5) * (g 6) * (g 18)) := by
  norm_num [atom1083, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1083_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5982693393600 : Int) atom1083) := by
  rw [SparsePolynomial.eval_scale, eval_atom1083]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1084 : SparsePolynomial.Poly := [([5,6,19], 1)]
theorem eval_atom1084 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1084 = ((g 5) * (g 6) * (g 19)) := by
  norm_num [atom1084, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1084_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11433151537920 : Int) atom1084) := by
  rw [SparsePolynomial.eval_scale, eval_atom1084]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1085 : SparsePolynomial.Poly := [([5,6,20], 1)]
theorem eval_atom1085 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1085 = ((g 5) * (g 6) * (g 20)) := by
  norm_num [atom1085, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1085_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17685804276000 : Int) atom1085) := by
  rw [SparsePolynomial.eval_scale, eval_atom1085]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1086 : SparsePolynomial.Poly := [([5,7,7], 1)]
theorem eval_atom1086 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1086 = ((g 5) * (g 7) * (g 7)) := by
  norm_num [atom1086, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1086_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2176055048448 : Int) atom1086) := by
  rw [SparsePolynomial.eval_scale, eval_atom1086]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1087 : SparsePolynomial.Poly := [([5,7,8], 1)]
theorem eval_atom1087 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1087 = ((g 5) * (g 7) * (g 8)) := by
  norm_num [atom1087, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1087_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (977584809600 : Int) atom1087) := by
  rw [SparsePolynomial.eval_scale, eval_atom1087]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1088 : SparsePolynomial.Poly := [([5,7,11], 1)]
theorem eval_atom1088 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1088 = ((g 5) * (g 7) * (g 11)) := by
  norm_num [atom1088, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1088_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (676775635200 : Int) atom1088) := by
  rw [SparsePolynomial.eval_scale, eval_atom1088]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1089 : SparsePolynomial.Poly := [([5,7,12], 1)]
theorem eval_atom1089 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1089 = ((g 5) * (g 7) * (g 12)) := by
  norm_num [atom1089, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1089_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (777042201600 : Int) atom1089) := by
  rw [SparsePolynomial.eval_scale, eval_atom1089]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1090 : SparsePolynomial.Poly := [([5,7,13], 1)]
theorem eval_atom1090 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1090 = ((g 5) * (g 7) * (g 13)) := by
  norm_num [atom1090, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1090_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1201322707200 : Int) atom1090) := by
  rw [SparsePolynomial.eval_scale, eval_atom1090]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1091 : SparsePolynomial.Poly := [([5,7,14], 1)]
theorem eval_atom1091 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1091 = ((g 5) * (g 7) * (g 14)) := by
  norm_num [atom1091, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1091_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1887516691200 : Int) atom1091) := by
  rw [SparsePolynomial.eval_scale, eval_atom1091]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1092 : SparsePolynomial.Poly := [([5,7,15], 1)]
theorem eval_atom1092 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1092 = ((g 5) * (g 7) * (g 15)) := by
  norm_num [atom1092, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1092_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11268696014208 : Int) atom1092) := by
  rw [SparsePolynomial.eval_scale, eval_atom1092]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1093 : SparsePolynomial.Poly := [([5,7,16], 1)]
theorem eval_atom1093 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1093 = ((g 5) * (g 7) * (g 16)) := by
  norm_num [atom1093, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1093_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7360279591680 : Int) atom1093) := by
  rw [SparsePolynomial.eval_scale, eval_atom1093]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1094 : SparsePolynomial.Poly := [([5,7,17], 1)]
theorem eval_atom1094 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1094 = ((g 5) * (g 7) * (g 17)) := by
  norm_num [atom1094, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1094_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (12136953868416 : Int) atom1094) := by
  rw [SparsePolynomial.eval_scale, eval_atom1094]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1095 : SparsePolynomial.Poly := [([5,7,18], 1)]
theorem eval_atom1095 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1095 = ((g 5) * (g 7) * (g 18)) := by
  norm_num [atom1095, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1095_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18104289410880 : Int) atom1095) := by
  rw [SparsePolynomial.eval_scale, eval_atom1095]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1096 : SparsePolynomial.Poly := [([5,7,19], 1)]
theorem eval_atom1096 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1096 = ((g 5) * (g 7) * (g 19)) := by
  norm_num [atom1096, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1096_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25272405692928 : Int) atom1096) := by
  rw [SparsePolynomial.eval_scale, eval_atom1096]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1097 : SparsePolynomial.Poly := [([5,7,20], 1)]
theorem eval_atom1097 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1097 = ((g 5) * (g 7) * (g 20)) := by
  norm_num [atom1097, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1097_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32557609173600 : Int) atom1097) := by
  rw [SparsePolynomial.eval_scale, eval_atom1097]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1098 : SparsePolynomial.Poly := [([5,8,8], 1)]
theorem eval_atom1098 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1098 = ((g 5) * (g 8) * (g 8)) := by
  norm_num [atom1098, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1098_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2814314861952 : Int) atom1098) := by
  rw [SparsePolynomial.eval_scale, eval_atom1098]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1099 : SparsePolynomial.Poly := [([5,8,9], 1)]
theorem eval_atom1099 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1099 = ((g 5) * (g 8) * (g 9)) := by
  norm_num [atom1099, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1099_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4832741349504 : Int) atom1099) := by
  rw [SparsePolynomial.eval_scale, eval_atom1099]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1100 : SparsePolynomial.Poly := [([5,8,10], 1)]
theorem eval_atom1100 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1100 = ((g 5) * (g 8) * (g 10)) := by
  norm_num [atom1100, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1100_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4664575499904 : Int) atom1100) := by
  rw [SparsePolynomial.eval_scale, eval_atom1100]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1101 : SparsePolynomial.Poly := [([5,8,11], 1)]
theorem eval_atom1101 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1101 = ((g 5) * (g 8) * (g 11)) := by
  norm_num [atom1101, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1101_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5173185285504 : Int) atom1101) := by
  rw [SparsePolynomial.eval_scale, eval_atom1101]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1102 : SparsePolynomial.Poly := [([5,8,12], 1)]
theorem eval_atom1102 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1102 = ((g 5) * (g 8) * (g 12)) := by
  norm_num [atom1102, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1102_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4937120152704 : Int) atom1102) := by
  rw [SparsePolynomial.eval_scale, eval_atom1102]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1103 : SparsePolynomial.Poly := [([5,8,13], 1)]
theorem eval_atom1103 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1103 = ((g 5) * (g 8) * (g 13)) := by
  norm_num [atom1103, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1103_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5452248875904 : Int) atom1103) := by
  rw [SparsePolynomial.eval_scale, eval_atom1103]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1104 : SparsePolynomial.Poly := [([5,8,14], 1)]
theorem eval_atom1104 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1104 = ((g 5) * (g 8) * (g 14)) := by
  norm_num [atom1104, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1104_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6229291077504 : Int) atom1104) := by
  rw [SparsePolynomial.eval_scale, eval_atom1104]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1105 : SparsePolynomial.Poly := [([5,8,15], 1)]
theorem eval_atom1105 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1105 = ((g 5) * (g 8) * (g 15)) := by
  norm_num [atom1105, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1105_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15678311099904 : Int) atom1105) := by
  rw [SparsePolynomial.eval_scale, eval_atom1105]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1106 : SparsePolynomial.Poly := [([5,8,16], 1)]
theorem eval_atom1106 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1106 = ((g 5) * (g 8) * (g 16)) := by
  norm_num [atom1106, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1106_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13269277891440 : Int) atom1106) := by
  rw [SparsePolynomial.eval_scale, eval_atom1106]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 8) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1107 : SparsePolynomial.Poly := [([5,8,17], 1)]
theorem eval_atom1107 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1107 = ((g 5) * (g 8) * (g 17)) := by
  norm_num [atom1107, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1107_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19501256738304 : Int) atom1107) := by
  rw [SparsePolynomial.eval_scale, eval_atom1107]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1108 : SparsePolynomial.Poly := [([5,8,18], 1)]
theorem eval_atom1108 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1108 = ((g 5) * (g 8) * (g 18)) := by
  norm_num [atom1108, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1108_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25795167116112 : Int) atom1108) := by
  rw [SparsePolynomial.eval_scale, eval_atom1108]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1109 : SparsePolynomial.Poly := [([5,8,19], 1)]
theorem eval_atom1109 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1109 = ((g 5) * (g 8) * (g 19)) := by
  norm_num [atom1109, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1109_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (33886745865360 : Int) atom1109) := by
  rw [SparsePolynomial.eval_scale, eval_atom1109]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1110 : SparsePolynomial.Poly := [([5,8,20], 1)]
theorem eval_atom1110 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1110 = ((g 5) * (g 8) * (g 20)) := by
  norm_num [atom1110, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1110_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41978324614608 : Int) atom1110) := by
  rw [SparsePolynomial.eval_scale, eval_atom1110]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1111 : SparsePolynomial.Poly := [([5,9,9], 1)]
theorem eval_atom1111 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1111 = ((g 5) * (g 9) * (g 9)) := by
  norm_num [atom1111, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1111_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6031211588352 : Int) atom1111) := by
  rw [SparsePolynomial.eval_scale, eval_atom1111]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1112 : SparsePolynomial.Poly := [([5,9,10], 1)]
theorem eval_atom1112 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1112 = ((g 5) * (g 9) * (g 10)) := by
  norm_num [atom1112, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1112_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10283151170304 : Int) atom1112) := by
  rw [SparsePolynomial.eval_scale, eval_atom1112]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1113 : SparsePolynomial.Poly := [([5,9,11], 1)]
theorem eval_atom1113 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1113 = ((g 5) * (g 9) * (g 11)) := by
  norm_num [atom1113, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1113_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10455429256704 : Int) atom1113) := by
  rw [SparsePolynomial.eval_scale, eval_atom1113]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1114 : SparsePolynomial.Poly := [([5,9,12], 1)]
theorem eval_atom1114 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1114 = ((g 5) * (g 9) * (g 12)) := by
  norm_num [atom1114, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1114_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10569226408704 : Int) atom1114) := by
  rw [SparsePolynomial.eval_scale, eval_atom1114]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1115 : SparsePolynomial.Poly := [([5,9,13], 1)]
theorem eval_atom1115 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1115 = ((g 5) * (g 9) * (g 13)) := by
  norm_num [atom1115, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1115_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11007037499904 : Int) atom1115) := by
  rw [SparsePolynomial.eval_scale, eval_atom1115]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1116 : SparsePolynomial.Poly := [([5,9,14], 1)]
theorem eval_atom1116 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1116 = ((g 5) * (g 9) * (g 14)) := by
  norm_num [atom1116, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1116_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11706762069504 : Int) atom1116) := by
  rw [SparsePolynomial.eval_scale, eval_atom1116]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1117 : SparsePolynomial.Poly := [([5,9,15], 1)]
theorem eval_atom1117 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1117 = ((g 5) * (g 9) * (g 15)) := by
  norm_num [atom1117, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1117_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20771126872704 : Int) atom1117) := by
  rw [SparsePolynomial.eval_scale, eval_atom1117]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1118 : SparsePolynomial.Poly := [([5,9,16], 1)]
theorem eval_atom1118 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1118 = ((g 5) * (g 9) * (g 16)) := by
  norm_num [atom1118, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1118_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18331227015840 : Int) atom1118) := by
  rw [SparsePolynomial.eval_scale, eval_atom1118]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1119 : SparsePolynomial.Poly := [([5,9,17], 1)]
theorem eval_atom1119 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1119 = ((g 5) * (g 9) * (g 17)) := by
  norm_num [atom1119, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1119_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25882377554304 : Int) atom1119) := by
  rw [SparsePolynomial.eval_scale, eval_atom1119]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1120 : SparsePolynomial.Poly := [([5,9,18], 1)]
theorem eval_atom1120 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1120 = ((g 5) * (g 9) * (g 18)) := by
  norm_num [atom1120, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1120_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31092814209312 : Int) atom1120) := by
  rw [SparsePolynomial.eval_scale, eval_atom1120]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1121 : SparsePolynomial.Poly := [([5,9,19], 1)]
theorem eval_atom1121 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1121 = ((g 5) * (g 9) * (g 19)) := by
  norm_num [atom1121, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1121_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39549718769760 : Int) atom1121) := by
  rw [SparsePolynomial.eval_scale, eval_atom1121]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1122 : SparsePolynomial.Poly := [([5,9,20], 1)]
theorem eval_atom1122 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1122 = ((g 5) * (g 9) * (g 20)) := by
  norm_num [atom1122, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1122_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48097833974208 : Int) atom1122) := by
  rw [SparsePolynomial.eval_scale, eval_atom1122]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1123 : SparsePolynomial.Poly := [([5,10,10], 1)]
theorem eval_atom1123 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1123 = ((g 5) * (g 10) * (g 10)) := by
  norm_num [atom1123, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1123_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8264724682752 : Int) atom1123) := by
  rw [SparsePolynomial.eval_scale, eval_atom1123]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1124 : SparsePolynomial.Poly := [([5,10,11], 1)]
theorem eval_atom1124 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1124 = ((g 5) * (g 10) * (g 11)) := by
  norm_num [atom1124, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1124_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15692732354304 : Int) atom1124) := by
  rw [SparsePolynomial.eval_scale, eval_atom1124]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1125 : SparsePolynomial.Poly := [([5,10,12], 1)]
theorem eval_atom1125 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1125 = ((g 5) * (g 10) * (g 12)) := by
  norm_num [atom1125, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1125_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15133866107904 : Int) atom1125) := by
  rw [SparsePolynomial.eval_scale, eval_atom1125]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1126 : SparsePolynomial.Poly := [([5,10,13], 1)]
theorem eval_atom1126 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1126 = ((g 5) * (g 10) * (g 13)) := by
  norm_num [atom1126, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1126_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15326193717504 : Int) atom1126) := by
  rw [SparsePolynomial.eval_scale, eval_atom1126]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 5) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1127 : SparsePolynomial.Poly := [([5,10,14], 1)]
theorem eval_atom1127 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1127 = ((g 5) * (g 10) * (g 14)) := by
  norm_num [atom1127, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1127_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15780434805504 : Int) atom1127) := by
  rw [SparsePolynomial.eval_scale, eval_atom1127]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 5) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1128 : SparsePolynomial.Poly := [([5,10,15], 1)]
theorem eval_atom1128 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1128 = ((g 5) * (g 10) * (g 15)) := by
  norm_num [atom1128, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1128_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (25134257493504 : Int) atom1128) := by
  rw [SparsePolynomial.eval_scale, eval_atom1128]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 5) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1129 : SparsePolynomial.Poly := [([5,10,16], 1)]
theorem eval_atom1129 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1129 = ((g 5) * (g 10) * (g 16)) := by
  norm_num [atom1129, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1129_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22912538329440 : Int) atom1129) := by
  rw [SparsePolynomial.eval_scale, eval_atom1129]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 5) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1130 : SparsePolynomial.Poly := [([5,10,17], 1)]
theorem eval_atom1130 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1130 = ((g 5) * (g 10) * (g 17)) := by
  norm_num [atom1130, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1130_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32993183522304 : Int) atom1130) := by
  rw [SparsePolynomial.eval_scale, eval_atom1130]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 5) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1131 : SparsePolynomial.Poly := [([5,10,18], 1)]
theorem eval_atom1131 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1131 = ((g 5) * (g 10) * (g 18)) := by
  norm_num [atom1131, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1131_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (36268263201312 : Int) atom1131) := by
  rw [SparsePolynomial.eval_scale, eval_atom1131]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 5) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1132 : SparsePolynomial.Poly := [([5,10,19], 1)]
theorem eval_atom1132 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1132 = ((g 5) * (g 10) * (g 19)) := by
  norm_num [atom1132, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1132_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (45020666086560 : Int) atom1132) := by
  rw [SparsePolynomial.eval_scale, eval_atom1132]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 5) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1133 : SparsePolynomial.Poly := [([5,10,20], 1)]
theorem eval_atom1133 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1133 = ((g 5) * (g 10) * (g 20)) := by
  norm_num [atom1133, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1133_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53773068971808 : Int) atom1133) := by
  rw [SparsePolynomial.eval_scale, eval_atom1133]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 5) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1134 : SparsePolynomial.Poly := [([5,11,11], 1)]
theorem eval_atom1134 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1134 = ((g 5) * (g 11) * (g 11)) := by
  norm_num [atom1134, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1134_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11440792772352 : Int) atom1134) := by
  rw [SparsePolynomial.eval_scale, eval_atom1134]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1135 : SparsePolynomial.Poly := [([5,11,12], 1)]
theorem eval_atom1135 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1135 = ((g 5) * (g 11) * (g 12)) := by
  norm_num [atom1135, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1135_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (20459364367104 : Int) atom1135) := by
  rw [SparsePolynomial.eval_scale, eval_atom1135]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 5) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block015 : SparsePolynomial.Poly := [([4,16,19], 40297587372000), ([4,16,20], 45912704890500), ([4,17,17], 39243222144000), ([4,17,18], 60042692026800), ([4,17,19], 42753122622000), ([4,17,20], 53503172881200), ([4,18,18], 16441201816200), ([4,18,19], 21090286866600), ([4,18,20], 31933858238100), ([4,19,20], 8021538207900), ([4,20,20], 10915331798700), ([5,5,5], 2384168341248), ([5,5,6], 5099671524096), ([5,5,7], 475114087296), ([5,5,9], 1116273312000), ([5,5,10], 773176320000), ([5,5,11], 847840896000), ([5,5,12], 261913478400), ([5,5,15], 3749450450688), ([5,6,6], 7321536603648), ([5,6,7], 5911986468096), ([5,6,8], 1501404912000), ([5,6,11], 158747500800), ([5,6,13], 165266438400), ([5,6,14], 592446355200), ([5,6,15], 7715209569408), ([5,6,17], 666940934016), ([5,6,18], 5982693393600), ([5,6,19], 11433151537920), ([5,6,20], 17685804276000), ([5,7,7], 2176055048448), ([5,7,8], 977584809600), ([5,7,11], 676775635200), ([5,7,12], 777042201600), ([5,7,13], 1201322707200), ([5,7,14], 1887516691200), ([5,7,15], 11268696014208), ([5,7,16], 7360279591680), ([5,7,17], 12136953868416), ([5,7,18], 18104289410880), ([5,7,19], 25272405692928), ([5,7,20], 32557609173600), ([5,8,8], 2814314861952), ([5,8,9], 4832741349504), ([5,8,10], 4664575499904), ([5,8,11], 5173185285504), ([5,8,12], 4937120152704), ([5,8,13], 5452248875904), ([5,8,14], 6229291077504), ([5,8,15], 15678311099904), ([5,8,16], 13269277891440), ([5,8,17], 19501256738304), ([5,8,18], 25795167116112), ([5,8,19], 33886745865360), ([5,8,20], 41978324614608), ([5,9,9], 6031211588352), ([5,9,10], 10283151170304), ([5,9,11], 10455429256704), ([5,9,12], 10569226408704), ([5,9,13], 11007037499904), ([5,9,14], 11706762069504), ([5,9,15], 20771126872704), ([5,9,16], 18331227015840), ([5,9,17], 25882377554304), ([5,9,18], 31092814209312), ([5,9,19], 39549718769760), ([5,9,20], 48097833974208), ([5,10,10], 8264724682752), ([5,10,11], 15692732354304), ([5,10,12], 15133866107904), ([5,10,13], 15326193717504), ([5,10,14], 15780434805504), ([5,10,15], 25134257493504), ([5,10,16], 22912538329440), ([5,10,17], 32993183522304), ([5,10,18], 36268263201312), ([5,10,19], 45020666086560), ([5,10,20], 53773068971808), ([5,11,11], 11440792772352), ([5,11,12], 20459364367104)]
theorem block015_data : block015 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (40297587372000 : Int) atom1056) (SparsePolynomial.scale (45912704890500 : Int) atom1057)) (SparsePolynomial.merge (SparsePolynomial.scale (39243222144000 : Int) atom1058) (SparsePolynomial.merge (SparsePolynomial.scale (60042692026800 : Int) atom1059) (SparsePolynomial.scale (42753122622000 : Int) atom1060)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (53503172881200 : Int) atom1061) (SparsePolynomial.scale (16441201816200 : Int) atom1062)) (SparsePolynomial.merge (SparsePolynomial.scale (21090286866600 : Int) atom1063) (SparsePolynomial.merge (SparsePolynomial.scale (31933858238100 : Int) atom1064) (SparsePolynomial.scale (8021538207900 : Int) atom1065))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (10915331798700 : Int) atom1066) (SparsePolynomial.scale (2384168341248 : Int) atom1067)) (SparsePolynomial.merge (SparsePolynomial.scale (5099671524096 : Int) atom1068) (SparsePolynomial.merge (SparsePolynomial.scale (475114087296 : Int) atom1069) (SparsePolynomial.scale (1116273312000 : Int) atom1070)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (773176320000 : Int) atom1071) (SparsePolynomial.scale (847840896000 : Int) atom1072)) (SparsePolynomial.merge (SparsePolynomial.scale (261913478400 : Int) atom1073) (SparsePolynomial.merge (SparsePolynomial.scale (3749450450688 : Int) atom1074) (SparsePolynomial.scale (7321536603648 : Int) atom1075)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5911986468096 : Int) atom1076) (SparsePolynomial.scale (1501404912000 : Int) atom1077)) (SparsePolynomial.merge (SparsePolynomial.scale (158747500800 : Int) atom1078) (SparsePolynomial.merge (SparsePolynomial.scale (165266438400 : Int) atom1079) (SparsePolynomial.scale (592446355200 : Int) atom1080)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (7715209569408 : Int) atom1081) (SparsePolynomial.scale (666940934016 : Int) atom1082)) (SparsePolynomial.merge (SparsePolynomial.scale (5982693393600 : Int) atom1083) (SparsePolynomial.merge (SparsePolynomial.scale (11433151537920 : Int) atom1084) (SparsePolynomial.scale (17685804276000 : Int) atom1085))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2176055048448 : Int) atom1086) (SparsePolynomial.scale (977584809600 : Int) atom1087)) (SparsePolynomial.merge (SparsePolynomial.scale (676775635200 : Int) atom1088) (SparsePolynomial.merge (SparsePolynomial.scale (777042201600 : Int) atom1089) (SparsePolynomial.scale (1201322707200 : Int) atom1090)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (1887516691200 : Int) atom1091) (SparsePolynomial.scale (11268696014208 : Int) atom1092)) (SparsePolynomial.merge (SparsePolynomial.scale (7360279591680 : Int) atom1093) (SparsePolynomial.merge (SparsePolynomial.scale (12136953868416 : Int) atom1094) (SparsePolynomial.scale (18104289410880 : Int) atom1095))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (25272405692928 : Int) atom1096) (SparsePolynomial.scale (32557609173600 : Int) atom1097)) (SparsePolynomial.merge (SparsePolynomial.scale (2814314861952 : Int) atom1098) (SparsePolynomial.merge (SparsePolynomial.scale (4832741349504 : Int) atom1099) (SparsePolynomial.scale (4664575499904 : Int) atom1100)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5173185285504 : Int) atom1101) (SparsePolynomial.scale (4937120152704 : Int) atom1102)) (SparsePolynomial.merge (SparsePolynomial.scale (5452248875904 : Int) atom1103) (SparsePolynomial.merge (SparsePolynomial.scale (6229291077504 : Int) atom1104) (SparsePolynomial.scale (15678311099904 : Int) atom1105))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13269277891440 : Int) atom1106) (SparsePolynomial.scale (19501256738304 : Int) atom1107)) (SparsePolynomial.merge (SparsePolynomial.scale (25795167116112 : Int) atom1108) (SparsePolynomial.merge (SparsePolynomial.scale (33886745865360 : Int) atom1109) (SparsePolynomial.scale (41978324614608 : Int) atom1110)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6031211588352 : Int) atom1111) (SparsePolynomial.scale (10283151170304 : Int) atom1112)) (SparsePolynomial.merge (SparsePolynomial.scale (10455429256704 : Int) atom1113) (SparsePolynomial.merge (SparsePolynomial.scale (10569226408704 : Int) atom1114) (SparsePolynomial.scale (11007037499904 : Int) atom1115)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (11706762069504 : Int) atom1116) (SparsePolynomial.scale (20771126872704 : Int) atom1117)) (SparsePolynomial.merge (SparsePolynomial.scale (18331227015840 : Int) atom1118) (SparsePolynomial.merge (SparsePolynomial.scale (25882377554304 : Int) atom1119) (SparsePolynomial.scale (31092814209312 : Int) atom1120)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (39549718769760 : Int) atom1121) (SparsePolynomial.scale (48097833974208 : Int) atom1122)) (SparsePolynomial.merge (SparsePolynomial.scale (8264724682752 : Int) atom1123) (SparsePolynomial.merge (SparsePolynomial.scale (15692732354304 : Int) atom1124) (SparsePolynomial.scale (15133866107904 : Int) atom1125))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (15326193717504 : Int) atom1126) (SparsePolynomial.scale (15780434805504 : Int) atom1127)) (SparsePolynomial.merge (SparsePolynomial.scale (25134257493504 : Int) atom1128) (SparsePolynomial.merge (SparsePolynomial.scale (22912538329440 : Int) atom1129) (SparsePolynomial.scale (32993183522304 : Int) atom1130)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (36268263201312 : Int) atom1131) (SparsePolynomial.scale (45020666086560 : Int) atom1132)) (SparsePolynomial.merge (SparsePolynomial.scale (53773068971808 : Int) atom1133) (SparsePolynomial.merge (SparsePolynomial.scale (11440792772352 : Int) atom1134) (SparsePolynomial.scale (20459364367104 : Int) atom1135)))))))) := by decide +kernel
theorem block015_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block015 := by
  rw [block015_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1056_nonneg g hg hA hB) (atom1057_nonneg g hg hA hB)) (add_nonneg (atom1058_nonneg g hg hA hB) (add_nonneg (atom1059_nonneg g hg hA hB) (atom1060_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1061_nonneg g hg hA hB) (atom1062_nonneg g hg hA hB)) (add_nonneg (atom1063_nonneg g hg hA hB) (add_nonneg (atom1064_nonneg g hg hA hB) (atom1065_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1066_nonneg g hg hA hB) (atom1067_nonneg g hg hA hB)) (add_nonneg (atom1068_nonneg g hg hA hB) (add_nonneg (atom1069_nonneg g hg hA hB) (atom1070_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1071_nonneg g hg hA hB) (atom1072_nonneg g hg hA hB)) (add_nonneg (atom1073_nonneg g hg hA hB) (add_nonneg (atom1074_nonneg g hg hA hB) (atom1075_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1076_nonneg g hg hA hB) (atom1077_nonneg g hg hA hB)) (add_nonneg (atom1078_nonneg g hg hA hB) (add_nonneg (atom1079_nonneg g hg hA hB) (atom1080_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1081_nonneg g hg hA hB) (atom1082_nonneg g hg hA hB)) (add_nonneg (atom1083_nonneg g hg hA hB) (add_nonneg (atom1084_nonneg g hg hA hB) (atom1085_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1086_nonneg g hg hA hB) (atom1087_nonneg g hg hA hB)) (add_nonneg (atom1088_nonneg g hg hA hB) (add_nonneg (atom1089_nonneg g hg hA hB) (atom1090_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1091_nonneg g hg hA hB) (atom1092_nonneg g hg hA hB)) (add_nonneg (atom1093_nonneg g hg hA hB) (add_nonneg (atom1094_nonneg g hg hA hB) (atom1095_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1096_nonneg g hg hA hB) (atom1097_nonneg g hg hA hB)) (add_nonneg (atom1098_nonneg g hg hA hB) (add_nonneg (atom1099_nonneg g hg hA hB) (atom1100_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1101_nonneg g hg hA hB) (atom1102_nonneg g hg hA hB)) (add_nonneg (atom1103_nonneg g hg hA hB) (add_nonneg (atom1104_nonneg g hg hA hB) (atom1105_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1106_nonneg g hg hA hB) (atom1107_nonneg g hg hA hB)) (add_nonneg (atom1108_nonneg g hg hA hB) (add_nonneg (atom1109_nonneg g hg hA hB) (atom1110_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1111_nonneg g hg hA hB) (atom1112_nonneg g hg hA hB)) (add_nonneg (atom1113_nonneg g hg hA hB) (add_nonneg (atom1114_nonneg g hg hA hB) (atom1115_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1116_nonneg g hg hA hB) (atom1117_nonneg g hg hA hB)) (add_nonneg (atom1118_nonneg g hg hA hB) (add_nonneg (atom1119_nonneg g hg hA hB) (atom1120_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1121_nonneg g hg hA hB) (atom1122_nonneg g hg hA hB)) (add_nonneg (atom1123_nonneg g hg hA hB) (add_nonneg (atom1124_nonneg g hg hA hB) (atom1125_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1126_nonneg g hg hA hB) (atom1127_nonneg g hg hA hB)) (add_nonneg (atom1128_nonneg g hg hA hB) (add_nonneg (atom1129_nonneg g hg hA hB) (atom1130_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1131_nonneg g hg hA hB) (atom1132_nonneg g hg hA hB)) (add_nonneg (atom1133_nonneg g hg hA hB) (add_nonneg (atom1134_nonneg g hg hA hB) (atom1135_nonneg g hg hA hB))))))))

end APPT.Finite21
