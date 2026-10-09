import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1216 : SparsePolynomial.Poly := [([6,9,13], 1)]
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
def atom1217 : SparsePolynomial.Poly := [([6,9,14], 1)]
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
def atom1218 : SparsePolynomial.Poly := [([6,9,15], 1)]
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
def atom1219 : SparsePolynomial.Poly := [([6,9,16], 1)]
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
def atom1220 : SparsePolynomial.Poly := [([6,9,17], 1)]
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
def atom1221 : SparsePolynomial.Poly := [([6,9,18], 1)]
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
def atom1222 : SparsePolynomial.Poly := [([6,9,19], 1)]
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
def atom1223 : SparsePolynomial.Poly := [([6,9,20], 1)]
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
def atom1224 : SparsePolynomial.Poly := [([6,10,10], 1)]
theorem eval_atom1224 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1224 = ((g 6) * (g 10) * (g 10)) := by
  norm_num [atom1224, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1224_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3204336038400 : Int) atom1224) := by
  rw [SparsePolynomial.eval_scale, eval_atom1224]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1225 : SparsePolynomial.Poly := [([6,10,11], 1)]
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
def atom1226 : SparsePolynomial.Poly := [([6,10,12], 1)]
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
def atom1227 : SparsePolynomial.Poly := [([6,10,13], 1)]
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
def atom1228 : SparsePolynomial.Poly := [([6,10,14], 1)]
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
def atom1229 : SparsePolynomial.Poly := [([6,10,15], 1)]
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
def atom1230 : SparsePolynomial.Poly := [([6,10,16], 1)]
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
def atom1231 : SparsePolynomial.Poly := [([6,10,17], 1)]
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
def atom1232 : SparsePolynomial.Poly := [([6,10,18], 1)]
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
def atom1233 : SparsePolynomial.Poly := [([6,10,19], 1)]
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
def atom1234 : SparsePolynomial.Poly := [([6,10,20], 1)]
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
def atom1235 : SparsePolynomial.Poly := [([6,11,11], 1)]
theorem eval_atom1235 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1235 = ((g 6) * (g 11) * (g 11)) := by
  norm_num [atom1235, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1235_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5780946124800 : Int) atom1235) := by
  rw [SparsePolynomial.eval_scale, eval_atom1235]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1236 : SparsePolynomial.Poly := [([6,11,12], 1)]
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
def atom1237 : SparsePolynomial.Poly := [([6,11,13], 1)]
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
def atom1238 : SparsePolynomial.Poly := [([6,11,14], 1)]
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
def atom1239 : SparsePolynomial.Poly := [([6,11,15], 1)]
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
def atom1240 : SparsePolynomial.Poly := [([6,11,16], 1)]
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
def atom1241 : SparsePolynomial.Poly := [([6,11,17], 1)]
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
def atom1242 : SparsePolynomial.Poly := [([6,11,18], 1)]
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
def atom1243 : SparsePolynomial.Poly := [([6,11,19], 1)]
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
def atom1244 : SparsePolynomial.Poly := [([6,11,20], 1)]
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
def atom1245 : SparsePolynomial.Poly := [([6,12,12], 1)]
theorem eval_atom1245 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1245 = ((g 6) * (g 12) * (g 12)) := by
  norm_num [atom1245, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1245_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8371086796800 : Int) atom1245) := by
  rw [SparsePolynomial.eval_scale, eval_atom1245]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 6) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1246 : SparsePolynomial.Poly := [([6,12,13], 1)]
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
def atom1247 : SparsePolynomial.Poly := [([6,12,14], 1)]
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
def atom1248 : SparsePolynomial.Poly := [([6,12,15], 1)]
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
def atom1249 : SparsePolynomial.Poly := [([6,12,16], 1)]
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
def atom1250 : SparsePolynomial.Poly := [([6,12,17], 1)]
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
def atom1251 : SparsePolynomial.Poly := [([6,12,18], 1)]
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
def atom1252 : SparsePolynomial.Poly := [([6,12,19], 1)]
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
def atom1253 : SparsePolynomial.Poly := [([6,12,20], 1)]
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
def atom1254 : SparsePolynomial.Poly := [([6,13,13], 1)]
theorem eval_atom1254 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1254 = ((g 6) * (g 13) * (g 13)) := by
  norm_num [atom1254, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1254_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11705777856000 : Int) atom1254) := by
  rw [SparsePolynomial.eval_scale, eval_atom1254]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 6) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1255 : SparsePolynomial.Poly := [([6,13,14], 1)]
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
def atom1256 : SparsePolynomial.Poly := [([6,13,15], 1)]
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
def atom1257 : SparsePolynomial.Poly := [([6,13,16], 1)]
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
def atom1258 : SparsePolynomial.Poly := [([6,13,17], 1)]
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
def atom1259 : SparsePolynomial.Poly := [([6,13,18], 1)]
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
def atom1260 : SparsePolynomial.Poly := [([6,13,19], 1)]
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
def atom1261 : SparsePolynomial.Poly := [([6,13,20], 1)]
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
def atom1262 : SparsePolynomial.Poly := [([6,14,14], 1)]
theorem eval_atom1262 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1262 = ((g 6) * (g 14) * (g 14)) := by
  norm_num [atom1262, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1262_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15983651980800 : Int) atom1262) := by
  rw [SparsePolynomial.eval_scale, eval_atom1262]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 6) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1263 : SparsePolynomial.Poly := [([6,14,15], 1)]
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
def atom1264 : SparsePolynomial.Poly := [([6,14,16], 1)]
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
def atom1265 : SparsePolynomial.Poly := [([6,14,17], 1)]
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
def atom1266 : SparsePolynomial.Poly := [([6,14,18], 1)]
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
def atom1267 : SparsePolynomial.Poly := [([6,14,19], 1)]
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
def atom1268 : SparsePolynomial.Poly := [([6,14,20], 1)]
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
def atom1269 : SparsePolynomial.Poly := [([6,15,15], 1)]
theorem eval_atom1269 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1269 = ((g 6) * (g 15) * (g 15)) := by
  norm_num [atom1269, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1269_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (23458334054400 : Int) atom1269) := by
  rw [SparsePolynomial.eval_scale, eval_atom1269]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 6) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1270 : SparsePolynomial.Poly := [([6,15,16], 1)]
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
def atom1271 : SparsePolynomial.Poly := [([6,15,17], 1)]
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
def atom1272 : SparsePolynomial.Poly := [([6,15,18], 1)]
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
def atom1273 : SparsePolynomial.Poly := [([6,15,19], 1)]
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
def atom1274 : SparsePolynomial.Poly := [([6,15,20], 1)]
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
def atom1275 : SparsePolynomial.Poly := [([6,16,16], 1)]
theorem eval_atom1275 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1275 = ((g 6) * (g 16) * (g 16)) := by
  norm_num [atom1275, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1275_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17545854735360 : Int) atom1275) := by
  rw [SparsePolynomial.eval_scale, eval_atom1275]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 6) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1276 : SparsePolynomial.Poly := [([6,16,17], 1)]
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
def atom1277 : SparsePolynomial.Poly := [([6,16,18], 1)]
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
def atom1278 : SparsePolynomial.Poly := [([6,16,19], 1)]
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
def atom1279 : SparsePolynomial.Poly := [([6,16,20], 1)]
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
def atom1280 : SparsePolynomial.Poly := [([6,17,17], 1)]
theorem eval_atom1280 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1280 = ((g 6) * (g 17) * (g 17)) := by
  norm_num [atom1280, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1280_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (40457273472000 : Int) atom1280) := by
  rw [SparsePolynomial.eval_scale, eval_atom1280]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 6) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1281 : SparsePolynomial.Poly := [([6,17,18], 1)]
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
def atom1282 : SparsePolynomial.Poly := [([6,17,19], 1)]
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
def atom1283 : SparsePolynomial.Poly := [([6,17,20], 1)]
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
def atom1284 : SparsePolynomial.Poly := [([6,18,18], 1)]
theorem eval_atom1284 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1284 = ((g 6) * (g 18) * (g 18)) := by
  norm_num [atom1284, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1284_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18855796377600 : Int) atom1284) := by
  rw [SparsePolynomial.eval_scale, eval_atom1284]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 6) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1285 : SparsePolynomial.Poly := [([6,18,19], 1)]
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
def atom1286 : SparsePolynomial.Poly := [([6,18,20], 1)]
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
def atom1287 : SparsePolynomial.Poly := [([7,7,7], 1)]
theorem eval_atom1287 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1287 = ((g 7) * (g 7) * (g 7)) := by
  norm_num [atom1287, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1287_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2264279068800 : Int) atom1287) := by
  rw [SparsePolynomial.eval_scale, eval_atom1287]
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 7) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1288 : SparsePolynomial.Poly := [([7,7,8], 1)]
theorem eval_atom1288 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1288 = ((g 7) * (g 7) * (g 8)) := by
  norm_num [atom1288, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1288_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3207232022400 : Int) atom1288) := by
  rw [SparsePolynomial.eval_scale, eval_atom1288]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1289 : SparsePolynomial.Poly := [([7,7,9], 1)]
theorem eval_atom1289 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1289 = ((g 7) * (g 7) * (g 9)) := by
  norm_num [atom1289, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1289_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (427179916800 : Int) atom1289) := by
  rw [SparsePolynomial.eval_scale, eval_atom1289]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1290 : SparsePolynomial.Poly := [([7,7,10], 1)]
theorem eval_atom1290 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1290 = ((g 7) * (g 7) * (g 10)) := by
  norm_num [atom1290, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1290_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (84082924800 : Int) atom1290) := by
  rw [SparsePolynomial.eval_scale, eval_atom1290]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1291 : SparsePolynomial.Poly := [([7,7,15], 1)]
theorem eval_atom1291 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1291 = ((g 7) * (g 7) * (g 15)) := by
  norm_num [atom1291, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1291_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3734859508992 : Int) atom1291) := by
  rw [SparsePolynomial.eval_scale, eval_atom1291]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1292 : SparsePolynomial.Poly := [([7,8,8], 1)]
theorem eval_atom1292 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1292 = ((g 7) * (g 8) * (g 8)) := by
  norm_num [atom1292, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1292_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2780052105600 : Int) atom1292) := by
  rw [SparsePolynomial.eval_scale, eval_atom1292]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1293 : SparsePolynomial.Poly := [([7,8,9], 1)]
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
def atom1294 : SparsePolynomial.Poly := [([7,8,13], 1)]
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
def atom1295 : SparsePolynomial.Poly := [([7,8,14], 1)]
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
def block017 : SparsePolynomial.Poly := [([6,9,13], 2066320569600), ([6,9,14], 2843362771200), ([6,9,15], 12526751865600), ([6,9,16], 9755314884000), ([6,9,17], 17449540819200), ([6,9,18], 24820650338400), ([6,9,19], 35164296367200), ([6,9,20], 45787493959200), ([6,10,10], 3204336038400), ([6,10,11], 5399676979200), ([6,10,12], 5672221632000), ([6,10,13], 6371946201600), ([6,10,14], 7071670771200), ([6,10,15], 17374084156800), ([6,10,16], 15150394274400), ([6,10,17], 25703681270400), ([6,10,18], 31388299941600), ([6,10,19], 42276310423200), ([6,10,20], 53312311684800), ([6,11,11], 5780946124800), ([6,11,12], 10139247820800), ([6,11,13], 10593488908800), ([6,11,14], 11047729996800), ([6,11,15], 21624024038400), ([6,11,16], 19839379392000), ([6,11,17], 33307519795200), ([6,11,18], 36744632870400), ([6,11,19], 47909475532800), ([6,11,20], 59097361881600), ([6,12,12], 8371086796800), ([6,12,13], 16355585433600), ([6,12,14], 16396177190400), ([6,12,15], 22971182707200), ([6,12,16], 23375330316800), ([6,12,17], 35615926976000), ([6,12,18], 39881932652800), ([6,12,19], 50170991001600), ([6,12,20], 61314928214400), ([6,13,13], 11705777856000), ([6,13,14], 21699798566400), ([6,13,15], 27731989051200), ([6,13,16], 27457319044800), ([6,13,17], 42282031276800), ([6,13,18], 47812699267200), ([6,13,19], 51497513812800), ([6,13,20], 68517790488000), ([6,14,14], 15983651980800), ([6,14,15], 32380953292800), ([6,14,16], 31420158336000), ([6,14,17], 51141665433600), ([6,14,18], 58156348723200), ([6,14,19], 57274763212800), ([6,14,20], 80303655398400), ([6,15,15], 23458334054400), ([6,15,16], 44424079257600), ([6,15,17], 68201800934400), ([6,15,18], 70646230771200), ([6,15,19], 52545926361600), ([6,15,20], 79011669542400), ([6,16,16], 17545854735360), ([6,16,17], 55664911411200), ([6,16,18], 60106665427200), ([6,16,19], 46866713241600), ([6,16,20], 57384114883200), ([6,17,17], 40457273472000), ([6,17,18], 65177036467200), ([6,17,19], 46861654694400), ([6,17,20], 53756858937600), ([6,18,18], 18855796377600), ([6,18,19], 24005993760000), ([6,18,20], 30962904739200), ([7,7,7], 2264279068800), ([7,7,8], 3207232022400), ([7,7,9], 427179916800), ([7,7,10], 84082924800), ([7,7,15], 3734859508992), ([7,8,8], 2780052105600), ([7,8,9], 518028134400), ([7,8,13], 427179916800), ([7,8,14], 854359833600)]
theorem block017_data : block017 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2066320569600 : Int) atom1216) (SparsePolynomial.scale (2843362771200 : Int) atom1217)) (SparsePolynomial.merge (SparsePolynomial.scale (12526751865600 : Int) atom1218) (SparsePolynomial.merge (SparsePolynomial.scale (9755314884000 : Int) atom1219) (SparsePolynomial.scale (17449540819200 : Int) atom1220)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (24820650338400 : Int) atom1221) (SparsePolynomial.scale (35164296367200 : Int) atom1222)) (SparsePolynomial.merge (SparsePolynomial.scale (45787493959200 : Int) atom1223) (SparsePolynomial.merge (SparsePolynomial.scale (3204336038400 : Int) atom1224) (SparsePolynomial.scale (5399676979200 : Int) atom1225))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (5672221632000 : Int) atom1226) (SparsePolynomial.scale (6371946201600 : Int) atom1227)) (SparsePolynomial.merge (SparsePolynomial.scale (7071670771200 : Int) atom1228) (SparsePolynomial.merge (SparsePolynomial.scale (17374084156800 : Int) atom1229) (SparsePolynomial.scale (15150394274400 : Int) atom1230)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (25703681270400 : Int) atom1231) (SparsePolynomial.scale (31388299941600 : Int) atom1232)) (SparsePolynomial.merge (SparsePolynomial.scale (42276310423200 : Int) atom1233) (SparsePolynomial.merge (SparsePolynomial.scale (53312311684800 : Int) atom1234) (SparsePolynomial.scale (5780946124800 : Int) atom1235)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (10139247820800 : Int) atom1236) (SparsePolynomial.scale (10593488908800 : Int) atom1237)) (SparsePolynomial.merge (SparsePolynomial.scale (11047729996800 : Int) atom1238) (SparsePolynomial.merge (SparsePolynomial.scale (21624024038400 : Int) atom1239) (SparsePolynomial.scale (19839379392000 : Int) atom1240)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (33307519795200 : Int) atom1241) (SparsePolynomial.scale (36744632870400 : Int) atom1242)) (SparsePolynomial.merge (SparsePolynomial.scale (47909475532800 : Int) atom1243) (SparsePolynomial.merge (SparsePolynomial.scale (59097361881600 : Int) atom1244) (SparsePolynomial.scale (8371086796800 : Int) atom1245))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (16355585433600 : Int) atom1246) (SparsePolynomial.scale (16396177190400 : Int) atom1247)) (SparsePolynomial.merge (SparsePolynomial.scale (22971182707200 : Int) atom1248) (SparsePolynomial.merge (SparsePolynomial.scale (23375330316800 : Int) atom1249) (SparsePolynomial.scale (35615926976000 : Int) atom1250)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (39881932652800 : Int) atom1251) (SparsePolynomial.scale (50170991001600 : Int) atom1252)) (SparsePolynomial.merge (SparsePolynomial.scale (61314928214400 : Int) atom1253) (SparsePolynomial.merge (SparsePolynomial.scale (11705777856000 : Int) atom1254) (SparsePolynomial.scale (21699798566400 : Int) atom1255))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (27731989051200 : Int) atom1256) (SparsePolynomial.scale (27457319044800 : Int) atom1257)) (SparsePolynomial.merge (SparsePolynomial.scale (42282031276800 : Int) atom1258) (SparsePolynomial.merge (SparsePolynomial.scale (47812699267200 : Int) atom1259) (SparsePolynomial.scale (51497513812800 : Int) atom1260)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (68517790488000 : Int) atom1261) (SparsePolynomial.scale (15983651980800 : Int) atom1262)) (SparsePolynomial.merge (SparsePolynomial.scale (32380953292800 : Int) atom1263) (SparsePolynomial.merge (SparsePolynomial.scale (31420158336000 : Int) atom1264) (SparsePolynomial.scale (51141665433600 : Int) atom1265))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (58156348723200 : Int) atom1266) (SparsePolynomial.scale (57274763212800 : Int) atom1267)) (SparsePolynomial.merge (SparsePolynomial.scale (80303655398400 : Int) atom1268) (SparsePolynomial.merge (SparsePolynomial.scale (23458334054400 : Int) atom1269) (SparsePolynomial.scale (44424079257600 : Int) atom1270)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (68201800934400 : Int) atom1271) (SparsePolynomial.scale (70646230771200 : Int) atom1272)) (SparsePolynomial.merge (SparsePolynomial.scale (52545926361600 : Int) atom1273) (SparsePolynomial.merge (SparsePolynomial.scale (79011669542400 : Int) atom1274) (SparsePolynomial.scale (17545854735360 : Int) atom1275)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (55664911411200 : Int) atom1276) (SparsePolynomial.scale (60106665427200 : Int) atom1277)) (SparsePolynomial.merge (SparsePolynomial.scale (46866713241600 : Int) atom1278) (SparsePolynomial.merge (SparsePolynomial.scale (57384114883200 : Int) atom1279) (SparsePolynomial.scale (40457273472000 : Int) atom1280)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (65177036467200 : Int) atom1281) (SparsePolynomial.scale (46861654694400 : Int) atom1282)) (SparsePolynomial.merge (SparsePolynomial.scale (53756858937600 : Int) atom1283) (SparsePolynomial.merge (SparsePolynomial.scale (18855796377600 : Int) atom1284) (SparsePolynomial.scale (24005993760000 : Int) atom1285))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (30962904739200 : Int) atom1286) (SparsePolynomial.scale (2264279068800 : Int) atom1287)) (SparsePolynomial.merge (SparsePolynomial.scale (3207232022400 : Int) atom1288) (SparsePolynomial.merge (SparsePolynomial.scale (427179916800 : Int) atom1289) (SparsePolynomial.scale (84082924800 : Int) atom1290)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3734859508992 : Int) atom1291) (SparsePolynomial.scale (2780052105600 : Int) atom1292)) (SparsePolynomial.merge (SparsePolynomial.scale (518028134400 : Int) atom1293) (SparsePolynomial.merge (SparsePolynomial.scale (427179916800 : Int) atom1294) (SparsePolynomial.scale (854359833600 : Int) atom1295)))))))) := by decide +kernel
theorem block017_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block017 := by
  rw [block017_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1216_nonneg g hg hA hB) (atom1217_nonneg g hg hA hB)) (add_nonneg (atom1218_nonneg g hg hA hB) (add_nonneg (atom1219_nonneg g hg hA hB) (atom1220_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1221_nonneg g hg hA hB) (atom1222_nonneg g hg hA hB)) (add_nonneg (atom1223_nonneg g hg hA hB) (add_nonneg (atom1224_nonneg g hg hA hB) (atom1225_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1226_nonneg g hg hA hB) (atom1227_nonneg g hg hA hB)) (add_nonneg (atom1228_nonneg g hg hA hB) (add_nonneg (atom1229_nonneg g hg hA hB) (atom1230_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1231_nonneg g hg hA hB) (atom1232_nonneg g hg hA hB)) (add_nonneg (atom1233_nonneg g hg hA hB) (add_nonneg (atom1234_nonneg g hg hA hB) (atom1235_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1236_nonneg g hg hA hB) (atom1237_nonneg g hg hA hB)) (add_nonneg (atom1238_nonneg g hg hA hB) (add_nonneg (atom1239_nonneg g hg hA hB) (atom1240_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1241_nonneg g hg hA hB) (atom1242_nonneg g hg hA hB)) (add_nonneg (atom1243_nonneg g hg hA hB) (add_nonneg (atom1244_nonneg g hg hA hB) (atom1245_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1246_nonneg g hg hA hB) (atom1247_nonneg g hg hA hB)) (add_nonneg (atom1248_nonneg g hg hA hB) (add_nonneg (atom1249_nonneg g hg hA hB) (atom1250_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1251_nonneg g hg hA hB) (atom1252_nonneg g hg hA hB)) (add_nonneg (atom1253_nonneg g hg hA hB) (add_nonneg (atom1254_nonneg g hg hA hB) (atom1255_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1256_nonneg g hg hA hB) (atom1257_nonneg g hg hA hB)) (add_nonneg (atom1258_nonneg g hg hA hB) (add_nonneg (atom1259_nonneg g hg hA hB) (atom1260_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1261_nonneg g hg hA hB) (atom1262_nonneg g hg hA hB)) (add_nonneg (atom1263_nonneg g hg hA hB) (add_nonneg (atom1264_nonneg g hg hA hB) (atom1265_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1266_nonneg g hg hA hB) (atom1267_nonneg g hg hA hB)) (add_nonneg (atom1268_nonneg g hg hA hB) (add_nonneg (atom1269_nonneg g hg hA hB) (atom1270_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1271_nonneg g hg hA hB) (atom1272_nonneg g hg hA hB)) (add_nonneg (atom1273_nonneg g hg hA hB) (add_nonneg (atom1274_nonneg g hg hA hB) (atom1275_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1276_nonneg g hg hA hB) (atom1277_nonneg g hg hA hB)) (add_nonneg (atom1278_nonneg g hg hA hB) (add_nonneg (atom1279_nonneg g hg hA hB) (atom1280_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1281_nonneg g hg hA hB) (atom1282_nonneg g hg hA hB)) (add_nonneg (atom1283_nonneg g hg hA hB) (add_nonneg (atom1284_nonneg g hg hA hB) (atom1285_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1286_nonneg g hg hA hB) (atom1287_nonneg g hg hA hB)) (add_nonneg (atom1288_nonneg g hg hA hB) (add_nonneg (atom1289_nonneg g hg hA hB) (atom1290_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1291_nonneg g hg hA hB) (atom1292_nonneg g hg hA hB)) (add_nonneg (atom1293_nonneg g hg hA hB) (add_nonneg (atom1294_nonneg g hg hA hB) (atom1295_nonneg g hg hA hB))))))))

end APPT.Finite21
