import APPT.Finite21Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite21
open SparsePolynomial

def atom1296 : SparsePolynomial.Poly := [([7,8,15], 1)]
theorem eval_atom1296 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1296 = ((g 7) * (g 8) * (g 15)) := by
  norm_num [atom1296, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1296_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (6427474232112 : Int) atom1296) := by
  rw [SparsePolynomial.eval_scale, eval_atom1296]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 8) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1297 : SparsePolynomial.Poly := [([7,8,17], 1)]
theorem eval_atom1297 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1297 = ((g 7) * (g 8) * (g 17)) := by
  norm_num [atom1297, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1297_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1510388496720 : Int) atom1297) := by
  rw [SparsePolynomial.eval_scale, eval_atom1297]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 8) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1298 : SparsePolynomial.Poly := [([7,8,18], 1)]
theorem eval_atom1298 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1298 = ((g 7) * (g 8) * (g 18)) := by
  norm_num [atom1298, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1298_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5786258284800 : Int) atom1298) := by
  rw [SparsePolynomial.eval_scale, eval_atom1298]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 8) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1299 : SparsePolynomial.Poly := [([7,8,19], 1)]
theorem eval_atom1299 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1299 = ((g 7) * (g 8) * (g 19)) := by
  norm_num [atom1299, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1299_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (11171238059520 : Int) atom1299) := by
  rw [SparsePolynomial.eval_scale, eval_atom1299]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 8) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1300 : SparsePolynomial.Poly := [([7,8,20], 1)]
theorem eval_atom1300 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1300 = ((g 7) * (g 8) * (g 20)) := by
  norm_num [atom1300, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1300_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17391151612800 : Int) atom1300) := by
  rw [SparsePolynomial.eval_scale, eval_atom1300]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 8) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1301 : SparsePolynomial.Poly := [([7,9,9], 1)]
theorem eval_atom1301 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1301 = ((g 7) * (g 9) * (g 9)) := by
  norm_num [atom1301, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1301_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (896401296000 : Int) atom1301) := by
  rw [SparsePolynomial.eval_scale, eval_atom1301]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1302 : SparsePolynomial.Poly := [([7,9,12], 1)]
theorem eval_atom1302 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1302 = ((g 7) * (g 9) * (g 12)) := by
  norm_num [atom1302, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1302_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (686193984000 : Int) atom1302) := by
  rw [SparsePolynomial.eval_scale, eval_atom1302]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1303 : SparsePolynomial.Poly := [([7,9,13], 1)]
theorem eval_atom1303 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1303 = ((g 7) * (g 9) * (g 13)) := by
  norm_num [atom1303, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1303_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1372387968000 : Int) atom1303) := by
  rw [SparsePolynomial.eval_scale, eval_atom1303]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1304 : SparsePolynomial.Poly := [([7,9,14], 1)]
theorem eval_atom1304 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1304 = ((g 7) * (g 9) * (g 14)) := by
  norm_num [atom1304, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1304_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2058581952000 : Int) atom1304) := by
  rw [SparsePolynomial.eval_scale, eval_atom1304]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1305 : SparsePolynomial.Poly := [([7,9,15], 1)]
theorem eval_atom1305 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1305 = ((g 7) * (g 9) * (g 15)) := by
  norm_num [atom1305, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1305_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8185219145856 : Int) atom1305) := by
  rw [SparsePolynomial.eval_scale, eval_atom1305]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 9) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1306 : SparsePolynomial.Poly := [([7,9,16], 1)]
theorem eval_atom1306 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1306 = ((g 7) * (g 9) * (g 16)) := by
  norm_num [atom1306, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1306_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3335794446240 : Int) atom1306) := by
  rw [SparsePolynomial.eval_scale, eval_atom1306]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 9) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1307 : SparsePolynomial.Poly := [([7,9,17], 1)]
theorem eval_atom1307 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1307 = ((g 7) * (g 9) * (g 17)) := by
  norm_num [atom1307, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1307_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9115747148160 : Int) atom1307) := by
  rw [SparsePolynomial.eval_scale, eval_atom1307]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 9) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1308 : SparsePolynomial.Poly := [([7,9,18], 1)]
theorem eval_atom1308 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1308 = ((g 7) * (g 9) * (g 18)) := by
  norm_num [atom1308, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1308_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13951505319840 : Int) atom1308) := by
  rw [SparsePolynomial.eval_scale, eval_atom1308]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 9) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1309 : SparsePolynomial.Poly := [([7,9,19], 1)]
theorem eval_atom1309 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1309 = ((g 7) * (g 9) * (g 19)) := by
  norm_num [atom1309, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1309_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22686649344864 : Int) atom1309) := by
  rw [SparsePolynomial.eval_scale, eval_atom1309]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 9) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1310 : SparsePolynomial.Poly := [([7,9,20], 1)]
theorem eval_atom1310 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1310 = ((g 7) * (g 9) * (g 20)) := by
  norm_num [atom1310, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1310_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32365160755200 : Int) atom1310) := by
  rw [SparsePolynomial.eval_scale, eval_atom1310]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 9) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1311 : SparsePolynomial.Poly := [([7,10,10], 1)]
theorem eval_atom1311 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1311 = ((g 7) * (g 10) * (g 10)) := by
  norm_num [atom1311, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1311_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (2262023971200 : Int) atom1311) := by
  rw [SparsePolynomial.eval_scale, eval_atom1311]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1312 : SparsePolynomial.Poly := [([7,10,11], 1)]
theorem eval_atom1312 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1312 = ((g 7) * (g 10) * (g 11)) := by
  norm_num [atom1312, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1312_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (3851384544000 : Int) atom1312) := by
  rw [SparsePolynomial.eval_scale, eval_atom1312]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1313 : SparsePolynomial.Poly := [([7,10,12], 1)]
theorem eval_atom1313 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1313 = ((g 7) * (g 10) * (g 12)) := by
  norm_num [atom1313, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1313_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4201246828800 : Int) atom1313) := by
  rw [SparsePolynomial.eval_scale, eval_atom1313]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1314 : SparsePolynomial.Poly := [([7,10,13], 1)]
theorem eval_atom1314 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1314 = ((g 7) * (g 10) * (g 13)) := by
  norm_num [atom1314, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1314_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4978289030400 : Int) atom1314) := by
  rw [SparsePolynomial.eval_scale, eval_atom1314]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1315 : SparsePolynomial.Poly := [([7,10,14], 1)]
theorem eval_atom1315 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1315 = ((g 7) * (g 10) * (g 14)) := by
  norm_num [atom1315, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1315_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (5755331232000 : Int) atom1315) := by
  rw [SparsePolynomial.eval_scale, eval_atom1315]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1316 : SparsePolynomial.Poly := [([7,10,15], 1)]
theorem eval_atom1316 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1316 = ((g 7) * (g 10) * (g 15)) := by
  norm_num [atom1316, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1316_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (13173656115456 : Int) atom1316) := by
  rw [SparsePolynomial.eval_scale, eval_atom1316]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 10) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1317 : SparsePolynomial.Poly := [([7,10,16], 1)]
theorem eval_atom1317 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1317 = ((g 7) * (g 10) * (g 16)) := by
  norm_num [atom1317, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1317_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9544641913440 : Int) atom1317) := by
  rw [SparsePolynomial.eval_scale, eval_atom1317]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 10) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1318 : SparsePolynomial.Poly := [([7,10,17], 1)]
theorem eval_atom1318 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1318 = ((g 7) * (g 10) * (g 17)) := by
  norm_num [atom1318, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1318_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (18856319074560 : Int) atom1318) := by
  rw [SparsePolynomial.eval_scale, eval_atom1318]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 10) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1319 : SparsePolynomial.Poly := [([7,10,18], 1)]
theorem eval_atom1319 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1319 = ((g 7) * (g 10) * (g 18)) := by
  norm_num [atom1319, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1319_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22426001022240 : Int) atom1319) := by
  rw [SparsePolynomial.eval_scale, eval_atom1319]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 10) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1320 : SparsePolynomial.Poly := [([7,10,19], 1)]
theorem eval_atom1320 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1320 = ((g 7) * (g 10) * (g 19)) := by
  norm_num [atom1320, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1320_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (32125924124064 : Int) atom1320) := by
  rw [SparsePolynomial.eval_scale, eval_atom1320]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 10) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1321 : SparsePolynomial.Poly := [([7,10,20], 1)]
theorem eval_atom1321 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1321 = ((g 7) * (g 10) * (g 20)) := by
  norm_num [atom1321, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1321_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42511529440800 : Int) atom1321) := by
  rw [SparsePolynomial.eval_scale, eval_atom1321]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 10) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1322 : SparsePolynomial.Poly := [([7,11,11], 1)]
theorem eval_atom1322 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1322 = ((g 7) * (g 11) * (g 11)) := by
  norm_num [atom1322, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1322_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (4747785840000 : Int) atom1322) := by
  rw [SparsePolynomial.eval_scale, eval_atom1322]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1323 : SparsePolynomial.Poly := [([7,11,12], 1)]
theorem eval_atom1323 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1323 = ((g 7) * (g 11) * (g 12)) := by
  norm_num [atom1323, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1323_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (8318410732800 : Int) atom1323) := by
  rw [SparsePolynomial.eval_scale, eval_atom1323]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1324 : SparsePolynomial.Poly := [([7,11,13], 1)]
theorem eval_atom1324 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1324 = ((g 7) * (g 11) * (g 13)) := by
  norm_num [atom1324, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1324_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9018135302400 : Int) atom1324) := by
  rw [SparsePolynomial.eval_scale, eval_atom1324]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1325 : SparsePolynomial.Poly := [([7,11,14], 1)]
theorem eval_atom1325 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1325 = ((g 7) * (g 11) * (g 14)) := by
  norm_num [atom1325, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1325_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (9717859872000 : Int) atom1325) := by
  rw [SparsePolynomial.eval_scale, eval_atom1325]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1326 : SparsePolynomial.Poly := [([7,11,15], 1)]
theorem eval_atom1326 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1326 = ((g 7) * (g 11) * (g 15)) := by
  norm_num [atom1326, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1326_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17823714742656 : Int) atom1326) := by
  rw [SparsePolynomial.eval_scale, eval_atom1326]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 11) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1327 : SparsePolynomial.Poly := [([7,11,16], 1)]
theorem eval_atom1327 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1327 = ((g 7) * (g 11) * (g 16)) := by
  norm_num [atom1327, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1327_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (15047395107840 : Int) atom1327) := by
  rw [SparsePolynomial.eval_scale, eval_atom1327]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 11) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1328 : SparsePolynomial.Poly := [([7,11,17], 1)]
theorem eval_atom1328 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1328 = ((g 7) * (g 11) * (g 17)) := by
  norm_num [atom1328, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1328_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27687575007360 : Int) atom1328) := by
  rw [SparsePolynomial.eval_scale, eval_atom1328]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 11) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1329 : SparsePolynomial.Poly := [([7,11,18], 1)]
theorem eval_atom1329 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1329 = ((g 7) * (g 11) * (g 18)) := by
  norm_num [atom1329, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1329_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29300658949440 : Int) atom1329) := by
  rw [SparsePolynomial.eval_scale, eval_atom1329]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 11) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1330 : SparsePolynomial.Poly := [([7,11,19], 1)]
theorem eval_atom1330 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1330 = ((g 7) * (g 11) * (g 19)) := by
  norm_num [atom1330, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1330_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39568321822464 : Int) atom1330) := by
  rw [SparsePolynomial.eval_scale, eval_atom1330]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 11) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1331 : SparsePolynomial.Poly := [([7,11,20], 1)]
theorem eval_atom1331 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1331 = ((g 7) * (g 11) * (g 20)) := by
  norm_num [atom1331, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1331_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (50335348946400 : Int) atom1331) := by
  rw [SparsePolynomial.eval_scale, eval_atom1331]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 11) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1332 : SparsePolynomial.Poly := [([7,12,12], 1)]
theorem eval_atom1332 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1332 = ((g 7) * (g 12) * (g 12)) := by
  norm_num [atom1332, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1332_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (7156230076800 : Int) atom1332) := by
  rw [SparsePolynomial.eval_scale, eval_atom1332]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 7) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1333 : SparsePolynomial.Poly := [([7,12,13], 1)]
theorem eval_atom1333 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1333 = ((g 7) * (g 12) * (g 13)) := by
  norm_num [atom1333, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1333_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14339521324800 : Int) atom1333) := by
  rw [SparsePolynomial.eval_scale, eval_atom1333]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1334 : SparsePolynomial.Poly := [([7,12,14], 1)]
theorem eval_atom1334 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1334 = ((g 7) * (g 12) * (g 14)) := by
  norm_num [atom1334, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1334_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14793762412800 : Int) atom1334) := by
  rw [SparsePolynomial.eval_scale, eval_atom1334]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1335 : SparsePolynomial.Poly := [([7,12,15], 1)]
theorem eval_atom1335 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1335 = ((g 7) * (g 12) * (g 15)) := by
  norm_num [atom1335, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1335_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19441485123456 : Int) atom1335) := by
  rw [SparsePolynomial.eval_scale, eval_atom1335]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 12) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1336 : SparsePolynomial.Poly := [([7,12,16], 1)]
theorem eval_atom1336 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1336 = ((g 7) * (g 12) * (g 16)) := by
  norm_num [atom1336, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1336_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19397114109440 : Int) atom1336) := by
  rw [SparsePolynomial.eval_scale, eval_atom1336]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 12) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1337 : SparsePolynomial.Poly := [([7,12,17], 1)]
theorem eval_atom1337 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1337 = ((g 7) * (g 12) * (g 17)) := by
  norm_num [atom1337, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1337_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31352906629760 : Int) atom1337) := by
  rw [SparsePolynomial.eval_scale, eval_atom1337]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 12) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1338 : SparsePolynomial.Poly := [([7,12,18], 1)]
theorem eval_atom1338 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1338 = ((g 7) * (g 12) * (g 18)) := by
  norm_num [atom1338, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1338_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (34150544280640 : Int) atom1338) := by
  rw [SparsePolynomial.eval_scale, eval_atom1338]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 12) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1339 : SparsePolynomial.Poly := [([7,12,19], 1)]
theorem eval_atom1339 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1339 = ((g 7) * (g 12) * (g 19)) := by
  norm_num [atom1339, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1339_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43898083947264 : Int) atom1339) := by
  rw [SparsePolynomial.eval_scale, eval_atom1339]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 12) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1340 : SparsePolynomial.Poly := [([7,12,20], 1)]
theorem eval_atom1340 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1340 = ((g 7) * (g 12) * (g 20)) := by
  norm_num [atom1340, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1340_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (54883075413600 : Int) atom1340) := by
  rw [SparsePolynomial.eval_scale, eval_atom1340]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 12) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1341 : SparsePolynomial.Poly := [([7,13,13], 1)]
theorem eval_atom1341 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1341 = ((g 7) * (g 13) * (g 13)) := by
  norm_num [atom1341, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1341_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (10477390550400 : Int) atom1341) := by
  rw [SparsePolynomial.eval_scale, eval_atom1341]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 7) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1342 : SparsePolynomial.Poly := [([7,13,14], 1)]
theorem eval_atom1342 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1342 = ((g 7) * (g 13) * (g 14)) := by
  norm_num [atom1342, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1342_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (19824839136000 : Int) atom1342) := by
  rw [SparsePolynomial.eval_scale, eval_atom1342]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1343 : SparsePolynomial.Poly := [([7,13,15], 1)]
theorem eval_atom1343 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1343 = ((g 7) * (g 13) * (g 15)) := by
  norm_num [atom1343, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1343_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24472903179456 : Int) atom1343) := by
  rw [SparsePolynomial.eval_scale, eval_atom1343]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 13) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1344 : SparsePolynomial.Poly := [([7,13,16], 1)]
theorem eval_atom1344 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1344 = ((g 7) * (g 13) * (g 16)) := by
  norm_num [atom1344, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1344_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (24292870914240 : Int) atom1344) := by
  rw [SparsePolynomial.eval_scale, eval_atom1344]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 13) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1345 : SparsePolynomial.Poly := [([7,13,17], 1)]
theorem eval_atom1345 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1345 = ((g 7) * (g 13) * (g 17)) := by
  norm_num [atom1345, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1345_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (39375935372160 : Int) atom1345) := by
  rw [SparsePolynomial.eval_scale, eval_atom1345]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 13) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1346 : SparsePolynomial.Poly := [([7,13,18], 1)]
theorem eval_atom1346 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1346 = ((g 7) * (g 13) * (g 18)) := by
  norm_num [atom1346, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1346_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (43793896443840 : Int) atom1346) := by
  rw [SparsePolynomial.eval_scale, eval_atom1346]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 13) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1347 : SparsePolynomial.Poly := [([7,13,19], 1)]
theorem eval_atom1347 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1347 = ((g 7) * (g 13) * (g 19)) := by
  norm_num [atom1347, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1347_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47292853414464 : Int) atom1347) := by
  rw [SparsePolynomial.eval_scale, eval_atom1347]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 13) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1348 : SparsePolynomial.Poly := [([7,13,20], 1)]
theorem eval_atom1348 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1348 = ((g 7) * (g 13) * (g 20)) := by
  norm_num [atom1348, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1348_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (64416097821600 : Int) atom1348) := by
  rw [SparsePolynomial.eval_scale, eval_atom1348]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 13) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1349 : SparsePolynomial.Poly := [([7,14,14], 1)]
theorem eval_atom1349 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1349 = ((g 7) * (g 14) * (g 14)) := by
  norm_num [atom1349, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1349_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (14909899939200 : Int) atom1349) := by
  rw [SparsePolynomial.eval_scale, eval_atom1349]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 7) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1350 : SparsePolynomial.Poly := [([7,14,15], 1)]
theorem eval_atom1350 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1350 = ((g 7) * (g 14) * (g 15)) := by
  norm_num [atom1350, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1350_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29392479133056 : Int) atom1350) := by
  rw [SparsePolynomial.eval_scale, eval_atom1350]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 14) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1351 : SparsePolynomial.Poly := [([7,14,16], 1)]
theorem eval_atom1351 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1351 = ((g 7) * (g 14) * (g 16)) := by
  norm_num [atom1351, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1351_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (29069478282240 : Int) atom1351) := by
  rw [SparsePolynomial.eval_scale, eval_atom1351]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 14) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1352 : SparsePolynomial.Poly := [([7,14,17], 1)]
theorem eval_atom1352 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1352 = ((g 7) * (g 14) * (g 17)) := by
  norm_num [atom1352, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1352_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (49592493970560 : Int) atom1352) := by
  rw [SparsePolynomial.eval_scale, eval_atom1352]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 14) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1353 : SparsePolynomial.Poly := [([7,14,18], 1)]
theorem eval_atom1353 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1353 = ((g 7) * (g 14) * (g 18)) := by
  norm_num [atom1353, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1353_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55850131448640 : Int) atom1353) := by
  rw [SparsePolynomial.eval_scale, eval_atom1353]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 14) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1354 : SparsePolynomial.Poly := [([7,14,19], 1)]
theorem eval_atom1354 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1354 = ((g 7) * (g 14) * (g 19)) := by
  norm_num [atom1354, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1354_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (55138349470464 : Int) atom1354) := by
  rw [SparsePolynomial.eval_scale, eval_atom1354]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 14) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1355 : SparsePolynomial.Poly := [([7,14,20], 1)]
theorem eval_atom1355 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1355 = ((g 7) * (g 14) * (g 20)) := by
  norm_num [atom1355, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1355_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (78532122866400 : Int) atom1355) := by
  rw [SparsePolynomial.eval_scale, eval_atom1355]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 14) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1356 : SparsePolynomial.Poly := [([7,15,15], 1)]
theorem eval_atom1356 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1356 = ((g 7) * (g 15) * (g 15)) := by
  norm_num [atom1356, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1356_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (21896742731904 : Int) atom1356) := by
  rw [SparsePolynomial.eval_scale, eval_atom1356]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 7) * (g 15) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1357 : SparsePolynomial.Poly := [([7,15,16], 1)]
theorem eval_atom1357 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1357 = ((g 7) * (g 15) * (g 16)) := by
  norm_num [atom1357, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1357_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (42928095901824 : Int) atom1357) := by
  rw [SparsePolynomial.eval_scale, eval_atom1357]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 15) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1358 : SparsePolynomial.Poly := [([7,15,17], 1)]
theorem eval_atom1358 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1358 = ((g 7) * (g 15) * (g 17)) := by
  norm_num [atom1358, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1358_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (68414874110208 : Int) atom1358) := by
  rw [SparsePolynomial.eval_scale, eval_atom1358]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 15) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1359 : SparsePolynomial.Poly := [([7,15,18], 1)]
theorem eval_atom1359 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1359 = ((g 7) * (g 15) * (g 18)) := by
  norm_num [atom1359, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1359_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (71594005599360 : Int) atom1359) := by
  rw [SparsePolynomial.eval_scale, eval_atom1359]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 15) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1360 : SparsePolynomial.Poly := [([7,15,19], 1)]
theorem eval_atom1360 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1360 = ((g 7) * (g 15) * (g 19)) := by
  norm_num [atom1360, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1360_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (53238031188480 : Int) atom1360) := by
  rw [SparsePolynomial.eval_scale, eval_atom1360]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 15) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1361 : SparsePolynomial.Poly := [([7,15,20], 1)]
theorem eval_atom1361 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1361 = ((g 7) * (g 15) * (g 20)) := by
  norm_num [atom1361, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1361_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (80901900693504 : Int) atom1361) := by
  rw [SparsePolynomial.eval_scale, eval_atom1361]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 15) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1362 : SparsePolynomial.Poly := [([7,16,16], 1)]
theorem eval_atom1362 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1362 = ((g 7) * (g 16) * (g 16)) := by
  norm_num [atom1362, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1362_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (17225211406464 : Int) atom1362) := by
  rw [SparsePolynomial.eval_scale, eval_atom1362]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 7) * (g 16) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1363 : SparsePolynomial.Poly := [([7,16,17], 1)]
theorem eval_atom1363 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1363 = ((g 7) * (g 16) * (g 17)) := by
  norm_num [atom1363, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1363_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (56900847134592 : Int) atom1363) := by
  rw [SparsePolynomial.eval_scale, eval_atom1363]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 16) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1364 : SparsePolynomial.Poly := [([7,16,18], 1)]
theorem eval_atom1364 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1364 = ((g 7) * (g 16) * (g 18)) := by
  norm_num [atom1364, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1364_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (63199359221184 : Int) atom1364) := by
  rw [SparsePolynomial.eval_scale, eval_atom1364]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 16) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1365 : SparsePolynomial.Poly := [([7,16,19], 1)]
theorem eval_atom1365 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1365 = ((g 7) * (g 16) * (g 19)) := by
  norm_num [atom1365, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1365_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (47004130814208 : Int) atom1365) := by
  rw [SparsePolynomial.eval_scale, eval_atom1365]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 16) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1366 : SparsePolynomial.Poly := [([7,16,20], 1)]
theorem eval_atom1366 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1366 = ((g 7) * (g 16) * (g 20)) := by
  norm_num [atom1366, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1366_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (59161605357600 : Int) atom1366) := by
  rw [SparsePolynomial.eval_scale, eval_atom1366]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 16) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1367 : SparsePolynomial.Poly := [([7,17,17], 1)]
theorem eval_atom1367 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1367 = ((g 7) * (g 17) * (g 17)) := by
  norm_num [atom1367, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1367_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (41545743986304 : Int) atom1367) := by
  rw [SparsePolynomial.eval_scale, eval_atom1367]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 7) * (g 17) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1368 : SparsePolynomial.Poly := [([7,17,18], 1)]
theorem eval_atom1368 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1368 = ((g 7) * (g 17) * (g 18)) := by
  norm_num [atom1368, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1368_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (70291863363456 : Int) atom1368) := by
  rw [SparsePolynomial.eval_scale, eval_atom1368]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 17) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1369 : SparsePolynomial.Poly := [([7,17,19], 1)]
theorem eval_atom1369 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1369 = ((g 7) * (g 17) * (g 19)) := by
  norm_num [atom1369, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1369_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (48185112168960 : Int) atom1369) := by
  rw [SparsePolynomial.eval_scale, eval_atom1369]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 17) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1370 : SparsePolynomial.Poly := [([7,17,20], 1)]
theorem eval_atom1370 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1370 = ((g 7) * (g 17) * (g 20)) := by
  norm_num [atom1370, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1370_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (51533139292416 : Int) atom1370) := by
  rw [SparsePolynomial.eval_scale, eval_atom1370]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 17) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1371 : SparsePolynomial.Poly := [([7,18,18], 1)]
theorem eval_atom1371 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1371 = ((g 7) * (g 18) * (g 18)) := by
  norm_num [atom1371, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1371_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (22921685971776 : Int) atom1371) := by
  rw [SparsePolynomial.eval_scale, eval_atom1371]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 7) * (g 18) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1372 : SparsePolynomial.Poly := [([7,18,19], 1)]
theorem eval_atom1372 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1372 = ((g 7) * (g 18) * (g 19)) := by
  norm_num [atom1372, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1372_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (27537164315136 : Int) atom1372) := by
  rw [SparsePolynomial.eval_scale, eval_atom1372]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 7) * (g 18) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1373 : SparsePolynomial.Poly := [([7,18,20], 1)]
theorem eval_atom1373 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1373 = ((g 7) * (g 18) * (g 20)) := by
  norm_num [atom1373, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1373_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (31480194875040 : Int) atom1373) := by
  rw [SparsePolynomial.eval_scale, eval_atom1373]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 7) * (g 18) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1374 : SparsePolynomial.Poly := [([8,8,8], 1)]
theorem eval_atom1374 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1374 = ((g 8) * (g 8) * (g 8)) := by
  norm_num [atom1374, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1374_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1353863952000 : Int) atom1374) := by
  rw [SparsePolynomial.eval_scale, eval_atom1374]
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 8) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1375 : SparsePolynomial.Poly := [([8,8,9], 1)]
theorem eval_atom1375 (g : Fin 21 → ℝ) : SparsePolynomial.eval (gapValues g) atom1375 = ((g 8) * (g 8) * (g 9)) := by
  norm_num [atom1375, SparsePolynomial.eval, SparsePolynomial.mon, gapValues]
  <;> ring
theorem atom1375_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) (SparsePolynomial.scale (1372387968000 : Int) atom1375) := by
  rw [SparsePolynomial.eval_scale, eval_atom1375]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block018 : SparsePolynomial.Poly := [([7,8,15], 6427474232112), ([7,8,17], 1510388496720), ([7,8,18], 5786258284800), ([7,8,19], 11171238059520), ([7,8,20], 17391151612800), ([7,9,9], 896401296000), ([7,9,12], 686193984000), ([7,9,13], 1372387968000), ([7,9,14], 2058581952000), ([7,9,15], 8185219145856), ([7,9,16], 3335794446240), ([7,9,17], 9115747148160), ([7,9,18], 13951505319840), ([7,9,19], 22686649344864), ([7,9,20], 32365160755200), ([7,10,10], 2262023971200), ([7,10,11], 3851384544000), ([7,10,12], 4201246828800), ([7,10,13], 4978289030400), ([7,10,14], 5755331232000), ([7,10,15], 13173656115456), ([7,10,16], 9544641913440), ([7,10,17], 18856319074560), ([7,10,18], 22426001022240), ([7,10,19], 32125924124064), ([7,10,20], 42511529440800), ([7,11,11], 4747785840000), ([7,11,12], 8318410732800), ([7,11,13], 9018135302400), ([7,11,14], 9717859872000), ([7,11,15], 17823714742656), ([7,11,16], 15047395107840), ([7,11,17], 27687575007360), ([7,11,18], 29300658949440), ([7,11,19], 39568321822464), ([7,11,20], 50335348946400), ([7,12,12], 7156230076800), ([7,12,13], 14339521324800), ([7,12,14], 14793762412800), ([7,12,15], 19441485123456), ([7,12,16], 19397114109440), ([7,12,17], 31352906629760), ([7,12,18], 34150544280640), ([7,12,19], 43898083947264), ([7,12,20], 54883075413600), ([7,13,13], 10477390550400), ([7,13,14], 19824839136000), ([7,13,15], 24472903179456), ([7,13,16], 24292870914240), ([7,13,17], 39375935372160), ([7,13,18], 43793896443840), ([7,13,19], 47292853414464), ([7,13,20], 64416097821600), ([7,14,14], 14909899939200), ([7,14,15], 29392479133056), ([7,14,16], 29069478282240), ([7,14,17], 49592493970560), ([7,14,18], 55850131448640), ([7,14,19], 55138349470464), ([7,14,20], 78532122866400), ([7,15,15], 21896742731904), ([7,15,16], 42928095901824), ([7,15,17], 68414874110208), ([7,15,18], 71594005599360), ([7,15,19], 53238031188480), ([7,15,20], 80901900693504), ([7,16,16], 17225211406464), ([7,16,17], 56900847134592), ([7,16,18], 63199359221184), ([7,16,19], 47004130814208), ([7,16,20], 59161605357600), ([7,17,17], 41545743986304), ([7,17,18], 70291863363456), ([7,17,19], 48185112168960), ([7,17,20], 51533139292416), ([7,18,18], 22921685971776), ([7,18,19], 27537164315136), ([7,18,20], 31480194875040), ([8,8,8], 1353863952000), ([8,8,9], 1372387968000)]
theorem block018_data : block018 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (6427474232112 : Int) atom1296) (SparsePolynomial.scale (1510388496720 : Int) atom1297)) (SparsePolynomial.merge (SparsePolynomial.scale (5786258284800 : Int) atom1298) (SparsePolynomial.merge (SparsePolynomial.scale (11171238059520 : Int) atom1299) (SparsePolynomial.scale (17391151612800 : Int) atom1300)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (896401296000 : Int) atom1301) (SparsePolynomial.scale (686193984000 : Int) atom1302)) (SparsePolynomial.merge (SparsePolynomial.scale (1372387968000 : Int) atom1303) (SparsePolynomial.merge (SparsePolynomial.scale (2058581952000 : Int) atom1304) (SparsePolynomial.scale (8185219145856 : Int) atom1305))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3335794446240 : Int) atom1306) (SparsePolynomial.scale (9115747148160 : Int) atom1307)) (SparsePolynomial.merge (SparsePolynomial.scale (13951505319840 : Int) atom1308) (SparsePolynomial.merge (SparsePolynomial.scale (22686649344864 : Int) atom1309) (SparsePolynomial.scale (32365160755200 : Int) atom1310)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (2262023971200 : Int) atom1311) (SparsePolynomial.scale (3851384544000 : Int) atom1312)) (SparsePolynomial.merge (SparsePolynomial.scale (4201246828800 : Int) atom1313) (SparsePolynomial.merge (SparsePolynomial.scale (4978289030400 : Int) atom1314) (SparsePolynomial.scale (5755331232000 : Int) atom1315)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13173656115456 : Int) atom1316) (SparsePolynomial.scale (9544641913440 : Int) atom1317)) (SparsePolynomial.merge (SparsePolynomial.scale (18856319074560 : Int) atom1318) (SparsePolynomial.merge (SparsePolynomial.scale (22426001022240 : Int) atom1319) (SparsePolynomial.scale (32125924124064 : Int) atom1320)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (42511529440800 : Int) atom1321) (SparsePolynomial.scale (4747785840000 : Int) atom1322)) (SparsePolynomial.merge (SparsePolynomial.scale (8318410732800 : Int) atom1323) (SparsePolynomial.merge (SparsePolynomial.scale (9018135302400 : Int) atom1324) (SparsePolynomial.scale (9717859872000 : Int) atom1325))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (17823714742656 : Int) atom1326) (SparsePolynomial.scale (15047395107840 : Int) atom1327)) (SparsePolynomial.merge (SparsePolynomial.scale (27687575007360 : Int) atom1328) (SparsePolynomial.merge (SparsePolynomial.scale (29300658949440 : Int) atom1329) (SparsePolynomial.scale (39568321822464 : Int) atom1330)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (50335348946400 : Int) atom1331) (SparsePolynomial.scale (7156230076800 : Int) atom1332)) (SparsePolynomial.merge (SparsePolynomial.scale (14339521324800 : Int) atom1333) (SparsePolynomial.merge (SparsePolynomial.scale (14793762412800 : Int) atom1334) (SparsePolynomial.scale (19441485123456 : Int) atom1335))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (19397114109440 : Int) atom1336) (SparsePolynomial.scale (31352906629760 : Int) atom1337)) (SparsePolynomial.merge (SparsePolynomial.scale (34150544280640 : Int) atom1338) (SparsePolynomial.merge (SparsePolynomial.scale (43898083947264 : Int) atom1339) (SparsePolynomial.scale (54883075413600 : Int) atom1340)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (10477390550400 : Int) atom1341) (SparsePolynomial.scale (19824839136000 : Int) atom1342)) (SparsePolynomial.merge (SparsePolynomial.scale (24472903179456 : Int) atom1343) (SparsePolynomial.merge (SparsePolynomial.scale (24292870914240 : Int) atom1344) (SparsePolynomial.scale (39375935372160 : Int) atom1345))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (43793896443840 : Int) atom1346) (SparsePolynomial.scale (47292853414464 : Int) atom1347)) (SparsePolynomial.merge (SparsePolynomial.scale (64416097821600 : Int) atom1348) (SparsePolynomial.merge (SparsePolynomial.scale (14909899939200 : Int) atom1349) (SparsePolynomial.scale (29392479133056 : Int) atom1350)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (29069478282240 : Int) atom1351) (SparsePolynomial.scale (49592493970560 : Int) atom1352)) (SparsePolynomial.merge (SparsePolynomial.scale (55850131448640 : Int) atom1353) (SparsePolynomial.merge (SparsePolynomial.scale (55138349470464 : Int) atom1354) (SparsePolynomial.scale (78532122866400 : Int) atom1355)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (21896742731904 : Int) atom1356) (SparsePolynomial.scale (42928095901824 : Int) atom1357)) (SparsePolynomial.merge (SparsePolynomial.scale (68414874110208 : Int) atom1358) (SparsePolynomial.merge (SparsePolynomial.scale (71594005599360 : Int) atom1359) (SparsePolynomial.scale (53238031188480 : Int) atom1360)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (80901900693504 : Int) atom1361) (SparsePolynomial.scale (17225211406464 : Int) atom1362)) (SparsePolynomial.merge (SparsePolynomial.scale (56900847134592 : Int) atom1363) (SparsePolynomial.merge (SparsePolynomial.scale (63199359221184 : Int) atom1364) (SparsePolynomial.scale (47004130814208 : Int) atom1365))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (59161605357600 : Int) atom1366) (SparsePolynomial.scale (41545743986304 : Int) atom1367)) (SparsePolynomial.merge (SparsePolynomial.scale (70291863363456 : Int) atom1368) (SparsePolynomial.merge (SparsePolynomial.scale (48185112168960 : Int) atom1369) (SparsePolynomial.scale (51533139292416 : Int) atom1370)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (22921685971776 : Int) atom1371) (SparsePolynomial.scale (27537164315136 : Int) atom1372)) (SparsePolynomial.merge (SparsePolynomial.scale (31480194875040 : Int) atom1373) (SparsePolynomial.merge (SparsePolynomial.scale (1353863952000 : Int) atom1374) (SparsePolynomial.scale (1372387968000 : Int) atom1375)))))))) := by decide +kernel
theorem block018_nonneg (g : Fin 21 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (gapValues g) block018 := by
  rw [block018_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1296_nonneg g hg hA hB) (atom1297_nonneg g hg hA hB)) (add_nonneg (atom1298_nonneg g hg hA hB) (add_nonneg (atom1299_nonneg g hg hA hB) (atom1300_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1301_nonneg g hg hA hB) (atom1302_nonneg g hg hA hB)) (add_nonneg (atom1303_nonneg g hg hA hB) (add_nonneg (atom1304_nonneg g hg hA hB) (atom1305_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1306_nonneg g hg hA hB) (atom1307_nonneg g hg hA hB)) (add_nonneg (atom1308_nonneg g hg hA hB) (add_nonneg (atom1309_nonneg g hg hA hB) (atom1310_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1311_nonneg g hg hA hB) (atom1312_nonneg g hg hA hB)) (add_nonneg (atom1313_nonneg g hg hA hB) (add_nonneg (atom1314_nonneg g hg hA hB) (atom1315_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1316_nonneg g hg hA hB) (atom1317_nonneg g hg hA hB)) (add_nonneg (atom1318_nonneg g hg hA hB) (add_nonneg (atom1319_nonneg g hg hA hB) (atom1320_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1321_nonneg g hg hA hB) (atom1322_nonneg g hg hA hB)) (add_nonneg (atom1323_nonneg g hg hA hB) (add_nonneg (atom1324_nonneg g hg hA hB) (atom1325_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1326_nonneg g hg hA hB) (atom1327_nonneg g hg hA hB)) (add_nonneg (atom1328_nonneg g hg hA hB) (add_nonneg (atom1329_nonneg g hg hA hB) (atom1330_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1331_nonneg g hg hA hB) (atom1332_nonneg g hg hA hB)) (add_nonneg (atom1333_nonneg g hg hA hB) (add_nonneg (atom1334_nonneg g hg hA hB) (atom1335_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1336_nonneg g hg hA hB) (atom1337_nonneg g hg hA hB)) (add_nonneg (atom1338_nonneg g hg hA hB) (add_nonneg (atom1339_nonneg g hg hA hB) (atom1340_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1341_nonneg g hg hA hB) (atom1342_nonneg g hg hA hB)) (add_nonneg (atom1343_nonneg g hg hA hB) (add_nonneg (atom1344_nonneg g hg hA hB) (atom1345_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1346_nonneg g hg hA hB) (atom1347_nonneg g hg hA hB)) (add_nonneg (atom1348_nonneg g hg hA hB) (add_nonneg (atom1349_nonneg g hg hA hB) (atom1350_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1351_nonneg g hg hA hB) (atom1352_nonneg g hg hA hB)) (add_nonneg (atom1353_nonneg g hg hA hB) (add_nonneg (atom1354_nonneg g hg hA hB) (atom1355_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1356_nonneg g hg hA hB) (atom1357_nonneg g hg hA hB)) (add_nonneg (atom1358_nonneg g hg hA hB) (add_nonneg (atom1359_nonneg g hg hA hB) (atom1360_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1361_nonneg g hg hA hB) (atom1362_nonneg g hg hA hB)) (add_nonneg (atom1363_nonneg g hg hA hB) (add_nonneg (atom1364_nonneg g hg hA hB) (atom1365_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1366_nonneg g hg hA hB) (atom1367_nonneg g hg hA hB)) (add_nonneg (atom1368_nonneg g hg hA hB) (add_nonneg (atom1369_nonneg g hg hA hB) (atom1370_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1371_nonneg g hg hA hB) (atom1372_nonneg g hg hA hB)) (add_nonneg (atom1373_nonneg g hg hA hB) (add_nonneg (atom1374_nonneg g hg hA hB) (atom1375_nonneg g hg hA hB))))))))

end APPT.Finite21
