import APPT.Finite24Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite24
open SparsePolynomial

def atom1249 : SparsePolynomial.Poly := [([3,20,21], 1)]
theorem eval_atom1249 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1249 = ((g 3) * (g 20) * (g 21)) := by
  norm_num [atom1249, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1249_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (519056458905600 : Int) atom1249) := by
  rw [SparsePolynomial.eval_scale, eval_atom1249]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 20) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1250 : SparsePolynomial.Poly := [([3,20,22], 1)]
theorem eval_atom1250 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1250 = ((g 3) * (g 20) * (g 22)) := by
  norm_num [atom1250, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1250_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (358976744985600 : Int) atom1250) := by
  rw [SparsePolynomial.eval_scale, eval_atom1250]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 20) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1251 : SparsePolynomial.Poly := [([3,20,23], 1)]
theorem eval_atom1251 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1251 = ((g 3) * (g 20) * (g 23)) := by
  norm_num [atom1251, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1251_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (415551344947200 : Int) atom1251) := by
  rw [SparsePolynomial.eval_scale, eval_atom1251]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg20 : 0 ≤ g 20 := hg 20
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 20) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1252 : SparsePolynomial.Poly := [([3,21,21], 1)]
theorem eval_atom1252 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1252 = ((g 3) * (g 21) * (g 21)) := by
  norm_num [atom1252, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1252_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (149899559040000 : Int) atom1252) := by
  rw [SparsePolynomial.eval_scale, eval_atom1252]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 3) * (g 21) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1253 : SparsePolynomial.Poly := [([3,21,22], 1)]
theorem eval_atom1253 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1253 = ((g 3) * (g 21) * (g 22)) := by
  norm_num [atom1253, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1253_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (193568557593600 : Int) atom1253) := by
  rw [SparsePolynomial.eval_scale, eval_atom1253]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg21 : 0 ≤ g 21 := hg 21
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 3) * (g 21) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1254 : SparsePolynomial.Poly := [([3,21,23], 1)]
theorem eval_atom1254 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1254 = ((g 3) * (g 21) * (g 23)) := by
  norm_num [atom1254, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1254_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (256657812364800 : Int) atom1254) := by
  rw [SparsePolynomial.eval_scale, eval_atom1254]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg21 : 0 ≤ g 21 := hg 21
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 21) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1255 : SparsePolynomial.Poly := [([3,22,23], 1)]
theorem eval_atom1255 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1255 = ((g 3) * (g 22) * (g 23)) := by
  norm_num [atom1255, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1255_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (65611984132800 : Int) atom1255) := by
  rw [SparsePolynomial.eval_scale, eval_atom1255]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg22 : 0 ≤ g 22 := hg 22
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 22) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1256 : SparsePolynomial.Poly := [([3,23,23], 1)]
theorem eval_atom1256 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1256 = ((g 3) * (g 23) * (g 23)) := by
  norm_num [atom1256, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1256_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (81519845299200 : Int) atom1256) := by
  rw [SparsePolynomial.eval_scale, eval_atom1256]
  have hg3 : 0 ≤ g 3 := hg 3
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 3) * (g 23) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1257 : SparsePolynomial.Poly := [([4,4,4], 1)]
theorem eval_atom1257 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1257 = ((g 4) * (g 4) * (g 4)) := by
  norm_num [atom1257, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1257_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19145134310400 : Int) atom1257) := by
  rw [SparsePolynomial.eval_scale, eval_atom1257]
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 4) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1258 : SparsePolynomial.Poly := [([4,4,5], 1)]
theorem eval_atom1258 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1258 = ((g 4) * (g 4) * (g 5)) := by
  norm_num [atom1258, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1258_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (33284636169696 : Int) atom1258) := by
  rw [SparsePolynomial.eval_scale, eval_atom1258]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1259 : SparsePolynomial.Poly := [([4,4,6], 1)]
theorem eval_atom1259 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1259 = ((g 4) * (g 4) * (g 6)) := by
  norm_num [atom1259, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1259_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12426232089600 : Int) atom1259) := by
  rw [SparsePolynomial.eval_scale, eval_atom1259]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1260 : SparsePolynomial.Poly := [([4,4,7], 1)]
theorem eval_atom1260 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1260 = ((g 4) * (g 4) * (g 7)) := by
  norm_num [atom1260, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1260_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (7216956633600 : Int) atom1260) := by
  rw [SparsePolynomial.eval_scale, eval_atom1260]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1261 : SparsePolynomial.Poly := [([4,4,8], 1)]
theorem eval_atom1261 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1261 = ((g 4) * (g 4) * (g 8)) := by
  norm_num [atom1261, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1261_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2007681177600 : Int) atom1261) := by
  rw [SparsePolynomial.eval_scale, eval_atom1261]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1262 : SparsePolynomial.Poly := [([4,4,9], 1)]
theorem eval_atom1262 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1262 = ((g 4) * (g 4) * (g 9)) := by
  norm_num [atom1262, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1262_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2810186767728 : Int) atom1262) := by
  rw [SparsePolynomial.eval_scale, eval_atom1262]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1263 : SparsePolynomial.Poly := [([4,4,10], 1)]
theorem eval_atom1263 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1263 = ((g 4) * (g 4) * (g 10)) := by
  norm_num [atom1263, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1263_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15244408345968 : Int) atom1263) := by
  rw [SparsePolynomial.eval_scale, eval_atom1263]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1264 : SparsePolynomial.Poly := [([4,4,11], 1)]
theorem eval_atom1264 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1264 = ((g 4) * (g 4) * (g 11)) := by
  norm_num [atom1264, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1264_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26040202684704 : Int) atom1264) := by
  rw [SparsePolynomial.eval_scale, eval_atom1264]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1265 : SparsePolynomial.Poly := [([4,4,12], 1)]
theorem eval_atom1265 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1265 = ((g 4) * (g 4) * (g 12)) := by
  norm_num [atom1265, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1265_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48752909452224 : Int) atom1265) := by
  rw [SparsePolynomial.eval_scale, eval_atom1265]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1266 : SparsePolynomial.Poly := [([4,4,13], 1)]
theorem eval_atom1266 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1266 = ((g 4) * (g 4) * (g 13)) := by
  norm_num [atom1266, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1266_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34882503465600 : Int) atom1266) := by
  rw [SparsePolynomial.eval_scale, eval_atom1266]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1267 : SparsePolynomial.Poly := [([4,4,14], 1)]
theorem eval_atom1267 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1267 = ((g 4) * (g 4) * (g 14)) := by
  norm_num [atom1267, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1267_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17337834662400 : Int) atom1267) := by
  rw [SparsePolynomial.eval_scale, eval_atom1267]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1268 : SparsePolynomial.Poly := [([4,4,15], 1)]
theorem eval_atom1268 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1268 = ((g 4) * (g 4) * (g 15)) := by
  norm_num [atom1268, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1268_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (14580172454400 : Int) atom1268) := by
  rw [SparsePolynomial.eval_scale, eval_atom1268]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 4) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1269 : SparsePolynomial.Poly := [([4,4,18], 1)]
theorem eval_atom1269 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1269 = ((g 4) * (g 4) * (g 18)) := by
  norm_num [atom1269, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1269_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (18173912097600 : Int) atom1269) := by
  rw [SparsePolynomial.eval_scale, eval_atom1269]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 4) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1270 : SparsePolynomial.Poly := [([4,5,5], 1)]
theorem eval_atom1270 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1270 = ((g 4) * (g 5) * (g 5)) := by
  norm_num [atom1270, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1270_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (37193995228896 : Int) atom1270) := by
  rw [SparsePolynomial.eval_scale, eval_atom1270]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 4) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1271 : SparsePolynomial.Poly := [([4,5,6], 1)]
theorem eval_atom1271 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1271 = ((g 4) * (g 5) * (g 6)) := by
  norm_num [atom1271, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1271_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (29044448275392 : Int) atom1271) := by
  rw [SparsePolynomial.eval_scale, eval_atom1271]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1272 : SparsePolynomial.Poly := [([4,5,7], 1)]
theorem eval_atom1272 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1272 = ((g 4) * (g 5) * (g 7)) := by
  norm_num [atom1272, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1272_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2242076371392 : Int) atom1272) := by
  rw [SparsePolynomial.eval_scale, eval_atom1272]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1273 : SparsePolynomial.Poly := [([4,5,9], 1)]
theorem eval_atom1273 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1273 = ((g 4) * (g 5) * (g 9)) := by
  norm_num [atom1273, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1273_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3077576911728 : Int) atom1273) := by
  rw [SparsePolynomial.eval_scale, eval_atom1273]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1274 : SparsePolynomial.Poly := [([4,5,10], 1)]
theorem eval_atom1274 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1274 = ((g 4) * (g 5) * (g 10)) := by
  norm_num [atom1274, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1274_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (12869199875664 : Int) atom1274) := by
  rw [SparsePolynomial.eval_scale, eval_atom1274]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 5) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1275 : SparsePolynomial.Poly := [([4,5,11], 1)]
theorem eval_atom1275 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1275 = ((g 4) * (g 5) * (g 11)) := by
  norm_num [atom1275, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1275_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (29390633404704 : Int) atom1275) := by
  rw [SparsePolynomial.eval_scale, eval_atom1275]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1276 : SparsePolynomial.Poly := [([4,5,12], 1)]
theorem eval_atom1276 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1276 = ((g 4) * (g 5) * (g 12)) := by
  norm_num [atom1276, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1276_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (79919010651744 : Int) atom1276) := by
  rw [SparsePolynomial.eval_scale, eval_atom1276]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 5) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1277 : SparsePolynomial.Poly := [([4,5,13], 1)]
theorem eval_atom1277 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1277 = ((g 4) * (g 5) * (g 13)) := by
  norm_num [atom1277, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1277_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (57281162390496 : Int) atom1277) := by
  rw [SparsePolynomial.eval_scale, eval_atom1277]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 5) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1278 : SparsePolynomial.Poly := [([4,5,14], 1)]
theorem eval_atom1278 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1278 = ((g 4) * (g 5) * (g 14)) := by
  norm_num [atom1278, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1278_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27294788496096 : Int) atom1278) := by
  rw [SparsePolynomial.eval_scale, eval_atom1278]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 5) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1279 : SparsePolynomial.Poly := [([4,5,15], 1)]
theorem eval_atom1279 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1279 = ((g 4) * (g 5) * (g 15)) := by
  norm_num [atom1279, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1279_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27620166864096 : Int) atom1279) := by
  rw [SparsePolynomial.eval_scale, eval_atom1279]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 5) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1280 : SparsePolynomial.Poly := [([4,5,16], 1)]
theorem eval_atom1280 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1280 = ((g 4) * (g 5) * (g 16)) := by
  norm_num [atom1280, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1280_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (16123034985696 : Int) atom1280) := by
  rw [SparsePolynomial.eval_scale, eval_atom1280]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 5) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1281 : SparsePolynomial.Poly := [([4,5,17], 1)]
theorem eval_atom1281 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1281 = ((g 4) * (g 5) * (g 17)) := by
  norm_num [atom1281, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1281_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19206075561696 : Int) atom1281) := by
  rw [SparsePolynomial.eval_scale, eval_atom1281]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 5) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1282 : SparsePolynomial.Poly := [([4,5,18], 1)]
theorem eval_atom1282 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1282 = ((g 4) * (g 5) * (g 18)) := by
  norm_num [atom1282, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1282_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (49319508264048 : Int) atom1282) := by
  rw [SparsePolynomial.eval_scale, eval_atom1282]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 5) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1283 : SparsePolynomial.Poly := [([4,5,19], 1)]
theorem eval_atom1283 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1283 = ((g 4) * (g 5) * (g 19)) := by
  norm_num [atom1283, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1283_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (36196508174400 : Int) atom1283) := by
  rw [SparsePolynomial.eval_scale, eval_atom1283]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 5) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1284 : SparsePolynomial.Poly := [([4,5,20], 1)]
theorem eval_atom1284 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1284 = ((g 4) * (g 5) * (g 20)) := by
  norm_num [atom1284, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1284_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47956822204752 : Int) atom1284) := by
  rw [SparsePolynomial.eval_scale, eval_atom1284]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 5) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1285 : SparsePolynomial.Poly := [([4,5,21], 1)]
theorem eval_atom1285 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1285 = ((g 4) * (g 5) * (g 21)) := by
  norm_num [atom1285, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1285_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (74969085851928 : Int) atom1285) := by
  rw [SparsePolynomial.eval_scale, eval_atom1285]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 5) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1286 : SparsePolynomial.Poly := [([4,5,22], 1)]
theorem eval_atom1286 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1286 = ((g 4) * (g 5) * (g 22)) := by
  norm_num [atom1286, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1286_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (101981349499104 : Int) atom1286) := by
  rw [SparsePolynomial.eval_scale, eval_atom1286]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 5) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1287 : SparsePolynomial.Poly := [([4,5,23], 1)]
theorem eval_atom1287 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1287 = ((g 4) * (g 5) * (g 23)) := by
  norm_num [atom1287, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1287_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (130089392506692 : Int) atom1287) := by
  rw [SparsePolynomial.eval_scale, eval_atom1287]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 5) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1288 : SparsePolynomial.Poly := [([4,6,6], 1)]
theorem eval_atom1288 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1288 = ((g 4) * (g 6) * (g 6)) := by
  norm_num [atom1288, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1288_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (25323457420800 : Int) atom1288) := by
  rw [SparsePolynomial.eval_scale, eval_atom1288]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 4) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1289 : SparsePolynomial.Poly := [([4,6,7], 1)]
theorem eval_atom1289 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1289 = ((g 4) * (g 6) * (g 7)) := by
  norm_num [atom1289, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1289_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (22823950195200 : Int) atom1289) := by
  rw [SparsePolynomial.eval_scale, eval_atom1289]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1290 : SparsePolynomial.Poly := [([4,6,8], 1)]
theorem eval_atom1290 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1290 = ((g 4) * (g 6) * (g 8)) := by
  norm_num [atom1290, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1290_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (850493952000 : Int) atom1290) := by
  rw [SparsePolynomial.eval_scale, eval_atom1290]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1291 : SparsePolynomial.Poly := [([4,6,9], 1)]
theorem eval_atom1291 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1291 = ((g 4) * (g 6) * (g 9)) := by
  norm_num [atom1291, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1291_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (4523416630128 : Int) atom1291) := by
  rw [SparsePolynomial.eval_scale, eval_atom1291]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1292 : SparsePolynomial.Poly := [([4,6,10], 1)]
theorem eval_atom1292 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1292 = ((g 4) * (g 6) * (g 10)) := by
  norm_num [atom1292, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1292_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (24745725232272 : Int) atom1292) := by
  rw [SparsePolynomial.eval_scale, eval_atom1292]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1293 : SparsePolynomial.Poly := [([4,6,11], 1)]
theorem eval_atom1293 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1293 = ((g 4) * (g 6) * (g 11)) := by
  norm_num [atom1293, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1293_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34961368790304 : Int) atom1293) := by
  rw [SparsePolynomial.eval_scale, eval_atom1293]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1294 : SparsePolynomial.Poly := [([4,6,12], 1)]
theorem eval_atom1294 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1294 = ((g 4) * (g 6) * (g 12)) := by
  norm_num [atom1294, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1294_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (60757116133824 : Int) atom1294) := by
  rw [SparsePolynomial.eval_scale, eval_atom1294]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1295 : SparsePolynomial.Poly := [([4,6,13], 1)]
theorem eval_atom1295 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1295 = ((g 4) * (g 6) * (g 13)) := by
  norm_num [atom1295, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1295_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (52032198556800 : Int) atom1295) := by
  rw [SparsePolynomial.eval_scale, eval_atom1295]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1296 : SparsePolynomial.Poly := [([4,6,14], 1)]
theorem eval_atom1296 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1296 = ((g 4) * (g 6) * (g 14)) := by
  norm_num [atom1296, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1296_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39633018163200 : Int) atom1296) := by
  rw [SparsePolynomial.eval_scale, eval_atom1296]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1297 : SparsePolynomial.Poly := [([4,6,15], 1)]
theorem eval_atom1297 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1297 = ((g 4) * (g 6) * (g 15)) := by
  norm_num [atom1297, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1297_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (42020844364800 : Int) atom1297) := by
  rw [SparsePolynomial.eval_scale, eval_atom1297]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 6) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1298 : SparsePolynomial.Poly := [([4,6,16], 1)]
theorem eval_atom1298 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1298 = ((g 4) * (g 6) * (g 16)) := by
  norm_num [atom1298, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1298_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (32586160320000 : Int) atom1298) := by
  rw [SparsePolynomial.eval_scale, eval_atom1298]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 6) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1299 : SparsePolynomial.Poly := [([4,6,17], 1)]
theorem eval_atom1299 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1299 = ((g 4) * (g 6) * (g 17)) := by
  norm_num [atom1299, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1299_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (37731648729600 : Int) atom1299) := by
  rw [SparsePolynomial.eval_scale, eval_atom1299]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 6) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1300 : SparsePolynomial.Poly := [([4,6,18], 1)]
theorem eval_atom1300 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1300 = ((g 4) * (g 6) * (g 18)) := by
  norm_num [atom1300, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1300_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (71505279014400 : Int) atom1300) := by
  rw [SparsePolynomial.eval_scale, eval_atom1300]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 6) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1301 : SparsePolynomial.Poly := [([4,6,19], 1)]
theorem eval_atom1301 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1301 = ((g 4) * (g 6) * (g 19)) := by
  norm_num [atom1301, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1301_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (79385314881600 : Int) atom1301) := by
  rw [SparsePolynomial.eval_scale, eval_atom1301]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 6) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1302 : SparsePolynomial.Poly := [([4,6,20], 1)]
theorem eval_atom1302 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1302 = ((g 4) * (g 6) * (g 20)) := by
  norm_num [atom1302, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1302_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (105439262846400 : Int) atom1302) := by
  rw [SparsePolynomial.eval_scale, eval_atom1302]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 6) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1303 : SparsePolynomial.Poly := [([4,6,21], 1)]
theorem eval_atom1303 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1303 = ((g 4) * (g 6) * (g 21)) := by
  norm_num [atom1303, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1303_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (152401670366400 : Int) atom1303) := by
  rw [SparsePolynomial.eval_scale, eval_atom1303]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 6) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1304 : SparsePolynomial.Poly := [([4,6,22], 1)]
theorem eval_atom1304 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1304 = ((g 4) * (g 6) * (g 22)) := by
  norm_num [atom1304, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1304_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (199364077886400 : Int) atom1304) := by
  rw [SparsePolynomial.eval_scale, eval_atom1304]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 6) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1305 : SparsePolynomial.Poly := [([4,6,23], 1)]
theorem eval_atom1305 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1305 = ((g 4) * (g 6) * (g 23)) := by
  norm_num [atom1305, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1305_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (246326485406400 : Int) atom1305) := by
  rw [SparsePolynomial.eval_scale, eval_atom1305]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 6) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1306 : SparsePolynomial.Poly := [([4,7,7], 1)]
theorem eval_atom1306 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1306 = ((g 4) * (g 7) * (g 7)) := by
  norm_num [atom1306, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1306_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28330898534400 : Int) atom1306) := by
  rw [SparsePolynomial.eval_scale, eval_atom1306]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 4) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1307 : SparsePolynomial.Poly := [([4,7,8], 1)]
theorem eval_atom1307 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1307 = ((g 4) * (g 7) * (g 8)) := by
  norm_num [atom1307, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1307_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (41917539417600 : Int) atom1307) := by
  rw [SparsePolynomial.eval_scale, eval_atom1307]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1308 : SparsePolynomial.Poly := [([4,7,9], 1)]
theorem eval_atom1308 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1308 = ((g 4) * (g 7) * (g 9)) := by
  norm_num [atom1308, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1308_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30177621698928 : Int) atom1308) := by
  rw [SparsePolynomial.eval_scale, eval_atom1308]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1309 : SparsePolynomial.Poly := [([4,7,10], 1)]
theorem eval_atom1309 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1309 = ((g 4) * (g 7) * (g 10)) := by
  norm_num [atom1309, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1309_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (49379337558672 : Int) atom1309) := by
  rw [SparsePolynomial.eval_scale, eval_atom1309]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1310 : SparsePolynomial.Poly := [([4,7,11], 1)]
theorem eval_atom1310 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1310 = ((g 4) * (g 7) * (g 11)) := by
  norm_num [atom1310, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1310_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (62699284041504 : Int) atom1310) := by
  rw [SparsePolynomial.eval_scale, eval_atom1310]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1311 : SparsePolynomial.Poly := [([4,7,12], 1)]
theorem eval_atom1311 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1311 = ((g 4) * (g 7) * (g 12)) := by
  norm_num [atom1311, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1311_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (91599334309824 : Int) atom1311) := by
  rw [SparsePolynomial.eval_scale, eval_atom1311]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1312 : SparsePolynomial.Poly := [([4,7,13], 1)]
theorem eval_atom1312 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1312 = ((g 4) * (g 7) * (g 13)) := by
  norm_num [atom1312, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1312_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (83916271824000 : Int) atom1312) := by
  rw [SparsePolynomial.eval_scale, eval_atom1312]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1313 : SparsePolynomial.Poly := [([4,7,14], 1)]
theorem eval_atom1313 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1313 = ((g 4) * (g 7) * (g 14)) := by
  norm_num [atom1313, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1313_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (72558946521600 : Int) atom1313) := by
  rw [SparsePolynomial.eval_scale, eval_atom1313]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 4) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1314 : SparsePolynomial.Poly := [([4,7,15], 1)]
theorem eval_atom1314 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1314 = ((g 4) * (g 7) * (g 15)) := by
  norm_num [atom1314, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1314_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (75988627814400 : Int) atom1314) := by
  rw [SparsePolynomial.eval_scale, eval_atom1314]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg15 : 0 ≤ g 15 := hg 15
  have ht : 0 ≤ ((g 4) * (g 7) * (g 15)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1315 : SparsePolynomial.Poly := [([4,7,16], 1)]
theorem eval_atom1315 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1315 = ((g 4) * (g 7) * (g 16)) := by
  norm_num [atom1315, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1315_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (67595798860800 : Int) atom1315) := by
  rw [SparsePolynomial.eval_scale, eval_atom1315]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg16 : 0 ≤ g 16 := hg 16
  have ht : 0 ≤ ((g 4) * (g 7) * (g 16)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1316 : SparsePolynomial.Poly := [([4,7,17], 1)]
theorem eval_atom1316 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1316 = ((g 4) * (g 7) * (g 17)) := by
  norm_num [atom1316, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1316_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (73783142361600 : Int) atom1316) := by
  rw [SparsePolynomial.eval_scale, eval_atom1316]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg17 : 0 ≤ g 17 := hg 17
  have ht : 0 ≤ ((g 4) * (g 7) * (g 17)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1317 : SparsePolynomial.Poly := [([4,7,18], 1)]
theorem eval_atom1317 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1317 = ((g 4) * (g 7) * (g 18)) := by
  norm_num [atom1317, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1317_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (110928036172800 : Int) atom1317) := by
  rw [SparsePolynomial.eval_scale, eval_atom1317]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg18 : 0 ≤ g 18 := hg 18
  have ht : 0 ≤ ((g 4) * (g 7) * (g 18)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1318 : SparsePolynomial.Poly := [([4,7,19], 1)]
theorem eval_atom1318 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1318 = ((g 4) * (g 7) * (g 19)) := by
  norm_num [atom1318, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1318_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (124508744001600 : Int) atom1318) := by
  rw [SparsePolynomial.eval_scale, eval_atom1318]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg19 : 0 ≤ g 19 := hg 19
  have ht : 0 ≤ ((g 4) * (g 7) * (g 19)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1319 : SparsePolynomial.Poly := [([4,7,20], 1)]
theorem eval_atom1319 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1319 = ((g 4) * (g 7) * (g 20)) := by
  norm_num [atom1319, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1319_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (156263363928000 : Int) atom1319) := by
  rw [SparsePolynomial.eval_scale, eval_atom1319]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg20 : 0 ≤ g 20 := hg 20
  have ht : 0 ≤ ((g 4) * (g 7) * (g 20)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1320 : SparsePolynomial.Poly := [([4,7,21], 1)]
theorem eval_atom1320 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1320 = ((g 4) * (g 7) * (g 21)) := by
  norm_num [atom1320, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1320_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (213585260280000 : Int) atom1320) := by
  rw [SparsePolynomial.eval_scale, eval_atom1320]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg21 : 0 ≤ g 21 := hg 21
  have ht : 0 ≤ ((g 4) * (g 7) * (g 21)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1321 : SparsePolynomial.Poly := [([4,7,22], 1)]
theorem eval_atom1321 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1321 = ((g 4) * (g 7) * (g 22)) := by
  norm_num [atom1321, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1321_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (270907156632000 : Int) atom1321) := by
  rw [SparsePolynomial.eval_scale, eval_atom1321]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg22 : 0 ≤ g 22 := hg 22
  have ht : 0 ≤ ((g 4) * (g 7) * (g 22)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1322 : SparsePolynomial.Poly := [([4,7,23], 1)]
theorem eval_atom1322 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1322 = ((g 4) * (g 7) * (g 23)) := by
  norm_num [atom1322, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1322_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (328229052984000 : Int) atom1322) := by
  rw [SparsePolynomial.eval_scale, eval_atom1322]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg23 : 0 ≤ g 23 := hg 23
  have ht : 0 ≤ ((g 4) * (g 7) * (g 23)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1323 : SparsePolynomial.Poly := [([4,8,8], 1)]
theorem eval_atom1323 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1323 = ((g 4) * (g 8) * (g 8)) := by
  norm_num [atom1323, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1323_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (45437639385600 : Int) atom1323) := by
  rw [SparsePolynomial.eval_scale, eval_atom1323]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1324 : SparsePolynomial.Poly := [([4,8,9], 1)]
theorem eval_atom1324 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1324 = ((g 4) * (g 8) * (g 9)) := by
  norm_num [atom1324, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1324_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (80170645487328 : Int) atom1324) := by
  rw [SparsePolynomial.eval_scale, eval_atom1324]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1325 : SparsePolynomial.Poly := [([4,8,10], 1)]
theorem eval_atom1325 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1325 = ((g 4) * (g 8) * (g 10)) := by
  norm_num [atom1325, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1325_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (71128035587664 : Int) atom1325) := by
  rw [SparsePolynomial.eval_scale, eval_atom1325]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1326 : SparsePolynomial.Poly := [([4,8,11], 1)]
theorem eval_atom1326 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1326 = ((g 4) * (g 8) * (g 11)) := by
  norm_num [atom1326, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1326_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (88712586556704 : Int) atom1326) := by
  rw [SparsePolynomial.eval_scale, eval_atom1326]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1327 : SparsePolynomial.Poly := [([4,8,12], 1)]
theorem eval_atom1327 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1327 = ((g 4) * (g 8) * (g 12)) := by
  norm_num [atom1327, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1327_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (114550858597824 : Int) atom1327) := by
  rw [SparsePolynomial.eval_scale, eval_atom1327]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 4) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom1328 : SparsePolynomial.Poly := [([4,8,13], 1)]
theorem eval_atom1328 (g : Fin 24 → ℝ) : SparsePolynomial.eval (variables g) atom1328 = ((g 4) * (g 8) * (g 13)) := by
  norm_num [atom1328, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom1328_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (106889058460800 : Int) atom1328) := by
  rw [SparsePolynomial.eval_scale, eval_atom1328]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 4) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block018 : SparsePolynomial.Poly := [([3,20,21], 519056458905600), ([3,20,22], 358976744985600), ([3,20,23], 415551344947200), ([3,21,21], 149899559040000), ([3,21,22], 193568557593600), ([3,21,23], 256657812364800), ([3,22,23], 65611984132800), ([3,23,23], 81519845299200), ([4,4,4], 19145134310400), ([4,4,5], 33284636169696), ([4,4,6], 12426232089600), ([4,4,7], 7216956633600), ([4,4,8], 2007681177600), ([4,4,9], 2810186767728), ([4,4,10], 15244408345968), ([4,4,11], 26040202684704), ([4,4,12], 48752909452224), ([4,4,13], 34882503465600), ([4,4,14], 17337834662400), ([4,4,15], 14580172454400), ([4,4,18], 18173912097600), ([4,5,5], 37193995228896), ([4,5,6], 29044448275392), ([4,5,7], 2242076371392), ([4,5,9], 3077576911728), ([4,5,10], 12869199875664), ([4,5,11], 29390633404704), ([4,5,12], 79919010651744), ([4,5,13], 57281162390496), ([4,5,14], 27294788496096), ([4,5,15], 27620166864096), ([4,5,16], 16123034985696), ([4,5,17], 19206075561696), ([4,5,18], 49319508264048), ([4,5,19], 36196508174400), ([4,5,20], 47956822204752), ([4,5,21], 74969085851928), ([4,5,22], 101981349499104), ([4,5,23], 130089392506692), ([4,6,6], 25323457420800), ([4,6,7], 22823950195200), ([4,6,8], 850493952000), ([4,6,9], 4523416630128), ([4,6,10], 24745725232272), ([4,6,11], 34961368790304), ([4,6,12], 60757116133824), ([4,6,13], 52032198556800), ([4,6,14], 39633018163200), ([4,6,15], 42020844364800), ([4,6,16], 32586160320000), ([4,6,17], 37731648729600), ([4,6,18], 71505279014400), ([4,6,19], 79385314881600), ([4,6,20], 105439262846400), ([4,6,21], 152401670366400), ([4,6,22], 199364077886400), ([4,6,23], 246326485406400), ([4,7,7], 28330898534400), ([4,7,8], 41917539417600), ([4,7,9], 30177621698928), ([4,7,10], 49379337558672), ([4,7,11], 62699284041504), ([4,7,12], 91599334309824), ([4,7,13], 83916271824000), ([4,7,14], 72558946521600), ([4,7,15], 75988627814400), ([4,7,16], 67595798860800), ([4,7,17], 73783142361600), ([4,7,18], 110928036172800), ([4,7,19], 124508744001600), ([4,7,20], 156263363928000), ([4,7,21], 213585260280000), ([4,7,22], 270907156632000), ([4,7,23], 328229052984000), ([4,8,8], 45437639385600), ([4,8,9], 80170645487328), ([4,8,10], 71128035587664), ([4,8,11], 88712586556704), ([4,8,12], 114550858597824), ([4,8,13], 106889058460800)]
theorem block018_data : block018 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (519056458905600 : Int) atom1249) (SparsePolynomial.scale (358976744985600 : Int) atom1250)) (SparsePolynomial.merge (SparsePolynomial.scale (415551344947200 : Int) atom1251) (SparsePolynomial.merge (SparsePolynomial.scale (149899559040000 : Int) atom1252) (SparsePolynomial.scale (193568557593600 : Int) atom1253)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (256657812364800 : Int) atom1254) (SparsePolynomial.scale (65611984132800 : Int) atom1255)) (SparsePolynomial.merge (SparsePolynomial.scale (81519845299200 : Int) atom1256) (SparsePolynomial.merge (SparsePolynomial.scale (19145134310400 : Int) atom1257) (SparsePolynomial.scale (33284636169696 : Int) atom1258))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (12426232089600 : Int) atom1259) (SparsePolynomial.scale (7216956633600 : Int) atom1260)) (SparsePolynomial.merge (SparsePolynomial.scale (2007681177600 : Int) atom1261) (SparsePolynomial.merge (SparsePolynomial.scale (2810186767728 : Int) atom1262) (SparsePolynomial.scale (15244408345968 : Int) atom1263)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (26040202684704 : Int) atom1264) (SparsePolynomial.scale (48752909452224 : Int) atom1265)) (SparsePolynomial.merge (SparsePolynomial.scale (34882503465600 : Int) atom1266) (SparsePolynomial.merge (SparsePolynomial.scale (17337834662400 : Int) atom1267) (SparsePolynomial.scale (14580172454400 : Int) atom1268)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (18173912097600 : Int) atom1269) (SparsePolynomial.scale (37193995228896 : Int) atom1270)) (SparsePolynomial.merge (SparsePolynomial.scale (29044448275392 : Int) atom1271) (SparsePolynomial.merge (SparsePolynomial.scale (2242076371392 : Int) atom1272) (SparsePolynomial.scale (3077576911728 : Int) atom1273)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (12869199875664 : Int) atom1274) (SparsePolynomial.scale (29390633404704 : Int) atom1275)) (SparsePolynomial.merge (SparsePolynomial.scale (79919010651744 : Int) atom1276) (SparsePolynomial.merge (SparsePolynomial.scale (57281162390496 : Int) atom1277) (SparsePolynomial.scale (27294788496096 : Int) atom1278))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (27620166864096 : Int) atom1279) (SparsePolynomial.scale (16123034985696 : Int) atom1280)) (SparsePolynomial.merge (SparsePolynomial.scale (19206075561696 : Int) atom1281) (SparsePolynomial.merge (SparsePolynomial.scale (49319508264048 : Int) atom1282) (SparsePolynomial.scale (36196508174400 : Int) atom1283)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (47956822204752 : Int) atom1284) (SparsePolynomial.scale (74969085851928 : Int) atom1285)) (SparsePolynomial.merge (SparsePolynomial.scale (101981349499104 : Int) atom1286) (SparsePolynomial.merge (SparsePolynomial.scale (130089392506692 : Int) atom1287) (SparsePolynomial.scale (25323457420800 : Int) atom1288))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (22823950195200 : Int) atom1289) (SparsePolynomial.scale (850493952000 : Int) atom1290)) (SparsePolynomial.merge (SparsePolynomial.scale (4523416630128 : Int) atom1291) (SparsePolynomial.merge (SparsePolynomial.scale (24745725232272 : Int) atom1292) (SparsePolynomial.scale (34961368790304 : Int) atom1293)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (60757116133824 : Int) atom1294) (SparsePolynomial.scale (52032198556800 : Int) atom1295)) (SparsePolynomial.merge (SparsePolynomial.scale (39633018163200 : Int) atom1296) (SparsePolynomial.merge (SparsePolynomial.scale (42020844364800 : Int) atom1297) (SparsePolynomial.scale (32586160320000 : Int) atom1298))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (37731648729600 : Int) atom1299) (SparsePolynomial.scale (71505279014400 : Int) atom1300)) (SparsePolynomial.merge (SparsePolynomial.scale (79385314881600 : Int) atom1301) (SparsePolynomial.merge (SparsePolynomial.scale (105439262846400 : Int) atom1302) (SparsePolynomial.scale (152401670366400 : Int) atom1303)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (199364077886400 : Int) atom1304) (SparsePolynomial.scale (246326485406400 : Int) atom1305)) (SparsePolynomial.merge (SparsePolynomial.scale (28330898534400 : Int) atom1306) (SparsePolynomial.merge (SparsePolynomial.scale (41917539417600 : Int) atom1307) (SparsePolynomial.scale (30177621698928 : Int) atom1308)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (49379337558672 : Int) atom1309) (SparsePolynomial.scale (62699284041504 : Int) atom1310)) (SparsePolynomial.merge (SparsePolynomial.scale (91599334309824 : Int) atom1311) (SparsePolynomial.merge (SparsePolynomial.scale (83916271824000 : Int) atom1312) (SparsePolynomial.scale (72558946521600 : Int) atom1313)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (75988627814400 : Int) atom1314) (SparsePolynomial.scale (67595798860800 : Int) atom1315)) (SparsePolynomial.merge (SparsePolynomial.scale (73783142361600 : Int) atom1316) (SparsePolynomial.merge (SparsePolynomial.scale (110928036172800 : Int) atom1317) (SparsePolynomial.scale (124508744001600 : Int) atom1318))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (156263363928000 : Int) atom1319) (SparsePolynomial.scale (213585260280000 : Int) atom1320)) (SparsePolynomial.merge (SparsePolynomial.scale (270907156632000 : Int) atom1321) (SparsePolynomial.merge (SparsePolynomial.scale (328229052984000 : Int) atom1322) (SparsePolynomial.scale (45437639385600 : Int) atom1323)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (80170645487328 : Int) atom1324) (SparsePolynomial.scale (71128035587664 : Int) atom1325)) (SparsePolynomial.merge (SparsePolynomial.scale (88712586556704 : Int) atom1326) (SparsePolynomial.merge (SparsePolynomial.scale (114550858597824 : Int) atom1327) (SparsePolynomial.scale (106889058460800 : Int) atom1328)))))))) := by decide +kernel
theorem block018_nonneg (g : Fin 24 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block018 := by
  rw [block018_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1249_nonneg g hg hA hB) (atom1250_nonneg g hg hA hB)) (add_nonneg (atom1251_nonneg g hg hA hB) (add_nonneg (atom1252_nonneg g hg hA hB) (atom1253_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1254_nonneg g hg hA hB) (atom1255_nonneg g hg hA hB)) (add_nonneg (atom1256_nonneg g hg hA hB) (add_nonneg (atom1257_nonneg g hg hA hB) (atom1258_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1259_nonneg g hg hA hB) (atom1260_nonneg g hg hA hB)) (add_nonneg (atom1261_nonneg g hg hA hB) (add_nonneg (atom1262_nonneg g hg hA hB) (atom1263_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1264_nonneg g hg hA hB) (atom1265_nonneg g hg hA hB)) (add_nonneg (atom1266_nonneg g hg hA hB) (add_nonneg (atom1267_nonneg g hg hA hB) (atom1268_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1269_nonneg g hg hA hB) (atom1270_nonneg g hg hA hB)) (add_nonneg (atom1271_nonneg g hg hA hB) (add_nonneg (atom1272_nonneg g hg hA hB) (atom1273_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1274_nonneg g hg hA hB) (atom1275_nonneg g hg hA hB)) (add_nonneg (atom1276_nonneg g hg hA hB) (add_nonneg (atom1277_nonneg g hg hA hB) (atom1278_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1279_nonneg g hg hA hB) (atom1280_nonneg g hg hA hB)) (add_nonneg (atom1281_nonneg g hg hA hB) (add_nonneg (atom1282_nonneg g hg hA hB) (atom1283_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1284_nonneg g hg hA hB) (atom1285_nonneg g hg hA hB)) (add_nonneg (atom1286_nonneg g hg hA hB) (add_nonneg (atom1287_nonneg g hg hA hB) (atom1288_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1289_nonneg g hg hA hB) (atom1290_nonneg g hg hA hB)) (add_nonneg (atom1291_nonneg g hg hA hB) (add_nonneg (atom1292_nonneg g hg hA hB) (atom1293_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1294_nonneg g hg hA hB) (atom1295_nonneg g hg hA hB)) (add_nonneg (atom1296_nonneg g hg hA hB) (add_nonneg (atom1297_nonneg g hg hA hB) (atom1298_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1299_nonneg g hg hA hB) (atom1300_nonneg g hg hA hB)) (add_nonneg (atom1301_nonneg g hg hA hB) (add_nonneg (atom1302_nonneg g hg hA hB) (atom1303_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1304_nonneg g hg hA hB) (atom1305_nonneg g hg hA hB)) (add_nonneg (atom1306_nonneg g hg hA hB) (add_nonneg (atom1307_nonneg g hg hA hB) (atom1308_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom1309_nonneg g hg hA hB) (atom1310_nonneg g hg hA hB)) (add_nonneg (atom1311_nonneg g hg hA hB) (add_nonneg (atom1312_nonneg g hg hA hB) (atom1313_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1314_nonneg g hg hA hB) (atom1315_nonneg g hg hA hB)) (add_nonneg (atom1316_nonneg g hg hA hB) (add_nonneg (atom1317_nonneg g hg hA hB) (atom1318_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom1319_nonneg g hg hA hB) (atom1320_nonneg g hg hA hB)) (add_nonneg (atom1321_nonneg g hg hA hB) (add_nonneg (atom1322_nonneg g hg hA hB) (atom1323_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom1324_nonneg g hg hA hB) (atom1325_nonneg g hg hA hB)) (add_nonneg (atom1326_nonneg g hg hA hB) (add_nonneg (atom1327_nonneg g hg hA hB) (atom1328_nonneg g hg hA hB))))))))

end APPT.Finite24
