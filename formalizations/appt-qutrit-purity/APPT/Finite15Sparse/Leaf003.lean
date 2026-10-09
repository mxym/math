import APPT.Finite15Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite15
open SparsePolynomial

def atom0233 : SparsePolynomial.Poly := [([1,6,9], 1)]
theorem eval_atom0233 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0233 = ((g 1) * (g 6) * (g 9)) := by
  norm_num [atom0233, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0233_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (90512640 : Int) atom0233) := by
  rw [SparsePolynomial.eval_scale, eval_atom0233]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0234 : SparsePolynomial.Poly := [([1,6,10], 1)]
theorem eval_atom0234 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0234 = ((g 1) * (g 6) * (g 10)) := by
  norm_num [atom0234, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0234_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (68604840 : Int) atom0234) := by
  rw [SparsePolynomial.eval_scale, eval_atom0234]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0235 : SparsePolynomial.Poly := [([1,6,11], 1)]
theorem eval_atom0235 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0235 = ((g 1) * (g 6) * (g 11)) := by
  norm_num [atom0235, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0235_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (82191240 : Int) atom0235) := by
  rw [SparsePolynomial.eval_scale, eval_atom0235]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0236 : SparsePolynomial.Poly := [([1,6,12], 1)]
theorem eval_atom0236 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0236 = ((g 1) * (g 6) * (g 12)) := by
  norm_num [atom0236, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0236_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (91916280 : Int) atom0236) := by
  rw [SparsePolynomial.eval_scale, eval_atom0236]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 6) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0237 : SparsePolynomial.Poly := [([1,6,13], 1)]
theorem eval_atom0237 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0237 = ((g 1) * (g 6) * (g 13)) := by
  norm_num [atom0237, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0237_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (98458200 : Int) atom0237) := by
  rw [SparsePolynomial.eval_scale, eval_atom0237]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 6) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0238 : SparsePolynomial.Poly := [([1,6,14], 1)]
theorem eval_atom0238 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0238 = ((g 1) * (g 6) * (g 14)) := by
  norm_num [atom0238, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0238_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (105000120 : Int) atom0238) := by
  rw [SparsePolynomial.eval_scale, eval_atom0238]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg6 : 0 ≤ g 6 := hg 6
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 6) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0239 : SparsePolynomial.Poly := [([1,7,7], 1)]
theorem eval_atom0239 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0239 = ((g 1) * (g 7) * (g 7)) := by
  norm_num [atom0239, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0239_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (34030080 : Int) atom0239) := by
  rw [SparsePolynomial.eval_scale, eval_atom0239]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 1) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0240 : SparsePolynomial.Poly := [([1,7,8], 1)]
theorem eval_atom0240 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0240 = ((g 1) * (g 7) * (g 8)) := by
  norm_num [atom0240, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0240_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (61189760 : Int) atom0240) := by
  rw [SparsePolynomial.eval_scale, eval_atom0240]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0241 : SparsePolynomial.Poly := [([1,7,9], 1)]
theorem eval_atom0241 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0241 = ((g 1) * (g 7) * (g 9)) := by
  norm_num [atom0241, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0241_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (95363520 : Int) atom0241) := by
  rw [SparsePolynomial.eval_scale, eval_atom0241]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0242 : SparsePolynomial.Poly := [([1,7,10], 1)]
theorem eval_atom0242 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0242 = ((g 1) * (g 7) * (g 10)) := by
  norm_num [atom0242, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0242_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (75650880 : Int) atom0242) := by
  rw [SparsePolynomial.eval_scale, eval_atom0242]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0243 : SparsePolynomial.Poly := [([1,7,11], 1)]
theorem eval_atom0243 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0243 = ((g 1) * (g 7) * (g 11)) := by
  norm_num [atom0243, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0243_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (90831240 : Int) atom0243) := by
  rw [SparsePolynomial.eval_scale, eval_atom0243]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0244 : SparsePolynomial.Poly := [([1,7,12], 1)]
theorem eval_atom0244 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0244 = ((g 1) * (g 7) * (g 12)) := by
  norm_num [atom0244, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0244_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (98742720 : Int) atom0244) := by
  rw [SparsePolynomial.eval_scale, eval_atom0244]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 7) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0245 : SparsePolynomial.Poly := [([1,7,13], 1)]
theorem eval_atom0245 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0245 = ((g 1) * (g 7) * (g 13)) := by
  norm_num [atom0245, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0245_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (105417600 : Int) atom0245) := by
  rw [SparsePolynomial.eval_scale, eval_atom0245]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 7) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0246 : SparsePolynomial.Poly := [([1,7,14], 1)]
theorem eval_atom0246 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0246 = ((g 1) * (g 7) * (g 14)) := by
  norm_num [atom0246, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0246_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (112092480 : Int) atom0246) := by
  rw [SparsePolynomial.eval_scale, eval_atom0246]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg7 : 0 ≤ g 7 := hg 7
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 7) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0247 : SparsePolynomial.Poly := [([1,8,8], 1)]
theorem eval_atom0247 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0247 = ((g 1) * (g 8) * (g 8)) := by
  norm_num [atom0247, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0247_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (42281280 : Int) atom0247) := by
  rw [SparsePolynomial.eval_scale, eval_atom0247]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 1) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0248 : SparsePolynomial.Poly := [([1,8,9], 1)]
theorem eval_atom0248 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0248 = ((g 1) * (g 8) * (g 9)) := by
  norm_num [atom0248, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0248_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (105534000 : Int) atom0248) := by
  rw [SparsePolynomial.eval_scale, eval_atom0248]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0249 : SparsePolynomial.Poly := [([1,8,10], 1)]
theorem eval_atom0249 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0249 = ((g 1) * (g 8) * (g 10)) := by
  norm_num [atom0249, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0249_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (83431440 : Int) atom0249) := by
  rw [SparsePolynomial.eval_scale, eval_atom0249]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0250 : SparsePolynomial.Poly := [([1,8,11], 1)]
theorem eval_atom0250 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0250 = ((g 1) * (g 8) * (g 11)) := by
  norm_num [atom0250, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0250_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (98601480 : Int) atom0250) := by
  rw [SparsePolynomial.eval_scale, eval_atom0250]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0251 : SparsePolynomial.Poly := [([1,8,12], 1)]
theorem eval_atom0251 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0251 = ((g 1) * (g 8) * (g 12)) := by
  norm_num [atom0251, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0251_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (105713280 : Int) atom0251) := by
  rw [SparsePolynomial.eval_scale, eval_atom0251]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 8) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0252 : SparsePolynomial.Poly := [([1,8,13], 1)]
theorem eval_atom0252 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0252 = ((g 1) * (g 8) * (g 13)) := by
  norm_num [atom0252, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0252_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (105421680 : Int) atom0252) := by
  rw [SparsePolynomial.eval_scale, eval_atom0252]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 8) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0253 : SparsePolynomial.Poly := [([1,8,14], 1)]
theorem eval_atom0253 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0253 = ((g 1) * (g 8) * (g 14)) := by
  norm_num [atom0253, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0253_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (123972480 : Int) atom0253) := by
  rw [SparsePolynomial.eval_scale, eval_atom0253]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg8 : 0 ≤ g 8 := hg 8
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 8) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0254 : SparsePolynomial.Poly := [([1,9,9], 1)]
theorem eval_atom0254 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0254 = ((g 1) * (g 9) * (g 9)) := by
  norm_num [atom0254, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0254_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (78278400 : Int) atom0254) := by
  rw [SparsePolynomial.eval_scale, eval_atom0254]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 1) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0255 : SparsePolynomial.Poly := [([1,9,10], 1)]
theorem eval_atom0255 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0255 = ((g 1) * (g 9) * (g 10)) := by
  norm_num [atom0255, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0255_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (124610400 : Int) atom0255) := by
  rw [SparsePolynomial.eval_scale, eval_atom0255]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0256 : SparsePolynomial.Poly := [([1,9,11], 1)]
theorem eval_atom0256 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0256 = ((g 1) * (g 9) * (g 11)) := by
  norm_num [atom0256, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0256_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (162543240 : Int) atom0256) := by
  rw [SparsePolynomial.eval_scale, eval_atom0256]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0257 : SparsePolynomial.Poly := [([1,9,12], 1)]
theorem eval_atom0257 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0257 = ((g 1) * (g 9) * (g 12)) := by
  norm_num [atom0257, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0257_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (171695520 : Int) atom0257) := by
  rw [SparsePolynomial.eval_scale, eval_atom0257]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 9) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0258 : SparsePolynomial.Poly := [([1,9,13], 1)]
theorem eval_atom0258 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0258 = ((g 1) * (g 9) * (g 13)) := by
  norm_num [atom0258, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0258_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (110190240 : Int) atom0258) := by
  rw [SparsePolynomial.eval_scale, eval_atom0258]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 9) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0259 : SparsePolynomial.Poly := [([1,9,14], 1)]
theorem eval_atom0259 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0259 = ((g 1) * (g 9) * (g 14)) := by
  norm_num [atom0259, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0259_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (132083640 : Int) atom0259) := by
  rw [SparsePolynomial.eval_scale, eval_atom0259]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg9 : 0 ≤ g 9 := hg 9
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 9) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0260 : SparsePolynomial.Poly := [([1,10,10], 1)]
theorem eval_atom0260 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0260 = ((g 1) * (g 10) * (g 10)) := by
  norm_num [atom0260, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0260_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (50720688 : Int) atom0260) := by
  rw [SparsePolynomial.eval_scale, eval_atom0260]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 1) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0261 : SparsePolynomial.Poly := [([1,10,11], 1)]
theorem eval_atom0261 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0261 = ((g 1) * (g 10) * (g 11)) := by
  norm_num [atom0261, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0261_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (119681280 : Int) atom0261) := by
  rw [SparsePolynomial.eval_scale, eval_atom0261]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0262 : SparsePolynomial.Poly := [([1,10,12], 1)]
theorem eval_atom0262 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0262 = ((g 1) * (g 10) * (g 12)) := by
  norm_num [atom0262, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0262_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (148644360 : Int) atom0262) := by
  rw [SparsePolynomial.eval_scale, eval_atom0262]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 10) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0263 : SparsePolynomial.Poly := [([1,10,13], 1)]
theorem eval_atom0263 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0263 = ((g 1) * (g 10) * (g 13)) := by
  norm_num [atom0263, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0263_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (109284120 : Int) atom0263) := by
  rw [SparsePolynomial.eval_scale, eval_atom0263]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 10) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0264 : SparsePolynomial.Poly := [([1,10,14], 1)]
theorem eval_atom0264 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0264 = ((g 1) * (g 10) * (g 14)) := by
  norm_num [atom0264, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0264_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (121793040 : Int) atom0264) := by
  rw [SparsePolynomial.eval_scale, eval_atom0264]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg10 : 0 ≤ g 10 := hg 10
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 10) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0265 : SparsePolynomial.Poly := [([1,11,11], 1)]
theorem eval_atom0265 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0265 = ((g 1) * (g 11) * (g 11)) := by
  norm_num [atom0265, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0265_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (86289840 : Int) atom0265) := by
  rw [SparsePolynomial.eval_scale, eval_atom0265]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 1) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0266 : SparsePolynomial.Poly := [([1,11,12], 1)]
theorem eval_atom0266 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0266 = ((g 1) * (g 11) * (g 12)) := by
  norm_num [atom0266, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0266_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (150873120 : Int) atom0266) := by
  rw [SparsePolynomial.eval_scale, eval_atom0266]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 11) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0267 : SparsePolynomial.Poly := [([1,11,13], 1)]
theorem eval_atom0267 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0267 = ((g 1) * (g 11) * (g 13)) := by
  norm_num [atom0267, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0267_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (111926880 : Int) atom0267) := by
  rw [SparsePolynomial.eval_scale, eval_atom0267]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 11) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0268 : SparsePolynomial.Poly := [([1,11,14], 1)]
theorem eval_atom0268 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0268 = ((g 1) * (g 11) * (g 14)) := by
  norm_num [atom0268, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0268_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (129163320 : Int) atom0268) := by
  rw [SparsePolynomial.eval_scale, eval_atom0268]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg11 : 0 ≤ g 11 := hg 11
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 11) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0269 : SparsePolynomial.Poly := [([1,12,12], 1)]
theorem eval_atom0269 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0269 = ((g 1) * (g 12) * (g 12)) := by
  norm_num [atom0269, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0269_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (60586920 : Int) atom0269) := by
  rw [SparsePolynomial.eval_scale, eval_atom0269]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 1) * (g 12) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0270 : SparsePolynomial.Poly := [([1,12,13], 1)]
theorem eval_atom0270 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0270 = ((g 1) * (g 12) * (g 13)) := by
  norm_num [atom0270, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0270_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (82651680 : Int) atom0270) := by
  rw [SparsePolynomial.eval_scale, eval_atom0270]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 12) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0271 : SparsePolynomial.Poly := [([1,12,14], 1)]
theorem eval_atom0271 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0271 = ((g 1) * (g 12) * (g 14)) := by
  norm_num [atom0271, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0271_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (99339120 : Int) atom0271) := by
  rw [SparsePolynomial.eval_scale, eval_atom0271]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg12 : 0 ≤ g 12 := hg 12
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 12) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0272 : SparsePolynomial.Poly := [([1,13,13], 1)]
theorem eval_atom0272 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0272 = ((g 1) * (g 13) * (g 13)) := by
  norm_num [atom0272, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0272_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (15121080 : Int) atom0272) := by
  rw [SparsePolynomial.eval_scale, eval_atom0272]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 1) * (g 13) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0273 : SparsePolynomial.Poly := [([1,13,14], 1)]
theorem eval_atom0273 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0273 = ((g 1) * (g 13) * (g 14)) := by
  norm_num [atom0273, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0273_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38720880 : Int) atom0273) := by
  rw [SparsePolynomial.eval_scale, eval_atom0273]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg13 : 0 ≤ g 13 := hg 13
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 13) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0274 : SparsePolynomial.Poly := [([1,14,14], 1)]
theorem eval_atom0274 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0274 = ((g 1) * (g 14) * (g 14)) := by
  norm_num [atom0274, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0274_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13514040 : Int) atom0274) := by
  rw [SparsePolynomial.eval_scale, eval_atom0274]
  have hg1 : 0 ≤ g 1 := hg 1
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 1) * (g 14) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0275 : SparsePolynomial.Poly := [([2,2,2], 1)]
theorem eval_atom0275 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0275 = ((g 2) * (g 2) * (g 2)) := by
  norm_num [atom0275, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0275_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10108800 : Int) atom0275) := by
  rw [SparsePolynomial.eval_scale, eval_atom0275]
  have hg2 : 0 ≤ g 2 := hg 2
  have ht : 0 ≤ ((g 2) * (g 2) * (g 2)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0276 : SparsePolynomial.Poly := [([2,2,3], 1)]
theorem eval_atom0276 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0276 = ((g 2) * (g 2) * (g 3)) := by
  norm_num [atom0276, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0276_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28200960 : Int) atom0276) := by
  rw [SparsePolynomial.eval_scale, eval_atom0276]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 2) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0277 : SparsePolynomial.Poly := [([2,2,4], 1)]
theorem eval_atom0277 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0277 = ((g 2) * (g 2) * (g 4)) := by
  norm_num [atom0277, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0277_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (26075520 : Int) atom0277) := by
  rw [SparsePolynomial.eval_scale, eval_atom0277]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 2) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0278 : SparsePolynomial.Poly := [([2,2,5], 1)]
theorem eval_atom0278 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0278 = ((g 2) * (g 2) * (g 5)) := by
  norm_num [atom0278, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0278_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23950080 : Int) atom0278) := by
  rw [SparsePolynomial.eval_scale, eval_atom0278]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 2) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0279 : SparsePolynomial.Poly := [([2,2,6], 1)]
theorem eval_atom0279 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0279 = ((g 2) * (g 2) * (g 6)) := by
  norm_num [atom0279, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0279_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21824640 : Int) atom0279) := by
  rw [SparsePolynomial.eval_scale, eval_atom0279]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 2) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0280 : SparsePolynomial.Poly := [([2,2,7], 1)]
theorem eval_atom0280 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0280 = ((g 2) * (g 2) * (g 7)) := by
  norm_num [atom0280, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0280_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (19699200 : Int) atom0280) := by
  rw [SparsePolynomial.eval_scale, eval_atom0280]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 2) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0281 : SparsePolynomial.Poly := [([2,2,8], 1)]
theorem eval_atom0281 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0281 = ((g 2) * (g 2) * (g 8)) := by
  norm_num [atom0281, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0281_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17573760 : Int) atom0281) := by
  rw [SparsePolynomial.eval_scale, eval_atom0281]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 2) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0282 : SparsePolynomial.Poly := [([2,2,9], 1)]
theorem eval_atom0282 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0282 = ((g 2) * (g 2) * (g 9)) := by
  norm_num [atom0282, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0282_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (42664320 : Int) atom0282) := by
  rw [SparsePolynomial.eval_scale, eval_atom0282]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 2) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0283 : SparsePolynomial.Poly := [([2,2,10], 1)]
theorem eval_atom0283 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0283 = ((g 2) * (g 2) * (g 10)) := by
  norm_num [atom0283, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0283_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13322880 : Int) atom0283) := by
  rw [SparsePolynomial.eval_scale, eval_atom0283]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 2) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0284 : SparsePolynomial.Poly := [([2,2,11], 1)]
theorem eval_atom0284 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0284 = ((g 2) * (g 2) * (g 11)) := by
  norm_num [atom0284, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0284_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (23926320 : Int) atom0284) := by
  rw [SparsePolynomial.eval_scale, eval_atom0284]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 2) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0285 : SparsePolynomial.Poly := [([2,2,12], 1)]
theorem eval_atom0285 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0285 = ((g 2) * (g 2) * (g 12)) := by
  norm_num [atom0285, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0285_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (9072000 : Int) atom0285) := by
  rw [SparsePolynomial.eval_scale, eval_atom0285]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 2) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0286 : SparsePolynomial.Poly := [([2,2,14], 1)]
theorem eval_atom0286 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0286 = ((g 2) * (g 2) * (g 14)) := by
  norm_num [atom0286, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0286_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (13262400 : Int) atom0286) := by
  rw [SparsePolynomial.eval_scale, eval_atom0286]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 2) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0287 : SparsePolynomial.Poly := [([2,3,3], 1)]
theorem eval_atom0287 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0287 = ((g 2) * (g 3) * (g 3)) := by
  norm_num [atom0287, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0287_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (21772800 : Int) atom0287) := by
  rw [SparsePolynomial.eval_scale, eval_atom0287]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have ht : 0 ≤ ((g 2) * (g 3) * (g 3)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0288 : SparsePolynomial.Poly := [([2,3,4], 1)]
theorem eval_atom0288 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0288 = ((g 2) * (g 3) * (g 4)) := by
  norm_num [atom0288, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0288_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (40072320 : Int) atom0288) := by
  rw [SparsePolynomial.eval_scale, eval_atom0288]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 3) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0289 : SparsePolynomial.Poly := [([2,3,5], 1)]
theorem eval_atom0289 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0289 = ((g 2) * (g 3) * (g 5)) := by
  norm_num [atom0289, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0289_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39398400 : Int) atom0289) := by
  rw [SparsePolynomial.eval_scale, eval_atom0289]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 3) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0290 : SparsePolynomial.Poly := [([2,3,6], 1)]
theorem eval_atom0290 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0290 = ((g 2) * (g 3) * (g 6)) := by
  norm_num [atom0290, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0290_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38724480 : Int) atom0290) := by
  rw [SparsePolynomial.eval_scale, eval_atom0290]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 3) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0291 : SparsePolynomial.Poly := [([2,3,7], 1)]
theorem eval_atom0291 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0291 = ((g 2) * (g 3) * (g 7)) := by
  norm_num [atom0291, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0291_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38499840 : Int) atom0291) := by
  rw [SparsePolynomial.eval_scale, eval_atom0291]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 3) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0292 : SparsePolynomial.Poly := [([2,3,8], 1)]
theorem eval_atom0292 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0292 = ((g 2) * (g 3) * (g 8)) := by
  norm_num [atom0292, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0292_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38275200 : Int) atom0292) := by
  rw [SparsePolynomial.eval_scale, eval_atom0292]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 3) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0293 : SparsePolynomial.Poly := [([2,3,9], 1)]
theorem eval_atom0293 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0293 = ((g 2) * (g 3) * (g 9)) := by
  norm_num [atom0293, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0293_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (91134720 : Int) atom0293) := by
  rw [SparsePolynomial.eval_scale, eval_atom0293]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 3) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0294 : SparsePolynomial.Poly := [([2,3,10], 1)]
theorem eval_atom0294 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0294 = ((g 2) * (g 3) * (g 10)) := by
  norm_num [atom0294, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0294_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38350800 : Int) atom0294) := by
  rw [SparsePolynomial.eval_scale, eval_atom0294]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 3) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0295 : SparsePolynomial.Poly := [([2,3,11], 1)]
theorem eval_atom0295 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0295 = ((g 2) * (g 3) * (g 11)) := by
  norm_num [atom0295, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0295_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (60812640 : Int) atom0295) := by
  rw [SparsePolynomial.eval_scale, eval_atom0295]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 3) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0296 : SparsePolynomial.Poly := [([2,3,12], 1)]
theorem eval_atom0296 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0296 = ((g 2) * (g 3) * (g 12)) := by
  norm_num [atom0296, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0296_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (38951280 : Int) atom0296) := by
  rw [SparsePolynomial.eval_scale, eval_atom0296]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 3) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0297 : SparsePolynomial.Poly := [([2,3,13], 1)]
theorem eval_atom0297 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0297 = ((g 2) * (g 3) * (g 13)) := by
  norm_num [atom0297, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0297_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (32479920 : Int) atom0297) := by
  rw [SparsePolynomial.eval_scale, eval_atom0297]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 3) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0298 : SparsePolynomial.Poly := [([2,3,14], 1)]
theorem eval_atom0298 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0298 = ((g 2) * (g 3) * (g 14)) := by
  norm_num [atom0298, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0298_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (48342960 : Int) atom0298) := by
  rw [SparsePolynomial.eval_scale, eval_atom0298]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg3 : 0 ≤ g 3 := hg 3
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 3) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0299 : SparsePolynomial.Poly := [([2,4,4], 1)]
theorem eval_atom0299 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0299 = ((g 2) * (g 4) * (g 4)) := by
  norm_num [atom0299, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0299_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27296640 : Int) atom0299) := by
  rw [SparsePolynomial.eval_scale, eval_atom0299]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have ht : 0 ≤ ((g 2) * (g 4) * (g 4)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0300 : SparsePolynomial.Poly := [([2,4,5], 1)]
theorem eval_atom0300 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0300 = ((g 2) * (g 4) * (g 5)) := by
  norm_num [atom0300, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0300_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (46281600 : Int) atom0300) := by
  rw [SparsePolynomial.eval_scale, eval_atom0300]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 4) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0301 : SparsePolynomial.Poly := [([2,4,6], 1)]
theorem eval_atom0301 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0301 = ((g 2) * (g 4) * (g 6)) := by
  norm_num [atom0301, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0301_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (46765440 : Int) atom0301) := by
  rw [SparsePolynomial.eval_scale, eval_atom0301]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 4) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0302 : SparsePolynomial.Poly := [([2,4,7], 1)]
theorem eval_atom0302 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0302 = ((g 2) * (g 4) * (g 7)) := by
  norm_num [atom0302, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0302_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47249280 : Int) atom0302) := by
  rw [SparsePolynomial.eval_scale, eval_atom0302]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 4) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0303 : SparsePolynomial.Poly := [([2,4,8], 1)]
theorem eval_atom0303 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0303 = ((g 2) * (g 4) * (g 8)) := by
  norm_num [atom0303, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0303_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (47733120 : Int) atom0303) := by
  rw [SparsePolynomial.eval_scale, eval_atom0303]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 2) * (g 4) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0304 : SparsePolynomial.Poly := [([2,4,9], 1)]
theorem eval_atom0304 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0304 = ((g 2) * (g 4) * (g 9)) := by
  norm_num [atom0304, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0304_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (96940800 : Int) atom0304) := by
  rw [SparsePolynomial.eval_scale, eval_atom0304]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 2) * (g 4) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0305 : SparsePolynomial.Poly := [([2,4,10], 1)]
theorem eval_atom0305 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0305 = ((g 2) * (g 4) * (g 10)) := by
  norm_num [atom0305, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0305_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (53688240 : Int) atom0305) := by
  rw [SparsePolynomial.eval_scale, eval_atom0305]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 2) * (g 4) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0306 : SparsePolynomial.Poly := [([2,4,11], 1)]
theorem eval_atom0306 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0306 = ((g 2) * (g 4) * (g 11)) := by
  norm_num [atom0306, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0306_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (73772640 : Int) atom0306) := by
  rw [SparsePolynomial.eval_scale, eval_atom0306]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 2) * (g 4) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0307 : SparsePolynomial.Poly := [([2,4,12], 1)]
theorem eval_atom0307 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0307 = ((g 2) * (g 4) * (g 12)) := by
  norm_num [atom0307, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0307_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (64630800 : Int) atom0307) := by
  rw [SparsePolynomial.eval_scale, eval_atom0307]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg12 : 0 ≤ g 12 := hg 12
  have ht : 0 ≤ ((g 2) * (g 4) * (g 12)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0308 : SparsePolynomial.Poly := [([2,4,13], 1)]
theorem eval_atom0308 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0308 = ((g 2) * (g 4) * (g 13)) := by
  norm_num [atom0308, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0308_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (64818000 : Int) atom0308) := by
  rw [SparsePolynomial.eval_scale, eval_atom0308]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg13 : 0 ≤ g 13 := hg 13
  have ht : 0 ≤ ((g 2) * (g 4) * (g 13)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0309 : SparsePolynomial.Poly := [([2,4,14], 1)]
theorem eval_atom0309 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0309 = ((g 2) * (g 4) * (g 14)) := by
  norm_num [atom0309, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0309_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (87339600 : Int) atom0309) := by
  rw [SparsePolynomial.eval_scale, eval_atom0309]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg4 : 0 ≤ g 4 := hg 4
  have hg14 : 0 ≤ g 14 := hg 14
  have ht : 0 ≤ ((g 2) * (g 4) * (g 14)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0310 : SparsePolynomial.Poly := [([2,5,5], 1)]
theorem eval_atom0310 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0310 = ((g 2) * (g 5) * (g 5)) := by
  norm_num [atom0310, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0310_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31582080 : Int) atom0310) := by
  rw [SparsePolynomial.eval_scale, eval_atom0310]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have ht : 0 ≤ ((g 2) * (g 5) * (g 5)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0311 : SparsePolynomial.Poly := [([2,5,6], 1)]
theorem eval_atom0311 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0311 = ((g 2) * (g 5) * (g 6)) := by
  norm_num [atom0311, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0311_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (61263360 : Int) atom0311) := by
  rw [SparsePolynomial.eval_scale, eval_atom0311]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 2) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0312 : SparsePolynomial.Poly := [([2,5,7], 1)]
theorem eval_atom0312 (g : Fin 15 → ℝ) : SparsePolynomial.eval (variables g) atom0312 = ((g 2) * (g 5) * (g 7)) := by
  norm_num [atom0312, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0312_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (61263360 : Int) atom0312) := by
  rw [SparsePolynomial.eval_scale, eval_atom0312]
  have hg2 : 0 ≤ g 2 := hg 2
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 2) * (g 5) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block003 : SparsePolynomial.Poly := [([1,6,9], 90512640), ([1,6,10], 68604840), ([1,6,11], 82191240), ([1,6,12], 91916280), ([1,6,13], 98458200), ([1,6,14], 105000120), ([1,7,7], 34030080), ([1,7,8], 61189760), ([1,7,9], 95363520), ([1,7,10], 75650880), ([1,7,11], 90831240), ([1,7,12], 98742720), ([1,7,13], 105417600), ([1,7,14], 112092480), ([1,8,8], 42281280), ([1,8,9], 105534000), ([1,8,10], 83431440), ([1,8,11], 98601480), ([1,8,12], 105713280), ([1,8,13], 105421680), ([1,8,14], 123972480), ([1,9,9], 78278400), ([1,9,10], 124610400), ([1,9,11], 162543240), ([1,9,12], 171695520), ([1,9,13], 110190240), ([1,9,14], 132083640), ([1,10,10], 50720688), ([1,10,11], 119681280), ([1,10,12], 148644360), ([1,10,13], 109284120), ([1,10,14], 121793040), ([1,11,11], 86289840), ([1,11,12], 150873120), ([1,11,13], 111926880), ([1,11,14], 129163320), ([1,12,12], 60586920), ([1,12,13], 82651680), ([1,12,14], 99339120), ([1,13,13], 15121080), ([1,13,14], 38720880), ([1,14,14], 13514040), ([2,2,2], 10108800), ([2,2,3], 28200960), ([2,2,4], 26075520), ([2,2,5], 23950080), ([2,2,6], 21824640), ([2,2,7], 19699200), ([2,2,8], 17573760), ([2,2,9], 42664320), ([2,2,10], 13322880), ([2,2,11], 23926320), ([2,2,12], 9072000), ([2,2,14], 13262400), ([2,3,3], 21772800), ([2,3,4], 40072320), ([2,3,5], 39398400), ([2,3,6], 38724480), ([2,3,7], 38499840), ([2,3,8], 38275200), ([2,3,9], 91134720), ([2,3,10], 38350800), ([2,3,11], 60812640), ([2,3,12], 38951280), ([2,3,13], 32479920), ([2,3,14], 48342960), ([2,4,4], 27296640), ([2,4,5], 46281600), ([2,4,6], 46765440), ([2,4,7], 47249280), ([2,4,8], 47733120), ([2,4,9], 96940800), ([2,4,10], 53688240), ([2,4,11], 73772640), ([2,4,12], 64630800), ([2,4,13], 64818000), ([2,4,14], 87339600), ([2,5,5], 31582080), ([2,5,6], 61263360), ([2,5,7], 61263360)]
theorem block003_data : block003 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (90512640 : Int) atom0233) (SparsePolynomial.scale (68604840 : Int) atom0234)) (SparsePolynomial.merge (SparsePolynomial.scale (82191240 : Int) atom0235) (SparsePolynomial.merge (SparsePolynomial.scale (91916280 : Int) atom0236) (SparsePolynomial.scale (98458200 : Int) atom0237)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (105000120 : Int) atom0238) (SparsePolynomial.scale (34030080 : Int) atom0239)) (SparsePolynomial.merge (SparsePolynomial.scale (61189760 : Int) atom0240) (SparsePolynomial.merge (SparsePolynomial.scale (95363520 : Int) atom0241) (SparsePolynomial.scale (75650880 : Int) atom0242))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (90831240 : Int) atom0243) (SparsePolynomial.scale (98742720 : Int) atom0244)) (SparsePolynomial.merge (SparsePolynomial.scale (105417600 : Int) atom0245) (SparsePolynomial.merge (SparsePolynomial.scale (112092480 : Int) atom0246) (SparsePolynomial.scale (42281280 : Int) atom0247)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (105534000 : Int) atom0248) (SparsePolynomial.scale (83431440 : Int) atom0249)) (SparsePolynomial.merge (SparsePolynomial.scale (98601480 : Int) atom0250) (SparsePolynomial.merge (SparsePolynomial.scale (105713280 : Int) atom0251) (SparsePolynomial.scale (105421680 : Int) atom0252)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (123972480 : Int) atom0253) (SparsePolynomial.scale (78278400 : Int) atom0254)) (SparsePolynomial.merge (SparsePolynomial.scale (124610400 : Int) atom0255) (SparsePolynomial.merge (SparsePolynomial.scale (162543240 : Int) atom0256) (SparsePolynomial.scale (171695520 : Int) atom0257)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (110190240 : Int) atom0258) (SparsePolynomial.scale (132083640 : Int) atom0259)) (SparsePolynomial.merge (SparsePolynomial.scale (50720688 : Int) atom0260) (SparsePolynomial.merge (SparsePolynomial.scale (119681280 : Int) atom0261) (SparsePolynomial.scale (148644360 : Int) atom0262))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (109284120 : Int) atom0263) (SparsePolynomial.scale (121793040 : Int) atom0264)) (SparsePolynomial.merge (SparsePolynomial.scale (86289840 : Int) atom0265) (SparsePolynomial.merge (SparsePolynomial.scale (150873120 : Int) atom0266) (SparsePolynomial.scale (111926880 : Int) atom0267)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (129163320 : Int) atom0268) (SparsePolynomial.scale (60586920 : Int) atom0269)) (SparsePolynomial.merge (SparsePolynomial.scale (82651680 : Int) atom0270) (SparsePolynomial.merge (SparsePolynomial.scale (99339120 : Int) atom0271) (SparsePolynomial.scale (15121080 : Int) atom0272))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (38720880 : Int) atom0273) (SparsePolynomial.scale (13514040 : Int) atom0274)) (SparsePolynomial.merge (SparsePolynomial.scale (10108800 : Int) atom0275) (SparsePolynomial.merge (SparsePolynomial.scale (28200960 : Int) atom0276) (SparsePolynomial.scale (26075520 : Int) atom0277)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (23950080 : Int) atom0278) (SparsePolynomial.scale (21824640 : Int) atom0279)) (SparsePolynomial.merge (SparsePolynomial.scale (19699200 : Int) atom0280) (SparsePolynomial.merge (SparsePolynomial.scale (17573760 : Int) atom0281) (SparsePolynomial.scale (42664320 : Int) atom0282))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (13322880 : Int) atom0283) (SparsePolynomial.scale (23926320 : Int) atom0284)) (SparsePolynomial.merge (SparsePolynomial.scale (9072000 : Int) atom0285) (SparsePolynomial.merge (SparsePolynomial.scale (13262400 : Int) atom0286) (SparsePolynomial.scale (21772800 : Int) atom0287)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (40072320 : Int) atom0288) (SparsePolynomial.scale (39398400 : Int) atom0289)) (SparsePolynomial.merge (SparsePolynomial.scale (38724480 : Int) atom0290) (SparsePolynomial.merge (SparsePolynomial.scale (38499840 : Int) atom0291) (SparsePolynomial.scale (38275200 : Int) atom0292)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (91134720 : Int) atom0293) (SparsePolynomial.scale (38350800 : Int) atom0294)) (SparsePolynomial.merge (SparsePolynomial.scale (60812640 : Int) atom0295) (SparsePolynomial.merge (SparsePolynomial.scale (38951280 : Int) atom0296) (SparsePolynomial.scale (32479920 : Int) atom0297)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (48342960 : Int) atom0298) (SparsePolynomial.scale (27296640 : Int) atom0299)) (SparsePolynomial.merge (SparsePolynomial.scale (46281600 : Int) atom0300) (SparsePolynomial.merge (SparsePolynomial.scale (46765440 : Int) atom0301) (SparsePolynomial.scale (47249280 : Int) atom0302))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (47733120 : Int) atom0303) (SparsePolynomial.scale (96940800 : Int) atom0304)) (SparsePolynomial.merge (SparsePolynomial.scale (53688240 : Int) atom0305) (SparsePolynomial.merge (SparsePolynomial.scale (73772640 : Int) atom0306) (SparsePolynomial.scale (64630800 : Int) atom0307)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (64818000 : Int) atom0308) (SparsePolynomial.scale (87339600 : Int) atom0309)) (SparsePolynomial.merge (SparsePolynomial.scale (31582080 : Int) atom0310) (SparsePolynomial.merge (SparsePolynomial.scale (61263360 : Int) atom0311) (SparsePolynomial.scale (61263360 : Int) atom0312)))))))) := by decide +kernel
theorem block003_nonneg (g : Fin 15 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block003 := by
  rw [block003_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0233_nonneg g hg hA hB) (atom0234_nonneg g hg hA hB)) (add_nonneg (atom0235_nonneg g hg hA hB) (add_nonneg (atom0236_nonneg g hg hA hB) (atom0237_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0238_nonneg g hg hA hB) (atom0239_nonneg g hg hA hB)) (add_nonneg (atom0240_nonneg g hg hA hB) (add_nonneg (atom0241_nonneg g hg hA hB) (atom0242_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0243_nonneg g hg hA hB) (atom0244_nonneg g hg hA hB)) (add_nonneg (atom0245_nonneg g hg hA hB) (add_nonneg (atom0246_nonneg g hg hA hB) (atom0247_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0248_nonneg g hg hA hB) (atom0249_nonneg g hg hA hB)) (add_nonneg (atom0250_nonneg g hg hA hB) (add_nonneg (atom0251_nonneg g hg hA hB) (atom0252_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0253_nonneg g hg hA hB) (atom0254_nonneg g hg hA hB)) (add_nonneg (atom0255_nonneg g hg hA hB) (add_nonneg (atom0256_nonneg g hg hA hB) (atom0257_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0258_nonneg g hg hA hB) (atom0259_nonneg g hg hA hB)) (add_nonneg (atom0260_nonneg g hg hA hB) (add_nonneg (atom0261_nonneg g hg hA hB) (atom0262_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0263_nonneg g hg hA hB) (atom0264_nonneg g hg hA hB)) (add_nonneg (atom0265_nonneg g hg hA hB) (add_nonneg (atom0266_nonneg g hg hA hB) (atom0267_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0268_nonneg g hg hA hB) (atom0269_nonneg g hg hA hB)) (add_nonneg (atom0270_nonneg g hg hA hB) (add_nonneg (atom0271_nonneg g hg hA hB) (atom0272_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0273_nonneg g hg hA hB) (atom0274_nonneg g hg hA hB)) (add_nonneg (atom0275_nonneg g hg hA hB) (add_nonneg (atom0276_nonneg g hg hA hB) (atom0277_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0278_nonneg g hg hA hB) (atom0279_nonneg g hg hA hB)) (add_nonneg (atom0280_nonneg g hg hA hB) (add_nonneg (atom0281_nonneg g hg hA hB) (atom0282_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0283_nonneg g hg hA hB) (atom0284_nonneg g hg hA hB)) (add_nonneg (atom0285_nonneg g hg hA hB) (add_nonneg (atom0286_nonneg g hg hA hB) (atom0287_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0288_nonneg g hg hA hB) (atom0289_nonneg g hg hA hB)) (add_nonneg (atom0290_nonneg g hg hA hB) (add_nonneg (atom0291_nonneg g hg hA hB) (atom0292_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0293_nonneg g hg hA hB) (atom0294_nonneg g hg hA hB)) (add_nonneg (atom0295_nonneg g hg hA hB) (add_nonneg (atom0296_nonneg g hg hA hB) (atom0297_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0298_nonneg g hg hA hB) (atom0299_nonneg g hg hA hB)) (add_nonneg (atom0300_nonneg g hg hA hB) (add_nonneg (atom0301_nonneg g hg hA hB) (atom0302_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0303_nonneg g hg hA hB) (atom0304_nonneg g hg hA hB)) (add_nonneg (atom0305_nonneg g hg hA hB) (add_nonneg (atom0306_nonneg g hg hA hB) (atom0307_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0308_nonneg g hg hA hB) (atom0309_nonneg g hg hA hB)) (add_nonneg (atom0310_nonneg g hg hA hB) (add_nonneg (atom0311_nonneg g hg hA hB) (atom0312_nonneg g hg hA hB))))))))

end APPT.Finite15
