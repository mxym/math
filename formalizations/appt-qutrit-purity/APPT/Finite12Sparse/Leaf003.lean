import APPT.Finite12Sparse.Data
set_option maxRecDepth 100000
set_option maxHeartbeats 8000000
set_option linter.unusedVariables false
set_option linter.unusedSimpArgs false
open scoped BigOperators
namespace APPT.Finite12
open SparsePolynomial

def atom0240 : SparsePolynomial.Poly := [([4,7,8], 1)]
theorem eval_atom0240 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0240 = ((g 4) * (g 7) * (g 8)) := by
  norm_num [atom0240, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0240_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (121344 : Int) atom0240) := by
  rw [SparsePolynomial.eval_scale, eval_atom0240]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0241 : SparsePolynomial.Poly := [([4,7,9], 1)]
theorem eval_atom0241 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0241 = ((g 4) * (g 7) * (g 9)) := by
  norm_num [atom0241, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0241_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (188448 : Int) atom0241) := by
  rw [SparsePolynomial.eval_scale, eval_atom0241]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0242 : SparsePolynomial.Poly := [([4,7,10], 1)]
theorem eval_atom0242 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0242 = ((g 4) * (g 7) * (g 10)) := by
  norm_num [atom0242, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0242_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (140352 : Int) atom0242) := by
  rw [SparsePolynomial.eval_scale, eval_atom0242]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0243 : SparsePolynomial.Poly := [([4,7,11], 1)]
theorem eval_atom0243 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0243 = ((g 4) * (g 7) * (g 11)) := by
  norm_num [atom0243, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0243_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (207408 : Int) atom0243) := by
  rw [SparsePolynomial.eval_scale, eval_atom0243]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0244 : SparsePolynomial.Poly := [([4,8,8], 1)]
theorem eval_atom0244 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0244 = ((g 4) * (g 8) * (g 8)) := by
  norm_num [atom0244, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0244_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (99072 : Int) atom0244) := by
  rw [SparsePolynomial.eval_scale, eval_atom0244]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 4) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0245 : SparsePolynomial.Poly := [([4,8,9], 1)]
theorem eval_atom0245 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0245 = ((g 4) * (g 8) * (g 9)) := by
  norm_num [atom0245, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0245_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (205824 : Int) atom0245) := by
  rw [SparsePolynomial.eval_scale, eval_atom0245]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0246 : SparsePolynomial.Poly := [([4,8,10], 1)]
theorem eval_atom0246 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0246 = ((g 4) * (g 8) * (g 10)) := by
  norm_num [atom0246, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0246_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (170208 : Int) atom0246) := by
  rw [SparsePolynomial.eval_scale, eval_atom0246]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0247 : SparsePolynomial.Poly := [([4,8,11], 1)]
theorem eval_atom0247 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0247 = ((g 4) * (g 8) * (g 11)) := by
  norm_num [atom0247, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0247_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (269952 : Int) atom0247) := by
  rw [SparsePolynomial.eval_scale, eval_atom0247]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0248 : SparsePolynomial.Poly := [([4,9,9], 1)]
theorem eval_atom0248 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0248 = ((g 4) * (g 9) * (g 9)) := by
  norm_num [atom0248, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0248_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (90432 : Int) atom0248) := by
  rw [SparsePolynomial.eval_scale, eval_atom0248]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 4) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0249 : SparsePolynomial.Poly := [([4,9,10], 1)]
theorem eval_atom0249 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0249 = ((g 4) * (g 9) * (g 10)) := by
  norm_num [atom0249, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0249_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (176016 : Int) atom0249) := by
  rw [SparsePolynomial.eval_scale, eval_atom0249]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0250 : SparsePolynomial.Poly := [([4,9,11], 1)]
theorem eval_atom0250 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0250 = ((g 4) * (g 9) * (g 11)) := by
  norm_num [atom0250, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0250_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (298752 : Int) atom0250) := by
  rw [SparsePolynomial.eval_scale, eval_atom0250]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0251 : SparsePolynomial.Poly := [([4,10,10], 1)]
theorem eval_atom0251 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0251 = ((g 4) * (g 10) * (g 10)) := by
  norm_num [atom0251, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0251_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (60672 : Int) atom0251) := by
  rw [SparsePolynomial.eval_scale, eval_atom0251]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 4) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0252 : SparsePolynomial.Poly := [([4,10,11], 1)]
theorem eval_atom0252 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0252 = ((g 4) * (g 10) * (g 11)) := by
  norm_num [atom0252, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0252_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (262776 : Int) atom0252) := by
  rw [SparsePolynomial.eval_scale, eval_atom0252]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0253 : SparsePolynomial.Poly := [([4,11,11], 1)]
theorem eval_atom0253 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0253 = ((g 4) * (g 11) * (g 11)) := by
  norm_num [atom0253, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0253_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (190080 : Int) atom0253) := by
  rw [SparsePolynomial.eval_scale, eval_atom0253]
  have hg4 : 0 ≤ g 4 := hg 4
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 4) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0254 : SparsePolynomial.Poly := [([5,5,6], 1)]
theorem eval_atom0254 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0254 = ((g 5) * (g 5) * (g 6)) := by
  norm_num [atom0254, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0254_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (2880 : Int) atom0254) := by
  rw [SparsePolynomial.eval_scale, eval_atom0254]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 5) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0255 : SparsePolynomial.Poly := [([5,5,8], 1)]
theorem eval_atom0255 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0255 = ((g 5) * (g 5) * (g 8)) := by
  norm_num [atom0255, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0255_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (3264 : Int) atom0255) := by
  rw [SparsePolynomial.eval_scale, eval_atom0255]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 5) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0256 : SparsePolynomial.Poly := [([5,5,9], 1)]
theorem eval_atom0256 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0256 = ((g 5) * (g 5) * (g 9)) := by
  norm_num [atom0256, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0256_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (8064 : Int) atom0256) := by
  rw [SparsePolynomial.eval_scale, eval_atom0256]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 5) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0257 : SparsePolynomial.Poly := [([5,5,11], 1)]
theorem eval_atom0257 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0257 = ((g 5) * (g 5) * (g 11)) := by
  norm_num [atom0257, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0257_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (27648 : Int) atom0257) := by
  rw [SparsePolynomial.eval_scale, eval_atom0257]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 5) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0258 : SparsePolynomial.Poly := [([5,6,6], 1)]
theorem eval_atom0258 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0258 = ((g 5) * (g 6) * (g 6)) := by
  norm_num [atom0258, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0258_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (20736 : Int) atom0258) := by
  rw [SparsePolynomial.eval_scale, eval_atom0258]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 5) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0259 : SparsePolynomial.Poly := [([5,6,7], 1)]
theorem eval_atom0259 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0259 = ((g 5) * (g 6) * (g 7)) := by
  norm_num [atom0259, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0259_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (39168 : Int) atom0259) := by
  rw [SparsePolynomial.eval_scale, eval_atom0259]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0260 : SparsePolynomial.Poly := [([5,6,8], 1)]
theorem eval_atom0260 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0260 = ((g 5) * (g 6) * (g 8)) := by
  norm_num [atom0260, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0260_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (118272 : Int) atom0260) := by
  rw [SparsePolynomial.eval_scale, eval_atom0260]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0261 : SparsePolynomial.Poly := [([5,6,9], 1)]
theorem eval_atom0261 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0261 = ((g 5) * (g 6) * (g 9)) := by
  norm_num [atom0261, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0261_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (158976 : Int) atom0261) := by
  rw [SparsePolynomial.eval_scale, eval_atom0261]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0262 : SparsePolynomial.Poly := [([5,6,10], 1)]
theorem eval_atom0262 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0262 = ((g 5) * (g 6) * (g 10)) := by
  norm_num [atom0262, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0262_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (81504 : Int) atom0262) := by
  rw [SparsePolynomial.eval_scale, eval_atom0262]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0263 : SparsePolynomial.Poly := [([5,6,11], 1)]
theorem eval_atom0263 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0263 = ((g 5) * (g 6) * (g 11)) := by
  norm_num [atom0263, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0263_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (211968 : Int) atom0263) := by
  rw [SparsePolynomial.eval_scale, eval_atom0263]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0264 : SparsePolynomial.Poly := [([5,7,7], 1)]
theorem eval_atom0264 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0264 = ((g 5) * (g 7) * (g 7)) := by
  norm_num [atom0264, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0264_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (17280 : Int) atom0264) := by
  rw [SparsePolynomial.eval_scale, eval_atom0264]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 5) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0265 : SparsePolynomial.Poly := [([5,7,8], 1)]
theorem eval_atom0265 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0265 = ((g 5) * (g 7) * (g 8)) := by
  norm_num [atom0265, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0265_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (88704 : Int) atom0265) := by
  rw [SparsePolynomial.eval_scale, eval_atom0265]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0266 : SparsePolynomial.Poly := [([5,7,9], 1)]
theorem eval_atom0266 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0266 = ((g 5) * (g 7) * (g 9)) := by
  norm_num [atom0266, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0266_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (167040 : Int) atom0266) := by
  rw [SparsePolynomial.eval_scale, eval_atom0266]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0267 : SparsePolynomial.Poly := [([5,7,10], 1)]
theorem eval_atom0267 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0267 = ((g 5) * (g 7) * (g 10)) := by
  norm_num [atom0267, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0267_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (130176 : Int) atom0267) := by
  rw [SparsePolynomial.eval_scale, eval_atom0267]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0268 : SparsePolynomial.Poly := [([5,7,11], 1)]
theorem eval_atom0268 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0268 = ((g 5) * (g 7) * (g 11)) := by
  norm_num [atom0268, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0268_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (209664 : Int) atom0268) := by
  rw [SparsePolynomial.eval_scale, eval_atom0268]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0269 : SparsePolynomial.Poly := [([5,8,8], 1)]
theorem eval_atom0269 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0269 = ((g 5) * (g 8) * (g 8)) := by
  norm_num [atom0269, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0269_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (88704 : Int) atom0269) := by
  rw [SparsePolynomial.eval_scale, eval_atom0269]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 5) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0270 : SparsePolynomial.Poly := [([5,8,9], 1)]
theorem eval_atom0270 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0270 = ((g 5) * (g 8) * (g 9)) := by
  norm_num [atom0270, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0270_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (201600 : Int) atom0270) := by
  rw [SparsePolynomial.eval_scale, eval_atom0270]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0271 : SparsePolynomial.Poly := [([5,8,10], 1)]
theorem eval_atom0271 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0271 = ((g 5) * (g 8) * (g 10)) := by
  norm_num [atom0271, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0271_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (189600 : Int) atom0271) := by
  rw [SparsePolynomial.eval_scale, eval_atom0271]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0272 : SparsePolynomial.Poly := [([5,8,11], 1)]
theorem eval_atom0272 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0272 = ((g 5) * (g 8) * (g 11)) := by
  norm_num [atom0272, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0272_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (298752 : Int) atom0272) := by
  rw [SparsePolynomial.eval_scale, eval_atom0272]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0273 : SparsePolynomial.Poly := [([5,9,9], 1)]
theorem eval_atom0273 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0273 = ((g 5) * (g 9) * (g 9)) := by
  norm_num [atom0273, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0273_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (93312 : Int) atom0273) := by
  rw [SparsePolynomial.eval_scale, eval_atom0273]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 5) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0274 : SparsePolynomial.Poly := [([5,9,10], 1)]
theorem eval_atom0274 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0274 = ((g 5) * (g 9) * (g 10)) := by
  norm_num [atom0274, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0274_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (211824 : Int) atom0274) := by
  rw [SparsePolynomial.eval_scale, eval_atom0274]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0275 : SparsePolynomial.Poly := [([5,9,11], 1)]
theorem eval_atom0275 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0275 = ((g 5) * (g 9) * (g 11)) := by
  norm_num [atom0275, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0275_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (343296 : Int) atom0275) := by
  rw [SparsePolynomial.eval_scale, eval_atom0275]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0276 : SparsePolynomial.Poly := [([5,10,10], 1)]
theorem eval_atom0276 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0276 = ((g 5) * (g 10) * (g 10)) := by
  norm_num [atom0276, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0276_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (93888 : Int) atom0276) := by
  rw [SparsePolynomial.eval_scale, eval_atom0276]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 5) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0277 : SparsePolynomial.Poly := [([5,10,11], 1)]
theorem eval_atom0277 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0277 = ((g 5) * (g 10) * (g 11)) := by
  norm_num [atom0277, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0277_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (339048 : Int) atom0277) := by
  rw [SparsePolynomial.eval_scale, eval_atom0277]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0278 : SparsePolynomial.Poly := [([5,11,11], 1)]
theorem eval_atom0278 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0278 = ((g 5) * (g 11) * (g 11)) := by
  norm_num [atom0278, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0278_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (228096 : Int) atom0278) := by
  rw [SparsePolynomial.eval_scale, eval_atom0278]
  have hg5 : 0 ≤ g 5 := hg 5
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 5) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0279 : SparsePolynomial.Poly := [([6,6,6], 1)]
theorem eval_atom0279 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0279 = ((g 6) * (g 6) * (g 6)) := by
  norm_num [atom0279, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0279_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (10176 : Int) atom0279) := by
  rw [SparsePolynomial.eval_scale, eval_atom0279]
  have hg6 : 0 ≤ g 6 := hg 6
  have ht : 0 ≤ ((g 6) * (g 6) * (g 6)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0280 : SparsePolynomial.Poly := [([6,6,7], 1)]
theorem eval_atom0280 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0280 = ((g 6) * (g 6) * (g 7)) := by
  norm_num [atom0280, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0280_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (30144 : Int) atom0280) := by
  rw [SparsePolynomial.eval_scale, eval_atom0280]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 6) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0281 : SparsePolynomial.Poly := [([6,6,8], 1)]
theorem eval_atom0281 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0281 = ((g 6) * (g 6) * (g 8)) := by
  norm_num [atom0281, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0281_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (79680 : Int) atom0281) := by
  rw [SparsePolynomial.eval_scale, eval_atom0281]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 6) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0282 : SparsePolynomial.Poly := [([6,6,9], 1)]
theorem eval_atom0282 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0282 = ((g 6) * (g 6) * (g 9)) := by
  norm_num [atom0282, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0282_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (105408 : Int) atom0282) := by
  rw [SparsePolynomial.eval_scale, eval_atom0282]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 6) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0283 : SparsePolynomial.Poly := [([6,6,10], 1)]
theorem eval_atom0283 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0283 = ((g 6) * (g 6) * (g 10)) := by
  norm_num [atom0283, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0283_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (28992 : Int) atom0283) := by
  rw [SparsePolynomial.eval_scale, eval_atom0283]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 6) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0284 : SparsePolynomial.Poly := [([6,6,11], 1)]
theorem eval_atom0284 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0284 = ((g 6) * (g 6) * (g 11)) := by
  norm_num [atom0284, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0284_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (104640 : Int) atom0284) := by
  rw [SparsePolynomial.eval_scale, eval_atom0284]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 6) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0285 : SparsePolynomial.Poly := [([6,7,7], 1)]
theorem eval_atom0285 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0285 = ((g 6) * (g 7) * (g 7)) := by
  norm_num [atom0285, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0285_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31104 : Int) atom0285) := by
  rw [SparsePolynomial.eval_scale, eval_atom0285]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have ht : 0 ≤ ((g 6) * (g 7) * (g 7)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0286 : SparsePolynomial.Poly := [([6,7,8], 1)]
theorem eval_atom0286 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0286 = ((g 6) * (g 7) * (g 8)) := by
  norm_num [atom0286, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0286_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (146112 : Int) atom0286) := by
  rw [SparsePolynomial.eval_scale, eval_atom0286]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0287 : SparsePolynomial.Poly := [([6,7,9], 1)]
theorem eval_atom0287 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0287 = ((g 6) * (g 7) * (g 9)) := by
  norm_num [atom0287, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0287_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (242688 : Int) atom0287) := by
  rw [SparsePolynomial.eval_scale, eval_atom0287]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0288 : SparsePolynomial.Poly := [([6,7,10], 1)]
theorem eval_atom0288 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0288 = ((g 6) * (g 7) * (g 10)) := by
  norm_num [atom0288, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0288_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (148032 : Int) atom0288) := by
  rw [SparsePolynomial.eval_scale, eval_atom0288]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0289 : SparsePolynomial.Poly := [([6,7,11], 1)]
theorem eval_atom0289 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0289 = ((g 6) * (g 7) * (g 11)) := by
  norm_num [atom0289, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0289_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (243456 : Int) atom0289) := by
  rw [SparsePolynomial.eval_scale, eval_atom0289]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0290 : SparsePolynomial.Poly := [([6,8,8], 1)]
theorem eval_atom0290 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0290 = ((g 6) * (g 8) * (g 8)) := by
  norm_num [atom0290, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0290_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (116352 : Int) atom0290) := by
  rw [SparsePolynomial.eval_scale, eval_atom0290]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 6) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0291 : SparsePolynomial.Poly := [([6,8,9], 1)]
theorem eval_atom0291 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0291 = ((g 6) * (g 8) * (g 9)) := by
  norm_num [atom0291, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0291_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (273408 : Int) atom0291) := by
  rw [SparsePolynomial.eval_scale, eval_atom0291]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0292 : SparsePolynomial.Poly := [([6,8,10], 1)]
theorem eval_atom0292 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0292 = ((g 6) * (g 8) * (g 10)) := by
  norm_num [atom0292, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0292_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (211968 : Int) atom0292) := by
  rw [SparsePolynomial.eval_scale, eval_atom0292]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0293 : SparsePolynomial.Poly := [([6,8,11], 1)]
theorem eval_atom0293 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0293 = ((g 6) * (g 8) * (g 11)) := by
  norm_num [atom0293, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0293_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (227712 : Int) atom0293) := by
  rw [SparsePolynomial.eval_scale, eval_atom0293]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0294 : SparsePolynomial.Poly := [([6,9,9], 1)]
theorem eval_atom0294 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0294 = ((g 6) * (g 9) * (g 9)) := by
  norm_num [atom0294, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0294_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (134208 : Int) atom0294) := by
  rw [SparsePolynomial.eval_scale, eval_atom0294]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 6) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0295 : SparsePolynomial.Poly := [([6,9,10], 1)]
theorem eval_atom0295 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0295 = ((g 6) * (g 9) * (g 10)) := by
  norm_num [atom0295, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0295_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (252096 : Int) atom0295) := by
  rw [SparsePolynomial.eval_scale, eval_atom0295]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0296 : SparsePolynomial.Poly := [([6,9,11], 1)]
theorem eval_atom0296 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0296 = ((g 6) * (g 9) * (g 11)) := by
  norm_num [atom0296, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0296_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (235776 : Int) atom0296) := by
  rw [SparsePolynomial.eval_scale, eval_atom0296]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0297 : SparsePolynomial.Poly := [([6,10,10], 1)]
theorem eval_atom0297 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0297 = ((g 6) * (g 10) * (g 10)) := by
  norm_num [atom0297, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0297_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (133056 : Int) atom0297) := by
  rw [SparsePolynomial.eval_scale, eval_atom0297]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 6) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0298 : SparsePolynomial.Poly := [([6,10,11], 1)]
theorem eval_atom0298 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0298 = ((g 6) * (g 10) * (g 11)) := by
  norm_num [atom0298, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0298_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (269952 : Int) atom0298) := by
  rw [SparsePolynomial.eval_scale, eval_atom0298]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0299 : SparsePolynomial.Poly := [([6,11,11], 1)]
theorem eval_atom0299 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0299 = ((g 6) * (g 11) * (g 11)) := by
  norm_num [atom0299, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0299_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (114048 : Int) atom0299) := by
  rw [SparsePolynomial.eval_scale, eval_atom0299]
  have hg6 : 0 ≤ g 6 := hg 6
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 6) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0300 : SparsePolynomial.Poly := [([7,7,8], 1)]
theorem eval_atom0300 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0300 = ((g 7) * (g 7) * (g 8)) := by
  norm_num [atom0300, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0300_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31104 : Int) atom0300) := by
  rw [SparsePolynomial.eval_scale, eval_atom0300]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 7) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0301 : SparsePolynomial.Poly := [([7,7,9], 1)]
theorem eval_atom0301 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0301 = ((g 7) * (g 7) * (g 9)) := by
  norm_num [atom0301, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0301_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (91776 : Int) atom0301) := by
  rw [SparsePolynomial.eval_scale, eval_atom0301]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 7) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0302 : SparsePolynomial.Poly := [([7,7,10], 1)]
theorem eval_atom0302 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0302 = ((g 7) * (g 7) * (g 10)) := by
  norm_num [atom0302, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0302_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (56448 : Int) atom0302) := by
  rw [SparsePolynomial.eval_scale, eval_atom0302]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 7) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0303 : SparsePolynomial.Poly := [([7,7,11], 1)]
theorem eval_atom0303 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0303 = ((g 7) * (g 7) * (g 11)) := by
  norm_num [atom0303, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0303_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (97152 : Int) atom0303) := by
  rw [SparsePolynomial.eval_scale, eval_atom0303]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 7) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0304 : SparsePolynomial.Poly := [([7,8,8], 1)]
theorem eval_atom0304 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0304 = ((g 7) * (g 8) * (g 8)) := by
  norm_num [atom0304, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0304_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (81024 : Int) atom0304) := by
  rw [SparsePolynomial.eval_scale, eval_atom0304]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 7) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0305 : SparsePolynomial.Poly := [([7,8,9], 1)]
theorem eval_atom0305 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0305 = ((g 7) * (g 8) * (g 9)) := by
  norm_num [atom0305, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0305_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (244224 : Int) atom0305) := by
  rw [SparsePolynomial.eval_scale, eval_atom0305]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0306 : SparsePolynomial.Poly := [([7,8,10], 1)]
theorem eval_atom0306 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0306 = ((g 7) * (g 8) * (g 10)) := by
  norm_num [atom0306, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0306_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (224256 : Int) atom0306) := by
  rw [SparsePolynomial.eval_scale, eval_atom0306]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0307 : SparsePolynomial.Poly := [([7,8,11], 1)]
theorem eval_atom0307 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0307 = ((g 7) * (g 8) * (g 11)) := by
  norm_num [atom0307, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0307_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (256512 : Int) atom0307) := by
  rw [SparsePolynomial.eval_scale, eval_atom0307]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0308 : SparsePolynomial.Poly := [([7,9,9], 1)]
theorem eval_atom0308 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0308 = ((g 7) * (g 9) * (g 9)) := by
  norm_num [atom0308, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0308_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (137088 : Int) atom0308) := by
  rw [SparsePolynomial.eval_scale, eval_atom0308]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 7) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0309 : SparsePolynomial.Poly := [([7,9,10], 1)]
theorem eval_atom0309 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0309 = ((g 7) * (g 9) * (g 10)) := by
  norm_num [atom0309, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0309_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (277248 : Int) atom0309) := by
  rw [SparsePolynomial.eval_scale, eval_atom0309]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0310 : SparsePolynomial.Poly := [([7,9,11], 1)]
theorem eval_atom0310 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0310 = ((g 7) * (g 9) * (g 11)) := by
  norm_num [atom0310, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0310_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (280320 : Int) atom0310) := by
  rw [SparsePolynomial.eval_scale, eval_atom0310]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg9 : 0 ≤ g 9 := hg 9
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 9) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0311 : SparsePolynomial.Poly := [([7,10,10], 1)]
theorem eval_atom0311 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0311 = ((g 7) * (g 10) * (g 10)) := by
  norm_num [atom0311, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0311_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (152064 : Int) atom0311) := by
  rw [SparsePolynomial.eval_scale, eval_atom0311]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 7) * (g 10) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0312 : SparsePolynomial.Poly := [([7,10,11], 1)]
theorem eval_atom0312 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0312 = ((g 7) * (g 10) * (g 11)) := by
  norm_num [atom0312, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0312_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (330240 : Int) atom0312) := by
  rw [SparsePolynomial.eval_scale, eval_atom0312]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg10 : 0 ≤ g 10 := hg 10
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 10) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0313 : SparsePolynomial.Poly := [([7,11,11], 1)]
theorem eval_atom0313 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0313 = ((g 7) * (g 11) * (g 11)) := by
  norm_num [atom0313, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0313_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (152064 : Int) atom0313) := by
  rw [SparsePolynomial.eval_scale, eval_atom0313]
  have hg7 : 0 ≤ g 7 := hg 7
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 7) * (g 11) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0314 : SparsePolynomial.Poly := [([8,8,8], 1)]
theorem eval_atom0314 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0314 = ((g 8) * (g 8) * (g 8)) := by
  norm_num [atom0314, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0314_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (31872 : Int) atom0314) := by
  rw [SparsePolynomial.eval_scale, eval_atom0314]
  have hg8 : 0 ≤ g 8 := hg 8
  have ht : 0 ≤ ((g 8) * (g 8) * (g 8)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0315 : SparsePolynomial.Poly := [([8,8,9], 1)]
theorem eval_atom0315 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0315 = ((g 8) * (g 8) * (g 9)) := by
  norm_num [atom0315, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0315_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (120000 : Int) atom0315) := by
  rw [SparsePolynomial.eval_scale, eval_atom0315]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 8) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0316 : SparsePolynomial.Poly := [([8,8,10], 1)]
theorem eval_atom0316 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0316 = ((g 8) * (g 8) * (g 10)) := by
  norm_num [atom0316, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0316_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (118272 : Int) atom0316) := by
  rw [SparsePolynomial.eval_scale, eval_atom0316]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 8) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0317 : SparsePolynomial.Poly := [([8,8,11], 1)]
theorem eval_atom0317 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0317 = ((g 8) * (g 8) * (g 11)) := by
  norm_num [atom0317, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0317_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (92736 : Int) atom0317) := by
  rw [SparsePolynomial.eval_scale, eval_atom0317]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg11 : 0 ≤ g 11 := hg 11
  have ht : 0 ≤ ((g 8) * (g 8) * (g 11)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0318 : SparsePolynomial.Poly := [([8,9,9], 1)]
theorem eval_atom0318 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0318 = ((g 8) * (g 9) * (g 9)) := by
  norm_num [atom0318, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0318_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (139968 : Int) atom0318) := by
  rw [SparsePolynomial.eval_scale, eval_atom0318]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have ht : 0 ≤ ((g 8) * (g 9) * (g 9)) := by positivity
  exact mul_nonneg (by norm_num) ht
def atom0319 : SparsePolynomial.Poly := [([8,9,10], 1)]
theorem eval_atom0319 (g : Fin 12 → ℝ) : SparsePolynomial.eval (variables g) atom0319 = ((g 8) * (g 9) * (g 10)) := by
  norm_num [atom0319, SparsePolynomial.eval, SparsePolynomial.mon, variables]
  <;> ring
theorem atom0319_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) (SparsePolynomial.scale (302400 : Int) atom0319) := by
  rw [SparsePolynomial.eval_scale, eval_atom0319]
  have hg8 : 0 ≤ g 8 := hg 8
  have hg9 : 0 ≤ g 9 := hg 9
  have hg10 : 0 ≤ g 10 := hg 10
  have ht : 0 ≤ ((g 8) * (g 9) * (g 10)) := by positivity
  exact mul_nonneg (by norm_num) ht
def block003 : SparsePolynomial.Poly := [([4,7,8], 121344), ([4,7,9], 188448), ([4,7,10], 140352), ([4,7,11], 207408), ([4,8,8], 99072), ([4,8,9], 205824), ([4,8,10], 170208), ([4,8,11], 269952), ([4,9,9], 90432), ([4,9,10], 176016), ([4,9,11], 298752), ([4,10,10], 60672), ([4,10,11], 262776), ([4,11,11], 190080), ([5,5,6], 2880), ([5,5,8], 3264), ([5,5,9], 8064), ([5,5,11], 27648), ([5,6,6], 20736), ([5,6,7], 39168), ([5,6,8], 118272), ([5,6,9], 158976), ([5,6,10], 81504), ([5,6,11], 211968), ([5,7,7], 17280), ([5,7,8], 88704), ([5,7,9], 167040), ([5,7,10], 130176), ([5,7,11], 209664), ([5,8,8], 88704), ([5,8,9], 201600), ([5,8,10], 189600), ([5,8,11], 298752), ([5,9,9], 93312), ([5,9,10], 211824), ([5,9,11], 343296), ([5,10,10], 93888), ([5,10,11], 339048), ([5,11,11], 228096), ([6,6,6], 10176), ([6,6,7], 30144), ([6,6,8], 79680), ([6,6,9], 105408), ([6,6,10], 28992), ([6,6,11], 104640), ([6,7,7], 31104), ([6,7,8], 146112), ([6,7,9], 242688), ([6,7,10], 148032), ([6,7,11], 243456), ([6,8,8], 116352), ([6,8,9], 273408), ([6,8,10], 211968), ([6,8,11], 227712), ([6,9,9], 134208), ([6,9,10], 252096), ([6,9,11], 235776), ([6,10,10], 133056), ([6,10,11], 269952), ([6,11,11], 114048), ([7,7,8], 31104), ([7,7,9], 91776), ([7,7,10], 56448), ([7,7,11], 97152), ([7,8,8], 81024), ([7,8,9], 244224), ([7,8,10], 224256), ([7,8,11], 256512), ([7,9,9], 137088), ([7,9,10], 277248), ([7,9,11], 280320), ([7,10,10], 152064), ([7,10,11], 330240), ([7,11,11], 152064), ([8,8,8], 31872), ([8,8,9], 120000), ([8,8,10], 118272), ([8,8,11], 92736), ([8,9,9], 139968), ([8,9,10], 302400)]
theorem block003_data : block003 = SparsePolynomial.trim (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (121344 : Int) atom0240) (SparsePolynomial.scale (188448 : Int) atom0241)) (SparsePolynomial.merge (SparsePolynomial.scale (140352 : Int) atom0242) (SparsePolynomial.merge (SparsePolynomial.scale (207408 : Int) atom0243) (SparsePolynomial.scale (99072 : Int) atom0244)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (205824 : Int) atom0245) (SparsePolynomial.scale (170208 : Int) atom0246)) (SparsePolynomial.merge (SparsePolynomial.scale (269952 : Int) atom0247) (SparsePolynomial.merge (SparsePolynomial.scale (90432 : Int) atom0248) (SparsePolynomial.scale (176016 : Int) atom0249))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (298752 : Int) atom0250) (SparsePolynomial.scale (60672 : Int) atom0251)) (SparsePolynomial.merge (SparsePolynomial.scale (262776 : Int) atom0252) (SparsePolynomial.merge (SparsePolynomial.scale (190080 : Int) atom0253) (SparsePolynomial.scale (2880 : Int) atom0254)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (3264 : Int) atom0255) (SparsePolynomial.scale (8064 : Int) atom0256)) (SparsePolynomial.merge (SparsePolynomial.scale (27648 : Int) atom0257) (SparsePolynomial.merge (SparsePolynomial.scale (20736 : Int) atom0258) (SparsePolynomial.scale (39168 : Int) atom0259)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (118272 : Int) atom0260) (SparsePolynomial.scale (158976 : Int) atom0261)) (SparsePolynomial.merge (SparsePolynomial.scale (81504 : Int) atom0262) (SparsePolynomial.merge (SparsePolynomial.scale (211968 : Int) atom0263) (SparsePolynomial.scale (17280 : Int) atom0264)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (88704 : Int) atom0265) (SparsePolynomial.scale (167040 : Int) atom0266)) (SparsePolynomial.merge (SparsePolynomial.scale (130176 : Int) atom0267) (SparsePolynomial.merge (SparsePolynomial.scale (209664 : Int) atom0268) (SparsePolynomial.scale (88704 : Int) atom0269))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (201600 : Int) atom0270) (SparsePolynomial.scale (189600 : Int) atom0271)) (SparsePolynomial.merge (SparsePolynomial.scale (298752 : Int) atom0272) (SparsePolynomial.merge (SparsePolynomial.scale (93312 : Int) atom0273) (SparsePolynomial.scale (211824 : Int) atom0274)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (343296 : Int) atom0275) (SparsePolynomial.scale (93888 : Int) atom0276)) (SparsePolynomial.merge (SparsePolynomial.scale (339048 : Int) atom0277) (SparsePolynomial.merge (SparsePolynomial.scale (228096 : Int) atom0278) (SparsePolynomial.scale (10176 : Int) atom0279))))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (30144 : Int) atom0280) (SparsePolynomial.scale (79680 : Int) atom0281)) (SparsePolynomial.merge (SparsePolynomial.scale (105408 : Int) atom0282) (SparsePolynomial.merge (SparsePolynomial.scale (28992 : Int) atom0283) (SparsePolynomial.scale (104640 : Int) atom0284)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (31104 : Int) atom0285) (SparsePolynomial.scale (146112 : Int) atom0286)) (SparsePolynomial.merge (SparsePolynomial.scale (242688 : Int) atom0287) (SparsePolynomial.merge (SparsePolynomial.scale (148032 : Int) atom0288) (SparsePolynomial.scale (243456 : Int) atom0289))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (116352 : Int) atom0290) (SparsePolynomial.scale (273408 : Int) atom0291)) (SparsePolynomial.merge (SparsePolynomial.scale (211968 : Int) atom0292) (SparsePolynomial.merge (SparsePolynomial.scale (227712 : Int) atom0293) (SparsePolynomial.scale (134208 : Int) atom0294)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (252096 : Int) atom0295) (SparsePolynomial.scale (235776 : Int) atom0296)) (SparsePolynomial.merge (SparsePolynomial.scale (133056 : Int) atom0297) (SparsePolynomial.merge (SparsePolynomial.scale (269952 : Int) atom0298) (SparsePolynomial.scale (114048 : Int) atom0299)))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (31104 : Int) atom0300) (SparsePolynomial.scale (91776 : Int) atom0301)) (SparsePolynomial.merge (SparsePolynomial.scale (56448 : Int) atom0302) (SparsePolynomial.merge (SparsePolynomial.scale (97152 : Int) atom0303) (SparsePolynomial.scale (81024 : Int) atom0304)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (244224 : Int) atom0305) (SparsePolynomial.scale (224256 : Int) atom0306)) (SparsePolynomial.merge (SparsePolynomial.scale (256512 : Int) atom0307) (SparsePolynomial.merge (SparsePolynomial.scale (137088 : Int) atom0308) (SparsePolynomial.scale (277248 : Int) atom0309))))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (280320 : Int) atom0310) (SparsePolynomial.scale (152064 : Int) atom0311)) (SparsePolynomial.merge (SparsePolynomial.scale (330240 : Int) atom0312) (SparsePolynomial.merge (SparsePolynomial.scale (152064 : Int) atom0313) (SparsePolynomial.scale (31872 : Int) atom0314)))) (SparsePolynomial.merge (SparsePolynomial.merge (SparsePolynomial.scale (120000 : Int) atom0315) (SparsePolynomial.scale (118272 : Int) atom0316)) (SparsePolynomial.merge (SparsePolynomial.scale (92736 : Int) atom0317) (SparsePolynomial.merge (SparsePolynomial.scale (139968 : Int) atom0318) (SparsePolynomial.scale (302400 : Int) atom0319)))))))) := by decide +kernel
theorem block003_nonneg (g : Fin 12 → ℝ) (hg : ∀ i, 0 ≤ g i) (hA : (matA (outer g)).PosSemidef) (hB : (matB (outer g)).PosSemidef) : 0 ≤ SparsePolynomial.eval (variables g) block003 := by
  rw [block003_data, SparsePolynomial.eval_trim]
  try simp only [SparsePolynomial.eval_merge]
  exact (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0240_nonneg g hg hA hB) (atom0241_nonneg g hg hA hB)) (add_nonneg (atom0242_nonneg g hg hA hB) (add_nonneg (atom0243_nonneg g hg hA hB) (atom0244_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0245_nonneg g hg hA hB) (atom0246_nonneg g hg hA hB)) (add_nonneg (atom0247_nonneg g hg hA hB) (add_nonneg (atom0248_nonneg g hg hA hB) (atom0249_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0250_nonneg g hg hA hB) (atom0251_nonneg g hg hA hB)) (add_nonneg (atom0252_nonneg g hg hA hB) (add_nonneg (atom0253_nonneg g hg hA hB) (atom0254_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0255_nonneg g hg hA hB) (atom0256_nonneg g hg hA hB)) (add_nonneg (atom0257_nonneg g hg hA hB) (add_nonneg (atom0258_nonneg g hg hA hB) (atom0259_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0260_nonneg g hg hA hB) (atom0261_nonneg g hg hA hB)) (add_nonneg (atom0262_nonneg g hg hA hB) (add_nonneg (atom0263_nonneg g hg hA hB) (atom0264_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0265_nonneg g hg hA hB) (atom0266_nonneg g hg hA hB)) (add_nonneg (atom0267_nonneg g hg hA hB) (add_nonneg (atom0268_nonneg g hg hA hB) (atom0269_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0270_nonneg g hg hA hB) (atom0271_nonneg g hg hA hB)) (add_nonneg (atom0272_nonneg g hg hA hB) (add_nonneg (atom0273_nonneg g hg hA hB) (atom0274_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0275_nonneg g hg hA hB) (atom0276_nonneg g hg hA hB)) (add_nonneg (atom0277_nonneg g hg hA hB) (add_nonneg (atom0278_nonneg g hg hA hB) (atom0279_nonneg g hg hA hB))))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0280_nonneg g hg hA hB) (atom0281_nonneg g hg hA hB)) (add_nonneg (atom0282_nonneg g hg hA hB) (add_nonneg (atom0283_nonneg g hg hA hB) (atom0284_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0285_nonneg g hg hA hB) (atom0286_nonneg g hg hA hB)) (add_nonneg (atom0287_nonneg g hg hA hB) (add_nonneg (atom0288_nonneg g hg hA hB) (atom0289_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0290_nonneg g hg hA hB) (atom0291_nonneg g hg hA hB)) (add_nonneg (atom0292_nonneg g hg hA hB) (add_nonneg (atom0293_nonneg g hg hA hB) (atom0294_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0295_nonneg g hg hA hB) (atom0296_nonneg g hg hA hB)) (add_nonneg (atom0297_nonneg g hg hA hB) (add_nonneg (atom0298_nonneg g hg hA hB) (atom0299_nonneg g hg hA hB)))))) (add_nonneg (add_nonneg (add_nonneg (add_nonneg (atom0300_nonneg g hg hA hB) (atom0301_nonneg g hg hA hB)) (add_nonneg (atom0302_nonneg g hg hA hB) (add_nonneg (atom0303_nonneg g hg hA hB) (atom0304_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0305_nonneg g hg hA hB) (atom0306_nonneg g hg hA hB)) (add_nonneg (atom0307_nonneg g hg hA hB) (add_nonneg (atom0308_nonneg g hg hA hB) (atom0309_nonneg g hg hA hB))))) (add_nonneg (add_nonneg (add_nonneg (atom0310_nonneg g hg hA hB) (atom0311_nonneg g hg hA hB)) (add_nonneg (atom0312_nonneg g hg hA hB) (add_nonneg (atom0313_nonneg g hg hA hB) (atom0314_nonneg g hg hA hB)))) (add_nonneg (add_nonneg (atom0315_nonneg g hg hA hB) (atom0316_nonneg g hg hA hB)) (add_nonneg (atom0317_nonneg g hg hA hB) (add_nonneg (atom0318_nonneg g hg hA hB) (atom0319_nonneg g hg hA hB))))))))

end APPT.Finite12
